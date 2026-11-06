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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 1440 of its 1488 lines of code are new or changed and 405 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the walk of the
   test harness's entry function LLVMFuzzerTestOneInput (0x84dc0), segment S09 of PLAN-asanubsan-main section 2.3,
   K855c8 -> K856f4 (0x855c8 .. 0x856f0): the statement lt_seg_S09_stmt of LLVMFuzzerTestOneInput_defs.v, proved as
   lt_seg_S09.

   proves function LLVMFuzzerTestOneInput (reuse search, rule 24: released units, the earlier proof delivery and working
   heads; the result is recorded with the commissioning brief; none: written new, ADAPTED from image A's S09 walk (the
   image-A G1 walk owner's) and plugin-hostd/fuzz_command's lib/B/Prog harness walk)

   THE FORM: plugin-hostd/fuzz_command's lib/B/Prog harness walk (origin/ossv/recipes 3abc3740de97: a seed symbolic
   state at each point, one run per straight stretch, each program call through its statement and the call rule,
   the next point's premises from the run's registers and the call's post), with the points and lemmas of image A's
   S09 walk (LLVMFuzzerTestOneInput_s18x.v of image A's twin walk, the same segment of image A) at image B's
   registers, slots and pcs. The code (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s lines 516-590):
   - 0x855c8 .. 0x855d4: a0 = c (168(s1)), a1 = s6 = m, a2 = returned (176(s1)), check_segments;
   - 0x855d8 .. 0x8562c: the shadow base (200(s1)); UBSan's alignment test of m->n (`bnez s5` 0x855dc, s5 = M & 3
     = 0: the trap 0x85ff8 not reached); 176(s1) := SH(m + 0x2000); check 18 (the shadow byte is 0: m + 0x2000 ..
     + 0x2007 are addressable); m->n; `blez` to K856f4 when it is 0; else the loop's registers (s2 = 256 i, s3 =
     &m->seg[i], s5 = i, s6 = 33, s7 = 4, s8 = 90, s9 = SH(FR), s10 = -8, s11 = c; 160(s1) := (M + 0x2000) & 7 + 3);
   - the loop head 0x85630, turn i < m->n <= 32: UBSan's index test `beq s5,s6` (i = 33) and pointer test
     `bltu ~M, 256 i` (m + 256 i wraps), both decided by the seed's ranges (the traps not reached); r in scope
     (SH(FR) + 22 := 04), r := 0x5a; reac_segconf_role(c, &m->seg[i], &r), check_role(set, r, &m->seg[i]),
     reac_segconf_model / check_model, reac_segconf_ignored / check_ignore, reac_segconf_role_file,
     reac_segconf_ignore_file, check_provenance; r out of scope (SH(FR) + 22 := f8); check 19 (the same shadow
     byte); m->n; i += 1; `blt` back to the head or on to K856f4.
   Each callee is taken as its statement (lib/B/Prog/<F>_c.v, a Section hypothesis at every FP state), with its
   premises from SegModel's agreement theorem at the payload (check_segments, check_seg of every model segment)
   and the reader / model encodings (LLVMFuzzerTestOneInput_s18k.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegSyms SegList SegPa SegPaLib PaCall PaDenot
  PaLibF PaLibG PaNoChain PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s18k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_segconf_find_c check_segments_c
  reac_segconf_role_c check_role_c reac_segconf_model_c check_model_c reac_segconf_ignored_c check_ignore_c
  reac_segconf_role_file_c reac_segconf_ignore_file_c check_provenance_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

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
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : seg_sig_prog.
(* the ten callees' statements at image B's entries and windows (SegInstB), at every FP state *)
Hypothesis HCSEG : forall fx0 : YK11.FPState,
  check_segments_contract (fx := fx0) SEGS B (BASE + AF_check_segments) STK_check_segments RLO_A RHI_A.
Hypothesis HROLE : forall fx0 : YK11.FPState,
  reac_segconf_role_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_role) STK_reac_segconf_role RLO_A RHI_A.
Hypothesis HCROLE : forall fx0 : YK11.FPState,
  check_role_contract (fx := fx0) SEGS B (BASE + AF_check_role) STK_check_role.
Hypothesis HMODEL : forall fx0 : YK11.FPState,
  reac_segconf_model_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_model) STK_reac_segconf_model RLO_A RHI_A.
Hypothesis HCMODEL : forall fx0 : YK11.FPState,
  check_model_contract (fx := fx0) SEGS B (BASE + AF_check_model) STK_check_model RLO_A RHI_A.
Hypothesis HIGN : forall fx0 : YK11.FPState,
  reac_segconf_ignored_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_ignored) STK_reac_segconf_ignored RLO_A RHI_A.
Hypothesis HCIGN : forall fx0 : YK11.FPState,
  check_ignore_contract (fx := fx0) SEGS B (BASE + AF_check_ignore) STK_check_ignore.
Hypothesis HRFILE : forall fx0 : YK11.FPState,
  reac_segconf_role_file_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_role_file) STK_reac_segconf_role_file
    RLO_A RHI_A.
Hypothesis HIFILE : forall fx0 : YK11.FPState,
  reac_segconf_ignore_file_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_ignore_file)
    STK_reac_segconf_ignore_file RLO_A RHI_A.
Hypothesis HCPROV : forall fx0 : YK11.FPState,
  check_provenance_contract (fx := fx0) SEGS B (BASE + AF_check_provenance) STK_check_provenance RLO_A RHI_A.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the points of S09 ---- *)
(* 0x855d8: check_segments returned; s5 = M & 3 = 0, s10 = (m + 0x2000) >> 3 *)
Definition S9_cs_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 -> s9M B MT cx ly S W regs mem md k acc LFO0 c m ->
  getr regs 21 = w64 0 -> getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO9_CS) regs mem md) (lt_post B MT cx).
(* 0x85630: the loop head, turn i < m->n; 176(s1) = SH(m + 0x2000) *)
Definition S9_loop_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  s9M B MT cx ly S W regs mem md k acc LFO0 c m -> s9S cx (rdW W mem) m -> s9R cx i regs c m ->
  SRr SEGS W (cfg_at SEGS (BASE + LO9_LOOP) regs mem md) (lt_post B MT cx).
(* the points of turn i after each call (image A's S09 walk's S9_at): s9M with r's shadow as o says, 176(s1), the
   loop's registers, and X *)
Definition S9_at (i : nat) (off : Z) (o : lfo) (X : lcx -> bvmap 5 word -> reader -> Z -> Z -> Prop) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  s9M B MT cx ly S W regs mem md k acc o c m -> s9S cx (rdW W mem) m -> s9R cx i regs c m ->
  X cx regs (rdW W mem) c m ->
  SRr SEGS W (cfg_at SEGS (BASE + off) regs mem md) (lt_post B MT cx).
Definition s9_X0 : lcx -> bvmap 5 word -> reader -> Z -> Z -> Prop := fun _ _ _ _ _ => True.
Definition s9_nm (cx : lcx) (i : nat) : list Z := SegModel.ms_name (x_seg cx i).
(* r's value after reac_segconf_role: the role when it answers Some, else the 0x5a stored before the call *)
Definition s9_rval (cx : lcx) (i : nat) : Z :=
  match SegModel.r_role (x_rcF cx) (s9_nm cx i) with Some v => v | None => 90 end.
Definition s9_rset (cx : lcx) (i : nat) : Z :=
  match SegModel.r_role (x_rcF cx) (s9_nm cx i) with Some _ => 1 | None => 0 end.
Definition S9_R1 (i : nat) : Prop := S9_at i LO9_R1 LFO_R (fun cx regs rd c m =>
  getr regs 20 = w64 (x_fr cx + FO_R) /\ getr regs 10 = w64 (s9_rset cx i) /\ sa_val rd (x_fr cx + FO_R) 4 (s9_rval cx i)).
Definition S9_R2 (i : nat) : Prop := S9_at i LO9_R2 LFO_R s9_X0.
Definition S9_R3 (i : nat) : Prop := S9_at i LO9_R3 LFO_R (fun cx regs rd c m =>
  getr regs 10 = w64 (seg_spec.model_ptr c (x_rcF cx) (s9_nm cx i))).
Definition S9_R4 (i : nat) : Prop := S9_at i LO9_R4 LFO_R s9_X0.
Definition S9_R5 (i : nat) : Prop := S9_at i LO9_R5 LFO_R (fun cx regs rd c m =>
  getr regs 10 = w64 (seg_spec.b2z (SegModel.r_ignored (x_rcF cx) (s9_nm cx i)))).
Definition S9_R6 (i : nat) : Prop := S9_at i LO9_R6 LFO_R s9_X0.
Definition S9_R7 (i : nat) : Prop := S9_at i LO9_R7 LFO_R (fun cx regs rd c m =>
  getr regs 10 = w64 (seg_spec.role_file_ptr c (x_rcF cx) (s9_nm cx i))).
Definition S9_R8 (i : nat) : Prop := S9_at i LO9_R8 LFO_R (fun cx regs rd c m =>
  getr regs 20 = w64 (seg_spec.role_file_ptr c (x_rcF cx) (s9_nm cx i)) /\
  getr regs 10 = w64 (seg_spec.ignore_file_ptr c (x_rcF cx) (s9_nm cx i))).
Definition S9_R9 (i : nat) : Prop := S9_at i LO9_R9 LFO_R s9_X0.

(* ---- the seed of a stretch with no region and no fact: every register its own atom ---- *)
Definition s9_E0 (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Lemma s9_seed0 : forall pc (W : world SEGS) regs mem,
  st_ok_pi SEGS VAL (s9_E0 regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 9 0) [] (s9_E0 regs) (mrestrict (w_H W) mem).
Proof.
intros pc W regs mem. split; [|apply Forall_nil]. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s9_E0. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.
Lemma s9_E0_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (s9_E0 regs) n = getr regs r.
Proof.
intros regs n r H. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold s9_E0. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact H.
Qed.
(* a run with no region keeps every byte *)
Lemma s9_nowin_kept : forall E (m m' : word -> option byte),
  frame_of E [] m m' -> m' = m.
Proof. intros E m m' HF. apply functional_extensionality. intros x. apply HF. intros (r0 & Hr0 & _). destruct Hr0. Qed.

(* ---- the seed of 0x855c8 .. jal check_segments: s1's slots 168 (c, atom 32) and 176 (returned, atom 33) ---- *)
Definition s9_ssA : sstate :=
  mkSS LO_K855c8 sr_atoms
    [YP09.mkRegion (Some 9%nat) 168 184 168 168
       [YP09.mkChunk 168 (CVal 8 (SOff 32 0)); YP09.mkChunk 176 (CVal 8 (SOff 33 0))]] None
    (mkFacts [] [] []).
Definition s9_EA (regs : bvmap 5 word) (c rt : Z) : env := Eimg (Ereg regs [w64 c; w64 rt]).
Lemma s9_seedA : forall cx (W : world SEGS) regs mem c rt,
  lt_base B MT cx -> getr regs 9 = w64 (x_s1 cx) ->
  rdword (rdW W mem) (x_s1 cx + 168) = Some c -> rdword (rdW W mem) (x_s1 cx + 176) = Some rt ->
  0 <= c < 2 ^ 64 -> 0 <= rt < 2 ^ 64 ->
  st_ok_pi SEGS VAL (s9_EA regs c rt) s9_ssA
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K855c8)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 9 0) [] (s9_EA regs c rt) (mrestrict (w_H W) mem).
Proof.
intros cx W regs mem c rt HB R9 H168 H176 Hc Hrt.
pose proof (s9_base_facts B MT cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *. pose proof asan_consts as (C1 & _).
assert (E9 : ew (s9_EA regs c rt) 9 = w64 (x_s1 cx)).
{ unfold s9_EA. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl). exact R9. }
assert (E32 : ew (s9_EA regs c rt) 32 = w64 c).
{ unfold s9_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E33 : ew (s9_EA regs c rt) 33 = w64 rt).
{ unfold s9_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
split.
- unfold s9_ssA. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold s9_EA. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val SEGS _ _ (x_s1 cx) 168 8 _ c).
      -- cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hc.
      -- lia.
      -- apply (val_mem_of_rdword SEGS). exact H168.
    * apply (chunk_ok_val SEGS _ _ (x_s1 cx) 176 8 _ rt).
      -- cbn [sv_denot]. rewrite E33, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hrt.
      -- lia.
      -- apply (val_mem_of_rdword SEGS). exact H176.
  + cbn. tauto.
  + unfold facts_ok. cbn. tauto.
- apply Forall_nil.
Qed.

(* 0x855c8 .. 0x855d4: a0 = c (168(s1)), a1 = s6 = m, a2 = returned (176(s1)), jal check_segments; the call; to
   0x855d8 *)
Lemma s9_head : S9_cs_stmt -> LT_K855c8_stmt B MT.
Proof.
intros HN cx ly S W regs mem md k acc c m HB HFRM HC Hc Hm R21 R22 R26 HSL HCM.
assert (HSL9 : lt_slots cx (rdW W mem) (LS9 cx c m)).
{ intros o v Hin. apply HSL. unfold LS9 in Hin. apply in_app_or in Hin as [Hin | Hin]; apply in_or_app; [left; exact Hin|].
  right. cbn [In] in Hin |- *. tauto. }
assert (HM : s9M B MT cx ly S W regs mem md k acc LFO0 c m) by (split; [exact HC|]; split; [exact Hc|]; split; [exact Hm|];
  split; [exact HSL9 | exact HCM]).
pose proof HC as ((HJ & R2 & R3 & R4 & R8 & R9 & _) & _).
pose proof Hc as (Hcin & Hc4 & Hc16 & Hcaddr). pose proof Hm as (Hmin & Hm4 & Hm16 & Hmaddr).
pose proof HJ as (HAR & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcin) as (_ & _ & Hcc & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & _ & Hmc & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc.
pose proof asan_consts as (C1 & _).
assert (Hc64 : 0 <= c < 2 ^ 64) by (unfold seg_spec.SEG_C_SIZE in *; lia).
assert (Hm64 : 0 <= m < 2 ^ 64) by (unfold seg_spec.SEG_M_SIZE in *; lia).
set (rt := seg_spec.b2z (seg_spec.seg_ret (x_run cx))) in *.
assert (Hrt : 0 <= rt < 2 ^ 64) by (unfold rt, seg_spec.b2z; destruct (seg_spec.seg_ret (x_run cx)); lia).
assert (H168 : rdword (rdW W mem) (x_s1 cx + 168) = Some c) by (apply HSL; unfold LT_LC; cbn [In app]; tauto).
assert (H176 : rdword (rdW W mem) (x_s1 cx + 176) = Some rt) by (apply HSL; apply in_or_app; right; cbn [In]; tauto).
destruct (s9_seedA cx W regs mem c rt HB R9 H168 H176 Hc64 Hrt) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (s9_EA regs c rt)) by (unfold s9_EA; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [w64 c; w64 rt]) (s9_EA regs c rt)).
{ unfold s9_EA. split; [intros i Hi; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (EM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r0 & Hr0 & Hw). cbn [s9_ssA ss_mem In] in Hr0.
  destruct Hr0 as [<-|[]]. cbn in Hw. lia. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [w64 c; w64 rt] HS); [exact HAE | vm_compute; reflexivity]. }
rewrite (SIGP SS_check_segments ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_check_segments) with AF_check_segments by (vm_compute; reflexivity).
rewrite EM in HJ |- *.
assert (EE32 : ew (s9_EA regs c rt) 32 = w64 c).
{ unfold s9_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (EE33 : ew (s9_EA regs c rt) 33 = w64 rt).
{ unfold s9_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
assert (EE22 : ew (s9_EA regs c rt) 22 = getr regs 22).
{ unfold s9_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ 22 22%bv eq_refl). }
rewrite EE32 in P10. rewrite EE22, R22 in P11. rewrite EE33 in P12.
assert (E2 : getr (ms_regs ms) 2 = getr regs 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
assert (E3 : getr (ms_regs ms) 3 = getr regs 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
assert (E4 : getr (ms_regs ms) 4 = getr regs 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
assert (E8 : getr (ms_regs ms) 8 = getr regs 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
assert (E9 : getr (ms_regs ms) 9 = getr regs 9) by exact (HPR 9 ltac:(unfold acallee_saved; lia)).
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBlo.
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
pose proof (s18_harness (x_pl cx)) as [HCS _].
assert (HPRE : check_segments_pre B ly S (rdW W mem) c m rt
  (seg_spec.seg_rc (x_run cx)) (seg_spec.seg_mc (x_run cx)) (seg_spec.seg_ret (x_run cx))).
{ destruct HCM as [HRC HMC].
  split; [lia|]. split; [exact Hc16|]. split; [exact HRC|].
  split; [exists c, seg_spec.SEG_C_SIZE; split; [exact Hcin | lia]|]. split; [exact Hcaddr|].
  split; [lia|]. split; [exact Hm16|]. split; [exact HMC|].
  split; [exists m, seg_spec.SEG_M_SIZE; split; [exact Hmin | lia]|]. split; [exact Hmaddr|].
  split; [reflexivity | exact HCS]. }
pose proof (s9M_run B MT LAWS MTFL cx ly S W regs mem md k acc LFO0 c m regs mem mdv HB HM HJ (fun a _ => eq_refl)
  eq_refl eq_refl eq_refl eq_refl eq_refl) as HMv.
eapply (s9_call B MT LAWS MTFL cx ly S W regs mem mdv k acc LFO0 c m (ms_regs ms) (BASE + AF_check_segments)
  STK_check_segments [] EV_check_segments (fun _ => False) _ (fun _ _ _ _ _ _ => True) _ HB HMv E2 E3 E4 E8 E9 HraT Hra4T
  ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) eq_refl).
- intros a Ha. exfalso. exact (inFP_nil a Ha).
- intros a Ha. destruct Ha.
- intros ch HPRE1 HRO Hnev.
  exact (HCSEG fx ly S W (ms_regs ms) mem mdv ch c m rt _ _ _ HPRE1 HRO P10 Hc64 P11 Hm64 P12 Hrt HPRE Hnev).
- cbv beta. intros ly' S' W' regs' mem' md' (HK1 & HNA). split; [exact I | split; [exact HK1 | exact HNA]].
- intros ly2 S2 W2 regs2 mem2 md2 HM2 HP2 _ _ _.
  rewrite P1.
  apply (HN cx ly2 S2 W2 regs2 mem2 md2 k acc c m HB HFRM HM2).
  + exact (eq_trans (HP2 21 ltac:(unfold acallee_saved; lia)) (eq_trans (HPR 21 ltac:(unfold acallee_saved; lia)) R21)).
  + exact (eq_trans (HP2 26 ltac:(unfold acallee_saved; lia)) (eq_trans (HPR 26 ltac:(unfold acallee_saved; lia)) R26)).
Qed.

(* an 8-byte chunk of a region of a state, read back (image A's S00 walk's s10_rd_chunk8) *)
Lemma s9_rd_chunk8 : forall E H mem base off a e v cs,
  Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  a = base + off -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros E H mem base off a e v cs Hc Hin -> He Hv. rewrite Forall_forall in Hc. specialize (Hc _ Hin).
apply rdword_of_val_mem; [|exact Hv].
apply (val_of_chunk_ok SEGS E _ base off 8 e v Hc He); [exact Hv | cbn; lia].
Qed.
(* the chunks of the region i of a state *)
Lemma s9_region_chunks : forall E ss (H : word -> bool) ms i b lo hi wlo whi cs,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some b) lo hi wlo whi cs) ->
  Forall (YP09.chunk_ok SEGS E (mrestrict H (ms_mem ms)) (bv_unsigned (ew E b))) cs.
Proof.
intros E ss H ms i b lo hi wlo whi cs HS Hi. pose proof (st_ok_pi_region_nth E ss (restrict H ms) i _ HS Hi) as HR.
unfold region_ok in HR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & HC). exact HC.
Qed.

(* ---- the seed at 0x855d8: s1's slots 160 and 176 (written), 168 (c, atom 32), 184 (SH(FR), 34), 192 (m, 33), 200
   (the shadow base, a literal), 216 (m + 0x2000, 35); SH(m + 0x2000) at s10 + the base, 0 (check 18); m->n (atom 36,
   in [lo, hi]); s5 pinned to 0 ---- *)
Definition s9_slotsB : smem :=
  [ YP09.mkRegion (Some 9%nat) 160 168 160 168 [];
    YP09.mkRegion (Some 9%nat) 168 176 168 168 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 9%nat) 176 184 176 184 [];
    YP09.mkRegion (Some 9%nat) 184 224 184 184
      [YP09.mkChunk 184 (CVal 8 (SOff 34 0)); YP09.mkChunk 192 (CVal 8 (SOff 33 0));
       YP09.mkChunk 200 (CVal 8 (SLit SHADOW_OFF)); YP09.mkChunk 216 (CVal 8 (SOff 35 0))];
    YP09.mkRegion (Some 26%nat) SHADOW_OFF (SHADOW_OFF + 1) SHADOW_OFF SHADOW_OFF
      [YP09.mkChunk SHADOW_OFF (CVal 1 (SLit 0))];
    YP09.mkRegion (Some 35%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 36 0))] ].
(* s1 lies above the shadow span (alloc_ceiling <= s1 < 2 ^ 47): the writable slots are apart from the shadow *)
Definition S1_LO : Z := 0x7fff7f800000.
Definition s9_FB (lo hi : Z) : facts := mkFacts [(9%nat, mkAF S1_LO (2 ^ 47) 0); (36%nat, mkAF lo hi 0)] [] [].
Definition s9_ssB0 (lo hi : Z) : sstate := mkSS LO9_CS sr_atoms s9_slotsB None (s9_FB lo hi).
Definition s9_ssB (lo hi : Z) : sstate := mkSS LO9_CS (sr_set sr_atoms 21%bv (SLit 0)) s9_slotsB None (s9_FB lo hi).
Definition s9_xB (cx : lcx) (c m n : Z) : list word :=
  [w64 c; w64 m; w64 (x_sh cx); w64 (m + seg_spec.MC_N); w64 n].
Definition s9_EB (regs : bvmap 5 word) (cx : lcx) (c m n : Z) : env := Eimg (Ereg regs (s9_xB cx c m n)).
Lemma s9_seedB : forall cx ly S W regs mem md k acc c m lo hi,
  lt_base B MT cx -> s9M B MT cx ly S W regs mem md k acc LFO0 c m ->
  getr regs 21 = w64 0 -> getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  lo <= Z.of_nat (length (SegModel.mc_seg (x_mcF cx))) <= hi ->
  st_ok_pi SEGS VAL (s9_EB regs cx c m (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) (s9_ssB lo hi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO9_CS)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 9 0) [] (s9_EB regs cx c m (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) (mrestrict (w_H W) mem).
Proof.
intros cx ly S W regs mem md k acc c m lo hi HB HM R21 R26 Hlh.
pose proof (s9_base_facts B MT cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
pose proof HM as ((HFR & _) & Hc & Hm & HSL & (HRC & HMC)).
destruct HFR as (HJ & _ & _ & _ & _ & R9 & _ & _ & _ & _ & _ & W200 & _ & W184).
pose proof Hc as (Hcin & Hc4 & Hc16 & _). pose proof Hm as (Hmin & Hm4 & Hm16 & Hmaddr).
pose proof HJ as (HAR & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcin) as (_ & _ & Hcc & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & _ & Hmc & Hmapp & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc, Hmapp.
pose proof asan_consts as (C1 & _).
destruct (s9_frame_at B MT LAWS cx ly S W mem md k HB HJ) as (_ & _ & _ & _ & Hf4 & Hfc & _).
set (n := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) in *.
assert (Hn : 0 <= n <= 32) by (pose proof (s18_mconf_len _ _ _ HMC); unfold n, x_mcF; lia).
assert (Hsh : 0x7fff8000 <= x_sh cx < 0x7fff8000 + 2 ^ 44).
{ unfold x_sh, shadow_addr, SHADOW_OFF. split; [pose proof (Z.div_pos (x_fr cx) 8); lia|].
  assert (x_fr cx / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (Hq : 0 <= (m + seg_spec.MC_N) / 8 < 2 ^ 44).
{ unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
set (E := s9_EB regs cx c m n).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs (s9_xB cx c m n)) q)
  by (intros q Hq'; unfold E, s9_EB; apply Eimg_low; exact Hq').
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E26 : ew E 26 = w64 ((m + seg_spec.MC_N) / 8))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E32 : ew E 32 = w64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 m) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (x_sh cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (m + seg_spec.MC_N)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (SL : forall o v, In (o, v) (LS9 cx c m) -> val_mem SEGS (mrestrict (w_H W) mem) (x_s1 cx + o) 8 v)
  by (intros o v Hin; apply (val_mem_of_rdword SEGS); exact (HSL o v Hin)).
assert (HS0 : st_ok_pi SEGS VAL E (s9_ssB0 lo hi) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO9_CS)) mem (seg_rom SEGS)))).
{ unfold s9_ssB0. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold E, s9_EB. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold s9_slotsB.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS).
      pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres.
      unfold STK_LLVMFuzzerTestOneInput, x_sp0 in *. lia.
    * rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (x_s1 cx) 168 8 _ c);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.SEG_C_SIZE in *; lia | lia
        | exact (SL 168 _ ltac:(unfold LS9, LT_LC; cbn [In app]; tauto))].
    * rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS).
      pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres.
      unfold STK_LLVMFuzzerTestOneInput, x_sp0 in *. lia.
    * rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS _ _ (x_s1 cx) 184 8 _ (x_sh cx));
           [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact (val_mem_of_rdword SEGS _ _ _ _ W184)].
      -- apply (chunk_ok_val SEGS _ _ (x_s1 cx) 192 8 _ m);
           [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.SEG_M_SIZE in *; lia | lia
           | exact (SL 192 _ ltac:(unfold LS9, LT_LC; cbn [In app]; tauto))].
      -- apply (chunk_ok_val SEGS _ _ (x_s1 cx) 200 8 _ SHADOW_OFF);
           [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | lia
           | exact (val_mem_of_rdword SEGS _ _ _ _ W200)].
      -- apply (chunk_ok_val SEGS _ _ (x_s1 cx) 216 8 _ (m + seg_spec.MC_N));
           [cbn [sv_denot]; rewrite E35, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.SEG_M_SIZE, seg_spec.MC_N in *; lia | lia
           | exact (SL 216 _ ltac:(unfold LS9, LT_LC; cbn [In app]; tauto))].
    * rewrite E26, unsigned_lit_small by lia.
      split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ ((m + seg_spec.MC_N) / 8) SHADOW_OFF 1 _ 0); [reflexivity | lia | lia |].
      apply s9_val_of_rd. intros k0 Hk0. destruct k0 as [|k0]; [|lia]. rewrite Z.add_0_r.
      replace ((m + seg_spec.MC_N) / 8 + SHADOW_OFF) with (shadow_addr (m + seg_spec.MC_N))
        by (unfold shadow_addr; lia).
      rewrite (s9_mn_shadow _ m Hmaddr Hm16). reflexivity.
    * rewrite E35, unsigned_lit_small by (unfold seg_spec.SEG_M_SIZE, seg_spec.MC_N in *; lia).
      split; [unfold seg_spec.MC_N; lia|]. split; [unfold seg_spec.SEG_M_SIZE, seg_spec.MC_N in *; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (m + seg_spec.MC_N) 0 4 _ n);
        [cbn [sv_denot]; rewrite E36, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
      rewrite Z.add_0_r. exact (s9_val_of_rd _ _ _ _ _ (s18_mconf_n _ _ _ HMC)).
  + apply pairwise_disjoint_of_extents.
    unfold s9_slotsB, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E26, E35, !unsigned_lit_small by (unfold seg_spec.SEG_M_SIZE, seg_spec.MC_N in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct Hmapp as (_ & [Hl | (Hh & _)]); unfold kLowShadowBeg, kHighMemBeg, seg_spec.SEG_M_SIZE, seg_spec.MC_N,
      SHADOW_OFF in *; repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [s9_FB f_atoms atoms_ok]. split; [|split; [|exact I]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    * rewrite E9, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. unfold S1_LO. lia.
    * rewrite E36, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
split; [|apply Forall_nil].
exact (st_ok_pi_pin_reg' _ _ _ 21%bv 0 HS0 R21 eq_refl).
Qed.

(* a byte the run did not store (image A's S09 walk's s9_aview_pt) *)
Lemma s9_aview_pt : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

(* 0x855d8 .. 0x85630: the shadow base; UBSan's alignment test of m->n (`bnez s5`, s5 = 0: the trap 0x85ff8 not
   reached); 176(s1) := SH(m + 0x2000); check 18 (the shadow byte is 0); m->n; `blez` to K856f4 when it is 0, else
   the loop's registers, 160(s1) := (M + 0x2000) & 7 + 3, and the head of turn 0 *)
Lemma s9_cs : S9_loop_stmt 0 -> LTA_K856f4 B MT -> S9_cs_stmt.
Proof.
intros HL HK cx ly S W regs mem md k acc c m HB HFRM HM R21 R26.
pose proof HM as ((HFR & _) & Hc & Hm & HSL & HCM).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof (s9_base_facts B MT cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
pose proof asan_consts as (C1 & _).
pose proof HM as (_ & _ & (Hmin & _ & Hm16 & _) & _).
pose proof HJ as (HAR & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & _ & Hmc & _).
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc.
pose proof HCM as [HRC HMC].
set (n := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) in *.
assert (Hn : 0 <= n <= 32) by (pose proof (s18_mconf_len _ _ _ HMC); unfold n, x_mcF; lia).
assert (Hq : 0 <= (m + seg_spec.MC_N) / 8 < 2 ^ 44).
{ pose proof HM as (_ & _ & (_ & Hm4 & _) & _). clear - Hm4 Hmc C1.
  unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
assert (Hsh : 0 <= shadow_addr (m + seg_spec.MC_N) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; lia).
(* the seed, the run's stores (the slots 160 and 176) and the slot 176 after it, for either outcome of `blez` *)
set (E := s9_EB regs cx c m n).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs (s9_xB cx c m n)) q)
  by (intros q Hq'; unfold E, s9_EB; apply Eimg_low; exact Hq').
assert (E9 : ew E 9 = w64 (x_s1 cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E26 : ew E 26 = w64 ((m + seg_spec.MC_N) / 8))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (HEI : img_env VAL A_LIM E) by (unfold E, s9_EB; apply Eimg_env).
assert (SEED : forall lo hi, lo <= n <= hi ->
  st_ok_pi SEGS VAL E (s9_ssB lo hi) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO9_CS)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 9 0) [] E (mrestrict (w_H W) mem)).
{ intros lo hi Hlh. exact (s9_seedB cx ly S W regs mem md k acc c m lo hi HB HM R21 R26 ltac:(fold n; lia)). }
assert (AWR : forall lo hi STK0 sp0 FP bl0 blc fr0 ly0 own, sp0 = x_sp0 cx -> STK0 = 32768 ->
  awr_ok SEGS B E (ss_mem (s9_ssB lo hi)) STK0 sp0 FP bl0 blc fr0 ly0 own).
{ intros lo hi STK0 sp0 FP bl0 blc fr0 ly0 own -> ->. unfold s9_ssB, s9_slotsB. cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
    [reflexivity | rewrite E9; unfold w64; rewrite unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
    [reflexivity | rewrite E9; unfold w64; rewrite unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
  do 3 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (KEPT : forall lo hi (mem2 : word -> option byte), frame_of E (ss_mem (s9_ssB lo hi)) mem mem2 ->
  forall a, 0 <= a < 2 ^ 64 -> ~ s9_slotw cx a -> rdW W mem2 a = rdW W mem a).
{ intros lo hi mem2 HF a Ha Hn'. apply s9_aview_pt. apply HF. rewrite unsigned_lit_small by lia.
  intros (r0 & Hr0 & Hw). unfold s9_ssB, s9_slotsB in Hr0. cbn [ss_mem In] in Hr0.
  destruct Hr0 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hw;
    try (rewrite E9 in Hw; unfold w64 in Hw; rewrite unsigned_lit_small in Hw by lia); unfold s9_slotw in Hn'; lia. }
destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
- (* m->n = 0: blez to K856f4 *)
  destruct (SEED 0 0 ltac:(lia)) as (HS & SHOK).
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) LO_K856f4.
  { exact (AWR 0 0 _ _ _ _ _ _ _ _ eq_refl eq_refl). }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  pose proof (KEPT 0 0 (ms_mem ms) HF) as KM.
  assert (H176 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 176) = Some (shadow_addr (m + seg_spec.MC_N))).
  { pose proof (s9_region_chunks E _ (w_H W) ms 2 9 176 184 176 184 _ HS eq_refl) as HC2.
    apply (s9_rd_chunk8 E (w_H W) (ms_mem ms) _ 176 _ (SOff 26 SHADOW_OFF) _ _ HC2 (or_introl eq_refl));
      [rewrite E9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | | exact Hsh].
    cbn [sv_denot]. rewrite E26. unfold w64. rewrite unsigned_lit_small by lia. unfold shadow_addr. f_equal. lia. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  rewrite EL in P2, P3, P4, P8, P9 by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in P2. rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl) in P3.
  rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl) in P4. rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl) in P8.
  rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl) in P9.
  destruct (s9_agree_slots B MT LAWS cx ly S W regs mem md k acc LFO0 c m W (ms_mem ms) HB HM KM) as [HAG H22].
  pose proof (s9M_agree B MT LAWS MTFL cx ly S W regs mem md k acc LFO0 LFO0 c m ly S W (ms_regs ms) (ms_mem ms) mdv
    HB HM HJ P2 P3 P4 P8 P9 HAG ltac:(rewrite H22; exact (s9_r_shadow B MT cx ly S W regs mem md k acc LFO0 c m HM))
    eq_refl eq_refl eq_refl eq_refl (Permutation_refl _) (or_introl eq_refl)) as (HC' & Hc' & Hm' & HSL' & HCM').
  apply (HK fx cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m HB HFRM HC' Hc' Hm'); [|exact HCM'].
  intros o v Hin. apply in_app_or in Hin as [Hin | Hin].
  + apply HSL'. unfold LS9. apply in_or_app. left. exact Hin.
  + cbn [In] in Hin. destruct Hin as [Hin | [Hin | []]]; injection Hin as <- <-.
    * apply HSL'. unfold LS9. apply in_or_app. right. cbn [In]. tauto.
    * exact H176.
- (* m->n >= 1: the loop's registers, then turn 0 *)
  destruct (SEED 1 32 ltac:(lia)) as (HS & SHOK).
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) LO9_LOOP.
  { exact (AWR 1 32 _ _ _ _ _ _ _ _ eq_refl eq_refl). }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  pose proof (KEPT 1 32 (ms_mem ms) HF) as KM.
  assert (H176 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 176) = Some (shadow_addr (m + seg_spec.MC_N))).
  { pose proof (s9_region_chunks E _ (w_H W) ms 2 9 176 184 176 184 _ HS eq_refl) as HC2.
    apply (s9_rd_chunk8 E (w_H W) (ms_mem ms) _ 176 _ (SOff 26 SHADOW_OFF) _ _ HC2 (or_introl eq_refl));
      [rewrite E9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | | exact Hsh].
    cbn [sv_denot]. rewrite E26. unfold w64. rewrite unsigned_lit_small by lia. unfold shadow_addr. f_equal. lia. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  rewrite EL in P2, P3, P4, P8, P9, P19, P25, P27 by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in P2. rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl) in P3.
  rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl) in P4. rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl) in P8.
  rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl) in P9.
  rewrite (ew_Ereg_extra regs _ 1) in P19. rewrite (ew_Ereg_extra regs _ 2) in P25.
  rewrite (ew_Ereg_extra regs _ 0) in P27.
  destruct (s9_agree_slots B MT LAWS cx ly S W regs mem md k acc LFO0 c m W (ms_mem ms) HB HM KM) as [HAG H22].
  pose proof (s9M_agree B MT LAWS MTFL cx ly S W regs mem md k acc LFO0 LFO0 c m ly S W (ms_regs ms) (ms_mem ms) mdv
    HB HM HJ P2 P3 P4 P8 P9 HAG ltac:(rewrite H22; exact (s9_r_shadow B MT cx ly S W regs mem md k acc LFO0 c m HM))
    eq_refl eq_refl eq_refl eq_refl (Permutation_refl _) (or_introl eq_refl)) as HM'.
  apply (HL cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m HB HFRM ltac:(unfold n in Hn0; lia) HM' H176).
  split; [exact P18|].
  split; [rewrite P19; unfold seg_spec.mseg_addr; cbn [Z.of_nat]; rewrite Z.mul_0_r, Z.add_0_r; reflexivity|].
  split; [exact P21|]. split; [exact P22|]. split; [exact P23|]. split; [exact P24|].
  split; [exact P25|]. split; [rewrite P26; apply bv_eq; reflexivity | exact P27].
Qed.

(* ---- the callees' premises at turn i, from s9M and the model (image A's S09 walk, word for word) ---- *)
Lemma s9_blocks : forall cx ly S W regs mem md k acc o c m, s9M B MT cx ly S W regs mem md k acc o c m ->
  c <> 0 /\ c mod 16 = 0 /\ 0 < c /\ c + seg_spec.SEG_C_SIZE < 2 ^ 63 /\
  m <> 0 /\ m mod 16 = 0 /\ 0 < m /\ m + seg_spec.SEG_M_SIZE < 2 ^ 63 /\
  sa_heap B ly S c seg_spec.SEG_C_SIZE /\ sa_heap B ly S m seg_spec.SEG_M_SIZE.
Proof.
intros cx ly S W regs mem md k acc o c m HM.
pose proof HM as ((HFR & _) & (Hcin & Hc4 & Hc16 & Hca) & (Hmin & Hm4 & Hm16 & Hma) & _).
pose proof HFR as ((HAR & _) & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcin) as (_ & _ & Hcc & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & _ & Hmc & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc.
pose proof asan_consts as (C1 & _).
split; [lia|]. split; [exact Hc16|]. split; [lia|]. split; [unfold seg_spec.SEG_C_SIZE in *; lia|].
split; [lia|]. split; [exact Hm16|]. split; [lia|]. split; [unfold seg_spec.SEG_M_SIZE in *; lia|].
split; [exists c, seg_spec.SEG_C_SIZE; split; [exact Hcin | lia] | exists m, seg_spec.SEG_M_SIZE; split; [exact Hmin | lia]].
Qed.

Lemma s9_query_pre : forall cx ly S W regs mem md k acc o c m i, s9M B MT cx ly S W regs mem md k acc o c m ->
  (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  query_pre SEGS B ly S (rdW W mem) c (seg_spec.mseg_addr m i) (x_rcF cx) (s9_nm cx i) /\
  0 <= c < 2 ^ 64 /\ 0 <= seg_spec.mseg_addr m i < 2 ^ 64.
Proof.
intros cx ly S W regs mem md k acc o c m i HM Hi.
destruct (s9_blocks cx ly S W regs mem md k acc o c m HM) as (Hc0 & Hc16 & Hcp & Hcb & Hm0 & Hm16 & Hmp & Hmb & Hch & Hmh).
pose proof HM as (_ & (_ & _ & _ & Hca) & (_ & _ & _ & Hma) & _ & (HRC & HMC)).
pose proof (s18_mconf_len _ _ _ HMC) as Hl32.
destruct (s18_mname _ _ _ i HMC Hm16 Hi) as [Hstr Hlen].
unfold s9_nm, x_seg. fold (x_mcF cx) in *.
assert (Ha : m <= seg_spec.mseg_addr m i /\ seg_spec.mseg_addr m i + 16 <= m + seg_spec.SEG_M_SIZE)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE; lia).
split; [|split; [unfold seg_spec.SEG_C_SIZE in *; lia | unfold seg_spec.SEG_M_SIZE in *; lia]].
split; [exact Hc0|]. split; [exact Hc16|]. split; [exact HRC|]. split; [exact Hch|]. split; [exact Hca|].
split; [unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia|]. split; [exact Hstr|]. split.
- left. destruct Hmh as (b & n & Hin & H1 & H2). exists b, n. split; [exact Hin | lia].
- split; [apply (s18_sa_addr_sub _ m seg_spec.SEG_M_SIZE); [exact Hma | lia | lia | lia] | lia].
Qed.

Lemma s9_want : forall cx ly S W regs mem md k acc o c m i, s9M B MT cx ly S W regs mem md k acc o c m ->
  (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  seg_spec.mseg_addr m i mod 4 = 0 /\ sa_mseg (rdW W mem) (seg_spec.mseg_addr m i) (x_seg cx i) /\
  sa_heap B ly S (seg_spec.mseg_addr m i) seg_spec.MSEG_SIZE /\
  sa_addr (rdW W mem) (seg_spec.mseg_addr m i) seg_spec.MSEG_SIZE.
Proof.
intros cx ly S W regs mem md k acc o c m i HM Hi.
destruct (s9_blocks cx ly S W regs mem md k acc o c m HM) as (_ & _ & _ & _ & _ & Hm16 & _ & _ & _ & Hmh).
pose proof HM as (_ & _ & (_ & _ & _ & Hma) & _ & (_ & HMC)).
pose proof (s18_mconf_len _ _ _ HMC) as Hl32.
assert (Ha : m <= seg_spec.mseg_addr m i /\ seg_spec.mseg_addr m i + seg_spec.MSEG_SIZE <= m + seg_spec.SEG_M_SIZE)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE; unfold x_mcF in Hi; lia).
split; [unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; Z.div_mod_to_equations; lia|].
split; [exact (s18_mseg _ _ _ i HMC Hi)|].
split; [destruct Hmh as (b & n & Hin & H1 & H2); exists b, n; split; [exact Hin | lia]|].
apply (s18_sa_addr_sub _ m seg_spec.SEG_M_SIZE); [exact Hma | lia | lia | unfold seg_spec.MSEG_SIZE; lia].
Qed.

Lemma s9_check_seg : forall cx i, (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  SegModel.check_seg (x_rcF cx) (x_seg cx i) = true.
Proof.
intros cx i Hi. pose proof (s18_harness (x_pl cx)) as [_ H].
exact (s18_check_seg_nth _ _ i H Hi).
Qed.

Lemma s9_E0_agree : forall regs, env_agree 32 (Ereg regs []) (s9_E0 regs).
Proof. intros regs. split; [intros i Hi; unfold s9_E0; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

Lemma s9R_pres : forall cx i regs regs2 c m, s9R cx i regs c m ->
  (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) -> s9R cx i regs2 c m.
Proof.
intros cx i regs regs2 c m (R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27) HP.
split; [exact (eq_trans (HP 18 ltac:(unfold acallee_saved; lia)) R18)|].
split; [exact (eq_trans (HP 19 ltac:(unfold acallee_saved; lia)) R19)|].
split; [exact (eq_trans (HP 21 ltac:(unfold acallee_saved; lia)) R21)|].
split; [exact (eq_trans (HP 22 ltac:(unfold acallee_saved; lia)) R22)|].
split; [exact (eq_trans (HP 23 ltac:(unfold acallee_saved; lia)) R23)|].
split; [exact (eq_trans (HP 24 ltac:(unfold acallee_saved; lia)) R24)|].
split; [exact (eq_trans (HP 25 ltac:(unfold acallee_saved; lia)) R25)|].
split; [exact (eq_trans (HP 26 ltac:(unfold acallee_saved; lia)) R26)|].
exact (eq_trans (HP 27 ltac:(unfold acallee_saved; lia)) R27).
Qed.

Lemma s9S_kept : forall cx (rd rd' : reader) m, lt_base B MT cx -> s9S cx rd m ->
  (forall a, x_s1 cx <= a < x_sp0 cx -> rd' a = rd a) -> s9S cx rd' m.
Proof.
intros cx rd rd' m HB H K. pose proof (s9_base_facts B MT cx HB) as (_ & _ & _ & Hs1 & _ & _).
unfold LT_FRAME in Hs1. unfold s9S in *. apply (s9_rdword_kept _ _ _ _ H). intros x Hx. apply K. lia.
Qed.

Lemma s9_apost_true : forall STK FP regs ly S (W : world SEGS) mem md k Q W' c',
  apost_base SEGS B STK FP regs ly S W mem md k Q W' c' ->
  apost_base SEGS B STK FP regs ly S W mem md k (fun a b d e f g => True /\ Q a b d e f g) W' c'.
Proof.
intros STK FP regs ly S W mem md k Q W' c' (ly' & S' & regs' & mem' & md' & Ec & HJ & HP & HQ).
exists ly', S', regs', mem', md'. split; [exact Ec|]. split; [exact HJ|]. split; [exact HP | split; [exact I | exact HQ]].
Qed.

(* a C string the reader block holds at p (or NULL): what check_model / check_provenance ask of it *)
Lemma s9_str_in_c : forall cx ly S W regs mem md k acc o c m (p : Z) (os : option (list Z)),
  s9M B MT cx ly S W regs mem md k acc o c m ->
  (forall s, os = Some s -> c <= p /\ p + Z.of_nat (length s) + 1 <= c + seg_spec.SEG_C_SIZE /\ (length s < 96)%nat) ->
  match os with
  | Some s => Z.of_nat (length s) + 1 < 2 ^ 32 /\ sa_heap B ly S p (Z.of_nat (length s) + 1) /\
              sa_addr (rdW W mem) p (Z.of_nat (length s) + 1)
  | None => True
  end.
Proof.
intros cx ly S W regs mem md k acc o c m p os HM Hb.
destruct os as [s|]; [|exact I]. destruct (Hb s eq_refl) as (H1 & H2 & H3).
destruct (s9_blocks cx ly S W regs mem md k acc o c m HM) as (_ & _ & _ & _ & _ & _ & _ & _ & Hch & _).
pose proof HM as (_ & (_ & _ & _ & Hca) & _).
split; [lia|]. split; [destruct Hch as (b & n & Hin & Hb1 & Hb2); exists b, n; split; [exact Hin | lia]|].
apply (s18_sa_addr_sub _ c seg_spec.SEG_C_SIZE); [exact Hca | lia | lia | lia].
Qed.

(* ---- one program call of S09 at sp = S1 (image A's S09 walk's s9_call_step / s9_call_step_w, over the kit's
   s9_call): the callee's statement, the return address BASE + ret, and the next point ---- *)
Lemma s9_step : forall cx ly S W regs mem md k acc o c m (regsc : bvmap 5 word) (A ret STK1 : Z)
  (FP1 : list (Z * Z)) (E : Z -> Prop) (Rpost : world SEGS -> bvmap 5 word -> (word -> option byte) -> Prop) Q,
  lt_base B MT cx -> s9M B MT cx ly S W regs mem md k acc o c m ->
  getr regsc 2 = getr regs 2 -> getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
  getr regsc 8 = getr regs 8 -> getr regsc 9 = getr regs 9 ->
  In STK1 LTOI_CALLEE_STKS ->
  getr regsc 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall a, inFP FP1 a -> x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
  (forall a, E a -> x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
  (forall ch, afn_pre SEGS B STK1 ly S W regsc mem md ch -> arodata_okP SEGS RLO_A RHI_A B (rdW W mem) ->
     st_nev S <= EV_MAX ->
     SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 A) mem (seg_rom SEGS)) md)
       (apost_base SEGS B STK1 FP1 regsc ly S W mem md 0
         (fun ly' S' W' regs' mem' md' => Rpost W' regs' mem' /\ sa_kept SEGS W mem W' mem' regsc STK1 E /\
            sa_noalloc B ly S ly' S'))) ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2, s9M B MT cx ly2 S2 W2 regs2 mem2 md2 k acc o c m ->
     aregs_preserved regsc regs2 -> Rpost W2 regs2 mem2 ->
     (forall a, x_s1 cx <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W mem a) ->
     (forall a, x_fr cx + FO_R <= a < x_fr cx + FO_R + 4 -> ~ inFP FP1 a -> rdW W2 mem2 a = rdW W mem a) ->
     SRr SEGS W2 (cfg_at SEGS (BASE + ret) regs2 mem2 md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 A) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regs mem md k acc o c m regsc A ret STK1 FP1 E Rpost Q HB HM E2 E3 E4 E8 E9 HIn P1 Hret Hret2 HFP HE
  HCALL HNEXT.
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBlo.
assert (HraT : YK0s.ret_ok (getr regsc 1)) by (rewrite P1; apply ret_ok_codeptr_v; lia).
assert (Hra4T : 4096 <= bv_unsigned (getr regsc 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
apply (s9_call B MT LAWS MTFL cx ly S W regs mem md k acc o c m regsc A STK1 FP1 0 E
  (fun ly' S' W' regs' mem' md' => Rpost W' regs' mem' /\ sa_kept SEGS W mem W' mem' regsc STK1 E /\
     sa_noalloc B ly S ly' S')
  (fun _ _ W' regs' mem' _ => Rpost W' regs' mem') Q HB HM E2 E3 E4 E8 E9 HraT Hra4T HIn eq_refl HFP HE).
- intros ch HPRE HRO Hnev. exact (HCALL ch HPRE HRO ltac:(lia)).
- intros ly' S' W' regs' mem' md' HQ. exact HQ.
- intros ly2 S2 W2 regs2 mem2 md2 HM2 HP2 HR2 HST KR. rewrite P1.
  exact (HNEXT ly2 S2 W2 regs2 mem2 md2 HM2 HP2 HR2 HST KR).
Qed.

(* a run that touches registers only (no region, no fact) *)
Ltac s9_pure_run W regs mem HS SHOK HJ HEI pc :=
  destruct (s9_seed0 pc W regs mem) as [HS SHOK];
  assert (HEI : img_env VAL A_LIM (s9_E0 regs)) by (unfold s9_E0; apply Eimg_env);
  unfold cfg_at, w64;
  paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1); [apply awr_ok_nil|].
Ltac s9_after_pure HS HF mdv EM HPR regs :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end;
  match goal with HF : frame_of _ _ _ _ |- _ =>
    assert (EM : ms_mem _ = _) by (apply (s9_nowin_kept _ _ _ HF)) end;
  pmkst HS;
  assert (HPR : aregs_preserved regs (ms_regs _))
    by (eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS); [exact (s9_E0_agree regs) | vm_compute; reflexivity]).
Ltac s9_target SS AF :=
  rewrite (SIGP SS ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])));
  replace (seg_af SS) with AF by (vm_compute; reflexivity).

(* 0x85664 .. 0x8566c: a0 = c (s11), a1 = &m->seg[i] (s3), jal reac_segconf_model; to 0x85670 *)
Lemma s9_T2 : forall i, S9_R3 i -> S9_R2 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HSS HR _.
pose proof HM as ((HFR & (HRO & _) & _ & _) & _). pose proof HFR as (HJ & _).
s9_pure_run W regs mem HS SHOK HJ HEI LO9_R2.
s9_after_pure HS HF mdv EM HPR regs.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
s9_target SS_reac_segconf_model AF_reac_segconf_model.
rewrite EM in HJ |- *.
rewrite (s9_E0_reg regs 27 27%bv eq_refl) in P10. rewrite (s9_E0_reg regs 19 19%bv eq_refl) in P11.
pose proof HR as (_ & R19 & _ & _ & _ & _ & _ & _ & R27). rewrite R27 in P10. rewrite R19 in P11.
pose proof (s9M_run B MT LAWS MTFL cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mem mdv HB HM HJ
  (fun a _ => eq_refl) (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (HQ & Hc64 & Hn64).
apply (s9_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_reac_segconf_model) LO9_R3
  STK_reac_segconf_model [] (fun _ => False)
  (fun _ r _ => getr r 10 = w64 (seg_spec.model_ptr c (x_rcF cx) (s9_nm cx i))) _
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R3; lia) eq_refl (fun a Ha => False_ind _ (inFP_nil a Ha)) (fun a Ha => False_ind _ Ha)).
- intros ch HPRE1 _ Hnev. exact (HMODEL fx ly S W (ms_regs ms) mem mdv ch c (seg_spec.mseg_addr m i) (x_rcF cx) (s9_nm cx i)
    HPRE1 HRO P10 Hc64 P11 Hn64 HQ ltac:(unfold EV_reac_segconf_model; lia)).
- intros ly2 S2 W2 regs2 mem2 md2 HM2 HP2 HR2 HST _.
  exact (HN cx ly2 S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2 (s9S_kept cx _ _ m HB HSS HST)
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) HR2).
Qed.

(* 0x85670 .. 0x85674: a1 = &m->seg[i], jal check_model (a0 = model_ptr); to 0x85678 *)
Lemma s9_T3 : forall i, S9_R4 i -> S9_R3 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HSS HR HX.
pose proof HM as ((HFR & (HRO & _) & _ & _) & _ & _ & _ & (HRC & _)). pose proof HFR as (HJ & _).
s9_pure_run W regs mem HS SHOK HJ HEI LO9_R3.
s9_after_pure HS HF mdv EM HPR regs.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
s9_target SS_check_model AF_check_model.
rewrite EM in HJ |- *.
rewrite (s9_E0_reg regs 10 10%bv eq_refl) in P10. rewrite (s9_E0_reg regs 19 19%bv eq_refl) in P11.
pose proof HR as (_ & R19 & _). rewrite HX in P10. rewrite R19 in P11.
pose proof (s9M_run B MT LAWS MTFL cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mem mdv HB HM HJ
  (fun a _ => eq_refl) (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (_ & Hc64 & Hn64).
destruct (s9_blocks cx ly S W regs mem md k acc LFO_R c m HM) as (_ & Hc16 & Hcp & Hcb & _).
destruct (s18_model_str _ _ _ (s9_nm cx i) HRC Hc16 Hcp) as [HSTR HB2].
pose proof (s18_ptr_rng _ _ _ (s9_nm cx i) HRC ltac:(lia)) as (Hp1 & _).
pose proof (s9_check_seg cx i Hi) as HCK. apply s18_check_seg_split in HCK. destruct HCK as (_ & HCK2 & _).
apply (s9_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_check_model) LO9_R4
  STK_check_model [] (fun _ => False) (fun _ _ _ => True) _
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R4; lia) eq_refl (fun a Ha => False_ind _ (inFP_nil a Ha)) (fun a Ha => False_ind _ Ha)).
- intros ch HPRE1 _ Hnev. eapply SRr_mono; [|intros W' c' _ H'; exact (s9_apost_true _ _ _ _ _ _ _ _ _ _ _ _ H')].
  assert (Hg64 : 0 <= seg_spec.model_ptr c (x_rcF cx) (s9_nm cx i) < 2 ^ 64)
    by (unfold x_rcF; unfold seg_spec.SEG_C_SIZE in *; lia).
  destruct (s9_want cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (Hw1 & Hw2 & Hw3 & Hw4).
  assert (HPRE : check_model_pre B ly S (rdW W mem) (seg_spec.model_ptr c (x_rcF cx) (s9_nm cx i))
    (seg_spec.mseg_addr m i) (SegModel.r_model (x_rcF cx) (s9_nm cx i)) (x_seg cx i)).
  { split; [exact Hw1|]. split; [exact Hw2|]. split; [exact Hw3|]. split; [exact Hw4|]. split; [exact HSTR|].
    split; [|exact HCK2].
    apply (s9_str_in_c cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m _ _ HM').
    intros s Hs. destruct (HB2 s Hs) as (h1 & h2 & h3). split; [exact h1|]. split; [exact h2 | lia]. }
  exact (HCMODEL fx ly S W (ms_regs ms) mem mdv ch _ _ _ _ HPRE1 HRO P10 Hg64 P11 Hn64 HPRE
    ltac:(unfold EV_check_model; lia)).
- intros ly2 S2 W2 regs2 mem2 md2 HM2 HP2 _ HST _.
  exact (HN cx ly2 S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2 (s9S_kept cx _ _ m HB HSS HST)
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) I).
Qed.

(* 0x85678 .. 0x85680: a0 = c, a1 = &m->seg[i], jal reac_segconf_ignored; to 0x85684 *)
Lemma s9_T4 : forall i, S9_R5 i -> S9_R4 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HSS HR _.
pose proof HM as ((HFR & (HRO & _) & _ & _) & _). pose proof HFR as (HJ & _).
s9_pure_run W regs mem HS SHOK HJ HEI LO9_R4.
s9_after_pure HS HF mdv EM HPR regs.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
s9_target SS_reac_segconf_ignored AF_reac_segconf_ignored.
rewrite EM in HJ |- *.
rewrite (s9_E0_reg regs 27 27%bv eq_refl) in P10. rewrite (s9_E0_reg regs 19 19%bv eq_refl) in P11.
pose proof HR as (_ & R19 & _ & _ & _ & _ & _ & _ & R27). rewrite R27 in P10. rewrite R19 in P11.
pose proof (s9M_run B MT LAWS MTFL cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mem mdv HB HM HJ
  (fun a _ => eq_refl) (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (HQ & Hc64 & Hn64).
apply (s9_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_reac_segconf_ignored) LO9_R5
  STK_reac_segconf_ignored [] (fun _ => False)
  (fun _ r _ => getr r 10 = w64 (seg_spec.b2z (SegModel.r_ignored (x_rcF cx) (s9_nm cx i)))) _
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R5; lia) eq_refl (fun a Ha => False_ind _ (inFP_nil a Ha)) (fun a Ha => False_ind _ Ha)).
- intros ch HPRE1 _ Hnev. exact (HIGN fx ly S W (ms_regs ms) mem mdv ch c (seg_spec.mseg_addr m i) (x_rcF cx) (s9_nm cx i)
    HPRE1 HRO P10 Hc64 P11 Hn64 HQ ltac:(unfold EV_reac_segconf_ignored; lia)).
- intros ly2 S2 W2 regs2 mem2 md2 HM2 HP2 HR2 HST _.
  exact (HN cx ly2 S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2 (s9S_kept cx _ _ m HB HSS HST)
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) HR2).
Qed.

(* 0x85684 .. 0x85688: a1 = &m->seg[i], jal check_ignore (a0 = r_ignored); to 0x8568c *)
Lemma s9_T5 : forall i, S9_R6 i -> S9_R5 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HSS HR HX.
pose proof HM as ((HFR & _) & _). pose proof HFR as (HJ & _).
s9_pure_run W regs mem HS SHOK HJ HEI LO9_R5.
s9_after_pure HS HF mdv EM HPR regs.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
s9_target SS_check_ignore AF_check_ignore.
rewrite EM in HJ |- *.
rewrite (s9_E0_reg regs 10 10%bv eq_refl) in P10. rewrite (s9_E0_reg regs 19 19%bv eq_refl) in P11.
pose proof HR as (_ & R19 & _). rewrite HX in P10. rewrite R19 in P11.
pose proof (s9M_run B MT LAWS MTFL cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mem mdv HB HM HJ
  (fun a _ => eq_refl) (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (_ & _ & Hn64).
pose proof (s9_check_seg cx i Hi) as HCK. apply s18_check_seg_split in HCK. destruct HCK as (_ & _ & HCK3 & _).
destruct (s9_want cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (Hw1 & Hw2 & Hw3 & Hw4).
apply (s9_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_check_ignore) LO9_R6
  STK_check_ignore [] (fun _ => False) (fun _ _ _ => True) _
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R6; lia) eq_refl (fun a Ha => False_ind _ (inFP_nil a Ha)) (fun a Ha => False_ind _ Ha)).
- intros ch HPRE1 _ Hnev. eapply SRr_mono; [|intros W' c' _ H'; exact (s9_apost_true _ _ _ _ _ _ _ _ _ _ _ _ H')].
  exact (HCIGN fx ly S W (ms_regs ms) mem mdv ch _ _ _ _ HPRE1 P10
    ltac:(unfold seg_spec.b2z; destruct (SegModel.r_ignored (x_rcF cx) (s9_nm cx i)); lia) P11 Hn64
    (conj Hw1 (conj Hw2 (conj Hw3 (conj Hw4 (conj eq_refl HCK3))))) ltac:(unfold EV_check_ignore; lia)).
- intros ly2 S2 W2 regs2 mem2 md2 HM2 HP2 _ HST _.
  exact (HN cx ly2 S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2 (s9S_kept cx _ _ m HB HSS HST)
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) I).
Qed.

(* 0x8568c .. 0x85694: a0 = c, a1 = &m->seg[i], jal reac_segconf_role_file; to 0x85698 *)
Lemma s9_T6 : forall i, S9_R7 i -> S9_R6 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HSS HR _.
pose proof HM as ((HFR & (HRO & _) & _ & _) & _). pose proof HFR as (HJ & _).
s9_pure_run W regs mem HS SHOK HJ HEI LO9_R6.
s9_after_pure HS HF mdv EM HPR regs.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
s9_target SS_reac_segconf_role_file AF_reac_segconf_role_file.
rewrite EM in HJ |- *.
rewrite (s9_E0_reg regs 27 27%bv eq_refl) in P10. rewrite (s9_E0_reg regs 19 19%bv eq_refl) in P11.
pose proof HR as (_ & R19 & _ & _ & _ & _ & _ & _ & R27). rewrite R27 in P10. rewrite R19 in P11.
pose proof (s9M_run B MT LAWS MTFL cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mem mdv HB HM HJ
  (fun a _ => eq_refl) (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (HQ & Hc64 & Hn64).
apply (s9_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_reac_segconf_role_file) LO9_R7
  STK_reac_segconf_role_file [] (fun _ => False)
  (fun _ r _ => getr r 10 = w64 (seg_spec.role_file_ptr c (x_rcF cx) (s9_nm cx i))) _
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R7; lia) eq_refl (fun a Ha => False_ind _ (inFP_nil a Ha)) (fun a Ha => False_ind _ Ha)).
- intros ch HPRE1 _ Hnev. exact (HRFILE fx ly S W (ms_regs ms) mem mdv ch c (seg_spec.mseg_addr m i) (x_rcF cx)
    (s9_nm cx i) HPRE1 HRO P10 Hc64 P11 Hn64 HQ ltac:(unfold EV_reac_segconf_role_file; lia)).
- intros ly2 S2 W2 regs2 mem2 md2 HM2 HP2 HR2 HST _.
  exact (HN cx ly2 S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2 (s9S_kept cx _ _ m HB HSS HST)
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) HR2).
Qed.

Lemma s9R_of_eq : forall cx i regs regs2 c m, s9R cx i regs c m ->
  getr regs2 18 = getr regs 18 -> getr regs2 19 = getr regs 19 -> getr regs2 21 = getr regs 21 ->
  getr regs2 22 = getr regs 22 -> getr regs2 23 = getr regs 23 -> getr regs2 24 = getr regs 24 ->
  getr regs2 25 = getr regs 25 -> getr regs2 26 = getr regs 26 -> getr regs2 27 = getr regs 27 -> s9R cx i regs2 c m.
Proof.
intros cx i regs regs2 c m (R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27) E18 E19 E21 E22 E23 E24 E25 E26 E27.
split; [rewrite E18; exact R18|]. split; [rewrite E19; exact R19|]. split; [rewrite E21; exact R21|].
split; [rewrite E22; exact R22|]. split; [rewrite E23; exact R23|]. split; [rewrite E24; exact R24|].
split; [rewrite E25; exact R25|]. split; [rewrite E26; exact R26 | rewrite E27; exact R27].
Qed.

(* 0x85698 .. 0x856a4: s4 = a0 (role_file_ptr), a0 = c, a1 = &m->seg[i], jal reac_segconf_ignore_file; to 0x856a8 *)
Lemma s9_T7 : forall i, S9_R8 i -> S9_R7 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HSS HR HX.
pose proof HM as ((HFR & (HRO & _) & _ & _) & _). pose proof HFR as (HJ & _).
s9_pure_run W regs mem HS SHOK HJ HEI LO9_R7.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (EM : ms_mem ms = mem) by exact (s9_nowin_kept _ _ _ HF).
pmkst HS. prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
rewrite (s9_E0_reg regs 27 27%bv eq_refl) in P10. rewrite (s9_E0_reg regs 19 19%bv eq_refl) in P11.
rewrite (s9_E0_reg regs 2 2%bv eq_refl) in P2. rewrite (s9_E0_reg regs 3 3%bv eq_refl) in P3.
rewrite (s9_E0_reg regs 4 4%bv eq_refl) in P4. rewrite (s9_E0_reg regs 8 8%bv eq_refl) in P8.
rewrite (s9_E0_reg regs 9 9%bv eq_refl) in P9. rewrite (s9_E0_reg regs 18 18%bv eq_refl) in P18.
rewrite (s9_E0_reg regs 19 19%bv eq_refl) in P19. rewrite (s9_E0_reg regs 10 10%bv eq_refl) in P20.
rewrite (s9_E0_reg regs 21 21%bv eq_refl) in P21. rewrite (s9_E0_reg regs 22 22%bv eq_refl) in P22.
rewrite (s9_E0_reg regs 23 23%bv eq_refl) in P23. rewrite (s9_E0_reg regs 24 24%bv eq_refl) in P24.
rewrite (s9_E0_reg regs 25 25%bv eq_refl) in P25. rewrite (s9_E0_reg regs 26 26%bv eq_refl) in P26.
rewrite (s9_E0_reg regs 27 27%bv eq_refl) in P27.
s9_target SS_reac_segconf_ignore_file AF_reac_segconf_ignore_file.
rewrite EM in HJ |- *.
pose proof (s9R_of_eq cx i regs (ms_regs ms) c m HR P18 P19 P21 P22 P23 P24 P25 P26 P27) as HR'.
pose proof HR as (_ & R19 & _ & _ & _ & _ & _ & _ & R27). rewrite R27 in P10. rewrite R19 in P11. rewrite HX in P20.
pose proof (s9M_run B MT LAWS MTFL cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mem mdv HB HM HJ
  (fun a _ => eq_refl) P2 P3 P4 P8 P9) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (HQ & Hc64 & Hn64).
apply (s9_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_reac_segconf_ignore_file) LO9_R8
  STK_reac_segconf_ignore_file [] (fun _ => False)
  (fun _ r _ => getr r 10 = w64 (seg_spec.ignore_file_ptr c (x_rcF cx) (s9_nm cx i))) _
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R8; lia) eq_refl (fun a Ha => False_ind _ (inFP_nil a Ha)) (fun a Ha => False_ind _ Ha)).
- intros ch HPRE1 _ Hnev. exact (HIFILE fx ly S W (ms_regs ms) mem mdv ch c (seg_spec.mseg_addr m i) (x_rcF cx)
    (s9_nm cx i) HPRE1 HRO P10 Hc64 P11 Hn64 HQ ltac:(unfold EV_reac_segconf_ignore_file; lia)).
- intros ly2 S2 W2 regs2 mem2 md2 HM2 HP2 HR2 HST _.
  apply (HN cx ly2 S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2 (s9S_kept cx _ _ m HB HSS HST)
    (s9R_pres cx i (ms_regs ms) regs2 c m HR' HP2)).
  split; [exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) P20) | exact HR2].
Qed.

(* 0x856a8 .. 0x856b4: a1 = ignore_file_ptr, a0 = s4 (role_file_ptr), a2 = &m->seg[i], jal check_provenance;
   to 0x856b8 *)
Lemma s9_T8 : forall i, S9_R9 i -> S9_R8 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HSS HR (HX20 & HX10).
pose proof HM as ((HFR & (HRO & _) & _ & _) & _ & _ & _ & (HRC & _)). pose proof HFR as (HJ & _).
s9_pure_run W regs mem HS SHOK HJ HEI LO9_R8.
s9_after_pure HS HF mdv EM HPR regs.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
s9_target SS_check_provenance AF_check_provenance.
rewrite EM in HJ |- *.
rewrite (s9_E0_reg regs 20 20%bv eq_refl) in P10. rewrite (s9_E0_reg regs 10 10%bv eq_refl) in P11.
rewrite (s9_E0_reg regs 19 19%bv eq_refl) in P12.
pose proof HR as (_ & R19 & _). rewrite HX20 in P10. rewrite HX10 in P11. rewrite R19 in P12.
pose proof (s9M_run B MT LAWS MTFL cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mem mdv HB HM HJ
  (fun a _ => eq_refl) (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (_ & _ & Hn64).
destruct (s9_blocks cx ly S W regs mem md k acc LFO_R c m HM) as (_ & Hc16 & Hcp & Hcb & _).
destruct (s18_role_file_str _ _ _ (s9_nm cx i) HRC Hc16 Hcp) as [HSTR1 HB1].
destruct (s18_ignore_file_str _ _ _ (s9_nm cx i) HRC Hc16 Hcp) as [HSTR2 HB2].
pose proof (s18_ptr_rng _ _ _ (s9_nm cx i) HRC ltac:(lia)) as (_ & Hp1 & Hp2).
pose proof (s9_check_seg cx i Hi) as HCK. apply s18_check_seg_split in HCK. destruct HCK as (_ & _ & _ & HCK4 & HCK5).
apply (s9_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_check_provenance) LO9_R9
  STK_check_provenance [] (fun _ => False) (fun _ _ _ => True) _
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R9; lia) eq_refl (fun a Ha => False_ind _ (inFP_nil a Ha)) (fun a Ha => False_ind _ Ha)).
- intros ch HPRE1 _ Hnev. eapply SRr_mono; [|intros W' c' _ H'; exact (s9_apost_true _ _ _ _ _ _ _ _ _ _ _ _ H')].
  assert (Hg1 : 0 <= seg_spec.role_file_ptr c (x_rcF cx) (s9_nm cx i) < 2 ^ 64)
    by (unfold x_rcF; unfold seg_spec.SEG_C_SIZE in *; lia).
  assert (Hg2 : 0 <= seg_spec.ignore_file_ptr c (x_rcF cx) (s9_nm cx i) < 2 ^ 64)
    by (unfold x_rcF; unfold seg_spec.SEG_C_SIZE in *; lia).
  destruct (s9_want cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (Hw1 & Hw2 & Hw3 & Hw4).
  assert (HPRE : check_provenance_pre B ly S (rdW W mem) (seg_spec.role_file_ptr c (x_rcF cx) (s9_nm cx i))
    (seg_spec.ignore_file_ptr c (x_rcF cx) (s9_nm cx i)) (seg_spec.mseg_addr m i)
    (SegModel.r_role_file (x_rcF cx) (s9_nm cx i)) (SegModel.r_ignore_file (x_rcF cx) (s9_nm cx i)) (x_seg cx i)).
  { split; [exact Hw1|]. split; [exact Hw2|]. split; [exact Hw3|]. split; [exact Hw4|]. split; [exact HSTR1|].
    split; [apply (s9_str_in_c cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m _ _ HM'); exact HB1|].
    split; [exact HSTR2|].
    split; [apply (s9_str_in_c cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m _ _ HM'); exact HB2|].
    split; [exact HCK4 | exact HCK5]. }
  exact (HCPROV fx ly S W (ms_regs ms) mem mdv ch _ _ _ _ _ _ HPRE1 HRO P10 Hg1 P11 Hg2 P12 Hn64 HPRE
    ltac:(unfold EV_check_provenance; lia)).
- intros ly2 S2 W2 regs2 mem2 md2 HM2 HP2 _ HST _.
  exact (HN cx ly2 S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2 (s9S_kept cx _ _ m HB HSS HST)
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) I).
Qed.

(* r's value is a 31-bit number: the role (SegModel's role field is below 2 ^ 31) or the stored 0x5a *)
Lemma s9_rval_rng : forall cx ly S W regs mem md k acc o c m i, s9M B MT cx ly S W regs mem md k acc o c m ->
  0 <= s9_rval cx i < 2 ^ 31.
Proof.
intros cx ly S W regs mem md k acc o c m i HM. pose proof HM as (_ & _ & _ & _ & (HRC & _)).
unfold s9_rval. destruct (SegModel.r_role (x_rcF cx) (s9_nm cx i)) as [v|] eqn:Ev; [|lia].
exact (s18_role_rng _ _ _ _ _ HRC Ev).
Qed.

(* ---- the seed at 0x85658: r (4 bytes at s4 = FR + 176) holds r's value, atom 32 ---- *)
Definition s9_ssR1 : sstate := mkSS LO9_R1 sr_atoms
  [ YP09.mkRegion (Some 20%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))] ] None
  (mkFacts [(32%nat, mkAF 0 (2 ^ 31 - 1) 0)] [] []).
Definition s9_ER1 (regs : bvmap 5 word) (v : Z) : env := Eimg (Ereg regs [w64 v]).
Lemma s9_seedR1 : forall cx (W : world SEGS) regs mem v,
  getr regs 20 = w64 (x_fr cx + FO_R) -> 0 <= x_fr cx + FO_R < 2 ^ 47 ->
  sa_val (rdW W mem) (x_fr cx + FO_R) 4 v -> 0 <= v < 2 ^ 31 ->
  st_ok_pi SEGS VAL (s9_ER1 regs v) s9_ssR1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO9_R1)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 9 0) [] (s9_ER1 regs v) (mrestrict (w_H W) mem).
Proof.
intros cx W regs mem v R20 Hfr Hv Hv31.
assert (E20 : ew (s9_ER1 regs v) 20 = w64 (x_fr cx + FO_R)).
{ unfold s9_ER1. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl). exact R20. }
assert (E32 : ew (s9_ER1 regs v) 32 = w64 v).
{ unfold s9_ER1. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
split; [|apply Forall_nil].
unfold s9_ssR1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s9_ER1. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E20. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (x_fr cx + FO_R) 0 4 _ v);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
  rewrite Z.add_0_r. exact (s9_val_of_rd _ _ _ _ _ Hv).
- cbn. tauto.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia.
  change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
Qed.

(* 0x85658 .. 0x85660: a1 = r (lw 0(s4)), a2 = &m->seg[i], jal check_role (a0 = the role's answer); to 0x85664 *)
Lemma s9_T1 : forall i, S9_R2 i -> S9_R1 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HSS HR (HX20 & HX10 & HXr).
pose proof HM as ((HFR & _) & _). pose proof HFR as (HJ & _).
destruct (s9_frame_at B MT LAWS cx ly S W mem md k HB HJ) as (_ & _ & _ & _ & Hf4 & Hfc & _).
pose proof asan_consts as (C1 & _).
pose proof (s9_rval_rng cx ly S W regs mem md k acc LFO_R c m i HM) as Hv31.
destruct (s9_seedR1 cx W regs mem (s9_rval cx i) HX20 ltac:(unfold FO_R; lia) HXr Hv31) as [HS SHOK].
set (E := s9_ER1 regs (s9_rval cx i)) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, s9_ER1; apply Eimg_env).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs [w64 (s9_rval cx i)]) q)
  by (intros q Hq; unfold E, s9_ER1; apply Eimg_low; exact Hq).
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (EM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r0 & Hr0 & Hw). cbn [s9_ssR1 ss_mem In] in Hr0.
  destruct Hr0 as [<-|[]]. cbn in Hw. lia. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [w64 (s9_rval cx i)] HS); [|vm_compute; reflexivity].
  split; [intros q Hq; unfold E, s9_ER1; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
s9_target SS_check_role AF_check_role.
rewrite EM in HJ |- *.
rewrite EL in P10, P11, P12 by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl) in P10. rewrite (ew_Ereg_extra regs _ 0) in P11.
rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl) in P12.
pose proof HR as (_ & R19 & _). rewrite HX10 in P10. rewrite R19 in P12. cbn [nth] in P11.
pose proof (s9M_run B MT LAWS MTFL cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mem mdv HB HM HJ
  (fun a _ => eq_refl) (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (_ & _ & Hn64).
destruct (s9_want cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (Hw1 & Hw2 & Hw3 & Hw4).
pose proof (s9_check_seg cx i Hi) as HCK. apply s18_check_seg_split in HCK. destruct HCK as (HCK1 & _).
change (SegModel.ms_name (x_seg cx i)) with (s9_nm cx i) in HCK1.
apply (s9_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_check_role) LO9_R2
  STK_check_role [] (fun _ => False) (fun _ _ _ => True) _
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R2; lia) eq_refl (fun a Ha => False_ind _ (inFP_nil a Ha)) (fun a Ha => False_ind _ Ha)).
- intros ch HPRE1 _ Hnev. eapply SRr_mono; [|intros W' c' _ H'; exact (s9_apost_true _ _ _ _ _ _ _ _ _ _ _ _ H')].
  assert (HPRE : check_role_pre B ly S (rdW W mem) (s9_rset cx i) (s9_rval cx i) (seg_spec.mseg_addr m i)
    (SegModel.r_role (x_rcF cx) (s9_nm cx i)) (x_seg cx i)).
  { split; [exact Hw1|]. split; [exact Hw2|]. split; [exact Hw3|]. split; [exact Hw4|].
    unfold s9_rset, s9_rval in *.
    destruct (SegModel.r_role (x_rcF cx) (s9_nm cx i)) as [v|];
      (split; [reflexivity | split; [|exact HCK1]]); [split; [reflexivity | lia] | exact I]. }
  exact (HCROLE fx ly S W (ms_regs ms) mem mdv ch _ _ _ _ _ HPRE1 P10
    ltac:(unfold s9_rset; destruct (SegModel.r_role (x_rcF cx) (s9_nm cx i)); lia) P11 ltac:(lia) P12 Hn64 HPRE
    ltac:(unfold EV_check_role; lia)).
- intros ly2 S2 W2 regs2 mem2 md2 HM2 HP2 _ HST _.
  exact (HN cx ly2 S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2 (s9S_kept cx _ _ m HB HSS HST)
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) I).
Qed.

(* ---- reading a stored chunk back byte by byte (image A's S09 walk's s9_chunk_rd), at a running state or at a
   call ---- *)
Lemma s9_chunk_rd_ok : forall E ss (H : word -> bool) ms i r off (w : N) e j,
  st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) -> 0 <= j < Z.of_N w ->
  aview SEGS H (ms_mem ms) (base_val E (YP09.r_base r) + off + j) = Some (bv_unsigned (byte_of_word (sv_denot E e) j)).
Proof.
intros E ss H ms i r off w e j HS Hi Hc Hj.
pose proof (st_ok_region_nth E ss (restrict H ms) i r HS Hi) as HR.
pose proof (region_ok_chunk SEGS E _ r _ HR Hc) as HC.
destruct (HC j ltac:(cbn; lia)) as (b & Hb & Hm). cbn in Hb. injection Hb as <-.
unfold aview. cbn [YP09.c_off] in Hm. change (ms_mem (restrict H ms)) with (mrestrict H (ms_mem ms)) in Hm.
rewrite Hm. reflexivity.
Qed.
Lemma s9_chunk_rd : forall E ss (H : word -> bool) ms i r off (w : N) e j,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) -> 0 <= j < Z.of_N w ->
  aview SEGS H (ms_mem ms) (base_val E (YP09.r_base r) + off + j) = Some (bv_unsigned (byte_of_word (sv_denot E e) j)).
Proof.
intros E ss H ms i r off w e j HS Hi.
exact (s9_chunk_rd_ok E (abs_ss VAL ss) H ms i r off w e j HS ltac:(destruct ss; exact Hi)).
Qed.

(* ---- the seed at the loop head 0x85630: s1's slots 112 (&r = FR + 176, atom 32) and 208 (~M, atom 33); r's
   shadow byte SH(FR) + 22 and r, both written by the run; s6 = 33, s7 = 4, s8 = 90 pinned; s2 = 256 i and s5 = i
   in range (UBSan's index test `beq s5,s6` and pointer test `bltu ~M,s2` are decided by them) ---- *)
Definition s9_ssL : sstate := mkSS LO9_LOOP
  (sr_set (sr_set (sr_set sr_atoms 22%bv (SLit 33)) 23%bv (SLit 4)) 24%bv (SLit 90))
  [ YP09.mkRegion (Some 9%nat) 112 120 112 112 [YP09.mkChunk 112 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 9%nat) 208 216 208 208 [YP09.mkChunk 208 (CVal 8 (SOff 33 0))];
    YP09.mkRegion (Some 25%nat) 22 23 22 23 [];
    YP09.mkRegion (Some 32%nat) 0 4 0 4 [] ] None
  (mkFacts [(18%nat, mkAF 0 7936 0); (21%nat, mkAF 0 31 0); (25%nat, mkAF 0x7fff8000 (0x7fff8000 + 2 ^ 44) 0);
            (32%nat, mkAF 4096 (2 ^ 47) 0); (33%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0)] [] []).
Definition s9_ssL0 : sstate := mkSS LO9_LOOP sr_atoms (ss_mem s9_ssL) None (ss_facts s9_ssL).
Definition s9_EL (regs : bvmap 5 word) (cx : lcx) (m : Z) : env := Eimg (Ereg regs [w64 (x_fr cx + FO_R); w64 (lt_not m)]).
Lemma s9_seedL : forall cx ly S W regs mem md k acc c m i,
  lt_base B MT cx -> s9M B MT cx ly S W regs mem md k acc LFO0 c m -> s9R cx i regs c m -> (i < 32)%nat ->
  st_ok_pi SEGS VAL (s9_EL regs cx m) s9_ssL
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO9_LOOP)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 9 0) [] (s9_EL regs cx m) (mrestrict (w_H W) mem).
Proof.
intros cx ly S W regs mem md k acc c m i HB HM HR Hi32.
pose proof (s9_base_facts B MT cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
pose proof HM as ((HFR & _) & _ & (Hmin & Hm4 & _) & HSL & _). destruct HFR as (HJ & _ & _ & _ & _ & R9 & _).
destruct (s9_frame_at B MT LAWS cx ly S W mem md k HB HJ) as (HAR & Hin & EF & Hfa & Hf4 & Hfc & Happ).
pose proof (al_frames _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & _ & HFP & HSP).
rewrite <- EF in HFP, HSP. change (fs_frame_bytes LT_FCLS) with 512 in HFP, HSP.
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & _ & Hmc & _).
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc.
pose proof HR as (R18 & _ & R21 & R22 & R23 & R24 & R25 & _).
pose proof asan_consts as (C1 & _).
assert (Hsh : x_sh cx = 0x7fff8000 + x_fr cx / 8) by (unfold x_sh, shadow_addr, SHADOW_OFF; lia).
assert (Hshr : 0x7fff8000 <= x_sh cx < 0x7fff8000 + 2 ^ 44).
{ rewrite Hsh. split; [pose proof (Z.div_pos (x_fr cx) 8); lia|].
  assert (x_fr cx / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
set (E := s9_EL regs cx m).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs [w64 (x_fr cx + FO_R); w64 (lt_not m)]) q)
  by (intros q Hq; unfold E, s9_EL; apply Eimg_low; exact Hq).
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 (256 * Z.of_nat i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E21 : ew E 21 = w64 (Z.of_nat i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E25 : ew E 25 = w64 (x_sh cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew E 32 = w64 (x_fr cx + FO_R)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (lt_not m)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (SL : forall o v, In (o, v) (LS9 cx c m) -> val_mem SEGS (mrestrict (w_H W) mem) (x_s1 cx + o) 8 v)
  by (intros o v Hin'; apply (val_mem_of_rdword SEGS); exact (HSL o v Hin')).
assert (HS0 : st_ok_pi SEGS VAL E s9_ssL0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO9_LOOP)) mem (seg_rom SEGS)))).
{ unfold s9_ssL0, s9_ssL. cbn [ss_mem ss_facts]. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold E, s9_EL. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E9. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (x_s1 cx) 112 8 _ (x_fr cx + FO_R));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold FO_R; lia | lia
        | exact (SL 112 _ ltac:(unfold LS9; apply in_or_app; right; cbn [In]; tauto))].
    * rewrite E9. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (x_s1 cx) 208 8 _ (lt_not m));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold lt_not, seg_spec.SEG_M_SIZE in *; lia | lia
        | exact (SL 208 _ ltac:(unfold LS9, LT_LC; cbn [In app]; tauto))].
    * rewrite E25. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace o with 22 by lia. apply (apresent_writable SEGS).
      replace (x_sh cx + 22) with (shadow_addr (x_fr cx) + 22) by reflexivity. exact (proj1 (HSP 22 ltac:(lia))).
    * rewrite E32. unfold w64. rewrite unsigned_lit_small by (unfold FO_R; lia).
      split; [unfold FO_R; lia|]. split; [unfold FO_R; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFP (x_fr cx + FO_R + o) ltac:(unfold FO_R; lia))).
  + apply pairwise_disjoint_of_extents.
    unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E25, E32. unfold w64. rewrite !unsigned_lit_small by (unfold FO_R; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold FO_R.
    destruct Happ as (_ & [Hl | (Hh & _)]); unfold kLowShadowBeg, kHighMemBeg in *; repeat split; lia.
  + split; [|split; exact I].
    cbn [f_atoms atoms_ok]. split; [|split; [|split; [|split; [|split; [|exact I]]]]];
      unfold afact_ok; cbn [af_lo af_hi af_al2]; change (2 ^ 0) with 1; rewrite ?Z.mod_1_r.
    * rewrite E18. unfold w64. rewrite unsigned_lit_small by lia. lia.
    * rewrite E21. unfold w64. rewrite unsigned_lit_small by lia. lia.
    * rewrite E25. unfold w64. rewrite unsigned_lit_small by lia. lia.
    * rewrite E32. unfold w64. rewrite unsigned_lit_small by (unfold FO_R; lia). unfold FO_R. lia.
    * rewrite E33. unfold w64. rewrite unsigned_lit_small by (unfold lt_not, seg_spec.SEG_M_SIZE in *; lia).
      unfold lt_not, seg_spec.SEG_M_SIZE in *. lia. }
split; [|apply Forall_nil].
pose proof (st_ok_pi_pin_reg' _ _ _ 22%bv 33 HS0 R22 eq_refl) as HS1.
pose proof (st_ok_pi_pin_reg' _ _ _ 23%bv 4 HS1 R23 eq_refl) as HS2.
exact (st_ok_pi_pin_reg' _ _ _ 24%bv 90 HS2 R24 eq_refl).
Qed.

(* 0x85630 .. 0x85654: UBSan's index and pointer tests (not taken), r's shadow byte := 4 (r in scope), r := 0x5a,
   a0 = c, a1 = &m->seg[i], a2 = &r, jal reac_segconf_role; to 0x85658 *)
Lemma s9_T0 : forall i, S9_R1 i -> S9_loop_stmt i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HSS HR.
pose proof HM as ((HFR & (HRO & _) & _ & _) & _ & _ & _ & (HRC & HMC)). pose proof HFR as (HJ & _).
pose proof (s18_mconf_len _ _ _ HMC) as Hl32. fold (x_mcF cx) in Hl32.
destruct (s9_frame_at B MT LAWS cx ly S W mem md k HB HJ) as (HAR & Hin & EF & Hfa & Hf4 & Hfc & Happ).
pose proof asan_consts as (C1 & _).
assert (Hsh : x_sh cx = 0x7fff8000 + x_fr cx / 8) by (unfold x_sh, shadow_addr, SHADOW_OFF; lia).
assert (Hshr : 0x7fff8000 <= x_sh cx < 0x7fff8000 + 2 ^ 44).
{ rewrite Hsh. split; [pose proof (Z.div_pos (x_fr cx) 8); lia|].
  assert (x_fr cx / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
destruct (s9_seedL cx ly S W regs mem md k acc c m i HB HM HR ltac:(lia)) as [HS SHOK].
set (E := s9_EL regs cx m) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, s9_EL; apply Eimg_env).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs [w64 (x_fr cx + FO_R); w64 (lt_not m)]) q)
  by (intros q Hq; unfold E, s9_EL; apply Eimg_low; exact Hq).
pose proof HR as (R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
assert (E25 : ew E 25 = w64 (x_sh cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew E 32 = w64 (x_fr cx + FO_R)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK (0, 0).
{ unfold s9_ssL. cbn [ss_mem].
  do 2 (apply awr_ok_cons_ro; [cbn; lia|]).
  eapply awr_ok_cons_gen with (n := 25%nat) (b := x_sh cx); [reflexivity | rewrite E25; unfold w64; apply unsigned_lit_small; lia | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite <- EF.
    change (fs_frame_bytes LT_FCLS / 8) with 64. unfold x_sh in Ha. lia. }
  eapply awr_ok_cons_gen with (n := 32%nat) (b := x_fr cx + FO_R);
    [reflexivity | rewrite E32; unfold w64; apply unsigned_lit_small; unfold FO_R; lia | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite <- EF.
    change (fs_frame_bytes LT_FCLS) with 512. unfold FO_R in Ha. lia. }
  apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
(* the run stored r's shadow byte and r only *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> x_sh cx + 22 -> ~ (x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
  rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha H22 Hr. apply s9_aview_pt. apply HF. rewrite unsigned_lit_small by lia.
  intros (r0 & Hr0 & Hw). unfold s9_ssL in Hr0. cbn [ss_mem In] in Hr0.
  destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]]; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; [lia | lia | |].
  - rewrite E25 in Hw. unfold w64 in Hw. rewrite unsigned_lit_small in Hw by lia. lia.
  - rewrite E32 in Hw. unfold w64 in Hw. rewrite unsigned_lit_small in Hw by (unfold FO_R; lia). lia. }
assert (H4 : rdW W (ms_mem ms) (x_sh cx + 22) = Some 4).
{ pose proof (s9_chunk_rd_ok E _ (w_H W) ms 2 _ 22 1 (SLit 4) 0 HS eq_refl (or_introl eq_refl) ltac:(lia)) as Hc.
  cbn [base_val YP09.r_base] in Hc. rewrite E25 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
  rewrite Z.add_0_r in Hc. rewrite Hc. reflexivity. }
assert (H90 : sa_val (rdW W (ms_mem ms)) (x_fr cx + FO_R) 4 90).
{ intros j Hj.
  pose proof (s9_chunk_rd_ok E _ (w_H W) ms 3 _ 0 4 (SLit 90) (Z.of_nat j) HS eq_refl (or_introl eq_refl) ltac:(cbn; lia)) as Hc.
  cbn [base_val YP09.r_base] in Hc. rewrite E32 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by (unfold FO_R; lia).
  rewrite Z.add_0_r in Hc. rewrite Hc. f_equal.
  all: do 4 (destruct j as [|j]; [reflexivity|]); lia. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
rewrite E32 in P12, P20.
rewrite EL in P10, P11, P2, P3, P4, P8, P9, P18, P19, P21, P25, P26, P27 by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl) in P10. rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl) in P11.
rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in P2. rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl) in P3.
rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl) in P4. rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl) in P8.
rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl) in P9. rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl) in P18.
rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl) in P19. rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl) in P21.
rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl) in P25. rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl) in P26.
rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl) in P27.
rewrite R27 in P10. rewrite R19 in P11.
pose proof (s9R_of_eq cx i regs (ms_regs ms) c m HR P18 P19 P21 (eq_trans P22 (eq_sym R22)) (eq_trans P23 (eq_sym R23))
  (eq_trans P24 (eq_sym R24)) P25 P26 P27) as HR'.
s9_target SS_reac_segconf_role AF_reac_segconf_role.
destruct (s9_agree_win B MT LAWS cx ly S W regs mem md k acc LFO0 c m W (ms_mem ms) HB HM KM) as [HAG HST0].
pose proof (s9M_agree B MT LAWS MTFL cx ly S W regs mem md k acc LFO0 LFO_R c m ly S W (ms_regs ms) (ms_mem ms) mdv
  HB HM HJ P2 P3 P4 P8 P9 HAG H4 eq_refl eq_refl eq_refl eq_refl (Permutation_refl _) (or_introl eq_refl)) as HM'.
pose proof (s9S_kept cx _ _ m HB HSS HST0) as HSS'.
destruct (s9_query_pre cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO_R c m i HM' Hi) as (HQ & Hc64 & Hn64).
set (out := x_fr cx + FO_R) in *.
assert (Hout : 0 <= out < 2 ^ 64) by (unfold out, FO_R; lia).
assert (Hout0 : out <> 0) by (unfold out, FO_R; lia).
assert (HPRE : reac_segconf_role_c.role_pre SEGS B ly S W (ms_mem ms) (ms_regs ms) c (seg_spec.mseg_addr m i) out
  (x_rcF cx) (s9_nm cx i)).
{ split; [exact HQ|]. right. split; [unfold out, FO_R; Z.div_mod_to_equations; lia|]. left. split.
  - exists LT_FCLS, (x_fpos cx). split; [exact Hin|]. split; [vm_compute; discriminate|].
    rewrite <- EF. change (fs_frame_bytes LT_FCLS) with 512. unfold out, FO_R. lia.
  - intros x Hx. exists 4. split; [|right; split; [unfold out, FO_R in Hx; Z.div_mod_to_equations; lia | lia]].
    replace (shadow_of_addr SHADOW_OFF x) with (x_sh cx + 22); [exact H4|].
    unfold shadow_of_addr, x_sh, shadow_addr, out, FO_R in *. Z.div_mod_to_equations. lia. }
apply (s9_step cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_reac_segconf_role) LO9_R1
  STK_reac_segconf_role (reac_segconf_role_c.role_W out (SegModel.r_role (x_rcF cx) (s9_nm cx i)))
  (fun a => out <> 0 /\ out <= a < out + 4)
  (fun W' regs' mem' => getr regs' 10 = w64 (match SegModel.r_role (x_rcF cx) (s9_nm cx i) with Some _ => 1 | None => 0 end) /\
     (match SegModel.r_role (x_rcF cx) (s9_nm cx i) with
      | Some v => out <> 0 -> sa_val (rdW W' mem') out 4%nat v
      | None => True
      end)) _
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R1; lia) eq_refl).
- intros a Ha. unfold reac_segconf_role_c.role_W in Ha.
  destruct (SegModel.r_role (x_rcF cx) (s9_nm cx i)); [|exact (False_ind _ (inFP_nil a Ha))].
  replace (out =? 0) with false in Ha by (symmetry; apply Z.eqb_neq; exact Hout0).
  destruct Ha as (r0 & [<-|[]] & Hr). cbn [fst snd] in Hr. unfold out in Hr. lia.
- intros a (_ & Ha). unfold out in Ha. lia.
- intros ch HPRE1 HRO1 Hnev.
  eapply SRr_mono; [exact (HROLE fx ly S W (ms_regs ms) (ms_mem ms) mdv ch c (seg_spec.mseg_addr m i) out (x_rcF cx)
    (s9_nm cx i) HPRE1 HRO1 P10 Hc64 P11 Hn64 P12 Hout HPRE ltac:(unfold EV_reac_segconf_role; lia))|].
  intros W' c' _ (ly' & S' & regs' & mem' & md' & Ec & HJ' & HP' & (Q1 & Q2 & Q3)).
  exists ly', S', regs', mem', md'. split; [exact Ec|]. split; [exact HJ'|]. split; [exact HP'|].
  split; [split; [exact Q1 | exact Q2] | exact Q3].
- intros ly2 S2 W2 regs2 mem2 md2 HM2 HP2 (HR10 & HRv) HST KR.
  apply (HN cx ly2 S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2 (s9S_kept cx _ _ m HB HSS' HST)
    (s9R_pres cx i (ms_regs ms) regs2 c m HR' HP2)).
  split; [exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) P20)|].
  split; [unfold s9_rset; exact HR10|].
  unfold s9_rval. destruct (SegModel.r_role (x_rcF cx) (s9_nm cx i)) as [v|] eqn:Ev; [exact (HRv Hout0)|].
  intros j Hj. change (x_fr cx + FO_R) with out.
  rewrite (KR (out + Z.of_nat j)); [exact (H90 j Hj) | unfold out; lia |].
  try rewrite Ev. unfold reac_segconf_role_c.role_W. exact (inFP_nil _).
Qed.

(* ---- the seed at 0x856b8 (check_provenance returned): r's shadow byte SH(FR) + 22 (written), 176(s1) =
   SH(m + 0x2000) (atom 32) and that shadow byte, 0 (check 19 reads it); 216(s1) = m + 0x2000 (atom 33) and m->n
   (atom 34, at least 1); s10 = -8 pinned; s5 = i in range; cs the outcome of `blt` the caller knows ---- *)
Definition s9_ssT (cs : list acond) : sstate := mkSS LO9_R9 (sr_set sr_atoms 26%bv (SLit 18446744073709551608))
  [ YP09.mkRegion (Some 25%nat) 22 23 22 23 [];
    YP09.mkRegion (Some 9%nat) 176 184 176 176 [YP09.mkChunk 176 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
    YP09.mkRegion (Some 9%nat) 216 224 216 216 [YP09.mkChunk 216 (CVal 8 (SOff 33 0))];
    YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))] ] None
  (mkFacts [(21%nat, mkAF 0 31 0); (25%nat, mkAF 0x7fff8000 (0x7fff8000 + 2 ^ 44) 0); (34%nat, mkAF 1 32 0)] cs []).
Definition s9_ssT0 (cs : list acond) : sstate := mkSS LO9_R9 sr_atoms (ss_mem (s9_ssT cs)) None (ss_facts (s9_ssT cs)).
Definition s9_ET (regs : bvmap 5 word) (m n : Z) : env :=
  Eimg (Ereg regs [w64 (shadow_addr (m + seg_spec.MC_N)); w64 (m + seg_spec.MC_N); w64 n]).
Lemma s9_seedT : forall cx ly S W regs mem md k acc c m i cs,
  lt_base B MT cx -> s9M B MT cx ly S W regs mem md k acc LFO_R c m -> s9S cx (rdW W mem) m -> s9R cx i regs c m ->
  (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  conds_ok (s9_ET regs m (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) cs ->
  st_ok_pi SEGS VAL (s9_ET regs m (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) (s9_ssT cs)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO9_R9)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 9 0) [] (s9_ET regs m (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) (mrestrict (w_H W) mem).
Proof.
intros cx ly S W regs mem md k acc c m i cs HB HM HSS HR Hi HCS.
pose proof (s9_base_facts B MT cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
pose proof HM as ((HFR & _) & _ & (Hmin & Hm4 & Hm16 & Hmaddr) & HSL & (_ & HMC)).
destruct HFR as (HJ & _ & _ & _ & _ & R9 & _).
destruct (s9_frame_at B MT LAWS cx ly S W mem md k HB HJ) as (HAR & Hin & EF & Hfa & Hf4 & Hfc & Happ).
pose proof (al_frames _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & _ & HFP & HSP).
rewrite <- EF in HFP, HSP. change (fs_frame_bytes LT_FCLS) with 512 in HFP, HSP.
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & _ & Hmc & Hmapp & _).
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc, Hmapp.
assert (Hapart : ~ (x_fr cx <= m + seg_spec.MC_N < x_fr cx + 512)).
{ pose proof (s9_blk_frame_apart B LAWS ly S W mem md m seg_spec.SEG_M_SIZE LT_FCLS (x_fpos cx) (m + seg_spec.MC_N)
    HAR Hmin Hin ltac:(change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE; unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE; lia))
    as Hn. rewrite <- EF in Hn. change (fs_frame_bytes LT_FCLS) with 512 in Hn. exact Hn. }
pose proof HR as (_ & _ & R21 & _ & _ & _ & R25 & R26 & _).
pose proof asan_consts as (C1 & _).
set (n := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) in *.
assert (Hn : 1 <= n <= 32) by (pose proof (s18_mconf_len _ _ _ HMC); unfold n, x_mcF in *; lia).
assert (Hsh : x_sh cx = 0x7fff8000 + x_fr cx / 8) by (unfold x_sh, shadow_addr, SHADOW_OFF; lia).
assert (Hshr : 0x7fff8000 <= x_sh cx < 0x7fff8000 + 2 ^ 44).
{ rewrite Hsh. split; [pose proof (Z.div_pos (x_fr cx) 8); lia|].
  assert (x_fr cx / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (Hsm : shadow_addr (m + seg_spec.MC_N) = 0x7fff8000 + (m + seg_spec.MC_N) / 8)
  by (unfold shadow_addr, SHADOW_OFF; lia).
assert (Hsmr : 0x7fff8000 <= shadow_addr (m + seg_spec.MC_N) < 0x7fff8000 + 2 ^ 44).
{ rewrite Hsm. unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *. split; [pose proof (Z.div_pos (m + 8192) 8); lia|].
  assert ((m + 8192) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
set (E := s9_ET regs m n) in *.
assert (EL : forall q, (q < A_TEXT)%nat ->
  ew E q = ew (Ereg regs [w64 (shadow_addr (m + seg_spec.MC_N)); w64 (m + seg_spec.MC_N); w64 n]) q)
  by (intros q Hq; unfold E, s9_ET; apply Eimg_low; exact Hq).
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = w64 (Z.of_nat i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E25 : ew E 25 = w64 (x_sh cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew E 32 = w64 (shadow_addr (m + seg_spec.MC_N)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (m + seg_spec.MC_N)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HS0 : st_ok_pi SEGS VAL E (s9_ssT0 cs) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO9_R9)) mem (seg_rom SEGS)))).
{ unfold s9_ssT0, s9_ssT. cbn [ss_mem ss_facts]. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold E, s9_ET. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E25. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace o with 22 by lia. apply (apresent_writable SEGS).
      replace (x_sh cx + 22) with (shadow_addr (x_fr cx) + 22) by reflexivity. exact (proj1 (HSP 22 ltac:(lia))).
    * rewrite E9. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (x_s1 cx) 176 8 _ (shadow_addr (m + seg_spec.MC_N)));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia
        | exact (val_mem_of_rdword SEGS _ _ _ _ HSS)].
    * rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (shadow_addr (m + seg_spec.MC_N)) 0 1 _ 0); [reflexivity | lia | lia |].
      apply s9_val_of_rd. intros k0 Hk0. destruct k0 as [|k0]; [|lia]. rewrite !Z.add_0_r.
      rewrite (s9_mn_shadow _ m Hmaddr Hm16). reflexivity.
    * rewrite E9. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (x_s1 cx) 216 8 _ (m + seg_spec.MC_N));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.SEG_M_SIZE, seg_spec.MC_N in *; lia | lia
        | apply (val_mem_of_rdword SEGS); exact (HSL 216 _ ltac:(unfold LS9, LT_LC; cbn [In app]; tauto))].
    * rewrite E33. unfold w64. rewrite unsigned_lit_small by (unfold seg_spec.SEG_M_SIZE, seg_spec.MC_N in *; lia).
      split; [unfold seg_spec.MC_N; lia|]. split; [unfold seg_spec.SEG_M_SIZE, seg_spec.MC_N in *; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (m + seg_spec.MC_N) 0 4 _ n);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
      rewrite Z.add_0_r. exact (s9_val_of_rd _ _ _ _ _ (s18_mconf_n _ _ _ HMC)).
  + apply pairwise_disjoint_of_extents.
    unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E25, E32, E33. unfold w64.
    rewrite !unsigned_lit_small by (unfold seg_spec.SEG_M_SIZE, seg_spec.MC_N in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite Hsh, Hsm. unfold seg_spec.SEG_M_SIZE, seg_spec.MC_N in *.
    destruct Hmapp as (_ & [Hl | (Hh & _)]); destruct Happ as (_ & [Hl' | (Hh' & _)]);
      unfold kLowShadowBeg, kHighMemBeg in *; repeat split; Z.div_mod_to_equations; lia.
  + split; [|split; [exact HCS | exact I]].
    cbn [f_atoms atoms_ok]. split; [|split; [|split; [|exact I]]];
      unfold afact_ok; cbn [af_lo af_hi af_al2]; change (2 ^ 0) with 1; rewrite ?Z.mod_1_r.
    * rewrite E21. unfold w64. rewrite unsigned_lit_small by lia. lia.
    * rewrite E25. unfold w64. rewrite unsigned_lit_small by lia. lia.
    * rewrite E34. unfold w64. rewrite unsigned_lit_small by lia. lia. }
split; [|apply Forall_nil].
exact (st_ok_pi_pin_reg' _ _ _ 26%bv 18446744073709551608 HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite R26; apply bv_eq; reflexivity) eq_refl).
Qed.

(* 0x856b8 .. 0x856dc: r's shadow byte := f8 (r out of scope); check 19 (SH(m + 0x2000) is 0: the report path
   0x856e4 not reached); m->n; i += 1, &m->seg[i] += 256, 256 i += 256; `blt` back to the head of turn i + 1, or
   on to K856f4 *)
Lemma s9_T9 : forall i, S9_loop_stmt (Datatypes.S i) -> LTA_K856f4 B MT -> S9_R9 i.
Proof.
intros i HL HK cx ly S W regs mem md k acc c m HB HFRM Hi HM HSS HR _.
pose proof HM as ((HFR & _) & _ & (Hmin & _) & _ & (_ & HMC)). pose proof HFR as (HJ & _).
destruct (s9_frame_at B MT LAWS cx ly S W mem md k HB HJ) as (HAR & Hin & EF & Hfa & Hf4 & Hfc & Happ).
pose proof (s9_base_facts B MT cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
pose proof asan_consts as (C1 & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & _ & Hmc & _).
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc.
pose proof HR as (R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
assert (Hsh : x_sh cx = 0x7fff8000 + x_fr cx / 8) by (unfold x_sh, shadow_addr, SHADOW_OFF; lia).
assert (Hshr : 0x7fff8000 <= x_sh cx < 0x7fff8000 + 2 ^ 44).
{ rewrite Hsh. split; [pose proof (Z.div_pos (x_fr cx) 8); lia|].
  assert (x_fr cx / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
pose proof (s18_mconf_len _ _ _ HMC) as Hl32. fold (x_mcF cx) in Hl32.
assert (Hseg0 : 0 <= m + 256 * Z.of_nat i < 2 ^ 64).
{ pose proof HM as (_ & _ & (_ & Hm4 & _) & _). clear - Hm4 Hmc C1 Hl32 Hi.
  unfold seg_spec.SEG_M_SIZE in *. lia. }
set (n := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) in *.
set (E := s9_ET regs m n).
assert (EL : forall q, (q < A_TEXT)%nat ->
  ew E q = ew (Ereg regs [w64 (shadow_addr (m + seg_spec.MC_N)); w64 (m + seg_spec.MC_N); w64 n]) q)
  by (intros q Hq; unfold E, s9_ET; apply Eimg_low; exact Hq).
assert (HEI : img_env VAL A_LIM E) by (unfold E, s9_ET; apply Eimg_env).
assert (E21 : ew E 21 = w64 (Z.of_nat i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E25 : ew E 25 = w64 (x_sh cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E34 : ew E 34 = w64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (D21 : sv_denot E (SOff 21 1) = Z_to_bv 64 (Z.of_nat i + 1))
  by (cbn [sv_denot]; rewrite E21; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (D34 : sv_denot E (SOff 34 0) = Z_to_bv 64 n)
  by (cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
(* the run stored r's shadow byte only, f8 *)
assert (KEPT : forall cs (mem2 : word -> option byte), frame_of E (ss_mem (s9_ssT cs)) mem mem2 ->
  forall a, 0 <= a < 2 ^ 64 -> a <> x_sh cx + 22 -> ~ (x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
  rdW W mem2 a = rdW W mem a).
{ intros cs mem2 HF a Ha H22 _. apply s9_aview_pt. apply HF. rewrite unsigned_lit_small by lia.
  intros (r0 & Hr0 & Hw). unfold s9_ssT in Hr0. cbn [ss_mem In] in Hr0.
  destruct Hr0 as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; try lia.
  rewrite E25 in Hw. unfold w64 in Hw. rewrite unsigned_lit_small in Hw by lia. lia. }
assert (AWR : forall cs STK0 sp0 FP bl0 blc fr0 ly0 own, ly0 = ly -> own = [(LT_FCLS, x_fpos cx)] ->
  awr_ok SEGS B E (ss_mem (s9_ssT cs)) STK0 sp0 FP bl0 blc fr0 ly0 own).
{ intros cs STK0 sp0 FP bl0 blc fr0 ly0 own -> ->. unfold s9_ssT. cbn [ss_mem].
  eapply awr_ok_cons_gen with (n := 25%nat) (b := x_sh cx); [reflexivity | rewrite E25; unfold w64; apply unsigned_lit_small; lia | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite <- EF.
    change (fs_frame_bytes LT_FCLS / 8) with 64. unfold x_sh in Ha. lia. }
  do 4 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
destruct (lt_dec (Datatypes.S i) (length (SegModel.mc_seg (x_mcF cx)))) as [Hlt | Hge].
- (* blt taken: turn i + 1 *)
  destruct (s9_seedT cx ly S W regs mem md k acc c m i [mkAC BC_LT (SOff 21 1) (SOff 34 0)] HB HM HSS HR Hi) as [HS SHOK].
  { cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken]. fold n. fold E.
    rewrite D21, D34, s9_lts by (rewrite !unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia.
    apply Z.ltb_lt. unfold n. lia. }
  fold n E in HS, SHOK.
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO9_LOOP.
  { exact (AWR _ _ _ _ _ _ _ _ _ eq_refl eq_refl). }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  pose proof (KEPT _ (ms_mem ms) HF) as KM.
  assert (Hf8 : rdW W (ms_mem ms) (x_sh cx + 22) = Some 0xf8).
  { pose proof (s9_chunk_rd E _ (w_H W) ms 0 _ 22 1 (SLit 18446744073709551608) 0 HS eq_refl (or_introl eq_refl)
      ltac:(lia)) as Hc.
    cbn [base_val YP09.r_base] in Hc. rewrite E25 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    rewrite Z.add_0_r in Hc. rewrite Hc. reflexivity. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  rewrite E21 in P21.
  rewrite EL in P2, P3, P4, P8, P9, P18, P19, P22, P23, P24, P25, P27 by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in P2. rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl) in P3.
  rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl) in P4. rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl) in P8.
  rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl) in P9. rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl) in P18.
  rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl) in P19. rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl) in P22.
  rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl) in P23. rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl) in P24.
  rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl) in P25. rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl) in P27.
  destruct (s9_agree_win B MT LAWS cx ly S W regs mem md k acc LFO_R c m W (ms_mem ms) HB HM KM) as [HAG HST0].
  pose proof (s9M_agree B MT LAWS MTFL cx ly S W regs mem md k acc LFO_R LFO0 c m ly S W (ms_regs ms) (ms_mem ms) mdv
    HB HM HJ P2 P3 P4 P8 P9 HAG Hf8 eq_refl eq_refl eq_refl eq_refl (Permutation_refl _) (or_introl eq_refl)) as HM'.
  apply (HL cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m HB HFRM Hlt HM' (s9S_kept cx _ _ m HB HSS HST0)).
  split; [rewrite P18, R18; unfold w64; rewrite unsigned_lit_small by lia; apply (f_equal (Z_to_bv 64)); lia|].
  split; [rewrite P19, R19; unfold w64, seg_spec.mseg_addr, seg_spec.MSEG_SIZE;
    rewrite unsigned_lit_small by exact Hseg0; apply (f_equal (Z_to_bv 64)); lia|].
  split; [rewrite P21; unfold w64; rewrite ?unsigned_lit_small by lia; apply (f_equal (Z_to_bv 64)); lia|].
  split; [rewrite P22; exact R22|]. split; [rewrite P23; exact R23|]. split; [rewrite P24; exact R24|].
  split; [rewrite P25; exact R25|]. split; [rewrite P26; apply bv_eq; reflexivity | rewrite P27; exact R27].
- (* blt not taken: i + 1 = m->n, on to K856f4 *)
  destruct (s9_seedT cx ly S W regs mem md k acc c m i [mkAC BC_GE (SOff 21 1) (SOff 34 0)] HB HM HSS HR Hi) as [HS SHOK].
  { cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken]. fold n. fold E.
    rewrite D21, D34, s9_lts by (rewrite !unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia.
    apply negb_true_iff. apply Z.ltb_ge. unfold n. lia. }
  fold n E in HS, SHOK.
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO_K856f4.
  { exact (AWR _ _ _ _ _ _ _ _ _ eq_refl eq_refl). }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  pose proof (KEPT _ (ms_mem ms) HF) as KM.
  assert (Hf8 : rdW W (ms_mem ms) (x_sh cx + 22) = Some 0xf8).
  { pose proof (s9_chunk_rd E _ (w_H W) ms 0 _ 22 1 (SLit 18446744073709551608) 0 HS eq_refl (or_introl eq_refl)
      ltac:(lia)) as Hc.
    cbn [base_val YP09.r_base] in Hc. rewrite E25 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    rewrite Z.add_0_r in Hc. rewrite Hc. reflexivity. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  rewrite EL in P2, P3, P4, P8, P9 by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in P2. rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl) in P3.
  rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl) in P4. rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl) in P8.
  rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl) in P9.
  destruct (s9_agree_win B MT LAWS cx ly S W regs mem md k acc LFO_R c m W (ms_mem ms) HB HM KM) as [HAG HST0].
  pose proof (s9M_agree B MT LAWS MTFL cx ly S W regs mem md k acc LFO_R LFO0 c m ly S W (ms_regs ms) (ms_mem ms) mdv
    HB HM HJ P2 P3 P4 P8 P9 HAG Hf8 eq_refl eq_refl eq_refl eq_refl (Permutation_refl _) (or_introl eq_refl))
    as (HC' & Hc' & Hm' & HSL' & HCM').
  pose proof (s9S_kept cx _ _ m HB HSS HST0) as HSS'.
  apply (HK fx cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m HB HFRM HC' Hc' Hm'); [|exact HCM'].
  intros o v Hin'. apply in_app_or in Hin' as [Hin' | Hin'].
  + apply HSL'. unfold LS9. apply in_or_app. left. exact Hin'.
  + cbn [In] in Hin'. destruct Hin' as [Hin' | [Hin' | []]]; injection Hin' as <- <-.
    * apply HSL'. unfold LS9. apply in_or_app. right. cbn [In]. tauto.
    * exact HSS'.
Qed.

(* ---- the loop: one turn is the ten steps T0 .. T9 ---- *)
Lemma s9_turn : forall i, S9_loop_stmt (Datatypes.S i) -> LTA_K856f4 B MT -> S9_loop_stmt i.
Proof.
intros i HL HK.
exact (s9_T0 i (s9_T1 i (s9_T2 i (s9_T3 i (s9_T4 i (s9_T5 i (s9_T6 i (s9_T7 i (s9_T8 i (s9_T9 i HL HK)))))))))).
Qed.
(* a turn i >= 32 is never reached: m->n <= 32 (sa_mconf) *)
Lemma s9_loop_vacuous : forall i, (32 <= i)%nat -> S9_loop_stmt i.
Proof.
intros i Hi cx ly S W regs mem md k acc c m _ _ Hlt HM _ _. exfalso.
pose proof HM as (_ & _ & _ & _ & (_ & HMC)). pose proof (s18_mconf_len _ _ _ HMC) as H32.
unfold x_mcF in Hlt. lia.
Qed.
(* every turn, by downward induction from 32 *)
Lemma s9_loop_all : LTA_K856f4 B MT -> forall i, S9_loop_stmt i.
Proof.
intros HK.
assert (H : forall d i, (32 <= i + d)%nat -> S9_loop_stmt i).
{ induction d as [|d IH]; intros i Hid.
  - apply s9_loop_vacuous. lia.
  - exact (s9_turn i (IH (Datatypes.S i) ltac:(lia)) HK). }
intros i. exact (H 32%nat i ltac:(lia)).
Qed.

(* ---- the segment ---- *)
Theorem lt_seg_S09 : lt_seg_S09_stmt B MT.
Proof. intros HK. exact (s9_head (s9_cs (s9_loop_all HK 0) HK)). Qed.

End e.
End f.
End d.
