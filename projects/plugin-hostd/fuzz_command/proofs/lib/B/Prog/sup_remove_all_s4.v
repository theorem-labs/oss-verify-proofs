(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_pool_config (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_sup_pool_config = 0x8bed0, 127 instructions): it proves a Theorem Labs lane's
   `tsup_pool_config_spec` (lib/B/Prog/sup_pool_config_c.v, a working branch 707acd856cb; the same text as at
   f490061c104) in the form of
   cgif_file_fuzzer's per-function walks: afn_pre at the entry, the symbolic executor over the position-abstract
   listing up to each call, the runtime's rules at the runtime calls (__asan_stack_malloc_0, the snprintf wrapper,
   the frame's release by its flag byte), the callee contracts record_c, arg_s_c, rec_shape_of_c and answer_c at the
   program calls (through cl_callS_wide / cl_callS_na), the return through paj_ret_at, and apost_base at the end.

   It is the B re-walk of the A walk lib/A/Prog/sup_pool_config.v (a working branch c4f188792bb),
   whose B code differs: B calls record() and arg_s() where A inlined record() and called xstrdup, and B inlines
   arg_i, so this function owns arg_i's class-0 side-stack frame (64 bytes, b = frame + 32) and its snprintf. The
   frame code (prologue, realignment `andi sp,sp,-32`, __asan_stack_malloc_0, header and shadow f1 f1 f1 f1 | f8 f8 |
   f3 f3, b unpoisoned around the snprintf and the second arg_s, the release through the flag byte) is arg_i's ASan
   walk's (lib/A/Prog/arg_i.v, a working branch 12dc52bfe84) and answer_code's ASan walk's
   (lib/A/Prog/answer_code.v, a working branch 2ba4488ce71); the B kit usage is socket_send's B walk
   (lib/B/Prog/socket_send.v, a working branch a470f91dbfb).

   Report and trap edges: none. The function has no `jal __asan_report_*`, no `unimp`, no UBSan handler call
   (capstone over the pin's .symtab, gen/traps.B.summary row `sup_pool_config 0`). Its branches: 0x8bf30 `beqz a2`
   on the use-after-return flag, read through the GOT word 0xa5fa8 at the record's const cell 0xb0c40 (= 1, lib/B/YF0m.v
   z4 (ANum 0xb0c40) 0x1, AR's const-cell law al_const; the executor decides it not taken); 0x8bf4c `bnez s2` and
   0x8c040 `beqz s2` on the side-stack frame (nonzero, __asan_stack_malloc_0's post; decided by the frame atom's
   fact), so the real-stack fallback 0x8bf50-0x8bf68 with its page probe and the real-stack release 0x8c074-0x8c090
   are not reached. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_pool_config.v, with its module paths, module names and numbers changed; 189 of its 252 lines of code are new or changed and 2001 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_remove_all_refit_s4.v, with its module paths, module names and addresses changed; 65 of its 140 lines of code are new or changed and 177 lines of the source are left out. *)
(* sup_remove_all's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan,
   BASE + AF_sup_remove_all = 0x8b434), the symbolic entry state and the small facts the walk takes beside the
   executor.

   The entry state (0x8b434): every register is its own atom; atom 32 is the shadow base 0x7fff8000 (the token
   executor's Bx; B's sup_remove_all has no inline shadow check, gen/funcs.tsv and the listing, so the run reads no
   shadow byte and the shadow table is empty). The only region is the 16-byte frame below sp (writable): the code
   reads no static, no GOT word and no shadow-base cell (all of record()'s and answer()'s reads are inside their
   contracts). Unlike a Theorem Labs lane's A entry state (lib/A/Prog/sup_remove_all_s4.v at 59cc4017e62: GOT word, shadow-base
   cell, g_rec.ncalls, the slot), it needs neither PALib's GOT and cell fields nor PRW.

   Beside it: sup_remove_all's footprint lies below alloc_ceiling (sra_fp_bound), and record's footprint for
   record(REC_REMOVE_ALL) lies in sup_remove_all's, each byte a live block's or a program static's of the image
   (sra_rec_fp_cover, in the form of PaCallPg.v's cl_callS_pg). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c answer_c sup_remove_all_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_remove_all_s1 sup_remove_all_s2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition sra_SB : Z := 0x7fff8000.
Definition sra_Bx : sv := SOff 32 0.
Definition sra_Bspan : Z * Z := (sra_SB, sra_SB + 2 ^ 44 - 1).
Definition sra_regions : smem := [ stack_region 16 ].
Definition sra_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF sra_SB sra_SB 0) ] [] [].
Definition ss_sra : sstate := mkSS AF_sup_remove_all sr_atoms sra_regions None sra_facts.
Definition sra_SH0 : list shent := [].
Definition sra_extra : list word := map (Z_to_bv 64) [sra_SB].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* sup_remove_all's footprint lies in the image's statics and the live blocks, below alloc_ceiling *)
Lemma sra_fp_bound : forall O, (forall p n, In (p, n) O -> 4096 <= p /\ p + req_size n <= alloc_ceiling) ->
  forall a, inFP (sra_FP O) a -> 4096 <= a < alloc_ceiling.
Proof.
intros O HO a Ha. pose proof asan_consts as (C1 & _).
unfold sra_FP in Ha. rewrite !inFP_cons in Ha.
destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
  [unfold A_G_REC, A_REC_SPILL, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE, SC_SIZE in Ha; lia ..|].
destruct (inFP_ablocks_fp_inv O a Ha) as (p & n & Hin & Hr). destruct (HO p n Hin). lia.
Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition sra_E (regs : bvmap 5 word) : env := Eimg (Ereg regs sra_extra).

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
(* the image facts (a Theorem Labs lane's RULING-STMT.md §1 IMG, CmdRecBase's cmd_img_facts): cif_prog_img *)
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.

(* a byte of the program's statics is as_prog_static B's (CmdBSyms' ts_prog) and an image byte (cif_prog_img) *)
Lemma sra_prog : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Proof.
intros a Hpg. split; [|exact (CmdRecBase.cif_prog_img _ _ IMG a Hpg)].
destruct Hpg as (r & Hr & Ha). rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC.
unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr. cbn [In] in Hr. apply Exists_exists.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha;
[exists (0x5e32c0, 960) | exists (0x5e3760, 56) | exists (0x5e37e0, 4)];
(split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]).
Qed.

(* record's footprint for record(REC_REMOVE_ALL) lies in sup_remove_all's: g_rec.ncalls and the slot's first 8
   bytes are program statics (g_rec's call table or record.spill), the spill arm's freed blocks are the recorder's
   live blocks *)
Lemma sra_rec_fp_cover : forall ly S rd R O, rec_repA B ly S rd R O ->
  forall a, inFP (sra_rec_FP R O) a -> inFP (sra_FP O) a /\
  ((exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
   (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a)).
Proof.
intros ly S rd R O HREP a Ha. unfold sra_rec_FP in Ha. rewrite !inFP_cons in Ha.
destruct Ha as [Ha | [Ha | Ha]].
- split.
  + unfold sra_FP. rewrite !inFP_cons. left. exact Ha.
  + right. apply sra_prog. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|].
    unfold OFF_NCALLS in Ha. cbn [fst snd]. lia.
- unfold rec_slot in Ha. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl | Hl].
  + split.
    * unfold sra_FP. rewrite !inFP_cons. right; left. unfold OFF_CALLS, OFF_ANSWER, CALL_SIZE in *. lia.
    * right. apply sra_prog. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|].
      unfold OFF_CALLS, CALL_SIZE, A_G_REC in *. cbn [fst snd]. lia.
  + split.
    * unfold sra_FP. rewrite !inFP_cons. right; right; right; left. unfold SC_SIZE. lia.
    * right. apply sra_prog. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity|].
      cbn [fst snd]. lia.
- destruct (Nat.ltb (length (r_calls R)) 16); [destruct Ha as (r & [] & _)|].
  destruct (inFP_ablocks_fp_inv O a Ha) as (p & n & Hin & Hr). split.
  + unfold sra_FP. rewrite !inFP_cons. right; right; right; right. exact Ha.
  + left. exists p, n. split; [exact (bsra_rep_live B ly S rd R O _ HREP Hin) | exact Hr].
Qed.

(* the same footprint lies below alloc_ceiling, so outside every stack window *)
Lemma sra_rec_fp_low : forall ly S (W : world SEGS) mem md rd R O, AR SEGS B ly S W mem md -> rec_repA B ly S rd R O ->
  forall a, inFP (sra_rec_FP R O) a -> 4096 <= a < alloc_ceiling.
Proof.
intros ly S W mem md rd R O HAR HREP a Ha.
destruct (sra_rec_fp_cover ly S rd R O HREP a Ha) as [Hf _].
apply (sra_fp_bound O); [|exact Hf].
intros p n Hin. destruct (bsra_blk B LAWS ly S W mem md p n HAR (bsra_rep_live B ly S rd R O _ HREP Hin)). lia.
Qed.

(* the symbolic entry state *)
Lemma sra_entry : forall W ly S regs mem md ch,
afn_pre SEGS B SUP_REMOVE_ALL_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (sra_E regs) ss_sra
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_remove_all)) mem (seg_rom SEGS))) /\
sh_ok SEGS sra_Bx sra_SH0 (sra_E regs) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : SUP_REMOVE_ALL_STK = ltac:(let v := eval vm_compute in SUP_REMOVE_ALL_STK in exact v)) by reflexivity.
split; [|unfold sh_ok, sra_SH0; apply Forall_nil].
rewrite restrict_mkst_fx.
set (E := sra_E regs).
assert (E2 : ew E 2 = getr regs 2) by (subst E; unfold sra_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 sra_SB) by (subst E; unfold sra_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold ss_sra. apply pa_entry_st_ok_full.
- subst E. unfold sra_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sra_regions, stack_region.
  repeat apply Forall_cons; try apply Forall_nil.
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- apply pairwise_disjoint_of_extents.
  unfold sra_regions, stack_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok sra_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32.
  rewrite !unsigned_lit_small by (unfold sra_SB in *; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; unfold sra_SB; first [exact I | lia | reflexivity].
Qed.
End e.
End f.
End d.
