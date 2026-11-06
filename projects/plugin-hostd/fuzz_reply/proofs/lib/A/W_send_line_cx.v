(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's send_line, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites), lib/A/AC8b.v (a loop over concrete cut states) and
   lib/A/ACfj.v (segments joined at cut points). *)
(* send_line (line, len) at 0x82734 (relay.c:66-86, fuzz_send inlined from fuzz_reply.c:278-313), 135 instructions.
   Three segments, each a lemma from a concrete machine state at a cut point:
   - the epilogue X (0x828f8): the 13 saved registers back from the frame, the return;
   - the loop L (0x827c8), by induction on a bound for (len - sent) * 2 + g_send_eintr: one round (the EINTR round,
     the dead controller, or a data round with the realloc of g_out when it is short and the memcpy into it);
   - the entry: the client test, len = 0, the broken test, then the first round.
   The walk's globals G_SL are stored to through the kept auipc registers, so their regions are rebased between the
   object atom (PLdHi reads) and the hi atom (stores) with W_rebase.v's prebase.
   Section hypotheses (what the rest of the proof owes this walk):
   - runtime: AERRNO (W_sites.v aerrno_realizes at __errno_location), AMEMCPY (donor aintrin_realizes OCpy at
     __asan_memcpy), AREALLOC (W_journal.v arealloc_cf_rule at the realloc trampoline);
   - instance: LAWS, MTL (the meter's laws), TL (PALib), HG (gx_ok of G_SL), HERRNO (as_errno = as_tp - 164),
     HERRZ (errno's 4 bytes inside one of the instance's zero-shadow ranges);
   - placement: HV9 .. HV15 and HH17 .. HH24, the objects' and kept auipc registers' addresses against RG;
     HROMO (rom_out of G_SL) and HGO (gx_ok of aout_at's three read-only cells).
   STATEMENT GAPS (facts the machine has that the first text lacked; each found at a prover's unprovable goal, each
   fixed by stating the fact and discharging it at the pinned placement by vm_compute, never by weakening):
   - sl_line_ok's image disjunct (W_contract.v) and HROMO / HGO here (SlLoop, sl_arm_data's growth round, the realloc
     at 0x82840 then the memcpy from the line): arealloc_cf_rule keeps an image byte only off the allocator's statics
     (acall_kept, YCbq.v:830; W_journal.v:846-872), and nothing said that an image line, or g_client / g_send_dead /
     g_send_max, is off them.  Counter-case: an image line in as_zero_shadow whose bytes are an allocator static is
     allowed by the old text and can change across the realloc.  Now an image line is stated off as_owned_static
     (directly, not through rom_out: W1 found rom_out's owned-static conjunct false against AF0m's
     Tfib_owned_static for .rodata ranges); heap lines use the block disjunct as before.  HROMO here serves
     rom_view across the realloc and follows W1's replacement of rom_out when it lands. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_send_line : Z := AF_fr_send_line.
Definition A_send_lineP : Z := BASE + A_send_line.
Definition A_sl_loop : Z := AF_fr_send_line + 0x94.
Definition A_sl_epi : Z := AF_fr_send_line + 0x1c4.
(* The callee-saved registers in their frame slots 24(sp), 32(sp), ..., 120(sp). *)
Definition SL_SAVED : list (bv 5) := [27%bv; 26%bv; 25%bv; 24%bv; 23%bv; 22%bv; 21%bv; 20%bv; 19%bv; 18%bv; 9%bv; 8%bv; 1%bv].
Definition sl_saved (W : world SEGS) (mem : word -> option byte) (spX : Z) (regsE : bvmap 5 word) : Prop :=
forall i, (i < 13)%nat ->
val_mem SEGS (mrestrict (w_H W) mem) (spX + 24 + 8 * Z.of_nat i) 8 (bv_unsigned (getr regsE (nth i SL_SAVED 0%bv))).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
(* the walk's globals are .data / .bss cells, never read-only image bytes (the pinned placement decides it) *)
Hypothesis HGR : forall a, inG (G_SL B RG) a -> ~ in_rom SEGS a.
(* nothing a callee's journal may change is a read-only image byte (W_journal.v rom_out / ajournal_gx_rom_view); and
   aout_at's three read-only cells are program globals off the allocator's statics, so a realloc keeps them *)
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* runtime and allocator sites *)
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
(* instance facts: errno is tp - 164 (W_sites.v aerrno_realizes) and its shadow is zero *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : exists r, In r (as_zero_shadow B) /\ fst r <= as_errno B /\ as_errno B + 4 <= fst r + snd r.
(* errno's 4 bytes are writable image bytes in the segments' own view (W_drain_cx.v HERRW, same text) *)
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
(* placement: the objects send_line reads by PLdHi, and the kept auipc registers it stores and loads through *)
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV10 : VAL (A_OBJ 10) = rg_client_broken RG.
Hypothesis HV11 : VAL (A_OBJ 11) = rg_send_eintr RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HV13 : VAL (A_OBJ 13) = rg_nout RG.
Hypothesis HV14 : VAL (A_OBJ 14) = rg_capout RG.
Hypothesis HV15 : VAL (A_OBJ 15) = rg_out RG.
Hypothesis HH17 : VAL (A_HI 17) + 92 = rg_client_broken RG.
Hypothesis HH19 : VAL (A_HI 19) + 248 = rg_send_eintr RG.
Hypothesis HH21 : VAL (A_HI 21) + 140 = rg_send_max RG.
(* g_send_max is not one of the listing's objects: place it in the image band by its address. *)
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Hypothesis HH22 : VAL (A_HI 22) + 260 = rg_nout RG.
Hypothesis HH23 : VAL (A_HI 23) + 864 = rg_capout RG.
Hypothesis HH24 : VAL (A_HI 24) + 892 = rg_out RG.
(* placement: the cells send_line reads or writes are pairwise disjoint ((lo, hi) extents, as extent_of_region
   makes them; the pinned placement decides it by vm_compute; errno is tp - 164, TFIB_ERRNO 0x5d93cc). *)
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].
Let RUN := paj_run_x B LAWS (G_SL B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_SL B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* ---- The epilogue X (0x828f8): ld ra/s0..s11 from the frame, addi sp,sp,128, ret. ---- *)
Definition BxX : sv := SOff 45 0.
Definition epi_regions : smem :=
[ YP09.mkRegion (Some 2%nat) 24 128 24 24
  (map (fun i => YP09.mkChunk (24 + 8 * Z.of_nat i) (CVal 8 (SOff (32 + i) 0))) (seq 0 13)) ].
Definition epi_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (45%nat, mkAF SB SB 0) ] [] [].
Definition ss_epi : sstate := mkSS A_sl_epi sr_atoms epi_regions None epi_facts.
Definition epi_extra (regsE : bvmap 5 word) : list word := map (getr regsE) SL_SAVED ++ [Z_to_bv 64 SB].
Lemma nth_epi_extra : forall regsE i, (i < 13)%nat -> nth i (epi_extra regsE) (Z_to_bv 64 0) = getr regsE (nth i SL_SAVED 0%bv).
Proof.
intros regsE i Hi. unfold epi_extra. rewrite app_nth1 by (rewrite length_map; cbn; lia).
rewrite (nth_indep _ _ (getr regsE 0%bv)) by (rewrite length_map; cbn; lia). rewrite List.map_nth. reflexivity.
Qed.
Lemma sl_epi_entry : forall W regsX memX regsE,
alloc_ceiling <= spZ regsX -> spZ regsX + 128 <= 2 ^ 47 -> 2 ^ 46 <= spZ regsX -> spZ regsX mod 16 = 0 ->
sl_saved W memX (spZ regsX) regsE ->
st_ok_pi SEGS VAL (Eimg (Ereg regsX (epi_extra regsE))) ss_epi
(restrict (w_H W) (mkst regsX (Z_to_bv 64 (BASE + A_sl_epi)) memX (seg_rom SEGS))).
Proof.
intros W regsX memX regsE Hceil Htop Hlo Hal HSV.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsX (epi_extra regsE))).
assert (E2 : ew E 2 = getr regsX 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 2 2%bv eq_refl)).
assert (E45 : ew E 45 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 13)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsX) by (rewrite E2; reflexivity).
unfold ss_epi, A_sl_epi. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold epi_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_map. apply Forall_forall. intros i Hi. apply in_seq in Hi. cbn [Nat.add] in Hi.
  apply (chunk_ok_val SEGS E _ (spZ regsX) (24 + 8 * Z.of_nat i) 8 _ (bv_unsigned (getr regsE (nth i SL_SAVED 0%bv)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite ew_Ereg_extra, nth_epi_extra by lia.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + pose proof (bv_unsigned_in_range 64 (getr regsE (nth i SL_SAVED 0%bv))) as R. change (bv_modulus 64) with (2 ^ 64) in R. zside.
  + zside.
  + replace (spZ regsX + (24 + 8 * Z.of_nat i)) with (spZ regsX + 24 + 8 * Z.of_nat i) by lia. exact (HSV i ltac:(lia)).
- cbn [pairwise_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [epi_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E45, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hceil Htop Hlo Hal. clear. unfold SB. intros. repeat match goal with |- _ /\ _ => split end; lia.
Qed.
(* The epilogue writes nothing: the caller's continuation gets the same restricted memory and the same journal. *)
Lemma sl_epi : forall W ly S mem md sp0 FP lyX SX WX regsX memX mdX k regsE (Q : world SEGS -> config -> Prop),
ajournal_gx SEGS B (G_SL B RG) 0 [] SL_STK sp0 FP ly S W mem md [] lyX SX WX memX mdX k ->
spZ regsE = sp0 -> spZ regsX = sp0 - SL_FRAME ->
getr regsX 3 = getr regsE 3 -> getr regsX 4 = getr regsE 4 -> YK0s.ret_ok (getr regsE 1) ->
sl_saved WX memX (sp0 - SL_FRAME) regsE ->
(forall regs' mem' md', aregs_preserved regsE regs' ->
  (forall x, mrestrict (w_H WX) mem' x = mrestrict (w_H WX) memX x) ->
  ajournal_gx SEGS B (G_SL B RG) 0 [] SL_STK sp0 FP ly S W mem md [] lyX SX WX mem' md' k ->
  Q WX (mkCfg (mkst regs' (getr regsE 1) mem' (seg_rom SEGS)) md')) ->
SRr SEGS WX (mkCfg (mkst regsX (Z_to_bv 64 (BASE + A_sl_epi)) memX (seg_rom SEGS)) mdX) Q.
Proof.
intros W ly S mem md sp0 FP lyX SX WX regsX memX mdX k regsE Q HJ HspE HspX H3 H4 HraE HSV HQ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : SL_STK = 16512) by reflexivity. rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
pose proof (sl_epi_entry WX regsX memX regsE ltac:(unfold SL_FRAME in *; lia) ltac:(unfold SL_FRAME in *; lia)
  ltac:(unfold SL_FRAME in *; lia) ltac:(unfold SL_FRAME in *; rewrite HspX; rewrite Zminus_mod, Hal16; reflexivity)
  ltac:(rewrite HspX; exact HSV)) as HS.
remember (Eimg (Ereg regsX (epi_extra regsE))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall i, (i < 13)%nat -> ew E (32 + i) = getr regsE (nth i SL_SAVED 0%bv)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (nth_epi_extra regsE i Hi). }
assert (E2 : ew E 2 = getr regsX 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsX 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsX 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsX) by (rewrite E2; reflexivity).
assert (SHOK : sh_ok SEGS BxX [] E (mrestrict (w_H WX) memX)) by constructor.
clear HE.
paj_run_tok RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
eapply (RET WX _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (RA : getr (ms_regs ms) 1 = getr regsE 1) by (rewrite R1; exact (EX 12%nat ltac:(lia))).
rewrite RA, HraE. apply HQ.
- intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R2, Usp, HspX. replace (sp0 - SL_FRAME + 128) with sp0 by (unfold SL_FRAME; lia).
    rewrite <- HspE. unfold spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R3, E3. exact H3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R4, E4. exact H4.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8. exact (EX 11%nat ltac:(lia)).
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9. exact (EX 10%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18. exact (EX 9%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R19. exact (EX 8%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R20. exact (EX 7%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R21. exact (EX 6%nat ltac:(lia)).
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R22. exact (EX 5%nat ltac:(lia)).
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R23. exact (EX 4%nat ltac:(lia)).
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R24. exact (EX 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R25. exact (EX 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R26. exact (EX 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R27. exact (EX 0%nat ltac:(lia)).
- intros x. apply HFr. intros (r & Hin & Hr). cbn [ss_mem ss_epi epi_regions In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
- apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

(* ---- The loop head L (0x827c8): the state at the top of `while (sent < len)`, after the entry's tests. ----
   The client is 3 (the bltz passed), g_client_broken is 0 (the bnez passed), g_send_dead is the entry's, and
   g_send_eintr is the entry's until the first round clears it.  sent bytes of the line are in g_out after the
   bytes O the controller had; the rounds still to come are the plain model's rounds from (no + sent, capL,
   len - sent) (Prog/send_line_b_c.v sl_run through send_line_cap / sl_cost_run); the room they need is the peak of
   their requests (C3, W_contract.v sl_spec: tr_peak of send_line_tr from this cut, on top of the live bytes; each
   growth frees the block it replaces, so the peak is never above the summed requests).  The registers are the loop's:
   s0 = len, s1 = line, s3 = 3, s6 = sent, s7 = the shadow base, s4 s5 s8 s9 s10 s11 the kept auipc values; the
   frame holds the two spilled auipc values at 8(sp) and 16(sp) and the 13 saved registers at 24(sp) .. 120(sp). *)
Definition sl_regsL (regsL : bvmap 5 word) (len line sent : Z) : Prop :=
getr regsL 8 = w64 len /\ getr regsL 9 = w64 line /\ getr regsL 19 = w64 3 /\ getr regsL 22 = w64 sent /\
getr regsL 23 = w64 SB /\ getr regsL 20 = w64 (VAL (A_HI 24)) /\ getr regsL 21 = w64 (VAL (A_HI 16)) /\
getr regsL 24 = w64 (VAL (A_HI 23)) /\ getr regsL 25 = w64 (VAL (A_HI 19)) /\ getr regsL 26 = w64 (VAL (A_HI 22)) /\
getr regsL 27 = w64 (VAL (A_HI 20)).
Definition SLI (regsE : bvmap 5 word) ly S W mem md (c : ctl) (O : list byte) (mx no cap out line : Z) (Bl : list byte)
(WL : world SEGS) (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) (sent eiL : Z) : Prop :=
let len := Z.of_nat (length Bl) in
let sp0 := spZ regsE in
exists lyL SL kL evL capL outL spent rest,
ajournal_gx SEGS B (G_SL B RG) 0 [] SL_STK sp0 (ablocks_fp (aout_blks cap out)) ly S W mem md [] lyL SL WL memL mdL kL /\
spZ regsL = sp0 - SL_FRAME /\ getr regsL 3 = getr regsE 3 /\ getr regsL 4 = getr regsE 4 /\
getr regsE 3 = w64 (as_gp B) /\ getr regsE 4 = w64 (as_tp B) /\
YK0s.ret_ok (getr regsE 1) /\ sl_regsL regsL len line sent /\
val_mem SEGS (mrestrict (w_H WL) memL) (sp0 - SL_FRAME + 8) 8 (VAL (A_HI 17)) /\
val_mem SEGS (mrestrict (w_H WL) memL) (sp0 - SL_FRAME + 16) 8 (VAL (A_HI 21)) /\
sl_saved WL memL (sp0 - SL_FRAME) regsE /\
ct_cl c = 3 /\ ct_br c = 0 /\ 0 <= sent < len /\ (eiL = ct_ei c \/ eiL = 0) /\ (0 < sent -> eiL = 0) /\
(ct_dd c = 1 -> sent = 0) /\
evL = (if (ct_ei c =? 1) && (eiL =? 0) then send_line_c.EINTR_V else ct_ev c) /\
aout_at B RG lyL SL WL memL (CTL 3 0 (ct_dd c) eiL evL) (O ++ firstn (Z.to_nat sent) Bl) mx (no + sent) capL outL /\
garr8 SEGS (arm WL memL) line (bzs Bl) /\ 0 <= line /\ line + len < 2 ^ 63 /\ rom_view SEGS WL memL /\
sl_line_ok B lyL SL outL line len /\ (forall a, line <= a < line + len -> ~ inG (G_SL B RG) a) /\
(ct_dd c = 0 -> sl_cap c mx no cap len = send_line_b_c.send_line_cap true mx (no + sent) capL (len - sent)) /\
(ct_dd c = 1 -> capL = cap /\ outL = out) /\
(ct_dd c = 0 -> sl_max_run (Z.to_nat (len - sent)) mx (no + sent) capL (len - sent) < MMAX) /\
(ct_dd c = 0 -> blocks_bytes SL +
  tr_peak (send_line_b_c.send_line_tr true mx (no + sent) capL (len - sent) 0 RelayRunF.adr0) <= LIVE_MAX) /\
apres_kept B W mem WL memL /\
mo_ok MT S (sl_cost MT c mx no cap len) /\ mo_le MT S SL spent /\
(ct_dd c = 0 -> spent + sl_cost_run MT (Z.to_nat (len - sent)) mx (no + sent) capL (len - sent) <= sl_cost MT c mx no cap len) /\
(ct_dd c = 1 -> spent = 0) /\
Permutation (ablocks B ly S) (aout_blks cap out ++ rest) /\ Permutation (ablocks B lyL SL) (aout_blks capL outL ++ rest) /\
frames SL = frames S.
(* The loop segment (an induction on n >= 2 (len - sent) + g_send_eintr): from L, send_line ends in its post. *)
Definition sl_loop_stmt : Prop :=
forall (n : nat) regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL,
SLI regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL ->
2 * (Z.of_nat (length Bl) - sent) + eiL <= Z.of_nat n ->
SRr SEGS WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_sl_loop)) memL (seg_rom SEGS)) mdL)
(sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl).
(* The entry segment, given the loop: the prologue, the three early returns (g_client < 0, len = 0, broken) through
   the epilogue, else the loop head with sent = 0. *)
Definition sl_entry_stmt : Prop := sl_loop_stmt -> sl_spec B MT MMAX RG A_send_lineP.
End c.
End b.
End a.
