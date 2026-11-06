(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_cmp_st.v, with its module paths and module names changed; 207 of its 246 lines of code are new or changed and 493 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_segX_up_a: the first stretch of the `up` segment of the image-B walk of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput (llvm_b_up_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_segs.v, proved in
   lib/B/Prog/LLVMFuzzerTestOneInput_segG.v): the symbolic entry state at +0x840 and the channel-count check
   +0x840 .. +0x8a4.

   Shape and tactics: a Theorem Labs lane's per-unit Pa walks (a working branch, lib/A/Prog/CtrlIdentityPollBlock.v's
   entry / run / branch / call skeleton and GrantBuildSweepCell.v's loop) and cgif_file_fuzzer's own ASan walk of
   LLVMFuzzerTestOneInput (origin/ossv/recipes lib/A/ACf2.v for the malloc stage, ACf0.v for the memset stage).
   The arithmetic of the in-line channel-count check is lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_arith.v and the
   read-only multiplier is lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_rom.v. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBAddr DecodeBPa DecodeBImg DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_segX_up_arith LLVMFuzzerTestOneInput_segX_up_rom LLVMFuzzerTestOneInput_segX_up_den.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN1y.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_upstream_channels_c reac_upstream_decode_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The listing's base is the function's entry: DEC_A_LLVMF of the statement is the Pa walk's BASE. *)
Lemma up_base_eq : DEC_A_LLVMF = decodeb_val A_TEXT.
Proof. vm_compute. reflexivity. Qed.

(* This unit's lia cannot evaluate 2 ^ k, so every power the walk's bounds use is turned into its literal. *)
Ltac up_lits :=
  try change (2 ^ 4) with 16 in *; try change (2 ^ 5) with 32 in *;
  try change (2 ^ 8) with 256 in *; try change (2 ^ 26) with 67108864 in *;
  try change (2 ^ 31) with 2147483648 in *; try change (2 ^ 32) with 4294967296 in *;
  try change (2 ^ 46) with 70368744177664 in *; try change (2 ^ 47) with 140737488355328 in *;
  try change (2 ^ 63) with 9223372036854775808 in *;
  try change (2 ^ 64) with 18446744073709551616 in *.

(* A read-only symbolic memory: every region has an empty writable window, so a run writes nothing it tracks. *)
Ltac awr_ro := lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* After a run over read-only regions the memory is the one before it (frame_of_nowin, lib/Reusable/YN1y.v:94);
   Hmem keeps the current machine memory equal to the segment's entry memory. *)
Ltac up_memeq HF :=
  lazymatch type of HF with frame_of _ ?rs ?m0 ?m1 =>
    let H := fresh "Hmn" in
    pose proof (frame_of_nowin _ rs m0 m1 ltac:(vm_compute; repeat constructor) HF) as H;
    try (lazymatch goal with Hm : m0 = _ |- _ => rewrite Hm in H; clear Hm end);
    rename H into Hmem
  end; clear HF; try (lazymatch goal with H : frame_of _ _ _ _ |- _ => clear H end);
  try (lazymatch goal with H : mem_grows _ _ |- _ => clear H end).
Ltac up_memchain := lazymatch goal with Hm : ms_mem _ = _ |- _ => exact Hm end.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation SEGS := (@pa_segs _ decodeb_listing PI_decodeb).
#[local] Abbreviation VAL := (@pa_val _ decodeb_listing PI_decodeb).
#[local] Abbreviation BASE := (@pa_val _ decodeb_listing PI_decodeb A_TEXT).

(* The env of the walk: the registers of the entry configuration, one extra atom (32) for the shadow base, and
   the image's own atoms above A_TEXT. cgif's rt_E / grant's ECG. *)
Definition up_extra : list word := [Z_to_bv 64 SHADOW_OFF].
Definition EUP (regs : bvmap 5 word) : env := Eimg (Ereg regs up_extra).
Definition UPBx : sv := SOff 32 0.
Definition UPspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* The two memory facts the segment's straight-line code reads: 32(s1), the spilled shadow base (+0x870 and
   +0x898), and the 8-byte read-only multiplier decodeb_obj 9 (+0x854). *)
Definition up_slot32_region : YP09.region :=
  YP09.mkRegion (Some 9%nat) 32 40 0 0 [YP09.mkChunk 32 (CVal 8 (SOff 32 0))].
Definition up_div36_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 9)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit UPSTREAM_DIV36))].
Definition up_regions : smem := [ up_slot32_region; up_div36_region ].
(* Bounds as literals: this unit's lia cannot evaluate 2 ^ k. 2 ^ 46 / 2 ^ 47 / 2 ^ 26. *)
Definition up_facts : facts :=
  mkFacts [ (2%nat, mkAF 70368744177664 140737488355328 4);
            (9%nat, mkAF 70368744177664 140737488355328 5);
            (22%nat, mkAF 0 67108864 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition ss_up : sstate := mkSS 0x840 sr_atoms up_regions None up_facts.
Definition up_SH : list shent := [].

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* The symbolic state of the walk at +0x840, built from the clauses of llvm_b_st_840: the registers are the
   entry's (sr_atoms), the spilled shadow base is 32(s1) and the multiplier is the read-only word. grant's
   cg_entry (CheckGroupaWalk.v:236) at this segment's two regions. *)
Lemma up_entry : forall (cx : dctx) ly' S' (W' : world SEGS) regs' mem' md',
  @dec_b_core rc B cx ly' S' W' regs' mem' md' dec_ev_840 ->
  dec_b_slot cx (aview SEGS (w_H W') mem') 32 SHADOW_OFF ->
  YK11.getr regs' 22 = w64 (dec_b_len (d_n cx)) ->
  0 <= d_n cx < 67108864 ->
  dec_crt_cells B ->
  st_ok_pi SEGS VAL (EUP regs') ss_up
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 (BASE + 0x840)) mem' (seg_rom SEGS)))
  /\ sh_ok SEGS UPBx up_SH (EUP regs') (mrestrict (w_H W') mem').
Proof.
intros cx ly' S' W' regs' mem' md' HCORE HSLOT HS6 HN HCELLS.
assert (HLEN : 0 <= dec_b_len (d_n cx) <= 67108864)
  by (unfold dec_b_len; lia).
pose proof HCORE as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1lo & Hsp1al & Hgp & Htp & Hsaved & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
up_lits.
assert (Rsp : 70368744177664 <= spZ regs' <= 140737488355328) by (rewrite Hsp; lia).
pose proof (pa_obj_img 9 ltac:(lia)) as Hob9.
rewrite restrict_mkst_fx.
set (E := EUP regs') in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs' up_extra) n)
  by (intros n Hn; subst E; unfold EUP; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs' 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs' _ 2 2%bv eq_refl)).
assert (E9 : ew E 9 = getr regs' 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs' _ 9 9%bv eq_refl)).
assert (E22 : ew E 22 = getr regs' 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs' _ 22 22%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 0)).
assert (EO9 : ew E (A_OBJ 9) = Z_to_bv 64 (VAL (A_OBJ 9))).
{ subst E. unfold EUP.
  rewrite (Eimg_img (Ereg regs' up_extra) (A_OBJ 9) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = d_sp1 cx) by (rewrite E2; exact Hsp).
assert (Us1 : bv_unsigned (ew E 9) = d_sp1 cx)
  by (rewrite E9, Hs1; apply unsigned_lit_small; lia).
assert (Uo9 : bv_unsigned (ew E (A_OBJ 9)) = VAL (A_OBJ 9)).
{ rewrite EO9. apply unsigned_lit_small.
  split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. }
assert (HV9 : VAL (A_OBJ 9) = 66360) by (vm_compute; reflexivity).
rewrite HV9 in Uo9.
assert (U22 : bv_unsigned (ew E 22) = dec_b_len (d_n cx))
  by (rewrite E22, HS6; apply unsigned_lit_small; lia).
assert (Hsp16 : d_sp1 cx mod 16 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hsp1al; [|lia].
  destruct Hsp1al as [q Hq]. exists (2 * q). lia. }
split; [|unfold sh_ok, up_SH; apply Forall_nil].
unfold ss_up. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold up_regions, up_slot32_region, up_div36_region.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Us1. up_lits. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (d_sp1 cx) 32 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
    exact (val_mem_of_rdword SEGS (w_H W') mem' _ _ HSLOT).
  + rewrite Uo9. up_lits. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 9)) 0 8 (SLit UPSTREAM_DIV36) UPSTREAM_DIV36);
      [reflexivity | unfold UPSTREAM_DIV36; zside | zside |].
    rewrite Z.add_0_r.
    exact (up_div36_val B HCELLS ly' S' W' mem' md' HAR).
- apply pairwise_disjoint_of_extents.
  unfold up_regions, up_slot32_region, up_div36_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite Us1, Uo9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 FFS Hstk0 Hsp1lo. clear. intros.
  repeat split; try exact I. right. lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok up_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Us1, U22, E32.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  up_lits. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.

(* The registers of the entry configuration are the env's atoms below 32. *)
Lemma EUP_reg : forall regs (r : bv 5) (n : nat), Z.of_nat n = bv_unsigned r ->
  ew (EUP regs) n = getr regs r.
Proof.
intros regs r n Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
unfold EUP. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hn).
Qed.

Let RUN := @paj_run fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let BR := @paj_branch fx rc decodeb_listing PI_decodeb.

(* The callee-saved and frame registers the channel-count check leaves alone (it writes a0..a3, s2, s5). *)
Definition up_keepA : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 22%bv; 27%bv].

(* +0x840 .. +0x8a4: the channel-count check. Four paths reach the abort edge +0x8a0 and each refutes it with
   the matching lemma of lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_den.v; all four leave memory as it was (the
   code only reads) and land at +0x8a4 with s2 the shadow base and s5 the channel count. *)
Lemma up_phaseA : forall cx ly' S' (W' : world SEGS) regs' mem' md' (Q : world SEGS -> config -> Prop),
  @dec_b_core rc B cx ly' S' W' regs' mem' md' dec_ev_840 ->
  dec_b_slot cx (aview SEGS (w_H W') mem') 32 SHADOW_OFF ->
  YK11.getr regs' 22 = w64 (dec_b_len (d_n cx)) ->
  YK11.getr regs' 10 = w64 (upstream_result (dec_b_len (d_n cx))) ->
  0 <= d_n cx < 67108864 ->
  dec_crt_cells B ->
  (forall (ms2 : machine_state) md2,
     ms_mem ms2 = mem' ->
     ms2 = mkst (ms_regs ms2) (Z_to_bv 64 (BASE + 0x8a4)) mem' (seg_rom SEGS) ->
     (forall r, In r up_keepA -> getr (ms_regs ms2) r = getr regs' r) ->
     getr (ms_regs ms2) 18 = w64 SHADOW_OFF ->
     getr (ms_regs ms2) 21 = w64 (upstream_result (dec_b_len (d_n cx))) ->
     @ajournal rc dec_B_sink_head SEGS B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
       (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' W' mem' md2 dec_ev_840 ->
     SRr SEGS W' (mkCfg ms2 md2) Q) ->
  SRr SEGS W' (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x840)) mem' (seg_rom SEGS)) md') Q.
Proof.
intros cx ly' S' W' regs' mem' md' Q HC HS32 HS6 HS10 HN HCELLS HK.
destruct (up_entry cx ly' S' W' regs' mem' md' HC HS32 HS6 HN HCELLS) as [HS SHOK].
pose proof HC as (HJ & _).
assert (HEI : img_env VAL A_LIM (EUP regs')) by (unfold EUP; apply Eimg_env).
set (len := dec_b_len (d_n cx)) in *.
assert (HLEN : 0 <= len < UP_NMAX) by (unfold len, dec_b_len, UP_NMAX; lia).
assert (E22 : ew (EUP regs') 22 = Z_to_bv 64 len) by (rewrite (EUP_reg regs' 22%bv 22 eq_refl); exact HS6).
assert (E10 : ew (EUP regs') 10 = Z_to_bv 64 (upstream_result len))
  by (rewrite (EUP_reg regs' 10%bv 10 eq_refl); exact HS10).
assert (HAE : env_agree 32 (Ereg regs' up_extra) (EUP regs'))
  by (split; [intros n Hn; unfold EUP; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia | reflexivity]).
(* the four landings at +0x8a4 share this conclusion *)
assert (LAND : forall ms md2 ss,
  st_ok_pi SEGS VAL (EUP regs') ss (restrict (w_H W') ms) -> ss_resv ss = None -> ss_pc ss = 0x8a4 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) up_keepA = true ->
  sr_get (ss_regs ss) 18%bv = SOff 32 0 -> sr_get (ss_regs ss) 21%bv = SOff 10 0 ->
  ms_mem ms = mem' ->
  @ajournal rc dec_B_sink_head SEGS B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' W' (ms_mem ms) md2 dec_ev_840 ->
  SRr SEGS W' (mkCfg ms md2) Q).
{ intros ms md2 ss HS2 Hrv Hpc Hkeep H18 H21 Hm HJ2.
  apply HK; [exact Hm | | | | | rewrite <- Hm; exact HJ2].
  - rewrite (st_ok_pi_restrict_mkst (w_H W') (EUP regs') ss ms HS2 Hrv) at 1. rewrite Hpc, Hm. reflexivity.
  - exact (regs_kept_of_st_ok_pi (EUP regs') ss (restrict (w_H W') ms) regs' up_extra up_keepA HS2 HAE Hkeep).
  - rewrite (st_ok_pi_restrict_reg (w_H W') (EUP regs') ss ms 18%bv HS2), H18. cbn [sv_denot].
    unfold EUP. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs' _ 0).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (st_ok_pi_restrict_reg (w_H W') (EUP regs') ss ms 21%bv HS2), H21. cbn [sv_denot].
    rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
clear HK.
paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|].
up_memeq HF.
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb0.
- (* len < 52 *)
  paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
  psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb1.
  + exfalso. rewrite (up_abort_lt52 (EUP regs') len E22 HLEN E10 Hb0) in Hb1. discriminate.
  + paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
    eapply LAND; [exact HS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | up_memchain | exact HJ].
- paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
  psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb1.
  + (* remainder not zero *)
    paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
    psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb2.
    * exfalso. rewrite (up_abort_rem (EUP regs') len E22 HLEN E10 Hb0 Hb1) in Hb2. discriminate.
    * paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
      eapply LAND; [exact HS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | up_memchain | exact HJ].
  + paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
    psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb2.
    * (* quotient outside [2, 40] *)
      paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
      psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb3.
      -- exfalso. rewrite (up_abort_range (EUP regs') len E22 HLEN E10 Hb0 Hb2) in Hb3. discriminate.
      -- paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
         eapply LAND; [exact HS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | up_memchain | exact HJ].
    * (* the in-line count *)
      paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
      psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb3.
      -- exfalso. pose proof (up_abort_count (EUP regs') len E22 HLEN E10 Hb0 Hb1 Hb2) as Hf.
         unfold up_sa0, up_sq in Hf. rewrite Hf in Hb3. discriminate.
      -- paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
         eapply LAND; [exact HS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | up_memchain | exact HJ].
Qed.
End h.
End g.
