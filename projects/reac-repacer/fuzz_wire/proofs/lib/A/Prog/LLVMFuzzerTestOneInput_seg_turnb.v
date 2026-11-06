(* LLVMFuzzerTestOneInput_seg_turnb: u_turn_b_ok : u_turn_b_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the
   turn_b segment of the image-A walk of fuzz_wire.asan's LLVMFuzzerTestOneInput (+0xfc .. +0x144). It is the image-A
   twin of this unit's image-B lib/B/Prog/LLVMFuzzerTestOneInput_seg_turnb.v (commit adb74ccdb2a), in the form of
   fuzz_uci's lib/A/Prog/LLVMFuzzerTestOneInput_seg_turnb.v (commit 14922e68e3b0: a run of the Pa engine to a call,
   the callee's rule or contract at the call, the run from its return address).

   Four runs of the Pa engine, each from a seat with no region and the registers as atoms (Ereg regs []); this stretch
   has no load, no store and no shadow check of its own:
   - tb_A, +0xfc .. +0x100: `mv a0, s3` (the block size fsz) and the `jal` to the malloc trampoline (ra = +0x104);
     tb_call_malloc (LLVMFuzzerTestOneInput_seg_turnb_lib.v) takes the call to tb_st_m;
   - tb_B, +0x104 .. +0x11c: `beqz a0` to the abort (refuted: the block c is at or above 4096), `mv s3, a0`,
     `beqz s6`: taken (size = 1, so fn = 0) the run stops at +0x120 and tb_skip gives tb_st_c; not taken, a0 = c,
     a1 = f, a2 = fn and the `jal` to __asan_memcpy (ra = +0x120), which tb_call_cpy takes to tb_st_c;
   - tb_C, +0x120 .. +0x12c: a0 = c, a1 = f, a2 = fn and the `jal` to check_copy (ra = +0x130); tb_call_ccpy takes the
     call to tb_st_r;
   - tb_D, +0x130 .. +0x140: `beqz a0` (check_copy's result len): taken the run stops at +0x144 and tb_exit_of gives
     u_st_exit; not taken, a1 = len, a0 = c, a2 = slot and the `jal` to check_read (ra = +0x144), which tb_call_crd
     takes to u_st_exit. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05 YE00 YE01 YO09 YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v ACfn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaJournal WirePSyms WirePList WirePAddr
  WirePPa WirePPaLib WirePImg WirePPaImg WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_lib LLVMFuzzerTestOneInput_seg_turnb_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* 1. The seat                                                         *)
(* ------------------------------------------------------------------ *)

(* Every seat of this segment: no region, no fact. *)
Definition tb_nofacts : facts := mkFacts [] [] [].
Definition ss_tb (pc : Z) : sstate := mkSS pc sr_atoms [] None tb_nofacts.

Section seat. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation SEGS := (@pa_segs _ wire_listing PI_wire).
Local Abbreviation VAL := (@pa_val _ wire_listing PI_wire).
Local Abbreviation BASE := (@pa_val _ wire_listing PI_wire A_TEXT).

Lemma tb_seat : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi SEGS VAL (Eimg (PI := PI_wire) (Ereg regs [])) (ss_tb pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc.
rewrite restrict_mkst_fx. unfold ss_tb.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint]. exact I.
- exact (conj I (conj I I)).
Qed.
End seat.

(* ------------------------------------------------------------------ *)
(* 2. Tactics of the runs                                              *)
(* ------------------------------------------------------------------ *)

(* A register's symbolic value at a state (st_ok_pi, or st_ok at a call). *)
Ltac tb_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  | st_ok ?sg ?Ex ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg sg H Ex ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.
(* The write rights of a run with no region. *)
Ltac tb_awr_ro :=
  lazymatch goal with |- awr_ok ?Ey ?rsx ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ey rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ].
(* The model and the machine state after a run, named. *)
Ltac tb_md md2 ms2 :=
  lazymatch goal with |- SRr _ _ (mkCfg ?m ?mdx) _ => set (md2 := mdx) in *; clearbody md2; rename m into ms2 end.
(* The run wrote no byte: its frame (no region) gives the memory unchanged. HF / HFr / HG: the names the run tactics
   of WirePPaLib.v give the run's two frames and its growth. *)
Ltac tb_mem HF HFr HG Hm :=
  apply frame_of_read_only in HF; [|vm_compute; reflexivity]; rename HF into Hm; clear HFr HG.
(* r is in a literal list of registers. *)
Ltac tb_kin Hr := cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [tb_in|]); destruct Hr.
(* `beqz x` against the value v of the register atom n (EL: the atoms are the registers): the condition is v = 0. *)
Ltac tb_eqz Hc E0 EL n r v Rv :=
  rewrite branch_eq_U in Hc;
  rewrite (U_atom E0 n v) in Hc by first [rewrite (EL n r eq_refl), Rv; reflexivity | lia];
  rewrite U_SLit in Hc; change (zcanon 0) with 0 in Hc.

(* ------------------------------------------------------------------ *)
(* 3. The runs                                                         *)
(* ------------------------------------------------------------------ *)

Section sg. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* +0xfc .. +0x100 and the malloc of c. *)
Lemma tb_A : forall cx (W : world segs) c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> u_st_pre B MT XL cx W c ->
  SRr segs W c (tb_st_m B MT XL cx).
Proof.
intros cx W c HP HB HPRE.
destruct HPRE as (ly' & S' & regs & mem & md & f & -> & Hn & HC & HM & HR & Hgf).
pose proof HR as (R8 & R9 & R18 & R19 & R21 & R22).
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (HJ & _).
pose proof (@tb_seat (u_fx cx) rc W regs mem U_PRE) as HS.
set (E0 := Eimg (PI := PI_wire) (Ereg regs [])) in HS.
assert (HEI : img_env (@pa_val _ wire_listing PI_wire) A_LIM E0) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ wire_listing PI_wire) (SOff 22 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) E0)
  by (split; [intros nn Hnn; unfold E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = YK11.getr regs r)
  by (intros nn r Hnn; unfold E0; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia);
      apply ew_Ereg_nat; exact Hnn).
pose proof (paj_run (fx := u_fx cx) (SK := AE2k.tfib_sink_head) (PI := PI_wire) B LAWS) as RUN.
unfold u_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr (@pa_segs _ wire_listing PI_wire) Wx
    (mkCfg (@YK11.mkst (u_fx cx) regs (Z_to_bv 64 (@pa_val _ wire_listing PI_wire A_TEXT + U_PRE)) mem
      (seg_rom (@pa_segs _ wire_listing PI_wire))) md) Qx) end.
paj_run_tok RUN HS HJ SHOK Bspan; [tb_awr_ro|].
tb_md mdA ms1. tb_mem HF HFr HG Hm1.
lazymatch type of HS with st_ok _ _ ?ssx _ =>
  pose proof (regs_kept_of_st_ok (@pa_segs _ wire_listing PI_wire) E0 ssx (restrict (w_H W) ms1) regs []
    [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KA end.
cbn [ms_regs restrict] in KA.
tb_reg HS (1%bv : bv 5) R1'. tb_reg HS (10%bv : bv 5) R10'.
cbn [ms_regs restrict] in R1', R10'.
assert (R1 : YK11.getr (ms_regs ms1) 1 = w64 (WIRE_A_LLVMF + 0x104)) by (rewrite R1'; exact (codeptr_val E0 _ HEI)).
assert (R10 : YK11.getr (ms_regs ms1) 10 = w64 (u_fsz cx))
  by (rewrite R10', (tb_soff_denot E0 19 _ (EL 19%nat 19%bv eq_refl)); exact R19).
pmkst HS. rewrite Hm1 in HJ |- *.
apply (tb_call_malloc B MT XL RLO RHI cx W (ms_regs ms1) mem mdA ly' S' f HP HB Hn).
- exact (tb_core_same B cx ly' S' W regs (ms_regs ms1) mem md mdA _ _ HC HJ (fun r Hr => KA r ltac:(tb_kin Hr))).
- exact HM.
- exact (tb_keep_kept cx regs (ms_regs ms1) f (conj R8 (conj R9 (conj R18 (conj R21 R22))))
    (fun r Hr => KA r ltac:(tb_kin Hr))).
- exact R10.
- exact R1.
- exact Hgf.
Qed.

(* +0x104 .. +0x11c: the abort refuted, s3 = c, and either the join at +0x120 (fn = 0) or __asan_memcpy. *)
Lemma tb_B : forall cx (W : world segs) c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> tb_st_m B MT XL cx W c ->
  SRr segs W c (tb_st_c B MT XL cx).
Proof.
intros cx W c HP HB HST.
destruct HST as (ly' & S' & regs & mem & md & f & cb & -> & Hn & HC & HM & HK & R10 & Hgf & HNEW & HDJ).
pose proof HK as (R8 & R9 & R18 & R21 & R22).
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
destruct (tb_blocks B MT XL RLO RHI cx ly' S' W regs mem md f cb _ HP Hn HC)
  as (Hfin & Hcin & Ereq & Hfsz & Hfnr & Hf4 & Hfc & Hc4 & Hcc).
destruct (tb_base B MT XL RLO RHI cx HP HB) as (Hn26 & _).
pose proof (@alloc_ceiling_val rc) as Hce.
pose proof HC as (HJ & _).
pose proof (@tb_seat (u_fx cx) rc W regs mem 0x104) as HS.
set (E0 := Eimg (PI := PI_wire) (Ereg regs [])) in HS.
assert (HEI : img_env (@pa_val _ wire_listing PI_wire) A_LIM E0) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ wire_listing PI_wire) (SOff 22 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) E0)
  by (split; [intros nn Hnn; unfold E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = YK11.getr regs r)
  by (intros nn r Hnn; unfold E0; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia);
      apply ew_Ereg_nat; exact Hnn).
pose proof (paj_run (fx := u_fx cx) (SK := AE2k.tfib_sink_head) (PI := PI_wire) B LAWS) as RUN.
pose proof (paj_run_to (fx := u_fx cx) (SK := AE2k.tfib_sink_head) (PI := PI_wire) B LAWS) as RUNTO.
unfold u_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr (@pa_segs _ wire_listing PI_wire) Wx
    (mkCfg (@YK11.mkst (u_fx cx) regs (Z_to_bv 64 (@pa_val _ wire_listing PI_wire A_TEXT + 0x104)) mem
      (seg_rom (@pa_segs _ wire_listing PI_wire))) md) Qx) end.
(* +0x104 `beqz a0`: a0 = c >= 4096, so the abort at +0x180 is not reached *)
psrr_branch_tok RUN (paj_branch (fx := u_fx cx) (PI := PI_wire)) HS SHOK Bspan.
{ exfalso. tb_eqz Hc E0 EL 10%nat (10%bv : bv 5) cb R10. apply Z.eqb_eq in Hc. lia. }
clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan; [tb_awr_ro|].
tb_md mdA ms1. tb_mem HF HFr HG Hm1.
(* +0x10c `beqz s6`: s6 = size - 1 *)
psrr_branch_tok RUN (paj_branch (fx := u_fx cx) (PI := PI_wire)) HS SHOK Bspan.
- (* size = 1: fn = 0, the join at +0x120 *)
  assert (Hfn0 : u_fn cx = 0).
  { tb_eqz Hc E0 EL 22%nat (22%bv : bv 5) (u_n cx - 1) R22. apply Z.eqb_eq in Hc.
    unfold u_fn, WIRE_RECV_MAX. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x120; [tb_awr_ro|].
  tb_md mdB ms2. tb_mem HF HFr HG Hm2.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    pose proof (regs_kept_of_st_ok_pi E0 ssx (restrict (w_H W) ms2) regs []
      [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KA end.
  cbn [ms_regs restrict] in KA.
  tb_reg HS (19%bv : bv 5) R19'. cbn [ms_regs restrict] in R19'.
  assert (R19 : YK11.getr (ms_regs ms2) 19 = w64 cb)
    by (rewrite R19', (tb_soff_denot E0 10 _ (EL 10%nat 10%bv eq_refl)); exact R10).
  pmkst HS. rewrite Hm2, Hm1 in HJ |- *.
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rg _ ?mm _) ?mdx) _ =>
    change (SRr segs W (u_cfg cx 0x120 rg mm mdx) (tb_st_c B MT XL cx)) end.
  apply SRr_ret.
  apply (tb_skip B MT XL cx W (ms_regs ms2) mem mdB ly' S' f cb Hn Hfn0).
  + exact (tb_core_same B cx ly' S' W regs (ms_regs ms2) mem md mdB _ _ HC HJ (fun r Hr => KA r ltac:(tb_kin Hr))).
  + exact HM.
  + exact (tb_keep_kept cx regs (ms_regs ms2) f HK (fun r Hr => KA r ltac:(tb_kin Hr))).
  + exact R19.
  + exact Hgf.
  + exact HNEW.
  + exact HDJ.
- (* size > 1: fn > 0, __asan_memcpy (c, f, fn) *)
  assert (Hfn0 : 0 < u_fn cx).
  { tb_eqz Hc E0 EL 22%nat (22%bv : bv 5) (u_n cx - 1) R22. apply Z.eqb_neq in Hc.
    unfold u_fn, WIRE_RECV_MAX. lia. }
  paj_run_tok RUN HS HJ SHOK Bspan; [tb_awr_ro|].
  tb_md mdB ms2. tb_mem HF HFr HG Hm2.
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    pose proof (regs_kept_of_st_ok (@pa_segs _ wire_listing PI_wire) E0 ssx (restrict (w_H W) ms2) regs []
      [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KA end.
  cbn [ms_regs restrict] in KA.
  tb_reg HS (1%bv : bv 5) R1'. tb_reg HS (10%bv : bv 5) R10'. tb_reg HS (11%bv : bv 5) R11'.
  tb_reg HS (12%bv : bv 5) R12'. tb_reg HS (19%bv : bv 5) R19'.
  cbn [ms_regs restrict] in R1', R10', R11', R12', R19'.
  assert (R1 : YK11.getr (ms_regs ms2) 1 = w64 (WIRE_A_LLVMF + 0x120)) by (rewrite R1'; exact (codeptr_val E0 _ HEI)).
  assert (R10x : YK11.getr (ms_regs ms2) 10 = w64 cb)
    by (rewrite R10', (tb_soff_denot E0 10 _ (EL 10%nat 10%bv eq_refl)); exact R10).
  assert (R11 : YK11.getr (ms_regs ms2) 11 = w64 f)
    by (rewrite R11', (tb_soff_denot E0 8 _ (EL 8%nat 8%bv eq_refl)); exact R8).
  assert (R12 : YK11.getr (ms_regs ms2) 12 = w64 (u_fn cx))
    by (rewrite R12', (tb_soff_denot E0 9 _ (EL 9%nat 9%bv eq_refl)); exact R9).
  assert (R19 : YK11.getr (ms_regs ms2) 19 = w64 cb)
    by (rewrite R19', (tb_soff_denot E0 10 _ (EL 10%nat 10%bv eq_refl)); exact R10).
  pmkst HS. rewrite Hm2, Hm1 in HJ |- *.
  apply (tb_call_cpy B MT XL RLO RHI cx W (ms_regs ms2) mem mdB ly' S' f cb HP HB Hn Hfn0).
  + exact (tb_core_same B cx ly' S' W regs (ms_regs ms2) mem md mdB _ _ HC HJ (fun r Hr => KA r ltac:(tb_kin Hr))).
  + exact HM.
  + exact (tb_keep_kept cx regs (ms_regs ms2) f HK (fun r Hr => KA r ltac:(tb_kin Hr))).
  + exact R19.
  + exact R10x.
  + exact R11.
  + exact R12.
  + exact R1.
  + exact Hgf.
  + exact HNEW.
  + exact HDJ.
Qed.

(* +0x120 .. +0x12c and check_copy. *)
Lemma tb_C : forall cx (W : world segs) c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> tb_st_c B MT XL cx W c ->
  SRr segs W c (tb_st_r B MT XL cx).
Proof.
intros cx W c HP HB HST.
destruct HST as (ly' & S' & regs & mem & md & f & cb & -> & Hn & HC & HM & HK & R19 & Hgf & Hgc & HNEW & HDJ).
pose proof HK as (R8 & R9 & R18 & R21 & R22).
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (HJ & _).
pose proof (@tb_seat (u_fx cx) rc W regs mem 0x120) as HS.
set (E0 := Eimg (PI := PI_wire) (Ereg regs [])) in HS.
assert (HEI : img_env (@pa_val _ wire_listing PI_wire) A_LIM E0) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ wire_listing PI_wire) (SOff 22 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) E0)
  by (split; [intros nn Hnn; unfold E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = YK11.getr regs r)
  by (intros nn r Hnn; unfold E0; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia);
      apply ew_Ereg_nat; exact Hnn).
pose proof (paj_run (fx := u_fx cx) (SK := AE2k.tfib_sink_head) (PI := PI_wire) B LAWS) as RUN.
unfold u_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr (@pa_segs _ wire_listing PI_wire) Wx
    (mkCfg (@YK11.mkst (u_fx cx) regs (Z_to_bv 64 (@pa_val _ wire_listing PI_wire A_TEXT + 0x120)) mem
      (seg_rom (@pa_segs _ wire_listing PI_wire))) md) Qx) end.
paj_run_tok RUN HS HJ SHOK Bspan; [tb_awr_ro|].
tb_md mdA ms1. tb_mem HF HFr HG Hm1.
lazymatch type of HS with st_ok _ _ ?ssx _ =>
  pose proof (regs_kept_of_st_ok (@pa_segs _ wire_listing PI_wire) E0 ssx (restrict (w_H W) ms1) regs []
    [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KA end.
cbn [ms_regs restrict] in KA.
tb_reg HS (1%bv : bv 5) R1'. tb_reg HS (10%bv : bv 5) R10'. tb_reg HS (11%bv : bv 5) R11'.
tb_reg HS (12%bv : bv 5) R12'.
cbn [ms_regs restrict] in R1', R10', R11', R12'.
assert (R1 : YK11.getr (ms_regs ms1) 1 = w64 (WIRE_A_LLVMF + 0x130)) by (rewrite R1'; exact (codeptr_val E0 _ HEI)).
assert (R10 : YK11.getr (ms_regs ms1) 10 = w64 cb)
  by (rewrite R10', (tb_soff_denot E0 19 _ (EL 19%nat 19%bv eq_refl)); exact R19).
assert (R11 : YK11.getr (ms_regs ms1) 11 = w64 f)
  by (rewrite R11', (tb_soff_denot E0 8 _ (EL 8%nat 8%bv eq_refl)); exact R8).
assert (R12 : YK11.getr (ms_regs ms1) 12 = w64 (u_fn cx))
  by (rewrite R12', (tb_soff_denot E0 9 _ (EL 9%nat 9%bv eq_refl)); exact R9).
pmkst HS. rewrite Hm1 in HJ |- *.
apply (tb_call_ccpy B MT XL RLO RHI cx W (ms_regs ms1) mem mdA ly' S' f cb HP HB Hn).
- exact (tb_core_same B cx ly' S' W regs (ms_regs ms1) mem md mdA _ _ HC HJ (fun r Hr => KA r ltac:(tb_kin Hr))).
- exact HM.
- rewrite (KA 8%bv ltac:(tb_in)). exact R8.
- rewrite (KA 18%bv ltac:(tb_in)). exact R18.
- rewrite (KA 19%bv ltac:(tb_in)). exact R19.
- exact R10.
- exact R11.
- exact R12.
- exact R1.
- exact Hgf.
- exact Hgc.
- exact HNEW.
- exact HDJ.
Qed.

(* +0x130 .. +0x140: `beqz a0` on len, and check_read unless len = 0. *)
Lemma tb_D : forall cx (W : world segs) c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> tb_st_r B MT XL cx W c ->
  SRr segs W c (u_st_exit B MT XL cx).
Proof.
intros cx W c HP HB HST.
destruct HST as (ly' & S' & regs & mem & md & f & cb & len & bs & -> & Hn & HC & HM & R8 & R18 & R19 & R10 & Hl
  & Hbs & Hgc).
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
destruct (tb_base B MT XL RLO RHI cx HP HB) as (Hn26 & _).
pose proof HC as (HJ & _).
pose proof (@tb_seat (u_fx cx) rc W regs mem 0x130) as HS.
set (E0 := Eimg (PI := PI_wire) (Ereg regs [])) in HS.
assert (HEI : img_env (@pa_val _ wire_listing PI_wire) A_LIM E0) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ wire_listing PI_wire) (SOff 22 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) E0)
  by (split; [intros nn Hnn; unfold E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = YK11.getr regs r)
  by (intros nn r Hnn; unfold E0; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia);
      apply ew_Ereg_nat; exact Hnn).
pose proof (paj_run (fx := u_fx cx) (SK := AE2k.tfib_sink_head) (PI := PI_wire) B LAWS) as RUN.
pose proof (paj_run_to (fx := u_fx cx) (SK := AE2k.tfib_sink_head) (PI := PI_wire) B LAWS) as RUNTO.
unfold u_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr (@pa_segs _ wire_listing PI_wire) Wx
    (mkCfg (@YK11.mkst (u_fx cx) regs (Z_to_bv 64 (@pa_val _ wire_listing PI_wire A_TEXT + 0x130)) mem
      (seg_rom (@pa_segs _ wire_listing PI_wire))) md) Qx) end.
psrr_branch_tok RUN (paj_branch (fx := u_fx cx) (PI := PI_wire)) HS SHOK Bspan.
- (* len = 0: to +0x144 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x144; [tb_awr_ro|].
  tb_md mdA ms1. tb_mem HF HFr HG Hm1.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    pose proof (regs_kept_of_st_ok_pi E0 ssx (restrict (w_H W) ms1) regs []
      [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KA end.
  cbn [ms_regs restrict] in KA.
  pmkst HS. rewrite Hm1 in HJ |- *.
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rg _ ?mm _) ?mdx) _ =>
    change (SRr segs W (u_cfg cx U_EXIT rg mm mdx) (u_st_exit B MT XL cx)) end.
  apply SRr_ret.
  apply (tb_exit_of B MT XL RLO RHI cx W (ms_regs ms1) mem mdA ly' S' f cb (U_EV_PRE + 1 + PCPY.CC_EV)
    (U_C_F MT cx + mo_malloc MT (u_fsz cx) + PCPY.wire_check_copy_cost MT (u_fn cx)) HP Hn).
  + exact (tb_core_same B cx ly' S' W regs (ms_regs ms1) mem md mdA _ _ HC HJ (fun r Hr => KA r ltac:(tb_kin Hr))).
  + reflexivity.
  + exact HM.
  + exact (tb_exit_cost B MT XL RLO RHI cx HP ltac:(lia)).
  + rewrite (KA 8%bv ltac:(tb_in)). exact R8.
  + rewrite (KA 19%bv ltac:(tb_in)). exact R19.
- (* len <> 0: check_read (c, len, slot) *)
  paj_run_tok RUN HS HJ SHOK Bspan; [tb_awr_ro|].
  tb_md mdA ms1. tb_mem HF HFr HG Hm1.
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    pose proof (regs_kept_of_st_ok (@pa_segs _ wire_listing PI_wire) E0 ssx (restrict (w_H W) ms1) regs []
      [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KA end.
  cbn [ms_regs restrict] in KA.
  tb_reg HS (1%bv : bv 5) R1'. tb_reg HS (10%bv : bv 5) R10'. tb_reg HS (11%bv : bv 5) R11'.
  tb_reg HS (12%bv : bv 5) R12'.
  cbn [ms_regs restrict] in R1', R10', R11', R12'.
  assert (R1 : YK11.getr (ms_regs ms1) 1 = w64 (WIRE_A_LLVMF + 0x144)) by (rewrite R1'; exact (codeptr_val E0 _ HEI)).
  assert (R10x : YK11.getr (ms_regs ms1) 10 = w64 cb)
    by (rewrite R10', (tb_soff_denot E0 19 _ (EL 19%nat 19%bv eq_refl)); exact R19).
  assert (R11 : YK11.getr (ms_regs ms1) 11 = w64 len)
    by (rewrite R11', (tb_soff_denot E0 10 _ (EL 10%nat 10%bv eq_refl)); exact R10).
  assert (R12 : YK11.getr (ms_regs ms1) 12 = w64 (u_slot cx))
    by (rewrite R12', (tb_soff_denot E0 18 _ (EL 18%nat 18%bv eq_refl)); exact R18).
  pmkst HS. rewrite Hm1 in HJ |- *.
  apply (tb_call_crd B MT XL RLO RHI cx W (ms_regs ms1) mem mdA ly' S' f cb len bs HP HB Hn).
  + exact (tb_core_same B cx ly' S' W regs (ms_regs ms1) mem md mdA _ _ HC HJ (fun r Hr => KA r ltac:(tb_kin Hr))).
  + exact HM.
  + rewrite (KA 8%bv ltac:(tb_in)). exact R8.
  + rewrite (KA 19%bv ltac:(tb_in)). exact R19.
  + exact R10x.
  + exact R11.
  + exact R12.
  + exact R1.
  + exact Hl.
  + exact Hbs.
  + exact Hgc.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Theorem u_turn_b_ok : u_turn_b_stmt B MT XL RLO RHI.
Proof.
intros HP cx W c HB HPRE.
eapply SRr_bind; [exact (tb_A cx W c HP HB HPRE)|].
intros W1 c1 _ H1.
eapply SRr_bind; [exact (tb_B cx W1 c1 HP HB H1)|].
intros W2 c2 _ H2.
eapply SRr_bind; [exact (tb_C cx W2 c2 HP HB H2)|].
intros W3 c3 _ H3.
exact (tb_D cx W3 c3 HP HB H3).
Qed.
End sg.
