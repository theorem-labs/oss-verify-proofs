(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepReallocf.v (commit 3cae605a900a, blob c0799ff25ac8) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from cgif_file_fuzzer asan-ubsan ce511d541cda (pin 1c29845fe605), the cf layer at part 3c; module paths changed; 4 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YE08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB15 AFff.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0v YK13 YG0b YFfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.Z Require Import Placement.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RepMmapcf RepUnmapcf RepMemKcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RepReallocD.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RepReallocBcf.

Ltac rintro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Ltac num := unfold REALLOC_STK, REALLOC_FRAME, RepMmapcf.MOD_STK, TFIB_IMG_END, TFIB_IMG_LO, TASK_SIZE in *.
Ltac fr_ok :=
  let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
  try unfold SS_R in Hr; cbn [ss_mem add_cond] in Hr;
  try unfold rSTKr, rVEC, rPSP, rPS, flit8 in Hr;
  repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; first [left; lia | right; num; lia] |]);
  try destruct Hr.
Ltac regv HS r :=
  lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
  rewrite (st_ok_reg_denot H E ss ms r HS);
  let t := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with t end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma ask_of_amreal : forall {R : Type} (snap : astate) (ncap : Z) (K : Z -> itree astate R) W c Q,
  amreal tfibsegs (IAsk (KMmapSec ncap) snap K) W c Q -> SRr tfibsegs W c (RepMmapcf.mmap_node_post snap ncap K Q).
Proof. intros R snap ncap K W c Q H. exact H. Qed.

Lemma round_val' : forall x, 0 < x < 2 ^ 48 ->
  zcanon (Z.land (zcanon (x + 4095)) (zcanon 18446744073709547520)) = page_round_up_Z x.
Proof.
intros x Hx. rewrite <- (RepMmapcf.round_val x Hx). change (zcanon 0) with 0. rewrite Z.add_0_r.
unfold zcanon, M64. symmetry. apply Z.mod_mod. lia.
Qed.
Lemma amreal_use_AI : forall {R : Type} (t : itree astate R) W c Q,
  (AI tfibsegs (w_H W) (w_A W) (cfg_model c) -> amreal tfibsegs t W c Q) -> amreal tfibsegs t W c Q.
Proof.
intros R t W c Q H.
eapply (amreal_SRr_pre tfibsegs t W c Q (fun W' c' => W' = W /\ c' = c /\ AI tfibsegs (w_H W) (w_A W) (cfg_model c))).
- apply SRr_use_AI. intros HAI. apply SRr_ret. split; [reflexivity | split; [reflexivity | exact HAI]].
- intros W' c' _ (-> & -> & HAI). exact (H HAI).
Qed.
Lemma val_mem_tr : forall (H H' : word -> bool) (mem mem' : word -> option byte) a (n : nat) v,
  (forall k, (k < n)%nat -> mrestrict H' mem' (Z_to_bv 64 (a + Z.of_nat k)) = mrestrict H mem (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem tfibsegs (mrestrict H mem) a n v -> val_mem tfibsegs (mrestrict H' mem') a n v.
Proof.
intros H H' mem mem' a n v Hfr Hv k Hk. unfold mbyte. rewrite (Hfr k Hk). exact (Hv k Hk).
Qed.

Definition Htail : realloc_tail_spec := realloc_tail.

Theorem realloc_node : forall {R : Type} (K : Z -> itree astate R) (Q : R -> world tfibsegs -> config -> Prop)
  (snap : astate) (rq : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (v nb d cap sz : Z),
realloc_pre W regs mem md v nb d cap sz ->
(forall W' c', realloc_post W regs mem md v nb d cap sz W' c' -> amreal tfibsegs (K 1) W' c' Q) ->
amreal tfibsegs (IAsk (KMmapSec rq) snap K) W (mkCfg (mkst regs (w64 A_REALLOC) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros R K Q snap rq W regs mem md v nb d cap sz HPRE HK.
pose proof HPRE as HPRE0. unfold realloc_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (H10 & H11 & Hra & MW & Hnb0 & Hnb1 & Hsz & Hszc & Hv0 & Hv1 & Hval & HVD & HVC & HVS & HVW &
  DVS & DVP1 & DVP2 & Hd0 & Hdcap & OLD & OLDP & DOS & DOV & HPSP & HPS & HFL & HDPM & HML & NOREF & GAP & GLAZY & GBUD &
  Hal & Hsp & HPRES).
pose proof Hwx_tfa as Hwx.
pose proof (u64_range (getr regs 2)) as Usp. set (sp := bv_unsigned (getr regs 2)) in *.
set (ncap := page_round_up_Z nb) in *.
assert (SPE : bv_unsigned (getr regs 2) = sp) by reflexivity.
assert (NCE : page_round_up_Z nb = ncap) by reflexivity.
assert (NCb : nb <= ncap <= nb + 4095) by (pose proof (YK02.page_round_up_Z_bounds nb ltac:(lia)) as X; unfold page_size in X; subst ncap; lia).
assert (NCm : ncap mod 4096 = 0) by (exact (page_round_up_Z_mod nb)).
assert (PRU : page_round_up_Z ncap = ncap) by (apply YK02.page_round_up_Z_aligned; [lia | exact NCm]).
assert (Hdc : 0 <= d /\ 0 <= cap /\ d + cap <= 2 ^ 47) by (unfold TASK_SIZE in Hdcap; lia).
assert (MWF0 : MWF md) by (exact (proj1 (amwf_MWF md) (proj1 MW))).
apply RepMmapcf.amreal_mmap_ask.
set (E0 := Ereg regs [w64 d; w64 cap; w64 sz]).
assert (E2 : ew E0 2 = getr regs 2) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 2 2%bv eq_refl)).
assert (E10 : ew E0 10 = w64 v) by (rewrite <- H10; exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 10 10%bv eq_refl)).
assert (E11 : ew E0 11 = w64 nb) by (rewrite <- H11; exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 11 11%bv eq_refl)).
assert (E8 : ew E0 8 = getr regs (Z_to_bv 5 8)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 8 (Z_to_bv 5 8) eq_refl)).
assert (E9 : ew E0 9 = getr regs (Z_to_bv 5 9)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 9 (Z_to_bv 5 9) eq_refl)).
assert (E18 : ew E0 18 = getr regs (Z_to_bv 5 18)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 18 (Z_to_bv 5 18) eq_refl)).
assert (E1r : ew E0 1 = getr regs (Z_to_bv 5 1)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 1 (Z_to_bv 5 1) eq_refl)).
assert (E3 : ew E0 3 = getr regs (Z_to_bv 5 3)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 3 (Z_to_bv 5 3) eq_refl)).
assert (E4 : ew E0 4 = getr regs (Z_to_bv 5 4)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 4 (Z_to_bv 5 4) eq_refl)).
assert (E19 : ew E0 19 = getr regs (Z_to_bv 5 19)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 19 (Z_to_bv 5 19) eq_refl)).
assert (E20 : ew E0 20 = getr regs (Z_to_bv 5 20)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 20 (Z_to_bv 5 20) eq_refl)).
assert (E21 : ew E0 21 = getr regs (Z_to_bv 5 21)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 21 (Z_to_bv 5 21) eq_refl)).
assert (E22 : ew E0 22 = getr regs (Z_to_bv 5 22)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 22 (Z_to_bv 5 22) eq_refl)).
assert (E23 : ew E0 23 = getr regs (Z_to_bv 5 23)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 23 (Z_to_bv 5 23) eq_refl)).
assert (E24 : ew E0 24 = getr regs (Z_to_bv 5 24)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 24 (Z_to_bv 5 24) eq_refl)).
assert (E25 : ew E0 25 = getr regs (Z_to_bv 5 25)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 25 (Z_to_bv 5 25) eq_refl)).
assert (E26 : ew E0 26 = getr regs (Z_to_bv 5 26)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 26 (Z_to_bv 5 26) eq_refl)).
assert (E27 : ew E0 27 = getr regs (Z_to_bv 5 27)) by (exact (ew_Ereg_nat regs [w64 d; w64 cap; w64 sz] 27 (Z_to_bv 5 27) eq_refl)).
assert (E32 : ew E0 32 = w64 d) by reflexivity.
assert (E33 : ew E0 33 = w64 cap) by reflexivity.
assert (E34 : ew E0 34 = w64 sz) by reflexivity.
assert (BV2 : bv_unsigned (ew E0 2) = sp) by (rewrite E2; reflexivity).
assert (BV10 : bv_unsigned (ew E0 10) = v) by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
assert (BV11 : bv_unsigned (ew E0 11) = nb) by (rewrite E11; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok tfibsegs E0 SS_R (restrict (w_H W) (mkst regs (w64 A_REALLOC) mem (seg_rom tfibsegs)))).
{ unfold SS_R, A_REALLOC, w64. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. unfold rSTKr, rVEC, rPSP, rPS, flit8.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
+ apply (region_ok_stack tfibsegs E0 _ 2 sp (- REALLOC_FRAME)); [exact BV2 | num; lia | lia |].
intros x Hx. apply apresent_writable; [num; lia | apply HPRES; num; lia].
+ rintro. fold E0. rewrite BV10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
* eapply (chunk_ok_val tfibsegs E0 _ _ _ _ _ d); [rewrite sdo0, E32; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HVD].
* eapply (chunk_ok_val tfibsegs E0 _ _ _ _ _ cap); [rewrite sdo0, E33; reflexivity | cbn; lia | cbn; lia | exact HVC].
* eapply (chunk_ok_val tfibsegs E0 _ _ _ _ _ sz); [rewrite sdo0, E34; reflexivity | cbn; lia | cbn; lia | exact HVS].
+ rintro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HPSP].
+ rintro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HPS].
- apply pairwise_disjoint_of_extents. unfold rSTKr, rVEC, rPSP, rPS, flit8, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
fold E0. rewrite BV2, BV10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. num. repeat split; lia.
- split; [|split; exact I]. cbn [IFR f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E0.
rewrite BV2, BV10, BV11, E34. unfold w64. rewrite !unsigned_lit_small by lia. num.
repeat split; first [lia | change (2 ^ 4) with 16; exact Hal | change (2 ^ 3) with 8; exact Hval | rewrite Z.mod_1_r; reflexivity]. }
clearbody E0.

srr_run_to_sh tbl_rea_ok HS 0x66988. rename HF into HF1. clear HFr.
srr_branch_sh tbl_rea_ok HS.
{ exfalso. rewrite !sdo0, E11, E34 in Hc. unfold branch_taken, bv_ltu in Hc. unfold w64 in Hc.
rewrite !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc. lia. }
clear Hc. srr_run_to_sh tbl_rea_ok HS 0x66988. rename HF into HF2. clear HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
assert (FRA : forall x : word, ~ (sp - REALLOC_FRAME <= bv_unsigned x < sp) -> ms_mem msA x = mem x).
{ intros x Hx. etransitivity; [apply (frame_of_outside E0 _ _ _ x HF2) | apply (frame_of_outside E0 _ _ _ x HF1)]; fr_ok. }
clear HF1 HF2.
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing _ ?mt _)) _ => rename mt into matA end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ msA HS eq_refl) as Hshape.
lazymatch type of Hshape with _ = mkst _ ?pcv _ _ => replace pcv with (w64 0x66988) in Hshape by reflexivity end.
rewrite Hshape. clear Hshape.
assert (RA1 : getr (ms_regs msA) 1 = w64 0x597a0) by (regv HS (1%bv : bv 5); reflexivity).
assert (RA2 : bv_unsigned (getr (ms_regs msA) 2) = sp - REALLOC_FRAME).
{ regv HS (2%bv : bv 5). cbn [sv_denot]. rewrite BV2. apply unsigned_lit_small. num. lia. }
assert (RA10 : getr (ms_regs msA) 10 = w64 ncap).
{ regv HS (10%bv : bv 5). rewrite denot_lit_U. unfold w64. f_equal. rewrite U_zev by reflexivity.
cbn [zev zalu_raw]. unfold rho_of. rewrite BV11. apply RepMmapcf.round_val. lia. }
assert (RA8 : getr (ms_regs msA) (Z_to_bv 5 8) = w64 v) by (regv HS (Z_to_bv 5 8); rewrite sdo0; exact E10).
assert (RA9 : getr (ms_regs msA) (Z_to_bv 5 9) = w64 ncap).
{ regv HS (Z_to_bv 5 9). rewrite denot_lit_U. unfold w64. f_equal. rewrite U_zev by reflexivity.
cbn [zev zalu_raw]. unfold rho_of. rewrite BV11. apply round_val'. lia. }
assert (RAcs : forall r : Z, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr (ms_regs msA) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr.
assert (C : r = 3 \/ r = 4 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]; subst r.
- regv HS (Z_to_bv 5 3); rewrite sdo0; exact E3.
- regv HS (Z_to_bv 5 4); rewrite sdo0; exact E4.
- regv HS (Z_to_bv 5 19); rewrite sdo0; exact E19.
- regv HS (Z_to_bv 5 20); rewrite sdo0; exact E20.
- regv HS (Z_to_bv 5 21); rewrite sdo0; exact E21.
- regv HS (Z_to_bv 5 22); rewrite sdo0; exact E22.
- regv HS (Z_to_bv 5 23); rewrite sdo0; exact E23.
- regv HS (Z_to_bv 5 24); rewrite sdo0; exact E24.
- regv HS (Z_to_bv 5 25); rewrite sdo0; exact E25.
- regv HS (Z_to_bv 5 26); rewrite sdo0; exact E26.
- regv HS (Z_to_bv 5 27); rewrite sdo0; exact E27. }
assert (SW1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msA)) (sp - 8) 8 (bv_unsigned (getr regs (Z_to_bv 5 1)))).
{ rewrite <- E1r. eapply (chunk_val_at (w_H W) E0 _ msA 0%nat 3%nat _ _ 8%N); [exact HS | reflexivity | reflexivity
  | cbn [YP09.r_base base_val]; rewrite BV2; num; lia | rewrite sdo0; symmetry; apply Z_to_bv_bv_unsigned
  | pose proof (u64_range (ew E0 1)); cbn; lia | cbn; lia]. }
assert (SW2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msA)) (sp - 16) 8 (bv_unsigned (getr regs (Z_to_bv 5 8)))).
{ rewrite <- E8. eapply (chunk_val_at (w_H W) E0 _ msA 0%nat 2%nat _ _ 8%N); [exact HS | reflexivity | reflexivity
  | cbn [YP09.r_base base_val]; rewrite BV2; num; lia | rewrite sdo0; symmetry; apply Z_to_bv_bv_unsigned
  | pose proof (u64_range (ew E0 8)); cbn; lia | cbn; lia]. }
assert (SW3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msA)) (sp - 24) 8 (bv_unsigned (getr regs (Z_to_bv 5 9)))).
{ rewrite <- E9. eapply (chunk_val_at (w_H W) E0 _ msA 0%nat 1%nat _ _ 8%N); [exact HS | reflexivity | reflexivity
  | cbn [YP09.r_base base_val]; rewrite BV2; num; lia | rewrite sdo0; symmetry; apply Z_to_bv_bv_unsigned
  | pose proof (u64_range (ew E0 9)); cbn; lia | cbn; lia]. }
assert (SW4 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msA)) (sp - 32) 8 (bv_unsigned (getr regs (Z_to_bv 5 18)))).
{ rewrite <- E18. eapply (chunk_val_at (w_H W) E0 _ msA 0%nat 0%nat _ _ 8%N); [exact HS | reflexivity | reflexivity
  | cbn [YP09.r_base base_val]; rewrite BV2; num; lia | rewrite sdo0; symmetry; apply Z_to_bv_bv_unsigned
  | pose proof (u64_range (ew E0 18)); cbn; lia | cbn; lia]. }
assert (FPRES : forall b, sp - REALLOC_FRAME <= b < sp -> apresent (w_H W) (ms_mem msA) b).
{ intros b Hb. eapply (st_ok_window_apresent (w_H W) E0 _ msA 0%nat _ b HS); [reflexivity
  | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite BV2; num; lia | num; lia]. }
clear HS.
apply SRr_use_AI. intros HAIA. cbn [cfg_model] in HAIA.
assert (MWFA : MWF (with_vm_backing (m_vm_lazy md) matA md)) by (exact (MWF_same_but_materialized md _ MWF0 (with_vm_backing_same md matA))).
assert (Hn34 : mmap_noreserve_b (w64 34) = false) by (vm_compute; reflexivity).
assert (HALT : m_halted md = None) by (pose proof (AI_halted tfibsegs (w_H W) (w_A W) _ HAIA) as X; rewrite m_halted_wvb in X; exact X).
apply ask_of_amreal.
pose proof (RepMmapcf.mmapordie_node_b K Q snap rq W (ms_regs msA) (ms_mem msA) (with_vm_backing (m_vm_lazy md) matA md) ncap) as HM.
cbv zeta in HM. rewrite PRU in HM. rewrite RA2 in HM.
apply HM; clear HM.
- exact RA10.
- rewrite RA1. apply YK0s.ret_ok_even. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- lia.
- lia.
- apply (AF0x.val_mem_frame (w_H W) mem); [intros k Hk; apply FRA; rewrite unsigned_lit_small by (num; lia); num; lia | exact HPSP].
- apply (AF0x.val_mem_frame (w_H W) mem); [intros k Hk; apply FRA; rewrite unsigned_lit_small by (num; lia); num; lia | exact HPS].
- apply (AF0x.val_mem_frame (w_H W) mem); [intros k Hk; apply FRA; rewrite unsigned_lit_small by (num; lia); num; lia | exact HFL].
- apply (AF0x.val_mem_frame (w_H W) mem); [intros k Hk; apply FRA; rewrite unsigned_lit_small by (num; lia); num; lia | exact HDPM].
- apply (AF0x.val_mem_frame (w_H W) mem); [intros k Hk; apply FRA; rewrite unsigned_lit_small by (num; lia); num; lia | exact HML].
- exact MWFA.
- intros mt Hmt. rewrite wvb_collapse. exact (NOREF mt Hmt).
- intros a0 Ha0. destruct (GAP a0 Ha0) as (G1 & G2 & G3). num. lia.
- num. lia.
- num. lia.
- intros b Hb. apply (apresent_same (w_H W) mem); [apply FRA; rewrite unsigned_lit_small by (num; lia); num; lia | apply HPRES; num; lia].
- intros a regs1 mem1 mat1. cbv zeta. intros Ha64 HG HP1 R1_10 FR1 ZR1 PR1 IO1.
rewrite wvb_collapse in HG, IO1 |- *.
assert (UA : bv_unsigned (w64 a) = a) by (unfold w64; apply unsigned_lit_small; lia).
assert (HGmd : grant_ok_na_pin md (w64 a) ncap = true) by exact HG.
destruct (RepMmapcf.grant_pin_parts md (w64 a) ncap HGmd) as (Gal & Gpos & Gtop & Grf). rewrite UA in Gal, Gpos, Gtop.
pose proof (RepMmapcf.alloc_top_lt (m_vmmaps md)) as ATL.
destruct (GAP (w64 a) HGmd) as (Ga1 & Ga2 & Ga3). rewrite UA in Ga1, Ga2, Ga3.
assert (UAn : bv_unsigned (w64 ncap) = ncap) by (unfold w64; apply unsigned_lit_small; lia).
assert (OLDAP : cap = 0 \/ d + cap <= a \/ a + ncap <= d).
{ destruct OLD as [Hc0|(_ & _ & _ & _ & OIn)]; [left; exact Hc0|].
  right. destruct (grant_apart_map md a ncap d cap HGmd ltac:(lia) ltac:(lia) OIn ltac:(lia) ltac:(lia)); lia. }
assert (MWFN : MWF (with_vm_backing (m_vm_lazy md) mat1 md)) by (exact (MWF_same_but_materialized md _ MWF0 (with_vm_backing_same md mat1))).
apply amreal_use_AI. intros HAI1. cbn [cfg_model] in HAI1.
assert (HAIN : AI tfibsegs (w_H W) (w_A W) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ apply (AI_transport tfibsegs (w_H W) (w_A W) (with_mmap_backing (w64 34) (w64 a) (w64 ncap) (mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy md) mat1 md)))); [exact HAI1
  | rewrite wmb34; reflexivity | rewrite wmb34; reflexivity | rewrite m_halted_wvb; exact HALT
  | rewrite eager_used_wvb, m_vmmaps_wvb; lia]. }
destruct (commit_AI tfibsegs (w_H W) (w_A W) (with_vm_backing (m_vm_lazy md) mat1 md) true (w64 34) (w64 a) ncap
  HAIN MWFN Hn34 ltac:(rewrite UA; unfold page_size; exact Gal) ltac:(lia)
  ltac:(rewrite UA, PRU, m_vmmaps_wvb; exact Gtop)
  ltac:(cbv zeta; rewrite PRU, !m_vmmaps_wvb; exact Grf)
  ltac:(rewrite eager_used_wvb, m_vmmaps_wvb, PRU; lia)) as [[AIg MWFg] _].
rewrite PRU in MWFg. unfold grant_md in MWFg.
assert (AMWF1 : amwf (with_mmap_backing (w64 34) (w64 a) (w64 ncap) (mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy md) mat1 md)))).
{ split; [exact (proj2 (amwf_MWF _) MWFg)|].
  intros q Hq. rewrite wmb34 in Hq. unfold mmap_model in Hq.
  rewrite m_vmmaps_with_vmmaps in Hq. cbn [vm_maps] in Hq. rewrite m_vmmaps_wvb in Hq.
  destruct Hq as [<-|Hq]; [cbn [snd]; rewrite UAn; lia | exact (proj2 MW q Hq)]. }
assert (IOmd : YG0d.same_io md (with_mmap_backing (w64 34) (w64 a) (w64 ncap) (mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy md) mat1 md)))) by (eapply sio_trans; [apply sio_wvb | exact IO1]).
pose proof (commit_expose tfibsegs W (with_vm_backing (m_vm_lazy md) mat1 md) true (w64 34) (w64 a) (w64 ncap) mem Hn34
  ltac:(rewrite UA; unfold page_size; exact Gal) ltac:(rewrite UAn; unfold page_size; exact NCm)
  ltac:(rewrite UA, UAn; lia)
  ltac:(intros _ pq Hp1 Hp2; apply (GLAZY a pq HGmd); [rewrite UA in Hp1; exact Hp1 | rewrite UA, UAn in Hp2; exact Hp2])
  ltac:(unfold grant_md; exact HAI1)) as CX.
cbv zeta in CX. rewrite UA, UAn in CX.
destruct CX as (LE2 & A2 & VIS2 & MON2 & AI2 & _).
match type of LE2 with wle _ ?W2e => set (W2 := W2e) in * end.
eapply (amreal_world_le tfibsegs (K 1) W W2); [exact LE2 | intros _; exact AI2 |].
assert (HCUT : forall x : word, ~ (a <= bv_unsigned x < a + ncap) -> w_H W2 x = w_H W x).
{ intros x Hx. unfold W2, wexpose. cbn [w_H]. unfold Hcut.
  replace ((a <=? bv_unsigned x) && (bv_unsigned x <? a + ncap)) with false; [apply andb_true_r|].
  symmetry. apply andb_false_iff. destruct (Z.le_gt_cases a (bv_unsigned x)); [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]. }
assert (FRall : forall x : word, ~ (sp - REALLOC_STK <= bv_unsigned x < sp) -> ~ (a <= bv_unsigned x < a + ncap) -> mem1 x = mem x).
{ intros x Hx Hy. rewrite (FR1 x ltac:(num; lia) Hy). apply FRA. num. lia. }
assert (PRESW : forall b, sp - REALLOC_STK <= b < sp -> apresent (w_H W2) mem1 b).
{ intros b Hb.
  assert (HP : apresent (w_H W) mem1 b).
  { apply PR1. destruct (Z.le_gt_cases (sp - REALLOC_FRAME) b).
    - apply FPRES. num. lia.
    - apply (apresent_same (w_H W) mem); [apply FRA; rewrite unsigned_lit_small by (num; lia); num; lia | apply HPRES; num; lia]. }
  destruct HP as [Hh Hb2]. split; [rewrite HCUT by (rewrite unsigned_lit_small by (num; lia); num; lia); exact Hh | exact Hb2]. }
assert (PRTR : forall b, 0 <= b < 2 ^ 64 -> ~ (sp - REALLOC_STK <= b < sp) -> apresent (w_H W) mem b -> apresent (w_H W2) mem1 b).
{ intros b Hb64 Hb HPb.
  destruct (Z.le_gt_cases a b) as [Hb1|Hb1]; [destruct (Z.lt_ge_cases b (a + ncap)) as [Hb2|Hb2]|].
  - split; [apply VIS2; rewrite unsigned_lit_small by lia; lia|].
    exists (Z_to_bv 8 0). apply ZR1. rewrite unsigned_lit_small by lia. lia.
  - assert (HPm : apresent (w_H W) mem1 b) by (apply PR1; apply (apresent_same (w_H W) mem); [apply FRA; rewrite unsigned_lit_small by (num; lia); num; lia | exact HPb]).
    destruct HPm as [Hh Hby]. split; [rewrite HCUT by (rewrite unsigned_lit_small by lia; lia); exact Hh | exact Hby].
  - assert (HPm : apresent (w_H W) mem1 b) by (apply PR1; apply (apresent_same (w_H W) mem); [apply FRA; rewrite unsigned_lit_small by (num; lia); num; lia | exact HPb]).
    destruct HPm as [Hh Hby]. split; [rewrite HCUT by (rewrite unsigned_lit_small by lia; lia); exact Hh | exact Hby]. }
assert (TRM : forall x : Z, ~ (sp - REALLOC_STK <= x < sp) -> ~ (a <= x < a + ncap) -> 0 <= x < 2 ^ 64 ->
  mrestrict (w_H W2) mem1 (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
{ intros x Hx Hy Hx64. apply mrestrict_same_at; [apply HCUT; rewrite unsigned_lit_small by lia; lia
  | apply FRall; rewrite unsigned_lit_small by lia; lia]. }
assert (TRA : forall x : Z, ~ (sp - REALLOC_STK <= x < sp - REALLOC_FRAME) -> ~ (a <= x < a + ncap) -> 0 <= x < 2 ^ 64 ->
  mrestrict (w_H W2) mem1 (Z_to_bv 64 x) = mrestrict (w_H W) (ms_mem msA) (Z_to_bv 64 x)).
{ intros x Hx Hy Hx64. apply mrestrict_same_at; [apply HCUT; rewrite unsigned_lit_small by lia; lia|].
  apply FR1; rewrite unsigned_lit_small by lia; num; lia. }
rewrite RA1.
eapply (amreal_SRr_pre tfibsegs (K 1) W2 _ Q (realloc_post W regs mem md v nb d cap sz)).
+ apply (Htail W regs mem md v nb d cap sz W2 regs1 mem1 a mat1 HPRE0 LE2 A2 VIS2 HCUT HGmd Gpos ltac:(lia)
    Ga1 Ga2 Ga3 OLDAP AMWF1 IOmd).
  * rewrite ?SPE, ?NCE. rewrite <- RA2. f_equal. exact (HP1 2 ltac:(left; reflexivity)).
  * rewrite ?SPE, ?NCE; rewrite <- RA8. exact (HP1 8 ltac:(right; right; right; left; reflexivity)).
  * rewrite ?SPE, ?NCE; rewrite <- RA9. exact (HP1 9 ltac:(right; right; right; right; left; reflexivity)).
  * rewrite ?SPE, ?NCE; exact R1_10.
  * rewrite ?SPE, ?NCE; intros r Hr. rewrite (HP1 r ltac:(unfold callee_saved; destruct Hr as [E'|[E'|E']];
  [right; left; exact E' | right; right; left; exact E' | right; right; right; right; right; lia])).
exact (RAcs r Hr).
  * rewrite ?SPE, ?NCE; apply (val_mem_tr (w_H W) (w_H W2) (ms_mem msA) mem1); [intros k Hk; apply TRA; num; lia | exact SW1].
  * rewrite ?SPE, ?NCE; apply (val_mem_tr (w_H W) (w_H W2) (ms_mem msA) mem1); [intros k Hk; apply TRA; num; lia | exact SW2].
  * rewrite ?SPE, ?NCE; apply (val_mem_tr (w_H W) (w_H W2) (ms_mem msA) mem1); [intros k Hk; apply TRA; num; lia | exact SW3].
  * rewrite ?SPE, ?NCE; apply (val_mem_tr (w_H W) (w_H W2) (ms_mem msA) mem1); [intros k Hk; apply TRA; num; lia | exact SW4].
  * rewrite ?SPE, ?NCE; apply (val_mem_tr (w_H W) (w_H W2) mem mem1); [intros k Hk; apply TRM; num; lia | exact HVD].
  * rewrite ?SPE, ?NCE; apply (val_mem_tr (w_H W) (w_H W2) mem mem1); [intros k Hk; apply TRM; num; lia | exact HVC].
  * rewrite ?SPE, ?NCE; apply (val_mem_tr (w_H W) (w_H W2) mem mem1); [intros k Hk; apply TRM; num; lia | exact HVS].
  * rewrite ?SPE, ?NCE; exact PRESW.
  * rewrite ?SPE, ?NCE; exact FRall.
  * rewrite ?SPE, ?NCE; intros x Hx. apply ZR1. exact Hx.
  * rewrite ?SPE, ?NCE; exact PRTR.
+ intros W' c' _ HP. exact (HK W' c' HP).
Qed.

End s.
Print Assumptions realloc_node.
Check @realloc_node.
