(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and numbers changed; 356 of its 490 lines of code are new or changed and 232 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaStep DiscoSyms DiscoList DiscoAddr DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YE00 YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntProCuts DiscoEntProSeat YC85s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac proA_hd AG HSK :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear - HSK; cbn; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - _ <= ?sp1 <= sp0 - _ |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1 HSK; cbn; lia | clear - Hsp1; cbn; lia |] end
end.
Definition byte_chunks (f : Z -> Z) (lo : Z) (n : nat) : list YP09.chunk :=
  map (fun k => YP09.mkChunk (lo + Z.of_nat k) (CVal 1 (SLit (f (lo + Z.of_nat k))))) (seq 0 n).
Lemma byte_chunks_ok : forall segs E m base f lo n,
  (forall k, lo <= k < lo + Z.of_nat n -> 0 <= f k < 256 /\ mbyte segs m (base + k) = Some (Z_to_bv 8 (f k))) ->
  Forall (YP09.chunk_ok segs E m base) (byte_chunks f lo n).
Proof.
  intros segs E m base f lo n H. unfold byte_chunks. apply Forall_forall. intros c Hc.
  apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
  destruct (H (lo + Z.of_nat j) ltac:(lia)) as (Hr & Hm).
  intros i Hi. unfold YP09.c_len, cv_len in Hi. cbn [YP09.c_val Z.of_N] in Hi.
  assert (i = 0) by lia. subst i.
  exists (Z_to_bv 8 (f (lo + Z.of_nat j))). cbn [YP09.c_off YP09.c_val cbyte sv_denot]. split.
  - f_equal. rewrite byte_of_word_lit. apply Z_to_bv_mod8.
    rewrite Z.mul_0_r, Z.shiftr_0_r, (Z.mod_small (f (lo + Z.of_nat j)) (2 ^ 64)) by lia. reflexivity.
  - rewrite Z.add_0_r. exact Hm.
Qed.
Lemma sh_bytes_range : forall segs E m shf r lo n,
  forallb (fun k => sh_byte_ok (YP09.r_chunks r) shf (lo + Z.of_nat k)) (seq 0 n) = true -> region_ok segs E m r ->
  forall k, lo <= k < lo + Z.of_nat n ->
  0 <= shf k < 256 /\ mbyte segs m (base_val E (YP09.r_base r) + k) = Some (Z_to_bv 8 (shf k)).
Proof.
  intros segs E m shf r lo n Hall (_ & _ & _ & H4) k Hk.
  assert (Hin : In (Z.to_nat (k - lo)) (seq 0 n)) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) Hall _ Hin) as Hb. cbv beta in Hb. rewrite Z2Nat.id in Hb by lia.
  replace (lo + (k - lo)) with k in Hb by lia.
  unfold sh_byte_ok in Hb.
  destruct (find_chunk (YP09.r_chunks r) k 1) as [c|] eqn:Hf; [|discriminate Hb].
  destruct c as [o cv]. destruct cv as [w v|l|l|d s l]; try discriminate Hb.
  destruct v; try discriminate Hb.
  apply andb_prop in Hb as [Hb Hlt]. apply andb_prop in Hb as [Heq Hge].
  apply Z.eqb_eq in Heq. apply Z.leb_le in Hge. apply Z.ltb_lt in Hlt.
  split; [lia|].
  destruct (find_chunk_sound _ _ _ _ Hf) as (Hc & Ho & Hol). cbn [YP09.c_off YP09.c_len YP09.c_val cv_len] in Ho, Hol.
  pose proof (proj1 (Forall_forall _ _) H4 _ Hc) as Hck.
  destruct (Hck (k - o) ltac:(cbn [YP09.c_len YP09.c_val cv_len]; lia)) as (b & Hb1 & Hb2).
  cbn [YP09.c_off YP09.c_val cbyte sv_denot] in Hb1, Hb2.
  replace (base_val E (YP09.r_base r) + o + (k - o)) with (base_val E (YP09.r_base r) + k) in Hb2 by lia.
  rewrite Hb2. injection Hb1 as <-. f_equal. rewrite byte_of_word_lit. apply Z_to_bv_mod8.
  rewrite Heq. symmetry. apply Z.mod_small. lia.
Qed.
Lemma mbyte_of_aview_val : forall segs H m a v, aview segs H m a = Some v -> mbyte segs (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
  intros segs H m a v Hv. unfold aview in Hv. destruct (mbyte segs (mrestrict H m) a) as [b|]; [|discriminate Hv].
  cbn [option_map] in Hv. injection Hv as <-. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition proA_extra : list word := [Z_to_bv 64 SB].
Definition proA_regions0 : smem :=
[ stack_region 576; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 67); uar_cell_regionP (A_OBJ 67) ].
Definition proA_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (11%nat, mkAF 0 (2^26 - 1) 0) ].
Definition ss_proA_entry : sstate := mkSS AF_LLVMFuzzerTestOneInput sr_atoms proA_regions0 None (mkFacts proA_atoms0 [] []).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Lemma proA_entryX : forall (fq : YK11.FPState) W ly S regs mem md ch STK nn,
afn_pre SEGS B STK ly S W regs mem md ch -> 576 <= STK ->
getr regs 11 = w64 nn -> 0 <= nn < 2 ^ 26 ->
st_ok_pi (fx := fq) SEGS VAL (Eimg (Ereg regs proA_extra)) ss_proA_entry
(restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)) mem (seg_rom SEGS))).
Proof.
intros fq W ly S regs mem md ch STK nn HPRE HSTK H11 Hnn.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TL), (pal_uar_cell B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kuar.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs proA_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 nn) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs proA_extra 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E307 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E308 : ew E (A_OBJ 67) = Z_to_bv 64 (VAL (A_OBJ 67))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(unfold disco_nobj; lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Hob1.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Hob66. pose proof (pa_obj_img 67 ltac:(unfold disco_nobj; lia)) as Hob67.
unfold IMG_LO, IMG_TOP in Hob0, Hob1, Hob66, Hob67.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep. rewrite (pal_uar_cell B TL) in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_proA_entry. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold proA_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
[cbn [sv_denot]; rewrite E307, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E307) by (pose proof (pa_val_range (A_OBJ 66)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 67) 0) (VAL (A_OBJ 67)));
[cbn [sv_denot]; rewrite E308, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 67)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 67) (VAL (A_OBJ 67)) E308) by (pose proof (pa_val_range (A_OBJ 67)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 67)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold proA_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E307) by (pose proof (pa_val_range (A_OBJ 66)); lia).
rewrite (VB (A_OBJ 67) (VAL (A_OBJ 67)) E308) by (pose proof (pa_val_range (A_OBJ 67)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Hob0 Hob1 Hob66 Hob67 Hsep. clear. unfold IMG_LO, IMG_TOP. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok proA_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E11, E32. rewrite !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 Hstk0 Hal16 Hnn HSTK. clear. unfold SB. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASM6 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 6.
Hypothesis ASSF8 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS B (SIGMA DS___asan_set_shadow_f8) 0xf8.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis KCAN : ak_canary tfib_K = AE2k.FF_canary.
Let errno_low := pal_env B TL.
Theorem pb_proA : pro_segA B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold pro_segA.
intros fq ly S W regs mem md pI nI pl M Hf0 Hpre Hext.
pose proof Hpre as (HPRE & Hra0 & H10 & H11 & Hpn & Hlen & Harr & Hfr0 & Hnev & Hbb & Harod & Hsink & Hfd & Hfs & Hmeta & Hmo).
assert (Hn26 : 0 <= nI < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hq _]]; lia).
destruct (astdio_env_canary SEGS tfib_K _ (proj1 Hsink)) as (cv & Hcvr & Hcv). rewrite KCAN in Hcv.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSK : 4736 <= LLVMF_STK) by (unfold LLVMF_STK; lia).
pose proof (proA_entryX fq W ly S regs mem md [] LLVMF_STK nI HPRE ltac:(unfold LLVMF_STK; lia) H11 Hn26) as HS.
pose proof (ajournal_init SEGS B LLVMF_STK [] ly S W regs mem md [] HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity.
remember (Eimg (Ereg regs proA_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 pI) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 nI) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs proA_extra 0)).
img_factsF E.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Hob242. pose proof (pa_obj_img 0 ltac:(unfold disco_nobj; lia)) as Hob241.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Hob307. pose proof (pa_obj_img 67 ltac:(unfold disco_nobj; lia)) as Hob308.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob307, Hob308.
pose proof (palf_uar_img B TL) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob307, Hob308, Huar.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs proA_extra) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_LLVMFuzzerTestOneInput)) with (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)).
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) mem).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x44. { awrFL_with ltac:(idtac; proA_hd AG HSK) AG 0 0 EFA0. }
upd_aboveW_init HFr AG HUP. clear_frames.
set (sp1 := 32 * ((spZ regs + -576) / 32)).
destruct (sp1_facts (spZ regs + -576) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 592 <= sp1 <= spZ regs - 576) by (clear - Hsp1r; lia). clear Hsp1r.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(denot_and_m32 Ev 2 (spZ regs) (-576) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia) ltac:(clear - Hshi H47; lia) ltac:(clear - Hceil Hslo Hstk0 HSK C1 Hshi H47; lia)) R2 end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 60 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 60%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E60 : ew Ev 60 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2; rewrite unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 HSK C1 Hshi H47; lia); reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 60%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 HSK C1 Hshi H47; lia); change (2 ^ 5) with 32;
clear - Hsp1 Hsp1al Hslo Hstk0 Hshi H47 Hceil HSK C1 C3; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 472 0 472 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E60, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 HSK C1 Hshi H47; lia); split; [clear - Hsp1 Hceil Hslo Hstk0 HSK C1; lia|]; split; [clear - Hsp1 Hshi H47; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply HJpres; clear - Ho Hsp1 HSK; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 Hob241 Hob242 Hob307 Hob308 Huar; repeat split; lia)) as HS3; clear HJpres;
clear HS; rename HS3 into HS end.
norm_ss HS.
reshok HS.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan. { awrFL_with ltac:(idtac; proA_hd AG HSK) AG 0 0 EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG.
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite (palf_sm6 B TLF).
pose proof (count_cid_le_length 6 (frames S)) as Hcnt. rewrite Hfr0 in Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 6 (ASM6 fq) ltac:(lia) W (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ HJ) end.
- unfold spZ at 1. rewrite R2. evalE AG.
- rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
- clear - Hsp1; lia. - rewrite Hes; clear - Hsp1 HSK; lia.
- rewrite R3. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp. - rewrite R4. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- rewrite Hfr0. vm_compute. reflexivity. }
cbv beta. clear R2 R3 R4 R1 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & _ & (fS2 & ES2)).
rewrite Hes in HK. replace (spZ regs + (sp1 - spZ regs) - 4096) with (sp1 - 4096) in HK by lia.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by lia.
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; clear - Ha Hsp1 Hceil Hslo Hstk0 HSK C1; lia. }
clear HUP. rename HUP2 into HUP.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (6, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 6 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFapp_img.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 6 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 6) with 4096 in *.
set (F := frame_addr ly 6 fpos) in *. set (FL := flag_addr ly 6 fpos) in *.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; keptFL HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)).
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 529 Ev ssv msv [Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 529%nat [Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 529 [Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E530 : ew Ev 530 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 529 [Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL ly S2 W mem2 md2 6 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 516 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 530 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E530, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 529 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 516 32 529 F SB RF ltac:(lia) E32' E529)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS;
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 0 4096 0 4096 [YP09.mkChunk 4088 (CVal 8 (SOff 530 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 4088 8 _ FL);
[cbn [sv_denot]; rewrite E530, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + 4088) with (F + 4096 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img Hob241 Hob242 Hob307 Hob308 Huar; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 529 6 0 512 []) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 6 / 8) with 512; rewrite E529, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
apply (proj1 (HFSpres o ltac:(change (4096 / 8) with 512; lia))) | apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 6 / 8) with 512; rewrite E529, RF; evalE AG;
unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob307 Hob308 Huar; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
paj_run_shc RUNP RUNC HS HJ2. { awrFL_with ltac:(idtac; proA_hd AG HSK) AG fpos F EFA0. }
rebaseE HS AG HEv. clear HEv.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ev ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as RSH0;
  pose proof (sh_bytes_range SEGS Ev _ dsh_obj r0 0 30 ltac:(vm_compute; reflexivity) RSH0) as SB0 end.
cbn [YP09.r_base base_val ms_mem restrict] in SB0. rewrite E529, unsigned_lit_small in SB0 by (unfold SB; lia).
assert (HWSH : forall o, 0 <= o < 512 -> writable_at SEGS (mrestrict (w_H W) (ms_mem ms1)) (SB + F / 8 + o)).
{ intros o Ho. destruct RSH0 as (_ & _ & RW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ms_mem restrict] in RW.
  rewrite E529, unsigned_lit_small in RW by (unfold SB; lia). exact (RW o Ho). }
clear RSH0.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_set_shadow_atS SEGS B LAWS Hsegs (SIGMA DS___asan_set_shadow_f8) 0xf8 (ASSF8 fq) W (ms_regs msX) (ms_mem msX)
    LLVMF_STK (spZ regs) [] ly S W mem md [(6, fpos)] _ _ _ _ 6 fpos (SB + F / 8 + 30) 162 (sp1 - spZ regs) _ HJ2) end.
- left; reflexivity.
- rewrite R10. cbn [sv_denot]. rewrite E529, unsigned_lit_small by (unfold SB; lia). reflexivity.
- rewrite R11. reflexivity.
- lia.
- unfold shadow_addr. fold F. rewrite <- SB_SHADOW_OFF. lia.
- unfold shadow_addr. fold F. rewrite <- SB_SHADOW_OFF. change (fs_frame_bytes 6 / 8) with 512. lia.
- unfold spZ at 1. rewrite R2. evalE AG.
- rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
- clear - Hsp1; lia. - rewrite Hes; clear - Hsp1 HSK; lia.
- rewrite R3. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp. - rewrite R4. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity]. }
cbv beta. clear R2 R3 R4 R1 R10 R11 HJ2.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hres & Hfr & Hpres3 & Hsame).
assert (SB1 : forall k, 0 <= k < 0 + Z.of_nat 192 -> 0 <= dsh_obj k < 256 /\
  mbyte SEGS (mrestrict (w_H W) mem3) (SB + F / 8 + k) = Some (Z_to_bv 8 (dsh_obj k))).
{ intros k Hk. destruct (Z.lt_ge_cases k 30) as [Hk30 | Hk30].
  - destruct (SB0 k ltac:(lia)) as (Hr & Hm). split; [exact Hr|]. rewrite <- Hm. apply (mbyte_of_aview SEGS).
    apply Hfr; unfold SB in *; lia.
  - assert (Hd : dsh_obj k = 248).
    { assert (Hall : forallb (fun j => Z.eqb (dsh_obj (30 + Z.of_nat j)) 248) (seq 0 162) = true) by (vm_compute; reflexivity).
      pose proof (proj1 (forallb_forall _ _) Hall (Z.to_nat (k - 30)) ltac:(apply in_seq; lia)) as Hj. cbv beta in Hj.
      rewrite Z2Nat.id in Hj by lia. replace (30 + (k - 30)) with k in Hj by lia. apply Z.eqb_eq in Hj. exact Hj. }
    rewrite Hd. split; [lia|]. replace (SB + F / 8 + k) with (SB + F / 8 + 30 + (k - 30)) by lia.
    apply mbyte_of_aview_val. apply Hres. lia. }
reseat HS HJ3 HP3 [1; 2; 3; 4; 5; 6; 7]%nat AG
  ltac:(idtac; eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr; unfold SB in *;
    clear - Ha Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob307 Hob308 Huar; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP in *; lia | exact Hpres3]).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 529 6 192 512 (byte_chunks dsh_obj 0 192)) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbv zeta; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
change (fs_frame_bytes 6 / 8) with 512; rewrite E529, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (writable_kept _ _ _ _ (Hpres3 _)); apply HWSH; lia | apply byte_chunks_ok; exact SB1 ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 6 / 8) with 512; rewrite E529, RF; evalE AG;
unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob307 Hob308 Huar; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
paj_run_to_shc RUNTOP HS HJ3 0x504. { awrFL_with ltac:(idtac; proA_hd AG HSK) AG fpos F EFA0. }
rebaseE HS AG HEv. clear HEv.
pose (BR := paj_branch (fx := fq) (PI := PI)).
psrr_branch_pi RUNP BR HS.
2: { exfalso. rewrite branch_eq_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
     rewrite (U_atom _ 11 nI ltac:(rewrite (AG 11%nat) by lia; exact E11) ltac:(lia)), !U_SLit in Hc.
     rewrite (zcanon_id 26), (zcanon_id 0) in Hc by (unfold M64; lia).
     change (Z.land 26 63) with 26 in Hc. rewrite Z.shiftr_div_pow2, Z.div_small in Hc by lia.
     vm_compute in Hc. discriminate Hc. }
norm_ss HS.
paj_run_to_shc RUNTOP HS HJ3 0x504. { awrFL_with ltac:(idtac; proA_hd AG HSK) AG fpos F EFA0. }
rebaseE HS AG HEv. clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (HdE : d_E (mkDCX ly S W regs mem md pI nI pl M fpos cv) Ev) end.
{ unfold d_E, d_A, d_S, d_FB, AT_A, AT_F, AT_SH. cbn [c_regs c_ly c_fpos].
  split; [intros nn r Hnn; rewrite (AG nn) by (pose proof (bv_unsigned_in_range _ r) as Hr; change (bv_modulus 5) with 32 in Hr; lia); exact (EE nn r Hnn)|].
  split; [rewrite (AG 32%nat) by lia; rewrite E32; reflexivity|].
  split; [assumption|].
  split; [rewrite E60; reflexivity|]. split; [rewrite RF; reflexivity|].
  rewrite E529. unfold shadow_addr, w64. fold F. rewrite <- SB_SHADOW_OFF. reflexivity. }
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
prreg HS (14%bv : bv 5) Q14.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msx) =>
  pose proof (p_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq (mkDCX ly S W regs mem md pI nI pl M fpos cv) dsh_our ps_C2 ly S2 W _ 0 Ev ssx msx
    ltac:(split; [exact (conj Hpre (conj Hext Hcv)) | split; [exact HJ3 | cbn [c_S]; rewrite Hfrs2, Hfr0; reflexivity]])
    HdE ltac:(cbn [c_ly c_fpos]; exact E530) HS ltac:(vm_compute; reflexivity)) as (HPF & HDS) end.
pmkst HS.
apply SRr_ret.
exists (mkDCX ly S W regs mem md pI nI pl M fpos cv).
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_M].
repeat (split; [reflexivity|]).
unfold pro_C2, d_at.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?md3 = _ /\ _ =>
  exists fq, ly, S2, rg, mm, md3, 0, 0 end.
split; [unfold cfg_at, POFF_C2; change (w64 (BASE + 1284)) with (Z_to_bv 64 (BASE + 1284)); reflexivity|].
split; [exact Hf0|].
split; [exact (conj Hpre (conj Hext Hcv))|].
split; [exact HJ3|].
split; [cbn [c_S]; rewrite Hfrs2, Hfr0; reflexivity|].
split; [lia|].
split; [pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnv & _); cbn [c_S]; lia|].
split; [rewrite MT_TRIV; cbn; exact I|].
split; [lia|].
split; [cbn [c_canary]; exact Hcvr|].
split; [|split; [exact HPF | cbn [c_ly c_S]; exact Eab]].
unfold p_rC2, p_rbase, d_A, d_S, d_FB, d_obj, dobj_off. cbn [c_regs c_ly c_fpos c_p c_n].
unfold d_FB, DFRAME_CLASS. cbn [c_ly c_fpos]. fold F.
assert (HspA : sp1 = 32 * ((spZ regs - MFRAME) / 32)) by (unfold sp1, MFRAME; do 3 f_equal; lia).
rewrite <- HspA.
split; [split; [unfold spZ at 1; rewrite Q2; evalE AG|] |].
all: try (split; [rewrite Q3; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp|]).
all: try (split; [rewrite Q4; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp|]).
all: try (split; [rewrite Q8; evalE AG; rewrite (EE 2%nat 2%bv eq_refl); unfold w64, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|]).
all: try (split; [rewrite Q9; evalE AG; reflexivity|]).
all: try (split; [rewrite Q18; evalE AG; rewrite E32; reflexivity|]).
all: try (split; [rewrite Q20; evalE AG; reflexivity|]).
all: try (split; [rewrite Q22; evalE AG; reflexivity|]).
all: try (split; [rewrite Q24; evalE AG; reflexivity|]).
all: try (split; [rewrite Q25; evalE AG; reflexivity|]).
all: try (rewrite Q26; evalE AG; reflexivity).
all: try (split; [rewrite Q21; evalE AG; rewrite E10; reflexivity|]).
all: try (split; [rewrite Q23; evalE AG; rewrite E11; reflexivity|]).
all: try (split; [rewrite Q12; reflexivity|]).
all: try (split; [rewrite Q13; reflexivity|]).
all: try (rewrite Q14; reflexivity).
Qed.
End h.
End f.
End d.
