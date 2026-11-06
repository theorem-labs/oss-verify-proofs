(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 929 of its 1013 lines of code are new or changed and 1840 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/B/FMW_hp_kit.v; 338 of its 401 lines of code are new or changed and 950 lines of the source are left out. *)
(* has_prefixed on fm.asan-ubsan (G2, image B): the entry 0x823e4..0x8246c (lv2_locate.c:57-62): frame of 128 bytes,
   prefix t + q to sp + 16, shadow base from the GOT (0x99c98 -> 0xa2078), strlen (location) to sp + 8, the first
   strstr (text, location); NULL -> return 0, else the loop head at the first occurrence (FMW_hp_loop.v hp_loop).
   No UBSan guard and no ASan check in this stretch. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YN3v YI08.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YC20 YI16 YI00 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g2rt FMW_hp_kit FMW_hp_model FMW_hp_loop.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel has_prefixed_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma he_sv_U : forall E e, sv_denot E e = Z_to_bv 64 (U E e).
Proof. intros E e. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma he_mod_eq : forall x y, x = y -> 0 <= y < 2 ^ 64 -> x mod 2 ^ 64 = y.
Proof. intros x y -> H. apply Z.mod_small. exact H. Qed.
Lemma he_bv_mod : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact H.
Qed.
Ltac he_umod := repeat first [ rewrite U_add2 | rewrite U_mul2 | rewrite U_lit ].
Ltac he_zmods := repeat first [ rewrite Zmult_mod_idemp_l | rewrite Zmult_mod_idemp_r | rewrite Zplus_mod_idemp_l
                              | rewrite Zplus_mod_idemp_r | rewrite <- Z.add_assoc ].
Ltac he_pcnorm := repeat lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?s)] =>
  let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p end.
Ltac he_rregU HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (Hr : getr (ms_regs ms) r = Z_to_bv 64 (U E e))
      by (rewrite <- he_sv_U; exact (st_ok_restrict_reg segs H E ss ms r HS))
  end.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis HGOTS : as_got_shadow B = HP_GOT_shadow.
Hypothesis HCELL : as_shadow_cell B = HP_shadow_cell.
Hypothesis IMGF : fm_img_facts tfibsegs B.
Hypothesis ASTRLEN : astrlen_realizes tfibsegs B PC_strlen.
Hypothesis ASTRSTR : astrstr_realizes tfibsegs B PC_strstr.
Hypothesis SH : seg_head_ok B.
Hypothesis SN : seg_ncmp_ok B.
Hypothesis SP : seg_pre_ok B.
Hypothesis SQ : seg_post_ok B.
Hypothesis ST : seg_tail_ok B.

(* a chunk of the walk's symbolic memory read back as val_mem (the donor's AF0x.v st_ok_chunk_val, on B) *)
Lemma he_chunk_val : forall (H : word -> bool) E ss ms r off (n : N) e v,
  st_ok tfibsegs E ss (restrict H ms) -> In r (ss_mem ss) ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros H E ss ms r off n e v HS Hi Hj He Hv Hn.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r Hi) as (_ & _ & _ & Hcs).
apply (val_of_chunk_ok tfibsegs E _ _ off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hcs _ Hj).
Qed.

Lemma he_chunk_at : forall (H : word -> bool) E ss ms r off e v p,
  st_ok tfibsegs E ss (restrict H ms) -> In r (ss_mem ss) ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (YP09.r_base r) + off = p ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) p 8 v.
Proof.
intros H E ss ms r off e v p HS Hr Hc He Hv <-.
exact (he_chunk_val H E ss ms r off 8 e v HS Hr Hc He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* a frame word of the walk's stack region read back (he_chunk_at), leaving the value and base goals *)
Ltac rdc HS off := eapply (he_chunk_at _ _ _ _ _ off _ _ _ HS);
  [simpl; left; reflexivity | simpl; repeat first [left; reflexivity | right] | | | ].
(* a saved register's chunk value: atom n of the walk's env is register R of the entry registers *)
Ltac fvt E XO := lazymatch goal with |- sv_denot _ (SOff ?n 0) = Z_to_bv 64 (bv_unsigned (getr ?rg ?R)) =>
  rewrite he_sv_U; f_equal; apply U_atom;
  [ rewrite (XO n ltac:(lia)); unfold E; rewrite (ew_Ereg_nat rg _ n R eq_refl), Z_to_bv_bv_unsigned; reflexivity
  | apply u64_range ] end.
Ltac fw HS off E XO F2b := rdc HS off; [fvt E XO | apply u64_range | cbn [base_val YP09.r_base]; rewrite F2b; lia].

Lemma hp_entry : forall ly S W regs mem md ch,
  afn_pre tfibsegs B STK_has_prefixed ly S W regs mem md ch ->
  st_ok tfibsegs (Ereg regs [w64 SBz]) ss_hp
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_has_prefixed) mem (seg_rom tfibsegs))).
Proof.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
ceil2. rewrite hp_stk in *.
assert (E2 : ew (Ereg regs [w64 SBz]) 2 = getr regs 2) by exact (ew_Ereg_nat regs _ 2 2%bv eq_refl).
assert (E32 : ew (Ereg regs [w64 SBz]) 32 = w64 SBz) by exact (ew_Ereg_extra regs _ 0).
assert (Usp : bv_unsigned (ew (Ereg regs [w64 SBz]) 2) = spZ regs) by (rewrite E2; reflexivity).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HGOTS, HCELL in Kgot. rewrite HCELL in Kcell.
rewrite restrict_mkst_fx. unfold ss_hp. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold hp_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + apply (region_ok_stack tfibsegs (Ereg regs [w64 SBz]) _ 2 (spZ regs) (-128)); [exact Usp | lia | lia |].
    intros a Ha. apply (apresent_writable tfibsegs). apply Hpres. lia.
  + unfold hp_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold HP_GOT_shadow; lia|]. split; [unfold HP_GOT_shadow; lia|].
    split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs _ _ 0 HP_GOT_shadow 8 (SLit HP_shadow_cell) HP_shadow_cell);
      [reflexivity | unfold HP_shadow_cell; cbn; lia | cbn; lia |].
    cbn [Z.add]. exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot).
  + unfold hp_cell_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold HP_shadow_cell; lia|]. split; [unfold HP_shadow_cell; lia|].
    split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs _ _ 0 HP_shadow_cell 8 (SOff 32 0) SBz);
      [cbn [sv_denot]; rewrite E32; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SBz; cbn; lia | cbn; lia |].
    cbn [Z.add]. unfold SBz. exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold hp_regions, hp_got_region, hp_cell_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold HP_GOT_shadow, HP_shadow_cell. repeat split; lia.
- split; [|split; exact I]. cbn [hp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E32. change (2 ^ 4) with 16. unfold w64, SBz. rewrite unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. unfold spZ in *. repeat split; lia.
Qed.

Theorem has_prefixed_walk : has_prefixed_spec tfibsegs B.
Proof.
unfold has_prefixed_spec, fpre, fpost.
intros ly S W regs mem md ch t q plen lp tb lb live peak cnt fail (HPRE & HRO) Hglob
  H10 H11 H12 H13 Ht Hl Hkt Hkl Hlb Hq Hplen Hqp Htmax.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof (ajournal_init tfibsegs B STK_has_prefixed [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
set (cx := mkHC regs ly S W mem md t q plen lp tb lb live peak cnt fail).
assert (HE : hp_entry_ok B cx) by exact (conj Hra (conj Hgp (conj Htp (conj Ht (conj Hl (conj Hkt (conj Hkl (conj Hlb (conj Hq (conj Hplen (conj Hqp (conj Htmax HRO)))))))))))).
assert (HPl : length (cx_pre cx) = Z.to_nat plen)
  by (unfold cx_pre; cbn [cx_tb cx_q cx_plen cx]; rewrite length_firstn, length_skipn; lia).
ceil2. unfold MANIFEST_MAX in Htmax.
pose proof Ht as (_ & Ht4 & Htc & _). pose proof Hl as (_ & Hl4 & Hlc & _).
change (SRr tfibsegs W (cfg_at tfibsegs A_has_prefixed regs mem md) (hp_post B cx)).
pose proof (hp_entry ly S W regs mem md ch HPRE) as HS.
set (E := Ereg regs [w64 SBz]) in HS.
assert (E1 : ew E 1 = getr regs 1) by exact (ew_Ereg_nat regs _ 1 1%bv eq_refl).
assert (E2 : ew E 2 = getr regs 2) by exact (ew_Ereg_nat regs _ 2 2%bv eq_refl).
assert (E3 : ew E 3 = getr regs 3) by exact (ew_Ereg_nat regs _ 3 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs 4) by exact (ew_Ereg_nat regs _ 4 4%bv eq_refl).
assert (E10 : ew E 10 = getr regs 10) by exact (ew_Ereg_nat regs _ 10 10%bv eq_refl).
assert (E13 : ew E 13 = getr regs 13) by exact (ew_Ereg_nat regs _ 13 13%bv eq_refl).
assert (E11 : ew E 11 = getr regs 11) by exact (ew_Ereg_nat regs _ 11 11%bv eq_refl).
assert (E12 : ew E 12 = getr regs 12) by exact (ew_Ereg_nat regs _ 12 12%bv eq_refl).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HCL : alloc_ceiling <= spZ regs - STK_has_prefixed) by (rewrite hp_stk in *; lia).
assert (SHOK : sh_ok tfibsegs hp_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold cfg_at. change (w64 A_has_prefixed) with (Z_to_bv 64 A_has_prefixed).
(* 0x823e4..0x8243c: frame, the 13 saves, s0 = lp, s1 = plen, sp + 16 = t + q, s7 = shadow base, s3 = t; strlen *)
aj_run_tok tbl_hp_ok HS HJ SHOK hp_Bspan.
{ awr_ok_tac. exact Usp. }
pose proof (gframe_of_frame tfibsegs W E _ 2 (-128) 0 (spZ regs)
  (spZ regs - STK_has_prefixed) (spZ regs) mem (ms_mem ms) HFr ltac:(vm_compute; reflexivity) Usp
  ltac:(rewrite hp_stk; lia) ltac:(lia)) as G1.
clear HF HFr HG.
rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
rreg HS (10%bv : bv 5) R10.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs + -128).
{ unfold spZ at 1. rewrite R2, E2. fold (spZ regs). apply unsigned_lit_small. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ apply (aj_rt_ro tfibsegs B LAWS Hsegs STK_RT_STR PC_strlen (fun v => v = Z.of_nat (length lb))
    W (ms_regs ms) (ms_mem ms) STK_has_prefixed (spZ regs) [] ly S W mem md [] ly S _ 0 (-128)
    (Z_to_bv 64 0x82440) HJ).
  - exact Hsp1.
  - reflexivity.
  - lia.
  - unfold STK_RT_STR, ESTACK; lia.
  - rewrite hp_stk; unfold STK_RT_STR, ESTACK; lia.
  - rewrite R3, E3; exact Hgp.
  - rewrite R4, E4; exact Htp.
  - exact R1.
  - apply g2_ret_ok_lit; [lia | reflexivity].
  - intros HPK.
    assert (HRO1 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) (ms_mem ms))).
    { apply (arodata_journal tfibsegs B FM_RLO FM_RHI STK_has_prefixed (spZ regs) [] ly S W mem md []
        ly S W (ms_mem ms) _ 0 HJ (fun a => fp_spares_closed [] a sink_closed_nil) inFP_nil g2_relro_img HRO). }
    destruct (IMGF ly S W (ms_mem ms) _ (proj1 HJ) HRO1) as (HROM & _).
    apply (ASTRLEN ly S W (ms_regs ms) (ms_mem ms) _ lp lb HPK HROM).
    + rewrite R10, E13. exact H13.
    + apply (cstr_ok_gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem); [exact G1 | exact HCL | exact Hl]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v4 & -> & HJ2 & HP2 & Ha0 & Hv4 & HRv4 & G2 & Hpres2).
jafter_call_keep HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1;2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr2 & _).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - split.
    + cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp. intros a Ha.
      apply (mbyte_of_aview tfibsegs). apply G2; unfold STK_RT_STR, ESTACK in *; lia.
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite Usp. intros a Ha _.
      apply (apresent_writable tfibsegs). apply Hpr2. rewrite hp_stk. lia.
  - split.
    + cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. intros a Ha.
      apply (mbyte_of_aview tfibsegs). apply G2; unfold STK_RT_STR, ESTACK, HP_GOT_shadow in *; lia.
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. intros a Ha. lia.
  - split.
    + cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. intros a Ha.
      apply (mbyte_of_aview tfibsegs). apply G2; unfold STK_RT_STR, ESTACK, HP_shadow_cell in *; lia.
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. intros a Ha. lia. }
clear HS. rename HS2 into HS. rewrite <- restrict_mkst_fx in HS.
set (Eh := havoc E 33 (map (getr regs2) CLOB)) in HS.
assert (F2 : bv_unsigned (ew Eh 2) = spZ regs) by (unfold Eh; rewrite YN3v.ew_havoc_old by lia; exact Usp).
clear SHOK.
assert (SHOK : sh_ok tfibsegs hp_Bx [] Eh (mrestrict (w_H W) mem2)) by apply Forall_nil.
(* 0x82440..0x8244c: sp + 8 = strlen (location), call strstr (text, location) *)
aj_run_tok tbl_hp_ok HS HJ2 SHOK hp_Bspan.
{ awr_ok_tac. exact F2. }
pose proof (gframe_of_frame tfibsegs W Eh _ 2 (-128) 0 (spZ regs)
  (spZ regs - STK_has_prefixed) (spZ regs) mem2 (ms_mem ms0) HFr ltac:(vm_compute; reflexivity) F2
  ltac:(rewrite hp_stk; lia) ltac:(lia)) as G3.
clear HF HFr HG.
rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4.
rreg HS (10%bv : bv 5) Q10. rreg HS (11%bv : bv 5) Q11.
assert (Hsp2 : spZ (ms_regs ms0) = spZ regs + -128).
{ unfold spZ at 1. rewrite Q2. unfold Eh. rewrite YN3v.ew_havoc_old by lia. rewrite E2.
  fold (spZ regs). apply unsigned_lit_small. lia. }
assert (GT : gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem (ms_mem ms0)).
{ apply (gframe_seq tfibsegs W _ _ mem mem2); [|exact G3].
  apply (gframe_seq tfibsegs W _ _ mem (ms_mem ms)); [exact G1|].
  apply (gframe_widen tfibsegs W _ _ (spZ regs + -128 - STK_RT_STR) (spZ regs + -128));
    [exact G2 | |]; rewrite ?hp_stk; unfold STK_RT_STR, ESTACK; lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) Eh _ ms0 HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ apply (aj_rt_ro tfibsegs B LAWS Hsegs STK_RT_STRSTR PC_strstr
    (fun v => (v = 0 /\ no_occ tb lb) \/ (exists j, first_occ tb lb j /\ v = t + Z.of_nat j))
    W (ms_regs ms0) (ms_mem ms0) STK_has_prefixed (spZ regs) [] ly S W mem md [] ly S _ 0 (-128)
    (Z_to_bv 64 0x82450) HJ2).
  - exact Hsp2.
  - reflexivity.
  - lia.
  - unfold STK_RT_STRSTR, ESTACK; lia.
  - rewrite hp_stk; unfold STK_RT_STRSTR, ESTACK; lia.
  - rewrite Q3. unfold Eh. rewrite YN3v.ew_havoc_old by lia. rewrite E3. exact Hgp.
  - rewrite Q4. unfold Eh. rewrite YN3v.ew_havoc_old by lia. rewrite E4. exact Htp.
  - exact Q1.
  - apply g2_ret_ok_lit; [lia | reflexivity].
  - intros HPK.
    assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) (ms_mem ms0))).
    { apply (arodata_journal tfibsegs B FM_RLO FM_RHI STK_has_prefixed (spZ regs) [] ly S W mem md []
        ly S W (ms_mem ms0) _ 0 HJ2 (fun a => fp_spares_closed [] a sink_closed_nil) inFP_nil g2_relro_img HRO). }
    destruct (IMGF ly S W (ms_mem ms0) _ (proj1 HJ2) HRO2) as (HROM & HROO & _).
    apply (hp_strstr_ro B ASTRSTR ly S W (ms_regs ms0) (ms_mem ms0) _ t lp tb lb HPK HROM HROO).
    + rewrite Q10. unfold Eh. rewrite YN3v.ew_havoc_old by lia. rewrite E10. exact H10.
    + rewrite Q11. unfold Eh. rewrite YN3v.ew_havoc_old by lia. rewrite E13. exact H13.
    + apply (cstr_ok_gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem); [exact GT | exact HCL | exact Ht].
    + apply (cstr_ok_gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem); [exact GT | exact HCL | exact Hl]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v5 & -> & HJ3 & HP3 & Hb0 & Hv5 & HRv5 & G4 & Hpres3).
jafter_call_keep HS 49%nat regs3 (mrestrict (w_H W) mem3) HP3 [0;1;2]%nat HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr3 & _).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - split.
    + cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite F2. intros a Ha.
      apply (mbyte_of_aview tfibsegs). apply G4; unfold STK_RT_STRSTR, ESTACK in *; lia.
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite F2. intros a Ha _.
      apply (apresent_writable tfibsegs). apply Hpr3. rewrite hp_stk. lia.
  - split.
    + cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. intros a Ha.
      apply (mbyte_of_aview tfibsegs). apply G4; unfold STK_RT_STRSTR, ESTACK, HP_GOT_shadow in *; lia.
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. intros a Ha. lia.
  - split.
    + cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. intros a Ha.
      apply (mbyte_of_aview tfibsegs). apply G4; unfold STK_RT_STRSTR, ESTACK, HP_shadow_cell in *; lia.
    + cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. intros a Ha. lia. }
clear HS. rename HS3 into HS. rewrite <- restrict_mkst_fx in HS.
set (Eg := havoc Eh 49 (map (getr regs3) CLOB)) in HS.
assert (F2b : bv_unsigned (ew Eg 2) = spZ regs) by (unfold Eg; rewrite YN3v.ew_havoc_old by lia; exact F2).
clear SHOK. assert (SHOK : sh_ok tfibsegs hp_Bx [] Eg (mrestrict (w_H W) mem3)) by apply Forall_nil.
assert (GT2 : gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem mem3).
{ apply (gframe_seq tfibsegs W _ _ mem (ms_mem ms0)); [exact GT|].
  apply (gframe_widen tfibsegs W _ _ (spZ regs + -128 - STK_RT_STRSTR) (spZ regs + -128));
    [exact G4 | |]; rewrite ?hp_stk; unfold STK_RT_STRSTR, ESTACK; lia. }
(* the atoms the rest reads, in Eg *)
assert (X37 : ew Eg 37 = w64 (Z.of_nat (length lb))).
{ unfold Eg. rewrite YN3v.ew_havoc_old by lia. unfold Eh. cbn [YN3v.havoc ew Nat.ltb Nat.leb nth Nat.sub map CLOB].
  rewrite Ha0, HRv4. reflexivity. }
assert (X53 : ew Eg 53 = w64 v5).
{ unfold Eg. cbn [YN3v.havoc ew Nat.ltb Nat.leb nth Nat.sub map CLOB]. exact Hb0. }
assert (XO : forall n, (n < 33)%nat -> ew Eg n = ew E n).
{ intros n Hn. unfold Eg. rewrite YN3v.ew_havoc_old by lia. unfold Eh. rewrite YN3v.ew_havoc_old by lia. reflexivity. }
(* 0x82450: beqz a0 *)
aj_run_tok tbl_hp_ok HS HJ3 SHOK hp_Bspan.
{ awr_ok_tac. exact F2b. }
pose proof (gframe_of_frame tfibsegs W Eg _ 2 (-128) 0 (spZ regs)
  (spZ regs - STK_has_prefixed) (spZ regs) mem3 _ HFr ltac:(vm_compute; reflexivity) F2b
  ltac:(rewrite hp_stk; lia) ltac:(lia)) as G5.
clear HF HFr HG.
assert (U53 : U Eg (SOff 53 0) = v5) by (apply (U_atom Eg 53 v5 X53 Hv5)).
srr_branch_with tbl_hp_ok HS.
- (* strstr found nothing: return 0 *)
  rewrite branch_eq_U, U53, U_lit in Hc. change (0 mod 2 ^ 64) with 0 in Hc. apply Z.eqb_eq in Hc. clear U53. subst v5.
  assert (Hno : no_occ tb lb).
  { destruct HRv5 as [(_ & Hno) | (j & _ & Hj)]; [exact Hno | lia]. }
  aj_run_to tbl_hp_ok HS HJ3 A_hp_epi.
  { awr_ok_tac. exact F2b. }
  pose proof (gframe_of_frame tfibsegs W Eg _ 2 (-128) 0 (spZ regs)
    (spZ regs - STK_has_prefixed) (spZ regs) _ _ HFr ltac:(vm_compute; reflexivity) F2b
    ltac:(rewrite hp_stk; lia) ltac:(lia)) as G6.
  clear HF HFr HG.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) Eg _ msx HS eq_refl); cbn [ss_pc]; he_pcnorm;
    rreg HS (2%bv : bv 5) P2; rreg HS (3%bv : bv 5) P3; rreg HS (4%bv : bv 5) P4; rreg HS (10%bv : bv 5) P10;
    rreg HS (8%bv : bv 5) P8; rreg HS (9%bv : bv 5) P9; rreg HS (19%bv : bv 5) P19; rreg HS (20%bv : bv 5) P20;
    rreg HS (21%bv : bv 5) P21; rreg HS (23%bv : bv 5) P23; rreg HS (24%bv : bv 5) P24;
    he_rregU HS (25%bv : bv 5) P25; rreg HS (26%bv : bv 5) P26; rreg HS (27%bv : bv 5) P27;
    set (rH := ms_regs msx) in *; set (mH := ms_mem msx) in *
  end.
  assert (GH : gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem mH).
  { eapply (gframe_seq tfibsegs W _ _ mem _ mH); [|exact G6].
    eapply (gframe_seq tfibsegs W _ _ mem _ _); [exact GT2 | exact G5]. }
  assert (Hgl : fm_glob tfibsegs W mH live peak cnt fail)
    by (apply (fm_glob_gframe tfibsegs W _ _ mem mH _ _ _ _ GH); [exact HCL | exact Hglob]).
  assert (K3 : getr rH 3 = w64 (as_gp B)) by (rewrite P3, (XO 3%nat) by lia; rewrite E3; exact Hgp).
  assert (K4 : getr rH 4 = w64 (as_tp B)) by (rewrite P4, (XO 4%nat) by lia; rewrite E4; exact Htp).
  assert (Qsp : spZ rH = spZ (cx_regs0 cx) - 128).
  { unfold spZ at 1. rewrite P2, (XO 2%nat) by lia. rewrite E2. fold (spZ regs). rewrite unsigned_lit_small by lia.
    cbn [cx_regs0 cx]. lia. }
  assert (HFR : hp_frame W (cx_regs0 cx) mH).
  { cbn [cx_regs0 cx]. unfold hp_frame.
    split; [fw HS (-8) E XO F2b|]. split; [fw HS (-16) E XO F2b|]. split; [fw HS (-24) E XO F2b|].
    split; [fw HS (-32) E XO F2b|]. split; [fw HS (-40) E XO F2b|]. split; [fw HS (-48) E XO F2b|].
    split; [fw HS (-56) E XO F2b|]. split; [fw HS (-64) E XO F2b|]. split; [fw HS (-72) E XO F2b|].
    split; [fw HS (-80) E XO F2b|]. split; [fw HS (-88) E XO F2b|]. split; [fw HS (-96) E XO F2b|].
    fw HS (-104) E XO F2b. }
  apply (hp_ret B HGOTS HCELL cx ly S W rH mH _).
  + exact (conj HE (conj HJ3 (conj eq_refl (conj K3 (conj K4 (conj Qsp (conj HFR Hgl))))))).
  + rewrite P10, X53. unfold hp_res. erewrite tok_none; [reflexivity | |].
    * exact (INV_0 tb (cx_pre cx) lb (Z.to_nat plen) HPl).
    * exact (noocc_mt tb (cx_pre cx) lb (Z.to_nat plen) HPl 0 Hno).
- rewrite branch_eq_U, U53, U_lit in Hc. change (0 mod 2 ^ 64) with 0 in Hc. apply Z.eqb_neq in Hc.
  destruct HRv5 as [(Hv0 & _) | (j & Hfo & Hj)]; [lia|]. clear U53. subst v5.
  aj_run_to tbl_hp_ok HS HJ3 HP_HEAD.
  { awr_ok_tac. exact F2b. }
  pose proof (gframe_of_frame tfibsegs W Eg _ 2 (-128) 0 (spZ regs)
    (spZ regs - STK_has_prefixed) (spZ regs) _ _ HFr ltac:(vm_compute; reflexivity) F2b
    ltac:(rewrite hp_stk; lia) ltac:(lia)) as G6.
  clear HF HFr HG.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) Eg _ msx HS eq_refl); cbn [ss_pc]; he_pcnorm;
    rreg HS (2%bv : bv 5) P2; rreg HS (3%bv : bv 5) P3; rreg HS (4%bv : bv 5) P4; rreg HS (10%bv : bv 5) P10;
    rreg HS (8%bv : bv 5) P8; rreg HS (9%bv : bv 5) P9; rreg HS (19%bv : bv 5) P19; rreg HS (20%bv : bv 5) P20;
    rreg HS (21%bv : bv 5) P21; rreg HS (23%bv : bv 5) P23; rreg HS (24%bv : bv 5) P24;
    he_rregU HS (25%bv : bv 5) P25; rreg HS (26%bv : bv 5) P26; rreg HS (27%bv : bv 5) P27;
    set (rH := ms_regs msx) in *; set (mH := ms_mem msx) in *
  end.
  assert (GH : gframe tfibsegs W (spZ regs - STK_has_prefixed) (spZ regs) mem mH).
  { eapply (gframe_seq tfibsegs W _ _ mem _ mH); [|exact G6].
    eapply (gframe_seq tfibsegs W _ _ mem _ _); [exact GT2 | exact G5]. }
  assert (Hgl : fm_glob tfibsegs W mH live peak cnt fail)
    by (apply (fm_glob_gframe tfibsegs W _ _ mem mH _ _ _ _ GH); [exact HCL | exact Hglob]).
  assert (K3 : getr rH 3 = w64 (as_gp B)) by (rewrite P3, (XO 3%nat) by lia; rewrite E3; exact Hgp).
  assert (K4 : getr rH 4 = w64 (as_tp B)) by (rewrite P4, (XO 4%nat) by lia; rewrite E4; exact Htp).
  assert (Qsp : spZ rH = spZ (cx_regs0 cx) - 128).
  { unfold spZ at 1. rewrite P2, (XO 2%nat) by lia. rewrite E2. fold (spZ regs). rewrite unsigned_lit_small by lia.
    cbn [cx_regs0 cx]. lia. }
  assert (HFR : hp_frame W (cx_regs0 cx) mH).
  { cbn [cx_regs0 cx]. unfold hp_frame.
    split; [fw HS (-8) E XO F2b|]. split; [fw HS (-16) E XO F2b|]. split; [fw HS (-24) E XO F2b|].
    split; [fw HS (-32) E XO F2b|]. split; [fw HS (-40) E XO F2b|]. split; [fw HS (-48) E XO F2b|].
    split; [fw HS (-56) E XO F2b|]. split; [fw HS (-64) E XO F2b|]. split; [fw HS (-72) E XO F2b|].
    split; [fw HS (-80) E XO F2b|]. split; [fw HS (-88) E XO F2b|]. split; [fw HS (-96) E XO F2b|].
    fw HS (-104) E XO F2b. }
  pose proof (has_prefixed_model.mt_len _ _ _ (first_occ_mt tb lb 0 j (Nat.le_0_l _) Hfo)) as Hjl.
  lazymatch goal with |- context [mkCfg _ ?d] => set (mdH := d) in * end.
  assert (Hst : hp_st B cx j ly S W rH mH mdH).
  { unfold hp_st. cbn [cx_regs0 cx_ly cx_S cx_W0 cx_mem cx_md cx_t cx_q cx_plen cx_lp cx_tb cx_lb cx_live cx_peak
      cx_cnt cx_fail cx].
    split; [exact HE|]. split; [exact HJ3|]. split; [reflexivity|]. split; [exact K3|]. split; [exact K4|].
    split; [exact Qsp|]. split; [exact HFR|].
    split.
    { split.
      - rdc HS (-120); [| lia | cbn [base_val YP09.r_base]; rewrite F2b; lia].
        rewrite he_sv_U. f_equal. apply U_atom; [exact X37 | lia].
      - rdc HS (-112); [| lia | cbn [base_val YP09.r_base]; rewrite F2b; lia].
        rewrite he_sv_U. f_equal. apply U_atom; [rewrite (XO 11%nat) by lia; rewrite E11; exact H11 | lia]. }
    split; [rewrite P8, (XO 13%nat) by lia; rewrite E13; exact H13|].
    split; [rewrite P9, (XO 12%nat) by lia; rewrite E12; exact H12|].
    split; [rewrite P19, (XO 10%nat) by lia; rewrite E10; exact H10|].
    split; [rewrite P20; reflexivity|].
    split; [rewrite P21, X53; reflexivity|].
    split; [rewrite P23, (XO 32%nat) by lia; unfold E; exact (ew_Ereg_extra regs _ 0)|].
    split; [rewrite P24, (XO 12%nat) by lia; rewrite E12, H12; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
    split.
    { rewrite P25. apply he_bv_mod. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_lit, (U_atom_mod Eg 12 0 plen).
      - unfold zcanon, M64. rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r, Z.mod_mod by lia. f_equal. lia.
      - rewrite (XO 12%nat) by lia. rewrite E12. exact H12. }
    split; [rewrite P26; apply he_bv_mod; reflexivity|].
    split; [rewrite P27; reflexivity|].
    split; [exact (first_occ_mt tb lb 0 j (Nat.le_0_l _) Hfo) | exact Hgl]. }
  exact (hp_loop B SH SN SP SQ ST cx HE (Datatypes.S (length tb)) j ltac:(change (cx_tb cx) with tb; apply Nat.lt_succ_r, Nat.le_sub_l)
    (first_occ_inv tb (cx_pre cx) lb (Z.to_nat plen) HPl 0 j (INV_0 tb (cx_pre cx) lb (Z.to_nat plen) HPl) Hfo)
    ly S W rH mH _ Hst I).
Qed.
End e.
