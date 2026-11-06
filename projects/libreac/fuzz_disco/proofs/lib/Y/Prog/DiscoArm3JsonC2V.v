(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 666 of its 732 lines of code are new or changed and 1212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntHobsS3.v, with its module names changed; 186 of its 230 lines of code are new or changed and 688 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0p YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC1h YC1i YC81 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut
DiscoArm3JsonC2Defs DiscoArm3JsonC2Mod DiscoArm3JsonK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition c2v_NP : nat := 33%nat.
Definition c2v_NB : nat := 34%nat.
Definition c2v_BX : sv := SOff 19 0.
Definition c2v_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition c2v_alias : sv * sv := (SAlu ALU_ADD (SOff 24 0) (SOff 10 0), SOff c2v_NP 0).
Definition c2v_atoms : list (nat * afact) :=
  [(19%nat, mkAF SB SB 0); (20%nat, mkAF 32 32 0);
   (c2v_NP, mkAF 4096 (2 ^ 47 - 16) 0); (c2v_NB, mkAF 33 255 0)].
Definition c2v_nz : acond := mkAC BC_NE (SOff 10 0) (SLit 0).
Definition c2v_lt : acond := mkAC BC_LTU (SOff 10 0) (SOff 26 0).
Definition c2v_ge : acond := mkAC BC_GEU (SOff 25 0) (SOff 10 0).
Definition c2v_reg : smem :=
  [YP09.mkRegion (Some c2v_NP) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff c2v_NB 0))]].
Definition c2v_ss : sstate :=
  mkSS VAL_OFF sr_atoms c2v_reg None (mkFacts c2v_atoms [c2v_nz; c2v_lt; c2v_ge] [c2v_alias]).
Definition c2v_SH : list shent := [mkSHE c2v_NP 0 1].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma c2v_shent : forall ly S (W : world SEGS) mem md (E : env) (q : nat) (bp len lo hi : Z),
  AR SEGS B ly S W mem md -> In (bp, len) (ablocks B ly S) ->
  U E c2v_BX = SHADOW_OFF -> 0 <= lo <= hi ->
  bp <= U E (SOff q 0) + lo -> U E (SOff q 0) + hi <= bp + req_size len ->
  shent_ok SEGS c2v_BX E (rd W mem) (mkSHE q lo hi).
Proof.
  intros ly S W mem md E q bp len lo hi HAR Hin HB Hlh Hlo Hhi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & _).
  eapply (shent_ok_of_range SEGS (w_H W) mem E c2v_BX q bp (req_size len) (U E (SOff q 0)) lo hi).
  - exact (range_addressable_of_block SEGS B LAWS ly S W mem md bp len bp (req_size len) HAR Hin
             ltac:(lia) ltac:(lia)).
  - exact HB.
  - reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

Theorem jc2_hopV : jc2_hopV_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros P W cf HV.
unfold jc2_val, jval_in, jcut, d_arm_at_pf, d_at in HV.
destruct HV as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc0 & Hcf & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev &
  HMO & Hacc & Hi & Hn & Hnow & HRL & (R26 & R24 & R25 & R10 & R22 & R23) &
  (HSP1 & HTAB & HBUF & HX) & HSP0 & HBODY).
subst cf.
assert (HXc : jc2_x P W mem3) by exact HX.
pose proof (jc2_ws P W mem3 HXc) as HWS.
pose proof HXc as (HFIN & Hip & _ & _ & _ & _ & _ & HCONT & _).
rewrite HWS in HCONT.
pose proof HFIN as (HJR & Hfinb & HNOWS & HTLEN & HTOKS).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HBUF as (Hcap & HGARR).
assert (Hrlen : a3_r (p_T1 P) (p_now P) = jlen (p_B P)) by reflexivity.
assert (Hjlt : p_j2 P < a3_r (p_T1 P) (p_now P)).
{ rewrite Hrlen.
  destruct (jpairs_cont_step (p_B P) (p_fin P) _ _ _ _ HCONT) as [(H44 & _) | (_ & H125 & _)];
    [exact (proj1 (at_byte_true _ _ _ H44)) | exact (proj1 (at_byte_true _ _ _ H125))]. }
assert (Hbyte : 33 <= jbyte (p_B P) (p_j2 P) <= 255) by (apply jno_ws_byte; [exact HNOWS | lia]).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K (p_cx P) ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS (p_cx P) ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & _ & _ & _ & _ & _ & _ & _ & _ & HAR3 & _).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range (p_cx P) ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBODY as (Tb & Gb & Lkb & Hb & _ & _ & _ & HBLK & _).
pose proof HBLK as (HPerm0 & _ & _ & _).
assert (Hinbuf : In (p_buf P, Z.max (slot_ser_defs.ser_cap (p_op P)) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinbuf) as (Hbuf16 & Hbuf4096 & Hbufceil & Hbufapp & _ & _ & _).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap (p_op P)) 1) = Z.max (slot_ser_defs.ser_cap (p_op P)) 1).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap (p_op P)) 1) 0); lia. }
rewrite Hreq in Hbufceil, Hbufapp.
assert (Hglen : Z.of_nat (length (a3_text (p_T1 P) (p_now P) ++ [0])) = a3_r (p_T1 P) (p_now P) + 1).
{ rewrite length_app. cbn [length]. unfold a3_r. lia. }
assert (Hr969 : a3_r (p_T1 P) (p_now P) <= 969) by (unfold a3_r; lia).
remember (Eimg (Ereg regs [w64 SB; w64 (p_buf P + p_j2 P); w64 (jbyte (p_B P) (p_j2 P))])) as E0 eqn:HE0.
assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
  by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
assert (ENP : ew E0 c2v_NP = w64 (p_buf P + p_j2 P)).
{ rewrite HE0, Eimg_low by (unfold c2v_NP, A_TEXT; lia).
  change c2v_NP with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (ENB : ew E0 c2v_NB = w64 (jbyte (p_B P) (p_j2 P))).
{ rewrite HE0, Eimg_low by (unfold c2v_NB, A_TEXT; lia).
  change c2v_NB with (32 + 2)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (U19 : U E0 (SOff 19 0) = SHADOW_OFF).
{ apply (U_atom E0 19%nat SHADOW_OFF); [rewrite (EE0 19%nat 19%bv eq_refl); exact Rs19 | unfold SHADOW_OFF; lia]. }
assert (U10 : U E0 (SOff 10 0) = p_j2 P).
{ apply (U_atom E0 10%nat (p_j2 P)); [rewrite (EE0 10%nat 10%bv eq_refl); exact R10 | lia]. }
assert (U26 : U E0 (SOff 26 0) = a3_r (p_T1 P) (p_now P)).
{ apply (U_atom E0 26%nat (a3_r (p_T1 P) (p_now P))); [rewrite (EE0 26%nat 26%bv eq_refl); exact R26 | lia]. }
assert (U24 : U E0 (SOff 24 0) = p_buf P).
{ apply (U_atom E0 24%nat (p_buf P)); [rewrite (EE0 24%nat 24%bv eq_refl); exact R24 | lia]. }
assert (U25 : U E0 (SOff 25 0) = 2 ^ 64 - 1 - p_buf P).
{ apply (U_atom E0 25%nat (2 ^ 64 - 1 - p_buf P));
    [rewrite (EE0 25%nat 25%bv eq_refl), R25; apply jk_lnot; lia | lia]. }
assert (UNP : U E0 (SOff c2v_NP 0) = p_buf P + p_j2 P) by (apply (U_atom E0 c2v_NP (p_buf P + p_j2 P) ENP); lia).
assert (HG : facts_ok E0 (mkFacts c2v_atoms [c2v_nz; c2v_lt; c2v_ge] [c2v_alias])).
{ unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split].
  - unfold c2v_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE0 19%nat 19%bv eq_refl), (EE0 20%nat 20%bv eq_refl), ENP, ENB, Rs19, Rs20.
    unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF, SB in *; lia).
    rewrite Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
    repeat split; lia.
  - cbn [conds_ok]. unfold c2v_nz, c2v_lt, c2v_ge, acond_ok. cbn [ac_c ac_a ac_b].
    rewrite branch_ne_U, U_lit by lia. rewrite branch_ltu_U, U10, U26. rewrite branch_geu_U, U25, U10.
    split; [apply negb_true_iff, Z.eqb_neq; lia|]. split; [apply Z.ltb_lt; lia|].
    split; [apply negb_true_iff, Z.ltb_ge; lia | exact I].
  - unfold c2v_alias. cbn [alias_ok]. split; [|exact I].
    rewrite (denot_lit_U E0 (SAlu ALU_ADD (SOff 24 0) (SOff 10 0))), (denot_lit_U E0 (SOff c2v_NP 0)).
    f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U10, U24, UNP. apply zcanon_id. unfold M64. lia. }
assert (HROK : Forall (region_ok SEGS E0 (rd W mem3)) c2v_reg).
{ constructor; [|constructor]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite ENP. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  destruct (jk_byte W mem3 (p_buf P) (a3_text (p_T1 P) (p_now P) ++ [0]) (p_j2 P) HGARR ltac:(lia)) as (Hv0 & _).
  rewrite (jk_nth_app (a3_text (p_T1 P) (p_now P)) (p_j2 P) ltac:(unfold p_B in Hrlen; lia)) in Hv0.
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E0 _ (p_buf P + p_j2 P) 0 1 (SOff c2v_NB 0) (jbyte (p_B P) (p_j2 P))).
  - rewrite (denot_lit_U E0 (SOff c2v_NB 0)). f_equal.
    apply (U_atom E0 c2v_NB (jbyte (p_B P) (p_j2 P)) ENB). lia.
  - cbn [Z.of_N]. lia.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. replace (p_buf P + p_j2 P + 0) with (p_buf P + p_j2 P) by lia. exact Hv0. }
assert (HS : st_ok_pi (fx := fq) SEGS VAL E0 c2v_ss
  (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + VAL_OFF)) mem3 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE0. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - exact HROK.
  - cbn [pairwise_disjoint all_disjoint c2v_reg]. split; exact I.
  - exact HG. }
assert (SHOK : sh_ok SEGS c2v_BX c2v_SH E0 (rd W mem3)).
{ unfold c2v_SH. constructor; [|constructor].
  apply (c2v_shent ly3 S3 W mem3 md3 E0 c2v_NP (p_buf P) (Z.max (slot_ser_defs.ser_cap (p_op P)) 1) 0 1 HAR3 Hinbuf);
    [exact U19 | lia | rewrite UNP; lia | rewrite UNP, Hreq; lia]. }
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK c2v_span.
{ lazymatch goal with |- awr_ok ?E ?rs ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?g1 =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' a1 b1 c1 d1 e1 f1 g1) end.
  intros a Ha. exfalso. revert Ha. apply jk_nowin. vm_compute. reflexivity. }
assert (Emem : ms_mem ms = mem3).
{ apply functional_extensionality. intros x. apply HF.
  apply (jk_nowin _ _ (bv_unsigned x)). vm_compute. reflexivity. }
rewrite Emem in HJ.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18.
prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
rewrite (EE0 2%nat 2%bv eq_refl) in Q2. rewrite (EE0 3%nat 3%bv eq_refl) in Q3.
rewrite (EE0 4%nat 4%bv eq_refl) in Q4. rewrite (EE0 8%nat 8%bv eq_refl) in Q8.
rewrite (EE0 9%nat 9%bv eq_refl) in Q9, Q10. rewrite (EE0 10%nat 10%bv eq_refl) in Q21.
rewrite (EE0 18%nat 18%bv eq_refl) in Q18. rewrite (EE0 19%nat 19%bv eq_refl) in Q19.
rewrite (EE0 20%nat 20%bv eq_refl) in Q20. rewrite (EE0 22%nat 22%bv eq_refl) in Q22.
rewrite (EE0 23%nat 23%bv eq_refl) in Q23. rewrite (EE0 24%nat 24%bv eq_refl) in Q24.
rewrite (EE0 25%nat 25%bv eq_refl) in Q25. rewrite (EE0 26%nat 26%bv eq_refl) in Q26.
rewrite (EE0 27%nat 27%bv eq_refl) in Q27.
rewrite Rs1 in Q10. unfold w64 in Q10. rewrite unsigned_lit_small in Q10 by lia.
pmkst HS.
rewrite Emem.
apply SRr_ret.
unfold jc2_call, jc2_at, jcut. split; [exact HFROM|].
unfold d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), mem3, (with_vm_backing (m_vm_lazy md3) mat md3), k, acc0.
split; [unfold cfg_at, w64; rewrite pa_sigma_jtok_is; reflexivity|].
split; [exact Hfrm0|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|].
split; [exact Hk|]. split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ; rewrite Q2; exact Rsp|].
  split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
  split; [rewrite Q9; exact Rs1|]. split; [rewrite Q19; exact Rs19|]. split; [rewrite Q18; exact Rs18|].
  split; [rewrite Q20; exact Rs20|]. rewrite Q27; exact Rs27. }
split.
{ split; [rewrite Q26; exact R26|]. split; [rewrite Q24; exact R24|]. split; [rewrite Q25; exact R25|].
  split.
  - split; [rewrite Q21; exact R10|]. split; [rewrite Q22; exact R22|]. rewrite Q23; exact R23.
  - split; [rewrite Q1; reflexivity|]. split; [exact Q10|]. split; [exact Q11|].
    rewrite Q12, HE0, Eimg_img by (unfold A_TEXT, A_LIM; lia). reflexivity. }
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|].
  split; [exact HXc | exact (jc2_kb0 P)]. }
split; [exact HSP0 | exact HBODY].
Qed.

End h.
End f.
End d.
