(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 211 of its 238 lines of code are new or changed and 1251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeShort.v, with its module paths and module names changed; 187 of its 217 lines of code are new or changed and 208 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC1h YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoArm3TailK DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoArm3JsonC2Defs
DiscoArm3JsonC2Mod.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb slot_ser_Pq.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition c2m_reg : YP09.region := YP09.mkRegion (Some 10%nat) 16 20 0 0 [YP09.mkChunk 16 (CVal 4 (SLit 0))].
Definition c2m_fa : list (nat * afact) :=
  [(10%nat, mkAF 4096 140737479966720 3); (19%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
Definition c2m_G : facts := mkFacts c2m_fa [] [].
Definition c2m_ss : sstate := mkSS C2_M sr_atoms [c2m_reg] None c2m_G.
Definition c2m_SH : list shent := [mkSHE 10 16 20].
Definition c2m_Bx : sv := SOff 19 0.
Definition c2m_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma c2m_le0 : forall w k, le_byte 0 w k = 0.
Proof. intros w k. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l, Z.mod_0_l; lia. Qed.

Lemma c2m_nth_map : forall (l : list byte) (j : nat),
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
  induction l as [|x l IH]; intros j; destruct j as [|j]; cbn [nth map]; try reflexivity. apply IH.
Qed.

Lemma c2m_dsh : forall k, 30 <= k < 192 -> dsh_scr k = 0.
Proof.
  intros k Hk. unfold dsh_scr, dsh, dobjs. cbn [dsh_look]. unfold dsh_in, dsh_live, live_scr.
  cbn [dobj_off dobj_size].
  replace ((32 / 8 <=? k) && (k <? (32 + 144 + 7) / 8)) with false
    by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
  replace ((240 / 8 <=? k) && (k <? (240 + 1296 + 7) / 8)) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  replace (k <? (240 + 1296) / 8) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
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

Theorem jc2_hopM : jc2_hopM_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros P ksl W cf HM.
unfold jc2_mat, jc2_at, jcut, d_arm_at_pf, d_at in HM.
destruct HM as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & accm & -> & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev &
  HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R26 & R24 & R25 & (R21 & R22 & R23) & R10) &
  (HSP1 & HTAB & HBUF & (HX & HSL)) & HSP0 & HBODY).
pose proof (slot_of_lt _ _ _ HSL) as Hksl.
pose proof (jc2_count P W mem3 HX) as Hcnt.
pose proof (jc2_acc6 P W mem3 HX) as Hacc6.
destruct (jc2_some P W mem3 ksl HX HSL) as (Hkind & _).
pose proof HX as (HFIN & Hip & Hc0 & Hlacc & Hkk & Hvk & HU & HCONT & Hlcur & HFAcur & Hkt & Hvt & HMEM & _).
pose proof HMEM as (Mpl & Mpad & MOO & MF6).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs3 & Rs2 & Rs4 & Rs11).
pose proof HBODY as (Tb & Gb & Lkb & Hbt & HFRM & HSHD & _).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K (p_cx P) ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS (p_cx P) ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GWpres & _ & _ & _ & _).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range (p_cx P) ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
assert (Hslot : p_slot P ksl = d_FB (p_cx P) + 240 + 144 * p_count P + 24 * Z.of_nat ksl)
  by (unfold p_slot, jcur, d_obj, dobj_off; lia).
assert (HsB : 4096 <= p_slot P ksl /\ p_slot P ksl + 24 <= d_FB (p_cx P) + 1536) by lia.
assert (VZ : val_mem SEGS (rd W mem3) (p_slot P ksl + 16) 4 0).
{ intros q Hq.
  pose proof (slot_ser_Pq.objs_len (p_buf P) (p_vpad P) (p_acc P ++ [p_cur P]) Mpl MF6) as HOL.
  rewrite length_app in HOL. cbn [length] in HOL.
  assert (Hj : (144 * length (p_acc P) + 24 * ksl + 16 + q <
    length (map (fun b : byte => bv_unsigned b)
      (slot_ser_defs.objs_bytes (p_buf P) (p_vpad P) (p_acc P ++ [p_cur P]))))%nat)
    by (rewrite length_map, HOL; lia).
  destruct (MOO _ Hj) as [Hv _]. specialize (Hv 0%nat ltac:(lia)).
  rewrite c2m_nth_map in Hv.
  rewrite (jc2_zero (p_buf P) (p_vpad P) (p_acc P) (p_cur P) ksl Hacc6 Hlcur Hksl Mpl Hkind) in Hv by lia.
  change (bv_unsigned (Z_to_bv 8 0)) with 0 in Hv.
  rewrite c2m_le0. rewrite c2m_le0 in Hv.
  replace (p_slot P ksl + 16 + Z.of_nat q) with
    (d_obj (p_cx P) OO + Z.of_nat (144 * length (p_acc P) + 24 * ksl + 16 + q) + Z.of_nat 0)
    by (rewrite Hslot; unfold d_obj, dobj_off; lia).
  exact Hv. }
assert (HFB8 : 0 <= d_FB (p_cx P) / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (RA : range_addressable (aview SEGS (w_H W) mem3) SHADOW_OFF (p_slot P ksl + 16) 4).
{ intros x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr.
  replace (SHADOW_OFF + x / 8) with
    (shadow_addr (d_FB (p_cx P)) + (32 + 18 * p_count P + 3 * Z.of_nat ksl))
    by (unfold shadow_addr; rewrite Hslot in Hx; lia).
  rewrite (HSHD (32 + 18 * p_count P + 3 * Z.of_nat ksl) ltac:(unfold DFRAME_SH; lia)). f_equal. apply c2m_dsh. lia. }
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
remember (Eimg (Ereg regs [Z_to_bv 64 SHADOW_OFF])) as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
  by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
assert (U10 : bv_unsigned (ew E0 10) = p_slot P ksl).
{ rewrite (EE0 10%nat 10%bv eq_refl), R10. unfold w64. apply unsigned_lit_small. lia. }
assert (U19 : bv_unsigned (ew E0 19) = SHADOW_OFF).
{ rewrite (EE0 19%nat 19%bv eq_refl), Rs3. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (HG : facts_ok E0 c2m_G).
{ split; [|split; exact I].
  unfold c2m_G, c2m_fa. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10, U19. rewrite Z.pow_0_r, Z.mod_1_r. change (2 ^ 3) with 8.
  unfold SHADOW_OFF in *.
  repeat split; try lia. }
assert (HRA : region_ok SEGS E0 (rd W mem3) c2m_reg).
{ unfold c2m_reg, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E0 _ (p_slot P ksl) 16 4 (SLit 0) 0).
  - cbn [sv_denot]. reflexivity.
  - lia.
  - lia.
  - cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact VZ. }
assert (HS : st_ok_pi (fx := fq) SEGS VAL E0 c2m_ss
  (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + C2_M)) mem3 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold c2m_ss. apply pa_entry_st_ok_full.
  - rewrite HE0. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HRA | constructor].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - exact HG. }
assert (SHOK : sh_ok SEGS c2m_Bx c2m_SH E0 (rd W mem3)).
{ unfold c2m_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem3 E0 c2m_Bx 10 (p_slot P ksl + 16) 4 (p_slot P ksl) 16 20 RA).
  - unfold c2m_Bx. rewrite U_SOff, U19, Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
  - rewrite U_SOff, U10, Z.add_0_r. apply zcanon_id. unfold M64. lia.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx.
    unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK c2m_span.
{ lazymatch goal with |- awr_ok ?Ev ?rs ?a ?b ?cc ?d ?e ?f ?g =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' a b cc d e f g) end.
  intros a (r & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
assert (Emem : ms_mem ms = mem3).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hin & Hr).
  cbn [In] in Hin. unfold c2m_ss in Hin. cbn [ss_mem] in Hin.
  destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val c2m_reg] in Hr; lia. }
pmkst HS.
rewrite Emem. rewrite Emem in HJ.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
rewrite (EE0 2%nat 2%bv eq_refl) in Q2. rewrite (EE0 3%nat 3%bv eq_refl) in Q3.
rewrite (EE0 4%nat 4%bv eq_refl) in Q4. rewrite (EE0 8%nat 8%bv eq_refl) in Q8.
rewrite (EE0 9%nat 9%bv eq_refl) in Q9. rewrite (EE0 10%nat 10%bv eq_refl) in Q10.
rewrite (EE0 18%nat 18%bv eq_refl) in Q18. rewrite (EE0 19%nat 19%bv eq_refl) in Q19.
rewrite (EE0 20%nat 20%bv eq_refl) in Q20. rewrite (EE0 21%nat 21%bv eq_refl) in Q21.
rewrite (EE0 22%nat 22%bv eq_refl) in Q22. rewrite (EE0 23%nat 23%bv eq_refl) in Q23.
rewrite (EE0 24%nat 24%bv eq_refl) in Q24. rewrite (EE0 25%nat 25%bv eq_refl) in Q25.
rewrite (EE0 26%nat 26%bv eq_refl) in Q26. rewrite (EE0 27%nat 27%bv eq_refl) in Q27.
assert (U9 : bv_unsigned (ew E0 9) = d_A (p_cx P)).
{ rewrite (EE0 9%nat 9%bv eq_refl), Rs1. unfold w64. apply unsigned_lit_small. lia. }
rewrite U9 in Q11.
apply SRr_ret.
unfold jc2_cpy, jc2_at, jcut.
split; [exact HFROM|].
unfold d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), mem3, (with_vm_backing (m_vm_lazy md3) mat md3), k, accm.
split; [unfold cfg_at; replace (BASE + (SIGMA AS___asan_memcpy - BASE)) with (SIGMA AS___asan_memcpy) by lia;
  reflexivity|].
split; [exact Hfrm0|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite Q2; exact Rsp|].
  split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
  split; [rewrite Q9; exact Rs1|]. split; [rewrite Q19; exact Rs3|]. split; [rewrite Q18; exact Rs2|].
  split; [rewrite Q20; exact Rs4|]. rewrite Q27; exact Rs11. }
split.
{ split; [rewrite Q26; exact R26|]. split; [rewrite Q24; exact R24|]. split; [rewrite Q25; exact R25|].
  split.
  - split; [rewrite Q21; exact R21|]. split; [rewrite Q22; exact R22|]. rewrite Q23; exact R23.
  - split; [unfold w64, SLOT_OFF; exact Q1|]. split; [rewrite Q10; exact R10|].
    split; [unfold w64; exact Q11|]. unfold w64; exact Q12. }
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HX | exact HSL]. }
split; [exact HSP0 | exact HBODY].
Qed.
End h.
End f.
End d.
