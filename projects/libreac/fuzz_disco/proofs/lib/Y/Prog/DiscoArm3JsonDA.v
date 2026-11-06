(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 211 of its 238 lines of code are new or changed and 1251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeShort.v, with its module paths and module names changed; 223 of its 256 lines of code are new or changed and 205 lines of the source are left out. *)
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
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC1h YC1i YC88 YI67 YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut
DiscoArm3JsonDDefs DiscoArm3JsonK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition da_fa : list (nat * afact) :=
  [(19%nat, mkAF SB SB 0); (20%nat, mkAF 32 32 0); (21%nat, mkAF 0 968 0); (22%nat, mkAF 0 7 0);
   (24%nat, mkAF 4096 140737479966720 0); (25%nat, mkAF 18446603336229584895 18446744073709547519 0);
   (26%nat, mkAF 2 969 0); (33%nat, mkAF 4096 140737479966720 0); (34%nat, mkAF 33 255 0)].
Definition da_cs : list acond := [mkAC BC_LTU (SOff 21 1) (SOff 26 0)].
Definition da_al : list (sv * sv) := [(SAlu ALU_ADD (SOff 24 0) (SOff 21 1), SOff 33 0)].
Definition da_G : facts := mkFacts da_fa da_cs da_al.
Definition da_rA : YP09.region :=
  YP09.mkRegion (Some 9%nat) 304 312 0 0 [YP09.mkChunk 304 (CVal 8 (SLit INT32_MAX))].
Definition da_rB : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition da_ss : sstate := mkSS OEND_OFF sr_atoms [da_rA; da_rB] None da_G.
Definition da_SH : list shent := [mkSHE 33 0 1].
Definition da_Bx : sv := SOff 19 0.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma da_shent : forall ly S (W : world SEGS) mem md (E : env) (bx q : nat) (bp len lo hi : Z),
  AR SEGS B ly S W mem md -> In (bp, len) (ablocks B ly S) ->
  U E (SOff bx 0) = SHADOW_OFF -> 0 <= lo <= hi ->
  bp <= U E (SOff q 0) + lo -> U E (SOff q 0) + hi <= bp + req_size len ->
  shent_ok SEGS (SOff bx 0) E (rd W mem) (mkSHE q lo hi).
Proof.
  intros ly S W mem md E bx q bp len lo hi HAR Hin HB Hlh Hlo Hhi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & _).
  eapply (shent_ok_of_range SEGS (w_H W) mem E (SOff bx 0) q bp (req_size len) (U E (SOff q 0)) lo hi).
  - exact (range_addressable_of_block SEGS B LAWS ly S W mem md bp len bp (req_size len) HAR Hin
             ltac:(lia) ltac:(lia)).
  - exact HB.
  - reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

Theorem a3j_D_A : jd_A_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin p cur count acc vpad W c HIN.
unfold joend_in, jcut, d_arm_at_pf, d_at in HIN.
destruct HIN as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc0 & -> & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev &
  HMO & Hacc & Hi & Hn & Hnow & HRL & (R26 & R24 & R25 & R21 & R22) & (HSP1 & HTAB & HBUF & HXS) & HSP0 & HBODY).
destruct HXS as (HFIN & Hp0 & Hcount & Hlacc & Hb125 & HAF & Hlcur & HFAcur & HMEM).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs3 & Rs2 & Rs4 & Rs11).
pose proof HFIN as (HJR & Hfin8 & HNOWS & HTLEN & HTOKS).
pose proof HBUF as ((Hr2 & Hrc) & HGARR).
pose proof ASAN_CEIL_range as (Hceil0 & _). unfold ASAN_CEIL in Hceil0.
assert (Hrle : a3_r T1 now <= 969) by (unfold a3_r; lia).
pose proof (jd_count_le T1 now fin (p + 1) count acc cur HFIN HAF) as Hc7.
assert (Hp1r : p + 1 < a3_r T1 now).
{ destruct (jobjs_after_step (a3_text T1 now) fin (p + 1) count acc cur HAF) as [(Hcm & _) | (_ & Hcb & _)].
  - rewrite (json_ws_id (a3_text T1 now) (p + 1) HNOWS ltac:(lia)) in Hcm.
    destruct (at_byte_true _ _ _ Hcm) as (Hlt & _). unfold a3_r. unfold jlen in Hlt. lia.
  - rewrite (json_ws_id (a3_text T1 now) (p + 1) HNOWS ltac:(lia)) in Hcb.
    destruct (at_byte_true _ _ _ Hcb) as (Hlt & _). unfold a3_r. unfold jlen in Hlt. lia. }
pose proof (jno_ws_byte (a3_text T1 now) (p + 1) HNOWS ltac:(unfold jlen, a3_r in *; lia)) as HV.
pose proof HBODY as (Tb & Gb & Lkb & Hbt & HFRM & HSHD & HOBJ & HBLK & _).
pose proof HBLK as (HPerm0 & _).
assert (Hinbuf : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _ & _ & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinbuf) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0) as [Eq | Eq]; lia. }
rewrite Hreq in Hbceil, Hbapp.
unfold in_app, ASAN_CEIL in Hbapp.
assert (M304 : val_mem SEGS (rd W mem3) (d_A cx + 304) 8 INT32_MAX).
{ pose proof HFRM as (Ef & HEf & HREG & _).
  unfold d_regions in HREG. rewrite !Forall_cons_iff in HREG. destruct HREG as (_ & HRAf & _).
  pose proof HEf as (_ & _ & _ & EfA & _).
  destruct HRAf as (_ & _ & _ & HCf). cbn [YP09.r_base YP09.r_chunks base_val] in HCf.
  rewrite Forall_forall in HCf.
  pose proof (HCf (YP09.mkChunk 304 (CVal 8 (SLit INT32_MAX))) ltac:(apply jk_in; vm_compute; reflexivity)) as HC.
  pose proof (val_of_chunk_ok SEGS Ef _ _ 304 8 (SLit INT32_MAX) INT32_MAX HC ltac:(reflexivity)
    ltac:(cbn; unfold INT32_MAX; lia) ltac:(cbn; lia)) as HVM.
  rewrite EfA in HVM. unfold w64 in HVM. rewrite unsigned_lit_small in HVM by lia. exact HVM. }
remember (Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 (buf + p + 1); Z_to_bv 64 (jbyte (a3_text T1 now) (p + 1))]))
  as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
  by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
assert (E33 : ew E0 33 = Z_to_bv 64 (buf + p + 1)).
{ rewrite HE0, Eimg_low by (unfold A_TEXT; lia). change 33%nat with (32 + 1)%nat.
  rewrite ew_Ereg_extra. reflexivity. }
assert (E34 : ew E0 34 = Z_to_bv 64 (jbyte (a3_text T1 now) (p + 1))).
{ rewrite HE0, Eimg_low by (unfold A_TEXT; lia). change 34%nat with (32 + 2)%nat.
  rewrite ew_Ereg_extra. reflexivity. }
assert (U9 : bv_unsigned (ew E0 9) = d_A cx).
{ rewrite (EE0 9%nat 9%bv eq_refl), Rs1. unfold w64. apply unsigned_lit_small. lia. }
assert (U19 : bv_unsigned (ew E0 19) = SHADOW_OFF).
{ rewrite (EE0 19%nat 19%bv eq_refl), Rs3. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (U20 : bv_unsigned (ew E0 20) = 32).
{ rewrite (EE0 20%nat 20%bv eq_refl), Rs4. unfold w64. apply unsigned_lit_small. lia. }
assert (U21 : bv_unsigned (ew E0 21) = p).
{ rewrite (EE0 21%nat 21%bv eq_refl), R21. unfold w64. apply unsigned_lit_small. lia. }
assert (U22 : bv_unsigned (ew E0 22) = count).
{ rewrite (EE0 22%nat 22%bv eq_refl), R22. unfold w64. apply unsigned_lit_small. lia. }
assert (U24 : bv_unsigned (ew E0 24) = buf).
{ rewrite (EE0 24%nat 24%bv eq_refl), R24. unfold w64. apply unsigned_lit_small. lia. }
assert (U25 : bv_unsigned (ew E0 25) = 2 ^ 64 - 1 - buf).
{ rewrite (EE0 25%nat 25%bv eq_refl), R25, jk_lnot by lia. apply unsigned_lit_small. lia. }
assert (U26 : bv_unsigned (ew E0 26) = a3_r T1 now).
{ rewrite (EE0 26%nat 26%bv eq_refl), R26. unfold w64. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E0 33) = buf + p + 1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E0 34) = jbyte (a3_text T1 now) (p + 1))
  by (rewrite E34; apply unsigned_lit_small; lia).
assert (HGf : facts_ok E0 da_G).
{ split; [|split].
  - unfold da_G, da_fa. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U20, U21, U22, U24, U25, U26, U33, U34. rewrite Z.pow_0_r. rewrite !Z.mod_1_r.
    unfold SB, SHADOW_OFF in *.
    repeat split; try lia.
  - unfold da_G, da_cs. cbn [f_conds conds_ok].
    split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite branch_ltu_U, !U_SOff, U21, U26.
    rewrite !zcanon_id by (unfold M64; lia). apply Z.ltb_lt; lia.
  - unfold da_G, da_al. cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj.
    rewrite (U_add_off_atom E0 24 0 21 1 ltac:(rewrite U24, U21; unfold M64; lia) ltac:(rewrite U21; unfold M64; lia)).
    rewrite U_SOff, U24, U21, U33. rewrite zcanon_id by (unfold M64; lia). lia. }
destruct (jk_byte W mem3 buf (a3_text T1 now ++ [0]) (p + 1) HGARR
  ltac:(rewrite length_app; cbn [length]; unfold a3_r in *; lia)) as (Hvp1 & _).
rewrite (jk_nth_app (a3_text T1 now) (p + 1) ltac:(unfold jlen, a3_r in *; lia)) in Hvp1.
assert (HRA : region_ok SEGS E0 (rd W mem3) da_rA).
{ unfold da_rA, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E0 _ (d_A cx) 304 8 (SLit INT32_MAX) INT32_MAX).
  - reflexivity.
  - cbn [Z.of_N]. unfold INT32_MAX. lia.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact M304. }
assert (HRB : region_ok SEGS E0 (rd W mem3) da_rB).
{ unfold da_rB, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U33.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E0 _ (buf + p + 1) 0 1 (SOff 34 0) (jbyte (a3_text T1 now) (p + 1))).
  - cbn [sv_denot]. rewrite U34, Z.add_0_r. reflexivity.
  - cbn [Z.of_N]. lia.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
    replace (buf + p + 1 + 0) with (buf + (p + 1)) by lia. exact Hvp1. }
assert (HPD : pairwise_disjoint E0 [da_rA; da_rB]).
{ cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, da_rA, da_rB.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33.
  split; [split; [right; lia | exact I] | split; [exact I | exact I]]. }
assert (HS : st_ok_pi (fx := fq) SEGS VAL E0 da_ss
  (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + OEND_OFF)) mem3 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold da_ss. apply pa_entry_st_ok_full.
  - rewrite HE0. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HRA | constructor; [exact HRB | constructor]].
  - exact HPD.
  - exact HGf. }
assert (SHOK : sh_ok SEGS da_Bx da_SH E0 (rd W mem3)).
{ unfold da_SH, da_Bx. constructor; [|constructor].
  apply (da_shent ly3 S3 W mem3 md3 E0 19%nat 33%nat buf (Z.max (slot_ser_defs.ser_cap op) 1) 0 1
    HAR3 Hinbuf).
  - rewrite U_SOff, U19, Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
  - lia.
  - rewrite U_SOff, U33, Z.add_0_r. rewrite zcanon_id by (unfold M64; lia). lia.
  - rewrite U_SOff, U33, Z.add_0_r. rewrite zcanon_id by (unfold M64; lia). rewrite Hreq. lia. }
clear HRA HRB HPD HGf.
unfold cfg_at. change (w64 (BASE + OEND_OFF)) with (Z_to_bv 64 (BASE + OEND_OFF)).
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MID_OFF.
{ lazymatch goal with |- awr_ok ?Ev ?rs ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?g1 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' a1 b1 c1 d1 e1 f1 g1) end.
  intros a Ha. exfalso. revert Ha. apply jk_nowin. vm_compute. reflexivity. }
assert (Emem1 : ms_mem ms = mem3).
{ apply functional_extensionality. intros x. apply HF. apply jk_nowin. vm_compute. reflexivity. }
clear HF HFr HG.
pmkst HS.
rewrite Emem1. rewrite Emem1 in HJ.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
rewrite (EE0 2%nat 2%bv eq_refl) in Q2. rewrite (EE0 3%nat 3%bv eq_refl) in Q3.
rewrite (EE0 4%nat 4%bv eq_refl) in Q4. rewrite (EE0 8%nat 8%bv eq_refl) in Q8.
rewrite (EE0 9%nat 9%bv eq_refl) in Q9. rewrite (EE0 18%nat 18%bv eq_refl) in Q18.
rewrite (EE0 19%nat 19%bv eq_refl) in Q19. rewrite (EE0 20%nat 20%bv eq_refl) in Q20.
rewrite (EE0 22%nat 22%bv eq_refl) in Q22. rewrite (EE0 24%nat 24%bv eq_refl) in Q24.
rewrite (EE0 25%nat 25%bv eq_refl) in Q25. rewrite (EE0 26%nat 26%bv eq_refl) in Q26.
rewrite (EE0 27%nat 27%bv eq_refl) in Q27.
rewrite E34 in Q10. rewrite U21 in Q11.
apply SRr_ret.
unfold jmid, jcut. split; [exact HFROM|].
unfold d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), mem3.
eexists. exists k, acc0.
split; [unfold cfg_at, w64; reflexivity|].
split; [exact Hfrm0|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|].
split; [exact Hk|]. split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite Q2; exact Rsp|].
  split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
  split; [rewrite Q9; exact Rs1|]. split; [rewrite Q19; exact Rs3|]. split; [rewrite Q18; exact Rs2|].
  split; [rewrite Q20; exact Rs4|]. rewrite Q27; exact Rs11. }
split.
{ split; [rewrite Q26; exact R26|]. split; [rewrite Q24; exact R24|]. split; [rewrite Q25; exact R25|].
  split; [rewrite Q10; unfold w64; reflexivity|].
  split; [rewrite Q11; unfold w64; reflexivity|].
  rewrite Q22; exact R22. }
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|].
  split; [exact HFIN|]. split; [exact Hp0|]. split; [exact Hp1r|]. split; [lia|].
  split; [exact Hlacc|]. split; [exact HAF|]. split; [exact Hlcur|]. split; [exact HFAcur | exact HMEM]. }
split; [exact HSP0 | exact HBODY].
Qed.

End h.
End f.
End d.
