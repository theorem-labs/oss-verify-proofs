(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 211 of its 238 lines of code are new or changed and 1251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeShort.v, with its module names changed; 850 of its 897 lines of code are new or changed and 191 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeCall2.v, with its module paths, module names and numbers changed; 175 of its 302 lines of code are new or changed and 770 lines of the source are left out. *)
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
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC1i YC81 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacHuntRole.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoArm3TailK DiscoYEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3 DiscoArm3TailDefs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import hunt_c slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac t5_bvne := let Hq := fresh "Hq" in intro Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).

Lemma t5_kept : forall (E : env) (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma t5_dE : forall (cx : dcx) E j ws, d_E cx E -> (530 <= j)%nat -> d_E cx (havoc E j ws).
Proof.
intros cx E j ws (H1 & H32 & HI & H60 & H516 & H529) Hj.
split; [|split; [|split; [|split; [|split]]]].
- intros nn r Hr. pose proof (bv_unsigned_in_range 5 r) as Hb. change (bv_modulus 5) with 32 in Hb.
  rewrite ew_havoc_old by lia. exact (H1 nn r Hr).
- rewrite ew_havoc_old by lia. exact H32.
- apply img_env_havoc_hi; [exact HI | unfold A_LIM; lia].
- rewrite ew_havoc_old by (unfold AT_A; lia). exact H60.
- rewrite ew_havoc_old by (unfold AT_F; lia). exact H516.
- rewrite ew_havoc_old by (unfold AT_SH; lia). exact H529.
Qed.

Lemma t5_regs_ok : forall (cx : dcx) (E : env) (R : bvmap 5 word),
  img_env VAL A_LIM E -> getr R 1 = Z_to_bv 64 (BASE + RL_OFF) ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs))) (SLit 0 :: SOff A_TEXT RL_OFF :: atom_regs 532 30) R.
Proof.
intros cx E R HEI H1.
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr R) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEI | unfold AT_FL, A_LIM; lia]).
regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity
                             | rewrite H1; symmetry; exact (codeptr_val _ RL_OFF HEId) ]).
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DROH : d_ro_hyps B.
Hypothesis DBPC : d_body_pcall_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis THROLE : treac_hunt_role_spec B.
Hypothesis DCAN : d_can_hyps B tfib_K.

Theorem a3t_T5 : a3t_step_spec (a3t_c B MT XM_LIB RLO RHI tfib_K) (a3t_r B MT XM_LIB RLO RHI tfib_K).
Proof.
intros cx h i n now W c Hc0.
unfold a3t_c, a3t_at, d_arm_at, d_at in Hc0.
destruct Hc0 as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HCSR & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
  Hi & Hn & Hnow & HRL & (R21 & R22 & R26) & HSP1 & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs3 & Rs2 & Rs4 & Rs11).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
remember (Eimg (Ereg regs [Z_to_bv 64 SB])) as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
  by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
assert (HS : st_ok_pi (fx := fq) SEGS VAL E0 (mkSS C_OFF sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + C_OFF)) mem3 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE0. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
unfold cfg_at, w64.
reshok_bx HS 32%nat.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?E ?rs ?a ?b ?c ?d ?e ?f ?g =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' a b c d e f g) end.
  apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem3).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hr & _). cbn in Hr. destruct Hr. }
pmkst HS.
rewrite Emem. rewrite Emem in HJ.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18.
prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
rewrite (EE0 2%nat 2%bv eq_refl) in Q2. rewrite (EE0 3%nat 3%bv eq_refl) in Q3. rewrite (EE0 4%nat 4%bv eq_refl) in Q4.
rewrite (EE0 8%nat 8%bv eq_refl) in Q8. rewrite (EE0 9%nat 9%bv eq_refl) in Q9. rewrite (EE0 21%nat 21%bv eq_refl) in Q10.
rewrite (EE0 18%nat 18%bv eq_refl) in Q18. rewrite (EE0 19%nat 19%bv eq_refl) in Q19.
rewrite (EE0 20%nat 20%bv eq_refl) in Q20. rewrite (EE0 21%nat 21%bv eq_refl) in Q21.
rewrite (EE0 22%nat 22%bv eq_refl) in Q22.
rewrite (EE0 26%nat 26%bv eq_refl) in Q26. rewrite (EE0 27%nat 27%bv eq_refl) in Q27.
rewrite R21 in Q10.
clear HS SHOK HF HFr HG Emem RUN.
set (R := ms_regs ms) in *.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pose proof HBODY as (T & G & Lk & HL & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & _).
pose proof (d_hslots_of_frame cx h dsh_loop W mem3 HFRM) as HHS.
pose proof HOBJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HlenH & HgH & HokH & HourH).
pose proof HBLK as (HPerm0 & _ & _ & HOFFb).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md' k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md' k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _ & _ & _ & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
assert (SpR : spZ R = d_A cx) by (unfold spZ in *; rewrite Q2; exact Rsp).
assert (HEIE : img_env VAL A_LIM E) by exact (proj1 (proj2 (proj2 HE))).
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr R) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEIE | unfold AT_FL, A_LIM; lia]).
pose proof (DSEAT LAWS PAL fq cx dsh_loop ly3 S3 W R mem3 md' k E AF_both3_reac_hunt_role
  (SLit 0 :: SOff A_TEXT RL_OFF :: atom_regs 532 30) (map (getr R) (tl all_regs)) [] [] [] (d_facts [] [])
  HCTX HE HREG HFLAG (t5_regs_ok cx E R HEIE Q1)
  (DFACTS LAWS cx ly3 S3 W mem3 md' k E (map (getr R) (tl all_regs)) [] [] HCTX HE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
assert (Hin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & _).
change (req_size HUNT_SIZE) with 480 in Hbceil, Hbapp.
assert (HAFN : afn_pre SEGS B REAC_HUNT_ROLE_STK ly3 S3 W (regupd R 8 (Z_to_bv 64 0)) mem3 md' []).
{ pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
  eapply (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md' k (regupd R 8 (Z_to_bv 64 0)) REAC_HUNT_ROLE_STK
    (d_A cx - d_S cx) [] HJ).
  - unfold spZ. rewrite getr_other by t5_bvne. fold (spZ R). rewrite SpR. lia.
  - pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as DS.
    rewrite GA32 in DA. rewrite GS16 in DS.
    replace (d_A cx - d_S cx) with ((2 * (d_A cx / 32) - d_S cx / 16) * 16) by lia. apply Z_mod_mult.
  - lia.
  - unfold REAC_HUNT_ROLE_STK, ESTACK. lia.
  - unfold REAC_HUNT_ROLE_STK, ESTACK, LLVMF_STK. lia.
  - rewrite getr_other by t5_bvne. rewrite Q1. apply ret_ok_codeptr_v; [unfold RL_OFF; lia | reflexivity].
  - unfold raZ. rewrite getr_other by t5_bvne. rewrite Q1. rewrite unsigned_lit_small by (unfold RL_OFF; lia).
    unfold RL_OFF. lia.
  - rewrite getr_other by t5_bvne. rewrite Q3. exact Rgp.
  - rewrite getr_other by t5_bvne. rewrite Q4. exact Rtp.
  - left. split; [|reflexivity]. left. unfold s0Z. rewrite getr_same by t5_bvne.
    rewrite unsigned_lit_small by lia. lia. }
rewrite pa_sigma_reac_hunt_role.
eapply SRr_mono.
{ apply (THROLE fq ly3 S3 W R mem3 md' [] h h HUNT_SIZE HL HAFN).
  - exact Q10.
  - lia.
  - pose proof (Z.div_mod h 16 ltac:(lia)) as Dh. rewrite Hb16 in Dh.
    replace h with ((2 * (h / 16)) * 8) by lia. apply Z_mod_mult.
  - exact Hin.
  - lia.
  - change (req_size HUNT_SIZE) with 480. lia.
  - exact HokH.
  - exact HgH. }
cbv beta. intros W2 c2 HW2 Hpost.
unfold treac_hunt_role_post, apost_base in Hpost.
destruct Hpost as (fq4 & ly4 & S4 & regs4 & mem4 & md4 & -> & Hfreg4 & Hfcsr4 & HJc & HP & Ha0' & -> & -> & -> & HPerm).
assert (HCSR4 : lib.Lib.FP.frm0 (@YK11.fp_csr fq4)) by exact (a3t_frm0 _ _ HCSR Hfcsr4).
pose proof (ajournal_sub SEGS B LAWS pa_segs_low LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md' k REAC_HUNT_ROLE_STK (spZ R) [] [] ly3 S3 W mem4 md4 0 HJ HJc
  ltac:(rewrite SpR; unfold LLVMF_STK, REAC_HUNT_ROLE_STK, ESTACK; lia) ltac:(rewrite SpR; lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ4.
cbn [app] in HJ4. rewrite Z.add_0_r in HJ4.
assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem4 md4 k) by exact (conj HBASE (conj HJ4 HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem4 md4 k HCTX4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & KF1 & _ & _ & KF4 & _).
assert (KA : forall a, d_A cx <= a < 2 ^ 64 -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply KF1; [lia | rewrite SpR; lia]. }
assert (KFR : forall a, d_FB cx <= a < d_FB cx + 4096 -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply (KF4 DFRAME_CLASS (c_fpos cx) a HFin3);
  [ left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA3;
    change (fs_frame_bytes DFRAME_CLASS) with 4096; lia
  | intros Hfp; exact (inFP_nil a Hfp) ]. }
assert (KSH : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 ->
  aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply (KF4 DFRAME_CLASS (c_fpos cx) a HFin3);
  [ right; unfold in_zr; cbn [fst snd]; rewrite EFA3;
    change (fs_frame_bytes DFRAME_CLASS / 8) with 512; lia
  | intros Hfp; exact (inFP_nil a Hfp) ]. }
assert (HFB8 : 0 <= d_FB cx / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (ES2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite (proj1 HE 2%nat 2%bv eq_refl); reflexivity).
assert (EA : ew E 60 = w64 (d_A cx)) by exact (proj1 (proj2 (proj2 (proj2 HE)))).
assert (EF : ew E 516 = w64 (d_FB cx)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 HE))))).
assert (ESH : ew E 529 = w64 (shadow_addr (d_FB cx))) by exact (proj2 (proj2 (proj2 (proj2 (proj2 HE))))).
jafter_call_keep_hi HS1 562%nat regs4 (mrestrict (w_H W) mem4) HP [0;1;2;3]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (t5_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_S cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). exact ES2.
    + intros a Ha. apply KA. lia.
    + intros a Ha. lia.
  - eapply (t5_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_A cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EA. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KA. lia.
    + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
  - eapply (t5_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_FB cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EF. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KFR. lia.
    + intros a Ha. apply GFpres4. lia.
  - eapply (t5_kept _ (w_H W) (w_H W) mem3 mem4 _ (shadow_addr (d_FB cx))).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite ESH. unfold w64. apply unsigned_lit_small.
      unfold shadow_addr, SHADOW_OFF. lia.
    + intros a Ha. apply KSH. lia.
    + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
      apply GFsh4. lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
assert (HE2 : d_E cx (havoc (d_env cx E (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)))
  by (apply t5_dE; [apply d_E_env; exact HE | lia]).
assert (HFL2 : ew (havoc (d_env cx E (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)) AT_FL =
  Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
  by (rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
assert (HHS4 : d_hslots cx h W mem4).
{ eapply (d_hslots_kept cx h W W mem3 mem4); [|exact HHS].
  intros a Ha. apply KA. lia. }
pose proof (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h dsh_loop ly3 S3 W md4 k _ _
  (YK11.mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + 8892)) mem4 (YK11.seg_rom SEGS))
  HCTX4 HE2 HFL2 HS2 ltac:(vm_compute; reflexivity) HHS4) as (HFRM4 & HSHD4).
pose proof (DBPC LAWS DROH DCAN cx h n [] dsh_loop dsh_loop ly3 S3 W mem3 md' ly3 S3 W mem4 md4 k REAC_HUNT_ROLE_STK
  (spZ R) [] 0 HBODY (conj HBASE HJ4) HJc
  ltac:(rewrite SpR; unfold LLVMF_STK, REAC_HUNT_ROLE_STK, ESTACK; lia) ltac:(rewrite SpR; lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))
  ltac:(intros (a & Ha & _); exfalso; exact (inFP_nil a Ha))
  HPerm HFRM4 HSHD4) as HBODY4.
assert (P2 : getr regs4 2 = getr regs 2) by (transitivity (getr R 2); [exact (HP 2 ltac:(unfold acallee_saved; lia)) | exact Q2]).
assert (P3 : getr regs4 3 = getr regs 3) by (transitivity (getr R 3); [exact (HP 3 ltac:(unfold acallee_saved; lia)) | exact Q3]).
assert (P4 : getr regs4 4 = getr regs 4) by (transitivity (getr R 4); [exact (HP 4 ltac:(unfold acallee_saved; lia)) | exact Q4]).
assert (P8 : getr regs4 8 = getr regs 8) by (transitivity (getr R 8); [exact (HP 8 ltac:(unfold acallee_saved; lia)) | exact Q8]).
assert (P9 : getr regs4 9 = getr regs 9) by (transitivity (getr R 9); [exact (HP 9 ltac:(unfold acallee_saved; lia)) | exact Q9]).
assert (P18 : getr regs4 18 = getr regs 18) by (transitivity (getr R 18); [exact (HP 18 ltac:(unfold acallee_saved; lia)) | exact Q18]).
assert (P19 : getr regs4 19 = getr regs 19) by (transitivity (getr R 19); [exact (HP 19 ltac:(unfold acallee_saved; lia)) | exact Q19]).
assert (P20 : getr regs4 20 = getr regs 20) by (transitivity (getr R 20); [exact (HP 20 ltac:(unfold acallee_saved; lia)) | exact Q20]).
assert (P21 : getr regs4 21 = getr regs 21) by (transitivity (getr R 21); [exact (HP 21 ltac:(unfold acallee_saved; lia)) | exact Q21]).
assert (P22 : getr regs4 22 = getr regs 22) by (transitivity (getr R 22); [exact (HP 22 ltac:(unfold acallee_saved; lia)) | exact Q22]).
assert (P26 : getr regs4 26 = getr regs 26) by (transitivity (getr R 26); [exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact Q26]).
assert (P27 : getr regs4 27 = getr regs 27) by (transitivity (getr R 27); [exact (HP 27 ltac:(unfold acallee_saved; lia)) | exact Q27]).
pose proof HSP1 as ((H208 & H320) & H192 & H200).
unfold a3t_r, a3t_at, d_arm_at, d_at.
exists fq4, ly3, S3, regs4, mem4, md4, k, acc.
split; [unfold cfg_at, w64; rewrite Q1; reflexivity|]. split; [exact HCSR4|].
split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR|].
split; [exact Hk|].
split; [exact Hnev|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite P2; exact Rsp|].
  split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact Rs0|].
  split; [rewrite P9; exact Rs1|]. split; [rewrite P19; exact Rs3|]. split; [rewrite P18; exact Rs2|].
  split; [rewrite P20; exact Rs4|]. rewrite P27; exact Rs11. }
split.
{ split; [rewrite P21; exact R21|]. split; [rewrite P22; exact R22|]. rewrite P26; exact R26. }
assert (KV : forall off v, 0 <= off <= 352 -> val_mem SEGS (mrestrict (w_H W) mem3) (d_A cx + off) 8 v ->
  val_mem SEGS (mrestrict (w_H W) mem4) (d_A cx + off) 8 v).
{ intros off v Hoff Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact Hv].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KA. lia. }
split.
{ split; [split|split].
  - apply KV; [lia | exact H208].
  - apply KV; [lia | exact H320].
  - apply KV; [lia | exact H192].
  - apply KV; [lia | exact H200]. }
split.
{ split; [apply KV; [lia | exact H208] | apply KV; [lia | exact H320]]. }
exact HBODY4.
Qed.

End h.
End f.
End d.
