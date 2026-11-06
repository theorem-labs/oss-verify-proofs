(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 pin asan 1be0f53d96cb), ex_string's UTF-8 cuts (ExsA_Stmt.v
   CUT_UTF8 / CUT_UTF8R):
     A 0x84228 lw a1,36(sp) (the code point cp); mv a0,s3 (o); jal ex_utf8 (A 0x84230, the callee's run form
     texutf8_runA, ExsA_Callee.v, through the Section hypothesis HUTF8), then CUT_UTF8R at the return A 0x84234:
     add s3,s3,a0 (o + n); li a3,101 / a4,91 / a5,113 / a6,114 (ESK again); j 0x84378 (CUT_CONT, acc ++ PjGrammar.utf8
     cp).
   PORTED from lib/B/Prog/ExsB_Utf8.v (a Theorem Labs lane's B' walk, on 66eac2b9522a): es_cut_utf8 is the donor's proof (one run
   to the call, the callee's run form, the return) re-pointed at A'; es_cut_utf8r is the donor's last run alone.
   CHANGED for A': the pcs (UTF8 0x1f4, UTF8R 0x200, CONT 0x344; B' 0x238 / 0x244 / 0x3b8); o / the next p are s3 / s5
   (atoms 19 / 21; B': s2 / s4); the return adds n into s3 (B': o + n into a0) and re-sets a3 .. a6 (B': a4 .. a7, t0
   with a4 = -1). REMOVED: the B' UBSan checks after the call (bltu a0,s2 / beqz s2 / beqz a0 to 0x84834) do not exist
   at A', so es_cut_utf8r is one run with no branch, and the entry facts on n (atom 10) and o that decided them go.
   Numerals: 0x1f4, 0x200, 0x344 (DERIVED: cut offsets); 36 (LENGTH: the code point's slot); 4 (LENGTH: at most four
   UTF-8 bytes); 101, 91, 113, 114 (WORD: the ESK literals); 2 ^ 21 (LENGTH: the code point range ex_utf8 takes). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Img Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA ExsA_Stmt ExsA_Lib ExsA_Sym ExsA_Exit ExsA_Cont ExsA_LH ExsA_Callee.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExsB_Model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).

Definition ES_RC : YP09.region := YP09.mkRegion (Some 2%nat) 36 40 0 0 [YP09.mkChunk 36 (CVal 4 (SOff 45 0))].
Definition ss_u8 : sstate :=
  mkSS (ES_PC + 0x1f4) sr_atoms [ES_RC] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (19%nat, mkAF 4096 ES_CEIL 0); (21%nat, mkAF 4096 ES_CEIL 0);
              (45%nat, mkAF 1 (2 ^ 21 - 1) 0)] [] []).
Definition ss_u8r : sstate :=
  mkSS (ES_PC + 0x200) sr_atoms [] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.
Hypothesis HUTF8 : texutf8_runA SK B prh_pst ARx (A_prog_sigma AS_ex_utf8).

Lemma es_cut_utf8r : forall E p, CUT_CONT B ARx SK E p -> CUT_UTF8R B ARx SK E p.
Proof.
intros E p HCT. unfold CUT_UTF8R. intros lyc Sc Hpc regs memc mdc k acc cpt HP HB HEG GA R10 R19 R21.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC0 & HC8 & HC16 & HC24 & R2 & R8 & R18 & R22 &
  R23 & R24 & R25 & R26 & R27 & R3 & R4 & HSc & HMN).
pose proof HEG as (HG1 & HG2 & HG3).
rewrite length_app in HG2.
unfold es_SP in *.
assert (Hn14 : (1 <= length (PjGrammar.utf8 cpt) <= 4)%nat).
{ unfold PjGrammar.utf8. destruct (Z.ltb_spec cpt 128); [cbn; lia|]. destruct (Z.ltb_spec cpt 2048); [cbn; lia|].
  destruct (Z.ltb_spec cpt 65536); cbn; lia. }
remember (es_xE regs (e_regs E) []) as Ex eqn:HEx.
assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
assert (E10 : ew Ex 10 = Z_to_bv 64 (Z.of_nat (length (PjGrammar.utf8 cpt))))
  by (rewrite HEx, (es_xE_reg _ _ _ 10%bv 10) by reflexivity; exact R10).
assert (E19 : ew Ex 19 = Z_to_bv 64 (e_scr E + Z.of_nat (length acc)))
  by (rewrite HEx, (es_xE_reg _ _ _ 19%bv 19) by reflexivity; exact R19).
assert (E21 : ew Ex 21 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 21%bv 21) by reflexivity; exact R21).
assert (HS : st_ok_pi rsegs VAL Ex ss_u8r
  (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x200))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_u8r.
  apply (pa_entry_st_ok_full (fx := fx) (L := A_prog_listing) (PI := PI_prog_A)).
  - rewrite HEx. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, !unsigned_lit_small by lia. change (2 ^ 4) with 16.
    repeat split; lia. }
assert (SHOK : sh_ok rsegs (SOff 23 0) [] Ex (rdW (e_W E) memc)) by apply Forall_nil.
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS _ (es_plaw E)).
assert (HPM : es_P E memc) by exact HMN.
unfold cfg_at, w64. rewrite es_pc_eq.
assert (HPN : Forall (fun rz => getr regs (fst rz) = Z_to_bv 64 (snd rz)) ([] : list (bv 5 * Z))) by constructor.
(* A 0x84234 add s3,s3,a0: o + n (the engine writes the sum with its atoms in order, a0 first) *)
assert (UA : forall Ef, (forall n, (n < 512)%nat -> ew Ef n = ew Ex n) ->
  U Ef (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) = e_scr E + Z.of_nat (length acc) + Z.of_nat (length (PjGrammar.utf8 cpt))).
{ intros Ef HW. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (es_U_off Ef Ex 10 0 _ HW ltac:(lia) E10) by lia. rewrite (es_U_off Ef Ex 19 0 _ HW ltac:(lia) E19) by lia.
  unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
(* the one run to A 0x84378 (CUT_CONT): no branch, no write *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x344).
{ apply awr_ok_nil. }
es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr. rename KEPT into MK3.
es_envkeep HS Ex EWf.
es_leaf_regs HS HEx regs ES_REGS ([] : list (bv 5 * Z)) HPN HR.
es_reg0 HS (19%bv : bv 5) R19'. es_reg0 HS (21%bv : bv 5) R21'.
es_reg0 HS (13%bv : bv 5) R13'. es_reg0 HS (14%bv : bv 5) R14'. es_reg0 HS (15%bv : bv 5) R15'.
es_reg0 HS (16%bv : bv 5) R16'.
pmkst HS. es_pc_to 0x344.
apply (HCT lyc Sc Hpc _ _ _ k (acc ++ PjGrammar.utf8 cpt) HP).
- apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
    [intros a [] | exact MK3 | exact HR | exact HPM].
- unfold ESK. rewrite R13', R14', R15', R16'. cbn [sv_denot].
  repeat split; first [reflexivity | unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity].
- exact HEG.
- apply (es_garr8_kept (w_H (e_W E)) memc); [|exact GA]. intros a Ha. rewrite length_app in Ha. apply MK3; [lia | tauto].
- rewrite R19'. lazymatch type of EWf with forall n, _ -> ew ?Ef n = _ =>
    rewrite <- (Z_to_bv_bv_unsigned _ (sv_denot Ef (SAlu ALU_ADD (SOff 10 0) (SOff 19 0))));
    fold (U Ef (SAlu ALU_ADD (SOff 10 0) (SOff 19 0))) end.
  rewrite (UA _ EWf). rewrite length_app, Nat2Z.inj_add. unfold w64. f_equal. lia.
- rewrite R21', es_den0. rewrite ?(EWf 21%nat ltac:(lia)). rewrite E21. reflexivity.
Qed.

Lemma es_cut_utf8 : forall E p, CUT_UTF8R B ARx SK E p -> CUT_UTF8 B ARx SK E p.
Proof.
intros E p HU8R. unfold CUT_UTF8. intros lyc Sc Hpc regs memc mdc k acc cpt HP HB HEG Hcp GA V36 R19 R21.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC0 & HC8 & HC16 & HC24 & R2 & R8 & R18 & R22 &
  R23 & R24 & R25 & R26 & R27 & R3 & R4 & HSc & HMN).
pose proof HEG as (HG1 & HG2 & HG3).
rewrite length_app in HG2.
destruct (es_cut_mem B ARx SK LAWS E lyc Sc Hpc regs memc mdc k HHEAD HP HB) as
  (_ & HRAs & _ & _ & (b & m & Hbm' & Hbs & Hsm & Hhd)).
unfold es_SP in *.
assert (Hn14 : (1 <= length (PjGrammar.utf8 cpt) <= 4)%nat).
{ unfold PjGrammar.utf8. destruct (Z.ltb_spec cpt 128); [cbn; lia|]. destruct (Z.ltb_spec cpt 2048); [cbn; lia|].
  destruct (Z.ltb_spec cpt 65536); cbn; lia. }
set (n := Z.of_nat (length (PjGrammar.utf8 cpt))) in *.
remember (es_xE regs (e_regs E) [w64 cpt]) as Ex eqn:HEx.
assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
assert (E19 : ew Ex 19 = Z_to_bv 64 (e_scr E + Z.of_nat (length acc)))
  by (rewrite HEx, (es_xE_reg _ _ _ 19%bv 19) by reflexivity; exact R19).
assert (E21 : ew Ex 21 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 21%bv 21) by reflexivity; exact R21).
assert (E45 : ew Ex 45 = Z_to_bv 64 cpt) by (rewrite HEx, (es_xE_extra _ _ _ 0) by lia; reflexivity).
assert (U2 : bv_unsigned (ew Ex 2) = es_sp E - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi rsegs VAL Ex ss_u8
  (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x1f4))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_u8.
  apply (pa_entry_st_ok_full (fx := fx) (L := A_prog_listing) (PI := PI_prog_A)).
  - rewrite HEx. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, ES_RC. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs Ex _ (es_sp E - 144) 36 4 (SOff 45 0) cpt);
      [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact V36].
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E19, E21, E45, !unsigned_lit_small by lia. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold ES_CEIL. repeat split; lia. }
assert (SHOK : sh_ok rsegs (SOff 23 0) [] Ex (rdW (e_W E) memc)) by apply Forall_nil.
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS _ (es_plaw E)).
assert (HPM : es_P E memc) by exact HMN.
unfold cfg_at, w64. rewrite es_pc_eq.
(* A 0x84228 .. 0x84230: the run to the call *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
{ es_awr ltac:(fun a Ha => fail). }
es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr.
lazymatch type of HS with st_ok _ ?Ef _ (restrict _ ?m) => rename m into msC;
  assert (EWc : forall n, (n < 512)%nat -> ew Ef n = ew Ex n)
    by (intros n0 Hn0; repeat (rewrite ew_ewset_other by lia); reflexivity);
  assert (HEIc : img_env VAL A_LIM Ef) by assumption end.
lazymatch goal with KEPT : forall a, _ -> _ -> aview ?sg ?H ?m' a = aview _ _ ?m a |- _ =>
  assert (MK2 : forall a, 0 <= a < 2 ^ 64 -> aview sg H m' a = aview sg H memc a)
    by (intros a Ha; exact (KEPT a Ha ltac:(tauto))) end.
clear KEPT.
es_reg_st HS (1%bv : bv 5) R1. rewrite (codeptr_val _ _ HEIc) in R1.
es_reg_st HS (2%bv : bv 5) R2'. es_reg_st HS (10%bv : bv 5) R10'. es_reg_st HS (11%bv : bv 5) R11'.
rewrite es_den0 in R2'. try rewrite (EWc 2%nat ltac:(lia)) in R2'. rewrite E2 in R2'.
rewrite es_den0 in R10'. try rewrite (EWc 19%nat ltac:(lia)) in R10'. rewrite E19 in R10'.
rewrite es_den0 in R11'. try rewrite (EWc 45%nat ltac:(lia)) in R11'. rewrite E45 in R11'.
assert (HKR : forall r, In r ES_REGS -> getr (ms_regs msC) r = getr regs r).
{ pose proof (regs_kept_of_st_ok _ _ _ _ regs _ ES_REGS HS ltac:(es_agree_tac HEx) ltac:(vm_compute; reflexivity)) as H0.
  cbn [ms_regs restrict] in H0. exact H0. }
assert (HKR3 : forall r, In r [19; 21]%bv -> getr (ms_regs msC) r = getr regs r).
{ pose proof (regs_kept_of_st_ok _ _ _ _ regs _ [19; 21]%bv HS ltac:(es_agree_tac HEx)
    ltac:(vm_compute; reflexivity)) as H0. cbn [ms_regs restrict] in H0. exact H0. }
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARc Hbm') as (B1 & B2 & B3 & Bapp & Bpres & _).
assert (Hreq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (HSP : spZ (ms_regs msC) = es_sp E - 144) by (unfold spZ; rewrite R2'; apply unsigned_lit_small; lia).
pmkst HS.
(* the callee: ex_utf8's run form at o = s3, cp = 36(sp) *)
eapply SRr_bind.
{ apply (HUTF8 (STK_ex_string + e_d E) (es_sp E + e_d E) (es_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E)
    (e_md E) [] lyc Sc Hpc (e_W E) (ms_mem msC) _ k (ms_regs msC) (e_scr E + Z.of_nat (length acc)) cpt HJ).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1. apply Z.leb_le. vm_compute. reflexivity.
  - exact R10'.
  - exact R11'.
  - lia.
  - rewrite HSP. lia.
  - rewrite HSP, es_stk_val. unfold EXU_STK. lia.
  - rewrite HSP. lia.
  - intros x Hx. rewrite HSP in Hx. apply HJpres. rewrite es_stk_val. unfold EXU_STK in Hx. lia.
  - lia.
  - fold n. lia.
  - fold n. apply (es_ra_kept (w_H (e_W E)) memc); [intros x Hx; apply MK2; unfold shadow_of_addr, SHADOW_OFF; lia|].
    intros x Hx. apply HRAs. lia.
  - fold n. intros x Hx. split.
    + apply (es_awr_scr E _ _ _ _ b m x Hbm' Hbs Hsm). lia.
    + apply Bpres. lia.
  - right. fold n. rewrite HSP. unfold EXU_STK. lia. }
(* the return A 0x84234 (CUT_UTF8R) *)
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & HAR' & HMNk & HKP & HRES & HGU).
rewrite R1. es_pc_to 0x200.
assert (HK' : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((es_sp E - 144 - 16 <= a < es_sp E - 144) \/ (e_scr E + Z.of_nat (length acc) <= a < e_scr E + Z.of_nat (length acc) + n)) ->
  aview rsegs (w_H (e_W E)) mem' a = aview rsegs (w_H (e_W E)) memc a).
{ intros a Ha Hn. etransitivity; [|exact (MK2 a Ha)]. apply HKP; [exact Ha | rewrite HSP; unfold EXU_STK; tauto | fold n; tauto]. }
assert (HR' : forall r, In r ES_REGS -> getr regs' r = getr regs r).
{ intros r Hr. rewrite (es_aregs_ES _ _ HAR' r Hr). exact (HKR r Hr). }
assert (HR3 : forall r, In r [19; 21]%bv -> getr regs' r = getr regs r).
{ intros r Hr. rewrite (es_aregs_l [19; 21]%bv _ _ ltac:(vm_compute; reflexivity) HAR' r Hr). exact (HKR3 r Hr). }
apply (HU8R lyc Sc Hpc regs' mem' md' k acc cpt HP).
- apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k regs' mem' md'
    (fun a => (es_sp E - 144 - 16 <= a < es_sp E - 144) \/
              (e_scr E + Z.of_nat (length acc) <= a < e_scr E + Z.of_nat (length acc) + n))
    HHEAD HP HB HJ').
  + intros a [Ha | Ha]; [right; left; unfold es_SP; lia | left; unfold es_len in *; lia].
  + exact HK'.
  + exact HR'.
  + intros H0. exact (HMNk (HPM H0)).
- exact HEG.
- apply es_garr8_app; [|exact HGU].
  apply (es_garr8_kept (w_H (e_W E)) memc); [|exact GA]. intros a Ha. apply HK'; [lia|]. lia.
- exact HRES.
- rewrite (HR3 19%bv ltac:(cbn; tauto)). exact R19.
- rewrite (HR3 21%bv ltac:(cbn; tauto)). exact R21.
Qed.
End c.
