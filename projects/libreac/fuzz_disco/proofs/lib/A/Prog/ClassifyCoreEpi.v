(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 321 of its 354 lines of code are new or changed and 36 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ClassifyCore ClassifyCoreSeg.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition epi_extra (regs : bvmap 5 word) (fl : Z) : list word :=
w64 fl :: map (fun p => getr regs (Z_to_bv 5 (fst p))) cls_spills.

Definition epi_spill_chunks : list YP09.chunk :=
[ YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
  YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
  YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
  YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
  YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
  YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
  YP09.mkChunk (-104) (CVal 8 (SOff 45 0)) ].

Definition epi_regions : smem :=
[ YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
  YP09.mkRegion (Some 27%nat) 0 32 0 32 [];
  YP09.mkRegion (Some 18%nat) 0 8 0 8 [];
  YP09.mkRegion (Some 19%nat) 248 256 248 248 [YP09.mkChunk 248 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 8%nat) (-104) 0 (-104) (-104) epi_spill_chunks ].

Definition epi_facts : facts := mkFacts [ (19%nat, mkAF 1 (2 ^ 47) 0) ] [] [].

Definition ss_epi : sstate := mkSS PC_X sr_atoms epi_regions None epi_facts.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Definition epi_env (regs3 regs : bvmap 5 word) (fl : Z) : env := Eimg (Ereg regs3 (epi_extra regs fl)).

Lemma epi_ew_extra : forall regs3 regs fl j, (j < 13)%nat ->
ew (epi_env regs3 regs fl) (33 + j) = getr regs (Z_to_bv 5 (fst (nth j cls_spills (0, 0)))).
Proof.
intros regs3 regs fl j Hj. unfold epi_env. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra. unfold epi_extra. cbn [nth].
rewrite (nth_indep _ (Z_to_bv 64 0) (getr regs (Z_to_bv 5 (fst (0, 0)))))
by (rewrite length_map; unfold cls_spills; cbn [length]; lia).
apply (map_nth (fun p : Z * Z => getr regs (Z_to_bv 5 (fst p))) cls_spills (0, 0) j).
Qed.

Lemma epi_ew_fl : forall regs3 regs fl, ew (epi_env regs3 regs fl) 32 = w64 fl.
Proof.
intros regs3 regs fl. unfold epi_env. rewrite Eimg_low by (unfold A_TEXT; lia).
replace 32%nat with (32 + 0)%nat by lia. rewrite ew_Ereg_extra. reflexivity.
Qed.

Lemma epi_ew_low : forall regs3 regs fl n (r : bv 5), Z.of_nat n = bv_unsigned r ->
ew (epi_env regs3 regs fl) n = getr regs3 r.
Proof. intros regs3 regs fl n r Hn. unfold epi_env. apply ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma epi_chunk_spill : forall (E : env) m (b : Z) (n : nat) (o v : Z),
bv_unsigned (ew E n) = v -> val_mem SEGS m (b + o) 8 v ->
YP09.chunk_ok SEGS E m b (YP09.mkChunk o (CVal 8 (SOff n 0))).
Proof.
intros E m b n o v Hn Hv.
apply (chunk_ok_val SEGS E m b o 8 (SOff n 0) v).
- cbn [sv_denot]. rewrite Z.add_0_r, Hn. reflexivity.
- rewrite <- Hn. pose proof (bv_unsigned_in_range 64 (ew E n)) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr. cbn [Z.of_N N.mul]. exact Hr.
- cbn [Z.of_N]. lia.
- exact Hv.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis NOW : cls_now_ok B.
Hypothesis KS : cls_kept_step_ok B.

Theorem cls_epi : cls_from_X B.
Proof.
unfold cls_from_X, cls_from. intros cx fpos W3 ly3 S3 regs3 mem3 md3 HPRE HX.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HX as HXc. unfold cls_at_X in HXc.
pose proof (NOW cx fpos _ _ _ _ _ _ _ _ _ _ _ _ _ HPRE HXc) as HN. cbv zeta in HN.
pose proof HXc as HX'. unfold cls_cut in HX'. cbv zeta in HX'.
destruct HX' as (HJ3 & Hfrs3 & Hnin3 & HPerm3 & HFAe & HFLe & HKEPT3 & R2 & R3 & R4 & R8 & R9 &
R18 & R19 & R20 & R27 & HRV & HSPF & HVo & HVf & HVF & HLSv & HSHlen & HSHg & HFLv & HPSv & HOlen & HOg & HLK).
pose proof HPRE as HP. unfold cls_pre in HP. cbv zeta in HP.
destruct HP as (HJ0 & HROD & HRA & HRA4 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hch &
Hal16 & Hbud & Hsp0 & Htop32 & HPrest).
destruct HJ0 as (HAR0 & _ & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & HSTK0 & _ & _).
destruct HSTK0 as (Hsp0al & HSTKnn & Hceil & Hlo & Hhi & H47 & _).
destruct HN as (HFR & HNf & HNu & HNuo & HNo & HNo4096 & HNoceil & HNow & HNlk).
destruct HFR as (HF4096 & HFceil & HFal & HFz2 & HFapp & HFpres & HSHpres & HFL4096 & HFLz2 & HFLceil &
HFLpres & HFLown & HFLnin & HFblk & HFfrm).
assert (ECS : 104 <= CLS_STK).
{ pose proof (Z.le_max_l CLS_OWN_BCMP CLS_VIA_PARSE) as Hm.
  unfold CLS_STK in *. unfold CLS_OWN_BCMP, CLS_FRAME, ESTACK in *. lia. }
set (F := cF cx fpos) in *. set (FL := cFL cx fpos) in *. set (SP := cSP cx) in *.
assert (ESPd : SP = spZ (x_regs cx)) by reflexivity.
assert (HSPlo : alloc_ceiling + 104 <= SP) by (rewrite ESPd; lia).
assert (HSPhi : SP <= 2 ^ 47) by (rewrite ESPd; lia).
assert (HF8lo : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HF8q : 8 * (F / 8) <= F) by (pose proof (Z.mul_div_le F 8 ltac:(lia)); lia).
assert (HF8hi : 8 * (F / 8) + 8 > F) by (pose proof (Z.mul_succ_div_gt F 8 ltac:(lia)); lia).
assert (HSH1 : kLowShadowBeg < SHADOW_OFF + F / 8).
{ unfold kLowShadowBeg, SHADOW_OFF in *. lia. }
assert (HSH2 : SHADOW_OFF + F / 8 + 32 <= kHighMemBeg).
{ unfold kHighMemBeg, SHADOW_OFF in *. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia. }
assert (HFrng : 0 <= F < 2 ^ 64) by lia.
assert (HFLrng : 0 <= FL < 2 ^ 64) by lia.
assert (HSPrng : 0 <= SP < 2 ^ 64) by lia.
assert (HSHrng : 0 <= SHADOW_OFF + F / 8 < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (HEI : img_env VAL A_LIM (epi_env regs3 (x_regs cx) FL))
by (unfold epi_env; apply Eimg_env).
assert (E32 : ew (epi_env regs3 (x_regs cx) FL) 32 = w64 FL) by apply epi_ew_fl.
assert (E33 : ew (epi_env regs3 (x_regs cx) FL) 33 = getr (x_regs cx) (Z_to_bv 5 1))
by (apply (epi_ew_extra regs3 (x_regs cx) FL 0); lia).
assert (E34 : ew (epi_env regs3 (x_regs cx) FL) 34 = getr (x_regs cx) (Z_to_bv 5 8))
by (apply (epi_ew_extra regs3 (x_regs cx) FL 1); lia).
assert (E35 : ew (epi_env regs3 (x_regs cx) FL) 35 = getr (x_regs cx) (Z_to_bv 5 9))
by (apply (epi_ew_extra regs3 (x_regs cx) FL 2); lia).
assert (E36 : ew (epi_env regs3 (x_regs cx) FL) 36 = getr (x_regs cx) (Z_to_bv 5 18))
by (apply (epi_ew_extra regs3 (x_regs cx) FL 3); lia).
assert (E37 : ew (epi_env regs3 (x_regs cx) FL) 37 = getr (x_regs cx) (Z_to_bv 5 19))
by (apply (epi_ew_extra regs3 (x_regs cx) FL 4); lia).
assert (E38 : ew (epi_env regs3 (x_regs cx) FL) 38 = getr (x_regs cx) (Z_to_bv 5 20))
by (apply (epi_ew_extra regs3 (x_regs cx) FL 5); lia).
assert (E39 : ew (epi_env regs3 (x_regs cx) FL) 39 = getr (x_regs cx) (Z_to_bv 5 21))
by (apply (epi_ew_extra regs3 (x_regs cx) FL 6); lia).
assert (E40 : ew (epi_env regs3 (x_regs cx) FL) 40 = getr (x_regs cx) (Z_to_bv 5 22))
by (apply (epi_ew_extra regs3 (x_regs cx) FL 7); lia).
assert (E41 : ew (epi_env regs3 (x_regs cx) FL) 41 = getr (x_regs cx) (Z_to_bv 5 23))
by (apply (epi_ew_extra regs3 (x_regs cx) FL 8); lia).
assert (E42 : ew (epi_env regs3 (x_regs cx) FL) 42 = getr (x_regs cx) (Z_to_bv 5 24))
by (apply (epi_ew_extra regs3 (x_regs cx) FL 9); lia).
assert (E43 : ew (epi_env regs3 (x_regs cx) FL) 43 = getr (x_regs cx) (Z_to_bv 5 25))
by (apply (epi_ew_extra regs3 (x_regs cx) FL 10); lia).
assert (E44 : ew (epi_env regs3 (x_regs cx) FL) 44 = getr (x_regs cx) (Z_to_bv 5 26))
by (apply (epi_ew_extra regs3 (x_regs cx) FL 11); lia).
assert (E45 : ew (epi_env regs3 (x_regs cx) FL) 45 = getr (x_regs cx) (Z_to_bv 5 27))
by (apply (epi_ew_extra regs3 (x_regs cx) FL 12); lia).
assert (E08 : ew (epi_env regs3 (x_regs cx) FL) 8 = getr regs3 8)
by (apply (epi_ew_low regs3 (x_regs cx) FL 8 8); reflexivity).
assert (E03 : ew (epi_env regs3 (x_regs cx) FL) 3 = getr regs3 3)
by (apply (epi_ew_low regs3 (x_regs cx) FL 3 3); reflexivity).
assert (E04 : ew (epi_env regs3 (x_regs cx) FL) 4 = getr regs3 4)
by (apply (epi_ew_low regs3 (x_regs cx) FL 4 4); reflexivity).
assert (E18 : ew (epi_env regs3 (x_regs cx) FL) 18 = getr regs3 18)
by (apply (epi_ew_low regs3 (x_regs cx) FL 18 18); reflexivity).
assert (E19 : ew (epi_env regs3 (x_regs cx) FL) 19 = getr regs3 19)
by (apply (epi_ew_low regs3 (x_regs cx) FL 19 19); reflexivity).
assert (E23 : ew (epi_env regs3 (x_regs cx) FL) 23 = getr regs3 23)
by (apply (epi_ew_low regs3 (x_regs cx) FL 23 23); reflexivity).
assert (E27 : ew (epi_env regs3 (x_regs cx) FL) 27 = getr regs3 27)
by (apply (epi_ew_low regs3 (x_regs cx) FL 27 27); reflexivity).
set (E := epi_env regs3 (x_regs cx) FL) in *.
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U08 : bv_unsigned (ew E 8) = SP) by (rewrite E08, R8; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18, R18; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = F) by (rewrite E19, R19; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF + F / 8)
by (rewrite E27, R27; apply unsigned_lit_small; lia).
assert (SPV : forall r o, In (r, o) cls_spills ->
  val_mem SEGS (mrestrict (w_H W3) mem3) (SP + o) 8 (bv_unsigned (getr (x_regs cx) (Z_to_bv 5 r))))
by (intros r o Hin; exact (proj1 (Forall_forall _ _) HSPF (r, o) Hin)).
assert (HS : st_ok_pi (fx := x_fq cx) SEGS VAL E ss_epi
  (restrict (w_H W3) (mkst (fx := x_fq cx) regs3 (Z_to_bv 64 (BASE + PC_X)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_epi, epi_regions. apply pa_entry_st_ok_full.
  - unfold E, epi_env. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons.
    { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). replace (FL + o) with FL by lia. exact HFLpres. }
    apply Forall_cons.
    { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U27. split; [lia|]. split; [unfold SHADOW_OFF in *; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      replace (SHADOW_OFF + F / 8 + o) with (SHADOW_OFF + F / 8 + o) by lia. apply HSHpres. lia. }
    apply Forall_cons.
    { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U18. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HFpres. lia. }
    apply Forall_cons.
    { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|constructor].
      apply (epi_chunk_spill E (mrestrict (w_H W3) mem3) F 32 248 FL); [exact U32 | exact HFLv]. }
    apply Forall_cons; [|constructor].
    { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U08. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold epi_spill_chunks.
      apply Forall_cons; [eapply epi_chunk_spill; [rewrite E33; reflexivity | apply SPV; cbn; tauto]|].
      apply Forall_cons; [eapply epi_chunk_spill; [rewrite E34; reflexivity | apply SPV; cbn; tauto]|].
      apply Forall_cons; [eapply epi_chunk_spill; [rewrite E35; reflexivity | apply SPV; cbn; tauto]|].
      apply Forall_cons; [eapply epi_chunk_spill; [rewrite E36; reflexivity | apply SPV; cbn; tauto]|].
      apply Forall_cons; [eapply epi_chunk_spill; [rewrite E37; reflexivity | apply SPV; cbn; tauto]|].
      apply Forall_cons; [eapply epi_chunk_spill; [rewrite E38; reflexivity | apply SPV; cbn; tauto]|].
      apply Forall_cons; [eapply epi_chunk_spill; [rewrite E39; reflexivity | apply SPV; cbn; tauto]|].
      apply Forall_cons; [eapply epi_chunk_spill; [rewrite E40; reflexivity | apply SPV; cbn; tauto]|].
      apply Forall_cons; [eapply epi_chunk_spill; [rewrite E41; reflexivity | apply SPV; cbn; tauto]|].
      apply Forall_cons; [eapply epi_chunk_spill; [rewrite E42; reflexivity | apply SPV; cbn; tauto]|].
      apply Forall_cons; [eapply epi_chunk_spill; [rewrite E43; reflexivity | apply SPV; cbn; tauto]|].
      apply Forall_cons; [eapply epi_chunk_spill; [rewrite E44; reflexivity | apply SPV; cbn; tauto]|].
      apply Forall_cons; [eapply epi_chunk_spill; [rewrite E45; reflexivity | apply SPV; cbn; tauto]|].
      constructor. }
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U32, U27, U18, U19, U08.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
    unfold zone2, off_img in HFLz2. repeat split; lia.
  - unfold epi_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, Z.pow_0_r. split; [lia|]. split; [apply Z.mod_1_r | lia]. }
pose proof (aj_flag_store_pi (fx := x_fq cx) B LAWS ML ASF FFL) as RUNF.
assert (HWR : forall a, in_wrange E epi_regions a ->
  a = FL \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 32) \/ (F <= a < F + 8)).
{ intros a (r & Hin & Hr). unfold epi_regions in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  [ rewrite U32 in Hr; left; lia
  | rewrite U27 in Hr; right; left; lia
  | rewrite U18 in Hr; right; right; lia
  | rewrite U19 in Hr; lia
  | rewrite U08 in Hr; lia ]. }
assert (HFB : fs_frame_bytes 2 = 256) by reflexivity.
pose proof HJ3 as HJ3c.
unfold cfg_at.
paj_run_flag_sh RUNF HS HJ3.
- lia.
- intros a Ha. apply HWR in Ha. rewrite HFLe.
  destruct Ha as [-> | [Hsh | Hf]].
  + right. reflexivity.
  + left. unfold awr_byte. right. right. right. unfold in_frames.
    exists 2, fpos. split; [left; reflexivity|].
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite HFAe, HFB.
    change (256 / 8) with 32. exact Hsh.
  + left. unfold awr_byte. right. right. right. unfold in_frames.
    exists 2, fpos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite HFAe, HFB. lia.
- intros msr HSr. rewrite HFLe.
  pose proof (st_ok_pi_region_nth E _ msr 0 _ HSr eq_refl) as HR. cbn [ms_mem] in HR.
  pose proof (field_of_region E (ms_mem msr) 32 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR U32
    ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0.
  rewrite Z.add_0_r in V0. exact V0.
- assert (HKEPT4 : tcls_kept B (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) W3 (ms_mem ms) SP (x_lk cx) (x_o cx) (x_L cx)).
  { eapply (KS cx fpos W3 ly3 S3 mem3 md3 (ms_mem ms) (in_wrange E epi_regions) HPRE (proj1 HJ3c)
      Hfrs3 Hnin3 HPerm3 HFAe HFLe HKEPT3).
    - intros a Ha Hno. apply (aview_kept_out E epi_regions (w_H W3) mem3 (ms_mem ms) HFr a Ha Hno).
    - intros a Ha. exact (apresent_grows (w_H W3) mem3 (ms_mem ms) a HG Ha).
    - intros a Ha. apply HWR in Ha.
      change (cF cx fpos) with F. change (cFL cx fpos) with FL.
      destruct Ha as [-> | [Hsh | Hf]];
      [ right; right; right; right; reflexivity
      | right; right; right; left; exact Hsh
      | right; right; left; lia ]. }
  assert (HMB : forall a, ~ (a = FL) -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 32) ->
    ~ (F <= a < F + 8) -> 0 <= a < 2 ^ 64 ->
    mbyte SEGS (mrestrict (w_H W3) (ms_mem ms)) a = mbyte SEGS (mrestrict (w_H W3) mem3) a).
  { intros a H1 H2 H3 H4. unfold mbyte. rewrite HFr; [reflexivity|].
    rewrite unsigned_lit_small by lia. intros Hin. apply HWR in Hin. destruct Hin as [|[|]]; auto. }
  eapply (paj_ret_at (fx := x_fq cx) (PL := PL_disco) (PI := PI) W3 E _ ms _ (cls_Q B cx) HS eq_refl
    ltac:(vm_compute; reflexivity)).
  intros mat2.
  prreg HS (1%bv : bv 5) P1.
  assert (P1' : getr (ms_regs ms) 1 = getr (x_regs cx) (Z_to_bv 5 1)) by (rewrite P1, E33; reflexivity).
  unfold cls_Q, tcls_post.
  exists (x_fq cx), ly3, (stack_free_state 2 fpos S3), (ms_regs ms), (ms_mem ms). eexists.
  split.
  { rewrite P1'. unfold YK0s.ret_ok in HRA.
    change (getr (x_regs cx) (Z_to_bv 5 1)) with (getr (x_regs cx) 1).
    rewrite HRA. reflexivity. }
  split; [intros kk Hk; reflexivity|].
  split; [left; reflexivity|].
  split.
  { replace (x_k cx + EV_CLS) with (x_k cx) by (unfold EV_CLS; lia).
    apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ3. }
  split.
  { apply aregs_preserved_eqs.
    - prreg HS (2%bv : bv 5) P. rewrite P, E08, R8. unfold w64, SP, cSP, spZ.
      apply Z_to_bv_bv_unsigned.
    - prreg HS (3%bv : bv 5) P. rewrite P, E03. exact R3.
    - prreg HS (4%bv : bv 5) P. rewrite P, E04. exact R4.
    - prreg HS (8%bv : bv 5) P. rewrite P, E34. reflexivity.
    - prreg HS (9%bv : bv 5) P. rewrite P, E35. reflexivity.
    - prreg HS (18%bv : bv 5) P. rewrite P, E36. reflexivity.
    - prreg HS (19%bv : bv 5) P. rewrite P, E37. reflexivity.
    - prreg HS (20%bv : bv 5) P. rewrite P, E38. reflexivity.
    - prreg HS (21%bv : bv 5) P. rewrite P, E39. reflexivity.
    - prreg HS (22%bv : bv 5) P. rewrite P, E40. reflexivity.
    - prreg HS (23%bv : bv 5) P. rewrite P, E41. reflexivity.
    - prreg HS (24%bv : bv 5) P. rewrite P, E42. reflexivity.
    - prreg HS (25%bv : bv 5) P. rewrite P, E43. reflexivity.
    - prreg HS (26%bv : bv 5) P. rewrite P, E44. reflexivity.
    - prreg HS (27%bv : bv 5) P. rewrite P, E45. reflexivity. }
  split.
  { pose proof HJ3 as (_ & _ & _ & _ & _ & Hfrs4 & _). rewrite Hfrs4, Hfrs0. reflexivity. }
  split.
  { assert (Eab : ablocks B ly3 (stack_free_state 2 fpos S3) = ablocks B ly3 S3)
      by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
    rewrite Eab. exact HPerm3. }
  split.
  { prreg HS (10%bv : bv 5) P. rewrite P, E23.
    exact (proj1 (Forall_forall _ _) HRV (23, cRet cx) ltac:(left; reflexivity)). }
  split.
  { apply (garr8_frame SEGS (mrestrict (w_H W3) mem3)); [exact HOg|].
    assert (HOL : Z.of_nat (length (cOut cx)) = 24) by exact (f_equal Z.of_nat HOlen).
    unfold cOut in HOL.
    intros a Ha. unfold cls_bytes in Ha. rewrite length_map, HOL in Ha.
    apply HMB.
    - intros Hae. rewrite Hae in Ha.
      destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3c
        (HNow FL ltac:(lia))) as (Hno & _). exact (Hno HFLown).
    - destruct HNo as ((Ho1 & Ho2 & Ho3 & Ho4 & Ho5) & _ & _ & _).
      unfold kLowShadowBeg, kHighMemBeg in *. lia.
    - destruct HNo as (_ & _ & Hof & _). lia.
    - destruct HNo as ((Ho1 & Ho2 & _) & _). lia. }
  split.
  { intros Lb HLb.
    assert (ECl : cLock cx = Some Lb) by (unfold cLock; exact HLb).
    rewrite ECl in HLK.
    destruct (x_L cx) as [Lb0|] eqn:ELk; rewrite ?ELk in HLK, HNlk; [|destruct HLK].
    destruct HLK as (HLblen & HLbg).
    destruct HNlk as (HLo & HL4096 & HLceil & HLow).
    apply (garr8_frame SEGS (mrestrict (w_H W3) mem3)); [exact HLbg|].
    intros a Ha. unfold cls_bytes in Ha. rewrite length_map, HLblen in Ha. apply HMB.
    - intros Hae. rewrite Hae in Ha.
      destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3c
        (HLow FL ltac:(lia))) as (Hno & _). exact (Hno HFLown).
    - destruct HLo as ((Hl1 & Hl2 & Hl3 & Hl4 & Hl5) & _ & _ & _).
      unfold kLowShadowBeg, kHighMemBeg in *. lia.
    - destruct HLo as (_ & _ & Hlf & _). lia.
    - destruct HLo as ((Hl1 & Hl2 & _) & _). lia. }
  exact HKEPT4.
Qed.

End h.
End f.
End d.
