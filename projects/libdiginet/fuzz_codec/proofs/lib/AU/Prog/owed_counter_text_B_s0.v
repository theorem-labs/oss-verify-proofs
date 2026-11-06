(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v:26-243 (the harness entry
   segment, tfib_lib_A_seg) at c8557374ad2e for fuzz_knock's ASan image (fuzz_knock.asan, sha256
   61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118), and the S0/S1 boundary state from the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACf7.v:27-28 (ss_A2). rule 24: no function proved (a port of the released
   cgif_file_fuzzer harness walk structure). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/A/APgMain0.v, with its module paths and module names changed; 210 of its 241 lines of code are new or changed and 275 lines of the source are left out. *)
(* Segment S0 of owed_counter_text's walk in image B (fuzz_codec.asan-ubsan 0x84474): oc_seg_S0 of
   owed_counter_text_B_inv.v, from parts a (entry -> the frame request) and b (-> __asan_memset's return) and the
   last part here, 0x845b8 .. the loop-1 head 0x845d4:
   s3 = 0, s11 = ~(F + 64), s2 = F + 32, 56(s1) := ~(F + 32), s6 = q - 1, s8 = 46: one plain run. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text codec_owe.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU owed_counter_text_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_s0_a owed_counter_text_B_s0_b.
(* DgnLib has another `st_ok`: take YP0l's back. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* not x (xori x, -1) *)
Lemma oc_lxor_ones : forall v, 0 <= v < 2 ^ 64 -> Z.lxor v (Z.ones 64) = Z.ones 64 - v.
Proof.
intros v Hv.
assert (Hd : Z.land v (Z.lxor v (Z.ones 64)) = 0).
{ apply Z.bits_inj_0. intros i. rewrite Z.land_spec, Z.lxor_spec.
  destruct (Z_lt_le_dec i 0) as [Hn|Hn]; [rewrite Z.testbit_neg_r by exact Hn; reflexivity|].
  destruct (Z_lt_le_dec i 64) as [Hi|Hi].
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit v i); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite <- (Z.mod_small v (2 ^ 64)) by exact Hv.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
pose proof (Z.add_nocarry_lxor _ _ Hd) as Hs. rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in Hs. lia.
Qed.
Lemma oc_D_not : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = Z_to_bv 64 (onot v).
Proof.
intros E n v H Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v H Hv), U_SLit.
replace (zcanon (-1)) with (Z.ones 64) by reflexivity.
rewrite oc_lxor_ones by exact Hv. rewrite Z.ones_equiv, zcanon_id by (unfold M64; lia). unfold onot. lia.
Qed.

Lemma oc_A_not : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  alu64 ALU_XOR (ew E n) (Z_to_bv 64 (-1)) = Z_to_bv 64 (onot v).
Proof.
intros E n v H Hv. rewrite <- (oc_D_not E n v H Hv).
change (Z_to_bv 64 (-1)) with (sv_denot E (SLit (-1))). rewrite <- (sv_denot_SOff0 E n). reflexivity.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variables (B : asyms) (MT : ameter_ops) (RLO RHI GLYPHA : Z) (ROSTRS : list (Z * Z)).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM1 : astack_malloc_realizes tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis AIS : aintrin_realizes tfibsegs B OSet 0x51f84.

(* 0x845b8 -> the loop-1 head *)
Lemma oc_s0_p3 : forall g W2 c2, oc_pre B g -> oc_s0_r2 B g W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => exists pos, oc_cut B MT g pos PC_L1 (P_L1 g pos (length (og_tb g))) W3 c3).
Proof.
intros [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj] W2 c2 Hpre Hr2.
pose proof (oc_wr_win B _ Hpre) as HWR.
unfold oc_pre in Hpre.
unfold oc_s0_r2, oc_s0_j, oc_saves, og_len, og_sp1, og_sp, og_F, og_FL, oc_wr in Hpre, HWR, Hr2.
cbn [og_STK og_sp0 og_FP og_ly og_S og_W0 og_mem0 og_md0 og_own og_lyc og_Sc og_W og_memc og_mdc og_k og_regs
  og_q og_sg og_dt og_tb og_sj og_dj] in Hpre, HWR, Hr2.
destruct Hpre as (HE & H10 & Hstr & H11 & Hsg & Hsj & Hsjl & H12 & Hdt & Hdj & Hd1 & Hd2 & Hd3 & Hfr8).
destruct Hr2 as (-> & S2 & regs2 & mem2 & md2 & pos & -> & (HJ2 & HK2 & KW2 & Eab & Hfrs2 & Hnin & HSf & Hio & Hflag &
  (V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27) & VSG) & GSH & GDOT &
  VP24 & VP32 & VP40 & VP80 & R2 & R9 & R8 & R3 & R4 & R20 & R21 & R22 & R23 & R26).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_owed_counter_text HE
  ltac:(unfold TB_owed_counter_text, ESTACK; lia)) as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as (HJc & Hra & Hra4 & Hgp & Htp & _ & Hwlo & Hwhi & Hev & Hlive).
pose proof HJc as (HARc & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (TT : TB_owed_counter_text = 4320) by reflexivity. rewrite TT in *.
pose proof Hsg as (Hsg0 & Hsg63 & _).
assert (Hdtb : 0 < dt /\ dt + 1 <= 2 ^ 63) by (destruct Hdt as [((Hx0 & Hx1 & _) & _) | (Hx0 & Hx1 & _)]; lia).
pose proof Hstr as (Hq0 & _ & Hin0 & (_ & Hqn & _ & _ & _ & Hqam & Hqwin)).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & (Hsp0al & _) & _).
assert (HP2 : Permutation (ablocks B lyc S2) (ablocks B lyc Sc)) by (rewrite Eab; apply Permutation_refl).
assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 1 pos HAR2 Hin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil.
destruct (FFL _ _ _ _ _ 1 pos HAR2 Hin) as (_ & _ & _ & (HFL4096 & _ & HFLc)).
pose proof alloc_ceiling_val as Hac.
set (F := frame_addr lyc 1 pos) in *. set (FL := flag_addr lyc 1 pos) in *.
assert (HF0 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HF8 : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
set (sp1 := 32 * ((spZ regs - 192) / 32)) in *.
destruct (sp1_facts (spZ regs - 192) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192) by lia. clear Hsp1r.
(* the start state *)
set (E := Ereg regs2 (cw_extra [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E20 : ew E 20 = Z_to_bv 64 q) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = Z_to_bv 64 (F + 64)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = Z_to_bv 64 (F + 32)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok tfibsegs E (mkSS 0x845b8 sr_atoms [YP09.mkRegion (Some 9%nat) 56 64 56 64 []] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0)] [] []))
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x845b8) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (cw_extra [])) with E.
  - subst E. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable tfibsegs). apply HJpres2. lia.
  - cbn [pairwise_disjoint]. split; exact I.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, E32, unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat split; try lia; try exact Hsp1al. }
clearbody E.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) mem2)) by constructor.
(* 0x845b8 .. 0x845d0: one plain run, stopped at the loop-1 head *)
aj_run_to tfibtbl_lib_ok HS HJ2 0x845d4.
{ lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyv ?ownv =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk s0 fp b0 bc lyv ownv) end.
  repeat first
  [ apply awr_ok_nil
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0)); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |] ]. }
set (Xs := fun a => sp1 + 56 <= a < sp1 + 64).
lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
  assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ Xs a -> aview tfibsegs H m2 a = aview tfibsegs H m1 a);
  [ intros a Ha Hx; apply (oc_kept_of_frame Ef rs H m1 m2 HFr a Ha); intros (r & Hr & Hb); apply Hx; unfold Xs;
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
    repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U9 in Hb; lia | ]);
    destruct Hr
  | ];
  assert (KP : forall a, apresent H m1 a -> apresent H m2 a) by (intros a Hp; exact (apresent_grows _ _ _ a HG Hp));
  clear HFr HG
end.
clear_frames.
assert (HK3 : tcj_kept tfibsegs B 4320 lyc Sc W memc W (ms_mem ms) (spZ regs) (fun a => sg <= a < sg + 8 \/ dt <= a < dt + 1)).
{ apply (cw_kept_step B LAWS 4320 lyc Sc W memc mdc W mem2 (ms_mem ms) (spZ regs) _ Xs ltac:(lia) HARc HK2 KX); [|exact KP].
  intros a Ha. left. unfold Xs in Ha. lia. }
assert (KV : forall a n v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat n -> ~ Xs x) ->
  val_mem tfibsegs (mrestrict (w_H W) mem2) a n v -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) a n v).
{ intros a n v H0 H1 H2 Hv. apply (cw_val_mem_kept (w_H W) (w_H W) mem2 (ms_mem ms) a n v); [|exact Hv].
  intros x Hx. apply KX; [lia | exact (H2 x Hx)]. }
assert (KWa : forall a, (sg <= a < sg + 8 \/ dt <= a < dt + 1) ->
  aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) memc a).
{ intros a Ha. rewrite <- (KW2 a Ha). pose proof (HWR a Ha) as Hw.
  apply KX; [destruct Ha; lia | unfold Xs; lia]. }
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
lazymatch type of RG with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG end.
rreg HS (2%bv : bv 5) G2. rreg HS (3%bv : bv 5) G3. rreg HS (4%bv : bv 5) G4. rreg HS (8%bv : bv 5) G8.
rreg HS (9%bv : bv 5) G9. rreg HS (18%bv : bv 5) G18. rreg HS (19%bv : bv 5) G19. rreg HS (20%bv : bv 5) G20.
rreg HS (21%bv : bv 5) G21. rreg HS (22%bv : bv 5) G22. rreg HS (23%bv : bv 5) G23. rreg HS (24%bv : bv 5) G24.
rreg HS (26%bv : bv 5) G26. rreg HS (27%bv : bv 5) G27.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (AGv : forall n, (n < 33)%nat -> ew Ev n = ew E n) by (intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity) end.
(* the spill of ~(F + 32) at 56(s1) *)
assert (VP56 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp1 + 56) 8 (onot (F + 32))).
{ lazymatch type of RG with region_ok _ ?Ev _ (YP09.mkRegion _ _ _ _ _ [YP09.mkChunk 56 (CVal 8 ?e)]) =>
    eapply (field_of_region Ev _ 9 _ _ _ _ _ _ 56 8%N e _ RG);
    [ rewrite ?(AGv 9%nat) by lia; exact U9 | left; reflexivity
    | rewrite <- (oc_D_not Ev 22 (F + 32)) by (first [rewrite ?(AGv 22%nat) by lia; exact E22 | lia]); reflexivity
    | unfold onot; change (8 * Z.of_N 8) with 64; lia | lia ] end. }
destruct (cw_frame_start MT MTL MTF B lyc Sc S2 HSf) as (_ & HMO).
apply SRr_ret. exists pos.
unfold oc_cut, P_L1, oc_common, oc_arrays, og_len, og_sp1, og_sp, og_F, og_FL, oc_wr.
cbn [og_STK og_sp0 og_FP og_ly og_S og_W0 og_mem0 og_md0 og_own og_lyc og_Sc og_W og_memc og_mdc og_k og_regs
  og_q og_sg og_dt og_tb og_sj og_dj].
fold F FL sp1. rewrite TT.
exists lyc, S2, (ms_regs ms), (ms_mem ms); eexists.
split; [rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) at 1; reflexivity|].
split; [exact HJ2|].
split; [exact HK3|]. split; [exact HP2|]. split; [exact Hnin|].
split; [eapply same_io_trans; [exact Hio | apply cw_same_io_wvb]|].
split; [exact HMO|].
split.
{ split; [rewrite G8, ?(AGv 8%nat ltac:(lia)), (EE 8%nat 8%bv eq_refl); exact R8|].
  split; [rewrite G2, ?(AGv 2%nat ltac:(lia)); exact E2|].
  split; [rewrite G9, ?(AGv 9%nat ltac:(lia)); exact E9|].
  split; [rewrite G3, ?(AGv 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl); exact R3|].
  split; [rewrite G4, ?(AGv 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl); exact R4|].
  split; [rewrite G23, ?(AGv 23%nat ltac:(lia)), (EE 23%nat 23%bv eq_refl); exact R23|].
  split; [rewrite G26, ?(AGv 26%nat ltac:(lia)), (EE 26%nat 26%bv eq_refl); exact R26|].
  split; [rewrite G18, ?(AGv 22%nat ltac:(lia)); exact E22|].
  split; [rewrite G21, ?(AGv 21%nat ltac:(lia)); exact E21|].
  split; [rewrite G24; reflexivity|].
  split; [rewrite G27; unfold w64; apply (oc_A_not _ 21 (F + 64)); [rewrite ?(AGv 21%nat) by lia; exact E21 | lia]|].
  do 13 (split; [apply KV; [lia | cbn; lia | intros x Hx; unfold Xs; cbn in Hx; lia | assumption]|]).
  split; [apply KV; [lia | cbn; lia | intros x Hx; unfold Xs; cbn in Hx; lia | exact VP24]|].
  split; [apply KV; [lia | cbn; lia | intros x Hx; unfold Xs; cbn in Hx; lia | exact VP32]|].
  split; [apply KV; [lia | cbn; lia | intros x Hx; unfold Xs; cbn in Hx; lia | exact VP40]|].
  split; [apply KV; [lia | cbn; lia | intros x Hx; unfold Xs; cbn in Hx; lia | exact VSG]|].
  split; [exact VP56|].
  split; [apply KV; [lia | cbn; lia | intros x Hx; unfold Xs; cbn in Hx; lia | exact VP80]|].
  split.
  { apply rdword_of_val_mem; [|lia].
    apply KV; [lia | cbn; lia | intros x Hx; unfold Xs; cbn in Hx; lia |].
    exact (val_mem_of_rdword tfibsegs _ _ _ _ Hflag). }
  intros j Hj. destruct (GSH j Hj) as (Vj & Rj). split; [|exact Rj].
  cbn [length OC_FRAME_SHADOW] in Hj.
  apply KV; [unfold SB; lia | cbn; unfold SB; lia | intros x Hx; unfold Xs, SB in *; cbn in Hx; lia | exact Vj]. }
exists 0, 0, [], (repeat 0 8).
split; [rewrite G19; reflexivity|].
split; [rewrite G20, ?(AGv 20%nat ltac:(lia)), Z.add_0_r; exact E20|].
split; [lazymatch goal with HS : st_ok ?segs ?Ev ?ss (restrict ?Hh ?msv) |- getr (ms_regs ?msv) ?r = _ =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs Hh Ev ss msv r HS : getr (ms_regs msv) r = sv_denot Ev e) end;
  rewrite denot_lit_U, (U_atom_off _ 20 q (-1)) by (first [rewrite ?(AGv 20%nat) by lia; exact E20 | lia]);
  unfold w64; f_equal; lia|].
split; [lia|]. split; [rewrite Z.sub_0_r, Nat2Z.id; lia|].
split; [cbn [firstn Z.to_nat]; constructor|].
split; [reflexivity|].
split; [split; [exact ct_inv_0|]; split; [repeat constructor; lia|]; split; [reflexivity | constructor]|].
split; [split; [intros i Hi; rewrite nth_repeat; apply KV; [lia | cbn; lia | intros x Hx; unfold Xs; cbn in Hx; lia | exact (GDOT i Hi)]
               | intros i Hi; lia]|].
split.
{ intros j Hj. destruct (Hsj j Hj) as (Vj & Rj). split; [|exact Rj]. rewrite Hsjl in Hj.
  apply (cw_val_mem_kept (w_H W) (w_H W) memc (ms_mem ms) _ 1 _); [|exact Vj].
  intros x Hx. cbn in Hx. apply KWa. left. lia. }
apply (cw_val_mem_kept (w_H W) (w_H W) memc (ms_mem ms) dt 1 dj); [|exact Hdj].
intros x Hx. cbn in Hx. apply KWa. right. lia.
Qed.

(* S0: entry -> the frame request (part a) -> __asan_memset (part b) -> the loop-1 head (above) *)
Theorem oc_s0_holds : oc_seg_S0 B MT RLO RHI GLYPHA ROSTRS.
Proof.
unfold oc_seg_S0. intros g Hpre Hnow.
eapply SRr_bind; [eapply oc_s0_p1; eassumption|]. intros W2 c2 _ H1.
eapply SRr_bind; [eapply oc_s0_p2; eassumption|]. intros W3 c3 _ H2.
exact (oc_s0_p3 g W3 c3 Hpre H2).
Qed.
End s.
