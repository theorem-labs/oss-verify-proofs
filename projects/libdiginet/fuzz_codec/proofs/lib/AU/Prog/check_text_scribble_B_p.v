(* Segment P of check_text_scribble's walk in image B (fuzz_codec.asan-ubsan 0x83dbc): bs_seg_P of
   check_text_scribble_B_inv.v, one byte of the pad loop 0x83fc0: the UBSan check of want + o (0x83fc0, decided from
   the facts of a2 and a1), the instrumented check of want[o] (its shadow entry), want[o] := ' ', o + 1, and
   0x83fe0 bne s3,a1: taken back to the head, not taken to the memset 0x83ff4. want[o]'s write window passes the token
   run's check with a fact apart from the shadow band, so the run is written once per zone of the frame. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_base check_text_scribble_B_lst.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the state at the pad loop's head: want[o] writable at atom 35 (the extras put it there), s7 = SB *)
Definition bsp_G (flo fhi : Z) : facts :=
  mkFacts [(32%nat, mkAF SB SB 0); (35%nat, mkAF flo fhi 0); (11%nat, mkAF 0 7 0); (19%nat, mkAF 1 8 0);
           (12%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0)] []
    [(SAlu ALU_ADD (SOff 22 0) (SOff 11 0), SOff 35 0)].
Definition bsp_xs (F o : Z) : list Z := [0; 0; F + 32 + o].

Lemma bsp_rep : forall (w : list Z) n o, 0 <= o < n ->
  w ++ repeat 32 (Z.to_nat (n - o)) = (w ++ [32]) ++ repeat 32 (Z.to_nat (n - (o + 1))).
Proof.
intros w n o Ho. replace (Z.to_nat (n - o)) with (S (Z.to_nat (n - (o + 1)))) by lia. cbn [repeat].
rewrite <- app_assoc. reflexivity.
Qed.

(* the byte the run stored into want[o], the state's one region *)
Ltac bsp_vn Vn :=
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv), U35 : bv_unsigned (ew _ 35) = ?b |- _ =>
    let HR := fresh "HR" in
    pose proof (st_ok_region_nth Ev ssv (restrict Hh msv) 0 _ HS eq_refl) as HR;
    cbn [ms_mem restrict] in HR;
    pose proof (field_of_region_any _ _ 35 b _ 0 1 0 1 0 1%N _ HR ltac:(ewpeel; exact U35) ltac:(left; reflexivity)
      ltac:(cbn; lia)) as Vn;
    clear HR; change (N.to_nat 1) with 1%nat in Vn; rewrite Z.add_0_r in Vn end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).

Lemma bsp_state : forall (regs2 : bvmap 5 word) (W2 : world tfibsegs) mem2 o n F flo fhi,
  getr regs2 23 = w64 SB -> getr regs2 22 = w64 (F + 32) -> getr regs2 11 = w64 o -> getr regs2 19 = w64 n ->
  getr regs2 12 = w64 (bnot (F + 32)) ->
  0 <= o < n -> n <= 8 -> 4096 <= F -> F + 64 <= 2 ^ 47 -> flo <= F + 32 + o <= fhi ->
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (F + 32 + o) 1 -> amem_range (F + 32 + o) 1 ->
  apresent (w_H W2) mem2 (F + 32 + o) ->
  st_ok tfibsegs (Ereg regs2 (cw_extra (bsp_xs F o)))
    (mkSS PC_P (sr_set sr_atoms 23%bv (SOff 32 0)) [bsl_want] None (bsp_G flo fhi))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_P) mem2 (seg_rom tfibsegs))) /\
  sh_ok tfibsegs CW_Bx [mkSHE 35 0 1] (Ereg regs2 (cw_extra (bsp_xs F o))) (mrestrict (w_H W2) mem2).
Proof.
intros regs2 W2 mem2 o n F flo fhi R23 R22 R11 R19 R12 Ho Hn HF0 HF1 Hfw Hra Ham Hpr.
set (E := Ereg regs2 (cw_extra (bsp_xs F o))).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E35 : ew E 35 = Z_to_bv 64 (F + 32 + o)) by (subst E; exact (cw_ew_x regs2 (bsp_xs F o) 2)).
assert (E22 : ew E 22 = Z_to_bv 64 (F + 32)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E11 : ew E 11 = Z_to_bv 64 o) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E12 : ew E 12 = Z_to_bv 64 (bnot (F + 32))) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (U32 : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U35 : bv_unsigned (ew E 35) = F + 32 + o) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = o) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = n) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = bnot (F + 32)) by (rewrite E12; apply unsigned_lit_small; unfold bnot; lia).
split.
- rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (cw_extra (bsp_xs F o))) with E.
  + apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx0; discriminate Hx0 |].
    rewrite R23, sv_denot_SOff0, E32. reflexivity.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, bsl_want. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U35. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros oo Hoo. apply (apresent_writable tfibsegs). replace (F + 32 + o + oo) with (F + 32 + o) by lia. exact Hpr.
  + apply pairwise_disjoint_of_extents. unfold bsl_want, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + split; [|split; [exact I|]].
    * unfold bsp_G. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U32, U35, U11, U19, U12. rewrite Z.pow_0_r, !Z.mod_1_r.
      unfold bnot, SB. repeat (split; [repeat split; lia|]). exact I.
    * unfold bsp_G. cbn [f_alias alias_ok]. split; [|exact I].
      rewrite (bsl_den_add E 22 11 (F + 32) o 0 E22 E11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)), Z.add_0_r.
      cbn [sv_denot]. rewrite U35, Z.add_0_r. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  exact (cw_shent_ra W2 mem2 E 35 (F + 32 + o) 1 Hra Ham ltac:(lia) ltac:(lia) ltac:(lia) E35 E32).
Qed.

Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem bs_p_holds : bs_seg_P B MT.
Proof.
unfold bs_seg_P. intros g pos fuel W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (i & o & w & R11 & R26 & R12 & R13 & R20 & Hi & Ho & Hfuel & Hwl & Hw1 & Hw2 & Hwg).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
destruct (bs_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R18 & R24 & R22 & R23 & R25 & R19 & R21 & _).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _).
assert (Hra : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (bs_F g pos + 32 + o) 1).
{ rewrite <- Z.add_assoc. apply (bs_ra_want (w_H W2) mem2 (bs_F g pos) (32 + o) 1); [| lia | lia | lia | exact Hsh].
  pose proof (Z.div_mod (bs_F g pos) 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (bs_F g pos / 64)) with ((8 * (bs_F g pos / 64)) * 8) by lia. apply Z.mod_mul. lia. }
assert (Ham : amem_range (bs_F g pos + 32 + o) 1)
  by (unfold in_app, amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *; lia).
assert (Hpr : apresent (w_H W2) mem2 (bs_F g pos + 32 + o)) by (apply HFp; lia).
assert (KP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros; assumption).
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 PC_P) with (Z_to_bv 64 PC_P).
unfold in_app in HFapp. destruct HFapp as (_ & [Hz | Hz]).
- (* the frame in the low zone *)
  destruct (bsp_state regs2 W2 mem2 o (bs_n g) (bs_F g pos) 4096 (kLowShadowBeg - 24) R23 R22 R11 R19 R12 ltac:(lia) (proj2 Hn) HF0
    ltac:(lia) ltac:(lia) Hra Ham Hpr) as (HS & SHOK).
  remember (Ereg regs2 (cw_extra (bsp_xs (bs_F g pos) o))) as E eqn:HEE.
  assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
    by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
  assert (E35 : ew E 35 = Z_to_bv 64 (bs_F g pos + 32 + o)) by (subst E; exact (cw_ew_x regs2 (bsp_xs (bs_F g pos) o) 2)).
  assert (U35 : bv_unsigned (ew E 35) = bs_F g pos + 32 + o) by (rewrite E35; apply unsigned_lit_small; lia).
  assert (E11 : ew E 11 = w64 o) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
  assert (E19 : ew E 19 = w64 (bs_n g)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (E26 : ew E 26 = w64 i) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  assert (E12 : ew E 12 = w64 (bnot (bs_F g pos + 32))) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
  assert (E13 : ew E 13 = w64 32) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
  assert (E20 : ew E 20 = w64 (bs_ch g)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (E23 : ew E 32 = getr regs2 23) by (subst E; rewrite cw_ew_SB; exact (eq_sym R23)).
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (a = bs_F g pos + 32 + o) ->
    aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
  cw_run_to bsl_awr 0x83fd8. ctk_keep bsl_kwr.
  cw_run_to bsl_awr 0x83fc0. ctk_keep bsl_kwr.
  cw_branch Hc1.
  all: lazymatch type of Hc1 with context [sv_denot ?Ev _] =>
    rewrite branch_ne_U, (U_atom Ev 19 (bs_n g) ltac:(ewpeel; exact E19) ltac:(lia)),
      (U_atom_off Ev 11 o 1 ltac:(ewpeel; exact E11) ltac:(lia) ltac:(lia)) in Hc1 end.
  + (* o + 1 < n: back to the head *)
    apply negb_true_iff, Z.eqb_neq in Hc1.
    cw_run_to bsl_awr 0x83fc0. ctk_keep bsl_kwr.
    bsp_vn Vn.
    lazymatch type of Vn with context [bv_unsigned (sv_denot ?Ev ?e) mod _] =>
      rewrite (bsl_byte_of Ev e 32 ltac:(apply (U_atom Ev 13 32); [ewpeel; exact E13 | lia]) ltac:(lia)) in Vn end.
    apply SRr_ret. cbv beta. left.
    lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
      apply (bs_cut_close B MT LAWS g pos PC_P (P_P g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
        Hio Hmo HC HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
      | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
      | bs_rfin | bs_rfin
      | intros a Ha Hzv; apply KE; [exact Ha | intros Ha'; apply Hzv; unfold bs_zv; lia] | exact KP | ] end.
    exists i, (o + 1), (w ++ [32]).
    split; [bsl_off E11|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
    split; [exact Hi|]. split; [lia|]. split; [lia|].
    split; [rewrite length_app; cbn [length]; lia|].
    split; [rewrite Hw1; apply bsp_rep; lia|]. split; [exact Hw2|].
    apply (bs_want_snoc (w_H W2) mem2 _ (bs_F g pos) w 32 Hwg).
    -- intros a Ha. apply KE; lia.
    -- replace (bs_F g pos + 32 + Z.of_nat (length w)) with (bs_F g pos + 32 + o) by lia. exact Vn.
    -- lia.
  + (* o + 1 = n: to the memset *)
    apply negb_false_iff, Z.eqb_eq in Hc1.
    cw_run_to bsl_awr 0x83ff4. ctk_keep bsl_kwr.
    bsp_vn Vn.
    lazymatch type of Vn with context [bv_unsigned (sv_denot ?Ev ?e) mod _] =>
      rewrite (bsl_byte_of Ev e 32 ltac:(apply (U_atom Ev 13 32); [ewpeel; exact E13 | lia]) ltac:(lia)) in Vn end.
    apply SRr_ret. cbv beta. right.
    lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
      apply (bs_cut_close B MT LAWS g pos PC_M (P_M g pos) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
        Hio Hmo HC HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
      | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
      | bs_rfin | bs_rfin
      | intros a Ha Hzv; apply KE; [exact Ha | intros Ha'; apply Hzv; unfold bs_zv; lia] | exact KP | ] end.
    split; [rewrite Hw2; bs_rfin|]. split; [bs_rfin|].
    rewrite Hw1, (bsp_rep w (bs_n g) o ltac:(lia)). replace (Z.to_nat (bs_n g - (o + 1))) with 0%nat by lia.
    cbn [repeat]. rewrite app_nil_r.
    apply (bs_want_snoc (w_H W2) mem2 _ (bs_F g pos) w 32 Hwg).
    -- intros a Ha. apply KE; lia.
    -- replace (bs_F g pos + 32 + Z.of_nat (length w)) with (bs_F g pos + 32 + o) by lia. exact Vn.
    -- lia.
- (* the frame in the high zone *)
  destruct (bsp_state regs2 W2 mem2 o (bs_n g) (bs_F g pos) (kHighMemBeg + 32) (2 ^ 47 - 24) R23 R22 R11 R19 R12 ltac:(lia) (proj2 Hn) HF0
    ltac:(lia) ltac:(lia) Hra Ham Hpr) as (HS & SHOK).
  remember (Ereg regs2 (cw_extra (bsp_xs (bs_F g pos) o))) as E eqn:HEE.
  assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
    by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
  assert (E35 : ew E 35 = Z_to_bv 64 (bs_F g pos + 32 + o)) by (subst E; exact (cw_ew_x regs2 (bsp_xs (bs_F g pos) o) 2)).
  assert (U35 : bv_unsigned (ew E 35) = bs_F g pos + 32 + o) by (rewrite E35; apply unsigned_lit_small; lia).
  assert (E11 : ew E 11 = w64 o) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
  assert (E19 : ew E 19 = w64 (bs_n g)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (E26 : ew E 26 = w64 i) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  assert (E12 : ew E 12 = w64 (bnot (bs_F g pos + 32))) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
  assert (E13 : ew E 13 = w64 32) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
  assert (E20 : ew E 20 = w64 (bs_ch g)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (E23 : ew E 32 = getr regs2 23) by (subst E; rewrite cw_ew_SB; exact (eq_sym R23)).
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (a = bs_F g pos + 32 + o) ->
    aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
  cw_run_to bsl_awr 0x83fd8. ctk_keep bsl_kwr.
  cw_run_to bsl_awr 0x83fc0. ctk_keep bsl_kwr.
  cw_branch Hc1.
  all: lazymatch type of Hc1 with context [sv_denot ?Ev _] =>
    rewrite branch_ne_U, (U_atom Ev 19 (bs_n g) ltac:(ewpeel; exact E19) ltac:(lia)),
      (U_atom_off Ev 11 o 1 ltac:(ewpeel; exact E11) ltac:(lia) ltac:(lia)) in Hc1 end.
  + (* o + 1 < n: back to the head *)
    apply negb_true_iff, Z.eqb_neq in Hc1.
    cw_run_to bsl_awr 0x83fc0. ctk_keep bsl_kwr.
    bsp_vn Vn.
    lazymatch type of Vn with context [bv_unsigned (sv_denot ?Ev ?e) mod _] =>
      rewrite (bsl_byte_of Ev e 32 ltac:(apply (U_atom Ev 13 32); [ewpeel; exact E13 | lia]) ltac:(lia)) in Vn end.
    apply SRr_ret. cbv beta. left.
    lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
      apply (bs_cut_close B MT LAWS g pos PC_P (P_P g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
        Hio Hmo HC HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
      | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
      | bs_rfin | bs_rfin
      | intros a Ha Hzv; apply KE; [exact Ha | intros Ha'; apply Hzv; unfold bs_zv; lia] | exact KP | ] end.
    exists i, (o + 1), (w ++ [32]).
    split; [bsl_off E11|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
    split; [exact Hi|]. split; [lia|]. split; [lia|].
    split; [rewrite length_app; cbn [length]; lia|].
    split; [rewrite Hw1; apply bsp_rep; lia|]. split; [exact Hw2|].
    apply (bs_want_snoc (w_H W2) mem2 _ (bs_F g pos) w 32 Hwg).
    -- intros a Ha. apply KE; lia.
    -- replace (bs_F g pos + 32 + Z.of_nat (length w)) with (bs_F g pos + 32 + o) by lia. exact Vn.
    -- lia.
  + (* o + 1 = n: to the memset *)
    apply negb_false_iff, Z.eqb_eq in Hc1.
    cw_run_to bsl_awr 0x83ff4. ctk_keep bsl_kwr.
    bsp_vn Vn.
    lazymatch type of Vn with context [bv_unsigned (sv_denot ?Ev ?e) mod _] =>
      rewrite (bsl_byte_of Ev e 32 ltac:(apply (U_atom Ev 13 32); [ewpeel; exact E13 | lia]) ltac:(lia)) in Vn end.
    apply SRr_ret. cbv beta. right.
    lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
      apply (bs_cut_close B MT LAWS g pos PC_M (P_M g pos) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
        Hio Hmo HC HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
      | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
      | bs_rfin | bs_rfin
      | intros a Ha Hzv; apply KE; [exact Ha | intros Ha'; apply Hzv; unfold bs_zv; lia] | exact KP | ] end.
    split; [rewrite Hw2; bs_rfin|]. split; [bs_rfin|].
    rewrite Hw1, (bsp_rep w (bs_n g) o ltac:(lia)). replace (Z.to_nat (bs_n g - (o + 1))) with 0%nat by lia.
    cbn [repeat]. rewrite app_nil_r.
    apply (bs_want_snoc (w_H W2) mem2 _ (bs_F g pos) w 32 Hwg).
    -- intros a Ha. apply KE; lia.
    -- replace (bs_F g pos + 32 + Z.of_nat (length w)) with (bs_F g pos + 32 + o) by lia. exact Vn.
    -- lia.
Qed.
End s.
