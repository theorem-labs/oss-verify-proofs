(* Segment F of check_text_counter's walk in image B (check_text_counter_B_inv.v), one byte of the inlined fuzz_all over
   the record's bytes [8, 24) at 0x84364: the UBSan check of (sg + 8) + j (0x84364, decided from the facts of a3 and
   a1), the instrumented check of the byte (its shadow entry, the record marked usable), the byte itself 0xa5 (the
   record holds eight digits in front of sixteen 0xa5 bytes), so the abort at 0x84380 is not reached (a2 = 0xa5
   pinned), j + 1, and 0x84388 bne a1,a4: taken back to the head, not taken through `j` to the release 0x8439c. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_l check_text_scribble_B_mi.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_f check_text_scribble_B_m2.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_counter_B_inv check_text_counter_B_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the state at the head: the record's byte 8 + j at atom 33 (the extras put it there), a read-only 0xa5; s8 = SB,
   a2 = 0xa5, a4 = 16 *)
Definition ccf_G : facts :=
  mkFacts [(32%nat, mkAF SB SB 0); (33%nat, mkAF 1 (2 ^ 47 - 2) 0); (11%nat, mkAF 0 15 0);
           (13%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0)] []
    [(SAlu ALU_ADD (SOff 19 0) (SOff 11 0), SOff 33 0)].
Definition ccf_rec : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 165))].
Definition ccf_sr : list sv := sr_set (sr_set (sr_set sr_atoms 24%bv (SOff 32 0)) 12%bv (SLit 165)) 14%bv (SLit 16).

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).

Lemma ccf_state : forall (regs2 : bvmap 5 word) (W2 : world tfibsegs) mem2 c j,
  getr regs2 24 = w64 SB -> getr regs2 12 = w64 165 -> getr regs2 14 = w64 16 -> getr regs2 19 = w64 c ->
  getr regs2 11 = w64 j -> getr regs2 13 = w64 (bnot c) ->
  1 <= c -> c + 16 <= 2 ^ 47 - 1 -> 0 <= j < 16 ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) (c + j) 1 165 ->
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (c + j) 1 -> amem_range (c + j) 1 ->
  st_ok tfibsegs (Ereg regs2 (cw_extra [c + j])) (mkSS CC_FL ccf_sr [ccf_rec] None ccf_G)
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 CC_FL) mem2 (seg_rom tfibsegs))) /\
  sh_ok tfibsegs CW_Bx [mkSHE 33 0 1] (Ereg regs2 (cw_extra [c + j])) (mrestrict (w_H W2) mem2).
Proof.
intros regs2 W2 mem2 c j R24 R12 R14 R19 R11 R13 Hc0 Hc1 Hj V Hra Ham.
set (E := Ereg regs2 (cw_extra [c + j])).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 (c + j)) by (subst E; exact (cw_ew_x regs2 [c + j] 0)).
assert (E19 : ew E 19 = Z_to_bv 64 c) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E11 : ew E 11 = Z_to_bv 64 j) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E13 : ew E 13 = Z_to_bv 64 (bnot c)) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (U32 : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U33 : bv_unsigned (ew E 33) = c + j) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = j) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E 13) = bnot c) by (rewrite E13; apply unsigned_lit_small; unfold bnot; lia).
split.
- rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (cw_extra [c + j])) with E.
  + unfold ccf_sr. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx0; discriminate Hx0 |]
      | intros Hx0; discriminate Hx0 |] | intros Hx0; discriminate Hx0 |].
    all: first [ rewrite R24, sv_denot_SOff0, E32; reflexivity | rewrite R12; reflexivity | rewrite R14; reflexivity ].
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, ccf_rec. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U33. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs E _ (c + j) 0 1 (SLit 165) 165); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact V.
  + apply pairwise_disjoint_of_extents. unfold ccf_rec, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + split; [|split; [exact I|]].
    * unfold ccf_G. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U32, U33, U11, U13. rewrite Z.pow_0_r, !Z.mod_1_r.
      unfold bnot, SB. repeat (split; [repeat split; lia|]). exact I.
    * unfold ccf_G. cbn [f_alias alias_ok]. split; [|exact I].
      rewrite (bsl_den_add E 19 11 c j 0 E19 E11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)), Z.add_0_r.
      cbn [sv_denot]. rewrite U33, Z.add_0_r. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  exact (cw_shent_ra W2 mem2 E 33 (c + j) 1 Hra Ham ltac:(lia) ltac:(lia) ltac:(lia) E33 E32).
Qed.

Variable B : asyms.
Variable MT : ameter_ops.
Variables SEG7TBL GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem cc_f_holds : cc_seg_F B MT SEG7TBL GLYPHA ROSTRS.
Proof.
unfold cc_seg_F. intros g pos fuel W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (j & R11 & R19 & R12 & R13 & R14 & Hj & Hfuel & (s & d & Ls & Grec & Vdt)).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R25 & R22 & R26 & R24 & R21 & R20 & _).
pose proof Hpre as (HE & _ & _ & _ & _ & _ & _ & (Hsg0 & Hsgn & Hsgtd & _ & _ & _ & Hsgam & _) & _).
pose proof (proj1 (proj1 HE)) as HARc.
destruct (cc_stack B SEG7TBL GLYPHA ROSTRS g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (cc_frame B SEG7TBL GLYPHA ROSTRS LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (_ & _ & _ & HF0 & HFc & _).
assert (HF8b : 0 <= cc_F g pos / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
specialize (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as (_ & (Hsgra & _) & _).
assert (Hlen : cc_sg g + 24 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemEnd in Hsgam; lia).
assert (V : val_mem tfibsegs (mrestrict (w_H W2) mem2) (cc_sg g + 8 + j) 1 165).
{ destruct (Grec (Z.to_nat (8 + j))) as (Vb & _); [rewrite length_app, repeat_length, Ls; lia|].
  rewrite app_nth2 in Vb by (rewrite Ls; lia). rewrite Ls in Vb.
  rewrite (bsf_nth_repeat 16 (Z.to_nat (8 + j) - 8) 165 0 ltac:(lia)) in Vb.
  rewrite Z2Nat.id in Vb by lia. replace (cc_sg g + 8 + j) with (cc_sg g + (8 + j)) by lia. exact Vb. }
assert (Hra : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cc_sg g + 8 + j) 1)
  by (intros a Ha; apply Hsgra; lia).
assert (Ham : amem_range (cc_sg g + 8 + j) 1)
  by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia).
destruct (ccf_state regs2 W2 mem2 (cc_sg g + 8) j R24 R12 R14 R19 R11 R13 ltac:(lia) ltac:(lia) Hj V Hra Ham)
  as (HS & SHOK).
remember (Ereg regs2 (cw_extra [cc_sg g + 8 + j])) as E eqn:HEE.
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (EC : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> acallee_saved (Z.of_nat nn) -> ew E nn = getr regs2 r)
  by (intros nn r Hnn _; exact (EE nn r Hnn)).
assert (E11 : ew E 11 = w64 j) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E19 : ew E 19 = w64 (cc_sg g + 8)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E13 : ew E 13 = w64 (bnot (cc_sg g + 8))) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros; assumption).
unfold cfg_at. change (w64 CC_FL) with (Z_to_bv 64 CC_FL).
cw_run_to ltac:(cbn [ss_mem]; repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]) 0x8439c.
ctk_keep cw_kwr_ro.
cw_branch Hc1.
all: lazymatch type of Hc1 with context [sv_denot ?Ev _] =>
  rewrite branch_ne_U, (U_atom_off Ev 11 j 1 ltac:(ewpeel; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc1 by lia end.
- (* back to the head *)
  apply negb_true_iff, Z.eqb_neq in Hc1.
  cw_run_to ltac:(cbn [ss_mem]; repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]) CC_FL.
  ctk_keep cw_kwr_ro.
  apply SRr_ret. cbv beta. left.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
    pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Hms;
    exists ly2, S2, (ms_regs msv), (ms_mem msv), md3;
    split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|]
  end.
  split; [exact HJ|].
  split.
  { apply (cw_kept_step B LAWS TB_check_text_counter (cc_lyc g) (cc_Sc g) (cc_W g) (cc_memc g) (cc_mdc g) W2 mem2
      _ (cc_sp g) (cc_wr g) (fun _ => False));
    [ unfold TB_check_text_counter, ESTACK; lia | exact HARc | exact HK | exact KE | intros a [] | exact KP ]. }
  split; [exact HP|]. split; [exact Hni|].
  split; [eapply same_io_trans; [exact Hio | kio]|].
  split; [exact Hmo|].
  split.
  { apply (cc_common_keep g pos regs2 mem2 W2 _ _ W2 HC);
    [ bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf
    | rv; rewrite ?sv_denot_SOff0; ewpeel; rewrite E32, R24; reflexivity
    | bsm_rf | bsm_rf
    | intros a Ha; apply KE; [unfold SB in *; lia | tauto] ]. }
  exists (j + 1).
  split; [rv; ewpeel; rewrite E11; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|].
  split; [lia|]. split; [lia|].
  exists s, d. split; [exact Ls|]. split.
  + apply (bs_garr8_kept (w_H W2) (w_H W2) mem2 _); [|exact Grec].
    intros x Hx. rewrite length_app, repeat_length, Ls in Hx. apply KE; [lia | tauto].
  + apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 _ _ 1 _); [|exact Vdt].
    intros x Hx. apply KE; [|tauto]. pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hdt0 & Hdtn & _) & _).
    cbn in Hx. lia.
- (* the last byte: to the release *)
  apply negb_false_iff, Z.eqb_eq in Hc1.
  cw_run_to ltac:(cbn [ss_mem]; repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]) CC_R.
  ctk_keep cw_kwr_ro.
  apply SRr_ret. cbv beta. right.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
    pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Hms;
    exists ly2, S2, (ms_regs msv), (ms_mem msv), md3;
    split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|]
  end.
  split; [exact HJ|].
  split.
  { apply (cw_kept_step B LAWS TB_check_text_counter (cc_lyc g) (cc_Sc g) (cc_W g) (cc_memc g) (cc_mdc g) W2 mem2
      _ (cc_sp g) (cc_wr g) (fun _ => False));
    [ unfold TB_check_text_counter, ESTACK; lia | exact HARc | exact HK | exact KE | intros a [] | exact KP ]. }
  split; [exact HP|]. split; [exact Hni|].
  split; [eapply same_io_trans; [exact Hio | kio]|].
  split; [exact Hmo|].
  split.
  { apply (cc_common_keep g pos regs2 mem2 W2 _ _ W2 HC);
    [ bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf
    | rv; rewrite ?sv_denot_SOff0; ewpeel; rewrite E32, R24; reflexivity
    | bsm_rf | bsm_rf
    | intros a Ha; apply KE; [unfold SB in *; lia | tauto] ]. }
  exists s, d. split; [exact Ls|]. split.
  + apply (bs_garr8_kept (w_H W2) (w_H W2) mem2 _); [|exact Grec].
    intros x Hx. rewrite length_app, repeat_length, Ls in Hx. apply KE; [lia | tauto].
  + apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 _ _ 1 _); [|exact Vdt].
    intros x Hx. apply KE; [|tauto]. pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hdt0 & Hdtn & _) & _).
    cbn in Hx. lia.
Qed.
End s.
