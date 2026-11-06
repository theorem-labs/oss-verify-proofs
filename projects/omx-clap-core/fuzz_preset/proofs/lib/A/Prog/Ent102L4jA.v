(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102L4jA.v, with its module paths changed; 72 of its 145 lines of code are new or changed and 8 lines of the source are left out. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetReqAt PresetRun PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog Ent102PLA PRH_Base Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Ent102PosA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Ent102CallA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma l4j_slot : plookup (@pl_tpi _ PL_102_A) 756 = Some (PW 0xed1ff06f).
Proof. vm_compute. reflexivity. Qed.

Lemma l4j_decode : decode_any (Z_to_bv 32 0xed1ff06f) = Some (Jal 0 (Z_to_bv 21 (-304)), 4%Z).
Proof. vm_refl_bv. Qed.

Lemma l4j_imm : bv_signed (Z_to_bv 21 (-304)) = -304.
Proof. vm_compute. reflexivity. Qed.

Lemma l4j_firstn : forall (A : Type) (l c : list A) k, firstn (length l + k) (l ++ c) = l ++ firstn k c.
Proof.
intros A l c k. rewrite firstn_app, (firstn_all2 l) by lia.
replace (length l + k - length l)%nat with k by lia. reflexivity.
Qed.

Section L4j. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
Variable ec_ccut : ecx -> nat -> Z.
Variable ec_lcut : ecx -> nat -> Z.

#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp A_prog_listing PA B).
#[local] Notation ECX := (@ecx rc A_prog_listing PA).

Lemma l4j_tail : forall (E : ECX) trp,
  ec_ranout E trp = false -> fst (PjGrammar.jr_run (e_sm E) (e_x E) []) = None ->
  firstn (length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rej E)) (ec_call_evs E trp) = ec_call_evs E trp.
Proof.
intros E trp Hr HR.
destruct (Z.le_gt_cases (Z.of_nat (length (e_x E))) PresetReqAt.MAXB) as [Hn|Hn].
- assert (Heq : ec_call_evs E trp = ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rej E).
  { rewrite (Ent102PosA.ec_call_evs_ranout_false rc A_prog_listing PA E trp Hn Hr). f_equal.
    unfold PresetRun.call_rest, PresetRun.call_tail, ec_pn, ec_sc, ec_rej. cbv zeta. rewrite HR. reflexivity. }
  rewrite Heq. apply firstn_all.
- destruct trp as [[o1 o2] o0]. cbn [ec_call_evs]. unfold PresetRun.call_evs. cbv zeta.
  replace (PresetReqAt.MAXB <? Z.of_nat (length (e_x E))) with true by (symmetry; apply Z.ltb_lt; exact Hn).
  apply firstn_nil.
Qed.

Lemma l4j_pos : forall (E : ECX) trp H0 hist St,
  e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)) ->
  ec_ranout E trp = false -> fst (PjGrammar.jr_run (e_sm E) (e_x E) []) = None ->
  PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [trp])
    (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rej E)) H0 hist St ->
  PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [trp]) (e_i0 E + length (ec_call_evs E trp)) H0 hist St.
Proof.
intros E trp H0 hist St Hi0 Hr HR H.
assert (Ehr : PresetRun.hruns (e_sm E) (e_x E) (e_os E ++ [trp]) =
  PresetRun.hruns (e_sm E) (e_x E) (e_os E) ++ ec_call_evs E trp).
{ destruct trp as [[o1 o2] o0]. exact (Ent102PosA.ec_hruns_snoc _ _ _ o1 o2 o0). }
unfold PresetRoomPos.iface_room_pos in H |- *. rewrite Ehr, Hi0, l4j_firstn in H |- *.
rewrite firstn_all. rewrite (l4j_tail E trp Hr HR) in H. exact H.
Qed.

Lemma l4j_fetch : fetch_word SEGS (Z_to_bv 64 (BASE + 756)) = Some (Z_to_bv 32 0xed1ff06f).
Proof.
pose proof l4j_slot as Hpl. rewrite <- (@pl_tpi_eq _ PL_102_A) in Hpl.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma A_prog_listing pa_cert _ _ Hpl) as (Hck & _ & _).
unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (BASE + 756)) as [wz|] eqn:Hl; [|discriminate Hck].
apply Z.eqb_eq in Hck. subst wz.
exact (pa_fetch_ok _ _ Hl).
Qed.

Theorem seg_L4j_A :
  @seg_L4j_stmt fx rc ci cp PI RL A_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
unfold seg_L4j_stmt, ec_laneR.
intros E fk HYP W c Hcut.
(* a no-call lane: the world does not move, so the plain SRr proof lifts to SRr' (YA0nH.SRr_SRr'); both cuts carry
   their journal at wle' (cut_crs0, cut_exitR WLE') *)
apply (SRr_SRr' SEGS (@YGcfRehidePost.RZ_cf rc)).
assert (HCOK : ec_ccut_ok ec_ccut) by (eapply ech_ccut_ok; exact HYP).
assert (HLOK : ec_lcut_ok ec_lcut) by (eapply ech_lcut_ok; exact HYP).
destruct Hcut
  as (ly & S & Hp & regs & mem & md & own & peak & cnt & k & trp & Hat & Hinv & HHp & Hro & HCC & HLC & Hrkd
      & Hfrm & Hnb & HR).
destruct Hat as (fy & Hfrm0 & Hkept & Hc). subst c.
assert (Hi0 : e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E))).
{ pose proof Hinv as Hpre. eapply ec_inv_preR in Hpre. unfold ec_pre in Hpre. ec_conj_pick Hpre. }
assert (LAWS : AR_laws_x SEGS B ARc cf_head) by exact (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)).
assert (Htgt : btgt (Z_to_bv 64 (BASE + 756)) (bv_signed (Z_to_bv 21 (-304))) = w64 (@EC_EXIT rc A_prog_listing PA)).
{ rewrite l4j_imm, YCbn.btgt_lit. unfold w64, EC_EXIT, EC_BASE. f_equal. lia. }
unfold cfg_at.
change (w64 (@EC_AR_CRS0 rc A_prog_listing PA)) with (Z_to_bv 64 (BASE + 756)).
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  exact (step_jal_x0 SEGS regs _ _ _ _ _ l4j_fetch eq_refl l4j_decode).
- intros md' Hsame. rewrite (same_but_materialized_wvb md md' Hsame).
  cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict. rewrite Htgt.
  apply SRr_ret.
  exists ly, S, Hp, regs, mem, (with_vm_backing (m_vm_lazy md) (m_vm_materialized md') md), own, peak, cnt, 0, k,
    trp.
  split; [exists fy; split; [exact Hfrm0|]; split; [exact Hkept | reflexivity]|].
  split.
  { (* the budgeted journal across this no-call slot: ec_inv_wk_grow materializes the model and grows the spent
       budget ec_wk_crs0 (10) to ec_wk_exit (76); the room position is moved by l4j_pos; the rest is the cut's own *)
    unfold ec_invR in Hinv |- *. ec_conj_split Hinv.
    repeat lazymatch goal with |- _ /\ _ => split end.
    all: first
      [ assumption
      | lazymatch goal with
        | Hj : exists WS, _ /\ YCbqGwild.wbudget [] _ WS |- exists WS, _ /\ YCbqGwild.wbudget [] _ WS =>
          let HJ := fresh "HJ" in let Hb := fresh "Hb" in
          destruct Hj as (? & HJ & Hb);
          eapply ec_inv_wk_growR; [exact LAWS | exact HJ | exact Hb | apply Nat.leb_le; vm_compute; reflexivity]
        | Hq : exists hist, PresetRoomPos.iface_room_pos _ _ _ _ _ hist _ |- exists hist, _ =>
          let hist := fresh "hist" in let Hh := fresh "Hh" in
          destruct Hq as (hist & Hh); exists hist; exact (l4j_pos E trp _ hist S Hi0 Hro HR Hh)
        end ]. }
  split; [exact HHp|].
  split; [pose proof (proj2 (HCOK E 5%nat 11%nat) ltac:(lia)); lia|].
  split; [pose proof (proj2 (HLOK E 5%nat 11%nat) ltac:(lia)); lia|].
  split; [exact (proj1 Hrkd) | exact Hfrm].
Qed.

End L4j.

Print Assumptions seg_L4j_A.
About seg_L4j_A.
