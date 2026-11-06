(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes
  MmapSim AllocSim FileSim AgentLib ShapeLaws LibWritev RefNodes Hoare RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec ShapeLawsX SumWalkTac Frame FContract.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan SymSlots
  SymPlanSoundA SymPlanSound SymPlanSoundH SymPlanSoundG RefATB RefImgHyps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.
Local Abbreviation cs_ok := (SPSA.cs_ok RSEGS) (only parsing).
Local Abbreviation cfg_of := (SPSA.cfg_of RSEGS) (only parsing).
Local Abbreviation co_know := (SPSA.co_know RSEGS) (only parsing).
Local Abbreviation co_slots := (SPSA.co_slots RSEGS) (only parsing).
Local Abbreviation co_halt := (SPSA.co_halt RSEGS) (only parsing).
Local Abbreviation co_lazy := (SPSA.co_lazy RSEGS) (only parsing).
Local Abbreviation reg_sound := (SPSA.reg_sound RSEGS) (only parsing).
Local Abbreviation reg_lit_sound := (SPSA.reg_lit_sound RSEGS) (only parsing).
Local Abbreviation ret_lit_sound := (SPS.ret_lit_sound RSEGS) (only parsing).

Local Abbreviation rw_okb_sound := (SPS.rw_okb_sound RSEGS H_wview_off_ref) (only parsing).
Local Abbreviation rw_ok_sound := (SPS.rw_ok_sound RSEGS H_wview_off_ref) (only parsing).
Local Abbreviation rw_ok_x_sound := (SPS.rw_ok_x_sound RSEGS H_wview_off_ref) (only parsing).
Local Abbreviation apart_e_sound := (SPS.apart_e_sound RSEGS H_wview_off_ref) (only parsing).
Local Abbreviation apart_x_sound := (SPS.apart_x_sound RSEGS H_wview_off_ref) (only parsing).
Local Abbreviation elo_sound := (SPS.elo_sound RSEGS) (only parsing).
Local Abbreviation ehi_sound := (SPS.ehi_sound RSEGS) (only parsing).
Local Abbreviation havocs_frame := (SymPlanSoundG.havocs_frame RSEGS) (only parsing).
Local Abbreviation kimg_cut_sound := (SymPlanSoundG.kimg_cut_sound RSEGS) (only parsing).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section NX0.
Variable nx0 : N.
Hypothesis nx0_pos : nx0_okP nx0.
Hypothesis FC : F_contract RSEGS FP_src0.
Local Abbreviation after_call_sound := (SPS.after_call_sound RSEGS nx0 nx0_pos) (only parsing).
Local Abbreviation cs_ok_bump1 := (SymPlanSoundG.cs_ok_bump1 RSEGS nx0 nx0_pos) (only parsing).

Lemma w2b8_Z0 : forall E, edenot E (ELit 0) = Z_to_bv 64 0.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_any_overlay : forall n (a : word) zs M,
  rdn RSEGS (fun _ => None) a n = Some zs ->
  exists bs, rdn RSEGS M a n = Some bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros a zs M H.
  - exists []. split; reflexivity.
  - cbn [rdn] in H |- *. destruct (seg_rom RSEGS a) as [b0|] eqn:Hrom; [|discriminate].
    destruct (rdn RSEGS (fun _ => None) (a + 1) n) as [zr|] eqn:Hzr; [|discriminate].
    destruct (IH (a + 1)%bv zr M Hzr) as (bs & Hbs & Hlen). rewrite Hbs.
    destruct (M a) as [b|]; eexists; (split; [reflexivity | cbn; lia]).
Qed.

(* [comment removed for export] *)
Lemma img_errno_4 : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x3670c) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Lemma errno_rdn4 : forall M, exists bs, rdn RSEGS M (Z_to_bv 64 0x3670c) 4 = Some bs /\ length bs = 4%nat.
Proof. intros M. exact (rdn_any_overlay 4 _ _ M img_errno_4). Qed.

Theorem call_F_sound' : F_sound_stmt RSEGS REF_ATB nx0.
Proof.
  unfold F_sound_stmt.
  intros cs cs' E R M model T HC Hpc Hn HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_slots _ _ _ _ _ HC) as HSL.
  unfold call_F in Hn.
  change (t_F_ret REF_ATB) with 0x13d7c%Z in Hn. change (t_tp REF_ATB) with 0x367b0%Z in Hn.
  change (t_F_nmax REF_ATB) with 67108864%Z in Hn. change (t_F_frame REF_ATB) with 132544%Z in Hn.
  change (- (132544))%Z with (-132544)%Z in Hn.
  change (d_prng REF_ATB) with 0x26360%Z in Hn. change (d_errno REF_ATB) with 0x3670c%Z in Hn.
  change (d_mcount REF_ATB) with 0x366d8%Z in Hn. change (d_ro_hi REF_ATB) with 0x2427c%Z in Hn.
  change (d_canary_got REF_ATB) with 0x252f8%Z in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 4) as [tp|] eqn:H4; [|discriminate].
  destruct (ehi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  set (spm := mkAlu ALU_ADD (reg cs 2) (ELit (-132544))) in Hn.
  destruct (split_lit spm) as [qb qk] eqn:Hsq.
  destruct (elo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (ehi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  destruct (elo (kn cs) (reg cs 10)) as [dlo|] eqn:Hdlo; [|discriminate].
  destruct (ehi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  set (v := s_next (c_ss cs)) in Hn. set (cs1 := bump_next cs 1) in Hn.
  set (k0 := kimg_cut (kimg_cut (kn cs) 0x26360 8) 0x3670c 4) in Hn.
  set (k3 := kn_havoc (kn_havoc (kn_havoc k0 qb qk (ELit 132544)) (ELit 0) 0x26360 (ELit 8)) (ELit 0) 0x3670c (ELit 4)) in Hn.
  set (k4 := KWord (SA (ELit 0) 0x3670c) 4 (EVar v) :: k3) in Hn.
  destruct (after_call nx0 cs1 ret (Some (ELit 0)) k4) as [csa|] eqn:Hac; [|discriminate].
  lazymatch type of Hn with Some ?c = Some cs' => assert (Ecs : cs' = c) by congruence end. clear Hn.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hmc]. apply andb_prop in Hcond as [Hcond Hgot].
  apply andb_prop in Hcond as [Hcond Himg]. apply andb_prop in Hcond as [Hcond Hapart].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hrw]. apply andb_prop in Hcond as [Hcond Hfrpos]. apply andb_prop in Hcond as [Hcond Heal].
  apply andb_prop in Hcond as [Hcond Hrd]. apply andb_prop in Hcond as [Hcond Hd63]. apply andb_prop in Hcond as [Hcond Hdlo'].
  apply andb_prop in Hcond as [Hcond Hnmax]. apply andb_prop in Hcond as [Hcond Hn0]. apply andb_prop in Hcond as [Hreq Htpq].
  apply Z.eqb_eq in Hreq. apply Z.eqb_eq in Htpq. apply Z.leb_le in Hn0. apply Z.ltb_lt in Hnmax. apply Z.leb_le in Hdlo'.
  apply Z.ltb_lt in Hd63. apply Z.leb_le in Heal. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  unfold SP.F_SPLO in Hsplo'. unfold SP.F_SPHI in Hsphi'.
  subst ret tp.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R M model 0x13d7c HC Hret) as (R1 & Hrok & _).
  destruct (reg_lit_sound E cs R M model 4 0x367b0 HC ltac:(lia) H4) as [R4 _].
  pose proof (reg_sound E cs R M model 2 HC ltac:(lia)) as R2.
  pose proof (reg_sound E cs R M model 10 HC ltac:(lia)) as R10.
  pose proof (reg_sound E cs R M model 11 HC ltac:(lia)) as R11.
  replace (Z_to_bv 5 1) with (1%bv : bv 5) in R1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 4)) with (4%bv : bv 5) in R4 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in R10 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in R11 by (apply bv_eq; reflexivity).
  set (sp := edenot E (reg cs 2)) in *. set (su := bv_unsigned sp).
  set (data := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 11)) in *.
  pose proof (elo_sound E M (kn cs) _ _ HKN Hsplo) as Hsplo2. fold sp in Hsplo2. fold su in Hsplo2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hsphi) as Hsphi2. fold sp in Hsphi2. fold su in Hsphi2.
  pose proof (elo_sound E M (kn cs) _ _ HKN Hdlo) as Hdlo2. fold data in Hdlo2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hdhi) as Hdhi2. fold data in Hdhi2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hnhi) as Hnhi2. fold nw in Hnhi2.
  pose proof (u64_range sp) as Hspr. fold su in Hspr. pose proof (u64_range nw) as Hnwr. pose proof (u64_range data) as Hdr.
  (* [comment removed for export] *)
  assert (Hspm : edenot E spm = Z_to_bv 64 (su - 132544)).
  { subst spm. rewrite mkAlu_denot. cbn [edenot]. fold sp. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold su. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  pose proof (split_lit_denot E spm qb qk Hsq) as Hsqd. rewrite Hspm in Hsqd.
  destruct (rw_okb_sound E M (kn cs) qb qk 132544 HKN Hrw ltac:(lia)) as (Wst & Wdef & Wimg & W0 & Wnw).
  assert (Hq : (bv_unsigned (edenot E qb) + qk = su - 132544)%Z).
  { apply (f_equal bv_unsigned) in Hsqd. rewrite !u64_lit in Hsqd by lia. lia. }
  rewrite Hq in Wst, Wdef, Wimg.
  (* [comment removed for export] *)
  destruct (ealign_sound RSEGS E M (kn cs) (reg cs 2) HKN) as [Heal0 Hdiv]. fold sp in Hdiv. fold su in Hdiv.
  assert (Hsu16 : su mod 16 = 0).
  { apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdiv].
    exists (2 ^ (ealign (kn cs) (reg cs 2) - 4)). change 16 with (2 ^ 4). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  (* [comment removed for export] *)
  assert (IMGOF : forall lo hi, kimg_covers (kn cs) lo hi = true -> forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None).
  { intros lo hi Hcov. unfold kimg_covers in Hcov. apply existsb_exists in Hcov as (K & HinK & HKb).
    destruct K as [| | |ilo ihi| | | |]; try discriminate. apply andb_prop in HKb as [Hil Hih].
    apply Z.leb_le in Hil. apply Z.leb_le in Hih.
    pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKi. cbn [kentry_ok] in HKi. destruct HKi as (_ & _ & Hnone).
    intros i Hi. apply Hnone. lia. }
  assert (PR : forall lo hi, kimg_covers (kn cs) lo hi = true -> 0 <= lo -> hi <= 2 ^ 64 -> pristine M lo hi).
  { intros lo hi Hcov Hlo Hhi a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (IMGOF lo hi Hcov). exact Ha. }
  (* [comment removed for export] *)
  assert (RD : forall i, 0 <= i < bv_unsigned nw -> exists b, rdn RSEGS M (Z_to_bv 64 (bv_unsigned data + i)) 1 = Some [b]).
  { intros i Hi.
    assert (DEF : M (Z_to_bv 64 (bv_unsigned data + i)) <> None).
    { apply Bool.orb_prop in Hrd as [Hrd|Hrd].
      - apply Bool.orb_prop in Hrd as [Hz|Hrd].
        + apply Z.eqb_eq in Hz. exfalso. lia.
        + destruct (rw_ok_sound E M (kn cs) (reg cs 10) nhi HKN Hrd ltac:(lia)) as (_ & Ddef & _). fold data in Ddef.
          apply Ddef. lia.
      - destruct (rw_ok_x_sound E M (kn cs) (reg cs 10) (reg cs 11) HKN Hrd) as (_ & Ddef & _). fold data in Ddef.
        apply Ddef. unfold elenZ. fold nw. lia. }
    cbn [rdn]. destruct (M (Z_to_bv 64 (bv_unsigned data + i))) as [b|] eqn:Eb; [|exfalso; apply DEF; reflexivity].
    exists b. reflexivity. }
  (* [comment removed for export] *)
  assert (APART : bv_unsigned data + bv_unsigned nw <= su - fp_frame FP_src0 \/ su <= bv_unsigned data).
  { cbn [fp_frame FP_src0].
    apply Bool.orb_prop in Hapart as [Hapart|Hap4].
    1: apply Bool.orb_prop in Hapart as [Hapart|Hap3].
    1: apply Bool.orb_prop in Hapart as [Hap1|Hap2].
    - apply Z.leb_le in Hap1. lia.
    - apply Z.leb_le in Hap2. lia.
    - apply andb_prop in Hap3 as [Hap3 Hape]. apply andb_prop in Hap3 as [Hpos Hrwd]. apply Z.ltb_lt in Hpos.
      assert (Hrws : rw_ok (kn cs) spm 132544 = true).
      { unfold rw_ok. rewrite Hsq. exact Hrw. }
      destruct (apart_e_sound E M (kn cs) (reg cs 10) nhi spm 132544 HKN Hape Hrwd Hrws Hpos ltac:(lia)) as [Hd|Hd];
        fold data in Hd; rewrite Hspm, u64_lit in Hd by lia; lia.
    - apply andb_prop in Hap4 as [Hap4 Hapx]. apply andb_prop in Hap4 as [Hrx1 Hrx2].
      destruct (apart_x_sound E M (kn cs) spm (ELit 132544) (reg cs 10) (reg cs 11) HKN Hapx Hrx2 Hrx1) as [Hd|Hd];
        fold data nw in Hd; rewrite Hspm, u64_lit in Hd by lia; unfold elenZ in Hd; cbn [edenot] in Hd;
        fold nw in Hd; rewrite ?u64_lit in Hd by lia; lia. }
  (* [comment removed for export] *)
  destruct (FC R M (seg_rom RSEGS) sp data (bv_unsigned nw) R1 ltac:(exact R2) R4 ltac:(exact R10)
              ltac:(rewrite Z_to_bv_bv_unsigned; exact R11) ltac:(cbn [fp_nmax FP_src0]; lia)
              ltac:(lia) ltac:(lia) Hsu16 ltac:(unfold FContract.F_SPLO, FContract.F_SPHI; lia)
              APART
              RD
              ltac:(cbn [fp_frame FP_src0]; intros a Ha;
                    replace a with (Z_to_bv 64 (su - 132544 + (bv_unsigned a - (su - 132544))))
                      by (apply bv_eq; rewrite u64_lit by (pose proof (u64_range a); lia); lia);
                    eapply (store_ok_sub RSEGS M (Z_to_bv 64 (su - 132544)) _ (Z.to_nat 132544) 1%nat);
                      rewrite ?u64_lit by lia; rewrite ?Z2Nat.id by lia; try lia; exact Wst)
              ltac:(apply (PR 0x10000 0x2427c Himg); lia)
              ltac:(apply (PR 0x252f8 (0x252f8 + 8) Hgot); lia)
              ltac:(apply (PR 0x366d8 (0x366d8 + 8) Hmc); lia))
    as (R' & M' & Hms & Hkeeps & Ha0 & Hframe).
  (* [comment removed for export] *)
  unfold cfg_of. rewrite Hpc. change (t_F REF_ATB) with (fp_entry FP_src0).
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
  change (fp_ret FP_src0) with 0x13d7c%Z.
  pose proof Hfresh as Hfresh0.
  unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh' Hnx0]. apply N.leb_le in Hnx0.
  (* [comment removed for export] *)
  destruct (errno_rdn4 M') as (ebs & Hebs & Hebl).
  set (ew := Z_to_bv 64 (bytes_le_to_Z ebs)).
  set (E1 := ext1 E v ew).
  pose proof (cs_ok_bump1 E cs R M model ew HC Hfresh0) as HC1. fold v in HC1. fold E1 in HC1. fold cs1 in HC1.
  pose proof (co_know _ _ _ _ _ HC1) as HKN1. pose proof (co_slots _ _ _ _ _ HC1) as HSL1.
  change (s_know (c_ss cs1)) with (kn cs) in HKN1. change (c_slots cs1) with (c_slots cs) in HSL1.
  pose proof (reg_sound E1 cs1 R M model 2 HC1 ltac:(lia)) as R2'.
  replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2' by (apply bv_eq; reflexivity).
  change (reg cs1 2) with (reg cs 2) in R2'. rewrite R2 in R2'. (* [comment removed for export] *)
  assert (Hspm1 : edenot E1 spm = Z_to_bv 64 (su - 132544)).
  { subst spm. rewrite mkAlu_denot. cbn [edenot]. rewrite <- R2'. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold su. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  pose proof (split_lit_denot E1 spm qb qk Hsq) as Hsqd1. rewrite Hspm1 in Hsqd1.
  destruct (rw_okb_sound E1 M (kn cs) qb qk 132544 HKN1 Hrw ltac:(lia)) as (Wst1 & Wdef1 & Wimg1 & W01 & Wnw1).
  assert (Hq1 : (bv_unsigned (edenot E1 qb) + qk = su - 132544)%Z).
  { apply (f_equal bv_unsigned) in Hsqd1. rewrite !u64_lit in Hsqd1 by lia. lia. }
  assert (Hnx1 : s_next (c_ss cs1) = N.succ v) by (subst cs1; cbn [bump_next c_ss s_next]; subst v; apply N.add_1_r).
  pose proof (ext_call_agree E1 (N.succ v) R') as Hag.
  destruct Hframe as [Hout Hgrows].
  set (rs := [(qb, qk, ELit 132544); (ELit 0, 0x26360%Z, ELit 8); (ELit 0, 0x3670c%Z, ELit 4)]).
  assert (HOUT : forall x : word, inrs E1 rs x = false -> M' x = M x).
  { intros x Hx. apply Hout. eapply (outside_of_inrs E1 rs); [|exact Hx]. subst rs. cbn [F_footprint fp_frame fp_prng fp_errno FP_src0].
    repeat apply Forall2_cons; try apply Forall2_nil; unfold rng_lo, rng_len, estart; cbn [fst snd a_base a_off edenot fp_frame fp_prng fp_errno FP_src0];
      rewrite ?Hq1; unfold elenZ; cbn [edenot]; fold su; rewrite !u64_lit by lia; lia. }
  destruct (havocs_frame E1 rs M (kn cs) M M' HKN1 HOUT Hgrows) as [HKV HSV].
  destruct (after_call_sound cs1 0x13d7c (Some (ELit 0)) k4 csa E1 R R' M M' model
              (slots_keep (kn cs) (ELit 0) 0x3670c (ELit 4)
                 (slots_keep (kn cs) (ELit 0) 0x26360 (ELit 8)
                    (slots_keep (kn cs) qb qk (ELit 132544) (c_slots cs)))) Hac HC1) as [HC' Hpc'].
  - (* [comment removed for export] *)
    apply kept_regs. intros kk Hin.
    assert (KEPT : forall r : bv 5, In r FContract.ekept -> getr R' r = getr R r) by exact Hkeeps.
    cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      (apply KEPT; unfold FContract.ekept; cbn [In Z.of_nat Pos.of_succ_nat Pos.succ];
       repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] end).
  - (* [comment removed for export] *)
    cbn [edenot]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). exact Ha0.
  - (* [comment removed for export] *)
    assert (HK0 : know_ok RSEGS E1 M k0) by (subst k0; apply kimg_cut_sound, kimg_cut_sound, HKN1).
    pose proof (HKV k0 HK0) as HK3. change (kn_havocs k0 rs) with k3 in HK3.
    subst k4. constructor; [|exact HK3].
    (* [comment removed for export] *)
    cbn [kentry_ok]. split; [lia|]. split.
    + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite u64_lit by lia. cbn. lia.
    + unfold adenot. cbn [a_base a_off edenot]. subst E1. rewrite ext1_at.
      replace (v_addi (Z_to_bv 64 0) 0x3670c) with (Z_to_bv 64 0x3670c : word) by (apply bv_eq; reflexivity).
      rewrite Hebs. f_equal. subst ew. symmetry. apply word_to_le_bytes_of_lez; [exact Hebl | lia].
  - (* [comment removed for export] *)
    pose proof (HSV (c_slots cs) HSL1) as HS3. exact HS3.
  - (* [comment removed for export] *)
    rewrite Hnx1. apply andb_prop in Hfresh' as [_ Hslv]. apply slots_vars_lt_keep. apply slots_vars_lt_keep. apply slots_vars_lt_keep.
    eapply slots_vars_lt_mono; [| exact Hslv]. lia.
  - (* [comment removed for export] *)
    subst cs'. rewrite Hnx1 in HC'.
    assert (Hag0 : env_agree nx0 E (ext_call E1 (N.succ v) R')).
    { eapply env_agree_le with (b' := v); [|exact Hnx0].
      eapply env_agree_trans'; [apply ext1_agree | eapply env_agree_le; [exact Hag | lia]]. }
    specialize (HK (ext_call E1 (N.succ v) R') R' M' Hag0 HC').
    rewrite Hpc' in HK. unfold cfg_of in HK. exact HK.
Qed.

Theorem call_F_ok : F_sound_stmt RSEGS REF_ATB nx0.
Proof. exact call_F_sound'. Qed.

End NX0.
