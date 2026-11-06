(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib ShapeLaws.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbPrintfBufBase UbPrintfBuf.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan SymSlots SymPlanSoundA SymPlanSound SymPlanSoundH SymPlanSoundG UbSymPlanSoundSW UbATB UbImgHyps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
Local Abbreviation cfg_of := (SPSA.cfg_of RSEGS) (only parsing).
Local Abbreviation ehi_sound := (SPS.ehi_sound RSEGS) (only parsing).
Local Abbreviation elo_sound := (SPS.elo_sound RSEGS) (only parsing).
Local Abbreviation havocs_frame := (SymPlanSoundG.havocs_frame RSEGS) (only parsing).
Local Abbreviation kentry_keep_sem := (SPS.kentry_keep_sem RSEGS) (only parsing).
Local Abbreviation kimg_cut_sound := (SymPlanSoundG.kimg_cut_sound RSEGS) (only parsing).
Local Abbreviation know_ok_havoc := (SPS.know_ok_havoc RSEGS) (only parsing).
Local Abbreviation know_ok_memeq := (SymPlanSoundG.know_ok_memeq RSEGS) (only parsing).
Local Abbreviation kreadZ_rdn := (SPS.kreadZ_rdn RSEGS) (only parsing).
Local Abbreviation printf_sound_stmt := (SPS.printf_sound_stmt RSEGS UB_ATB) (only parsing).
Local Abbreviation reg_lit_sound := (SPSA.reg_lit_sound RSEGS) (only parsing).
Local Abbreviation reg_sound := (SPSA.reg_sound RSEGS) (only parsing).
Local Abbreviation ret_lit_sound := (SPS.ret_lit_sound RSEGS) (only parsing).
Local Abbreviation rw_okb_sound := (SPS.rw_okb_sound RSEGS H_wview_off_ub) (only parsing).
Local Abbreviation slot_ok_agree := (SSL.slot_ok_agree RSEGS) (only parsing).
Local Abbreviation slots_keep_sound := (SSL.slots_keep_sound RSEGS) (only parsing).
Local Abbreviation slots_ok := (SSL.slots_ok RSEGS) (only parsing).
Local Abbreviation slots_ok_memeq := (SymPlanSoundG.slots_ok_memeq RSEGS) (only parsing).
Local Abbreviation kread8e_rdn := (SymPlanSoundH.kread8e_rdn RSEGS) (only parsing).
Local Abbreviation co_know := (SPSA.co_know RSEGS) (only parsing).
Local Abbreviation co_halt := (SPSA.co_halt RSEGS) (only parsing).
Local Abbreviation co_lazy := (SPSA.co_lazy RSEGS) (only parsing).
Local Abbreviation co_slots := (SPSA.co_slots RSEGS) (only parsing).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma w2b2_0a30 : forall E, word_to_le_bytes 2 (edenot E (ELit 0x0a30)) = [Z_to_bv 8 0x30; Z_to_bv 8 0x0a].
Proof.
  intros E. cbn [edenot]. unfold word_to_le_bytes. rewrite u64_lit by lia. cbn [Z_to_le_bytes].
  f_equal; apply bv_eq; reflexivity.
Qed.

Lemma rdn_split2 : forall M (a : Z) b0 b1,
  0 <= a -> a + 2 <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) 2 = Some [b0; b1] ->
  rdn RSEGS M (Z_to_bv 64 a) 1 = Some [b0] /\ rdn RSEGS M (Z_to_bv 64 (a + 1)) 1 = Some [b1].
Proof.
  intros M a b0 b1 Ha Ha2 H. cbn [rdn] in *.
  destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end) as [x|]; [|discriminate].
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1) : word) in H.
  2:{ apply bv_eq. rewrite (u_add1 (Z_to_bv 64 a)) by (rewrite u64_lit by lia; lia). rewrite !u64_lit by lia. reflexivity. }
  destruct (match M (Z_to_bv 64 (a + 1)) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 (a + 1)) end) as [y|]; [|discriminate].
  injection H as <- <-. split; reflexivity.
Qed.

Section NX0.
Variable nx0 : N.
Hypothesis nx0_pos : nx0_okP nx0.
Local Abbreviation after_call_sound := (SPS.after_call_sound RSEGS nx0 nx0_pos) (only parsing).

(* [comment removed for export] *)

Theorem call_printf_sound' : printf_sound_stmt nx0.
Proof.
  unfold SPS.printf_sound_stmt.
  intros cs cs' E R M model T HC Hpc Hn HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_slots _ _ _ _ _ HC) as HSL.
  rewrite call_printf_eq in Hn. unfold call_printf_ref in Hn.
  change (d_stdout UB_ATB) with 0x269f0%Z in Hn. change (d_stdout_buf UB_ATB) with 0x57730%Z in Hn.
  change (d_canary UB_ATB) with 0x56ca0%Z in Hn. change (t_printf_ret UB_ATB) with 0x13e6c%Z in Hn. change (d_rw_lo UB_ATB) with 0x26000%Z in Hn.
  change (- PF_WIN)%Z with (-1056)%Z in Hn. unfold PF_WIN in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [[|p11|p11]|] eqn:H11; try discriminate.
  destruct (negb (Z.eqb ret 0x13e6c)) eqn:Hreq; [discriminate|].
  apply negb_false_iff in Hreq. apply Z.eqb_eq in Hreq. subst ret.
  destruct (kreadZ RSEGS (kn cs) (ELit 0) 0x269f0 4) as [flags|] eqn:Hflags; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x269f0 + 32) 8) as [wend|] eqn:Hwend; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x269f0 + 40) 8) as [w|] eqn:Hw; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x269f0 + 96) 8) as [bsz|] eqn:Hbsz; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x269f0 + 140) 4) as [lock|] eqn:Hlock; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0x269f0 + 144) 4) as [lbf|] eqn:Hlbf; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) 0x56ca0) as [canv|] eqn:Hcan; [|discriminate].
  set (spm := mkAlu ALU_ADD (reg cs 2) (ELit (-1056))) in Hn.
  destruct (split_lit spm) as [qb qk] eqn:Hsq.
  destruct (elo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (ehi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  set (k0 := kimg_cut (kimg_cut (kimg_cut (kn cs) 0x269f0 4) (0x269f0 + 40) 8) w 2) in Hn.
  set (k4 := kn_havoc (kn_havoc (kn_havoc (kn_havoc k0 qb qk (ELit 1056)) (ELit 0) 0x269f0 (ELit 4))
                        (ELit 0) (0x269f0 + 40) (ELit 8)) (ELit 0) w (ELit 2)) in Hn.
  set (k5 := KWord (SA (ELit 0) 0x269f0) 4 (ELit 5)
             :: KWord (SA (ELit 0) (0x269f0 + 40)) 8 (ELit (w + 2))
             :: KWord (SA (ELit 0) w) 2 (ELit 0x0a30) :: k4) in Hn.
  destruct (after_call nx0 cs 0x13e6c None k5) as [csa|] eqn:Hac; [|discriminate].
  lazymatch type of Hn with Some ?c = Some cs' => assert (Ecs : cs' = c) by congruence end. clear Hn.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hrw]. apply andb_prop in Hcond as [Hcond Heal]. apply andb_prop in Hcond as [Hcond Himg].
  apply andb_prop in Hcond as [Hcond Hlbf']. apply andb_prop in Hcond as [Hcond Hlock']. apply andb_prop in Hcond as [Hcond Hbsz'].
  apply andb_prop in Hcond as [Hcond Hwhi]. apply andb_prop in Hcond as [Hcond Hwlo]. apply andb_prop in Hcond as [Hflags' Hwend'].
  apply Z.eqb_eq in Hflags'. apply Z.eqb_eq in Hwend'. apply Z.leb_le in Hwlo. apply Z.leb_le in Hwhi. apply Z.eqb_eq in Hbsz'.
  apply Z.eqb_eq in Hlock'. apply Z.eqb_eq in Hlbf'. apply Z.leb_le in Heal. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  subst flags wend bsz lock lbf.
  unfold SP.IMG_HI, SP.IMG_LO, SP.PF_WIN in *.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R M model 0x13e6c HC Hret) as (R1 & Hrok & _).
  destruct (reg_lit_sound E cs R M model 11 0 HC ltac:(lia) H11) as [R11 _].
  pose proof (reg_sound E cs R M model 2 HC ltac:(lia)) as R2.
  replace (Z_to_bv 5 1) with (1%bv : bv 5) in R1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in R11 by (apply bv_eq; reflexivity).
  set (sp := edenot E (reg cs 2)) in *. set (su := bv_unsigned sp).
  pose proof (elo_sound E M (kn cs) _ _ HKN Hsplo) as Hsplo2. fold sp in Hsplo2. fold su in Hsplo2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hsphi) as Hsphi2. fold sp in Hsphi2. fold su in Hsphi2.
  pose proof (u64_range sp) as Hspr. fold su in Hspr.
  (* [comment removed for export] *)
  assert (Hspm : edenot E spm = Z_to_bv 64 (su - 1056)).
  { subst spm. rewrite mkAlu_denot. cbn [edenot]. fold sp. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold su. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  pose proof (split_lit_denot E spm qb qk Hsq) as Hsqd. rewrite Hspm in Hsqd.
  destruct (rw_okb_sound E M (kn cs) qb qk 1056 HKN Hrw ltac:(lia)) as (Wst & Wdef & Wimg & W0 & Wnw).
  assert (Hq : (bv_unsigned (edenot E qb) + qk = su - 1056)%Z).
  { apply (f_equal bv_unsigned) in Hsqd. rewrite !u64_lit in Hsqd by lia. lia. }
  rewrite Hq in Wst, Wdef, Wimg.
  (* [comment removed for export] *)
  destruct (ealign_sound RSEGS E M (kn cs) (reg cs 2) HKN) as [Heal0 Hdiv]. fold sp in Hdiv. fold su in Hdiv.
  assert (Hsu16 : su mod 16 = 0).
  { apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdiv].
    exists (2 ^ (ealign (kn cs) (reg cs 2) - 4)). change 16 with (2 ^ 4). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 <= n)%Z -> (off + n <= 2 ^ 64)%Z -> (off < 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C D. apply flat_abs0; lia. }
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) 0x269f0 4 5 HKN Hflags ltac:(lia) ltac:(apply FL; lia)) as [Rflags _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x269f0 + 32) 8 _ HKN Hwend ltac:(lia) ltac:(apply FL; lia)) as [Rwend _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x269f0 + 40) 8 w HKN Hw ltac:(lia) ltac:(apply FL; lia)) as [Rw Hwr].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x269f0 + 96) 8 _ HKN Hbsz ltac:(lia) ltac:(apply FL; lia)) as [Rbsz _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x269f0 + 140) 4 _ HKN Hlock ltac:(lia) ltac:(apply FL; lia)) as [Rlock _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0x269f0 + 144) 4 _ HKN Hlbf ltac:(lia) ltac:(apply FL; lia)) as [Rlbf _].
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) 0x56ca0 canv HKN Hcan ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_abs0 in Rflags, Rwend, Rw, Rbsz, Rlock, Rlbf, Rcan.
  (* [comment removed for export] *)
  assert (IMG : forall i, 0x10000 <= i < 0x26000 -> M (Z_to_bv 64 i) = None).
  { unfold kimg_covers in Himg. apply existsb_exists in Himg as (K & HinK & HKb).
    destruct K as [| | |ilo ihi| | | |]; try discriminate. apply andb_prop in HKb as [Hil Hih].
    apply Z.leb_le in Hil. apply Z.leb_le in Hih.
    pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKi. cbn [kentry_ok] in HKi. destruct HKi as (_ & _ & Hnone).
    intros i Hi. apply Hnone. lia. }
  (* [comment removed for export] *)
  assert (PH : pfH M sp w (bv_unsigned (edenot E canv))).
  { constructor.
    - exact Hsu16.
    - lia.
    - lia.
    - unfold SymRun.stk_ok, PF_FR. intros a n Ha Hn.
      eapply (store_ok_sub RSEGS M (Z_to_bv 64 (su - 1056)) a (Z.to_nat 1056) n);
        rewrite ?u64_lit by lia; rewrite ?Z2Nat.id by lia; try lia. exact Wst.
    - exact IMG.
    - exact Rflags.
    - exact Rwend.
    - exact Rw.
    - lia.
    - exact Rbsz.
    - exact Rlock.
    - exact Rlbf.
    - rewrite Z_to_bv_bv_unsigned. exact Rcan.
    - apply u64_range. }
  destruct (printf0_buffered R M (seg_rom RSEGS) sp w (bv_unsigned (edenot E canv)) PH R1 ltac:(exact R2) R11)
    as (R' & M' & Hms & Hkeeps & Hframe & Bw & Bwpos & Bflags).
  (* [comment removed for export] *)
  unfold cfg_of. rewrite Hpc. change (t_printf UB_ATB) with 0x13f18%Z.
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |].
  unfold fresh_ok in Hfresh. apply andb_prop in Hfresh as [Hfresh' Hnx0]. apply N.leb_le in Hnx0.
  set (nx := s_next (c_ss cs)) in *.
  pose proof (ext_call_agree E nx R') as Hag.
  destruct Hframe as [Hout Hgrows].
  set (rs := [(qb, qk, ELit 1056); (ELit 0, 0x269f0%Z, ELit 4); (ELit 0, (0x269f0 + 40)%Z, ELit 8); (ELit 0, w, ELit 2)]).
  assert (HOUT : forall x : word, inrs E rs x = false -> M' x = M x).
  { intros x Hx. apply Hout. eapply (outside_of_inrs E rs); [|exact Hx]. subst rs.
    repeat apply Forall2_cons; try apply Forall2_nil; unfold rng_lo, rng_len, estart; cbn [fst snd a_base a_off edenot];
      rewrite ?Hq; unfold elenZ; cbn [edenot]; rewrite !u64_lit by lia; lia. }
  destruct (havocs_frame E rs M (kn cs) M M' HKN HOUT Hgrows) as [HKV HSV].
  destruct (after_call_sound cs 0x13e6c None k5 csa E R R' M M' model
              (slots_keep (kn cs) (ELit 0) w (ELit 2)
                 (slots_keep (kn cs) (ELit 0) (0x269f0 + 40) (ELit 8)
                    (slots_keep (kn cs) (ELit 0) 0x269f0 (ELit 4)
                       (slots_keep (kn cs) qb qk (ELit 1056) (c_slots cs))))) Hac HC) as [HC' Hpc'].
  - (* [comment removed for export] *)
    apply kept_regs. intros kk Hin.
    assert (KEPT : forall r : bv 5, In r RefMemcpyLib.callee_saved -> getr R' r = getr R r) by exact Hkeeps.
    cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      (apply KEPT; unfold RefMemcpyLib.callee_saved; cbn [In Z.of_nat Pos.of_succ_nat Pos.succ];
       repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] end).
  - exact I.
  - (* [comment removed for export] *)
    assert (HK0 : know_ok RSEGS E M k0) by (subst k0; apply kimg_cut_sound, kimg_cut_sound, kimg_cut_sound, HKN).
    pose proof (HKV k0 HK0) as HK4. change (kn_havocs k0 rs) with k4 in HK4.
    subst k5.
    pose proof (rdn_split2 M' w _ _ ltac:(lia) ltac:(lia) Bw) as [B0 B1].
    repeat apply Forall_cons; [ | | | exact HK4]; cbn [kentry_ok]; (split; [lia|]); (split; [apply FL; lia|]); rewrite adenot_abs0.
    + exact Bflags.
    + cbn [edenot]. exact Bwpos.
    + rewrite w2b2_0a30. exact Bw.
  - (* [comment removed for export] *)
    pose proof (HSV (c_slots cs) HSL) as HS4. exact HS4.
  - (* [comment removed for export] *)
    apply andb_prop in Hfresh' as [_ Hslv]. apply slots_vars_lt_keep. apply slots_vars_lt_keep. apply slots_vars_lt_keep. apply slots_vars_lt_keep. exact Hslv.
  - (* [comment removed for export] *)
    subst cs'. specialize (HK (ext_call E nx R') R' M' ltac:(eapply env_agree_le; [exact Hag | exact Hnx0]) HC').
    rewrite Hpc' in HK. unfold cfg_of in HK. exact HK.
Qed.

Theorem call_printf_ok : printf_sound_stmt nx0.
Proof. exact call_printf_sound'. Qed.

End NX0.
