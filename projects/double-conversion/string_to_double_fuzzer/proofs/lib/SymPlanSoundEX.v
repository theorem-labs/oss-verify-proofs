(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes
  MmapSim AllocSim FileSim AgentLib ShapeLaws Spec SpecConsts Hoare Frame
  RefExitBase RefStdioDefs RefExit.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan SymSlots
  SymPlanSoundA SymPlanSound SymPlanSoundH SymPlanSoundSW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := ImgP.M.loaded_segments.
Section FX.
Context {fx : PropExec.FPState}.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

Lemma kread4e_rdn : forall E M k b off v,
  know_ok RSEGS E M k -> kread4e RSEGS k b off = Some v -> flat E (SA b off) 4 ->
  rdn RSEGS M (adenot E (SA b off)) 4 = Some (word_to_le_bytes 4 (edenot E v)).
Proof.
  intros E M k b off v HK H Hfl. apply (kread_rdn RSEGS E M k b off 4 v HK); [exact H | lia | lia | exact Hfl].
Qed.

(* [comment removed for export] *)
Lemma cells_ok_one : forall E M k cells a n v,
  know_ok RSEGS E M k -> cells_ok RSEGS k cells = true -> In (a, n, v) cells ->
  (1 <= n <= 8)%nat -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros E M k cells a n v HK H Hin Hn Ha0 Ha8.
  unfold cells_ok in H. rewrite forallb_forall in H. specialize (H _ Hin). cbn beta iota in H.
  destruct (kreadZ RSEGS k (ELit 0) a n) as [z|] eqn:Hz; [|discriminate]. apply Z.eqb_eq in H. subst z.
  destruct (kreadZ_rdn E M k (ELit 0) a n v HK Hz Hn ltac:(apply flat_abs0; lia)) as [R _].
  rewrite adenot_abs0 in R. exact R.
Qed.

Lemma w2b1_0 : word_to_le_bytes 1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. rewrite w2lb1. reflexivity. Qed.

(* [comment removed for export] *)

Theorem node_exitcall_sound'_fx : forall cs bs code E R M model,
  cs_ok E cs R M model -> pc cs = t_exitc P0 -> node_exitcall RSEGS P0 cs = Some (bs, code) ->
  realizes RSEGS (cfg_of R (pc cs) M model) (t_emit (Wz 1 bs) (t_exit (Z_to_bv 64 code) (m_fs model))).
Proof.
  
  intros cs bs code E R M model HC Hpc Hn.
  pose proof (co_know _ _ _ _ _ HC) as HKN.
  unfold node_exitcall in Hn.
  change (d_stdout P0) with 0xb2d90%Z in Hn. change (d_stderr P0) with 0xb2ca0%Z in Hn.
  change (d_canary P0) with 0xe4b88%Z in Hn. change (d_canary_got P0) with 0xb1bb0%Z in Hn.
  change (t_stdio_write P0) with 0x9ba34%Z in Hn.
  destruct (reg_lit cs 10) as [c|] eqn:H10; [|discriminate].
  destruct (reg_lit cs 4) as [tp|] eqn:H4; [|discriminate].
  set (spm := mkAlu ALU_ADD (reg cs 2) (ELit (-144))) in Hn.
  destruct (split_lit spm) as [qb qk] eqn:Hsq.
  destruct (elo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (ehi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  destruct (kread4e RSEGS (kn cs) (ELit 0) (tp - 168)) as [tide|] eqn:Htid; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0xb2d90 + 140) 4) as [lock|] eqn:Hlock; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0xb2d90 + 40) 8) as [wp|] eqn:Hwp; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) (ELit 0) (0xb2d90 + 56) 8) as [wb|] eqn:Hwb; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (0xb2d90 + 8)) as [rp|] eqn:Hrp; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (0xb2d90 + 16)) as [re|] eqn:Hre; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (0xb2ca0 + 40)) as [w2|] eqn:Hw2; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (0xb2ca0 + 56)) as [b2|] eqn:Hb2; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (0xb2ca0 + 8)) as [r2|] eqn:Hr2; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (0xb2ca0 + 16)) as [e2|] eqn:He2; [|discriminate].
  destruct (elo (kn cs) tide) as [tlo|] eqn:Htlo; [|discriminate].
  destruct (ehi (kn cs) tide) as [thi|] eqn:Hthi; [|discriminate].
  match type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hcond; [|discriminate] end.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hthi']. apply andb_prop in Hcond as [Hcond Htlo'].
  apply andb_prop in Hcond as [Hcond Htphi]. apply andb_prop in Hcond as [Hcond Htplo].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo']. apply andb_prop in Hcond as [Hcond Hrw].
  apply andb_prop in Hcond as [Hcond Eq2]. apply andb_prop in Hcond as [Hcond Eqw2]. apply andb_prop in Hcond as [Hcond Eqrp].
  apply andb_prop in Hcond as [Hcells Hlock'].
  apply Z.ltb_lt in Hthi'. apply Z.leb_le in Htlo'. apply Z.leb_le in Htphi. apply Z.leb_le in Htplo.
  apply Z.leb_le in Hsphi'. apply Z.leb_le in Hsplo'. apply Z.eqb_eq in Hlock'. subst lock.
  apply expr_eqb_eq in Eq2. apply expr_eqb_eq in Eqw2. apply expr_eqb_eq in Eqrp. subst e2 b2 re.
  (* [comment removed for export] *)
  destruct (reg_lit_sound E cs R M model 10 c HC ltac:(lia) H10) as [R10 Hc].
  destruct (reg_lit_sound E cs R M model 4 tp HC ltac:(lia) H4) as [R4 Htp].
  pose proof (reg_sound E cs R M model 2 HC ltac:(lia)) as R2.
  replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 4)) with (4%bv : bv 5) in R4 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in R10 by (apply bv_eq; reflexivity).
  set (sp := edenot E (reg cs 2)) in *. set (su := bv_unsigned sp).
  pose proof (elo_sound E M (kn cs) _ _ HKN Hsplo) as Hsplo2. fold sp in Hsplo2. fold su in Hsplo2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hsphi) as Hsphi2. fold sp in Hsphi2. fold su in Hsphi2.
  pose proof (elo_sound E M (kn cs) _ _ HKN Htlo) as Htlo2.
  pose proof (ehi_sound E M (kn cs) _ _ HKN Hthi) as Hthi2.
  pose proof (u64_range sp) as Hspr. fold su in Hspr. unfold two64 in Htp, Hc.
  (* [comment removed for export] *)
  assert (Hspm : edenot E spm = Z_to_bv 64 (su - 144)).
  { subst spm. rewrite mkAlu_denot. cbn [edenot]. fold sp. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold su. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
  pose proof (split_lit_denot E spm qb qk Hsq) as Hsqd. rewrite Hspm in Hsqd.
  destruct (rw_okb_sound E M (kn cs) qb qk 144 HKN Hrw ltac:(lia)) as (Wst & Wdef & Wimg & W0 & Wnw).
  assert (Hq : (bv_unsigned (edenot E qb) + qk = su - 144)%Z).
  { apply (f_equal bv_unsigned) in Hsqd. rewrite !u64_lit in Hsqd by lia. lia. }
  rewrite Hq in Wst, Wdef, Wimg.
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 <= n)%Z -> (off + n <= 2 ^ 64)%Z -> (off < 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C D. apply flat_abs0; lia. }
  pose proof (kread4e_rdn E M (kn cs) (ELit 0) (tp - 168) tide HKN Htid ltac:(apply FL; lia)) as Rtid.
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0xb2d90 + 140) 4 _ HKN Hlock ltac:(lia) ltac:(apply FL; lia)) as [Rlock _].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0xb2d90 + 40) 8 wp HKN Hwp ltac:(lia) ltac:(apply FL; lia)) as [Rwp Hwpr].
  destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0xb2d90 + 56) 8 wb HKN Hwb ltac:(lia) ltac:(apply FL; lia)) as [Rwb Hwbr].
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0xb2d90 + 8) rp HKN Hrp ltac:(apply FL; lia)) as Rrp.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0xb2d90 + 16) rp HKN Hre ltac:(apply FL; lia)) as Rre.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0xb2ca0 + 40) w2 HKN Hw2 ltac:(apply FL; lia)) as Rw2.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0xb2ca0 + 56) w2 HKN Hb2 ltac:(apply FL; lia)) as Rb2.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0xb2ca0 + 8) r2 HKN Hr2 ltac:(apply FL; lia)) as Rr2.
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0xb2ca0 + 16) r2 HKN He2 ltac:(apply FL; lia)) as Re2.
  rewrite adenot_abs0 in Rtid, Rlock, Rwp, Rwb, Rrp, Rre, Rw2, Rb2, Rr2, Re2. unfold two64 in Hwpr, Hwbr.
  (* [comment removed for export] *)
  change (e_cells P0) with
    [(0xe4b80, 4%nat, 0); (0xb1bb8, 8%nat, 0xac708); (0xb1bc0, 8%nat, 0xac700); (0xac700, 8%nat, 0x324e4);
     (0xb2ee8, 1%nat, 0); (0xb1a70, 8%nat, 0x95eb0); (0xb1a78, 8%nat, 0); (0xb2be0, 8%nat, 0xb2be0);
     (0xe4bab, 1%nat, 0); (0xe50f0, 8%nat, 0); (0xe50e0, 8%nat, 0);
     (0xb2e78, 8%nat, 0xb2d90); (0xb2d88, 8%nat, 0xb2ca0); (0xb2ca0 + 140, 4%nat, 4294967295);
     (0xe4964, 4%nat, 0); (0xe4970, 8%nat, 0xe4978);
     (0xe4968, 4%nat, 1); (0xe4978, 8%nat, 0); (0xe4980, 8%nat, 0x96040);
     (0xe4a80, 8%nat, 0x3299c); (0xc2ef4, 1%nat, 0)]%Z in Hcells.
  assert (CELL : forall a n v, In (a, n, v)
     [(0xe4b80, 4%nat, 0); (0xb1bb8, 8%nat, 0xac708); (0xb1bc0, 8%nat, 0xac700); (0xac700, 8%nat, 0x324e4);
      (0xb2ee8, 1%nat, 0); (0xb1a70, 8%nat, 0x95eb0); (0xb1a78, 8%nat, 0); (0xb2be0, 8%nat, 0xb2be0);
      (0xe4bab, 1%nat, 0); (0xe50f0, 8%nat, 0); (0xe50e0, 8%nat, 0);
      (0xb2e78, 8%nat, 0xb2d90); (0xb2d88, 8%nat, 0xb2ca0); (0xb2ca0 + 140, 4%nat, 4294967295);
      (0xe4964, 4%nat, 0); (0xe4970, 8%nat, 0xe4978);
     (0xe4968, 4%nat, 1); (0xe4978, 8%nat, 0); (0xe4980, 8%nat, 0x96040);
     (0xe4a80, 8%nat, 0x3299c); (0xc2ef4, 1%nat, 0)]%Z ->
     (1 <= n <= 8)%nat -> 0 <= a -> a + 8 <= 2 ^ 64 ->
     rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v))).
  { intros a n v Hin Hn8 A B. eapply cells_ok_one; [exact HKN | exact Hcells | exact Hin | exact Hn8 | exact A | exact B]. }
  (* [comment removed for export] *)
  assert (EC : exit_common1 R M sp (Z_to_bv 64 tp) (Z_to_bv 64 c) (bv_unsigned (edenot E tide)) (edenot E w2) (edenot E r2)).
  { constructor.
    - exact R2.
    - exact R4.
    - exact R10.
    - lia.
    - lia.
    - exact Wst.
    - rewrite u64_lit by lia. lia.
    - rewrite u64_lit by lia. lia.
    - lia.
    - rewrite u64_lit by lia. rewrite Z_to_bv_bv_unsigned. exact Rtid.
    - apply (CELL 0xe4b80 4%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0xb1bb8 8%nat 0xac708); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0xb1bc0 8%nat 0xac700); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0xac700 8%nat 0x324e4); [cbn; noncert_qtauto | lia | lia | lia].
    - rewrite <- w2b1_0. apply (CELL 0xb2ee8 1%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0xb1a70 8%nat 0x95eb0); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0xb1a78 8%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0xb2be0 8%nat 0xb2be0); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0xe4964 4%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0xe4968 4%nat 1); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0xe4970 8%nat 0xe4978); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0xe4978 8%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0xe4980 8%nat 0x96040); [cbn; noncert_qtauto | lia | lia | lia].
    - apply (CELL 0xe4a80 8%nat 0x3299c); [cbn; noncert_qtauto | lia | lia | lia].
    - rewrite <- w2b1_0. apply (CELL 0xc2ef4 1%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
    - repeat split.
      + rewrite <- w2b1_0. apply (CELL 0xe4bab 1%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
      + apply (CELL 0xe50f0 8%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
      + apply (CELL 0xe50e0 8%nat 0); [cbn; noncert_qtauto | lia | lia | lia].
      + apply (CELL 0xb2e78 8%nat 0xb2d90); [cbn; noncert_qtauto | lia | lia | lia].
      + apply (CELL 0xb2d88 8%nat 0xb2ca0); [cbn; noncert_qtauto | lia | lia | lia].
    - repeat split.
      + apply (CELL (0xb2ca0 + 140) 4%nat 4294967295); [cbn; noncert_qtauto | lia | lia | lia].
      + exact Rw2.
      + exact Rb2.
      + exact Rr2.
      + exact Re2. }
  (* [comment removed for export] *)
  assert (Hcode : Z_to_bv 64 (Z.land c 255) = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)).
  { apply bv_eq. rewrite !bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    assert (Hl : (0 <= Z.land c 255 < 256)%Z).
    { split; [apply Z.land_nonneg; lia|]. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
      pose proof (Z.mod_pos_bound c (2^8) ltac:(lia)). lia. }
    rewrite !Z.mod_small; try lia. }
  unfold cfg_of. rewrite Hpc. change (t_exitc P0) with 0x96094%Z.
  (* [comment removed for export] *)
  destruct (Z.eqb_spec wb wp) as [Ewb|Nwb].
  - (* [comment removed for export] *)
    injection Hn as <- <-. cbn [Wz map]. rewrite Hcode. change (@nil event) with (W 1 []).
    apply ref_exit1_Z. exists sp, (Z_to_bv 64 tp), (bv_unsigned (edenot E tide)), (edenot E w2), (edenot E r2).
    split; [exact EC|]. split; [exact (co_halt _ _ _ _ _ HC)|]. split; [exact (co_lazy _ _ _ _ _ HC)|].
    left. split; [reflexivity|]. exists (Z_to_bv 64 wp), (edenot E rp).
    repeat split; [exact Rlock | exact Rwp | subst wb; exact Rwb | exact Rrp | exact Rre].
  - (* [comment removed for export] *)
    destruct (kreadZ RSEGS (kn cs) (ELit 0) (0xb2d90 + 72) 8) as [wr|] eqn:Hwr; [|discriminate].
    destruct (kread8e RSEGS (kn cs) (ELit 0) (0xb2d90 + 88)) as [bufp|] eqn:Hbufp; [|discriminate].
    destruct (kread8e RSEGS (kn cs) (ELit 0) (0xb2d90 + 96)) as [bufsz|] eqn:Hbufsz; [|discriminate].
    destruct (kreadZ RSEGS (kn cs) (ELit 0) (0xb2d90 + 120) 4) as [fd|] eqn:Hfd; [|discriminate].
    destruct (kreadZ RSEGS (kn cs) (ELit 0) 0xb1bb0 8) as [cg|] eqn:Hcg; [|discriminate].
    destruct (kread8e RSEGS (kn cs) (ELit 0) 0xe4b88) as [canv|] eqn:Hcan; [|discriminate].
    destruct (kread_bytes RSEGS (Z.to_nat (wp - wb)) (kn cs) (ELit 0) wb) as [pend|] eqn:Hpend; [|discriminate].
    match type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc2; [|discriminate] end.
    injection Hn as <- <-.
    apply andb_prop in Hc2 as [Hc2 Hmax]. apply andb_prop in Hc2 as [Hc2 Hwphi]. apply andb_prop in Hc2 as [Hc2 Hlt].
    apply andb_prop in Hc2 as [Hc2 Hwblo]. apply andb_prop in Hc2 as [Hc2 Hcgv]. apply andb_prop in Hc2 as [Hwr' Hfd'].
    rewrite ITOP_eq in Hwphi. apply Z.leb_le in Hmax. apply Z.leb_le in Hwphi. apply Z.ltb_lt in Hlt. apply Z.leb_le in Hwblo.
    apply Z.eqb_eq in Hcgv. apply Z.eqb_eq in Hwr'. apply Z.eqb_eq in Hfd'. subst wr fd cg.
    destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0xb2d90 + 72) 8 _ HKN Hwr ltac:(lia) ltac:(apply FL; lia)) as [Rwr _].
    pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0xb2d90 + 88) bufp HKN Hbufp ltac:(apply FL; lia)) as Rbufp.
    pose proof (kread8e_rdn E M (kn cs) (ELit 0) (0xb2d90 + 96) bufsz HKN Hbufsz ltac:(apply FL; lia)) as Rbufsz.
    destruct (kreadZ_rdn E M (kn cs) (ELit 0) (0xb2d90 + 120) 4 1 HKN Hfd ltac:(lia) ltac:(apply FL; lia)) as [Rfd _].
    destruct (kreadZ_rdn E M (kn cs) (ELit 0) 0xb1bb0 8 _ HKN Hcg ltac:(lia) ltac:(apply FL; lia)) as [Rcg _].
    pose proof (kread8e_rdn E M (kn cs) (ELit 0) 0xe4b88 canv HKN Hcan ltac:(apply FL; lia)) as Rcan.
    rewrite adenot_abs0 in Rwr, Rbufp, Rbufsz, Rfd, Rcg, Rcan.
    destruct (kread_bytes_rdn E M (kn cs) (Z.to_nat (wp - wb)) (ELit 0) wb pend HKN Hpend
                ltac:(cbn [edenot]; rewrite u64_lit by lia; lia) ltac:(cbn [edenot]; rewrite u64_lit by lia; lia)) as [Rpend Lpend].
    cbn [edenot] in Rpend. rewrite (u64_lit 0) in Rpend by lia. rewrite Z.add_0_l in Rpend.
    rewrite Wz_map, Hcode. change (map (WriteEv (Z_to_bv 64 1)) ?l) with (W 1 l).
    apply ref_exit1_Z. exists sp, (Z_to_bv 64 tp), (bv_unsigned (edenot E tide)), (edenot E w2), (edenot E r2).
    split; [exact EC|]. split; [exact (co_halt _ _ _ _ _ HC)|]. split; [exact (co_lazy _ _ _ _ _ HC)|].
    right. exists wb, wp, (edenot E bufp), (edenot E bufsz), (edenot E rp), (edenot E canv).
    split; [| apply fd_lookup_std1; exact (co_fds _ _ _ _ _ HC)].
    constructor.
    + exact Rlock.
    + exact Rwp.
    + exact Rwb.
    + exact Rwr.
    + exact Rbufp.
    + exact Rbufsz.
    + exact Rfd.
    + exact Rrp.
    + exact Rre.
    + lia.
    + rewrite length_map, Lpend, Z2Nat.id by lia. reflexivity.
    + rewrite length_map, Lpend, Z2Nat.id by lia. pose proof rw_bytes_max_ge17. lia.
    + rewrite length_map, Lpend. exact Rpend.
    + split; [exact Rcg | exact Rcan].
Qed.

Theorem node_exitcall_ok_fx : forall cs bs code E R M model,
  cs_ok E cs R M model -> pc cs = t_exitc P0 -> node_exitcall RSEGS P0 cs = Some (bs, code) ->
  realizes RSEGS (cfg_of R (pc cs) M model) (t_emit (Wz 1 bs) (t_exit (Z_to_bv 64 code) (m_fs model))).
Proof. exact node_exitcall_sound'_fx. Qed.
End FX.


(* [comment removed for export] *)
Theorem node_exitcall_sound' : exitcall_sound_stmt.
Proof. intros  fx. exact (node_exitcall_sound'_fx ). Qed.
Theorem node_exitcall_ok : exitcall_sound_stmt.
Proof. intros  fx. exact (node_exitcall_ok_fx ). Qed.
