(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import AsanNodesAux AsanMaxVA.
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma set_reg_unfold12 : forall (cs : acs) n e,
  set_reg cs n e = with_ss cs (mk_ss (s_pc (a_ss cs)) (sr_upd (s_regs (a_ss cs)) n e) (s_know (a_ss cs)) (s_next (a_ss cs))).
Proof. reflexivity. Qed.
Lemma set_reg_with_ss12 : forall (cs : acs) s n e,
  set_reg (with_ss cs s) n e = with_ss cs (mk_ss (s_pc s) (sr_upd (s_regs s) n e) (s_know s) (s_next s)).
Proof. reflexivity. Qed.
Lemma set_pc_with_ss12 : forall (cs : acs) s p,
  set_pc (with_ss cs s) p = with_ss cs (mk_ss p (s_regs s) (s_know s) (s_next s)).
Proof. reflexivity. Qed.

Section NodesMaxVA.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  (* [comment removed for export] *)
  Hypothesis Xmv : 0 < x_maxva A /\ x_maxva A + 180 < 2 ^ 64.
  Hypothesis CODE : forall i, (i < 45)%nat ->
    fetch_word SEGS (Z_to_bv 64 (x_maxva A + 4 * Z.of_nat i)) = Some (nth i MAXVA_WORDS W0).

  #[local] Notation Hv := (AsanNodesAux.Hv A).
  #[local] Notation lazy_cover_vis := (AsanNodesAux.lazy_cover_vis SEGS A LIMIT SINV argH FS0 HULL_ok).
  #[local] Notation H_off_segments_vis := (AsanNodesAux.H_off_segments_vis SEGS A SEGS_in_hull).

  Theorem x_sound_maxva : x_stmt SEGS A nx0 LIMIT SINV argH FS0 XMaxVA.
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold summary_maxva in Hn.
    destruct (Z.eqb (x_maxva A) 0 || negb (Z.eqb (pc cs) (x_maxva A)))%bool eqn:Hg; [discriminate|].
    apply orb_false_iff in Hg as [_ Hpc]. apply negb_false_iff in Hpc. apply Z.eqb_eq in Hpc.
    destruct (xlo (kn cs) (reg cs 10)) as [lo|] eqn:Hlo; [|discriminate].
    destruct (xhi (kn cs) (reg cs 10)) as [hi|] eqn:Hhi; [|discriminate].
    destruct (Z.leb TWO46 lo && Z.ltb hi TWO47)%bool eqn:Hb; [|discriminate].
    apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
    injection Hn as <-.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (xlo_sound SEGS E _ (kn cs) (reg cs 10) lo HK Hlo) as Xlo.
    pose proof (xhi_sound SEGS E _ (kn cs) (reg cs 10) hi HK Hhi) as Xhi.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as H10.
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
    assert (Hx10 : 2 ^ 46 <= bv_unsigned (getr R 10%bv) < 2 ^ 47) by (rewrite H10; unfold TWO46, TWO47 in *; lia).
    (* [comment removed for export] *)
    set (H2 := Hv E cs model).
    set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
    destruct (maxva_block SEGS (x_maxva A) ltac:(lia) CODE R (mrestrict H2 FULL) (seg_rom SEGS) Hx10) as [R' [Hms Hpost]].
    unfold cfg_of. fold ms.
    assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (x_maxva A + 180)) (mrestrict H2 FULL) (seg_rom SEGS))).
    { unfold ms. rewrite restrict_mkst, Hpc. exact Hms. }
    apply (srz_msteps_restricted_T SEGS H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (x_maxva A + 180)) (mrestrict H2 FULL) (seg_rom SEGS)))
      with (mkst R' (Z_to_bv 64 (x_maxva A + 180)) (munrestrict H2 FULL (mrestrict H2 FULL)) (seg_rom SEGS)).
    rewrite munrestrict_mrestrict.
    specialize (Hk E R' FULL model' (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    cbn [fold_left MAXVA_POST fst snd] in Hk. unfold MAXVA_LEN in Hk.
    set (cs' := set_pc _ _) in Hk.
    assert (Epc : pc cs' = x_maxva A + 180) by (rewrite <- Hpc; reflexivity).
    unfold cfg_of in Hk. rewrite Epc in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    subst cs'. rewrite (set_reg_unfold12 cs).
    repeat (rewrite set_reg_with_ss12; cbn [s_pc s_regs s_know s_next mk_ss]).
    rewrite set_pc_with_ss12. cbn [s_pc s_regs s_know s_next mk_ss].
    eapply cs_ok_frame; [exact SINV_frame | exact HC | exact Hsame | exact Hinv' | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
    cbn [s_regs mk_ss].
    destruct Hpost as (P10 & P11 & P12 & P13 & P14 & P15 & Pag).
    set (R6 := regupd (regupd (regupd (regupd (regupd (regupd R
                 (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0x7fffffffffff))
                 (Z_to_bv 5 (Z.of_nat 11)) (Z_to_bv 64 0xffffffffffffffff))
                 (Z_to_bv 5 (Z.of_nat 12)) (Z_to_bv 64 0x3333333333333333))
                 (Z_to_bv 5 (Z.of_nat 13)) (Z_to_bv 64 0x0f0f0f0f0f0f0f0f))
                 (Z_to_bv 5 (Z.of_nat 14)) (Z_to_bv 64 0x0101010101010101))
                 (Z_to_bv 5 (Z.of_nat 15)) (Z_to_bv 64 0x7fffc00000000000)).
    assert (HR6 : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (s_regs (a_ss cs))
                    10 (ELit 0x7fffffffffff)) 11 (ELit 0xffffffffffffffff)) 12 (ELit 0x3333333333333333))
                    13 (ELit 0x0f0f0f0f0f0f0f0f)) 14 (ELit 0x0101010101010101)) 15 (ELit 0x7fffc00000000000)) R6).
    { unfold R6. do 6 (apply regs_ok_set_n; [|lia|rewrite edenot_lit; reflexivity]). exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC). }
    intros r. rewrite <- (HR6 r). unfold R6.
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 13)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 14)) with (14%bv : bv 5) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 15)) with (15%bv : bv 5) by (apply bv_eq; reflexivity).
    Ltac onereg r n P :=
      destruct (bv_eqb r n) eqn:Q;
      [ unfold bv_eqb in Q; apply Z.eqb_eq in Q; apply bv_eq in Q; subst r; rewrite P;
        repeat first [rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac]; reflexivity
      | assert (r <> n) by (intros ->; rewrite bv_eqb_refl in Q; discriminate); clear Q ].
    onereg r (15%bv : bv 5) P15. onereg r (14%bv : bv 5) P14. onereg r (13%bv : bv 5) P13.
    onereg r (12%bv : bv 5) P12. onereg r (11%bv : bv 5) P11. onereg r (10%bv : bv 5) P10.
    rewrite !getr_other by assumption. apply Pag; assumption.
  Qed.
End NodesMaxVA.
