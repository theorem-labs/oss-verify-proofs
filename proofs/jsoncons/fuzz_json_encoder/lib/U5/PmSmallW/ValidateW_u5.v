(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5 PmLibSpecsW_u5 PmRef_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RelLeaf.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5 CutHeap2.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import SmallWin_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmallW Require Import SmallPtW_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmallW Require Import SmallPureW. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmallW Require Import ValidateKW_u5 ValidateKC_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_validate_xsrc_T_u5 Cut_validate_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ValidateProof.
Module G := Cut_validate_xsrc_u5.
Module GT := Cut_validate_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Definition F0 : list SGP.region := CC.cp_F G.cp0.
Definition LENB : Z := 134217728.

Definition post_chk (ps : SR.post_spec) : bool :=
  match SP.reg_of ps 10, SP.reg_of ps 11 with
  | Some a0e, Some a1e =>
      (PB.prove (SR.ps_cells ps) (KRange a1e 0 6) && PB.prove (SR.ps_cells ps) (KRange (APC.esub a0e (EVar 10)) 0 LENB)
       && PB.prove (SR.ps_cells ps) (KRange (APC.esub (APC.eadd (EVar 10) (EVar 11)) a0e) 0 LENB))%bool
  | _, _ => false
  end.

Lemma cut_facts : CC.cps_all G.CPS (fun _ c => SP.cut_chk GT.NF F0 c) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exit_facts0 : CC.others_all G.CPS G.TAGS (fun _ ps _ => SP.exit_chk GT.ENDS ps) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exit_facts : CC.others_all G.CPS G.TAGS (fun _ ps _ => post_chk ps) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rets : forall pc, In pc GT.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc H. cbn [GT.ENDS In] in H. repeat (destruct H as [<-|H]; [CL.solve_is_ret|]). destruct H. Qed.

(* [comment removed for export] *)
Lemma legal_range : forall l, 0 <= PMR.legal l <= 6.
Proof.
  intros [|ld rest]; cbn [PMR.legal]; [lia|]. destruct (4 <=? Z.of_nat (length rest)); [lia|]. destruct (negb (forallb PMR.is_cont rest)); [lia|].
  set (chk1 := match rest with [] => 0 | b1 :: _ => _ end).
  assert (Hc : 0 <= chk1 <= 6) by (unfold chk1; destruct rest; [lia|]; repeat (first [destruct (ld =? _) | destruct (_ <? _)]); lia).
  destruct (negb (chk1 =? 0)); [exact Hc|]. destruct ((128 <=? ld) && (ld <=? 193))%bool; [lia|]. destruct (244 <? ld); lia.
Qed.
Lemma u8_feeds_err_range : forall v l, 0 <= PMR.u_err v <= 6 -> 0 <= PMR.u_err (PMR.u8_feeds v l) <= 6.
Proof.
  intros v l. revert v. induction l as [|b r IH]; intros v Hv; [exact Hv|]. cbn [PMR.u8_feeds]. apply IH. unfold PMR.u8_feed.
  destruct (negb (PMR.u_err v =? 0)); [exact Hv|]. destruct (PMR.u_pend v); [destruct (PMR.trailing b =? 0); cbn [PMR.u_err]; [apply legal_range | lia]|].
  destruct (Z.of_nat (length _) =? PMR.u_need v); cbn [PMR.u_err]; [apply legal_range | lia].
Qed.
Lemma validate_range : forall l, 0 <= PMR.validate l <= 6.
Proof.
  intros l. unfold PMR.validate, PMR.u8_finish. pose proof (u8_feeds_err_range PMR.u8_init (PMR.b256 l) ltac:(cbn; lia)) as H.
  destruct (negb _); [exact H|]. destruct (PMR.u_pend _); lia.
Qed.
Lemma arun_split : forall (ab : nat -> Z) va m j, (m <= j)%nat -> VKW.arun ab va 0 j = PMR.u8_feeds (VKW.arun ab va 0 m) (map ab (seq m (j - m))).
Proof.
  intros ab va m j H. unfold VKW.arun. rewrite !Nat.sub_0_r, <- VKW.u8_feeds_app, <- map_app. f_equal. f_equal.
  replace j with (m + (j - m))%nat at 1 by lia. rewrite (seq_app m (j - m) 0). reflexivity.
Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Theorem validate_okw : PMW.validate_specw L PMR.the_rm.
Proof.
  intros s len sp r bs fx R M model K Hh Hl HK0 Hfp ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Hlen & Hdefs & IMGRO & Hs1 & Hs2 & Hbs & Hbl' & Hbr) Hcont.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  assert (Hbi : Forall VKW.inb bs) by (apply Forall_impl with (P := fun b => 0 <= b <= 255); [intros b Hb; exact Hb | exact Hbr]).
  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun id => match id with 0%nat => map (Z_to_bv 8) bs | _ => [] end)).
  set (WI := fun (i : nat) (E : env) (_ : word -> option byte) =>
     match i with 0%nat => True | _ => exists n : Z, 0 <= n <= len /\ PB.uv E (EVar 32) = len - n /\ PMR.u8_feeds PMR.u8_init (firstn (Z.to_nat n) bs) = PMR.u8_init end).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite (EV 2%bv), Hsp; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = s) by (rewrite (EV 10%bv), Ha0; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = len) by (rewrite (EV 11%bv), Ha1; apply u64_of_Z; lia).
  unfold PML.cfg. change PML.PC_VALIDATE with (CC.cp_pc G.cp0).
  eapply (SPUW.pure_leaf_sound_w RSEGS PML.fp_ok FPM G.CPS G.TAGS GT.NF F0 GT.ENDS eq_refl ltac:(unfold GT.NF; lia) G.plans G.tags_ok cut_facts exit_facts0 rets WI
            fx R M model K E0 G.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
  - (* [comment removed for export] *)
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kblob_intro with (bs := bs) (A := s); [ev_start | unfold elenZ; cbn [edenot]; rewrite U11; lia | lia | lia | lia | reflexivity | exact Hbs | rewrite Hbl'; exact Hdefs].
    + sp_unk Hdefs.
    + e_range. + e_range.
    + sp_wr S5.
    + e_range.
    + e_align S1.
    + cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
    + sp_disj.
    + sp_unk S5.
    + e_range.
  - (* [comment removed for export] *) exact I.
  - (* [comment removed for export] *)
    intros i c tags k ps0 j sb E R1 M1 E' R' M' Hc Htags Hps Htag HAt HagE Hfr1 HW Hag HLF HagE' Hfr'.
    pose proof (CH2.leaves_all_sound _ _ _ VKC.leaf_ok i c k ps0 _ (ex_intro _ tags (conj Hc (conj Htags (conj Hps Htag))))) as X. unfold VKC.leaf_chk in X.
    assert (HK : know_ok RSEGS E' M' (SR.ps_cells ps0)) by (unfold know_ok; apply Forall_forall; exact (CC.lf_cells _ _ _ _ _ _ _ HLF)).
    pose proof (CC.cps_all_sound _ _ VKC.nx_ok i c Hc) as Hnx. cbv beta in Hnx. apply Nat.leb_le in Hnx.
    assert (A11 : PB.uv E' (EVar 11) = len) by (rewrite (PB.uv_agree GT.NF E0 E' (EVar 11) HagE' eq_refl); exact U11).
    assert (A10 : PB.uv E' (EVar 10) = s) by (rewrite (PB.uv_agree GT.NF E0 E' (EVar 10) HagE' eq_refl); exact U10).
    destruct i as [|i1].
    + apply andb_prop in X as [Hj Hs32]. apply Nat.eqb_eq in Hj. subst j. apply expr_eqb_eq in Hs32. cbv beta iota. exists 0. split; [lia|].
      split; [|reflexivity]. unfold PB.uv. rewrite <- (CC.esubstL_denot GT.NF sb E' (EVar 32)). cbn [CC.esubstL Nat.ltb Nat.leb GT.NF]. rewrite Hs32. fold (PB.uv E' (EVar 11)). rewrite A11. lia.
    + apply andb_prop in X as [X XG]. apply andb_prop in X as [Hi1 HKI]. apply Nat.eqb_eq in Hi1. injection Hi1 as Hi0. subst i1. cbn [Nat.eqb] in Hnx.
      apply andb_prop in XG as [Hj XG]. apply Nat.eqb_eq in Hj. subst j. destruct (VKC.delta_of sb) as [d|] eqn:Hd; [|discriminate XG].
      unfold VKC.delta_of in Hd. apply find_some in Hd as [Hdin Hd]. apply expr_eqb_eq in Hd. assert (Hd12 : 1 <= d <= 12) by (cbn [In] in Hdin; lia). clear Hdin.
      pose proof (PB.has_ok E' M' _ _ HK HKI) as HKImg.
      cbv beta iota in HW. destruct HW as (n & Hn & HjE & Hfeed).
      assert (A32 : PB.uv E' (EVar 32) = len - n) by (rewrite (PB.uv_agree (CC.cp_nx c) E E' (EVar 32) Hag ltac:(cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; lia)); exact HjE).
      assert (ACUR : PB.uv E' VKW.CUR = s + Z.of_nat (Z.to_nat n)).
      { pose proof A10 as B10. pose proof A11 as B11. pose proof A32 as B32. unfold PB.uv in B10, B11, B32. cbn [edenot] in B10, B11, B32.
        unfold PB.uv, VKW.CUR, VKW.JV. apply CL5.u_lin; [lin_eval; rewrite B10, B11, B32; lia | lia]. }
      assert (HFB : L5.frame_but [(sp - 96, 96)] M M').
      { apply (SP.frame_but_of_outside E0 F0 [(sp - 96, 96)] M M'); [|exact Hfr'].
        intros rb rlo rlen [Hin|[]]; injection Hin as <- <- <-; right.
        exists (sp - 96, 96). split; [left; reflexivity|]. cbn [fst snd].
        assert (Es : estart E0 (SA (EVar 2) (-96)) = sp - 96) by ev_start. assert (El : elenZ E0 (ELit 96) = 96) by ev_len. rewrite Es, El. lia. }
      assert (HBM : L5.bytes_at RSEGS M' s bs).
      { intros q Hq. apply (SPW.u8_frame M M'); [|exact (Hbs q Hq)]. apply HFB. rewrite L5.unsigned_lit by (unfold hl_ceil in *; lia).
        intros rg [<-|[]]. unfold L5.in_rng. cbn [fst snd]. unfold hl_ceil in *. rewrite <- Hbl' in Hs2 || idtac. lia. }
      unfold VKW.goto_chk in XG. destruct (VKW.jrange (SR.ps_cells ps0)) as [[lo hi]|] eqn:Hjr; [|discriminate XG]. apply andb_prop in XG as [XG XS]. apply andb_prop in XG as [Hd1 Hdlo].
      apply Z.leb_le in Hd1. apply Z.leb_le in Hdlo. pose proof (CX.range3_sound RSEGS E' M' _ _ lo hi HK Hjr) as Rj. fold (PB.uv E' VKW.JV) in Rj. change VKW.JV with (EVar 32) in Rj. rewrite A32 in Rj.
      assert (CLEAN : PMR.u8_feeds PMR.u8_init (map (fun k0 => nth (Z.to_nat n + k0) bs 0) (seq 0 (Z.to_nat d - 0))) = PMR.u8_init).
      { apply orb_prop in XS as [XD|XS]; [exfalso; exact (VKW.dead_sound E' M' _ HK HKImg XD)|].
        pose proof (VKW.sim_sound (fun k0 => nth (Z.to_nat n + k0) bs 0) ltac:(intros k0; apply VKW.Forall_nth0; exact Hbi) (VKW.rtab (SR.ps_cells ps0)) (Z.to_nat d)
                      ltac:(intros k0 q Hk0; apply (VKW.rtab_sound E' M' _ s bs (Z.to_nat n) HK HKImg HBM Hbi ACUR); [unfold hl_ceil in *; lia | lia | lia])
                      16 0 0 PMR.u8_init (VKW.WClean (Z.to_nat d)) XS ltac:(constructor) ltac:(lia)) as SS.
        cbv beta iota in SS. exact (proj2 SS). }
      cbv beta iota. exists (n + d). split; [lia|]. split.
      * unfold PB.uv. rewrite <- (CC.esubstL_denot GT.NF sb E' (EVar 32)). cbn [CC.esubstL Nat.ltb Nat.leb GT.NF]. rewrite Hd. fold (PB.uv E' (APC.eaddz VKW.JV (- d))).
        rewrite PB.uv_eaddz. change VKW.JV with (EVar 32). rewrite A32. rewrite Z.mod_small by lia. lia.
      * replace (Z.to_nat (n + d)) with (Z.to_nat n + Z.to_nat d)%nat by lia. rewrite VKW.firstn_add, VKW.u8_feeds_app, Hfeed.
        rewrite <- (VKW.map_nth_seq bs (Z.to_nat d) (Z.to_nat n)) by (rewrite <- (Nat2Z.id (length bs)), Hbl'; lia). rewrite Nat.sub_0_r in CLEAN. exact CLEAN.
  - (* [comment removed for export] *)
    intros fx' i c tags k ps0 id E Rc M1 E' R' M' Hc Htags Hps Htag HAt HW Hag HFP HagE HLF Hfr Hgr Hrp.
    pose proof (CC.others_all_sound _ _ _ exit_facts i c tags k ps0 id Hc Htags Hps Htag) as X. unfold post_chk in X.
    destruct (SP.reg_of ps0 10) as [a0e|] eqn:H10; [|discriminate]. destruct (SP.reg_of ps0 11) as [a1e|] eqn:H11; [|discriminate].
    apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
    assert (HK : know_ok RSEGS E' M' (SR.ps_cells ps0)) by (unfold know_ok; apply Forall_forall; exact (CC.lf_cells _ _ _ _ _ _ _ HLF)).
    pose proof (PB.prove_ok E' M' _ _ HK X1) as R1. pose proof (PB.prove_ok E' M' _ _ HK X2) as R2. pose proof (PB.prove_ok E' M' _ _ HK X3) as R3.
    cbn [kentry_ok] in R1, R2, R3.
    fold (PB.uv E' a1e) in R1. fold (PB.uv E' (APC.esub a0e (EVar 10))) in R2. fold (PB.uv E' (APC.esub (APC.eadd (EVar 10) (EVar 11)) a0e)) in R3.
    rewrite PB.uv_esub in R2, R3. rewrite PB.uv_eadd in R3.
    assert (A10 : PB.uv E' (EVar 10) = s) by (rewrite (PB.uv_agree GT.NF E0 E' (EVar 10) HagE eq_refl); exact U10).
    assert (A11 : PB.uv E' (EVar 11) = len) by (rewrite (PB.uv_agree GT.NF E0 E' (EVar 11) HagE eq_refl); exact U11).
    rewrite A10 in R2, R3. rewrite A11 in R3. rewrite (Z.mod_small (s + len)) in R3 by lia.
    pose proof (PB.uv_range E' a0e) as Hq. set (q := PB.uv E' a0e) in *. unfold LENB in *.
    assert (Hq1 : s <= q <= s + len).
    { destruct (Z_lt_dec q s) as [N|N]; [rewrite (PB.mod_neg_wrap (q - s)) in R2 by lia; lia|]. rewrite Z.mod_small in R2 by lia.
      destruct (Z_lt_dec (s + len) q) as [N2|N2]; [rewrite (PB.mod_neg_wrap (s + len - q)) in R3 by lia; lia | lia]. }
    apply (Hcont fx' R' M' HFP); [| exact Hrp | | exact Hgr].
    + exists q, (PB.uv E' a1e). split; [unfold PML.a0; rewrite (SP.reg_of_sound RSEGS _ _ _ _ _ _ 10%bv _ _ HLF H10 eq_refl); symmetry; apply Z_to_bv_bv_unsigned|].
      split; [rewrite (SP.reg_of_sound RSEGS _ _ _ _ _ _ 11%bv _ _ HLF H11 eq_refl); symmetry; apply Z_to_bv_bv_unsigned|]. split; [exact Hq1|]. split; [lia|].
      (* [comment removed for export] *)
      cbn [PMW.rm_validate PMR.the_rm].
      pose proof (CH2.leaves_all_sound _ _ _ VKC.leaf_ok i c k ps0 _ (ex_intro _ tags (conj Hc (conj Htags (conj Hps Htag))))) as XW. unfold VKC.leaf_chk in XW.
      pose proof (CC.cps_all_sound _ _ VKC.nx_ok i c Hc) as Hnx. cbv beta in Hnx. apply Nat.leb_le in Hnx.
      destruct i as [|i1].
      * (* [comment removed for export] *)
        rewrite H11 in XW. apply andb_prop in XW as [Xe Xz]. apply expr_eqb_eq in Xe. subst a1e.
        pose proof (PB.prove_ok E' M' _ _ HK Xz) as Rz. cbn [kentry_ok] in Rz. fold (PB.uv E' (EVar 11)) in Rz. rewrite A11 in Rz |- *.
        destruct bs as [|b0 br]; [change (PMR.validate []) with 0; lia | cbn [length] in Hbl'; lia].
      * (* [comment removed for export] *)
        cbn [Nat.eqb] in Hnx. apply andb_prop in XW as [XW XE]. apply andb_prop in XW as [_ HKI]. rewrite H11 in XE. destruct a1e as [cv| | | | | | |]; try discriminate XE.
        pose proof (PB.has_ok E' M' _ _ HK HKI) as HKImg.
        cbv beta iota in HW. destruct HW as (n & Hn & HjE & Hfeed).
        assert (A32 : PB.uv E' (EVar 32) = len - n) by (rewrite (PB.uv_agree (CC.cp_nx c) E E' (EVar 32) Hag ltac:(cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; lia)); exact HjE).
        assert (ACUR : PB.uv E' VKW.CUR = s + Z.of_nat (Z.to_nat n)).
        { pose proof A10 as B10. pose proof A11 as B11. pose proof A32 as B32. unfold PB.uv in B10, B11, B32. cbn [edenot] in B10, B11, B32.
          unfold PB.uv, VKW.CUR, VKW.JV. apply CL5.u_lin; [lin_eval; rewrite B10, B11, B32; lia | lia]. }
        assert (HFB : L5.frame_but [(sp - 96, 96)] M M').
        { apply (SP.frame_but_of_outside E0 F0 [(sp - 96, 96)] M M'); [|exact Hfr].
          intros rb rlo rlen [Hin|[]]; injection Hin as <- <- <-; right.
          exists (sp - 96, 96). split; [left; reflexivity|]. cbn [fst snd].
          assert (Es : estart E0 (SA (EVar 2) (-96)) = sp - 96) by ev_start. assert (El : elenZ E0 (ELit 96) = 96) by ev_len. rewrite Es, El. lia. }
        assert (HBM : L5.bytes_at RSEGS M' s bs).
        { intros q0 Hq0. apply (SPW.u8_frame M M'); [|exact (Hbs q0 Hq0)]. apply HFB. rewrite L5.unsigned_lit by (unfold hl_ceil in *; lia).
          intros rg [<-|[]]. unfold L5.in_rng. cbn [fst snd]. unfold hl_ceil in *. lia. }
        pose (ab := fun k0 : nat => nth (Z.to_nat n + k0) bs 0).
        assert (Hab : forall k0, VKW.inb (ab k0)) by (intros k0; apply VKW.Forall_nth0; exact Hbi).
        unfold VKW.exit_chk in XE. destruct (VKW.jrange (SR.ps_cells ps0)) as [[lo hi]|] eqn:Hjr; [|discriminate XE].
        pose proof (CX.range3_sound RSEGS E' M' _ _ lo hi HK Hjr) as Rj. fold (PB.uv E' VKW.JV) in Rj. change VKW.JV with (EVar 32) in Rj. rewrite A32 in Rj.
        apply orb_prop in XE as [XD|XE]; [exfalso; exact (VKW.dead_sound E' M' _ HK HKImg XD)|].
        assert (HRT : forall av, Z.of_nat av <= Z.min (len - n) 13 -> forall k0 q0, (k0 < av)%nat -> In (VKW.canonq q0 (ab k0)) (VKW.rget (VKW.rtab (SR.ps_cells ps0)) k0 q0)).
        { intros av Hav k0 q0 Hk0. apply (VKW.rtab_sound E' M' _ s bs (Z.to_nat n) HK HKImg HBM Hbi ACUR); [unfold hl_ceil in *; lia | lia | lia]. }
        (* [comment removed for export] *)
        assert (HV : PMR.validate bs = PMR.u8_finish (VKW.arun ab PMR.u8_init 0 (Z.to_nat (len - n)))).
        { rewrite (VKW.validate_split (Z.to_nat n) bs) by (rewrite VKW.b256_firstn, (VKW.b256_id bs Hbi); exact Hfeed).
          rewrite VKW.b256_skipn, (VKW.b256_id bs Hbi), (VKW.skipn_as_map bs (Z.to_nat n)) by lia. unfold VKW.arun. rewrite Nat.sub_0_r.
          replace (length bs - Z.to_nat n)%nat with (Z.to_nat (len - n)) by lia. reflexivity. }
        assert (FINERR : forall m, (m <= Z.to_nat (len - n))%nat -> PMR.u_err (VKW.arun ab PMR.u8_init 0 m) <> 0 -> PMR.validate bs = PMR.u_err (VKW.arun ab PMR.u8_init 0 m)).
        { intros m Hm He. rewrite HV, (arun_split ab PMR.u8_init m _ Hm), (VKW.u8_feeds_err _ _ He). unfold PMR.u8_finish.
          replace (negb (PMR.u_err (VKW.arun ab PMR.u8_init 0 m) =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; exact He). reflexivity. }
        destruct (Z.eqb_spec cv 5) as [->|N5].
        { (* [comment removed for export] *)
          apply andb_prop in XE as [XE XP]. apply andb_prop in XE as [Hhi Hlo]. apply Z.leb_le in Hhi. apply Z.leb_le in Hlo.
          rewrite forallb_forall in XP. specialize (XP (len - n) (VKW.range_vals_in lo hi (len - n) ltac:(lia))).
          pose proof (HRT (Z.to_nat (len - n)) ltac:(lia)) as HRT1.
          pose proof (VKW.sim_sound ab Hab _ (Z.to_nat (len - n)) HRT1 16 0 0 PMR.u8_init VKW.WPend XP ltac:(constructor) ltac:(lia)) as SS. cbv beta iota in SS.
          destruct SS as [Se Sp]. rewrite PB2.uv_lit by lia. rewrite HV. unfold PMR.u8_finish. rewrite Se. cbn [Z.eqb negb].
          destruct (PMR.u_pend _); [exfalso; exact (Sp eq_refl) | reflexivity]. }
        destruct (Z.eqb_spec cv 0) as [->|N0].
        { (* [comment removed for export] *)
          apply andb_prop in XE as [XE XS]. apply andb_prop in XE as [XE Hlo2]. apply andb_prop in XE as [Hhl Hlo]. apply Z.eqb_eq in Hhl. apply Z.leb_le in Hlo. apply Z.leb_le in Hlo2. subst hi.
          pose proof (HRT (Z.to_nat lo) ltac:(lia)) as HRT1.
          pose proof (VKW.sim_sound ab Hab _ (Z.to_nat lo) HRT1 16 0 0 PMR.u8_init (VKW.WClean (Z.to_nat lo)) XS ltac:(constructor) ltac:(lia)) as SS. cbv beta iota in SS.
          destruct SS as [_ Sc]. rewrite PB2.uv_lit by lia. rewrite HV. replace (len - n) with lo by lia. rewrite Sc. reflexivity. }
        (* [comment removed for export] *)
        apply andb_prop in XE as [Hlo XS]. apply Z.leb_le in Hlo.
        pose proof (HRT (Z.to_nat (Z.min lo 13)) ltac:(lia)) as HRT1.
        pose proof (VKW.sim_sound ab Hab _ (Z.to_nat (Z.min lo 13)) HRT1 16 0 0 PMR.u8_init (VKW.WErr cv) XS ltac:(constructor) ltac:(lia)) as SS. cbv beta iota in SS.
        destruct SS as (Hc0 & m & Hm & Hem). rewrite (FINERR m ltac:(lia) ltac:(rewrite Hem; exact Hc0)), Hem.
        pose proof (u8_feeds_err_range PMR.u8_init (map ab (seq 0 (m - 0))) ltac:(cbn; lia)) as Hcr. fold (VKW.arun ab PMR.u8_init 0 m) in Hcr. rewrite Hem in Hcr.
        rewrite PB2.uv_lit by lia. reflexivity.
    + apply (SP.frame_but_of_outside E0 F0 [(sp - 96, 96)] M M'); [|exact Hfr].
      intros rb rlo rlen [Hin|[]]; injection Hin as <- <- <-; right.
      exists (sp - 96, 96). split; [left; reflexivity|]. cbn [fst snd].
      assert (Es : estart E0 (SA (EVar 2) (-96)) = sp - 96) by ev_start. assert (El : elenZ E0 (ELit 96) = 96) by ev_len. rewrite Es, El. lia.
Qed.
End S.
End ValidateProof.
Print Assumptions ValidateProof.validate_okw.
