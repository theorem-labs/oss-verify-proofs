(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VStep VStepMem VStepSound VStepMemSound VCert VItab VDriverMatch VContract VDriver VSoundMatch VSound VSoundStep VSoundCall VSoundCall2 VSoundContract VState2 VStepMem2 VCert2 VContract2 VDriverMatch2 VDriver2 VGamma2 VStepMem2SoundA VSound2 VSoundStep2 VContract2Iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

Section Contract2.
  Variable SEGS : list Segment.
  Variable G : genv2.
  Variable rom : word -> option byte.
  Variable done : list vunit2.
  Variable U : vunit2.
  Variable E : venv2.
  Variables mem0 mem_e : word -> option byte.

  Let D := mk_denv2 G done U.
  Let P := unit_params2 G U.
  Let G1 := genv1_of G.
  Local Notation gammaP := (gamma2 SEGS P E mem0).
  Local Notation gammaPE := (gammaE SEGS G U E mem0 mem_e).

  Hypothesis CTAB2 : ctab_sound2 SEGS P E mem0 rom (ge2_CI G) (ge2_ctab G).
  Hypothesis RET : ret_ok (wordZ (unit_ret2 U E)).
  Hypothesis STATIC : unit_static_ok2 G P U = None.
  Hypothesis VSTEP2 : forall A i succs nu regs mem (pc : word) w,
    vstep2 P A i = VR2_next succs ->
    gammaP A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
  Hypothesis MATCH : forall A X pc ctx sigma nu regs mem,
    gammaP A nu regs mem ->
    cstate2_ok P X = true ->
    match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 P X pc ctx) A = MOk sigma ->
    gammaP (load_cstate2 P X pc ctx) (vsubst nu sigma) regs mem /\ ext FIRST_FRESH2 nu (vsubst nu sigma)
    /\ (forall a, In a (own_flags (load_cstate2 P X pc ctx) (vsubst nu sigma)) <-> In a (own_flags A nu)).

  Lemma vs_globs_set_reg (X : vstate) r v : vs_globs (set_reg X r v) = vs_globs X.
  Proof. unfold set_reg. destruct (Z.eqb r 0); reflexivity. Qed.

  Lemma vs_globs_set_pc (X : vstate) p : vs_globs (set_pc X p) = vs_globs X.
  Proof. destruct X; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma gamma2_set_reg1 A2 nu' regs' mem' (v : absval) :
    gammaP A2 nu' regs' mem' ->
    (forall e, v = Some e -> bv_unsigned (getr regs' 1%bv) = zwrap 64 (eval nu' e) /\ lin_below e (vs2_next A2) = true) ->
    gammaP (set_reg2 A2 1 v) nu' regs' mem'.
  Proof.
    intros HG2 Hv.
    pose proof HG2 as (HV1 & HE & HM & HF & HDD & HRG & HL & HB & HGL & HFI & HMM).
    split; [|split; [exact HE|split; [exact HM|split; [exact HF|split; [exact HDD|split; [exact HRG|split; [exact HL|split; [|split; [|split; [exact HFI|exact HMM]]]]]]]]]].
    - unfold set_reg2, with_v1. cbn [v1].
      exact (gamma_set_reg1 SEGS G1 (u1 U) (ev1 E) _ (v1 A2) nu' regs' mem' v HV1 Hv).
    - destruct HB as (B0 & B1 & B2 & B3 & B4). unfold set_reg2, with_v1, state_below2. cbn [v1 vs_rgn vs_live vs_divdef vs_memo].
      rewrite vs_next_set_reg. auto.
    - unfold globs_ok2 in *. unfold set_reg2, with_v1. cbn [v1]. rewrite vs_globs_set_reg. exact HGL.
  Qed.

  Lemma own_flags_with_v1 A B nu : own_flags (with_v1 A B) nu = own_flags A nu.
  Proof. reflexivity. Qed.

  Lemma flags_step_regs A A1 A2 nu nu' mem mem' :
    vs_rgn A1 = vs_rgn A2 ->
    flags_step P E A A1 nu nu' mem mem' -> flags_step P E A A2 nu nu' mem mem'.
  Proof. intros ER H. unfold flags_step, own_flags in *. rewrite <- ER. exact H. Qed.

  Lemma flags_step_refl A nu mem : flags_step P E A A nu nu mem mem.
  Proof. intros a _. left. split; [tauto|reflexivity]. Qed.


  Lemma get_reg_v1_set_reg2 A r v : 0 < r -> get_reg (v1 (set_reg2 A r v)) r = v.
  Proof. intros Hr. unfold set_reg2, with_v1. cbn [v1]. apply get_reg_set_reg_same. exact Hr. Qed.

  Lemma vs_ctx_v1_set_reg2 A r v : vs_ctx (v1 (set_reg2 A r v)) = vs_ctx (v1 A).
  Proof. unfold set_reg2, with_v1, set_reg. cbn [v1]. destruct (Z.eqb r 0); [reflexivity|]. destruct v; reflexivity. Qed.

  Lemma collect_sn2_in {T} (f : T -> sres2) : forall l succs x,
    collect_sn2 (map f l) = SN2 succs -> In x l -> exists s, f x = SN2 s /\ incl s succs.
  Proof.
    induction l as [|y t IH]; intros succs x H Hin; [destruct Hin|]. cbn [map collect_sn2] in H.
    destruct (f y) as [s|m] eqn:Fy; [|discriminate].
    destruct (collect_sn2 (map f t)) as [s'|m] eqn:Ct; [|discriminate]. injection H as <-.
    destruct Hin as [<-|Hin].
    - exists s. split; [exact Fy|]. apply incl_appl, incl_refl.
    - destruct (IH s' x eq_refl Hin) as (s0 & F0 & I0). exists s0. split; [exact F0|]. apply incl_appr. exact I0.
  Qed.

  #[using="P G1 CTAB2 RET STATIC VSTEP2 MATCH"] Theorem contract2_sound A c (rd : reg) (imm : bv 21) succs nu regs mem (pc : word) w :
    do_contract2 D A c (rz rd) (npc_of (v1 A)) = SN2 succs ->
    (if Z.ltb 0 (wrap64 (vs2_pc A + bv_signed imm))
     then pm_get (zkey (wrap64 (vs2_pc A + bv_signed imm))) (ge2_ctab G) else None) = Some c ->
    (FIRST_FRESH2 <= vs2_next A)%positive ->
    gammaPE A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Jal rd imm, 4) ->
    dstep_post2 SEGS G rom U E mem0 mem_e A succs nu regs pc mem.
  Proof.
    intros Hx Hct HJ [HG HFI] Hpc Hf He Hd.
    set (tgt := wrap64 (vs2_pc A + bv_signed imm)) in *. set (npc := npc_of (v1 A)) in *.
    destruct (Z.ltb_spec 0 tgt) as [Htgt|]; [|discriminate].
    destruct (CTAB2 tgt c Htgt Hct) as [POST DEAD].
    unfold do_contract2 in Hx. change (de2_P D) with P in Hx. change (de2_G D) with G in Hx. change (de2_U D) with U in Hx.
    destruct (Z.eqb (rz rd) 0 || Z.eqb (rz rd) 1) eqn:RD; [|discriminate]. cbn [negb] in Hx.
    set (tail := Z.eqb (rz rd) 0) in *.
    set (A'0 := if tail then A else set_reg2 A 1 (Some (lconst npc))) in *.
    set (A' := clear_memo A'0) in *.
    change (sp_offset (v1 A')) with (sp_offset (v1 A'0)) in Hx.
    destruct (sp_offset (v1 A'0)) as [spoff|] eqn:SPO; [|discriminate].
    destruct (negb (Z.eqb (contract2_K c) 0) && negb (in_ranges (vp_wstack (p1 P)) (spoff - contract2_K c) (contract2_K c))) eqn:KW; [discriminate|].
    assert (KW' : contract2_K c = 0 \/ in_ranges (vp_wstack (p1 P)) (spoff - contract2_K c) (contract2_K c) = true).
    { destruct (Z.eqb_spec (contract2_K c) 0); [now left|]. right. cbn [negb andb] in KW. destruct (in_ranges _ _ _); [reflexivity|discriminate]. }
    assert (NPC : 0 <= npc < 2 ^ 64) by (unfold npc, npc_of; rewrite wrap64_zwrap; apply zwrap64_range).
    (* [comment removed for export] *)
    assert (Ej : vstep2 P A (Jal rd imm) = VR2_next [with_v1 A (set_pc (set_reg (v1 A) (rz rd) (Some (lconst npc))) tgt)]).
    { apply vstep2_of_raw; [unfold vstep2_raw; destruct (asan_mode P); reflexivity|].
      cbn [forallb]. rewrite (globs_in_fcells_same P A); [now rewrite (gamma2_globs_in_fcells _ _ _ _ _ _ _ _ HG : globs_in_fcells P A = true)|].
      cbn [v1 with_v1]. now rewrite vs_globs_set_pc, vs_globs_set_reg. }
    destruct (VSTEP2 _ _ _ _ _ _ _ _ Ej HG Hpc Hf He Hd) as (regs1 & pc1 & mem1 & A1j & nu1 & Hst & Hin1 & Hpc1 & X1 & L1 & FM1 & FL1 & HG1).
    destruct Hin1 as [<-|[]]. cbn [vs2_pc v1 with_v1 vs_pc set_pc] in Hpc1.
    assert (HG1' : gammaP A'0 nu1 regs1 mem1 /\ vs2_next A'0 = vs2_next A /\ vs_rgn A'0 = vs_rgn A).
    { assert (GP : forall X p nu r m, gammaP (with_v1 A (set_pc X p)) nu r m -> gammaP (with_v1 A X) nu r m).
      { intros X p nu0 r m HH. destruct X. exact HH. }
      apply GP in HG1.
      unfold A'0, tail. destruct (Z.eqb_spec (rz rd) 0) as [R0|R0].
      - rewrite R0 in HG1. unfold set_reg in HG1. cbn [Z.eqb] in HG1.
        assert (EA : with_v1 A (v1 A) = A) by (destruct A; reflexivity). rewrite EA in HG1.
        split; [exact HG1|split; reflexivity].
      - apply Bool.orb_prop in RD as [RD|RD]; [unfold tail in RD; first [discriminate | apply Z.eqb_eq in RD; lia]|].
        apply Z.eqb_eq in RD. rewrite RD in HG1.
        split; [exact HG1|]. split; [unfold set_reg2, vs2_next, with_v1; cbn [v1]; apply vs_next_set_reg|reflexivity]. }
    destruct HG1' as (HG1'0 & NX'0 & RG'0).
    assert (HG1' : gammaP A' nu1 regs1 mem1) by (unfold A'; apply gamma2_clear_memo; exact HG1'0).
    assert (NX' : vs2_next A' = vs2_next A) by exact NX'0.
    assert (RG' : vs_rgn A' = vs_rgn A) by exact RG'0.
    assert (MM' : vs_memo A' = []) by reflexivity.
    assert (FLA' : flags_step P E A A' nu nu1 mem mem1).
    { eapply flags_step_regs; [|exact FL1]. cbn [vs_rgn with_v1]. symmetry. exact RG'. }
    destruct (contract_apply2 P (ge2_CI G) c A' spoff) as [ol| |m] eqn:CA; [|exfalso; exact (DEAD _ _ _ _ _ CA HG1')|discriminate].
    assert (GR1 : forall e, get_reg (v1 A') 1 = Some e -> bv_unsigned (getr regs1 1%bv) = zwrap 64 (eval nu1 e) /\ lin_below e (vs2_next A') = true).
    { intros e He1. pose proof (gamma2_v1 _ _ _ _ _ _ _ _ HG1') as HV. pose proof HV as (_&_&_&_&_&_&_&HR1&_&_&_&HB1). destruct HB1 as (_&_&RB1&_).
      unfold get_reg in He1. cbn [Z.eqb] in He1. split; [apply (HR1 1%bv e); [discriminate|exact He1]|exact (RB1 _ _ He1)]. }
    (* [comment removed for export] *)
    assert (MAIN : forall ra, getr regs1 1%bv = ra -> ret_ok ra ->
              exists A1 v regs' mem' nu', let A2 := contract_frame2 c A1 spoff v in
                   In (A1, v) ol
                /\ msteps SEGS (mkst regs pc mem rom) (mkst regs' ra mem' rom)
                /\ gammaPE (set_reg2 A2 1 (get_reg (v1 A') 1)) nu' regs' mem'
                /\ getr regs' 1%bv = ra
                /\ ext (vs2_next A) nu nu' /\ (vs2_next A <= vs2_next (set_reg2 A2 1 (get_reg (v1 A') 1)))%positive
                /\ frame_mod mem mem' (unit_regions2 P E)).
    { intros ra Hra Hok.
      destruct (POST A' spoff ol nu1 regs1 mem1 ra CA HG1' MM' (sp_offset_get _ _ SPO) KW' Hok Hra)
        as (A1 & v & regs' & mem' & nu' & HinO & Hrun & HG2 & Hra' & X2 & L2 & FM2 & FL2).
      exists A1, v, regs', mem', nu'. cbv zeta. set (A2 := contract_frame2 c A1 spoff v) in *. split; [exact HinO|]. split.
      { eapply msteps_trans; [eapply msteps_one; [reflexivity|exact Hst]|].
        replace pc1 with (wordZ tgt); [exact Hrun|]. rewrite <- (wordZ_u pc1), <- Hpc1. reflexivity. }
      split.
      { split.
        - apply (gamma2_set_reg1 A2 nu' regs' mem' (get_reg (v1 A') 1) HG2). intros e Hge. destruct (GR1 e Hge) as [Q1 Q2]. split.
          + rewrite Hra', <- Hra, Q1. f_equal. symmetry. exact (eval_ext_below _ _ _ _ X2 Q2).
          + eapply lin_below_mono; [exact L2|exact Q2].
        - eapply fl_inv_step; [eapply fl_inv_step; [exact HFI|exact FLA']|].
          eapply flags_step_regs; [|exact FL2]. reflexivity. }
      split; [exact Hra'|]. split; [|split].
      - eapply (ext_trans (vs2_next A) (vs2_next A)); [lia|exact X1|]. rewrite <- NX'. exact X2.
      - replace (vs2_next (set_reg2 A2 1 (get_reg (v1 A') 1))) with (vs2_next A2) by (unfold set_reg2, vs2_next, with_v1; cbn [v1]; symmetry; apply vs_next_set_reg). rewrite <- NX'. exact L2.
      - eapply frame_mod_trans_same; [exact FM1|exact FM2]. }
    change (de2_U D) with U in Hx.
    destruct ol as [|o1 ol']; [discriminate|].
    (* [comment removed for export] *)
    assert (OUT : forall A1 v, In (A1, v) (o1 :: ol') ->
              exists s, after_return2 D (set_reg2 (contract_frame2 c A1 spoff v) 1 (get_reg (v1 A') 1)) tail npc = SN2 s /\ incl s succs).
    { intros A1 v Hin. exact (collect_sn2_in _ _ _ _ Hx Hin). }
    clear Hx.
    (* [comment removed for export] *)
    destruct (OUT (fst o1) (snd o1) ltac:(left; destruct o1; reflexivity)) as (s0 & H0 & _).
    unfold after_return2 in H0. change (de2_U D) with U in H0.
    rewrite !get_reg_v1_set_reg2 in H0 by lia. rewrite !vs_ctx_v1_set_reg2 in H0.
    assert (GS : forall X nu0 r m, gammaPE X nu0 r m -> forall p, gammaPE (set_pc2 X p) nu0 r m).
    { intros X nu0 r m HH p. destruct X as [Xv rg lv dd]. destruct Xv. exact HH. }
    assert (GC : forall X nu0 r m, gammaPE X nu0 r m -> forall cx, gammaPE (set_ctx2 X cx) nu0 r m).
    { intros X nu0 r m HH cx. destruct X as [Xv rg lv dd]. destruct Xv. exact HH. }
    assert (CTXF : forall A1 v, vs_ctx (v1 (contract_frame2 c A1 spoff v)) = vs_ctx (v1 A1)).
    { intros A1 v. unfold contract_frame2, with_v1. cbn [v1]. generalize (v1 A1). intros X. unfold frame_rule.
      assert (SR : forall Y r a, vs_ctx (set_reg Y r a) = vs_ctx Y) by (intros Y r a; unfold set_reg; destruct (Z.eqb r 0); [reflexivity|]; destruct a; reflexivity).
      assert (KN : forall Y lo hi a, vs_ctx (kill_nul Y lo hi a) = vs_ctx Y).
      { intros Y lo hi a. unfold kill_nul. destruct (vs_nul Y); [reflexivity|]. destruct (is_zero_val Y a); reflexivity. }
      rewrite SR, set_tops_eq. cbn [vs_ctx set_regs]. destruct (Z.eqb (contract2_K c) 0); [reflexivity|]. rewrite KN. reflexivity. }
    unfold tail in *. destruct (Z.eqb_spec (rz rd) 0) as [R0|R0].
    - (* [comment removed for export] *)
      cbn [negb] in H0.
      pose proof (rz_is0 rd ltac:(apply Z.eqb_eq; exact R0)) as Erd.
      assert (Eregs : regs1 = regs /\ mem1 = mem).
      { rewrite Erd in Hd. pose proof (step_jal_x0 SEGS regs pc mem rom w imm Hf He Hd) as Hst'.
        rewrite Hst in Hst'. inversion Hst'. auto. }
      destruct Eregs as [-> ->].
      destruct (ra_is_exit2 U (get_reg (v1 A') 1)) eqn:RX.
      + (* [comment removed for export] *)
        assert (R1 : getr regs 1%bv = wordZ (unit_ret2 U E)).
        { eapply (ra_is_exit_sound SEGS G1 (u1 U) (ev1 E) _ (v1 A')); [exact (gamma2_v1 _ _ _ _ _ _ _ _ HG1')|reflexivity|exact RX]. }
        destruct (MAIN _ R1 RET) as (A1 & v & regs' & mem' & nu' & HinO & Hrun & HG3 & Hra' & X3 & L3 & FM3).
        destruct (OUT _ _ HinO) as (s1 & Hx & INCL).
        set (A2 := contract_frame2 c A1 spoff v) in *. unfold after_return2 in Hx. change (de2_U D) with U in Hx. cbn [negb] in Hx.
        rewrite !get_reg_v1_set_reg2 in Hx by lia. rewrite !vs_ctx_v1_set_reg2 in Hx. rewrite RX in Hx.
        destruct (vs_ctx (v1 A2)); [|discriminate].
        destruct (unit_exit2_exit SEGS G done U E mem0 mem_e STATIC MATCH _ _ _ _ _ Hx
                    ltac:(rewrite get_reg_v1_set_reg2 by lia; exact RX) HG3)
          as (-> & _ & XR & X & nu'' & HinX & HGX & EXT & FLX).
        right. exists regs', mem'. split; [exact Hrun|].
        exists X, nu''. split; [exact HinX|]. split; [exact HGX|]. split.
        { eapply (ext_trans FIRST_FRESH2 FIRST_FRESH2); [lia|eapply ext_mono; [exact HJ|exact X3]|exact EXT]. }
        split; [exact Hra'|]. split; [|split; [exact FM3|exact FLX]].
        eapply exit_regs2_ext; [eapply ext_mono; [exact HJ|exact X3]|exact XR].
      + (* [comment removed for export] *)
        destruct (get_reg (v1 A') 1) as [e|] eqn:Gr1; [|discriminate].
        destruct (lin_is_const e) eqn:Hc; [|discriminate].
        destruct (Z.eqb (lc e mod 2) 0 && Z.leb 0 (lc e) && Z.ltb (lc e) (2 ^ 64)) eqn:CK; [|discriminate]. cbn [negb] in H0.
        apply andb_prop in CK as [CK C3]. apply andb_prop in CK as [C1 C2].
        apply Z.eqb_eq in C1. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
        assert (R1 : getr regs 1%bv = wordZ (lc e)).
        { destruct (GR1 e eq_refl) as [R1 _]. rewrite (eval_is_const _ _ Hc) in R1. rewrite zwrap64_id in R1 by (ltac2:(LK.k [@NPC; @NX'0; @NX'; @C2; @C3]); lia).
          rewrite <- (wordZ_u (getr regs 1%bv)). now rewrite R1. }
        assert (ROK : ret_ok (wordZ (lc e))) by (apply ret_ok_even; rewrite u_wordZ by lia; exact C1).
        destruct (MAIN _ R1 ROK) as (A1 & v & regs' & mem' & nu' & HinO & Hrun & HG3 & Hra' & X3 & L3 & FM3).
        destruct (OUT _ _ HinO) as (s1 & Hx & INCL).
        set (A2 := contract_frame2 c A1 spoff v) in *. unfold after_return2 in Hx. change (de2_U D) with U in Hx. cbn [negb] in Hx.
        rewrite !get_reg_v1_set_reg2 in Hx by (ltac2:(LK.k [@NPC; @NX'0; @NX'; @C2]); lia). rewrite !vs_ctx_v1_set_reg2 in Hx. rewrite RX, Hc in Hx.
        rewrite (proj2 (andb_true_iff _ _) (conj (proj2 (andb_true_iff _ _) (conj (proj2 (Z.eqb_eq _ _) C1) (proj2 (Z.leb_le _ _) C2))) (proj2 (Z.ltb_lt _ _) C3))) in Hx.
        cbn [negb] in Hx.
        destruct (vs_ctx (v1 A2)) as [|c' rest] eqn:CTX; [discriminate|].
        destruct (Z.eqb_spec c' (lc e)); [|discriminate]. injection Hx as <-. subst c'.
        left. exists regs', (wordZ (lc e)), mem', (set_ctx2 (set_pc2 (set_reg2 A2 1 (Some e)) (lc e)) rest), nu'.
        split; [exact Hrun|]. split; [apply INCL; now left|]. split; [cbn; rewrite u_wordZ by lia; reflexivity|].
        split; [exact X3|]. split; [exact L3|]. split; [exact FM3|].
        apply GC. apply GS. exact HG3.
    - (* [comment removed for export] *)
      assert (Gr1 : get_reg (v1 A') 1 = Some (lconst npc)).
      { unfold A'. unfold set_reg2, with_v1. cbn [v1]. apply get_reg_set_reg_same. lia. }
      assert (R1 : getr regs1 1%bv = wordZ npc).
      { destruct (GR1 _ Gr1) as [R1 _]. rewrite eval_lconst, zwrap64_id in R1 by lia.
        rewrite <- (wordZ_u (getr regs1 1%bv)). now rewrite R1. }
      assert (ROK : ret_ok (wordZ npc)).
      { apply ret_ok_even. rewrite u_wordZ by lia. unfold npc, npc_of. rewrite wrap64_zwrap, zwrap64_mod2.
        pose proof (fetch_word_even SEGS pc w Hf) as Ev. unfold vs2_pc in Hpc. rewrite <- Hpc in Ev.
        replace (vs_pc (v1 A) + 4) with (vs_pc (v1 A) + 2 * 2) by lia. rewrite Z_mod_plus_full. exact Ev. }
      destruct (MAIN _ R1 ROK) as (A1 & v & regs' & mem' & nu' & HinO & Hrun & HG3 & Hra' & X3 & L3 & FM3).
      destruct (OUT _ _ HinO) as (s1 & Hx & INCL).
      set (A2 := contract_frame2 c A1 spoff v) in *. unfold after_return2 in Hx. cbn [negb] in Hx. injection Hx as <-.
      left. exists regs', (wordZ npc), mem', (set_pc2 (set_reg2 A2 1 (get_reg (v1 A') 1)) npc), nu'.
      split; [exact Hrun|]. split; [apply INCL; now left|]. split; [cbn; rewrite u_wordZ by lia; reflexivity|].
      split; [exact X3|]. split; [exact L3|]. split; [exact FM3|].
      apply GS. exact HG3.
  Qed.
End Contract2.
