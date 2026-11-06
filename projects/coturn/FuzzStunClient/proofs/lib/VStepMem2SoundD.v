(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VStepSound VStepMemSound VStepMemSound2 VState2 VStepMem2 VGamma2 VStepMem2SoundA VStepMem2SoundB VStepMem2SoundC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section D.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variable mem0 : word -> option byte.
  Let P1 := p1 P.
  Let E1 := ev1 E.
  Hypothesis PO2 : params_ok2 SEGS P.

  Notation gamma2P := (gamma2 SEGS P E mem0).

  (* [comment removed for export] *)
  Definition dd_ext (A : vstate2) (nu1 : val) (b : positive) (dd' : pmap (lin * Z)) : Prop :=
    forall q x m, pm_get q dd' = Some (x, m) ->
      pm_get q (vs_divdef A) = Some (x, m)
      \/ (0 < m /\ nu1 q = Z.div (eval nu1 x) m /\ (q < b)%positive /\ lin_below x b = true).

  Lemma dd_ext_refl A nu1 b : dd_ext A nu1 b (vs_divdef A).
  Proof. intros q x m H. left; exact H. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma gamma2_transfer_dd A A1' nu nu' regs regs' mem dd' :
    gamma2P A nu regs mem ->
    ext (vs_next (v1 A)) nu nu' -> (vs_next (v1 A) <= vs_next A1')%positive ->
    gamma SEGS P1 E1 (zpatch P E mem0 mem) A1' nu' regs' mem ->
    vs_globs A1' = vs_globs (v1 A) ->
    dd_ext A nu' (vs_next A1') dd' ->
    gamma2P (mkVS2 A1' (vs_rgn A) (vs_live A) dd' (vs_memo A)) nu' regs' mem.
  Proof.
    intros HG2 X Hle G1' EG DD.
    pose proof HG2 as (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & GL & FI2 & _).
    pose proof (gamma2_transfer SEGS P E mem0 PO2 A A1' nu nu' regs regs' mem mem HG2 X Hle (frame_mod_refl _ _) G1'
                  ltac:(unfold globs_ok2; cbn [v1 with_v1]; rewrite EG; exact GL) (or_introl eq_refl)) as T.
    pose proof T as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4|]. split.
    { intros q x m Hq. cbn [vs_divdef] in Hq. destruct (DD q x m Hq) as [OLD|(M & Q & _ & _)]; [|split; [exact M|exact Q]].
      exact (T5 q x m OLD). }
    split; [exact T6|]. split; [exact T7|]. split; [|exact T9].
    destruct T8 as (BF & BR & BL & BD & BM). cbn [v1 vs_rgn vs_live vs_divdef vs_memo with_v1] in BF, BR, BL, BD, BM |- *.
    split; [exact BF|]. split; [exact BR|]. split; [exact BL|]. split; [|exact BM].
    intros q x m Hq. destruct (DD q x m Hq) as [OLD|(M & Q & B1 & B2)]; [exact (BD q x m OLD)|auto].
  Qed.

  (* [comment removed for export] *)
  Lemma value_post2 A nu regs mem pc rom (rd : reg) (wl : word) e A1v dd' nu1 :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc -> rz rd <> 0 ->
    aext (v1 A) A1v nu nu1 -> lgamma A1v nu1 ->
    bv_unsigned wl = zwrap 64 (eval nu1 e) -> lin_below e (vs_next A1v) = true ->
    dd_ext A nu1 (vs_next A1v) dd' ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd wl) (v_addi pc 4) mem rom) ->
    step_post2 SEGS P E mem0 A nu [mkVS2 (finish A1v (rz rd) (Some e)) (vs_rgn A) (vs_live A) dd' (vs_memo A)] regs mem pc rom.
  Proof.
    intros HG2 Hpc Hrd X HL1 Hw Hb DD ST.
    pose proof HG2 as (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & GL & FI2 & _).
    pose proof X as (X1 & X2 & SH).
    pose proof (gamma_upd SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) A1v nu nu1 regs mem rd wl (Some e) (npc_of A1v) G1 X HL1 Hrd
                  ltac:(split; [exact Hw|exact Hb])) as G1'.
    exists (regupd regs rd wl), (v_addi pc 4), mem, (mkVS2 (finish A1v (rz rd) (Some e)) (vs_rgn A) (vs_live A) dd' (vs_memo A)), nu1.
    split; [exact ST|]. split; [left; reflexivity|]. split.
    { unfold vs2_pc, finish. cbn [v1]. unfold npc_of, v_addi. rewrite u_Z_to_bv64, wrap64_zwrap.
      destruct SH as (_ & _ & _ & _ & SP & _). unfold set_reg. destruct (Z.eqb (rz rd) 0); cbn; rewrite SP; unfold vs2_pc in Hpc; rewrite Hpc; reflexivity. }
    split; [exact X1|]. split.
    { unfold vs2_next, finish, set_reg. cbn [v1]. destruct (Z.eqb (rz rd) 0); cbn; exact X2. }
    split; [apply frame_mod_refl|]. split.
    { intros a Ha. left. split; [|reflexivity].
      change (own_flags (mkVS2 (finish A1v (rz rd) (Some e)) (vs_rgn A) (vs_live A) dd' (vs_memo A)) nu1) with (own_flags A nu1).
      rewrite (own_flags_ext A nu nu1 X1 BEL2). tauto. }
    apply (gamma2_transfer_dd A _ nu nu1 regs _ mem dd' HG2 X1).
    - unfold finish, set_reg. destruct (Z.eqb (rz rd) 0); cbn; exact X2.
    - exact G1'.
    - destruct SH as (_ & _ & SG & _). unfold finish, set_reg. destruct (Z.eqb (rz rd) 0); cbn; exact SG.
    - unfold finish, set_reg. destruct (Z.eqb (rz rd) 0); cbn; exact DD.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma lin_below_lterm k s n : (s < n)%positive -> lin_below (lterm k s) n = true.
  Proof.
    intros H. apply (proj2 (lin_below_iff _ _)). unfold lterm. destruct (Z.eqb k 0); cbn; [tauto|].
    intros s' [<-|[]]. exact H.
  Qed.

  Lemma divdef_find_in l x m q :
    divdef_find l x m = Some q -> exists x', In (q, (x', m)) l /\ lin_eqb x' x = true.
  Proof.
    induction l as [|[q0 [x0 m0]] t IH]; simpl; [discriminate|].
    destruct (Z.eqb_spec m0 m); simpl.
    - destruct (lin_eqb x0 x) eqn:LE; simpl.
      + intros H; injection H as <-. subst. exists x0. auto.
      + intros H. destruct (IH H) as (x' & Hin & Hle). exists x'. auto.
    - intros H. destruct (IH H) as (x' & Hin & Hle). exists x'. auto.
  Qed.

  Lemma floor_div_bounds X m : 0 < m -> m * (X / m) <= X <= m * (X / m) + (m - 1).
  Proof. intros Hm. pose proof (Z.div_mod X m ltac:(lia)). pose proof (Z.mod_pos_bound X m Hm). lia. Qed.

  Lemma fdivm_sound A nu x m q A1 :
    lgamma (v1 A) nu -> gamma_divdef nu A -> state_below2 A ->
    0 < m -> lin_below x (vs_next (v1 A)) = true ->
    fdivm A x m = Some (q, A1) ->
    exists nu1, aext (v1 A) (v1 A1) nu nu1 /\ lgamma (v1 A1) nu1 /\
      eval nu1 q = eval nu x / m /\ lin_below q (vs_next (v1 A1)) = true /\
      vs_rgn A1 = vs_rgn A /\ vs_live A1 = vs_live A /\ vs_memo A1 = vs_memo A /\ dd_ext A nu1 (vs_next (v1 A1)) (vs_divdef A1).
  Proof.
    intros HL DIV BEL Hm Bx F. unfold fdivm in F.
    destruct (lin_is_const x) eqn:CX.
    { injection F as <- <-. exists nu. split; [apply aext_refl|]. split; [exact HL|].
      split; [rewrite eval_lconst, (eval_is_const nu x CX); reflexivity|]. split; [apply lin_below_lconst|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. apply dd_ext_refl. }
    destruct (Z.eqb m 8 && ldivisible x 8) eqn:EX.
    { apply andb_prop in EX as [M8 LD]. apply Z.eqb_eq in M8. subst m.
      injection F as <- <-. exists nu. split; [apply aext_refl|]. split; [exact HL|].
      split; [change 8 with (2 ^ 3); apply lshiftr_eval; [lia|exact LD]|]. split; [apply lin_below_lshiftr; exact Bx|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. apply dd_ext_refl. }
    destruct (divdef_find (pm_elements (vs_divdef A)) x m) as [q0|] eqn:FD.
    { injection F as <- <-. apply divdef_find_in in FD as (x' & Hin & Hle). apply pm_elements_correct in Hin.
      destruct (DIV q0 x' m Hin) as [M0 Hq0]. destruct BEL as (_ & _ & _ & BD & _). destruct (BD q0 x' m Hin) as [Q1 Q2].
      exists nu. split; [apply aext_refl|]. split; [exact HL|].
      split; [rewrite eval_lsym, Hq0, (lin_eqb_sound nu x' x Hle); reflexivity|]. split; [apply lin_below_lsym; exact Q1|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. apply dd_ext_refl. }
    (* [comment removed for export] *)
    set (s := vs_next (v1 A)) in *.
    set (bq := (match fst (lp_bounds (vs_store (v1 A)) x) with Some lo => Some (lo / m) | None => None end,
                match snd (lp_bounds (vs_store (v1 A)) x) with Some hi => Some (hi / m) | None => None end)) in *.
    set (A2 := set_next (set_store (v1 A) (store_set_box (vs_store (v1 A)) s bq)) (Pos.succ s)) in *.
    destruct (aassume A2 (lsub (lterm m s) x)) as [ok1 A3] eqn:E3.
    destruct (aassume A3 (laddc (lsub x (lterm m s)) (- (m - 1)))) as [ok2 A4] eqn:E4.
    destruct (ok1 && ok2) eqn:OK; [|discriminate]. injection F as <- <-. cbn [v1 vs_rgn vs_live vs_divdef vs_memo].
    set (X := eval nu x). set (nu1 := vupd nu s (X / m)).
    assert (EXT : ext s nu nu1) by (intros s' Hs'; unfold nu1; apply vupd_other; lia).
    assert (EX1 : eval nu1 x = X) by (unfold X; apply (eval_ext_below s); [exact EXT|exact Bx]).
    assert (ITV : in_itv (X / m) bq).
    { pose proof (lp_bounds_sound nu (vs_store (v1 A)) (lgamma_sat _ _ HL) x) as [B1 B2]. unfold bq, in_itv. cbn [fst snd].
      destruct (lp_bounds (vs_store (v1 A)) x) as [[lo|] [hi|]]; cbn [fst snd lo_le hi_ge] in B1, B2 |- *;
        repeat split; try exact I; try (apply Z.div_le_mono; unfold X in *; lia). }
    assert (HL2 : lgamma A2 nu1) by exact (proj1 (lgamma_fresh (v1 A) nu (X / m) bq HL ITV)).
    assert (N2 : vs_next A2 = Pos.succ s) by reflexivity.
    pose proof (floor_div_bounds X m Hm) as [F1 F2].
    pose proof (aassume_sound A2 nu1 (lsub (lterm m s) x) HL2
                  ltac:(rewrite eval_lsub, eval_lterm, EX1; unfold nu1; rewrite vupd_same; lia)
                  ltac:(rewrite N2; apply lin_below_lsub; [apply lin_below_lterm; lia|eapply lin_below_mono; [|exact Bx]; lia])) as (OK1 & HL3 & X3).
    rewrite E3 in OK1, HL3, X3. cbn [fst snd] in OK1, HL3, X3. subst ok1.
    pose proof (aassume_next A2 (lsub (lterm m s) x)) as N3. rewrite E3 in N3. cbn [snd] in N3. rewrite N2 in N3.
    pose proof (aassume_sound A3 nu1 (laddc (lsub x (lterm m s)) (- (m - 1))) HL3
                  ltac:(rewrite eval_laddc, eval_lsub, eval_lterm, EX1; unfold nu1; rewrite vupd_same; lia)
                  ltac:(rewrite N3; apply lin_below_laddc, lin_below_lsub; [eapply lin_below_mono; [|exact Bx]; lia|apply lin_below_lterm; lia])) as (OK2 & HL4 & X4).
    rewrite E4 in OK2, HL4, X4. cbn [fst snd] in OK2, HL4, X4. subst ok2.
    pose proof (aassume_next A3 (laddc (lsub x (lterm m s)) (- (m - 1)))) as N4. rewrite E4 in N4. cbn [snd] in N4. rewrite N3 in N4.
    exists nu1. split.
    { eapply aext_trans; [|eapply aext_trans; [exact X3|exact X4]].
      split; [exact EXT|]. split; [rewrite N2; lia|]. repeat split; reflexivity. }
    split; [exact HL4|]. split; [rewrite eval_lsym; unfold nu1; rewrite vupd_same; reflexivity|].
    split; [rewrite N4; apply lin_below_lsym; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros q' x' m' Hq. rewrite pm_get_set in Hq. destruct (Pos.eqb_spec q' s) as [->|NE]; [|left; exact Hq].
    injection Hq as <- <-. right. split; [exact Hm|]. split; [unfold nu1 at 1; rewrite vupd_same, EX1; reflexivity|].
    rewrite N4. split; [lia|]. eapply lin_below_mono; [|exact Bx]. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma comp_sound A nu regs mem B B8 :
    gamma2P A nu regs mem -> comp A B = Some B8 -> nu B8 = nu B / 8 /\ (B8 < vs_next (v1 A))%positive.
  Proof.
    intros HG2 HC. pose proof HG2 as (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & GL & FI2).
    pose proof (gamma_fix2_fix _ _ FIX2) as FIX1. pose proof BEL2 as (BF & _ & _ & BD & _). unfold LAST_FIXED2 in BF.
    unfold comp in HC. unfold env_comp in HC.
    destruct (Pos.eqb_spec B SP0) as [->|N1].
    { injection HC as <-. split; [|unfold SP8; lia]. rewrite (nu_SP8 _ _ _ _ _ _ _ _ HG2), (nu_SP0 (ev1 E) nu FIX1). reflexivity. }
    destruct (Pos.eqb_spec B DATA) as [->|N2].
    { injection HC as <-. split; [|unfold DATA8; lia]. rewrite (nu_DATA8 _ _ _ _ _ _ _ _ HG2), (nu_DATA (ev1 E) nu FIX1). reflexivity. }
    destruct (Pos.eqb_spec B FSB) as [->|N3].
    { injection HC as <-. split; [|unfold FS8; lia]. rewrite (nu_FSB _ _ _ _ _ _ _ _ HG2).
      apply FIX2. unfold fix_val2. replace (fix_val (ev1 E) FS8) with (@None Z) by reflexivity. reflexivity. }
    set (cand := match fixed_comp B with Some c => Some c | None => match rgn_get (vs_rgn A) B with Some r => vr_b8 r | None => None end end) in HC.
    destruct cand as [c|]; [|discriminate].
    destruct (divdef_is A c (lsym B) 8) eqn:DI; [|discriminate]. injection HC as <-.
    unfold divdef_is in DI. destruct (pm_get c (vs_divdef A)) as [[x' m']|] eqn:G; [|discriminate].
    apply andb_prop in DI as [M8 LE]. apply Z.eqb_eq in M8. subst m'.
    destruct (DIV c x' 8 G) as [_ Hc]. destruct (BD c x' 8 G) as [Q1 _].
    split; [|exact Q1]. rewrite Hc, (lin_eqb_sound nu x' (lsym B) LE), eval_lsym. reflexivity.
  Qed.

  Lemma base_res8_sound A nu B rB :
    lgamma (v1 A) nu -> base_res8 A B = Some rB -> 0 <= rB < 8 /\ exists k, nu B = 8 * k + rB.
  Proof.
    intros HL H. unfold base_res8 in H.
    destruct (pm_get B (scong (vs_store (v1 A)))) as [[m r]|] eqn:G; [|discriminate].
    destruct (negb (m =? 0) && (m mod 8 =? 0)) eqn:C; [|discriminate]. injection H as <-.
    apply andb_prop in C as [C1 C2]. apply negb_true_iff in C1. apply Z.eqb_neq in C1. apply Z.eqb_eq in C2.
    pose proof (sat_cong _ _ (lgamma_sat _ _ HL) B m r G) as [k Hk].
    apply Z.mod_divide in C2; [|lia]. destruct C2 as [j Hj].
    split; [apply Z.mod_pos_bound; lia|].
    exists (k * j + r / 8). pose proof (Z.div_mod r 8 ltac:(lia)). nia.
  Qed.

  Lemma split_base_inv A ea B B8 e :
    split_base A ea = Some (B, B8, e) -> comp A B = Some B8 /\ lcoef ea B = 1 /\ e = lsub ea (lsym B) /\ In B (lsyms ea).
  Proof.
    unfold split_base.
    destruct (List.filter _ (lsyms ea)) as [|B0 [|]] eqn:F; try discriminate.
    destruct (Z.eqb_spec (lcoef ea B0) 1); [|discriminate].
    destruct (comp A B0) as [c|] eqn:HC; [|discriminate]. intros H; injection H as <- <- <-.
    repeat split; auto. assert (X : In B0 (B0 :: nil)) by (left; reflexivity). rewrite <- F in X. apply filter_In in X. tauto.
  Qed.

  Lemma finish2_eq A1 rd v :
    finish2 A1 rd v = mkVS2 (finish (v1 A1) rd v) (vs_rgn A1) (vs_live A1) (vs_divdef A1) (vs_memo A1).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="P1 E1 PO2"] Lemma x_srl3_sound A nu regs mem pc rom w (rd rs1 : reg) (sh : bv 6) r :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (ShiftImm ALU_SRL rd rs1 sh, 4) ->
    rz rd <> 0 -> bv_unsigned sh = 3 ->
    x_srl3 A (rz rd) (rz rs1) = Some r -> forall succs, r = VR2_next succs ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
  Proof.
    intros HG2 Hpc Hf He Hd Hrd Hsh HX succs ->.
    pose proof HG2 as (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & GL & FI2).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (gamma_get_reg SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem rs1 G1) as [Wa Ba].
    assert (Hbe : bv_eqb rd 0%bv = false) by (rewrite bv_eqb_rz; destruct (Z.eqb_spec (rz rd) 0); [contradiction|reflexivity]).
    unfold x_srl3, get_reg2 in HX.
    destruct (get_reg (v1 A) (rz rs1)) as [ea|] eqn:Hea; [|discriminate].
    pose proof (wval_some _ _ _ Wa) as Ua. cbn [vbelow] in Ba.
    pose proof (u64_range (getr regs rs1)) as UR.
    (* [comment removed for export] *)
    assert (ST : RiscvSemantics.step SEGS (mkst regs pc mem rom)
                 = MachineOk (mkst (regupd regs rd (Z_to_bv 64 (bv_unsigned (getr regs rs1) / 8))) (v_addi pc 4) mem rom)).
    { eapply step_srli_at; eauto. unfold v_srli. rewrite Hsh, Z.shiftr_div_pow2 by lia. reflexivity. }
    destruct (split_base A ea) as [[[B B8] e]|] eqn:SB.
    - (* [comment removed for export] *)
      destruct (split_base_inv A ea B B8 e SB) as (HC & HK & -> & HinB).
      destruct (base_res8 A B) as [rB|] eqn:BR; [|discriminate].
      destruct (inU (v1 A) ea) eqn:IU; cbn [negb] in HX; [|discriminate].
      destruct (fdiv8 A (anorm (v1 A) (laddc (lsub ea (lsym B)) rB))) as [[q A1]|] eqn:FD; [|injection HX as HX1; discriminate].
      injection HX as HX1. cbn [one2] in HX1. first [subst succs | injection HX1 as <-].
      pose proof (inU_sound _ _ _ HL IU) as EU.
      destruct (base_res8_sound A nu B rB HL BR) as [RB1 [kB HkB]].
      destruct (comp_sound A nu regs mem B B8 HG2 HC) as [HB8 LB8].
      assert (BB : (B < vs_next (v1 A))%positive) by exact (proj1 (lin_below_iff ea _) Ba B HinB).
      unfold fdiv8 in FD.
      destruct (fdivm_sound A nu (anorm (v1 A) (laddc (lsub ea (lsym B)) rB)) 8 q A1 HL DIV BEL2 ltac:(lia)
                  ltac:(apply anorm_below, lin_below_laddc, lin_below_lsub; [exact Ba|apply lin_below_lsym; exact BB]) FD)
        as (nu1 & X & HL1 & Eq & Bq & ER & EL & EM & DD).
      rewrite finish2_eq, ER, EL, EM.
      pose proof X as (X1 & X2 & _).
      eapply (value_post2 A nu regs mem pc rom rd _ _ (v1 A1) (vs_divdef A1) nu1 HG2 Hpc Hrd X HL1); [| |exact DD|exact ST].
      + rewrite u_Z_to_bv64. f_equal.
        rewrite (anorm_sound _ _ _ HL1), eval_ladd, eval_lsym, Eq, (anorm_sound _ _ _ HL), eval_laddc, eval_lsub, eval_lsym.
        rewrite X1 by exact LB8. rewrite HB8, Ua, (zwrap_id 64 (eval nu ea)) by (ltac2:(LK.k [@UR; @EU; @RB1]); lia). rewrite HkB.
        replace (8 * kB + rB) with (rB + kB * 8) by lia. rewrite Z.div_add by lia. rewrite (Z.div_small rB 8) by (ltac2:(LK.k [@UR; @EU; @RB1]); lia).
        replace (eval nu ea - (rB + kB * 8) + rB) with (eval nu ea + (- kB) * 8) by lia. rewrite Z.div_add by lia. lia.
      + apply anorm_below, lin_below_ladd; [apply lin_below_lsym; lia|exact Bq].
    - (* [comment removed for export] *)
      destruct (has_base A ea || lin_is_const ea || negb (inU (v1 A) ea)) eqn:C; [discriminate|].
      apply orb_false_iff in C as [C IU]. apply orb_false_iff in C as [_ NC]. apply negb_false_iff in IU.
      destruct (lp_bounds (vs_store (v1 A)) ea) as [[lo|] [hi|]]; try discriminate.
      destruct (Z.ltb (2 ^ 20) (hi - lo)); [discriminate|].
      destruct (fdiv8 A (anorm (v1 A) ea)) as [[q A1]|] eqn:FD; [|injection HX as HX1; discriminate].
      injection HX as HX1. cbn [one2] in HX1. first [subst succs | injection HX1 as <-].
      pose proof (inU_sound _ _ _ HL IU) as EU.
      unfold fdiv8 in FD.
      destruct (fdivm_sound A nu (anorm (v1 A) ea) 8 q A1 HL DIV BEL2 ltac:(lia) ltac:(apply anorm_below; exact Ba) FD)
        as (nu1 & X & HL1 & Eq & Bq & ER & EL & EM & DD).
      rewrite finish2_eq, ER, EL, EM.
      eapply (value_post2 A nu regs mem pc rom rd _ _ (v1 A1) (vs_divdef A1) nu1 HG2 Hpc Hrd X HL1); [| exact Bq |exact DD|exact ST].
      rewrite u_Z_to_bv64. f_equal. rewrite Eq, (anorm_sound _ _ _ HL), Ua, (zwrap_id 64 (eval nu ea)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma x_and7_sound A nu regs mem pc rom w (rd rs1 : reg) (imm : bv 12) r :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (OpImm ALU_AND rd rs1 imm, 4) ->
    rz rd <> 0 -> bv_signed imm = 7 ->
    x_and7 A (rz rd) (rz rs1) = Some r -> forall succs, r = VR2_next succs ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
  Proof.
    intros HG2 Hpc Hf He Hd Hrd Himm HX succs ->.
    pose proof HG2 as (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & GL & FI2).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (gamma_get_reg SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem rs1 G1) as [Wa Ba].
    assert (Hbe : bv_eqb rd 0%bv = false) by (rewrite bv_eqb_rz; destruct (Z.eqb_spec (rz rd) 0); [contradiction|reflexivity]).
    unfold x_and7, get_reg2 in HX.
    destruct (get_reg (v1 A) (rz rs1)) as [ea|] eqn:Hea; [|discriminate].
    pose proof (wval_some _ _ _ Wa) as Ua. cbn [vbelow] in Ba.
    pose proof (u64_range (getr regs rs1)) as UR.
    destruct (split_base A ea) as [[[B B8] e]|] eqn:SB; [|discriminate].
    destruct (split_base_inv A ea B B8 e SB) as (HC & HK & -> & HinB).
    destruct (base_res8 A B) as [rB|] eqn:BR; [|discriminate].
    set (x8 := anorm (v1 A) (laddc (lsub ea (lsym B)) rB)) in HX.
    destruct (lin_is_const x8); [discriminate|].
    destruct (lin_cong (scong (vs_store (v1 A))) x8) as [m0 r0].
    destruct (negb (m0 =? 0) && (m0 mod 8 =? 0)); [discriminate|].
    destruct (inU (v1 A) ea) eqn:IU; cbn [negb] in HX; [|discriminate].
    destruct (fdiv8 A x8) as [[q A1]|] eqn:FD; [|injection HX as HX1; discriminate].
    injection HX as HX1. cbn [one2] in HX1. first [subst succs | injection HX1 as <-].
    pose proof (inU_sound _ _ _ HL IU) as EU.
    destruct (base_res8_sound A nu B rB HL BR) as [RB1 [kB HkB]].
    assert (BB : (B < vs_next (v1 A))%positive) by exact (proj1 (lin_below_iff ea _) Ba B HinB).
    assert (Bx8 : lin_below x8 (vs_next (v1 A)) = true).
    { unfold x8. apply anorm_below, lin_below_laddc, lin_below_lsub; [exact Ba|apply lin_below_lsym; exact BB]. }
    unfold fdiv8 in FD.
    destruct (fdivm_sound A nu x8 8 q A1 HL DIV BEL2 ltac:(lia) Bx8 FD) as (nu1 & X & HL1 & Eq & Bq & ER & EL & EM & DD).
    rewrite finish2_eq, ER, EL, EM. pose proof X as (X1 & X2 & _).
    assert (EX8 : eval nu x8 = eval nu ea - nu B + rB).
    { unfold x8. rewrite (anorm_sound _ _ _ HL), eval_laddc, eval_lsub, eval_lsym. reflexivity. }
    eapply (value_post2 A nu regs mem pc rom rd _ _ (v1 A1) (vs_divdef A1) nu1 HG2 Hpc Hrd X HL1);
      [| |exact DD|eapply step_andi_at; eauto].
    - unfold v_andi. rewrite u_Z_to_bv64. f_equal.
      rewrite (anorm_sound _ _ _ HL1), eval_lsub, eval_lscale, Eq, (eval_ext_below _ _ _ _ X1 Bx8), EX8.
      rewrite Ua, (zwrap_id 64 (eval nu ea)) by lia.
      change (bv_wrap 64 (bv_signed imm)) with (zwrap 64 (bv_signed imm)). rewrite Himm. change (zwrap 64 7) with (Z.ones 3).
      rewrite Z.land_ones by lia. rewrite HkB.
      replace (eval nu ea - (8 * kB + rB) + rB) with (eval nu ea + (- kB) * 8) by lia.
      rewrite Z.div_add by lia. change (2 ^ 3) with 8.
      pose proof (Z.div_mod (eval nu ea) 8 ltac:(lia)). lia.
    - apply anorm_below, lin_below_lsub; [eapply lin_below_mono; [exact X2|exact Bx8]|apply lin_below_lscale; exact Bq].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="P1 E1 PO2"] Lemma x_srl_magic_sound A nu regs mem pc rom w (rd rs1 : reg) (sh : bv 6) r :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (ShiftImm ALU_SRL rd rs1 sh, 4) ->
    rz rd <> 0 ->
    x_srl_magic A (rz rd) (rz rs1) (bv_unsigned sh) = Some r -> forall succs, r = VR2_next succs ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
  Proof.
    intros HG2 Hpc Hf He Hd Hrd HX succs ->.
    pose proof HG2 as (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & GL & FI2).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (gamma_get_reg SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem rs1 G1) as [Wa Ba].
    assert (Hbe : bv_eqb rd 0%bv = false) by (rewrite bv_eqb_rz; destruct (Z.eqb_spec (rz rd) 0); [contradiction|reflexivity]).
    pose proof (bv_unsigned_in_range 6 sh) as Hsh. unfold bv_modulus in Hsh. simpl in Hsh.
    unfold x_srl_magic, get_reg2 in HX.
    destruct (get_reg (v1 A) (rz rs1)) as [ea|] eqn:Hea; [|discriminate].
    pose proof (wval_some _ _ _ Wa) as Ua. cbn [vbelow] in Ba.
    pose proof (u64_range (getr regs rs1)) as UR.
    destruct (negb (lc ea =? 0) || has_base A ea || negb (inU (v1 A) ea)) eqn:C; [discriminate|].
    apply orb_false_iff in C as [C IU]. apply orb_false_iff in C as [C0 _]. apply negb_false_iff in IU. apply negb_false_iff in C0. apply Z.eqb_eq in C0.
    destruct (lin_single ea) as [[x c]|] eqn:LS; [|discriminate].
    destruct (Z.leb_spec c 1); [discriminate|].
    destruct (lp_bounds (vs_store (v1 A)) (lsym x)) as [[lo|] [hi|]] eqn:LB; try discriminate.
    destruct (Z.ltb lo 0 || Z.ltb 4096 (hi - lo) || Z.leb (2 ^ 40) hi || Z.ltb hi lo) eqn:W; [discriminate|].
    set (d := (2 ^ bv_unsigned sh + c / 2) / c) in HX.
    destruct (Z.leb_spec d 1); [discriminate|].
    destruct (magic_ok c (bv_unsigned sh) d lo (S (Z.to_nat (hi - lo)))) eqn:MG; cbn [negb] in HX; [|discriminate].
    destruct (fdivm A (lsym x) d) as [[q A1]|] eqn:FD; [|injection HX as HX1; discriminate].
    injection HX as HX1. cbn [one2] in HX1. first [subst succs | injection HX1 as <-].
    pose proof (inU_sound _ _ _ HL IU) as EU.
    pose proof (eval_single nu ea x c LS) as Eea. rewrite C0 in Eea.
    assert (Hx : In x (lsyms ea)).
    { unfold lin_single in LS. unfold lsyms. destruct (lt ea) as [|[s' k'] [|]]; try discriminate. injection LS as -> ->. left; reflexivity. }
    assert (BX : (x < vs_next (v1 A))%positive) by exact (proj1 (lin_below_iff ea _) Ba x Hx).
    pose proof (lp_bounds_sound nu (vs_store (v1 A)) (lgamma_sat _ _ HL) (lsym x)) as QB.
    rewrite LB, eval_lsym in QB. destruct QB as [Q1 Q2]. cbn [fst snd lo_le hi_ge] in Q1, Q2.
    apply orb_false_iff in W as [W W4]. apply orb_false_iff in W as [W W3]. apply orb_false_iff in W as [W1 W2].
    apply Z.ltb_ge in W1. apply Z.ltb_ge in W2. apply Z.leb_gt in W3. apply Z.ltb_ge in W4.
    (* [comment removed for export] *)
    unfold magic_ok in MG. rewrite forallb_forall in MG.
    specialize (MG (nu x) ltac:(apply zrange_in; lia)). cbn beta in MG. apply Z.eqb_eq in MG.
    destruct (fdivm_sound A nu (lsym x) d q A1 HL DIV BEL2 ltac:(lia) ltac:(apply lin_below_lsym; exact BX) FD)
      as (nu1 & X & HL1 & Eq & Bq & ER & EL & EM & DD).
    rewrite finish2_eq, ER, EL, EM.
    eapply (value_post2 A nu regs mem pc rom rd _ _ (v1 A1) (vs_divdef A1) nu1 HG2 Hpc Hrd X HL1);
      [|exact Bq|exact DD|eapply step_srli_at; eauto].
    unfold v_srli. rewrite u_Z_to_bv64. f_equal. rewrite Eq, eval_lsym, <- MG, Ua, (zwrap_id 64 (eval nu ea)), Eea by (ltac2:(LK.k [@Hsh; @UR; @EU]); lia).
    f_equal; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition XSPLIT_stmt : Prop :=
    forall A nu regs mem pc rom w (rd rs1 : reg) (sh : bv 6) r,
      gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
      fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (ShiftImm ALU_SRL rd rs1 sh, 4) ->
      rz rd <> 0 -> x_srl_split A (rz rd) (rz rs1) (bv_unsigned sh) = Some r ->
      forall succs, r = VR2_next succs -> step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
  Hypothesis XSTACK : XSTACK_stmt SEGS P E mem0.
  Hypothesis XINSTALL : XINSTALL_stmt SEGS P E mem0.
  Hypothesis XSPLIT : XSPLIT_stmt.

  Lemma lift_case A nu regs mem pc rom w i succs :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    lift1 A (vstep (p1 P) (v1 A) i) = VR2_next succs -> forallb (globs_in_fcells P) succs = true ->
    not_store i ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
  Proof.
    intros HG2 Hpc Hf He Hd Hx GLB NS. apply lift1_next_inv in Hx as (l & Hl & ->).
    eapply lift1_sound; eauto. intros x Hxl. rewrite forallb_forall in GLB. apply GLB. apply in_map. exact Hxl.
  Qed.

  Theorem vstep2_sound A nu regs mem pc rom w i succs :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    vstep2 P A i = VR2_next succs ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
  Proof.
    intros HG2 Hpc Hf He Hd Hx.
    apply check_globs_next in Hx as [Hx GLB].
    unfold vstep2_raw in Hx.
    destruct (asan_mode P); cbn [negb] in Hx.
    - destruct i as [ | | | | |sz sg rd rs1 imm|sz rs1 rs2 imm|op rd rs1 imm|op rd rs1 sh| | | | | | | | | | | | | | | | | | | | | | | | | | ];
        rewrite ?bvs_eq in Hx;   (* [comment removed for export] *)
        try (eapply lift_case; eauto; exact I).
      + eapply x_load2_sound; eauto.
      + eapply x_store2_sound; eauto.
      + (* [comment removed for export] *)
        destruct op; try (eapply lift_case; eauto; exact I).
        destruct (negb (rz rd =? 0) && (bv_signed imm =? 7)) eqn:C; [|eapply lift_case; eauto; exact I].
        apply andb_prop in C as [C1 C2]. apply negb_true_iff in C1. apply Z.eqb_neq in C1. apply Z.eqb_eq in C2.
        destruct (x_and7 A (rz rd) (rz rs1)) as [r|] eqn:X7; [|eapply lift_case; eauto; exact I].
        subst r. eapply x_and7_sound; eauto.
      + (* [comment removed for export] *)
        destruct op; try (eapply lift_case; eauto; exact I).
        destruct (Z.eqb_spec (rz rd) 0) as [Z0|NZ]; [eapply lift_case; eauto; exact I|].
        destruct (if bv_unsigned sh =? 3 then x_srl3 A (rz rd) (rz rs1) else None) as [r|] eqn:X3.
        * destruct (Z.eqb_spec (bv_unsigned sh) 3); [|discriminate]. subst r. eapply x_srl3_sound; eauto.
        * destruct (x_srl_magic A (rz rd) (rz rs1) (bv_unsigned sh)) as [r|] eqn:XM.
          { subst r. eapply x_srl_magic_sound; eauto. }
          destruct (x_srl_split A (rz rd) (rz rs1) (bv_unsigned sh)) as [r|] eqn:XS; [|eapply lift_case; eauto; exact I].
          eapply XSPLIT; eauto.
    - destruct i; rewrite ?bvs_eq in Hx; try (eapply lift_case; eauto; exact I).
      + eapply x_load2_sound; eauto.
      + eapply x_store2_sound; eauto.
  Qed.
End D.

(* [comment removed for export] *)
Theorem vstep2_sound_iface (SEGS : list Segment) :
  (forall P E mem0, params_ok2 SEGS P -> XSTACK_stmt SEGS P E mem0) ->
  (forall P E mem0, params_ok2 SEGS P -> XINSTALL_stmt SEGS P E mem0) ->
  (forall P E mem0, params_ok2 SEGS P -> XSPLIT_stmt SEGS P E mem0) ->
  forall P E mem0 rom A i succs nu regs mem (pc : word) w,
    params_ok2 SEGS P ->
    vstep2 P A i = VR2_next succs ->
    gamma2 SEGS P E mem0 A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
Proof. intros XS XI XP. intros. eapply vstep2_sound; eauto. Qed.
