(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GGran GGranP.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM StepS PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GChk.

Definition no_store (fi : finstr) : bool :=
  match fi with
  | IJal _ _ | IBranch _ _ _ _ | ILoad _ _ _ _ _ | IOpImm _ _ _ _ | IOp _ _ _ _ => true
  | _ => false
  end.

Definition frame (st st' : sstate) : Prop :=
  s_ff st' = s_ff st /\ s_resv st' = s_resv st /\ s_regs st' = s_regs st /\ s_ops st' = s_ops st /\ s_priv st' = s_priv st /\ s_next st' = s_next st.
Lemma frame_refl : forall st, frame st st. Proof. intros st. repeat split. Qed.
Lemma frame_trans : forall a b c, frame a b -> frame b c -> frame a c.
Proof. intros a b c (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6). repeat split; congruence. Qed.
Lemma frame_setpc : forall st pc, frame st (setpc st pc). Proof. intros st pc. repeat split. Qed.
Lemma frame_setr : forall st r v, frame st (setr st r v). Proof. intros st r v. unfold setr. destruct r; repeat split. Qed.

Fixpoint havoc_rf (x : rf sv) (l : list r5) (n : int) : rf sv :=
  match l with [] => x | r :: l' => havoc_rf (rf_set x r (VP n wzero)) l' (PrimInt63.add n 1%uint63) end.
Fixpoint env_havoc (E : env) (vs : list word) (n : int) : env :=
  match vs with [] => E | v :: vs' => env_havoc (env_upd E n v) vs' (PrimInt63.add n 1%uint63) end.

Section Join.
Variable segs : list Segment.
Variable ARMS : sstate -> option (list sstate).
Variable G_PC : int.
Variable PC_OK : int.
Variable HV : list r5.
Variable RL : list r5.
Variable FUEL : nat.

Fixpoint crun (fuel : nat) (st : sstate) : option sstate :=
  if PrimInt63.eqb (s_pc st) PC_OK then Some st else
  match fuel with
  | O => None
  | S f =>
      match decode_at segs (s_pc st) with
      | Some fi =>
          if no_store fi then
            match step segs (IMap.add (s_pc st) fi IMap.empty) st with
            | SOk st' => crun f st'
            | SStop _ _ => None
            end
          else None
      | None => None
      end
  end.

Definition base_of (st b : sstate) : sstate :=
  SS (s_pc b) (s_rf b) (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) (s_next st).

Definition restore (st b : sstate) : sstate := fold_left (fun acc r => setr acc r (getr st r)) RL b.
Definition restorable (a b : sstate) : bool := forallb (fun r => negb (r5_eqb r X0) && sv_eqb (getr b r) (getr a r)) RL.

Definition arm_ok (st : sstate) (rfW : rf sv) (a : sstate) : bool :=
  match crun FUEL a with
  | Some b => restorable a b
              && st_vars_below (s_next st) (base_of st (restore st b))
              && rf_forallb2 sv_eqb (havoc_rf (s_rf (restore st b)) HV (s_next st)) rfW
  | None => false
  end.

Definition joined (st : sstate) (rfW : rf sv) : sstate :=
  SS PC_OK rfW (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st)
     (PrimInt63.add (s_next st) (Uint63.of_Z (Z.of_nat (length HV)))).

Definition gchk_apply (st : sstate) : option (list sstate) :=
  match ARMS st with
  | Some (a1 :: arms') =>
      match crun FUEL a1 with
      | Some b1 =>
          let rfW := havoc_rf (s_rf (restore st b1)) HV (s_next st) in
          if forallb (fun r => negb (r5_eqb r X0)) HV
             && PrimInt63.ltb 0%uint63 (s_next st)
             && Z.ltb (to_Z (s_next st) + Z.of_nat (length HV)) 4611686018427387904
             && forallb (arm_ok st rfW) (a1 :: arms')
          then Some [joined st rfW] else None
      | None => None
      end
  | _ => None
  end.

Definition gchk_contract : contract := Contract G_PC gchk_apply.

Section Sound.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Hypothesis ARMS_CASES : forall st arms E ms model, ARMS st = Some arms -> st_ok segs OPS E st ms model ->
  exists a, In a arms /\ st_ok segs OPS E a ms model.
Hypothesis ARMS_FRAME : forall st arms a, ARMS st = Some arms -> In a arms -> frame st a.

Lemma exec_frame : forall fi st st', no_store fi = true -> exec segs fi st = XOk st' -> frame st st'.
Proof.
  intros fi st st' NS H. destruct fi; try discriminate NS; unfold exec in H.
  - destruct (pc_add (s_pc st) off); [|discriminate]. injection H as <-. eapply frame_trans; [apply frame_setr| apply frame_setpc].
  - destruct (decide_branch_t (s_facts st) c (getr st rs1) (getr st rs2)) as [[|]|]; [| |discriminate].
    + destruct (pc_add (s_pc st) off); [|discriminate]. injection H as <-. apply frame_setpc.
    + injection H as <-. apply frame_setpc.
  - destruct (do_load segs st (sv_alu ALU_ADD (getr st rs1) (VL off)) (msize_bytes sz) sx) as [[v|]|k]; try discriminate.
    injection H as <-. eapply frame_trans; [apply frame_setr| apply frame_setpc].
  - injection H as <-. eapply frame_trans; [apply frame_setr| apply frame_setpc].
  - injection H as <-. eapply frame_trans; [apply frame_setr| apply frame_setpc].
Qed.

Lemma single_itab_ok : forall pc fi, decode_at segs pc = Some fi -> itab_ok segs (IMap.add pc fi IMap.empty).
Proof.
  intros pc fi D pc' fi' F. destruct (PrimInt63.eqb pc pc') eqn:Q.
  - apply Uint63.eqb_correct in Q. subst pc'. rewrite IMap.find_add_same in F by exact IMap.bst_empty. injection F as <-. exact D.
  - rewrite IMap.find_add_other_eqb in F by (exact IMap.bst_empty || exact Q). rewrite IMap.find_empty in F. discriminate.
Qed.

Lemma crun_sound : forall fuel E a b ms model, crun fuel a = Some b -> st_ok segs OPS E a ms model ->
  exists ms' model', asteps segs ms model ms' model' /\ st_ok segs OPS E b ms' model' /\ s_pc b = PC_OK /\ frame a b.
Proof.
  induction fuel as [|f IH]; intros E a b ms model H HS; cbn [crun] in H.
  - destruct (PrimInt63.eqb (s_pc a) PC_OK) eqn:Q; [|discriminate]. injection H as <-. apply Uint63.eqb_correct in Q.
    exists ms, model. split; [apply ast_refl|]. split; [exact HS|]. split; [exact Q| apply frame_refl].
  - destruct (PrimInt63.eqb (s_pc a) PC_OK) eqn:Q.
    + injection H as <-. apply Uint63.eqb_correct in Q.
      exists ms, model. split; [apply ast_refl|]. split; [exact HS|]. split; [exact Q| apply frame_refl].
    + destruct (decode_at segs (s_pc a)) as [fi|] eqn:D; [|discriminate]. destruct (no_store fi) eqn:NS; [|discriminate].
      destruct (step segs (IMap.add (s_pc a) fi IMap.empty) a) as [a'|why a'] eqn:ST; [|discriminate].
      destruct (step_sound_a segs OPS E a ms model _ a' (single_itab_ok _ _ D) HS ST) as (ms1 & mo1 & STEP & HS1).
      assert (FR : frame a a').
      { unfold step in ST. destruct (PrimInt63.ltb (s_pc a) bit62i); [|discriminate].
        rewrite IMap.find_add_same in ST by exact IMap.bst_empty.
        destruct (exec segs fi a) as [x|w] eqn:X; [|discriminate]. injection ST as <-. exact (exec_frame fi a x NS X). }
      destruct (IH E a' b ms1 mo1 H HS1) as (ms' & mo' & AS & HSb & PCb & FRb).
      exists ms', mo'. split; [| split; [exact HSb| split; [exact PCb| exact (frame_trans _ _ _ FR FRb)]]].
      eapply ast_step; [exact (so_svc _ _ _ _ _ _ HS)| exact STEP| exact AS].
Qed.

Lemma r5_eq_dec : forall a b : r5, {a = b} + {a <> b}. Proof. decide equality. Qed.

Lemma havoc_rf_other : forall l x n r, ~ In r l -> rf_get (havoc_rf x l n) r = rf_get x r.
Proof.
  induction l as [|r0 l IH]; intros x n r NI; cbn [havoc_rf]; [reflexivity|].
  rewrite IH by (intros Q; apply NI; right; exact Q). apply rf_get_set_other. intros ->. apply NI. left. reflexivity.
Qed.

Lemma add1_Z : forall n k, to_Z n + k < 4611686018427387904 -> 0 < k -> to_Z (PrimInt63.add n 1%uint63) = to_Z n + 1.
Proof.
  intros n k H K. pose proof (int_range n) as B. rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1.
  apply Z.mod_small. rewrite wB_two63. unfold two63 in *. lia.
Qed.

Lemma env_havoc_ext : forall vs E n, to_Z n + Z.of_nat (length vs) < 4611686018427387904 -> env_ext n E (env_havoc E vs n).
Proof.
  induction vs as [|v vs IH]; intros E n B; cbn [env_havoc]; [apply env_ext_refl|].
  cbn [length] in B. rewrite Nat2Z.inj_succ in B.
  pose proof (add1_Z n (Z.succ (Z.of_nat (length vs))) B ltac:(lia)) as A1.
  apply (env_ext_trans n (PrimInt63.add n 1%uint63) E (env_upd E n v)); [lia| apply env_upd_ext|].
  apply IH. rewrite A1. lia.
Qed.

Lemma havoc_den : forall l x n E0 (f : r5 -> word), to_Z n + Z.of_nat (length l) < 4611686018427387904 ->
  forall r, In r l -> den (env_havoc E0 (map f l) n) (rf_get (havoc_rf x l n) r) = f r.
Proof.
  induction l as [|r0 l IH]; intros x n E0 f B r Hin; [destruct Hin|].
  cbn [havoc_rf map env_havoc]. cbn [length] in B. rewrite Nat2Z.inj_succ in B.
  pose proof (add1_Z n (Z.succ (Z.of_nat (length l))) B ltac:(lia)) as A1.
  destruct (in_dec r5_eq_dec r l) as [I|NI].
  - apply IH; [rewrite A1; lia| exact I].
  - destruct Hin as [<-|I]; [|contradiction]. rewrite havoc_rf_other by exact NI. rewrite rf_get_set_same.
    pose proof (env_havoc_ext (map f l) (env_upd E0 n (f r0)) (PrimInt63.add n 1%uint63) ltac:(rewrite length_map, A1; lia)) as (_ & EX).
    destruct (EX n ltac:(rewrite A1; lia)) as [EV _].
    apply bv_eq. rewrite (den_VP0 _ n wzero (weqb_refl _)), EV, env_upd_same. reflexivity.
Qed.

Lemma rf_forallb2_eq : forall x y : rf sv, rf_forallb2 sv_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y. unfold rf_forallb2 in H. cbn in H.
  repeat (apply andb_prop in H; destruct H as [H ?]).
  repeat match goal with Q : sv_eqb _ _ = true |- _ => apply sv_eqb_eq in Q end. subst. reflexivity.
Qed.

Lemma getr_setr_same : forall st r v, r <> X0 -> getr (setr st r v) r = v.
Proof. intros st r v N. unfold getr, setr. destruct r; try contradiction; cbn [s_rf]; apply rf_get_set_same. Qed.
Lemma getr_setr_other : forall st r r' v, r <> r' -> getr (setr st r v) r' = getr st r'.
Proof. intros st r r' v N. unfold getr, setr. destruct r; try reflexivity; cbn [s_rf]; apply rf_get_set_other; exact N. Qed.
Lemma setr_pc : forall st r v, s_pc (setr st r v) = s_pc st.
Proof. intros st r v. unfold setr. destruct r; reflexivity. Qed.

Lemma restore_sound : forall E st l b ms model, st_ok segs OPS E b ms model ->
  (forall r, In r l -> r <> X0 /\ den E (getr b r) = den E (getr st r)) ->
  let b' := fold_left (fun acc r => setr acc r (getr st r)) l b in
  st_ok segs OPS E b' ms model /\ frame b b' /\ s_pc b' = s_pc b.
Proof.
  intros E st l. induction l as [|r l IH]; intros b ms model HSb H; cbn [fold_left].
  - split; [exact HSb|]. split; [apply frame_refl| reflexivity].
  - destruct (H r (or_introl eq_refl)) as [N D].
    assert (HS2 : st_ok segs OPS E (setr b r (getr st r)) ms model) by (apply setreg_sound; [exact HSb| exact N| exact D]).
    destruct (IH (setr b r (getr st r)) ms model HS2) as (A1 & A2 & A3).
    { intros r' Hr'. destruct (H r' (or_intror Hr')) as [N' D']. split; [exact N'|].
      destruct (r5_eq_dec r r') as [<-|NE]; [rewrite getr_setr_same by exact N; reflexivity| rewrite getr_setr_other by exact NE; exact D']. }
    split; [exact A1|]. split; [exact (frame_trans _ _ _ (frame_setr b r _) A2)| rewrite A3; apply setr_pc].
Qed.

Theorem gchk_sound : contract_sound segs OPS MP PB gchk_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gchk_contract c_apply] in HA. unfold gchk_apply in HA.
  destruct (ARMS st) as [arms|] eqn:AR; [|discriminate]. destruct arms as [|a1 arms']; [discriminate|].
  destruct (crun FUEL a1) as [b1|]; [|discriminate].
  set (rfW := havoc_rf (s_rf (restore st b1)) HV (s_next st)) in *.
  match type of HA with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end. injection HA as <-.
  apply andb_prop in COND as [COND AOK]. apply andb_prop in COND as [COND NB]. apply andb_prop in COND as [NX0 NPOS].
  apply Z.ltb_lt in NB. apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS.
  destruct (ARMS_CASES st (a1 :: arms') E ms model AR HS) as (a & Hin & HSa).
  pose proof (ARMS_FRAME st (a1 :: arms') a AR Hin) as FRa.
  pose proof (proj1 (forallb_forall _ _) AOK a Hin) as OKa. unfold arm_ok in OKa.
  destruct (crun FUEL a) as [b0|] eqn:CR; [|discriminate]. apply andb_prop in OKa as [OKa REG]. apply andb_prop in OKa as [RST VB]. apply rf_forallb2_eq in REG.
  destruct (crun_sound FUEL E a b0 ms model CR HSa) as (ms' & mo' & AS & HSb0 & PCb0 & FRb0).

  assert (RD : forall r, In r RL -> r <> X0 /\ den E (getr b0 r) = den E (getr st r)).
  { intros r Hr. pose proof (proj1 (forallb_forall _ _) RST r Hr) as P. apply andb_prop in P as [P1 P2]. apply sv_eqb_eq in P2.
    split; [intros Q; rewrite Q in P1; cbn in P1; discriminate P1|].
    rewrite P2. unfold getr. rewrite <- (so_regs _ _ _ _ _ _ HSa r), <- (so_regs _ _ _ _ _ _ HS r). reflexivity. }
  destruct (restore_sound E st RL b0 ms' mo' HSb0 RD) as (HSb & FRr & PCr). fold (restore st b0) in HSb, FRr, PCr.
  set (b := restore st b0) in *.
  assert (PCb : s_pc b = PC_OK) by (rewrite PCr; exact PCb0).
  pose proof (frame_trans _ _ _ FRb0 FRr) as FRb.
  pose proof (frame_trans _ _ _ FRa FRb) as (F1 & F2 & F3 & F4 & F5 & F6).
  apply (rz_asteps segs ms model ms' mo' K (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) AS).
  set (n := s_next st) in *.
  set (f := fun r => den E (rf_get (s_rf b) r)).
  set (E' := env_havoc E (map f HV) n).
  assert (EXT : env_ext n E E') by (apply env_havoc_ext; rewrite length_map; exact NB).

  assert (HS1 : st_ok segs OPS E' (base_of st b) ms' mo').
  { apply (st_ok_reval segs OPS n E E' EXT _ ms' mo' NPOS VB).
    destruct HSb as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
    unfold base_of. constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; rewrite <- ?F1, <- ?F2, <- ?F3, <- ?F4, <- ?F5; try assumption.
    exact (so_facts _ _ _ _ _ _ HS). }
  refine (Hk _ (or_introl eq_refl) E' ms' mo' EXT (asteps_MP segs MP HMPA _ _ _ _ AS HMP) _).
  assert (VBR : forall r, sv_vars_below n (rf_get (s_rf b) r) = true).
  { unfold st_vars_below in VB. do 5 (apply andb_prop in VB; destruct VB as [VB ?]). cbn [base_of s_rf] in VB. exact (rf_allb_get _ _ _ VB). }
  destruct HS1 as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  unfold base_of in *. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in *.
  assert (NX : forall r, In r HV -> r <> X0).
  { intros r Hr Q. pose proof (proj1 (forallb_forall _ _) NX0 r Hr) as P. rewrite Q in P. cbn in P. discriminate P. }
  unfold joined. constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - rewrite Ppc, PCb. reflexivity.
  - rewrite <- REG. rewrite havoc_rf_other by (intros Q; exact (NX X0 Q eq_refl)). exact Px0.
  - intros r. rewrite (Pregs r). rewrite <- REG.
    destruct (in_dec r5_eq_dec r HV) as [I|NI].
    + unfold E'. rewrite (havoc_den HV (s_rf b) n E f NB r I). unfold f. exact (den_reval n E E' EXT _ (VBR r)).
    + rewrite havoc_rf_other by exact NI. reflexivity.
Qed.

End Sound.
End Join.

Section GranL.
Variable segs : list Segment.
Variable G_PC : int.
Variable RS : r5.
Variable OFF : w64.
Variable PC_OK : int.
Variable HV : list r5.
Variable RL : list r5.
Variable FUEL : nat.

Definition gchkl_contract : contract := gchk_contract segs (GGranP.ggranl_apply RS OFF) G_PC PC_OK HV RL FUEL.

Theorem gchkl_sound : forall OPS MP PB,
  (forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo') ->
  contract_sound segs OPS MP PB gchkl_contract.
Proof.
  intros OPS MP PB HMPA. apply gchk_sound; [exact HMPA| |].
  - intros st arms E ms model HA HS. exact (GGranP.ggranl_cases RS OFF segs OPS MP st arms E ms model HA HS).
  - intros st arms a HA Hin. destruct (GGranP.ggranl_frame RS OFF st arms a HA Hin) as (A1 & A2 & A3 & A4 & A5 & A6). repeat split; assumption.
Qed.
End GranL.

End GChk.
