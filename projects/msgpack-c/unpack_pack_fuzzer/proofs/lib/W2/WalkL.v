(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs StepSoundBase StepSoundAlu StepSoundMem Acc StepAcc StepSound Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Mem Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require Import SpecFrame SpecLeib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step ValP StepB StepS PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Module EF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.

Module WalkL.
Section W.
Variable segs : list Segment.
Variable OPS : optable.
Variable it : itab.
Variable stops : list int.
Variables (ROOM IMGLO IMGHI : Z).

Definition addr_ok (st : sstate) (s : r5) (immw : w64) (width : Z) (load : bool) : bool :=
  match getr st s with
  | VP k off => PrimInt63.eqb k 1%uint63 && (let z := w2Zs (wadd off immw) in (- ROOM <=? z) && (z + width <=? 0))
  | VL lit => load && (let z := w2Z (wadd lit immw) in (IMGLO <=? z) && (z + width <=? IMGHI))
  | _ => false
  end.

Definition int_fi (fi : finstr) : bool :=
  match fi with
  | ILui _ _ | IAuipc _ _ | IJal _ _ | IJalr _ _ _ | IBranch _ _ _ _ | ILoad _ _ _ _ _ | IStore _ _ _ _ | IOpImm _ _ _ _ | IOp _ _ _ _
  | IOpImm32 _ _ _ _ | IOp32 _ _ _ _ | IMul _ _ _ _ | IMul32 _ _ _ _ | IFence => true
  | _ => false
  end.

Lemma int_fi_instr : forall i fi, of_instr i = Some fi -> int_fi fi = true -> SpecLeib.int_instr i = true.
Proof.
  intros i fi Hof HI. destruct i; try reflexivity; unfold of_instr in Hof;
    repeat match type of Hof with
           | context [match r5_of_reg ?r with _ => _ end] => destruct (r5_of_reg r)
           | context [match ?d with FC_W => _ | _ => _ end] => destruct d
           end;
    try discriminate Hof; injection Hof as <-; discriminate HI.
Qed.

Definition wsafe0 (st : sstate) : bool :=
  match IMap.find (s_pc st) it with
  | Some (ILoad sz _ _ s imm) => addr_ok st s imm (Z.of_nat (Acc.msz_nat sz)) true
  | Some (IStore sz s _ imm) => addr_ok st s imm (Z.of_nat (Acc.msz_nat sz)) false
  | Some (ILr _ _ _) | Some (ISc _ _ _ _) | Some (IAmo _ _ _ _ _) | Some (IFLoad _ _ _ _) | Some (IFStore _ _ _ _) => false
  | _ => true
  end.
Definition wsafe (st : sstate) : bool :=
  wsafe0 st && match IMap.find (s_pc st) it with Some fi => int_fi fi | None => false end.

Inductive wres : Type :=
| WOk (st : sstate)
| WStopPc (st : sstate)
| WBranch (c : branch_cond) (rs1 rs2 : r5) (off : w64) (st : sstate)
| WFail.

Definition wstep1 (st : sstate) : wres :=
  if in_stops (s_pc st) stops then WStopPc st else
  if negb (wsafe st) then WFail else
  match step segs it st with
  | SOk st' => WOk st'
  | SStop (KBranch _ _ _ _) _ =>
      match IMap.find (s_pc st) it with
      | Some (IBranch c rs1 rs2 off) => if PrimInt63.ltb (s_pc st) bit62i then WBranch c rs1 rs2 off st else WFail
      | _ => WFail
      end
  | _ => WFail
  end.

Definition wbind (r : wres) (f : sstate -> wres) : wres := match r with WOk st' => f st' | r' => r' end.
Fixpoint wrunP (p : positive) (st : sstate) : wres :=
  match p with
  | xH => wstep1 st
  | xO q => wbind (wrunP q st) (wrunP q)
  | xI q => wbind (wrunP q st) (fun st' => wbind (wrunP q st') wstep1)
  end.

Variable fuel : positive.
Variable fin : sstate -> bool.

Fixpoint wcheck (depth : nat) (st : sstate) : bool :=
  match wrunP fuel st with
  | WStopPc st' => fin st'
  | WBranch c rs1 rs2 off st' =>
      match depth with
      | O => false
      | S d =>
          match take_branch c (getr st' rs1) (getr st' rs2) off true st', take_branch c (getr st' rs1) (getr st' rs2) off false st' with
          | Some sT, Some sF => wcheck d sT && wcheck d sF
          | _, _ => false
          end
      end
  | _ => false
  end.

Variable RNG : EF.footprint.
Hypothesis HIT : itab_ok segs it.

Definition rmono (m0 m : word -> option byte) : Prop := forall x : word, AM.mrd segs m0 x <> None -> AM.mrd segs m x <> None.
Definition winv (lo hi : Z) (m0 m : word -> option byte) : Prop :=
  AF.munch [(lo, hi)] m0 m /\ AF.wmono segs m0 m /\ rmono m0 m.

Lemma winv_refl : forall lo hi m, winv lo hi m m.
Proof. intros lo hi m. split; [apply AF.munch_refl|]. split; [apply AF.wmono_refl| intros x H; exact H]. Qed.

Section Fixed.
Variable E : env.
Let SP0 : Z := bv_unsigned (ev E 1%uint63).
Hypothesis WLO : 0 <= SP0 - ROOM.
Hypothesis RWIN : EF.rng RNG (SP0 - ROOM) ROOM.
Hypothesis RIMG : EF.rng RNG IMGLO (IMGHI - IMGLO).
Hypothesis IMG0 : 0 <= IMGLO.

Lemma addr_ok_sound : forall st ms mo s rs1 n (imm : bv n) width load,
  st_ok segs OPS E st ms mo -> r5_of_reg rs1 = Some s -> addr_ok st s (w_of_imm imm) width load = true -> 0 <= width ->
  let a := (rget (core_of ms) rs1 + sext 64 imm)%bv in
  (SP0 - ROOM <= bv_unsigned a /\ bv_unsigned a + width <= SP0)
  \/ (load = true /\ IMGLO <= bv_unsigned a /\ bv_unsigned a + width <= IMGHI).
Proof.
  intros st ms mo s rs1 n imm width load HS Hr H Hw a. unfold addr_ok in H.
  assert (EA : a = alu64 ALU_ADD (den E (getr st s)) (den E (VL (w_of_imm imm)))).
  { unfold a. rewrite (StepM.getr_den segs OPS E st ms mo s rs1 HS Hr). cbn [den alu64 alu]. rewrite StepM.wbv_w_of_imm. reflexivity. }
  pose proof (bv_unsigned_in_range 64 (ev E 1%uint63)) as RB. rewrite bv_modulus_64 in RB. fold SP0 in RB.
  destruct (getr st s) as [lit|k off| | | | | | | | |] eqn:G; try discriminate H.
  - right. apply andb_prop in H as [HL H]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    split; [exact HL|].
    assert (UA : bv_unsigned a = w2Z (wadd lit (w_of_imm imm))).
    { rewrite EA. cbn [den alu64 alu]. rewrite bv_add_unsigned, !wbv_unsigned, wadd_ok. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. }
    rewrite UA. lia.
  - left. apply andb_prop in H as [HK H]. apply Uint63.eqb_correct in HK. subst k.
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    assert (UA : bv_unsigned a = (SP0 + w2Zs (wadd off (w_of_imm imm))) mod two64).
    { rewrite EA. rewrite <- (alu_add_pl E 1%uint63 off (w_of_imm imm)). rewrite den_VP. reflexivity. }
    rewrite UA. rewrite Z.mod_small by (unfold two64 in *; lia). lia.
Qed.

Lemma wsafe_accs : forall st ms mo fi i,
  st_ok segs OPS E st ms mo -> IMap.find (s_pc st) it = Some fi -> of_instr i = Some fi -> wsafe st = true ->
  forall a n, Acc.mem_acc i (core_of ms) a n ->
     ((SP0 - ROOM <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= SP0) \/ (IMGLO <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= IMGHI))
     /\ (SpecFrame.store_acc i (core_of ms) a n -> SP0 - ROOM <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= SP0).
Proof.
  intros st ms mo fi i HS Hfind Hof HW a n HM. unfold wsafe in HW. apply andb_prop in HW as [HW _]. unfold wsafe0 in HW. rewrite Hfind in HW.
  destruct i; cbn [Acc.mem_acc] in HM; try contradiction; unfold of_instr in Hof;
    repeat match type of Hof with context [match r5_of_reg ?r with _ => _ end] => let X := fresh "R" in destruct (r5_of_reg r) eqn:X end;
    try discriminate Hof; injection Hof as <-; try discriminate HW.
  -   destruct HM as [-> ->].
    destruct (addr_ok_sound st ms mo _ rs1 _ imm _ true HS R0 HW ltac:(lia)) as [A|(_ & A)]; (split; [tauto| cbn [SpecFrame.store_acc]; contradiction]).
  -   destruct HM as [-> ->].
    destruct (addr_ok_sound st ms mo _ rs1 _ imm _ false HS R HW ltac:(lia)) as [A|(X & _)]; [| discriminate X].
    split; [left; exact A| intros _; exact A].
Qed.

Lemma account_inv : forall ms mo ms' mo', Run.mi_account_step segs ms mo = MachineOk (ms', mo') ->
  exists report, step_accesses segs ms = MachineOk report /\ @access_value _ report = ms'.
Proof.
  intros ms mo ms' mo' H. unfold Run.mi_account_step in H.
  destruct (step_accesses segs ms) as [report| |]; try discriminate H.
  destruct (materialize_model_accesses mo (@accessed_ranges _ report)) as [mo2|]; [|discriminate H].
  injection H as <- <-. exists report. split; reflexivity.
Qed.

Lemma winv_write : forall m0 m1 (a : word) bs, winv (SP0 - ROOM) SP0 m0 m1 ->
  SP0 - ROOM <= bv_unsigned a -> bv_unsigned a + Z.of_nat (length bs) <= SP0 ->
  winv (SP0 - ROOM) SP0 m0 (write_to_mem m1 a bs).
Proof.
  intros m0 m1 a bs (MU & WM & RM) LO HI.
  pose proof (bv_unsigned_in_range 64 (ev E 1%uint63)) as RB. rewrite bv_modulus_64 in RB. fold SP0 in RB. unfold two64 in RB.
  assert (EA : a = AM.wa (bv_unsigned a)) by (unfold AM.wa; symmetry; apply Z_to_bv_bv_unsigned).
  split; [| split].
  - rewrite EA. apply AF.munch_write; [exact MU| lia| lia|]. cbn [AF.inside]. left. lia.
  - apply AF.wmono_write. exact WM.
  - intros x Hx. specialize (RM x Hx). unfold AM.mrd in *. rewrite EA. rewrite AM.write_to_mem_spec by lia.
    destruct (Z.leb (bv_unsigned a) (bv_unsigned x) && Z.ltb (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs)))%bool eqn:IN; [| exact RM].
    apply andb_prop in IN as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
    destruct (nth_error bs (Z.to_nat (bv_unsigned x - bv_unsigned a))) eqn:NE; [discriminate|].
    apply nth_error_None in NE. lia.
Qed.

Lemma mstep_of_account : forall st ms mo ms' mo' fi,
  st_ok segs OPS E st ms mo -> PrimInt63.ltb (s_pc st) bit62i = true -> IMap.find (s_pc st) it = Some fi -> fi <> IEcall -> wsafe st = true ->
  Run.mi_account_step segs ms mo = MachineOk (ms', mo') ->
  EF.mstepF segs RNG ms ms' /\ (forall m0, winv (SP0 - ROOM) SP0 m0 (ms_mem ms) -> winv (SP0 - ROOM) SP0 m0 (ms_mem ms'))
  /\ SpecLeib.mkeep ms ms'.
Proof.
  intros st ms mo ms' mo' fi HS Hpc Hfind NE HW ACC.
  assert (HIF : int_fi fi = true) by (unfold wsafe in HW; rewrite Hfind in HW; apply andb_prop in HW as [_ HW]; exact HW).
  destruct (itab_find segs it (s_pc st) fi HIT Hfind) as (w & Hfetch & [[He Hfi] | (He & i & Hdec & Hof)]); [contradiction|].
  rewrite <- (so_pc _ _ _ _ _ _ HS) in Hfetch.
  destruct (account_inv ms mo ms' mo' ACC) as (report & SA & <-).
  pose proof (Acc.step_accesses_accs segs ms w i report Hfetch He Hdec SA) as FA.
  pose proof (wsafe_accs st ms mo fi i HS Hfind Hof HW) as WA.
  split; [| split].
  - split; [exact (so_svc _ _ _ _ _ _ HS)|]. exists (@accessed_ranges _ report). split; [rewrite SA; destruct report; reflexivity|].
    eapply Forall_impl; [| exact FA]. intros [a n] HM. cbn [fst snd] in HM.
    destruct (proj1 (WA a n HM)) as [A|A].
    + apply (EF.rng_acc_var RNG _ _ a n RWIN). lia.
    + apply (EF.rng_acc_var RNG _ _ a n RIMG). lia.
  - intros m0 HI.
    apply (SpecFrame.step_inv segs (winv (SP0 - ROOM) SP0 m0) ms w i report Hfetch He Hdec SA); [| exact HI].
    intros m1 a bs H1 SAcc _.
    assert (HM : Acc.mem_acc i (core_of ms) a (length bs)).
    { unfold SpecFrame.store_acc in SAcc. destruct i; try contradiction; exact SAcc. }
    destruct (proj2 (WA a _ HM) SAcc) as [LO HI2]. apply winv_write; assumption.
  - exact (SpecLeib.step_keep segs ms w i 4 report Hfetch He Hdec SA (int_fi_instr i fi Hof HIF)).
Qed.

Definition reach (st' : sstate) (ms : machine_state) : Prop :=
  exists ms' mo', EF.mstepsF segs RNG ms ms' /\ st_ok segs OPS E st' ms' mo'
    /\ (forall m0, winv (SP0 - ROOM) SP0 m0 (ms_mem ms) -> winv (SP0 - ROOM) SP0 m0 (ms_mem ms'))
    /\ SpecLeib.mkeep ms ms'.

Definition wres_ok (r : wres) (ms : machine_state) : Prop :=
  match r with
  | WOk st' => reach st' ms
  | WStopPc st' => reach st' ms
  | WBranch c rs1 rs2 off st' => reach st' ms /\ PrimInt63.ltb (s_pc st') bit62i = true
                                  /\ IMap.find (s_pc st') it = Some (IBranch c rs1 rs2 off)
  | WFail => True
  end.

Lemma reach_refl : forall st ms mo, st_ok segs OPS E st ms mo -> reach st ms.
Proof. intros st ms mo HS. exists ms, mo. split; [constructor|]. split; [exact HS|]. split; [intros m0 H; exact H| apply SpecLeib.mkeep_refl]. Qed.

Lemma reach_trans : forall st1 st2 ms, reach st1 ms ->
  (forall ms1 mo1, st_ok segs OPS E st1 ms1 mo1 -> reach st2 ms1) -> reach st2 ms.
Proof.
  intros st1 st2 ms (ms1 & mo1 & S1 & HS1 & I1 & L1) K. destruct (K ms1 mo1 HS1) as (ms2 & mo2 & S2 & HS2 & I2 & L2).
  exists ms2, mo2. split; [eapply EF.mstepsF_trans; eassumption|]. split; [exact HS2|]. split; [intros m0 H; apply I2, I1, H| eapply SpecLeib.mkeep_trans; eassumption].
Qed.

Lemma wstep1_sound : forall st ms mo, st_ok segs OPS E st ms mo -> wres_ok (wstep1 st) ms.
Proof.
  intros st ms mo HS. unfold wstep1.
  destruct (in_stops (s_pc st) stops); [exact (reach_refl st ms mo HS)|].
  destruct (wsafe st) eqn:HW; cbn [negb]; [| exact I].
  destruct (step segs it st) as [st'|why st'] eqn:Hstep.
  - cbn [wres_ok].
    destruct (step_sound_a segs OPS E st ms mo it st' HIT HS Hstep) as (ms' & mo' & ACC & HS').
    unfold step in Hstep.
    destruct (PrimInt63.ltb (s_pc st) bit62i) eqn:Hpc; [|discriminate].
    destruct (IMap.find (s_pc st) it) as [fi|] eqn:Hfind; [|discriminate].
    assert (NE : fi <> IEcall) by (intros ->; cbn in Hstep; discriminate Hstep).
    destruct (mstep_of_account st ms mo ms' mo' fi HS Hpc Hfind NE HW ACC) as (MS & INV & LK).
    exists ms', mo'. split; [apply EF.mstepsF_one; exact MS|]. split; [exact HS'|]. split; [exact INV| exact LK].
  - destruct why; try exact I.
    destruct (IMap.find (s_pc st) it) as [[]|] eqn:Hfind; try exact I.
    destruct (PrimInt63.ltb (s_pc st) bit62i) eqn:Hpc; [| exact I].
    cbn [wres_ok]. split; [exact (reach_refl st ms mo HS)|]. split; [exact Hpc| exact Hfind].
Qed.

Lemma wres_ok_bind : forall r ms (f : sstate -> wres),
  wres_ok r ms -> (forall st1 ms1 mo1, st_ok segs OPS E st1 ms1 mo1 -> wres_ok (f st1) ms1) ->
  wres_ok (wbind r f) ms.
Proof.
  intros r ms f H K. unfold wbind. destruct r as [st1| | |]; try exact H.
  cbn [wres_ok] in H. destruct H as (ms1 & mo1 & S1 & HS1 & I1 & L1).
  specialize (K st1 ms1 mo1 HS1).
  assert (RT : forall st2, reach st2 ms1 -> reach st2 ms).
  { intros st2 (ms2 & mo2 & S2 & HS2 & I2 & L2). exists ms2, mo2. split; [eapply EF.mstepsF_trans; eassumption|]. split; [exact HS2|].
    split; [intros m0 H; apply I2, I1, H| eapply SpecLeib.mkeep_trans; eassumption]. }
  destruct (f st1) as [st2|st2|c rs1 rs2 off st2|]; cbn [wres_ok] in K |- *; try exact I.
  - exact (RT _ K). - exact (RT _ K). - destruct K as (K1 & K2 & K3). split; [exact (RT _ K1)|]. split; assumption.
Qed.

Lemma wrunP_sound : forall p st ms mo, st_ok segs OPS E st ms mo -> wres_ok (wrunP p st) ms.
Proof.
  induction p as [q IH|q IH|]; intros st ms mo HS; cbn [wrunP].
  - apply wres_ok_bind; [exact (IH st ms mo HS)|]. intros st1 ms1 mo1 HS1.
    apply wres_ok_bind; [exact (IH st1 ms1 mo1 HS1)|]. intros st2 ms2 mo2 HS2. exact (wstep1_sound st2 ms2 mo2 HS2).
  - apply wres_ok_bind; [exact (IH st ms mo HS)|]. intros st1 ms1 mo1 HS1. exact (IH st1 ms1 mo1 HS1).
  - exact (wstep1_sound st ms mo HS).
Qed.

Theorem wcheck_sound : forall depth st ms mo, wcheck depth st = true -> st_ok segs OPS E st ms mo ->
  exists ms' mo' st', EF.mstepsF segs RNG ms ms' /\ st_ok segs OPS E st' ms' mo' /\ fin st' = true
    /\ winv (SP0 - ROOM) SP0 (ms_mem ms) (ms_mem ms') /\ SpecLeib.mkeep ms ms'.
Proof.
  induction depth as [|d IH]; intros st ms mo HC HS; cbn [wcheck] in HC;
    pose proof (wrunP_sound fuel st ms mo HS) as R; destruct (wrunP fuel st) as [st1|st1|c rs1 rs2 off st1|]; try discriminate HC.
  - cbn [wres_ok] in R. destruct R as (ms1 & mo1 & S1 & HS1 & I1 & L1). exists ms1, mo1, st1. split; [exact S1|]. split; [exact HS1|].
    split; [exact HC|]. split; [apply I1, winv_refl| exact L1].
  - cbn [wres_ok] in R. destruct R as (ms1 & mo1 & S1 & HS1 & I1 & L1). exists ms1, mo1, st1. split; [exact S1|]. split; [exact HS1|].
    split; [exact HC|]. split; [apply I1, winv_refl| exact L1].
  - cbn [wres_ok] in R. destruct R as ((ms1 & mo1 & S1 & HS1 & I1 & L1) & Hpc & Hfind).
    destruct (take_branch c (getr st1 rs1) (getr st1 rs2) off true st1) as [sT|] eqn:HT; [|discriminate HC].
    destruct (take_branch c (getr st1 rs1) (getr st1 rs2) off false st1) as [sF|] eqn:HF; [|discriminate HC].
    apply andb_prop in HC as [HCT HCF].
    assert (HWs : wsafe st1 = true) by (unfold wsafe, wsafe0; rewrite Hfind; reflexivity).
    assert (NE : IBranch c rs1 rs2 off <> IEcall) by discriminate.
    destruct (branch_taken c (den E (getr st1 rs1)) (den E (getr st1 rs2))) eqn:BT.
    + destruct (take_branch_sound segs OPS E st1 ms1 mo1 it c rs1 rs2 off true sT HIT HS1 Hpc Hfind BT HT) as (ms2 & ACC & HS2).
      destruct (mstep_of_account st1 ms1 mo1 ms2 mo1 _ HS1 Hpc Hfind NE HWs ACC) as (MS & INV & LK).
      destruct (IH sT ms2 mo1 HCT HS2) as (ms3 & mo3 & st3 & S3 & HS3 & F3 & I3 & L3).
      exists ms3, mo3, st3. split; [eapply EF.mstepsF_trans; [exact S1|]; eapply EF.mstepsF_cons; [exact MS| exact S3]|].
      split; [exact HS3|]. split; [exact F3|].
      split; [| eapply SpecLeib.mkeep_trans; [exact L1|]; eapply SpecLeib.mkeep_trans; [exact LK| exact L3]].
      destruct I3 as (MU3 & WM3 & RM3). destruct (INV _ (I1 _ (winv_refl _ _ (ms_mem ms)))) as (MU2 & WM2 & RM2).
      split; [eapply AF.munch_trans; eassumption|]. split; [eapply AF.wmono_trans; eassumption|]. intros x Hx. apply RM3, RM2, Hx.
    + destruct (take_branch_sound segs OPS E st1 ms1 mo1 it c rs1 rs2 off false sF HIT HS1 Hpc Hfind BT HF) as (ms2 & ACC & HS2).
      destruct (mstep_of_account st1 ms1 mo1 ms2 mo1 _ HS1 Hpc Hfind NE HWs ACC) as (MS & INV & LK).
      destruct (IH sF ms2 mo1 HCF HS2) as (ms3 & mo3 & st3 & S3 & HS3 & F3 & I3 & L3).
      exists ms3, mo3, st3. split; [eapply EF.mstepsF_trans; [exact S1|]; eapply EF.mstepsF_cons; [exact MS| exact S3]|].
      split; [exact HS3|]. split; [exact F3|].
      split; [| eapply SpecLeib.mkeep_trans; [exact L1|]; eapply SpecLeib.mkeep_trans; [exact LK| exact L3]].
      destruct I3 as (MU3 & WM3 & RM3). destruct (INV _ (I1 _ (winv_refl _ _ (ms_mem ms)))) as (MU2 & WM2 & RM2).
      split; [eapply AF.munch_trans; eassumption|]. split; [eapply AF.wmono_trans; eassumption|]. intros x Hx. apply RM3, RM2, Hx.
Qed.

End Fixed.
End W.
End WalkL.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundAlu OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Acc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepAcc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import SpecFrame.TwinB SpecLeib.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step ValP StepB StepS PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Module EF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.

Module WalkL.
Section W.
Variable segs : list Segment.
Variable OPS : optable.
Variable it : itab.
Variable stops : list int.
Variables (ROOM IMGLO IMGHI : Z).

Definition addr_ok (st : sstate) (s : r5) (immw : w64) (width : Z) (load : bool) : bool :=
  match getr st s with
  | VP k off => PrimInt63.eqb k 1%uint63 && (let z := w2Zs (wadd off immw) in (- ROOM <=? z) && (z + width <=? 0))
  | VL lit => load && (let z := w2Z (wadd lit immw) in (IMGLO <=? z) && (z + width <=? IMGHI))
  | _ => false
  end.

Definition int_fi (fi : finstr) : bool :=
  match fi with
  | ILui _ _ | IAuipc _ _ | IJal _ _ | IJalr _ _ _ | IBranch _ _ _ _ | ILoad _ _ _ _ _ | IStore _ _ _ _ | IOpImm _ _ _ _ | IOp _ _ _ _
  | IOpImm32 _ _ _ _ | IOp32 _ _ _ _ | IMul _ _ _ _ | IMul32 _ _ _ _ | IFence => true
  | _ => false
  end.

Lemma int_fi_instr : forall i fi, of_instr i = Some fi -> int_fi fi = true -> SpecLeib.TwinB.SpecLeib.int_instr i = true.
Proof.
  intros i fi Hof HI. destruct i; try reflexivity; unfold of_instr in Hof;
    repeat match type of Hof with
           | context [match r5_of_reg ?r with _ => _ end] => destruct (r5_of_reg r)
           | context [match ?d with FC_W => _ | _ => _ end] => destruct d
           end;
    try discriminate Hof; injection Hof as <-; discriminate HI.
Qed.

Definition wsafe0 (st : sstate) : bool :=
  match IMap.find (s_pc st) it with
  | Some (ILoad sz _ _ s imm) => addr_ok st s imm (Z.of_nat (Acc.msz_nat sz)) true
  | Some (IStore sz s _ imm) => addr_ok st s imm (Z.of_nat (Acc.msz_nat sz)) false
  | Some (ILr _ _ _) | Some (ISc _ _ _ _) | Some (IAmo _ _ _ _ _) | Some (IFLoad _ _ _ _) | Some (IFStore _ _ _ _) => false
  | _ => true
  end.
Definition wsafe (st : sstate) : bool :=
  wsafe0 st && match IMap.find (s_pc st) it with Some fi => int_fi fi | None => false end.

Inductive wres : Type :=
| WOk (st : sstate)
| WStopPc (st : sstate)
| WBranch (c : branch_cond) (rs1 rs2 : r5) (off : w64) (st : sstate)
| WFail.

Definition wstep1 (st : sstate) : wres :=
  if in_stops (s_pc st) stops then WStopPc st else
  if negb (wsafe st) then WFail else
  match step segs it st with
  | SOk st' => WOk st'
  | SStop (KBranch _ _ _ _) _ =>
      match IMap.find (s_pc st) it with
      | Some (IBranch c rs1 rs2 off) => if PrimInt63.ltb (s_pc st) bit62i then WBranch c rs1 rs2 off st else WFail
      | _ => WFail
      end
  | _ => WFail
  end.

Definition wbind (r : wres) (f : sstate -> wres) : wres := match r with WOk st' => f st' | r' => r' end.
Fixpoint wrunP (p : positive) (st : sstate) : wres :=
  match p with
  | xH => wstep1 st
  | xO q => wbind (wrunP q st) (wrunP q)
  | xI q => wbind (wrunP q st) (fun st' => wbind (wrunP q st') wstep1)
  end.

Variable fuel : positive.
Variable fin : sstate -> bool.

Fixpoint wcheck (depth : nat) (st : sstate) : bool :=
  match wrunP fuel st with
  | WStopPc st' => fin st'
  | WBranch c rs1 rs2 off st' =>
      match depth with
      | O => false
      | S d =>
          match take_branch c (getr st' rs1) (getr st' rs2) off true st', take_branch c (getr st' rs1) (getr st' rs2) off false st' with
          | Some sT, Some sF => wcheck d sT && wcheck d sF
          | _, _ => false
          end
      end
  | _ => false
  end.

Variable RNG : EF.footprint.
Hypothesis HIT : itab_ok segs it.

Definition rmono (m0 m : word -> option byte) : Prop := forall x : word, AM.mrd segs m0 x <> None -> AM.mrd segs m x <> None.
Definition winv (lo hi : Z) (m0 m : word -> option byte) : Prop :=
  AF.munch [(lo, hi)] m0 m /\ AF.wmono segs m0 m /\ rmono m0 m.

Lemma winv_refl : forall lo hi m, winv lo hi m m.
Proof. intros lo hi m. split; [apply AF.munch_refl|]. split; [apply AF.wmono_refl| intros x H; exact H]. Qed.

Section Fixed.
Variable E : env.
Let SP0 : Z := bv_unsigned (ev E 1%uint63).
Hypothesis WLO : 0 <= SP0 - ROOM.
Hypothesis RWIN : EF.rng RNG (SP0 - ROOM) ROOM.
Hypothesis RIMG : EF.rng RNG IMGLO (IMGHI - IMGLO).
Hypothesis IMG0 : 0 <= IMGLO.

Lemma addr_ok_sound : forall st ms mo s rs1 n (imm : bv n) width load,
  st_ok segs OPS E st ms mo -> r5_of_reg rs1 = Some s -> addr_ok st s (w_of_imm imm) width load = true -> 0 <= width ->
  let a := (rget (core_of ms) rs1 + sext 64 imm)%bv in
  (SP0 - ROOM <= bv_unsigned a /\ bv_unsigned a + width <= SP0)
  \/ (load = true /\ IMGLO <= bv_unsigned a /\ bv_unsigned a + width <= IMGHI).
Proof.
  intros st ms mo s rs1 n imm width load HS Hr H Hw a. unfold addr_ok in H.
  assert (EA : a = alu64 ALU_ADD (den E (getr st s)) (den E (VL (w_of_imm imm)))).
  { unfold a. rewrite (StepM.getr_den segs OPS E st ms mo s rs1 HS Hr). cbn [den alu64 alu]. rewrite StepM.wbv_w_of_imm. reflexivity. }
  pose proof (bv_unsigned_in_range 64 (ev E 1%uint63)) as RB. rewrite bv_modulus_64 in RB. fold SP0 in RB.
  destruct (getr st s) as [lit|k off| | | | | | | | |] eqn:G; try discriminate H.
  - right. apply andb_prop in H as [HL H]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    split; [exact HL|].
    assert (UA : bv_unsigned a = w2Z (wadd lit (w_of_imm imm))).
    { rewrite EA. cbn [den alu64 alu]. rewrite bv_add_unsigned, !wbv_unsigned, wadd_ok. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. }
    rewrite UA. lia.
  - left. apply andb_prop in H as [HK H]. apply Uint63.eqb_correct in HK. subst k.
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    assert (UA : bv_unsigned a = (SP0 + w2Zs (wadd off (w_of_imm imm))) mod two64).
    { rewrite EA. rewrite <- (alu_add_pl E 1%uint63 off (w_of_imm imm)). rewrite den_VP. reflexivity. }
    rewrite UA. rewrite Z.mod_small by (unfold two64 in *; lia). lia.
Qed.

Lemma wsafe_accs : forall st ms mo fi i,
  st_ok segs OPS E st ms mo -> IMap.find (s_pc st) it = Some fi -> of_instr i = Some fi -> wsafe st = true ->
  forall a n, Acc.mem_acc i (core_of ms) a n ->
     ((SP0 - ROOM <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= SP0) \/ (IMGLO <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= IMGHI))
     /\ (SpecFrame.TwinB.SpecFrame.store_acc i (core_of ms) a n -> SP0 - ROOM <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= SP0).
Proof.
  intros st ms mo fi i HS Hfind Hof HW a n HM. unfold wsafe in HW. apply andb_prop in HW as [HW _]. unfold wsafe0 in HW. rewrite Hfind in HW.
  destruct i; cbn [Acc.mem_acc] in HM; try contradiction; unfold of_instr in Hof;
    repeat match type of Hof with context [match r5_of_reg ?r with _ => _ end] => let X := fresh "R" in destruct (r5_of_reg r) eqn:X end;
    try discriminate Hof; injection Hof as <-; try discriminate HW.
  -   destruct HM as [-> ->].
    destruct (addr_ok_sound st ms mo _ rs1 _ imm _ true HS R0 HW ltac:(lia)) as [A|(_ & A)]; (split; [tauto| cbn [SpecFrame.TwinB.SpecFrame.store_acc]; contradiction]).
  -   destruct HM as [-> ->].
    destruct (addr_ok_sound st ms mo _ rs1 _ imm _ false HS R HW ltac:(lia)) as [A|(X & _)]; [| discriminate X].
    split; [left; exact A| intros _; exact A].
Qed.

Lemma account_inv : forall ms mo ms' mo', Run.mi_account_step segs ms mo = MachineOk (ms', mo') ->
  exists report, step_accesses segs ms = MachineOk report /\ @access_value _ report = ms'.
Proof.
  intros ms mo ms' mo' H. unfold Run.mi_account_step in H.
  destruct (step_accesses segs ms) as [report| |]; try discriminate H.
  destruct (materialize_model_accesses mo (@accessed_ranges _ report)) as [mo2|]; [|discriminate H].
  injection H as <- <-. exists report. split; reflexivity.
Qed.

Lemma winv_write : forall m0 m1 (a : word) bs, winv (SP0 - ROOM) SP0 m0 m1 ->
  SP0 - ROOM <= bv_unsigned a -> bv_unsigned a + Z.of_nat (length bs) <= SP0 ->
  winv (SP0 - ROOM) SP0 m0 (write_to_mem m1 a bs).
Proof.
  intros m0 m1 a bs (MU & WM & RM) LO HI.
  pose proof (bv_unsigned_in_range 64 (ev E 1%uint63)) as RB. rewrite bv_modulus_64 in RB. fold SP0 in RB. unfold two64 in RB.
  assert (EA : a = AM.wa (bv_unsigned a)) by (unfold AM.wa; symmetry; apply Z_to_bv_bv_unsigned).
  split; [| split].
  - rewrite EA. apply AF.munch_write; [exact MU| lia| lia|]. cbn [AF.inside]. left. lia.
  - apply AF.wmono_write. exact WM.
  - intros x Hx. specialize (RM x Hx). unfold AM.mrd in *. rewrite EA. rewrite AM.write_to_mem_spec by lia.
    destruct (Z.leb (bv_unsigned a) (bv_unsigned x) && Z.ltb (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs)))%bool eqn:IN; [| exact RM].
    apply andb_prop in IN as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
    destruct (nth_error bs (Z.to_nat (bv_unsigned x - bv_unsigned a))) eqn:NE; [discriminate|].
    apply nth_error_None in NE. lia.
Qed.

Lemma mstep_of_account : forall st ms mo ms' mo' fi,
  st_ok segs OPS E st ms mo -> PrimInt63.ltb (s_pc st) bit62i = true -> IMap.find (s_pc st) it = Some fi -> fi <> IEcall -> wsafe st = true ->
  Run.mi_account_step segs ms mo = MachineOk (ms', mo') ->
  EF.mstepF segs RNG ms ms' /\ (forall m0, winv (SP0 - ROOM) SP0 m0 (ms_mem ms) -> winv (SP0 - ROOM) SP0 m0 (ms_mem ms'))
  /\ SpecLeib.TwinB.SpecLeib.mkeep ms ms'.
Proof.
  intros st ms mo ms' mo' fi HS Hpc Hfind NE HW ACC.
  assert (HIF : int_fi fi = true) by (unfold wsafe in HW; rewrite Hfind in HW; apply andb_prop in HW as [_ HW]; exact HW).
  destruct (itab_find segs it (s_pc st) fi HIT Hfind) as (w & Hfetch & [[He Hfi] | (He & i & Hdec & Hof)]); [contradiction|].
  rewrite <- (so_pc _ _ _ _ _ _ HS) in Hfetch.
  destruct (account_inv ms mo ms' mo' ACC) as (report & SA & <-).
  pose proof (Acc.step_accesses_accs segs ms w i report Hfetch He Hdec SA) as FA.
  pose proof (wsafe_accs st ms mo fi i HS Hfind Hof HW) as WA.
  split; [| split].
  - split; [exact (so_svc _ _ _ _ _ _ HS)|]. exists (@accessed_ranges _ report). split; [rewrite SA; destruct report; reflexivity|].
    eapply Forall_impl; [| exact FA]. intros [a n] HM. cbn [fst snd] in HM.
    destruct (proj1 (WA a n HM)) as [A|A].
    + apply (EF.rng_acc_var RNG _ _ a n RWIN). lia.
    + apply (EF.rng_acc_var RNG _ _ a n RIMG). lia.
  - intros m0 HI.
    apply (SpecFrame.TwinB.SpecFrame.step_inv segs (winv (SP0 - ROOM) SP0 m0) ms w i report Hfetch He Hdec SA); [| exact HI].
    intros m1 a bs H1 SAcc _.
    assert (HM : Acc.mem_acc i (core_of ms) a (length bs)).
    { unfold SpecFrame.TwinB.SpecFrame.store_acc in SAcc. destruct i; try contradiction; exact SAcc. }
    destruct (proj2 (WA a _ HM) SAcc) as [LO HI2]. apply winv_write; assumption.
  - exact (SpecLeib.TwinB.SpecLeib.step_keep segs ms w i 4 report Hfetch He Hdec SA (int_fi_instr i fi Hof HIF)).
Qed.

Definition reach (st' : sstate) (ms : machine_state) : Prop :=
  exists ms' mo', EF.mstepsF segs RNG ms ms' /\ st_ok segs OPS E st' ms' mo'
    /\ (forall m0, winv (SP0 - ROOM) SP0 m0 (ms_mem ms) -> winv (SP0 - ROOM) SP0 m0 (ms_mem ms'))
    /\ SpecLeib.TwinB.SpecLeib.mkeep ms ms'.

Definition wres_ok (r : wres) (ms : machine_state) : Prop :=
  match r with
  | WOk st' => reach st' ms
  | WStopPc st' => reach st' ms
  | WBranch c rs1 rs2 off st' => reach st' ms /\ PrimInt63.ltb (s_pc st') bit62i = true
                                  /\ IMap.find (s_pc st') it = Some (IBranch c rs1 rs2 off)
  | WFail => True
  end.

Lemma reach_refl : forall st ms mo, st_ok segs OPS E st ms mo -> reach st ms.
Proof. intros st ms mo HS. exists ms, mo. split; [constructor|]. split; [exact HS|]. split; [intros m0 H; exact H| apply SpecLeib.TwinB.SpecLeib.mkeep_refl]. Qed.

Lemma reach_trans : forall st1 st2 ms, reach st1 ms ->
  (forall ms1 mo1, st_ok segs OPS E st1 ms1 mo1 -> reach st2 ms1) -> reach st2 ms.
Proof.
  intros st1 st2 ms (ms1 & mo1 & S1 & HS1 & I1 & L1) K. destruct (K ms1 mo1 HS1) as (ms2 & mo2 & S2 & HS2 & I2 & L2).
  exists ms2, mo2. split; [eapply EF.mstepsF_trans; eassumption|]. split; [exact HS2|]. split; [intros m0 H; apply I2, I1, H| eapply SpecLeib.TwinB.SpecLeib.mkeep_trans; eassumption].
Qed.

Lemma wstep1_sound : forall st ms mo, st_ok segs OPS E st ms mo -> wres_ok (wstep1 st) ms.
Proof.
  intros st ms mo HS. unfold wstep1.
  destruct (in_stops (s_pc st) stops); [exact (reach_refl st ms mo HS)|].
  destruct (wsafe st) eqn:HW; cbn [negb]; [| exact I].
  destruct (step segs it st) as [st'|why st'] eqn:Hstep.
  - cbn [wres_ok].
    destruct (step_sound_a segs OPS E st ms mo it st' HIT HS Hstep) as (ms' & mo' & ACC & HS').
    unfold step in Hstep.
    destruct (PrimInt63.ltb (s_pc st) bit62i) eqn:Hpc; [|discriminate].
    destruct (IMap.find (s_pc st) it) as [fi|] eqn:Hfind; [|discriminate].
    assert (NE : fi <> IEcall) by (intros ->; cbn in Hstep; discriminate Hstep).
    destruct (mstep_of_account st ms mo ms' mo' fi HS Hpc Hfind NE HW ACC) as (MS & INV & LK).
    exists ms', mo'. split; [apply EF.mstepsF_one; exact MS|]. split; [exact HS'|]. split; [exact INV| exact LK].
  - destruct why; try exact I.
    destruct (IMap.find (s_pc st) it) as [[]|] eqn:Hfind; try exact I.
    destruct (PrimInt63.ltb (s_pc st) bit62i) eqn:Hpc; [| exact I].
    cbn [wres_ok]. split; [exact (reach_refl st ms mo HS)|]. split; [exact Hpc| exact Hfind].
Qed.

Lemma wres_ok_bind : forall r ms (f : sstate -> wres),
  wres_ok r ms -> (forall st1 ms1 mo1, st_ok segs OPS E st1 ms1 mo1 -> wres_ok (f st1) ms1) ->
  wres_ok (wbind r f) ms.
Proof.
  intros r ms f H K. unfold wbind. destruct r as [st1| | |]; try exact H.
  cbn [wres_ok] in H. destruct H as (ms1 & mo1 & S1 & HS1 & I1 & L1).
  specialize (K st1 ms1 mo1 HS1).
  assert (RT : forall st2, reach st2 ms1 -> reach st2 ms).
  { intros st2 (ms2 & mo2 & S2 & HS2 & I2 & L2). exists ms2, mo2. split; [eapply EF.mstepsF_trans; eassumption|]. split; [exact HS2|].
    split; [intros m0 H; apply I2, I1, H| eapply SpecLeib.TwinB.SpecLeib.mkeep_trans; eassumption]. }
  destruct (f st1) as [st2|st2|c rs1 rs2 off st2|]; cbn [wres_ok] in K |- *; try exact I.
  - exact (RT _ K). - exact (RT _ K). - destruct K as (K1 & K2 & K3). split; [exact (RT _ K1)|]. split; assumption.
Qed.

Lemma wrunP_sound : forall p st ms mo, st_ok segs OPS E st ms mo -> wres_ok (wrunP p st) ms.
Proof.
  induction p as [q IH|q IH|]; intros st ms mo HS; cbn [wrunP].
  - apply wres_ok_bind; [exact (IH st ms mo HS)|]. intros st1 ms1 mo1 HS1.
    apply wres_ok_bind; [exact (IH st1 ms1 mo1 HS1)|]. intros st2 ms2 mo2 HS2. exact (wstep1_sound st2 ms2 mo2 HS2).
  - apply wres_ok_bind; [exact (IH st ms mo HS)|]. intros st1 ms1 mo1 HS1. exact (IH st1 ms1 mo1 HS1).
  - exact (wstep1_sound st ms mo HS).
Qed.

Theorem wcheck_sound : forall depth st ms mo, wcheck depth st = true -> st_ok segs OPS E st ms mo ->
  exists ms' mo' st', EF.mstepsF segs RNG ms ms' /\ st_ok segs OPS E st' ms' mo' /\ fin st' = true
    /\ winv (SP0 - ROOM) SP0 (ms_mem ms) (ms_mem ms') /\ SpecLeib.TwinB.SpecLeib.mkeep ms ms'.
Proof.
  induction depth as [|d IH]; intros st ms mo HC HS; cbn [wcheck] in HC;
    pose proof (wrunP_sound fuel st ms mo HS) as R; destruct (wrunP fuel st) as [st1|st1|c rs1 rs2 off st1|]; try discriminate HC.
  - cbn [wres_ok] in R. destruct R as (ms1 & mo1 & S1 & HS1 & I1 & L1). exists ms1, mo1, st1. split; [exact S1|]. split; [exact HS1|].
    split; [exact HC|]. split; [apply I1, winv_refl| exact L1].
  - cbn [wres_ok] in R. destruct R as (ms1 & mo1 & S1 & HS1 & I1 & L1). exists ms1, mo1, st1. split; [exact S1|]. split; [exact HS1|].
    split; [exact HC|]. split; [apply I1, winv_refl| exact L1].
  - cbn [wres_ok] in R. destruct R as ((ms1 & mo1 & S1 & HS1 & I1 & L1) & Hpc & Hfind).
    destruct (take_branch c (getr st1 rs1) (getr st1 rs2) off true st1) as [sT|] eqn:HT; [|discriminate HC].
    destruct (take_branch c (getr st1 rs1) (getr st1 rs2) off false st1) as [sF|] eqn:HF; [|discriminate HC].
    apply andb_prop in HC as [HCT HCF].
    assert (HWs : wsafe st1 = true) by (unfold wsafe, wsafe0; rewrite Hfind; reflexivity).
    assert (NE : IBranch c rs1 rs2 off <> IEcall) by discriminate.
    destruct (branch_taken c (den E (getr st1 rs1)) (den E (getr st1 rs2))) eqn:BT.
    + destruct (take_branch_sound segs OPS E st1 ms1 mo1 it c rs1 rs2 off true sT HIT HS1 Hpc Hfind BT HT) as (ms2 & ACC & HS2).
      destruct (mstep_of_account st1 ms1 mo1 ms2 mo1 _ HS1 Hpc Hfind NE HWs ACC) as (MS & INV & LK).
      destruct (IH sT ms2 mo1 HCT HS2) as (ms3 & mo3 & st3 & S3 & HS3 & F3 & I3 & L3).
      exists ms3, mo3, st3. split; [eapply EF.mstepsF_trans; [exact S1|]; eapply EF.mstepsF_cons; [exact MS| exact S3]|].
      split; [exact HS3|]. split; [exact F3|].
      split; [| eapply SpecLeib.TwinB.SpecLeib.mkeep_trans; [exact L1|]; eapply SpecLeib.TwinB.SpecLeib.mkeep_trans; [exact LK| exact L3]].
      destruct I3 as (MU3 & WM3 & RM3). destruct (INV _ (I1 _ (winv_refl _ _ (ms_mem ms)))) as (MU2 & WM2 & RM2).
      split; [eapply AF.munch_trans; eassumption|]. split; [eapply AF.wmono_trans; eassumption|]. intros x Hx. apply RM3, RM2, Hx.
    + destruct (take_branch_sound segs OPS E st1 ms1 mo1 it c rs1 rs2 off false sF HIT HS1 Hpc Hfind BT HF) as (ms2 & ACC & HS2).
      destruct (mstep_of_account st1 ms1 mo1 ms2 mo1 _ HS1 Hpc Hfind NE HWs ACC) as (MS & INV & LK).
      destruct (IH sF ms2 mo1 HCF HS2) as (ms3 & mo3 & st3 & S3 & HS3 & F3 & I3 & L3).
      exists ms3, mo3, st3. split; [eapply EF.mstepsF_trans; [exact S1|]; eapply EF.mstepsF_cons; [exact MS| exact S3]|].
      split; [exact HS3|]. split; [exact F3|].
      split; [| eapply SpecLeib.TwinB.SpecLeib.mkeep_trans; [exact L1|]; eapply SpecLeib.TwinB.SpecLeib.mkeep_trans; [exact LK| exact L3]].
      destruct I3 as (MU3 & WM3 & RM3). destruct (INV _ (I1 _ (winv_refl _ _ (ms_mem ms)))) as (MU2 & WM2 & RM2).
      split; [eapply AF.munch_trans; eassumption|]. split; [eapply AF.wmono_trans; eassumption|]. intros x Hx. apply RM3, RM2, Hx.
Qed.

End Fixed.
End W.
End WalkL.
End TwinB.
