(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GGran.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GGranP.

Definition pair_sel (RS : r5) (OFF : w64) (st : sstate) : option (int * sv * sv) :=
  let a := sv_alu ALU_ADD (getr st RS) (VL OFF) in
  match addr_of a with
  | Some (k, o) =>
      if PrimInt63.eqb k 0%uint63 then None else
      match IMap.find k (s_regs st) with
      | Some r => match rg_bg r with BGZero => Some (k, VL o, rg_hi r) | _ => None end
      | None => None
      end
  | None =>
      match sym_addr_of (s_regs st) a with
      | Some (k, r, o) => match rg_bg r with BGZero => Some (k, o, rg_hi r) | _ => None end
      | None => None
      end
  end.

Fixpoint find_tail (fs : list fact) (sh : int) (hi : sv) : option int :=
  match fs with
  | [] => None
  | FEq (VP s2 o2) (VAlu ALU_ADD (VP sh' o') hi') :: fs' =>
      if weqb o2 wzero && PrimInt63.eqb sh' sh && weqb o' wzero && sv_eqb hi' hi then Some s2 else find_tail fs' sh hi
  | _ :: fs' => find_tail fs' sh hi
  end.

Definition gran_len2 (hi : sv) : option sv :=
  match hi with
  | VAlu ALU_SRL n (VL s) => if weqb s GGran.w3 then Some n else None
  | _ => None
  end.

Lemma mod_sub_help : forall M G O S2 SH H : Z, 0 < M -> 0 <= G < M -> 0 <= O < M ->
  (G + O) mod M = (SH + H) mod M -> S2 mod M = (SH mod M + H) mod M -> 0 <= S2 < M -> G = (S2 + (- O) mod M) mod M.
Proof.
  intros M G O S2 SH H HM RG RO DA TL RS2.
  assert (E1 : S2 = (G + O) mod M).
  { rewrite <- (Z.mod_small S2 M RS2), TL, Zplus_mod_idemp_l. symmetry. exact DA. }
  rewrite Zplus_mod_idemp_r, E1, Zplus_mod_idemp_l. replace (G + O + - O) with G by lia. symmetry. apply Z.mod_small. exact RG.
Qed.

Section WithPc.
Variable G_PC : int.
Variable RS : r5.
Variable OFF : w64.

Definition ggranp_apply (st : sstate) : option (list sstate) :=
  let fs := s_facts st in
  match pair_sel RS OFF st with
  | Some (sh, o, hi) =>
      match GGran.gran_src o, gran_len2 hi, find_tail fs sh hi with
      | Some X, Some n, Some s2 =>
          if negb (r5_eqb RS X0) && match decide_ltu fs X n with Some true => true | _ => false end
          then Some [addfact st (FULt o hi); addfact (setr st RS (VP s2 (wneg OFF))) (FEq o hi)] else None
      | _, _, _ => None
      end
  | None => None
  end.

Definition ggranp_contract : contract := Contract G_PC ggranp_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma find_tail_spec : forall fs sh hi s2, find_tail fs sh hi = Some s2 -> In (FEq (VP s2 wzero) (VAlu ALU_ADD (VP sh wzero) hi)) fs.
Proof.
  induction fs as [|f fs IH]; intros sh hi s2 H; cbn [find_tail] in H; [discriminate|].
  destruct f as [| | | |x y| | |]; try (right; apply IH; exact H).
  destruct x as [|k2 o2| | | | | | | | |]; try (right; apply IH; exact H).
  destruct y as [| |op y1 y2| | | | | | | |]; try (right; apply IH; exact H).
  destruct op; try (right; apply IH; exact H).
  destruct y1 as [|k1 o1| | | | | | | | |]; try (right; apply IH; exact H).
  destruct (weqb o2 wzero && PrimInt63.eqb k1 sh && weqb o1 wzero && sv_eqb y2 hi) eqn:Q; [|right; apply IH; exact H].
  injection H as <-. apply andb_true_iff in Q as [Q Q4]. apply andb_true_iff in Q as [Q Q3]. apply andb_true_iff in Q as [Q1 Q2].
  apply (proj1 (weqb_ok _ _)) in Q1. apply (proj1 (weqb_ok _ _)) in Q3. apply Uint63.eqb_correct in Q2. apply sv_eqb_eq in Q4. subst. left. reflexivity.
Qed.

Lemma gran_len2_spec : forall hi n, gran_len2 hi = Some n -> hi = VAlu ALU_SRL n (VL GGran.w3).
Proof.
  intros hi n H. unfold gran_len2 in H.
  destruct hi as [| |op x y| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
  destruct y as [s| | | | | | | | | |]; try discriminate H.
  destruct (weqb s GGran.w3) eqn:E3; [|discriminate H]. injection H as <-. apply (proj1 (weqb_ok _ _)) in E3. subst s. reflexivity.
Qed.

Lemma pair_sel_den : forall E st ms model sh o hi, st_ok segs OPS E st ms model -> pair_sel RS OFF st = Some (sh, o, hi) ->
  den E (sv_alu ALU_ADD (getr st RS) (VL OFF)) = (ev E sh + den E o)%bv.
Proof.
  intros E st ms model sh o hi HS H. unfold pair_sel in H.
  destruct (addr_of (sv_alu ALU_ADD (getr st RS) (VL OFF))) as [[k o']|] eqn:A.
  - destruct (PrimInt63.eqb k 0%uint63); [discriminate|].
    destruct (IMap.find k (s_regs st)) as [r|]; [|discriminate]. destruct (rg_bg r); try discriminate. injection H as <- <- _.
    rewrite (addr_of_den E _ _ _ (so_zero _ _ _ _ _ _ HS) A). reflexivity.
  - destruct (sym_addr_of (s_regs st) (sv_alu ALU_ADD (getr st RS) (VL OFF))) as [[[k r] o']|] eqn:SA; [|discriminate].
    destruct (rg_bg r); try discriminate. injection H as <- <- _.
    exact (proj2 (sym_addr_of_sound E _ _ _ _ _ SA)).
Qed.

Theorem ggranp_sound : contract_sound segs OPS MP PB ggranp_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [ggranp_contract c_apply] in HA. unfold ggranp_apply in HA.
  destruct (pair_sel RS OFF st) as [[[sh o] hi]|] eqn:PS; [|discriminate].
  destruct (GGran.gran_src o) as [X|] eqn:GS; [|discriminate]. destruct (gran_len2 hi) as [n|] eqn:GL; [|discriminate].
  destruct (find_tail (s_facts st) sh hi) as [s2|] eqn:FT; [|discriminate].
  destruct (negb (r5_eqb RS X0)) eqn:RX; [|discriminate].
  destruct (decide_ltu (s_facts st) X n) as [[|]|] eqn:DL; try discriminate.
  cbn [andb] in HA. injection HA as <-.
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  pose proof (decide_ltu_sound E (s_facts st) FH X n true DL) as LT. apply (proj1 (ltu_iff _ _ true)) in LT.
  pose proof (GGran.gran_src_spec E o X GS) as DO. pose proof (gran_len2_spec hi n GL) as EH.
  assert (DH : bv_unsigned (den E hi) = bv_unsigned (den E n) / 8) by (rewrite EH; apply GGran.srl3_unsigned).
  assert (LE : bv_unsigned (den E o) <= bv_unsigned (den E hi)) by (rewrite DO, DH; apply Z.div_le_mono; lia).
  destruct (Z_lt_ge_dec (bv_unsigned (den E o)) (bv_unsigned (den E hi))) as [D|D].
  - refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP _).
    apply addfact_sound; [exact HS|]. cbn [fact_holds]. exact D.
  - assert (EQ : den E o = den E hi) by (apply bv_eq; lia).
    refine (Hk _ (or_intror (or_introl eq_refl)) E ms model (env_ext_refl (s_next st) E) HMP _).
    apply addfact_sound; [|cbn [fact_holds]; exact EQ].
    apply setreg_sound; [exact HS| |].
    + intros Q. rewrite Q in RX. cbn in RX. discriminate RX.
    +
      pose proof (pair_sel_den E st ms model sh o hi HS PS) as DA.
      rewrite den_sv_alu in DA. cbn [alu64 alu den] in DA.
      pose proof (find_tail_spec _ _ _ _ FT) as TI.
      pose proof (proj1 (Forall_forall _ _) FH _ TI) as TL. cbn [fact_holds den alu64 alu] in TL.
      apply bv_eq. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, wneg_ok.
      apply (f_equal bv_unsigned) in DA. rewrite !bv_add_unsigned, wbv_unsigned, EQ in DA.
      apply (f_equal bv_unsigned) in TL. rewrite !bv_add_unsigned, !wbv_unsigned in TL. change (w2Z wzero) with 0 in TL. rewrite !Z.add_0_r in TL.
      pose proof (bv_unsigned_in_range _ (den E (getr st RS))) as R1. pose proof (bv_unsigned_in_range _ (ev E s2)) as R2. pose proof (w2Z_range OFF) as R5.
      unfold bv_wrap in *. rewrite bv_modulus_64 in *.
      exact (mod_sub_help two64 _ _ _ _ _ ltac:(unfold two64; lia) R1 R5 DA TL R2).
Qed.

End Sound.
End WithPc.

Definition and7 (n : sv) : sv := VAlu ALU_AND n (VL GGran.w7).
Definition srl3 (n : sv) : sv := sv_alu ALU_SRL n (VL GGran.w3).
Definition pred_n (n : sv) : sv := sv_alu ALU_ADD n (VL wones).

Definition tail_cell (st : sstate) (s2 : int) : option sv :=
  match IMap.find s2 (s_regs st) with
  | Some r =>
      match IMap.find 0%uint63 (rg_cells r) with
      | Some (Gran _ (c :: _)) => if PrimInt63.eqb (c_idx c) 0%uint63 && PrimInt63.eqb (c_w c) 1%uint63 then Some (c_v c) else None
      | _ => None
      end
  | None => None
  end.
Definition and7_arg (v : sv) : option sv :=
  match v with
  | VAlu ALU_AND n (VL c) => if weqb c GGran.w7 then Some n else None
  | _ => None
  end.

Definition last_size (st : sstate) (s2 : int) (m : sv) : option sv :=
  match tail_cell st s2 with
  | Some c => match and7_arg c with
              | Some n => if sv_eqb (pred_n n) m then Some n else None
              | None => None
              end
  | None => None
  end.

Section WithPcL.
Variable G_PC : int.
Variable RS : r5.
Variable OFF : w64.

Definition ggranl_outs (st : sstate) (o hi : sv) (s2 : int) (n X : sv) : list sstate :=
  let st2 := addfact (setr st RS (VP s2 (wneg OFF))) (FEq o hi) in
  [addfact st (FULt o hi);
   addfact st2 (FEq (and7 n) (VL wzero));
   addfact (addfact (addfact st2 (FULt (VL wzero) (and7 n))) (FEq o (srl3 n))) (FULt (and7 X) (and7 n))].

Definition ggranl_apply (st : sstate) : option (list sstate) :=
  let fs := s_facts st in
  match pair_sel RS OFF st with
  | Some (sh, o, hi) =>
      match GGran.gran_src o, gran_len2 hi, find_tail fs sh hi with
      | Some X, Some m, Some s2 =>
          match last_size st s2 m with
          | Some n =>
              if negb (r5_eqb RS X0) && match decide_ltu fs X n with Some true => true | _ => false end
              then Some (ggranl_outs st o hi s2 n X) else None
          | None => None
          end
      | _, _, _ => None
      end
  | None => None
  end.

Definition ggranl_contract : contract := Contract G_PC ggranl_apply.

Section SoundL.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma den_pred_n : forall E n, bv_unsigned (den E (pred_n n)) = (bv_unsigned (den E n) + (two64 - 1)) mod two64.
Proof.
  intros E n. unfold pred_n. rewrite den_sv_alu. cbn [alu64 alu]. rewrite bv_add_unsigned, den_VL. replace (w2Z wones) with (two64 - 1) by (vm_compute; reflexivity).
  unfold bv_wrap. rewrite bv_modulus_64. reflexivity.
Qed.
Lemma den_and7 : forall E n, bv_unsigned (den E (and7 n)) = bv_unsigned (den E n) mod 8.
Proof.
  intros E n. unfold and7. cbn [den alu64 alu]. rewrite bv_and_unsigned, wbv_unsigned.
  change (w2Z GGran.w7) with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma den_srl3 : forall E n, bv_unsigned (den E (srl3 n)) = bv_unsigned (den E n) / 8.
Proof.
  intros E n. unfold srl3. rewrite den_sv_alu. change (alu64 ALU_SRL (den E n) (den E (VL GGran.w3))) with (den E (VAlu ALU_SRL n (VL GGran.w3))). apply GGran.srl3_unsigned.
Qed.
Lemma last_size_spec : forall st s2 m n, last_size st s2 m = Some n -> m = pred_n n.
Proof.
  intros st s2 m n H. unfold last_size in H. destruct (tail_cell st s2) as [c|]; [|discriminate]. destruct (and7_arg c) as [n'|]; [|discriminate].
  destruct (sv_eqb (pred_n n') m) eqn:Q; [|discriminate]. injection H as <-. apply sv_eqb_eq in Q. symmetry. exact Q.
Qed.

Lemma ggranl_cases : forall st sts E ms model, ggranl_apply st = Some sts -> st_ok segs OPS E st ms model ->
  exists a, In a sts /\ st_ok segs OPS E a ms model.
Proof.
  intros st sts E ms model HA HS. unfold ggranl_apply in HA.
  destruct (pair_sel RS OFF st) as [[[sh o] hi]|] eqn:PS; [|discriminate].
  destruct (GGran.gran_src o) as [X|] eqn:GS; [|discriminate]. destruct (gran_len2 hi) as [m|] eqn:GL; [|discriminate].
  destruct (find_tail (s_facts st) sh hi) as [s2|] eqn:FT; [|discriminate].
  destruct (last_size st s2 m) as [n|] eqn:LS; [|discriminate].
  destruct (negb (r5_eqb RS X0)) eqn:RX; [|discriminate].
  destruct (decide_ltu (s_facts st) X n) as [[|]|] eqn:DL; try discriminate.
  cbn [andb] in HA. injection HA as <-.
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  pose proof (decide_ltu_sound E (s_facts st) FH X n true DL) as LT. apply (proj1 (ltu_iff _ _ true)) in LT.
  pose proof (GGran.gran_src_spec E o X GS) as DO. pose proof (gran_len2_spec hi m GL) as EH.
  assert (DH : bv_unsigned (den E hi) = bv_unsigned (den E m) / 8) by (rewrite EH; apply GGran.srl3_unsigned).
  pose proof (last_size_spec st s2 m n LS) as EM.
  pose proof (bv_unsigned_in_range _ (den E X)) as RXz. pose proof (bv_unsigned_in_range _ (den E n)) as RN. rewrite bv_modulus_64 in RXz, RN.

  assert (MZ : bv_unsigned (den E m) = bv_unsigned (den E n) - 1).
  { rewrite EM, den_pred_n. replace (bv_unsigned (den E n) + (two64 - 1)) with (bv_unsigned (den E n) - 1 + 1 * two64) by lia.
    rewrite Z.mod_add by (unfold two64; lia). apply Z.mod_small. lia. }
  set (Xz := bv_unsigned (den E X)) in *. set (Nz := bv_unsigned (den E n)) in *.
  assert (LE : bv_unsigned (den E o) <= bv_unsigned (den E hi)) by (rewrite DO, DH, MZ; apply Z.div_le_mono; lia).

  assert (ST2 : den E o = den E hi -> st_ok segs OPS E (addfact (setr st RS (VP s2 (wneg OFF))) (FEq o hi)) ms model).
  { intros EQ. apply addfact_sound; [|cbn [fact_holds]; exact EQ].
    apply setreg_sound; [exact HS| |].
    + intros Q. rewrite Q in RX. cbn in RX. discriminate RX.
    + pose proof (pair_sel_den RS OFF segs OPS E st ms model sh o hi HS PS) as DA.
      rewrite den_sv_alu in DA. cbn [alu64 alu den] in DA.
      pose proof (find_tail_spec _ _ _ _ FT) as TI.
      pose proof (proj1 (Forall_forall _ _) FH _ TI) as TL. cbn [fact_holds den alu64 alu] in TL.
      apply bv_eq. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, wneg_ok.
      apply (f_equal bv_unsigned) in DA. rewrite !bv_add_unsigned, wbv_unsigned, EQ in DA.
      apply (f_equal bv_unsigned) in TL. rewrite !bv_add_unsigned, !wbv_unsigned in TL. change (w2Z wzero) with 0 in TL. rewrite !Z.add_0_r in TL.
      pose proof (bv_unsigned_in_range _ (den E (getr st RS))) as R1. pose proof (bv_unsigned_in_range _ (ev E s2)) as R2. pose proof (w2Z_range OFF) as R5.
      unfold bv_wrap in *. rewrite bv_modulus_64 in *.
      exact (mod_sub_help two64 _ _ _ _ _ ltac:(unfold two64; lia) R1 R5 DA TL R2). }
  unfold ggranl_outs.
  destruct (Z_lt_ge_dec (bv_unsigned (den E o)) (bv_unsigned (den E hi))) as [D|D].
  - eexists. split; [left; reflexivity|].
    apply addfact_sound; [exact HS|]. cbn [fact_holds]. exact D.
  - assert (EQ : den E o = den E hi) by (apply bv_eq; lia).
    pose proof (den_and7 E n) as DC. fold Nz in DC.
    pose proof (Z.mod_pos_bound Nz 8 ltac:(lia)) as RC.
    destruct (Z.eq_dec (Nz mod 8) 0) as [C0|C1].
    + eexists. split; [right; left; reflexivity|].
      apply addfact_sound; [exact (ST2 EQ)|]. cbn [fact_holds]. apply bv_eq. rewrite DC, C0, den_VL. reflexivity.
    + eexists. split; [right; right; left; reflexivity|].
      assert (Q8 : (Nz - 1) / 8 = Nz / 8).
      {
        pose proof (Z.div_mod Nz 8 ltac:(lia)) as A. pose proof (Z.div_mod (Nz - 1) 8 ltac:(lia)) as B.
        pose proof (Z.mod_pos_bound (Nz - 1) 8 ltac:(lia)) as RB. lia. }
      apply addfact_sound; [apply addfact_sound; [apply addfact_sound; [exact (ST2 EQ)|]|]|].
      * cbn [fact_holds]. rewrite den_VL, DC. change (w2Z wzero) with 0. lia.
      * cbn [fact_holds]. apply bv_eq. rewrite den_srl3, EQ, DH, MZ. fold Nz. exact Q8.
      *
        cbn [fact_holds]. rewrite (den_and7 E X), DC. fold Xz.
        assert (QX : Xz / 8 = Nz / 8) by (rewrite <- Q8, <- MZ, <- DH, <- EQ, DO; reflexivity).
        pose proof (Z.div_mod Nz 8 ltac:(lia)) as A. pose proof (Z.div_mod Xz 8 ltac:(lia)) as B. lia.
Qed.

Lemma ggranl_frame : forall st sts a, ggranl_apply st = Some sts -> In a sts ->
  s_ff a = s_ff st /\ s_resv a = s_resv st /\ s_regs a = s_regs st /\ s_ops a = s_ops st /\ s_priv a = s_priv st /\ s_next a = s_next st.
Proof.
  intros st sts a HA Hin. unfold ggranl_apply in HA.
  destruct (pair_sel RS OFF st) as [[[sh o] hi]|]; [|discriminate].
  destruct (GGran.gran_src o) as [X|]; [|discriminate]. destruct (gran_len2 hi) as [m|]; [|discriminate].
  destruct (find_tail (s_facts st) sh hi) as [s2|]; [|discriminate].
  destruct (last_size st s2 m) as [n|]; [|discriminate].
  match type of HA with (if ?c then _ else _) = _ => destruct c; [|discriminate] end. injection HA as <-.
  unfold ggranl_outs in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [addfact s_ff s_resv s_regs s_ops s_priv s_next]; unfold setr; destruct RS; cbn [s_ff s_resv s_regs s_ops s_priv s_next]; repeat split; reflexivity.
Qed.

Theorem ggranl_sound : contract_sound segs OPS MP PB ggranl_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [ggranl_contract c_apply] in HA.
  destruct (ggranl_cases st sts E ms model HA HS) as (a & Hin & HSa).
  exact (Hk a Hin E ms model (env_ext_refl (s_next st) E) HMP HSa).
Qed.

End SoundL.
End WithPcL.

End GGranP.
