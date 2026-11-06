(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec RefMemcpyLib ZStores.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VStepSound VStepMemSound VStepMemSound2 VCert VContract VContractSound VContractSound2 VState2 VStepMem2 VGamma2 VStepMem2SoundA VStepMem2SoundB VStepMem2SoundC VStepMem2SoundD VContractA VCert2 VContract2 VContract2Iface VContractASound1 VContractASound2.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma NoDup_map_inj {X Y} (f : X -> Y) l :
  (forall a b, List.In a l -> List.In b l -> f a = f b -> a = b) -> List.NoDup l -> List.NoDup (map f l).
Proof.
  intros INJ ND. induction ND as [|x l Hx ND IH]; cbn; constructor.
  - intros Hin. apply List.in_map_iff in Hin as (y & Ey & Hy). apply Hx.
    rewrite (INJ x y (or_introl eq_refl) (or_intror Hy) (eq_sym Ey)). exact Hy.
  - apply IH. intros a b Ha Hb. apply INJ; right; assumption.
Qed.

Lemma seqZ_facts (n : nat) : List.NoDup (map Z.of_nat (seq 0 n)) /\ (forall z, List.In z (map Z.of_nat (seq 0 n)) <-> 0 <= z < Z.of_nat n)
                                /\ length (map Z.of_nat (seq 0 n)) = n.
Proof.
  split; [|split; [|rewrite length_map, length_seq; reflexivity]].
  - apply NoDup_map_inj; [intros; lia|apply List.seq_NoDup].
  - intros z. rewrite List.in_map_iff. split.
    + intros (k & <- & Hk). apply List.in_seq in Hk. lia.
    + intros Hz. exists (Z.to_nat z). split; [lia|]. apply List.in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma positions_le_length (f : Z -> Z) (l : list Z) (n : nat) :
  (forall p q, 0 <= p < Z.of_nat n -> 0 <= q < Z.of_nat n -> f p = f q -> p = q) ->
  (forall p, 0 <= p < Z.of_nat n -> List.In (f p) l) ->
  (n <= length l)%nat.
Proof.
  intros INJ ALL. destruct (seqZ_facts n) as (ND & IN & LEN).
  rewrite <- LEN, <- (length_map f). apply List.NoDup_incl_length.
  - apply NoDup_map_inj; [|exact ND]. intros a b Ha Hb. apply IN in Ha. apply IN in Hb. apply INJ; assumption.
  - intros y Hy. apply List.in_map_iff in Hy as (p & <- & Hp). apply IN in Hp. apply ALL. exact Hp.
Qed.

Lemma pos_lt_ne0 (s x : positive) : (s < x)%positive -> s <> x. Proof. lia. Qed.
Lemma pos_lt_ne1 (s x : positive) : (s < x)%positive -> s <> Pos.succ x. Proof. lia. Qed.
Lemma pos_lt_ne2 (s x : positive) : (s < x)%positive -> s <> Pos.succ (Pos.succ x). Proof. lia. Qed.
Lemma pos_ne_s1 (x : positive) : x <> Pos.succ x. Proof. lia. Qed.
Lemma pos_ne_s2 (x : positive) : x <> Pos.succ (Pos.succ x). Proof. lia. Qed.
Lemma pos_s1_ne_s2 (x : positive) : Pos.succ x <> Pos.succ (Pos.succ x). Proof. lia. Qed.
Lemma pos_le_s3 (x : positive) : (x <= Pos.succ (Pos.succ (Pos.succ x)))%positive. Proof. lia. Qed.
Lemma pos_lt_s3 (x : positive) : (x < Pos.succ (Pos.succ (Pos.succ x)))%positive. Proof. lia. Qed.

(* [comment removed for export] *)
Lemma store_ok1_ext segs (m1 m2 : word -> option byte) (x : word) :
  m1 x = m2 x -> store_ok segs m1 x 1 = store_ok segs m2 x 1.
Proof. intros H. cbn [store_ok]. unfold wview. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RW.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variable mem0 : word -> option byte.
  Let P1 := p1 P.
  Let E1 := ev1 E.
  Hypothesis PO2 : params_ok2 SEGS P.

  (* [comment removed for export] *)
  Definition rw_change (mem mem' : word -> option byte) : Prop :=
       (forall y, 0 <= y < 2 ^ 64 -> in_rw_zones P E y = false -> mem' (wordZ y) = mem (wordZ y))
    /\ (forall x, mem x <> None -> mem' x <> None)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS mem' x 1 = true).

  Lemma rw_change_refl mem : rw_change mem mem.
  Proof. split; [intros; reflexivity|]. split; auto. Qed.

  Lemma rw_change_trans m1 m2 m3 : rw_change m1 m2 -> rw_change m2 m3 -> rw_change m1 m3.
  Proof.
    intros (A1 & A2 & A3) (B1 & B2 & B3). split; [|split; auto].
    intros y Hy Hz. rewrite (B1 y Hy Hz). apply A1; auto.
  Qed.

  Lemma rw_change_block mem a bs :
    0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
    (forall i, 0 <= i < Z.of_nat (length bs) -> in_rw_zones P E (a + i) = true) ->
    rw_change mem (wbytes mem (wordZ a) bs).
  Proof.
    intros Ha Hl HZ. split; [|split].
    - intros y Hy Hn. destruct bs as [|b0 bs']; [reflexivity|]. cbn [length] in *. rewrite Nat2Z.inj_succ in *.
      apply wblock_byte; cbn [length]; rewrite ?Nat2Z.inj_succ; try lia. intros IN. specialize (HZ (y - a) ltac:(lia)).
      replace (a + (y - a)) with y in HZ by lia. congruence.
    - intros x Hx. apply (wbytes_grows bs mem (wordZ a)). exact Hx.
    - intros x Hx. eapply store_ok_mono; [apply wbytes_grows|exact Hx].
  Qed.

  Lemma rdn_rw_out mem mem' a n :
    rw_change mem mem' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (forall i, 0 <= i < Z.of_nat n -> in_rw_zones P E (a + i) = false) ->
    rdn SEGS mem' (wordZ a) n = rdn SEGS mem (wordZ a) n.
  Proof.
    intros (R1 & _) Ha Hn HO. destruct n as [|n]; [reflexivity|]. rewrite Nat2Z.inj_succ in *.
    apply rdn_ext; [rewrite u_wordZ, ?Nat2Z.inj_succ; lia|].
    intros x Hx. rewrite Nat2Z.inj_succ in Hx. rewrite u_wordZ in Hx by lia. rewrite <- (wordZ_u x).
    pose proof (bv_unsigned_in_range 64 x) as BX. change (bv_modulus 64) with (2 ^ 64) in BX. apply R1; [lia|].
    replace (bv_unsigned x) with (a + (bv_unsigned x - a)) by lia. apply HO. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma v1_rw_change A1 nu regs mem mem' :
    env_ok2 P E ->
    (forall g w v, In (g, (w, v)) (vs_globs A1) -> exists f, In f (vp_fcells P1) /\ fst f <= g /\ g + w <= fst f + snd f) ->
    gamma SEGS P1 E1 (zpatch P E mem0 mem) A1 nu regs mem ->
    rw_change mem mem' ->
    gamma SEGS P1 E1 (zpatch P E mem0 mem') A1 nu regs mem'.
  Proof.
    intros HE GL HG RW. pose proof RW as (R1 & GR & SOK).
    pose proof HG as (HE1 & HM & HF & HS & HC & HMo & HV & HR & HSl & HGl & HN & HB).
    (* [comment removed for export] *)
    assert (KEEP : forall y, 0 <= y < 2 ^ 64 ->
              (e_sp0 E1 - vp_frame P1 <= y < e_sp0 E1 \/ (exists c, In c (vp_fcells P1) /\ fst c <= y < fst c + snd c)
               \/ (exists lo hi, In (lo, hi) (vp_pristine P1) /\ lo <= y < hi)) ->
              in_rw_zones P E y = false).
    { intros y Hy Hc. destruct (in_rw_zones P E y) eqn:ZY; [|reflexivity]. exfalso.
      destruct (rw_byte_apart P E y HE ZY) as (N1 & N2 & N3 & N4 & _).
      destruct Hc as [Hc|[(c & Hc & Hcy)|(lo & hi & Hp & Hlh)]]; [exact (N1 Hc)|exact (N2 c Hc Hcy)|exact (N4 lo hi Hp Hlh)]. }
    pose proof (PO1 _ _ PO2) as (POfr & POsphi & POsegs & POfc & POwc & POws & POpr & POrom).
    pose proof HE1 as (Esp16 & Esp & Esz & Ed0 & Edpos & Ed63 & Era & Etp & Egp & Esregs & Efrsp).
    assert (SPHI : e_sp0 E1 < 2 ^ 64) by (unfold P1, E1 in *; lia).
    assert (RD : forall a n, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
              (forall i, 0 <= i < Z.of_nat n ->
                 e_sp0 E1 - vp_frame P1 <= a + i < e_sp0 E1 \/ (exists c, In c (vp_fcells P1) /\ fst c <= a + i < fst c + snd c)
                 \/ (exists lo hi, In (lo, hi) (vp_pristine P1) /\ lo <= a + i < hi)) ->
              rdn SEGS mem' (wordZ a) n = rdn SEGS mem (wordZ a) n).
    { intros a n Ha Hn Hi. apply (rdn_rw_out mem mem' a n RW Ha Hn). intros i Hii. apply KEEP; [lia|]. apply Hi. exact Hii. }
    split; [exact HE1|]. split.
    { (* [comment removed for export] *)
      destruct HM as (MF & MD & MP & MFM). split; [|split; [|split]].
      - intros x Hx. destruct (MF x Hx) as [S1 Q1]. split; [apply SOK; exact S1|].
        eapply (VContractASound2.rdn1_grows SEGS mem mem'); [apply GR|exact Q1].
      - intros i Hi. eapply (VContractASound2.rdn1_grows SEGS mem mem'); [apply GR|exact (MD i Hi)].
      - intros lo hi x Hp Hx. destruct (POpr _ _ Hp) as [L0 H0].
        rewrite R1; [exact (MP lo hi x Hp Hx)|unfold P1 in *; lia|].
        apply KEEP; [unfold P1 in *; lia|]. right; right. exists lo, hi. auto.
      - split.
        + intros y Hout. unfold zpatch. destruct (in_rw_zones P E (bv_unsigned y)) eqn:ZY; [reflexivity|].
          pose proof (proj1 MFM y Hout) as OLD. unfold zpatch in OLD. rewrite ZY in OLD.
          rewrite <- OLD. rewrite <- (wordZ_u y). pose proof (bv_unsigned_in_range 64 y). change (bv_modulus 64) with (2 ^ 64) in *.
          apply R1; [lia|exact ZY].
        + intros y Hy. unfold zpatch in Hy. destruct (in_rw_zones P E (bv_unsigned y)) eqn:ZY; [exact Hy|].
          apply GR. apply (proj2 MFM y). unfold zpatch. rewrite ZY. exact Hy. }
    split; [exact HF|]. split; [exact HS|]. split; [exact HC|]. split; [exact HMo|]. split; [exact HV|].
    split; [|split; [|split; [|split; [|exact HB]]]].
    - intros r' e Hr' Hg. exact (HR r' e Hr' Hg).
    - (* [comment removed for export] *)
      intros off w v Hin. destruct (HSl off w v Hin) as [Hrg Hch]. split; [exact Hrg|].
      eapply cell_holds_same; [|exact Hch]. apply RD; [unfold P1, E1 in *; lia|rewrite Z2Nat.id by lia; unfold P1, E1 in *; lia|].
      intros i Hi. left. rewrite Z2Nat.id in Hi by lia. unfold P1, E1 in *. lia.
    - (* [comment removed for export] *)
      intros g w v Hin. destruct (HGl g w v Hin) as [Hrg Hch]. split; [exact Hrg|].
      destruct (GL g w v Hin) as (f & Hf & F1 & F2). destruct (POfc f Hf) as (Q1 & Q2 & _).
      eapply cell_holds_same; [|exact Hch]. apply RD; [unfold P1 in *; lia|rewrite Z2Nat.id by lia; unfold P1 in *; lia|].
      intros i Hi. right; left. exists f. split; [exact Hf|]. rewrite Z2Nat.id in Hi by lia. lia.
    - (* [comment removed for export] *)
      intros lo hi Hin. destruct (HN lo hi Hin) as (off & b & Q1 & Q2 & Q3 & Q4). exists off, b.
      split; [exact Q1|]. split; [exact Q2|]. split; [|exact Q4]. rewrite <- Q3.
      apply RD; [unfold P1, E1 in *; lia|cbn; unfold P1, E1 in *; lia|]. intros i Hi. left. cbn in Hi. unfold P1, E1 in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma MC2_rw_change mem mem' :
    env_ok2 P E -> MC2 SEGS P E mem0 mem -> rw_change mem mem' ->
    (forall cp, In cp (e_live E) -> mem' (wordZ (flag_addr (e_fs E) (fst cp) (snd cp))) = mem (wordZ (flag_addr (e_fs E) (fst cp) (snd cp)))) ->
    MC2 SEGS P E mem0 mem'.
  Proof.
    intros HE (K & Zo & DS & LF & RT & KR) RW HLF. pose proof RW as (R1 & GR & SOK).
    pose proof HE as (HE1 & HD2 & HF & HZN & [KC KRC]).
    assert (RD : forall a n, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
              (forall i, 0 <= i < Z.of_nat n -> in_rw_zones P E (a + i) = false) ->
              rdn SEGS mem' (wordZ a) n = rdn SEGS mem (wordZ a) n)
      by (intros; eapply rdn_rw_out; eauto).
    split; [|split; [|split; [|split; [|split]]]].
    - (* [comment removed for export] *)
      intros k w v Hin. destruct (K k w v Hin) as (K0 & W0 & KW & bs0 & Hr & Hv). split; [lia|]. split; [lia|]. split; [lia|].
      exists bs0. split; [|exact Hv]. rewrite <- Hr. apply RD; rewrite ?Z2Nat.id by lia; try lia.
      intros i Hi. exact (proj1 (KC (k, (w, v)) (k + i) Hin ltac:(cbn; lia))).
    - (* [comment removed for export] *)
      intros z y Hz Hy. destruct (Zo z y Hz Hy) as [[b Hb] Hw]. split; [eapply (VContractASound2.rdn1_grows SEGS mem mem'); [apply GR|exists b; exact Hb]|].
      intros Hrw. apply SOK. exact (Hw Hrw).
    - (* [comment removed for export] *)
      intros Hal Hfs. destruct (DS Hal Hfs) as (D1 & D2 & D3).
      unfold env_fs in HF. destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|congruence].
      destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & Hdat & Hnrw & _).
      destruct (PO2_fs _ _ PO2 ltac:(rewrite Efs; discriminate)) as [SH _].
      pose proof HE1 as (_ & _ & Hsz & _ & Hdpos & _).
      split.
      + intros g Hg. destruct (D1 g Hg) as (k & Hk & K1 & K2). exists k. split; [|auto]. rewrite <- Hk.
        destruct (Hdat ltac:(lia)) as [HD3 HD4]. unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
        unfold shadow_byte in *.
        pose proof (Z.div_mod (e_data E1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_data E1) 8 ltac:(lia)).
        pose proof (Z.div_mod (e_data E1 + e_size E1 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_data E1 + e_size E1 - 1) 8 ltac:(lia)).
        unfold E1 in *.
        apply RD; [lia|cbn; lia|]. intros i Hi. cbn in Hi. apply Hnrw; lia.
      + split.
        * intros y Hy Hpos. destruct (D2 y Hy Hpos) as [b Hb]. exists b. rewrite <- Hb.
          destruct (Hdat Hpos) as [HD3 HD4]. unfold HIGH_MEM_BEG, HIGH_MEM_END in *. unfold shadow_byte in *.
          pose proof (Z.div_mod (e_data E1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_data E1) 8 ltac:(lia)).
          pose proof (Z.div_mod (e_data E1 + e_size E1 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_data E1 + e_size E1 - 1) 8 ltac:(lia)).
          pose proof (PO2_shoff _ _ PO2). unfold E1 in *.
          apply RD; [lia|cbn; lia|]. intros i Hi. cbn in Hi. apply Hnrw; lia.
        * intros Hpos a Ha. destruct (D3 Hpos a Ha) as [b Hb]. exists b. rewrite <- Hb.
          destruct (Hdat Hpos) as [HD3 HD4]. unfold HIGH_MEM_BEG, HIGH_MEM_END in *. unfold shadow_byte in *.
          pose proof (Z.div_mod (e_data E1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_data E1) 8 ltac:(lia)).
          pose proof (Z.div_mod (e_data E1 + e_size E1 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_data E1 + e_size E1 - 1) 8 ltac:(lia)).
          pose proof (Z.div_mod (vp_shoff P + e_data E1 / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (vp_shoff P + e_data E1 / 8) 8 ltac:(lia)).
          pose proof (Z.div_mod (vp_shoff P + (e_data E1 + e_size E1 - 1) / 8) 8 ltac:(lia)).
          pose proof (Z.mod_pos_bound (vp_shoff P + (e_data E1 + e_size E1 - 1) / 8) 8 ltac:(lia)).
          pose proof (PO2_shoff _ _ PO2). unfold E1 in *.
          apply RD; [lia|cbn; lia|]. intros i Hi. cbn in Hi. apply Hnrw; lia.
    - (* [comment removed for export] *)
      intros cp Hcp. destruct (LF cp Hcp) as (b & Hb & Hb1). exists b. split; [|exact Hb1]. rewrite <- Hb.
      cbn [rdn]. rewrite (HLF cp Hcp). reflexivity.
    - (* [comment removed for export] *)
      unfold rtctx_ok in RT |- *. destruct (vp_fs P) as [fsv|]; [|exact I].
      destruct RT as (tsd & ctx & thr & db & beg & C1 & C2 & C3 & C4 & C5 & NZ1 & C6 & NZ2 & C7 & C8 & NZ3 & NZ4 & C9 & NZ5).
      assert (TC : forall a w v, rt_cell SEGS P E mem a w v -> rt_cell SEGS P E mem' a w v).
      { intros a w v (Q0 & Q1 & Q2 & AP & Q3). split; [exact Q0|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact AP|].
        rewrite <- Q3. apply RD; rewrite ?Z2Nat.id by lia; try lia. intros i Hi. exact (proj1 (AP (a + i) ltac:(lia))). }
      assert (TR : forall a w, rt_readable SEGS P E mem a w -> rt_readable SEGS P E mem' a w).
      { intros a w (Q0 & Q2 & AP & Q3). split; [exact Q0|]. split; [exact Q2|]. split; [exact AP|].
        intros i Hi. destruct (Q3 i Hi) as [b Hb]. exists b. rewrite <- Hb. apply RD; [lia|cbn; lia|].
        intros j Hj. cbn in Hj. replace (a + i + j) with (a + i) by lia. exact (proj1 (AP (a + i) ltac:(lia))). }
      exists tsd, ctx, thr, db, beg.
      split; [apply TC; exact C1|]. split; [apply TC; exact C2|]. split; [apply TC; exact C3|]. split; [apply TC; exact C4|].
      split; [apply TC; exact C5|]. split; [exact NZ1|]. split; [apply TC; exact C6|]. split; [exact NZ2|].
      split; [apply TR; exact C7|]. split; [apply TC; exact C8|]. split; [exact NZ3|]. split; [exact NZ4|].
      split; [apply TC; exact C9|exact NZ5].
    - (* [comment removed for export] *)
      intros lo hi b Hin. destruct (KR lo hi b Hin) as (L0 & H64 & Hb). split; [lia|]. split; [lia|].
      intros y Hy. destruct (Hb y Hy) as (k & Hk & Hv). exists k. split; [|exact Hv]. rewrite <- Hk.
      apply RD; [lia|cbn; lia|]. intros i Hi. cbn in Hi. replace (y + i) with y by lia.
      exact (proj1 (proj2 (KRC (lo, (hi, b)) y Hin ltac:(cbn; lia)))).
  Qed.
End RW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variables mem0 rom : word -> option byte.
  Variable CI : cimg.
  Let P1 := p1 P.
  Let E1 := ev1 E.
  Hypothesis PO2 : params_ok2 SEGS P.
  #[warnings="-notation-for-abbreviation"] Notation gamma2P := (gamma2 SEGS P E mem0).

  Hypothesis SHOFF : vp_shoff P = SBz.
  (* [comment removed for export] *)
  Definition zone_covers (b : sym) (d lo hi : Z) : Prop :=
    exists z l h, In z (vp_fzones P) /\ fz_base z = b /\ fz_disp z = d /\ fz_rw z = true
                  /\ fz_lo z = lconst l /\ fz_hi z = lconst h /\ l <= lo /\ hi <= h.
  Hypothesis Z_HINTS : zone_covers FSB 0 0 88.
  Hypothesis Z_FLAGS : zone_covers FSB 0 FS_FLAGS FS_FRAMES.
  Hypothesis Z_FRAMES : zone_covers FSB 0 FS_FRAMES (FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL).
  Hypothesis Z_FSHAD : zone_covers FS8 SBz (FS_FRAMES / 8) ((FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) / 8).

  Variable cid : Z.
  Hypothesis Hcid : 0 <= cid <= 4.
  Variable tgt : Z.
  (* [comment removed for export] *)
  Variable MCELLS : (word -> option byte) -> Prop.
  Hypothesis MCELLS_OK : forall A nu regs mem, gamma2P A nu regs mem -> MCELLS mem.
  (* [comment removed for export] *)
  Variable TSD : Z.
  Hypothesis TSD_OK : forall A nu regs mem bs, gamma2P A nu regs mem ->
    rdn SEGS mem (wordZ (vp_tp P - 88)) 8 = Some bs -> bytes_le_to_Z bs = TSD.

  Definition K208 : Z := 208.

  (* [comment removed for export] *)
  Definition in_blocks (fs usp p : Z) (y : Z) : Prop :=
       (fs + 8 * cid <= y < fs + 8 * cid + 8)
    \/ y = flag_addr fs cid p
    \/ (frame_addr fs cid p + 24 <= y < frame_addr fs cid p + 32)
    \/ (frame_addr fs cid p + fake_size cid - 8 <= y < frame_addr fs cid p + fake_size cid)
    \/ (SBz + frame_addr fs cid p / 8 <= y < SBz + frame_addr fs cid p / 8 + fake_size cid / 8).
  Definition effect (mem mZ : word -> option byte) (fs usp p : Z) : Prop :=
       (forall y, 0 <= y < 2 ^ 64 -> ~ in_blocks fs usp p y -> mZ (wordZ y) = mem (wordZ y))
    /\ rdn SEGS mZ (wordZ (flag_addr fs cid p)) 1 = Some [Z_to_bv 8 1]
    /\ rdn SEGS mZ (wordZ (frame_addr fs cid p + 24)) 8 = Some (word_to_le_bytes 8 (wordZ usp))
    /\ rdn SEGS mZ (wordZ (frame_addr fs cid p + fake_size cid - 8)) 8 = Some (word_to_le_bytes 8 (wordZ (flag_addr fs cid p)))
    /\ (forall g, 0 <= g < fake_size cid / 8 -> rdn SEGS mZ (wordZ (SBz + frame_addr fs cid p / 8 + g)) 1 = Some [Z_to_bv 8 0])
    /\ (forall x, mem x <> None -> mZ x <> None)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS mZ x 1 = true).

  Definition RUN_spec : Prop := forall mem (usp tp fs tsd ctx thr db beg : Z) (a2v a3v hint : word) (FL : Z -> byte) (p0 : Z) regs (ra : word),
    MCELLS mem -> tp = vp_tp P ->
    (* [comment removed for export] *)
    rdn SEGS mem (wordZ tp) 8 = Some (word_to_le_bytes 8 (wordZ fs)) ->
    rdn SEGS mem (wordZ (tp - 88)) 8 = Some (word_to_le_bytes 8 (wordZ tsd)) -> tsd = TSD ->
    rdn SEGS mem (wordZ tsd) 8 = Some (word_to_le_bytes 8 (wordZ ctx)) -> 0 < ctx -> ctx + 160 <= 2 ^ 64 ->
    rdn SEGS mem (wordZ (ctx + 152)) 8 = Some (word_to_le_bytes 8 (wordZ thr)) -> 0 < thr -> thr + 64 <= 2 ^ 64 ->
    rdn SEGS mem (wordZ (thr + 48)) 8 = Some (word_to_le_bytes 8 a2v) ->
    rdn SEGS mem (wordZ (thr + 56)) 8 = Some (word_to_le_bytes 8 a3v) ->
    rdn SEGS mem (wordZ (tp + 8)) 8 = Some (word_to_le_bytes 8 (wordZ db)) -> 0 < db -> db + 32 <= 2 ^ 64 -> db <> 2 ^ 64 - 1 ->   (* [comment removed for export] *)
    rdn SEGS mem (wordZ (db + 24)) 8 = Some (word_to_le_bytes 8 (wordZ beg)) -> 0 < beg < 2 ^ 64 ->
    (ctx + 160 <= usp - K208 \/ usp <= ctx + 152) -> (thr + 64 <= usp - K208 \/ usp <= thr + 48) -> (db + 32 <= usp - K208 \/ usp <= db + 24) ->
    (* [comment removed for export] *)
    rdn SEGS mem (wordZ (fs + 96)) 1 = Some [Z_to_bv 8 0] ->
    rdn SEGS mem (wordZ (fs + 88)) 8 = Some (word_to_le_bytes 8 (wordZ 20)) ->
    (* [comment removed for export] *)
    vp_imgend P <= fs -> off_band fs (FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) -> fs + FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL <= 2 ^ 47 -> fs mod 4096 = 0 ->
    (fs + FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL <= usp - K208 \/ usp <= fs) ->
    (* [comment removed for export] *)
    HIGH_MEM_BEG + K208 <= usp -> usp + 16 <= 2 ^ 64 ->
    (forall a, usp - K208 <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true) ->
    (* [comment removed for export] *)
    rdn SEGS mem (wordZ (fs + 8 * cid)) 8 = Some (word_to_le_bytes 8 hint) ->
    (forall p, 0 <= p < fs_nframes cid -> rdn SEGS mem (wordZ (flag_addr fs cid p)) 1 = Some [FL p]) ->
    0 <= p0 < fs_nframes cid -> bv_unsigned (FL p0) = 0 ->
    (forall j, 0 <= j < 8 -> store_ok SEGS mem (wordZ (fs + 8 * cid + j)) 1 = true) ->
    (forall p, 0 <= p < fs_nframes cid -> store_ok SEGS mem (wordZ (flag_addr fs cid p)) 1 = true) ->
    (forall p j, 0 <= p < fs_nframes cid -> 0 <= j < fake_size cid -> store_ok SEGS mem (wordZ (frame_addr fs cid p + j)) 1 = true) ->
    (forall p j, 0 <= p < fs_nframes cid -> 0 <= j < fake_size cid / 8 -> store_ok SEGS mem (wordZ (SBz + frame_addr fs cid p / 8 + j)) 1 = true) ->
    (* [comment removed for export] *)
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = wordZ usp -> getr regs 4%bv = wordZ tp ->
    exists i p regs' m' mZ,
         0 <= i < fs_nframes cid /\ p = (bv_unsigned hint + i) mod fs_nframes cid /\ bv_unsigned (FL p) = 0
      /\ msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra m' rom)
      /\ getr regs' 10%bv = wordZ (frame_addr fs cid p) /\ getr regs' 2%bv = wordZ usp /\ getr regs' 1%bv = ra
      /\ (forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r)
      /\ effect mem mZ fs usp p
      /\ (forall x : word, (bv_unsigned x < usp - K208 \/ usp <= bv_unsigned x) -> m' x = mZ x)
      /\ (forall x, mem x <> None -> m' x <> None).
  (* [comment removed for export] *)
  Hypothesis RUN : RUN_spec.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ca_stack_malloc_inv A spoff l :
    contract_apply2 P CI (C_stack_malloc cid) A spoff = CR2OkN l ->
    exists ea etp fsr,
      asan_mode P = true
      /\ get_reg2 A 4 = Some etp /\ etp = lconst (ci_tp CI)
      /\ get_reg2 A A0r = Some ea /\ lin_is_const ea = true /\ 0 < lc ea <= fake_size cid
      /\ rgn_get (vs_rgn A) FSB = Some fsr /\ vr_kind fsr = RK_fs
      /\ Z.of_nat (length (vs_live A)) < 8
      /\ vp_fdepth P + Z.of_nat (length (vs_live A)) + 1 <= fs_nframes cid
      /\ let A1 := v1 A in let FF := vs_next A1 in let FL := Pos.succ FF in let F8 := Pos.succ FL in
         let A2 := set_next A1 (Pos.succ F8) in
         let lo_off := FS_FRAMES_OFF + Z.shiftl cid FS_LOG in
         let hi_off := FS_FRAMES_OFF + Z.shiftl (cid + 1) FS_LOG - fake_size cid in
         let '(ok1, A3) := aassume2 A2 (lsub (laddc (lsym FSB) lo_off) (lsym FF)) (laddc (lsub (lsym FF) (lsym FSB)) (- hi_off)) in
         let '(ok2, A4) := ameet_cong A3 FF (fake_size cid) 0 in
         let '(ok3, A5) := aassume2 A4 (lsub (laddc (lsym FSB) 4096) (lsym FL)) (laddc (lsub (lsym FL) (lsym FSB)) (- (4096 + 32768 - 1))) in
         let '(ok4, A6) := aassume2 A5 (lsub (lscale 8 (lsym F8)) (lsym FF)) (lsub (lsym FF) (lscale 8 (lsym F8))) in
         ok1 = true /\ ok2 = true /\ ok3 = true /\ ok4 = true /\
         let spc := match get_reg2 A 2 with Some e => [(24, (8, Some e))] | None => [] end in
         let fake := mkVR FF 0 (RK_fake cid FL) 0 (fake_size cid) [(0, fake_size cid)] (spc ++ [(fake_size cid - 8, (8, Some (lsym FL)))])%list [] (Some F8) in
         let shad := mkVR F8 (vp_shoff P) (RK_shadow FF) 0 (fake_size cid / 8) [(0, fake_size cid / 8)] [(0, (fake_size cid / 8, Some (lconst 0)))] [] None in
         let flag := mkVR FL 0 (RK_flag FF) 0 1 [(0, 1)] [] [] None in
         l = [(mkVS2 A6 (flag :: shad :: fake :: rgn_of_kill (vs_rgn A) FSB (8 * cid) (8 * cid + 8)) (FF :: vs_live A)
                     (pm_set F8 (lsym FF, 8) (vs_divdef A)) [], Some (lsym FF))].
  Proof.
    cbn [contract_apply2]. unfold of_ca, ca_stack_malloc. change (Z.shiftl 64 cid) with (fake_size cid).
    destruct (asan_mode P); cbn [negb]; [|discriminate].
    destruct ((0 <=? cid) && (cid <=? 4)); cbn [negb]; [|discriminate].
    destruct (get_reg2 A 4) as [etp|]; cbn [negb]; [|discriminate].
    destruct (lin_eqb etp (lconst (ci_tp CI))) eqn:ETP; cbn [negb]; [|discriminate]. apply lin_eqb_eq in ETP.
    destruct (get_reg2 A A0r) as [ea|]; [|discriminate].
    destruct (lin_is_const ea && (0 <? lc ea) && (lc ea <=? fake_size cid)) eqn:EA; cbn [negb]; [|discriminate].
    apply andb_prop in EA as [EA EA3]. apply andb_prop in EA as [EA1 EA2]. apply Z.ltb_lt in EA2. apply Z.leb_le in EA3.
    destruct (rgn_get (vs_rgn A) FSB) as [fsr|]; [|discriminate].
    destruct (vr_kind fsr) eqn:KF; cbn [negb]; try discriminate.
    destruct (Z.leb_spec 8 (Z.of_nat (length (vs_live A)))); [discriminate|].
    rewrite (Z.shiftl_1_l (14 - cid)). change (2 ^ (14 - cid)) with (fs_nframes cid).
    destruct (Z.leb_spec (vp_fdepth P + Z.of_nat (length (vs_live A)) + 1) (fs_nframes cid)); cbn [negb]; [|discriminate].
    cbv zeta.
    destruct (aassume2 _ _ _) as [ok1 A3] eqn:E3. destruct (ameet_cong A3 _ _ _) as [ok2 A4] eqn:E4.
    destruct (aassume2 A4 _ _) as [ok3 A5] eqn:E5. destruct (aassume2 A5 _ _) as [ok4 A6] eqn:E6.
    destruct ok1, ok2, ok3, ok4; cbn [negb andb]; try discriminate.
    intros HC. injection HC as <-.
    exists ea, etp, fsr. repeat split; try reflexivity; try assumption; try lia.
  Qed.

  Hypothesis CITP : ci_tp CI = vp_tp P.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fake_size_pow : fake_size cid = 64 * 2 ^ cid.
  Proof. unfold fake_size. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

  Lemma fake_size_div8 : fake_size cid / 8 * 8 = fake_size cid /\ 8 <= fake_size cid / 8 <= 128.
  Proof.
    rewrite fake_size_pow. assert (1 <= 2 ^ cid <= 16).
    { split; [assert (0 < 2 ^ cid) by (apply Z.pow_pos_nonneg; lia); lia|]. change 16 with (2 ^ 4). apply Z.pow_le_mono_r; lia. }
    replace (64 * 2 ^ cid) with (8 * 2 ^ cid * 8) by lia. rewrite Z.div_mul by lia. lia.
  Qed.

  Lemma frame_facts fs p : fs mod 4096 = 0 -> 0 <= p < fs_nframes cid ->
    fs + FS_FRAMES + cid * 2 ^ FS_SSL <= frame_addr fs cid p
    /\ frame_addr fs cid p + fake_size cid <= fs + FS_FRAMES + (cid + 1) * 2 ^ FS_SSL
    /\ frame_addr fs cid p mod fake_size cid = 0 /\ frame_addr fs cid p mod 8 = 0.
  Proof.
    intros Hfs Hp. destruct (frame_in_class fs cid p ltac:(lia) ltac:(lia) Hp) as [A B].
    pose proof fake_size_pow as FP. pose proof (fake_size_bounds cid Hcid) as FB.
    assert (D1 : (fake_size cid | 1024)).
    { rewrite FP. exists (2 ^ (4 - cid)). replace 1024 with (64 * (2 ^ (4 - cid) * 2 ^ cid)); [lia|].
      rewrite <- Z.pow_add_r by lia. replace (4 - cid + cid) with 4 by lia. reflexivity. }
    assert (M : frame_addr fs cid p mod fake_size cid = 0).
    { unfold frame_addr, FS_FRAMES, FS_SSL. apply Z.mod_divide; [lia|].
      destruct D1 as [k Hk].
      apply Z.divide_add_r; [|exists p; lia].
      apply Z.divide_add_r; [|exists (cid * 1024 * k); rewrite <- Z.mul_assoc, <- Hk; lia].
      apply Z.divide_add_r; [|exists (36 * k); rewrite <- Z.mul_assoc, <- Hk; lia].
      apply Z.mod_divide in Hfs; [|lia]. destruct Hfs as [q Hq]. exists (q * 4 * k). rewrite <- Z.mul_assoc, <- Hk. lia. }
    split; [exact A|]. split; [exact B|]. split; [exact M|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in M; [|lia]. destruct M as [k Hk].
    rewrite FP in Hk. exists (k * 8 * 2 ^ cid). rewrite Hk. lia.
  Qed.

  Lemma flag_facts fs p : 0 <= p < fs_nframes cid ->
    fs + FS_FLAGS <= flag_addr fs cid p < fs + FS_FRAMES.
  Proof. intros Hp. pose proof (flag_addr_range fs cid p Hcid Hp). unfold FS_FLAGS, FS_FRAMES in *. lia. Qed.

  Lemma zone_covers_sound A nu regs mem b d lo hi a :
    gamma2P A nu regs mem -> zone_covers b d lo hi ->
    d + nuE E b + lo <= a < d + nuE E b + hi ->
    in_rw_zones P E a = true /\ (exists k, rdn SEGS mem (wordZ a) 1 = Some [k]) /\ store_ok SEGS mem (wordZ a) 1 = true.
  Proof.
    intros HG2 (z & l & h & Hz & Hb & Hd & Hrw & Hl & Hh & L1 & L2) Ha. pose proof HG2 as (_ & _ & (_ & ZOK & _) & _).
    assert (IZ : in_zone E a z).
    { unfold in_zone, zone_lo, zone_hi. rewrite Hb, Hd, Hl, Hh, !eval_lconst. lia. }
    destruct (ZOK z a Hz IZ) as [R W]. split; [|split; [exact R|exact (W Hrw)]].
    unfold in_rw_zones, rw_zones. apply existsb_exists. exists z. split; [apply filter_In; auto|].
    unfold in_zoneb. unfold in_zone in IZ. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  Qed.

  Lemma nuE_FSB : nuE E FSB = e_fs E.
  Proof. unfold nuE, fix_val2. replace (fix_val (ev1 E) FSB) with (@None Z) by reflexivity. reflexivity. Qed.
  Lemma nuE_FS8 : nuE E FS8 = e_fs E / 8.
  Proof. unfold nuE, fix_val2. replace (fix_val (ev1 E) FS8) with (@None Z) by reflexivity. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma apart_window a w usp : (forall x, a <= x < a + w -> ~ (e_sp0 E1 - vp_frame P1 <= x < e_sp0 E1)) ->
    0 < w -> e_sp0 E1 - vp_frame P1 <= usp - K208 -> usp <= e_sp0 E1 ->
    a + w <= usp - K208 \/ usp <= a.
  Proof.
    intros AP Hw L1 L2. unfold K208 in *.
    destruct (Z.le_gt_cases (a + w) (usp - 208)) as [X|X]; [left; exact X|right].
    destruct (Z.le_gt_cases usp a) as [Y|Y]; [exact Y|exfalso].
    destruct (Z.le_gt_cases (e_sp0 E1 - vp_frame P1) a).
    - apply (AP a); lia.
    - apply (AP (e_sp0 E1 - vp_frame P1)); lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis ROM_IMG : forall a : word, vp_imgend P <= bv_unsigned a -> seg_rom SEGS a = None.
  Lemma rdn1_mem_img mem a k : 0 <= a < 2 ^ 64 -> vp_imgend P <= a -> rdn SEGS mem (wordZ a) 1 = Some [k] -> mem (wordZ a) = Some k.
  Proof.
    intros Ha Hi H. cbn [rdn] in H. destruct (mem (wordZ a)) as [b|] eqn:M.
    - injection H as ->. reflexivity.
    - rewrite ROM_IMG in H by (rewrite u_wordZ by lia; lia). discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma rcell_holds_ext sh nu nu' mem mem' a w v (b : positive) :
    ext b nu nu' -> (match v with Some e => lin_below e b = true | None => True end) ->
    0 <= a -> a + w <= 2 ^ 64 -> 0 < w ->
    (forall i, 0 <= i < w -> rdn SEGS mem' (wordZ (a + i)) 1 = rdn SEGS mem (wordZ (a + i)) 1) ->
    rdn SEGS mem' (wordZ a) (Z.to_nat w) = rdn SEGS mem (wordZ a) (Z.to_nat w) ->
    rcell_holds SEGS sh nu mem a w v -> rcell_holds SEGS sh nu' mem' a w v.
  Proof.
    intros X Bv Ha Haw Hw R1 RW RC. unfold rcell_holds in *. destruct v as [e|]; [|exact I].
    destruct (sh && lin_is_const e).
    - intros i Hi. destruct (RC i Hi) as (k & Hk & Hb). exists k. split; [|exact Hb]. rewrite R1 by exact Hi. exact Hk.
    - unfold cell_holds in *. destruct RC as (bs & R & V). exists bs. split; [rewrite RW; exact R|].
      rewrite (eval_ext_below b nu nu' e X Bv). exact V.
  Qed.

  (* [comment removed for export] *)
  Lemma own_flags_nu_ext A nu nu' : ext (vs_next (v1 A)) nu nu' -> state_below2 A -> own_flags A nu' = own_flags A nu.
  Proof.
    intros X (_ & BR & _). unfold own_flags.
    assert (G : forall l, (forall r, In r l -> match vr_kind r with RK_fake _ fl => (fl < vs_next (v1 A))%positive | _ => True end) ->
               flat_map (fun r => match vr_kind r with RK_fake _ fl => [nu' fl] | _ => [] end) l
               = flat_map (fun r => match vr_kind r with RK_fake _ fl => [nu fl] | _ => [] end) l).
    { induction l as [|r t IH]; intros Hl; [reflexivity|]. cbn [flat_map].
      rewrite IH by (intros x Hx; apply Hl; right; exact Hx). pose proof (Hl r (or_introl eq_refl)) as K.
      destruct (vr_kind r); try reflexivity. rewrite X by exact K. reflexivity. }
    apply G. intros r Hr. exact (proj2 (proj2 (BR r Hr))).
  Qed.

  (* [comment removed for export] *)
  #[using="Hcid"] Lemma block_desc fs sp0 frame y pq :
    fs mod 8 = 0 -> 0 <= pq < fs_nframes cid -> 64 <= fake_size cid -> frame_addr fs cid pq mod 8 = 0 -> fake_size cid / 8 * 8 = fake_size cid ->
    in_blocks fs 0 pq y ->
    dbyte fs sp0 frame SBz DHints y \/ dbyte fs sp0 frame SBz (DFlag cid pq) y
    \/ dbyte fs sp0 frame SBz (DSlot cid pq) y \/ dbyte fs sp0 frame SBz (DShSlot cid pq) y.
  Proof.
    intros M8 Hp SZ FM S8 IB. cbn [dbyte]. unfold in_blocks in IB. pose proof (div8_exact _ FM). (ltac2:(LK.k [@Hcid; @SZ; @IB; @H]); lia).
  Qed.

  (* [comment removed for export] *)
  Lemma in_class_regions fs c pq L :
    0 <= c -> 0 <= pq < fs_nframes c ->
    ~ In (c, pq) L ->
    In (wordZ (frame_addr fs c pq), fake_size c) (class_regions P fs c L)
    /\ In (wordZ (vp_shoff P + frame_addr fs c pq / 8), fake_size c / 8) (class_regions P fs c L).
  Proof.
    intros Hc Hp NL. unfold class_regions.
    assert (IN : In pq (map Z.of_nat (seq 0 (Z.to_nat (fs_nframes c))))).
    { apply in_map_iff. exists (Z.to_nat pq). split; [lia|]. apply in_seq. lia. }
    assert (NE : existsb (fun cp : Z * Z => (fst cp =? c) && (snd cp =? pq)) L = false).
    { destruct (existsb _ L) eqn:X; [|reflexivity]. exfalso. apply existsb_exists in X as ([c' p'] & Hin & EQ).
      cbn in EQ. apply andb_prop in EQ as [EQ1 EQ2]. apply Z.eqb_eq in EQ1. apply Z.eqb_eq in EQ2. subst. exact (NL Hin). }
    split; apply in_flat_map; exists pq; (split; [exact IN|]); rewrite NE; cbn; auto.
  Qed.

  Lemma in_classes_regions fs n c L e :
    (Z.to_nat c < n)%nat -> 0 <= c -> In e (class_regions P fs c L) -> In e (classes_regions P fs n L).
  Proof.
    intros Hn Hc Hin. induction n as [|n IH]; [lia|]. cbn [classes_regions]. apply in_app_iff.
    destruct (Nat.eq_dec (Z.to_nat c) n) as [EQ|NE]; [right; rewrite <- EQ, Z2Nat.id by lia; exact Hin|left; apply IH; lia].
  Qed.

  Lemma rw_any a : in_rw_zones P E a = true -> in_any_zone P E a = true.
  Proof.
    intros H. unfold in_rw_zones, rw_zones in H. unfold in_any_zone. apply existsb_exists in H as (z & Hz & Hin).
    apply filter_In in Hz as [Hz _]. apply existsb_exists. exists z. auto.
  Qed.

  Lemma covered_in l b m a : In (wordZ b, m) l -> 0 <= b -> b <= a -> a + 1 <= b + m -> b < 2 ^ 64 -> covered l a 1.
  Proof. intros Hin H0 H1 H2 H3. exists (wordZ b), m. rewrite u_wordZ by lia. auto. Qed.

  Lemma lin_below_lsymc s c n : (s < n)%positive -> lin_below (lsymc s c) n = true.
  Proof. intros. unfold lin_below, lsymc; simpl. rewrite (proj2 (Pos.ltb_lt s n)); auto. Qed.

  (* [comment removed for export] *)
  Lemma own_flags_length A nu : live_ok nu A -> (length (own_flags A nu) <= length (vs_live A))%nat.
  Proof.
    intros (LV1 & LV2 & LV3 & LV4).
    set (isf := fun r : vregion => match vr_kind r with RK_fake _ _ => true | _ => false end).
    assert (LEN : length (own_flags A nu) = length (map vr_base (List.filter isf (vs_rgn A)))).
    { unfold own_flags. rewrite length_map. generalize (vs_rgn A) as l. induction l as [|r t IH]; [reflexivity|].
      cbn [flat_map List.filter]. unfold isf at 1. destruct (vr_kind r); cbn [app length]; rewrite IH; reflexivity. }
    rewrite LEN. apply List.NoDup_incl_length.
    - apply nodup_map_filter. exact LV4.
    - intros s Hs. apply List.in_map_iff in Hs as (r & <- & Hr). apply List.filter_In in Hr as [Hr Hf].
      apply (proj2 (LV1 (vr_base r))). exists r. split; [exact Hr|]. split; [reflexivity|].
      unfold isf in Hf. destruct (vr_kind r); try discriminate. exact I.
  Qed.

  Lemma own_flags_cons3 X r1 r2 r3 l lv dd mm nu :
    own_flags (mkVS2 X (r1 :: r2 :: r3 :: l) lv dd mm) nu =
    ((match vr_kind r1 with RK_fake _ fl => [nu fl] | _ => [] end) ++
     (match vr_kind r2 with RK_fake _ fl => [nu fl] | _ => [] end) ++
     (match vr_kind r3 with RK_fake _ fl => [nu fl] | _ => [] end) ++ own_flags (mkVS2 X l lv dd mm) nu)%list.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="P1 E1 PO2 SHOFF Z_HINTS Z_FLAGS Z_FRAMES Z_FSHAD Hcid MCELLS MCELLS_OK TSD TSD_OK RUN CITP ROM_IMG"] Theorem stack_malloc_post : contract_post2 SEGS P E mem0 rom CI (C_stack_malloc cid) tgt.
  Proof.
    intros A spoff l nu regs mem ra HC HG2 MEMO Hsp HK Hret Hra.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & HD2 & HFS & HZN & HKC). pose proof HEV1 as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
    pose proof HM as (KC & ZOK & DSH & LFL & RT & KR).
    destruct (ca_stack_malloc_inv A spoff l HC) as (ea & etp & fsr & AM & Hetp & Eetp & Hea & CEA & SZA & Gfsr & Kfsr & LIV8 & BUDGET & RULE).
    Time (assert (FSnz : vp_fs P <> None) by (unfold asan_mode in AM; destruct (vp_fs P); [discriminate|discriminate AM])).
    pose proof (layout_of_env _ _ _ PO2 HE FSnz) as LAY.
    destruct (PO2_fs _ _ PO2 FSnz) as [SH FCLO]. rewrite SHOFF in SH.
    unfold rtctx_ok in RT.
    unfold env_fs in HFS. destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|exfalso; exact (FSnz eq_refl)].
    destruct HFS as (Hssl & FSlo & FShi & FSal & FSlen & LVAL & LND & APsf & APdf & APds & SPlo & DAThi & DSHrw & SP47 & FDEP).
    (* [comment removed for export] *)
    assert (FSlo' : 0 <= e_fs E /\ off_band (e_fs E) (FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL)) by (clear - FSlo FSlen; unfold off_band in *; lia).
    assert (FSIMG : vp_imgend P <= e_fs E) by (clear - FDEP; tauto).
    clear FSlo. rename FSlo' into FSlo.
    clear APdf APds DAThi DSHrw.
    Time (assert (FSnz' : vp_fs P <> None) by (rewrite Efs; discriminate)).
    (* [comment removed for export] *)
    unfold get_reg2 in Hetp, Hea. subst etp.
    Time (assert (R4 : bv_unsigned (getr regs 4%bv) = zwrap 64 (ci_tp CI))).
    { rewrite (proj1 (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 4%bv (lconst (ci_tp CI)) HG1 ltac:(vm_compute; lia) Hetp)).
      rewrite eval_lconst. reflexivity. }
    Time (assert (R2 : getr regs 2%bv = wordZ (e_sp0 E1 + spoff))).
    { apply (reg_word SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 2%bv (lsymc SP0 spoff) (e_sp0 E1 + spoff) HG1);
        [vm_compute; lia|exact Hsp| |].
      - rewrite eval_lsymc. rewrite (proj1 (proj2 (proj2 HG1)) SP0 (e_sp0 E1)) by reflexivity. reflexivity.
      - destruct HK as [HK'|HK']; [cbn in HK'; discriminate|]. apply in_ranges_sound in HK' as (wlo & whi & Hw & W1 & W2).
        destruct (PR _ Hw). cbn [fst snd contract2_K] in *. unfold K_stack_malloc, P1, E1 in *. lia. }
    Time (assert (HKR : - vp_frame P1 <= spoff - 208 /\ spoff <= 0 /\ exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - 208 /\ spoff <= snd wr)).
    { destruct HK as [HK'|HK']; [cbn in HK'; discriminate|]. apply in_ranges_sound in HK' as (wlo & whi & Hw & W1 & W2).
      destruct (PR _ Hw). cbn [fst snd contract2_K] in *. unfold K_stack_malloc, P1, E1 in *. split; [lia|]. split; [lia|].
      exists (wlo, whi). cbn. split; [exact Hw|lia]. }
    destruct HKR as (K1 & K2 & KW).
    set (usp := e_sp0 E1 + spoff) in *.
    assert (USP : 0 <= e_sp0 E1 - vp_frame P1 /\ e_sp0 E1 - vp_frame P1 <= usp - 208 /\ usp <= e_sp0 E1 /\ e_sp0 E1 + 16 <= 2 ^ 47)
      by (unfold usp, HIGH_MEM_BEG, HIGH_MEM_END, P1, E1 in *; lia).
    pose proof (proj1 (proj2 HG1)) as (MF & MD & MP & MFM).
    Time (assert (JOK : forall a, usp - K208 <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true)).
    { intros a Ha. unfold K208 in Ha. apply (proj1 (MF a ltac:(unfold usp, P1, E1 in *; lia))). }
    (* [comment removed for export] *)
    try rewrite Efs in RT.
    destruct RT as (tsd & ctx & thr & db & beg & C1 & C2 & C3 & C4 & C5 & NZ1 & C6 & NZ2 & C7 & C8 & NZ3 & NZ4 & C9 & NZ5).
    assert (CELL : forall a w v, rt_cell SEGS P E mem a w v ->
              rdn SEGS mem (wordZ a) (Z.to_nat w) = Some (word_to_le_bytes (Z.to_nat w) (wordZ v))
              /\ 0 <= a /\ a + w <= 2 ^ 64 /\ (forall x, a <= x < a + w -> ~ (e_sp0 E1 - vp_frame P1 <= x < e_sp0 E1))).
    { intros a w v (Q0 & Q1 & Q2 & AP & Q3). split; [exact Q3|]. split; [exact Q0|]. split; [exact Q2|].
      intros x Hx. exact (proj1 (proj2 (AP x Hx))). }
    destruct (CELL _ _ _ C1) as (D1 & _). destruct (CELL _ _ _ C2) as (D2 & _). destruct (CELL _ _ _ C3) as (D3 & _).
    destruct (CELL _ _ _ C4) as (D4 & _). destruct (CELL _ _ _ C5) as (D5 & T5a & T5b & _).
    destruct (CELL _ _ _ C6) as (D6 & T6a & T6b & AP6). destruct (CELL _ _ _ C8) as (D8 & _). destruct (CELL _ _ _ C9) as (D9 & T9a & T9b & AP9).
    destruct C7 as (T7a & T7b & AP7' & RD7).
    Time (assert (AP7 : forall x, thr + 48 <= x < thr + 48 + 16 -> ~ (e_sp0 E1 - vp_frame P1 <= x < e_sp0 E1)) by (intros x Hx; exact (proj1 (proj2 (AP7' x Hx))))).
    change (Z.to_nat 8) with 8%nat in *. change (Z.to_nat 1) with 1%nat in *.
    Time (assert (TSDE : tsd = TSD)).
    { pose proof (TSD_OK A nu regs mem _ HG2 D4) as X. rewrite bytes_le_to_Z_8, u_wordZ in X; [exact X|].
      destruct (CELL _ _ _ C5) as (_ & Y1 & Y2 & _). lia. }
    (* [comment removed for export] *)
    Time (destruct (word_readable SEGS P E mem0 A nu regs mem (thr + 48) HG2 ltac:(intros i Hi; apply RD7; lia) ltac:(lia) ltac:(lia)) as [a2v A2V]).
    destruct (word_readable SEGS P E mem0 A nu regs mem (thr + 56) HG2
                ltac:(intros i Hi; replace (thr + 56 + i) with (thr + 48 + (8 + i)) by lia; apply RD7; lia) ltac:(lia) ltac:(lia)) as [a3v A3V].
    (* [comment removed for export] *)
    destruct (rgn_get_in _ _ _ Gfsr) as [Hfsr Bfsr].
    pose proof (RGN fsr Hfsr) as FOK. pose proof FOK as (FB1 & FB2 & FB3 & FDS & FCELLS & FPERM & FNUL & FKIND).
    unfold kind_ok in FKIND. rewrite Kfsr in FKIND. destruct FKIND as (_ & _ & Fdisp & Flo & Fhi).
    Time (assert (Frb : rbase nu fsr = (e_fs E)) by (unfold rbase; rewrite Fdisp, Bfsr, (nu_FSB _ _ _ _ A nu regs mem HG2); lia)).
    Time (assert (NDF : is_data_shadow fsr = false) by (unfold is_data_shadow; rewrite Kfsr; reflexivity)).
    destruct (FPERM NDF) as [FRD FWR].
    destruct (word_readable SEGS P E mem0 A nu regs mem ((e_fs E) + 8 * cid) HG2
                ltac:(intros i Hi; destruct (FRD (8 * cid + i) ltac:((ltac2:(LK.k [@Hcid; @P0; @E4; @E5; @E11; @E12; @NZ4; @FSlo; @T9b; @Bfsr; @Flo; @Fhi; @Hi; @SPlo; @FB2; @Frb]); lia))) as [_ X]; rewrite Frb in X; replace ((e_fs E) + 8 * cid + i) with ((e_fs E) + (8 * cid + i)) by (ltac2:(LK.k [@Hcid; @P0; @E4; @E5; @E11; @E12; @NZ4; @FSlo; @T9b; @Bfsr; @Flo; @Fhi; @Hi; @SPlo; @FB2; @Frb]); lia); exact X)
                ltac:(unfold HIGH_MEM_BEG in *; (ltac2:(LK.k [@Hcid; @P0; @E4; @E5; @E11; @E12; @NZ4; @FSlo; @T9b; @Bfsr; @Flo; @Fhi; @Hi; @SPlo; @FB2; @Frb]); lia)) ltac:(unfold HIGH_MEM_END in *; (ltac2:(LK.k [@Hcid; @P0; @E4; @E5; @E11; @E12; @NZ4; @FSlo; @T9b; @Bfsr; @Flo; @Fhi; @Hi; @SPlo; @FB2; @Frb]); lia))) as [hint HINT].
    (* [comment removed for export] *)
    set (FL := fun p : Z => match rdn SEGS mem (wordZ (flag_addr (e_fs E) cid p)) 1 with Some [b] => b | _ => Z_to_bv 8 0 end).
    Time (assert (FLAGS : forall p, 0 <= p < fs_nframes cid -> rdn SEGS mem (wordZ (flag_addr (e_fs E) cid p)) 1 = Some [FL p])).
    { intros p Hp. pose proof (flag_facts (e_fs E) p Hp).
      destruct (zone_covers_sound A nu regs mem FSB 0 FS_FLAGS FS_FRAMES (flag_addr (e_fs E) cid p) HG2 Z_FLAGS ltac:(rewrite nuE_FSB; lia)) as (_ & [k Hk] & _).
      unfold FL. rewrite Hk. reflexivity. }
    clearbody FL.
    (* [comment removed for export] *)
    Time (assert (FSAP : (e_fs E) + FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL <= usp - K208 \/ usp <= (e_fs E))).
    { unfold K208, usp. subst ssl. unfold FS_SSL, P1, E1 in *. destruct APsf as [X|X]; [left|right]; lia. }
    clear APsf.
    pose proof (fs_nframes_pos cid ltac:(lia)) as NPOS. pose proof (fs_nframes_le cid ltac:(lia)) as NLE.
    (* [comment removed for export] *)
    Time (assert (FREE : exists p0, 0 <= p0 < fs_nframes cid /\ bv_unsigned (FL p0) = 0)).
    { destruct (List.find (fun p => Z.eqb (bv_unsigned (FL p)) 0) (map Z.of_nat (seq 0 (Z.to_nat (fs_nframes cid))))) as [p0|] eqn:FD.
      - apply List.find_some in FD as [I0 E0]. apply Z.eqb_eq in E0. destruct (seqZ_facts (Z.to_nat (fs_nframes cid))) as (_ & IN & _).
        apply IN in I0. exists p0. split; [lia|exact E0].
      - exfalso.
        assert (TAKEN : forall p, 0 <= p < fs_nframes cid ->
                  List.In (flag_addr (e_fs E) cid p) (map (fun cp : Z * Z => flag_addr (e_fs E) (fst cp) (snd cp)) (e_live E) ++ own_flags A nu)).
        { intros p Hp. destruct (seqZ_facts (Z.to_nat (fs_nframes cid))) as (_ & IN & _).
          pose proof (List.find_none _ _ FD p ltac:(apply IN; lia)) as NZ. cbn beta in NZ. apply Z.eqb_neq in NZ.
          apply List.in_app_iff.
          destruct (List.in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (cid, p) (e_live E)) as [IL|NL].
          { left. apply List.in_map_iff. exists (cid, p). split; [reflexivity|exact IL]. }
          destruct (List.in_dec Z.eq_dec (flag_addr (e_fs E) cid p) (own_flags A nu)) as [IO|NO]; [right; exact IO|].
          exfalso. destruct (FI2 FSnz' cid p Hcid Hp NL NO) as (b & Hb & Hb0).
          apply NZ. pose proof (FLAGS p Hp) as X. cbn [rdn] in X. rewrite Hb in X. injection X as <-. exact Hb0. }
        pose proof (positions_le_length (flag_addr (e_fs E) cid) _ (Z.to_nat (fs_nframes cid))
                      ltac:(intros p q Hp Hq EQ; exact (proj2 (flag_addr_inj (e_fs E) cid p cid q Hcid ltac:((ltac2:(LK.k [@E4; @E5; @E11; @NZ4; @FSlo; @T9b; @Bfsr; @NPOS; @Hp; @Hq]); lia)) Hcid ltac:((ltac2:(LK.k [@E4; @E5; @E11; @NZ4; @FSlo; @T9b; @Bfsr; @NPOS; @Hp; @Hq]); lia)) EQ)))
                      ltac:(intros p Hp; apply TAKEN; (ltac2:(LK.k [@E4; @E5; @E11; @NZ4; @FSlo; @T9b; @Bfsr; @NPOS; @Hp; @Hq]); lia))) as LEN.
        rewrite length_app, length_map in LEN. pose proof (own_flags_length A nu LIVE). lia. }
    Time (destruct FREE as (p0 & Hp0 & Zp0)).
    (* [comment removed for export] *)
    Time (assert (WHINT : forall j, 0 <= j < 8 -> store_ok SEGS mem (wordZ ((e_fs E) + 8 * cid + j)) 1 = true)).
    { intros j Hj.
      exact (proj2 (proj2 (zone_covers_sound A nu regs mem FSB 0 0 88 ((e_fs E) + 8 * cid + j) HG2 Z_HINTS ltac:(rewrite nuE_FSB; (ltac2:(LK.k [@Hcid; @P0; @E4; @E5; @E11; @E12; @NZ4; @FSlo; @T9b; @Bfsr; @Hj]); lia))))). }
    Time (assert (WFLAG : forall p, 0 <= p < fs_nframes cid -> store_ok SEGS mem (wordZ (flag_addr (e_fs E) cid p)) 1 = true)).
    { intros p Hp. pose proof (flag_facts (e_fs E) p Hp).
      exact (proj2 (proj2 (zone_covers_sound A nu regs mem FSB 0 FS_FLAGS FS_FRAMES (flag_addr (e_fs E) cid p) HG2 Z_FLAGS ltac:(rewrite nuE_FSB; lia)))). }
    Time (assert (WFRAME : forall p j, 0 <= p < fs_nframes cid -> 0 <= j < fake_size cid -> store_ok SEGS mem (wordZ (frame_addr (e_fs E) cid p + j)) 1 = true)).
    { intros p j Hp Hj. destruct (frame_facts (e_fs E) p FSal Hp) as (Q1 & Q2 & _).
      assert (0 <= cid * 2 ^ FS_SSL /\ (cid + 1) * 2 ^ FS_SSL <= FS_NCLASSES * 2 ^ FS_SSL) by (unfold FS_SSL, FS_NCLASSES; change (2 ^ 20) with 1048576; (ltac2:(LK.k [@Hcid; @E4; @E5; @E11; @NZ4; @FSlo; @T9b; @Bfsr]); lia)).
      exact (proj2 (proj2 (zone_covers_sound A nu regs mem FSB 0 FS_FRAMES (FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) (frame_addr (e_fs E) cid p + j) HG2 Z_FRAMES
                ltac:(rewrite nuE_FSB; (ltac2:(LK.k [@E4; @E5; @E11; @NZ4; @FSlo; @T9b; @Bfsr; @Hj; @Q1; @Q2; @H]); lia))))). }
    pose proof fake_size_div8 as [SZ8 SZ8b].
    Time (assert (WSHAD : forall p j, 0 <= p < fs_nframes cid -> 0 <= j < fake_size cid / 8 -> store_ok SEGS mem (wordZ (SBz + frame_addr (e_fs E) cid p / 8 + j)) 1 = true)).
    { intros p j Hp Hj. destruct (frame_facts (e_fs E) p FSal Hp) as (Q1 & Q2 & _ & Q4).
      assert (0 <= cid * 2 ^ FS_SSL /\ (cid + 1) * 2 ^ FS_SSL <= FS_NCLASSES * 2 ^ FS_SSL) by (unfold FS_SSL, FS_NCLASSES; change (2 ^ 20) with 1048576; (ltac2:(LK.k [@Hcid; @E4; @E5; @E11; @NZ4; @FSlo; @T9b; @Bfsr; @SZ8; @SZ8b]); lia)).
      pose proof (div8_exact _ Q4). apply Z.mod_divide in FSal; [|lia]. destruct FSal as [q Hq].
      assert (DIV8 : (e_fs E) / 8 = q * 512) by (rewrite Hq; replace (q * 4096) with (q * 512 * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
      assert (RG : SBz + nuE E FS8 + FS_FRAMES / 8 <= SBz + frame_addr (e_fs E) cid p / 8 + j < SBz + nuE E FS8 + (FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) / 8).
      { rewrite nuE_FS8, DIV8. change (FS_FRAMES / 8) with 4608. change ((FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) / 8) with 659968.
        unfold FS_FRAMES, FS_NCLASSES, FS_SSL in *. (ltac2:(LK.k [@Hq; @E4; @E5; @E11; @NZ4; @FSlo; @K1; @USP; @T9b; @Bfsr; @SZ8; @SZ8b; @Hj; @Q1; @Q2; @H; @H0]); lia). }
      exact (proj2 (proj2 (zone_covers_sound A nu regs mem FS8 SBz (FS_FRAMES / 8) ((FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) / 8) _ HG2 Z_FSHAD RG))). }
    (* [comment removed for export] *)
    pose proof (apart_window _ _ usp AP6 ltac:(lia) ltac:(unfold K208; lia) ltac:(lia)) as AQ6'.
    pose proof (apart_window _ _ usp AP7 ltac:(lia) ltac:(unfold K208; lia) ltac:(lia)) as AQ7'.
    pose proof (apart_window _ _ usp AP9 ltac:(lia) ltac:(unfold K208; lia) ltac:(lia)) as AQ9'.
    assert (AQ6 : ctx + 160 <= usp - K208 \/ usp <= ctx + 152) by lia.
    assert (AQ7 : thr + 64 <= usp - K208 \/ usp <= thr + 48) by lia.
    assert (AQ9 : db + 32 <= usp - K208 \/ usp <= db + 24) by lia. clear AQ6' AQ7' AQ9'.
    assert (R4w : getr regs 4%bv = wordZ (vp_tp P)).
    { apply wordZ_eq_u. rewrite R4, CITP. apply zwrap_id. destruct (CELL _ _ _ C1) as (_ & Y1 & Y2 & _). lia. }
    assert (U1 : HIGH_MEM_BEG + K208 <= usp) by (unfold K208, P1, E1 in *; (ltac2:(LK.k [@SPlo; @E4; @E5; @E11; @NZ1; @NZ2; @NZ3; @NZ4; @FSlo; @K1; @K2; @USP; @T9b; @Bfsr; @SZ8; @SZ8b]); lia)).
    assert (U2 : usp + 16 <= 2 ^ 64) by (unfold P1, E1 in *; (ltac2:(LK.k [@E4; @E5; @E11; @NZ4; @FSlo; @K2; @USP; @T9b; @Bfsr]); lia)).
    assert (FS47 : e_fs E + FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL <= 2 ^ 47) by (subst ssl; unfold HIGH_MEM_END, FS_SSL in *; (ltac2:(LK.k [@FShi; @FSlen; @E4; @E5; @E11; @NZ4; @FSlo; @T9b; @Bfsr; @SZ8; @SZ8b]); lia)).
    destruct (RUN mem usp (vp_tp P) (e_fs E) tsd ctx thr db beg a2v a3v hint FL p0 regs ra
                (MCELLS_OK _ _ _ _ HG2) eq_refl D1 D4 TSDE D5 NZ1 ltac:(lia) D6 NZ2 ltac:(lia) A2V A3V D8 NZ3 ltac:(lia) NZ4 D9 NZ5
                AQ6 AQ7 AQ9 D3 ltac:(exact D2) FSIMG (proj2 FSlo) FS47 FSal FSAP U1 U2 JOK HINT FLAGS Hp0 Zp0 WHINT WFLAG WFRAME WSHAD Hret Hra R2 R4w)
      as (i & p & regs' & m' & mZ & Hi & Hp & ZP & MS & Q10 & Q2 & Q1 & QK & EFF & JM & JG0).
    (* [comment removed for export] *)
    assert (PRG : 0 <= p < fs_nframes cid) by (rewrite Hp; apply Z.mod_pos_bound; lia).
    set (ffa := frame_addr (e_fs E) cid p) in *. set (fla := flag_addr (e_fs E) cid p) in *.
    destruct (frame_facts (e_fs E) p FSal PRG) as (FF1 & FF2 & FFM & FF8). fold ffa in FF1, FF2, FFM, FF8.
    pose proof (flag_facts (e_fs E) p PRG) as FL1. fold fla in FL1.
    assert (FLA : rdn SEGS mem (wordZ fla) 1 = Some [FL p]) by exact (FLAGS p PRG).
    pose proof (fake_size_bounds cid Hcid) as SZB.
    assert (CL5 : 0 <= cid * 2 ^ FS_SSL /\ (cid + 1) * 2 ^ FS_SSL <= FS_NCLASSES * 2 ^ FS_SSL) by (clear -Hcid; unfold FS_SSL, FS_NCLASSES; change (2 ^ 20) with 1048576; lia).
    assert (FFR : 0 <= ffa /\ ffa + fake_size cid <= 2 ^ 47 /\ off_band ffa (fake_size cid))
      by (clear -FF1 FF2 CL5 FSlo FS47; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, FS_FRAMES, FS_NCLASSES, FS_SSL in *; lia).
    pose proof (div8_exact _ FF8) as FFD.
    (* [comment removed for export] *)
    assert (NLIVE : ~ In (cid, p) (e_live E)).
    { intros IN. destruct (LFL (cid, p) IN) as (b & Hb & Hb1). cbn [fst snd] in Hb. rewrite (FLAGS p PRG) in Hb.
      injection Hb as Eb. rewrite <- Eb, ZP in Hb1. discriminate Hb1. }
    assert (NOWN : ~ In fla (own_flags A nu)).
    { intros IN. unfold own_flags in IN. apply in_flat_map in IN as (r & Hr & Hin).
      pose proof (RGN r Hr) as (_ & _ & _ & _ & _ & _ & _ & KIND). unfold kind_ok in KIND.
      destruct (vr_kind r) as [c fl| | | |]; try (destruct Hin; fail). destruct Hin as [EQ|[]].
      destruct KIND as (_ & _ & _ & _ & _ & pos & _ & _ & _ & (b & Hb & Hb1) & _). rewrite EQ in Hb. unfold fla in Hb.
      rewrite (FLAGS p PRG) in Hb. injection Hb as Eb. rewrite <- Eb, ZP in Hb1. discriminate Hb1. }
    (* [comment removed for export] *)
    set (A1 := v1 A) in *. set (FF := vs_next A1) in *. set (FLs := Pos.succ FF) in *. set (F8 := Pos.succ FLs) in *.
    set (nu' := vupd (vupd (vupd nu FF ffa) FLs fla) F8 (ffa / 8)).
    assert (NFF : nu' FF = ffa).
    { unfold nu'. rewrite (vupd_other _ _ _ _ (pos_ne_s2 FF)), (vupd_other _ _ _ _ (pos_ne_s1 FF)). apply vupd_same. }
    assert (NFL : nu' FLs = fla).
    { unfold nu'. rewrite (vupd_other _ _ _ _ (pos_s1_ne_s2 FF)). apply vupd_same. }
    assert (NF8 : nu' F8 = ffa / 8) by (unfold nu'; apply vupd_same).
    assert (EXT : ext FF nu nu').
    { intros s Hs. unfold nu'.
      rewrite (vupd_other _ _ _ _ (pos_lt_ne2 s FF Hs)), (vupd_other _ _ _ _ (pos_lt_ne1 s FF Hs)), (vupd_other _ _ _ _ (pos_lt_ne0 s FF Hs)). reflexivity. }
    destruct BEL2 as (BF & BR & BL & BD & BM). fold A1 FF in BF, BR, BL, BD, BM.
    assert (NFSB : nu' FSB = e_fs E) by (rewrite EXT by (unfold LAST_FIXED2, FSB in *; lia); exact (nu_FSB _ _ _ _ A nu regs mem HG2)).
    (* [comment removed for export] *)
    cbv zeta in RULE. fold A1 in RULE. fold FF in RULE. fold FLs in RULE. fold F8 in RULE.
    set (A2 := set_next A1 (Pos.succ F8)) in RULE.
    set (lo_off := FS_FRAMES_OFF + Z.shiftl cid FS_LOG) in RULE.
    set (hi_off := FS_FRAMES_OFF + Z.shiftl (cid + 1) FS_LOG - fake_size cid) in RULE.
    set (e1 := lsub (laddc (lsym FSB) lo_off) (lsym FF)) in RULE. set (e2 := laddc (lsub (lsym FF) (lsym FSB)) (- hi_off)) in RULE.
    destruct (aassume2 A2 e1 e2) as [ok1 A3] eqn:Q3.
    set (e3 := lsub (laddc (lsym FSB) 4096) (lsym FLs)) in RULE. set (e4 := laddc (lsub (lsym FLs) (lsym FSB)) (- (4096 + 32768 - 1))) in RULE.
    destruct (ameet_cong A3 FF (fake_size cid) 0) as [ok2 A4] eqn:Q4.
    destruct (aassume2 A4 e3 e4) as [ok3 A5] eqn:Q5.
    set (e5 := lsub (lscale 8 (lsym F8)) (lsym FF)) in RULE. set (e6 := lsub (lsym FF) (lscale 8 (lsym F8))) in RULE.
    destruct (aassume2 A5 e5 e6) as [ok4 A6] eqn:Q6.
    destruct RULE as (OK1 & OK2 & OK3 & OK4 & El). subst ok1 ok2 ok3 ok4.
    (* [comment removed for export] *)
    assert (L2 : lgamma A2 nu').
    { pose proof (proj2 (lgamma_fresh A1 nu ffa itv_top HL (in_itv_top ffa))) as L1. cbv zeta in L1. fold FF in L1.
      pose proof (proj2 (lgamma_fresh (set_next A1 (Pos.succ FF)) (vupd nu FF ffa) fla itv_top L1 (in_itv_top fla))) as L1'.
      cbv zeta in L1'. change (vs_next (set_next A1 (Pos.succ FF))) with FLs in L1'.
      change (set_next (set_next A1 (Pos.succ FF)) (Pos.succ FLs)) with (set_next A1 F8) in L1'.
      pose proof (proj2 (lgamma_fresh (set_next A1 F8) (vupd (vupd nu FF ffa) FLs fla) (ffa / 8) itv_top L1' (in_itv_top _))) as L1''.
      cbv zeta in L1''. change (vs_next (set_next A1 F8)) with F8 in L1''.
      change (set_next (set_next A1 F8) (Pos.succ F8)) with A2 in L1''. exact L1''. }
    assert (NX2 : vs_next A2 = Pos.succ F8) by reflexivity.
    (* [comment removed for export] *)
    assert (LOFF : lo_off = FS_FRAMES + cid * 2 ^ FS_SSL).
    { unfold lo_off, FS_FRAMES_OFF, FS_LOG, FS_FRAMES, FS_SSL. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
    assert (HOFF : hi_off = FS_FRAMES + (cid + 1) * 2 ^ FS_SSL - fake_size cid).
    { unfold hi_off, FS_FRAMES_OFF, FS_LOG, FS_FRAMES, FS_SSL. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
    assert (BFF : (FSB < FF)%positive) by (unfold FSB, LAST_FIXED2 in *; lia).
    pose proof (aassume2_sound A2 nu' e1 e2 L2
                  ltac:(unfold e1; rewrite eval_lsub, eval_laddc, !eval_lsym, NFSB, NFF; clear -FF1 LOFF; lia)
                  ltac:(unfold e2; rewrite eval_laddc, eval_lsub, !eval_lsym, NFSB, NFF; clear -FF2 HOFF; lia)
                  ltac:(unfold e1; rewrite NX2; apply lin_below_lsub; [apply lin_below_laddc|]; apply lin_below_lsym; unfold F8, FLs; lia)
                  ltac:(unfold e2; rewrite NX2; apply lin_below_laddc, lin_below_lsub; apply lin_below_lsym; unfold F8, FLs; lia)) as (_ & L3 & X3).
    rewrite Q3 in L3, X3. cbn [snd] in L3, X3.
    assert (NX3 : vs_next A3 = Pos.succ F8) by (rewrite <- NX2; pose proof (aassume2_next A2 e1 e2) as X; rewrite Q3 in X; exact X).
    pose proof (ameet_cong_sound A3 nu' FF (fake_size cid) 0 L3
                  ltac:(rewrite NFF, Z.sub_0_r; apply Z.mod_divide; [lia|exact FFM])
                  ltac:(rewrite NX3; unfold F8, FLs; lia)) as (_ & L4 & X4).
    rewrite Q4 in L4, X4. cbn [snd] in L4, X4.
    assert (NX4 : vs_next A4 = Pos.succ F8) by (rewrite <- NX3; pose proof (ameet_cong_next A3 FF (fake_size cid) 0) as X; rewrite Q4 in X; exact X).
    pose proof (aassume2_sound A4 nu' e3 e4 L4
                  ltac:(unfold e3; rewrite eval_lsub, eval_laddc, !eval_lsym, NFSB, NFL; clear -FL1; unfold FS_FLAGS in *; (ltac2:(LK.k [@FL1; @E4; @E5; @E11; @NZ4; @T9b; @Bfsr; @NX2; @BFF; @NX3; @NX4]); lia))
                  ltac:(unfold e4; rewrite eval_laddc, eval_lsub, !eval_lsym, NFSB, NFL; clear -FL1; unfold FS_FRAMES in *; (ltac2:(LK.k [@FL1; @E4; @E5; @E11; @NZ4; @T9b; @Bfsr; @NX2; @BFF; @NX3; @NX4]); lia))
                  ltac:(unfold e3; rewrite NX4; apply lin_below_lsub; [apply lin_below_laddc|]; apply lin_below_lsym; unfold F8, FLs; (ltac2:(LK.k [@FL1; @E4; @E5; @E11; @NZ4; @T9b; @Bfsr; @NX2; @BFF; @NX3; @NX4]); lia))
                  ltac:(unfold e4; rewrite NX4; apply lin_below_laddc, lin_below_lsub; apply lin_below_lsym; unfold F8, FLs; (ltac2:(LK.k [@FL1; @E4; @E5; @E11; @NZ4; @T9b; @Bfsr; @NX2; @BFF; @NX3; @NX4]); lia))) as (_ & L5 & X5).
    rewrite Q5 in L5, X5. cbn [snd] in L5, X5.
    assert (NX5 : vs_next A5 = Pos.succ F8) by (rewrite <- NX4; pose proof (aassume2_next A4 e3 e4) as X; rewrite Q5 in X; exact X).
    pose proof (aassume2_sound A5 nu' e5 e6 L5
                  ltac:(unfold e5; rewrite eval_lsub, eval_lscale, !eval_lsym, NFF, NF8; clear -FFD; (ltac2:(LK.k [@FFD; @E11; @Bfsr; @NX2; @NX3; @NX4; @NX5]); lia))
                  ltac:(unfold e6; rewrite eval_lsub, eval_lscale, !eval_lsym, NFF, NF8; clear -FFD; (ltac2:(LK.k [@FFD; @E11; @Bfsr; @NX2; @NX3; @NX4; @NX5]); lia))
                  ltac:(unfold e5; rewrite NX5; apply lin_below_lsub; [apply lin_below_lscale|]; apply lin_below_lsym; unfold F8, FLs; (ltac2:(LK.k [@FFD; @E11; @Bfsr; @NX2; @NX3; @NX4; @NX5]); lia))
                  ltac:(unfold e6; rewrite NX5; apply lin_below_lsub; [|apply lin_below_lscale]; apply lin_below_lsym; unfold F8, FLs; (ltac2:(LK.k [@FFD; @E11; @Bfsr; @NX2; @NX3; @NX4; @NX5]); lia))) as (_ & L6 & X6).
    rewrite Q6 in L6, X6. cbn [snd] in L6, X6.
    assert (NX6 : vs_next A6 = Pos.succ F8) by (rewrite <- NX5; pose proof (aassume2_next A5 e5 e6) as X; rewrite Q6 in X; exact X).
    (* [comment removed for export] *)
    assert (SH6 : same_shape A1 A6).
    { destruct X3 as (_ & _ & S3). destruct X4 as (_ & _ & S4). destruct X5 as (_ & _ & S5). destruct X6 as (_ & _ & S6).
      eapply same_shape_trans; [|exact S6]. eapply same_shape_trans; [|exact S5]. eapply same_shape_trans; [|exact S4].
      eapply same_shape_trans; [|exact S3]. apply same_shape_set_next. }
    (* [comment removed for export] *)
    destruct EFF as (E0 & Eflag & E24 & Esz & Esh & EG & ES).
    assert (BLK : forall y, 0 <= y < 2 ^ 64 -> in_blocks (e_fs E) usp p y -> in_rw_zones P E y = true).
    { intros y Hy IB. unfold in_blocks in IB. fold ffa fla in IB. destruct IB as [B|[B|[B|[B|B]]]].
      - exact (proj1 (zone_covers_sound A nu regs mem FSB 0 0 88 y HG2 Z_HINTS ltac:(rewrite nuE_FSB; clear -B Hcid; lia))).
      - subst y. exact (proj1 (zone_covers_sound A nu regs mem FSB 0 FS_FLAGS FS_FRAMES fla HG2 Z_FLAGS ltac:(rewrite nuE_FSB; clear -FL1; lia))).
      - exact (proj1 (zone_covers_sound A nu regs mem FSB 0 FS_FRAMES (FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) y HG2 Z_FRAMES
                 ltac:(rewrite nuE_FSB; clear -B FF1 FF2 CL5 SZB; lia))).
      - exact (proj1 (zone_covers_sound A nu regs mem FSB 0 FS_FRAMES (FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) y HG2 Z_FRAMES
                 ltac:(rewrite nuE_FSB; clear -B FF1 FF2 CL5 SZB; lia))).
      - apply Z.mod_divide in FSal; [|lia]. destruct FSal as [q Hq].
        assert (DIV8 : e_fs E / 8 = q * 512) by (rewrite Hq; replace (q * 4096) with (q * 512 * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
        assert (RG : SBz + nuE E FS8 + FS_FRAMES / 8 <= y < SBz + nuE E FS8 + (FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) / 8).
        { rewrite nuE_FS8, DIV8. change (FS_FRAMES / 8) with 4608. change ((FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) / 8) with 659968.
          clear -B FF1 FF2 CL5 SZB FFD SZ8 Hq. unfold FS_FRAMES, FS_NCLASSES, FS_SSL in *. lia. }
        exact (proj1 (zone_covers_sound A nu regs mem FS8 SBz (FS_FRAMES / 8) ((FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) / 8) y HG2 Z_FSHAD RG)). }
    assert (RWC : rw_change SEGS P E mem mZ).
    { split; [|split; [exact EG|exact ES]]. intros y Hy NZ. apply E0; [exact Hy|]. intros IB. rewrite (BLK y Hy IB) in NZ. discriminate. }
    (* [comment removed for export] *)
    assert (GLB : forall g w v, In (g, (w, v)) (vs_globs A1) -> exists f, In f (vp_fcells P1) /\ fst f <= g /\ g + w <= fst f + snd f)
      by (intros g w v Hin; exact (GL2 AM g w v Hin)).
    pose proof (v1_rw_change SEGS P E mem0 PO2 A1 nu regs mem mZ HE GLB HG1 RWC) as G1z.
    destruct SH6 as (SR6 & SS6 & SG6 & SN6 & _).
    assert (LE6 : (vs_next A1 <= vs_next A6)%positive) by (rewrite NX6; unfold F8, FLs, FF; apply pos_le_s3).
    destruct (gamma_call_post SEGS P1 E1 (zpatch P E mem0 mZ) rom PO A1 A6 nu nu' regs regs mZ mZ [] G1z EXT LE6 L6) as [GZ1 _].
    { (* [comment removed for export] *) intros r e Hr Hg. rewrite SR6 in Hg. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 G1z)))))))) as HRg.
      rewrite (eval_ext_below FF nu nu' e EXT); [exact (HRg r e Hr Hg)|].
      destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 G1z))))))))))) as (_ & _ & RB & _). exact (RB _ _ Hg). }
    { intros off w v Hin. left. rewrite SS6 in Hin. split; [exact Hin|]. intros x _. exact I. }
    { intros g w v Hin. rewrite SG6 in Hin. split; [exact Hin|]. intros x _. exact I. }
    { intros lo' hi' Hin. left. rewrite SN6 in Hin. split; [exact Hin|]. intros x _. exact I. }
    { apply frame_mod_refl. }
    { intros x Hx. exfalso. apply Hx. exact I. }
    (* [comment removed for export] *)
    assert (SHR : SBz + ffa / 8 + fake_size cid / 8 <= HIGH_MEM_BEG).
    { clear -FFR FFD SZ8; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *. unfold HIGH_MEM_BEG, SBz in *. lia. }
    assert (HNT : e_fs E + 8 * cid + 8 <= e_fs E + FS_FLAGS) by (clear -Hcid; unfold FS_FLAGS; lia).
    (* [comment removed for export] *)
    assert (LFK : forall cp, In cp (e_live E) ->
              mZ (wordZ (flag_addr (e_fs E) (fst cp) (snd cp))) = mem (wordZ (flag_addr (e_fs E) (fst cp) (snd cp)))).
    { intros cp Hcp. rewrite Forall_forall in LVAL. destruct (LVAL cp Hcp) as [V1 V2].
      pose proof (flag_addr_range (e_fs E) (fst cp) (snd cp) V1 V2) as FR.
      apply E0; [clear -FR FSlo FS47; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; lia|].
      intros IB. unfold in_blocks in IB. fold ffa fla in IB. destruct IB as [B|[B|[B|[B|B]]]].
      - clear -B FR HNT. unfold FS_FLAGS in *. lia.
      - destruct (flag_addr_inj (e_fs E) (fst cp) (snd cp) cid p V1 V2 Hcid PRG B) as [Ec Ep].
        apply NLIVE. rewrite <- Ec, <- Ep, <- surjective_pairing. exact Hcp.
      - clear -B FR FF1 CL5. unfold FS_FRAMES in *. lia.
      - clear -B FR FF1 CL5 SZB. unfold FS_FRAMES in *. lia.
      - clear -B FR SHR FSlo FFR FFD; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *. unfold FS_FLAGS in *. lia. }
    pose proof (MC2_rw_change SEGS P E mem0 PO2 mem mZ HE HM RWC LFK) as MC2Z.
    (* [comment removed for export] *)
    assert (FLB0 : exists b, mem (wordZ fla) = Some b /\ bv_unsigned b = 0).
    { exists (FL p). split; [|exact ZP]. apply rdn1_mem_img.
      - clear -FL1 FSlo FS47; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *. unfold SBz, HIGH_MEM_BEG, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *. lia.
      - clear -FL1 FSIMG; unfold FS_FLAGS, FS_FRAMES in *; lia.
      - exact (FLAGS p PRG). }
    (* [comment removed for export] *)
    unfold get_reg2 in El. fold A1 in El. fold A1 in Hsp. rewrite Hsp in El. cbn [app] in El.
    set (fake0 := mkVR FF 0 (RK_fake cid FLs) 0 (fake_size cid) [(0, fake_size cid)]
                        [(24, (8, Some (lsymc SP0 spoff))); (fake_size cid - 8, (8, Some (lsym FLs)))] [] (Some F8)) in El.
    set (shad0 := mkVR F8 (vp_shoff P) (RK_shadow FF) 0 (fake_size cid / 8) [(0, fake_size cid / 8)]
                        [(0, (fake_size cid / 8, Some (lconst 0)))] [] None) in El.
    set (flag0 := mkVR FLs 0 (RK_flag FF) 0 1 [(0, 1)] [] [] None) in El.
    unfold rgn_of_kill in El. rewrite Gfsr in El.
    set (fsr' := set_rnul (set_cells fsr (cm_kill (vr_cells fsr) (8 * cid) (8 * cid + 8)))
                          (List.filter (fun f : Z * Z => (snd f <? 8 * cid) || (8 * cid + 8 <=? fst f)) (vr_nul fsr))) in El.
    set (rg := flag0 :: shad0 :: fake0 :: rgn_upd (vs_rgn A) fsr') in El.
    set (AZ := mkVS2 A6 rg (FF :: vs_live A) (pm_set F8 (lsym FF, 8) (vs_divdef A)) []) in El.
    (* [comment removed for export] *)
    assert (SHf : rshape fsr fsr') by (eapply rshape_trans; [apply rshape_set_cells|apply rshape_set_rnul]).
    pose proof SHf as (SBf & _).
    pose proof LIVE as (LV1 & LV2 & LV3 & ND0).
    assert (INB : In (vr_base fsr') (map vr_base (vs_rgn A))) by (rewrite SBf; apply in_map; exact Hfsr).
    assert (SM : shape_map (vs_rgn A) (rgn_upd (vs_rgn A) fsr')).
    { apply rgn_upd_shape; [|exact INB]. intros x Hx EB.
      rewrite (live_ok_base_inj nu A x fsr LIVE Hx Hfsr ltac:(rewrite EB; exact SBf)). exact SHf. }
    assert (MEM : forall x, In x (rgn_upd (vs_rgn A) fsr') -> x = fsr' \/ (In x (vs_rgn A) /\ vr_base x <> FSB)).
    { intros x Hx. destruct (rgn_upd_other _ _ _ ND0 INB Hx) as [->|[Y1 Y2]]; [auto|right]. rewrite SBf, Bfsr in Y2. auto. }
    assert (OLDB : forall x, In x (vs_rgn A) -> (vr_base x < FF)%positive) by (intros x Hx; exact (proj1 (BR x Hx))).
    assert (INrg : forall x, In x rg <-> x = flag0 \/ x = shad0 \/ x = fake0 \/ In x (rgn_upd (vs_rgn A) fsr')).
    { intros x. unfold rg. split.
      - intros [<-|[<-|[<-|H]]]; auto.
      - intros [->|[->|[->|H]]]; cbn [In]; auto. }
    (* [comment removed for export] *)
    assert (ZFR : forall j, 0 <= j < fake_size cid ->
              in_rw_zones P E (ffa + j) = true /\ (exists k, rdn SEGS mZ (wordZ (ffa + j)) 1 = Some [k]) /\ store_ok SEGS mZ (wordZ (ffa + j)) 1 = true
              /\ covered (unit_regions2 P E) (ffa + j) 1).
    { intros j Hj.
      destruct (zone_covers_sound A nu regs mem FSB 0 FS_FRAMES (FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) (ffa + j) HG2 Z_FRAMES
                  ltac:(rewrite nuE_FSB; clear -Hj FF1 FF2 CL5 SZB; lia)) as (Y1 & [k Y2] & Y3).
      split; [exact Y1|]. split; [eapply (VContractASound2.rdn1_grows SEGS mem mZ); [apply EG|exists k; exact Y2] |].
      split; [apply ES; exact Y3|].
      destruct (in_class_regions (e_fs E) cid p (e_live E) ltac:(lia) PRG NLIVE) as [IC _].
      apply (covered_in _ ffa (fake_size cid)); try (clear -Hj FFR; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG in *; lia).
      unfold unit_regions2. rewrite !in_app_iff. right; right; right. unfold fs_regions. rewrite Efs. apply in_app_iff. right.
      apply (in_classes_regions (e_fs E) (Z.to_nat FS_NCLASSES) cid (e_live E)); [unfold FS_NCLASSES; clear -Hcid; lia|lia|exact IC]. }
    assert (ZSH : forall g, 0 <= g < fake_size cid / 8 ->
              in_rw_zones P E (SBz + ffa / 8 + g) = true /\ (exists k, rdn SEGS mZ (wordZ (SBz + ffa / 8 + g)) 1 = Some [k])
              /\ store_ok SEGS mZ (wordZ (SBz + ffa / 8 + g)) 1 = true /\ covered (unit_regions2 P E) (SBz + ffa / 8 + g) 1).
    { intros g Hg.
      assert (RG : SBz + nuE E FS8 + FS_FRAMES / 8 <= SBz + ffa / 8 + g < SBz + nuE E FS8 + (FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) / 8).
      { pose proof FSal as M. apply Z.mod_divide in M; [|lia]. destruct M as [q Hq].
        assert (DIV8 : e_fs E / 8 = q * 512) by (rewrite Hq; replace (q * 4096) with (q * 512 * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
        rewrite nuE_FS8, DIV8. change (FS_FRAMES / 8) with 4608. change ((FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) / 8) with 659968.
        clear -Hg FF1 FF2 CL5 SZB FFD SZ8 Hq. unfold FS_FRAMES, FS_NCLASSES, FS_SSL in *. lia. }
      destruct (zone_covers_sound A nu regs mem FS8 SBz (FS_FRAMES / 8) ((FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) / 8) _ HG2 Z_FSHAD RG) as (Y1 & [k Y2] & Y3).
      split; [exact Y1|]. split; [eapply (VContractASound2.rdn1_grows SEGS mem mZ); [apply EG|exists k; exact Y2] |].
      split; [apply ES; exact Y3|].
      destruct (in_class_regions (e_fs E) cid p (e_live E) ltac:(lia) PRG NLIVE) as [_ IC]. rewrite SHOFF in IC. fold ffa in IC.
      apply (covered_in _ (SBz + ffa / 8) (fake_size cid / 8)); try (clear -Hg SHR FFR FFD; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG, SBz in *; lia).
      unfold unit_regions2. rewrite !in_app_iff. right; right; right. unfold fs_regions. rewrite Efs. apply in_app_iff. right.
      apply (in_classes_regions (e_fs E) (Z.to_nat FS_NCLASSES) cid (e_live E)); [unfold FS_NCLASSES; clear -Hcid; lia|lia|exact IC]. }
    assert (ZFL : in_rw_zones P E fla = true /\ store_ok SEGS mZ (wordZ fla) 1 = true /\ covered (unit_regions2 P E) fla 1).
    { destruct (zone_covers_sound A nu regs mem FSB 0 FS_FLAGS FS_FRAMES fla HG2 Z_FLAGS ltac:(rewrite nuE_FSB; clear -FL1; lia)) as (Y1 & _ & Y3).
      split; [exact Y1|]. split; [apply ES; exact Y3|].
      apply (covered_in _ (e_fs E + FS_FLAGS) 32768); try (clear -FL1 FSlo FS47; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; lia).
      unfold unit_regions2. rewrite !in_app_iff. right; right; right. unfold fs_regions. rewrite Efs. apply in_app_iff. left. right. left. reflexivity. }
    (* [comment removed for export] *)
    assert (OWN1 : forall ro c fl, In ro (vs_rgn A) -> vr_kind ro = RK_fake c fl -> nu fl = fla -> False).
    { intros ro c fl Hro Kro EQ. pose proof (RGN ro Hro) as (_ & _ & _ & _ & _ & _ & _ & KIND). unfold kind_ok in KIND. rewrite Kro in KIND.
      destruct KIND as (_ & _ & _ & _ & _ & pos & _ & _ & _ & (b & Hb & Hb1) & _). rewrite EQ, FLA in Hb.
      injection Hb as Eb. rewrite <- Eb, ZP in Hb1. discriminate Hb1. }
    assert (FRINJ : forall pos, 0 <= pos < fs_nframes cid -> frame_addr (e_fs E) cid pos = ffa -> pos = p).
    { intros pos Hpos EQ. unfold ffa, frame_addr in EQ. clear -EQ SZB Hpos PRG. nia. }
    assert (FREED : forall x d, In x (vs_rgn A) -> desc_matches E A nu x d -> d <> DFlag cid p /\ d <> DSlot cid p /\ d <> DShSlot cid p).
    { intros x d Hx M. unfold desc_matches in M.
      split; [|split]; intros ->; destruct (vr_kind x) as [c fl| |owner|sx|] eqn:Kx; try contradiction.
      - destruct M as (ro & fl & Gro & KO & Bx & RBo & FLo & NLo). destruct (rgn_get_in _ _ _ Gro) as [Hro _]. exact (OWN1 ro cid fl Hro KO FLo).
      - destruct M as (Ec & RBx & FLx & NLx). subst c. exact (OWN1 x cid fl Hx Kx FLx).
      - destruct M as (ro & Gro & B8 & [(fl & KO & RBo & NLo)|(KO & W0 & L)]); [|exact (NLIVE L)].
        destruct (rgn_get_in _ _ _ Gro) as [Hro _].
        pose proof (RGN ro Hro) as (_ & _ & _ & _ & _ & _ & _ & KIND). unfold kind_ok in KIND. rewrite KO in KIND.
        destruct KIND as (_ & _ & _ & _ & _ & pos & Hpos & RB2 & FL2 & _). rewrite RB2 in RBo. fold ffa in RBo.
        pose proof (FRINJ pos Hpos RBo) as ->. exact (OWN1 ro cid fl Hro KO FL2). }
    (* [comment removed for export] *)
    rewrite SHOFF in LAY.
    assert (OUTB : forall x o, In x (vs_rgn A) -> vr_base x <> FSB -> is_data_shadow x = false -> vr_lo x <= o < vr_hi x ->
              ~ in_blocks (e_fs E) usp p (rbase nu x + o)).
    { intros x o Hx NB ND Ho IB. destruct (region_desc _ _ _ _ PO2 A nu regs mem x HG2 Hx ND) as (d & V & M & D).
      specialize (D o Ho). rewrite SHOFF in D.
      pose proof (slot_range _ _ _ _ cid p LAY Hcid PRG) as (_ & _ & M8 & _ & S64). fold ffa in M8.
      assert (FS8 : e_fs E mod 8 = 0) by (clear -FSal; apply Z.mod_divide; [lia|]; apply Z.mod_divide in FSal; [|lia]; destruct FSal as [q Hq]; exists (q * 512); lia).
      assert (DV : dvalid DHints /\ dvalid (DFlag cid p) /\ dvalid (DSlot cid p) /\ dvalid (DShSlot cid p)) by (unfold dvalid; clear -Hcid PRG; tauto).
      destruct DV as (DV1 & DV2 & DV3 & DV4).
      destruct (block_desc (e_fs E) (e_sp0 (ev1 E)) (vp_frame (p1 P)) _ p FS8 PRG (proj1 SZB) M8 SZ8 IB) as [B|[B|[B|B]]];
        [ pose proof (dbyte_disjoint _ _ _ _ _ _ _ LAY V DV1 D B) as ED
        | pose proof (dbyte_disjoint _ _ _ _ _ _ _ LAY V DV2 D B) as ED
        | pose proof (dbyte_disjoint _ _ _ _ _ _ _ LAY V DV3 D B) as ED
        | pose proof (dbyte_disjoint _ _ _ _ _ _ _ LAY V DV4 D B) as ED ].
      - subst d. unfold desc_matches in M. destruct (vr_kind x); contradiction.
      - exact (proj1 (FREED x d Hx M) ED).
      - exact (proj1 (proj2 (FREED x d Hx M)) ED).
      - exact (proj2 (proj2 (FREED x d Hx M)) ED). }
    (* [comment removed for export] *)
    assert (BEL2' : state_below2 A) by (split; [exact BF|]; split; [exact BR|]; split; [exact BL|]; split; [exact BD|exact BM]).
    assert (RF : forall x0, In x0 (vs_rgn A) -> region_ok SEGS P E nu' (with_v1 A A6) mem x0).
    { intros x0 Hx0. apply (region_ok_frame _ _ _ PO2 A A6 nu nu' mem mem x0 HE (frame_mod_refl _ _) EXT BEL2' Hx0 (RGN x0 Hx0)). }
    assert (REB : forall x0, In x0 (vs_rgn A) -> rbase nu' x0 = rbase nu x0).
    { intros x0 Hx0. unfold rbase. rewrite EXT by exact (OLDB x0 Hx0). reflexivity. }
    assert (RGhead : forall s, (s < FF)%positive -> rgn_get rg s = rgn_get (rgn_upd (vs_rgn A) fsr') s).
    { intros s Hs. unfold rg. cbn [rgn_get vr_base flag0 shad0 fake0].
      rewrite (proj2 (Pos.eqb_neq FLs s)) by (unfold FLs; lia). rewrite (proj2 (Pos.eqb_neq F8 s)) by (unfold F8, FLs; lia).
      rewrite (proj2 (Pos.eqb_neq FF s)) by lia. reflexivity. }
    assert (GETrg : forall s ro, rgn_get (vs_rgn A) s = Some ro -> exists ro', rgn_get rg s = Some ro' /\ rshape ro ro').
    { intros s ro G. destruct (rgn_get_in _ _ _ G) as [Iro Bro].
      rewrite (RGhead s ltac:(rewrite <- Bro; exact (OLDB ro Iro))). exact (shape_map_get _ _ _ _ SM G). }
    assert (BYTE1 : forall y, 0 <= y < 2 ^ 64 -> ~ in_blocks (e_fs E) usp p y -> rdn SEGS mZ (wordZ y) 1 = rdn SEGS mem (wordZ y) 1).
    { intros y Hy NBk. cbn [rdn]. rewrite (E0 y Hy NBk). reflexivity. }
    assert (OLDOK : forall x0, In x0 (vs_rgn A) -> vr_base x0 <> FSB -> region_ok SEGS P E nu' AZ mZ x0).
    { intros x0 Hx0 NB. pose proof (RF x0 Hx0) as ROK. pose proof ROK as (B1 & B2 & B3 & DS & CELLS & PERM & NUL & KIND).
      pose proof (REB x0 Hx0) as RB.
      destruct (is_data_shadow x0) eqn:ND.
      - (* [comment removed for export] *)
        destruct (DS eq_refl) as (C0 & W0 & N0).
        split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [intros _; auto|].
        split; [intros off w v Hin; rewrite C0 in Hin; destruct Hin|].
        split; [intros X; rewrite ND in X; discriminate X|].
        split; [intros lo' hi' Hin; rewrite N0 in Hin; destruct Hin|].
        unfold kind_ok in KIND |- *. unfold is_data_shadow in ND. destruct (vr_kind x0) as [| | |sx|]; try discriminate ND.
        destruct KIND as (F1 & F2 & F3 & F4 & F5 & F6). apply Pos.eqb_eq in ND. subst sx.
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
        intros _ ND2 _. exfalso. exact (ND2 eq_refl).
      - assert (EXTB : forall o, vr_lo x0 <= o < vr_hi x0 -> rdn SEGS mZ (wordZ (rbase nu' x0 + o)) 1 = rdn SEGS mem (wordZ (rbase nu' x0 + o)) 1).
        { intros o Ho. rewrite RB. apply BYTE1; [clear -Ho B1 B2 RB; lia|]. exact (OUTB x0 o Hx0 NB ND Ho). }
        apply (region_ok_self SEGS P E (with_v1 A A6) AZ nu' mem mZ x0 x0 HE ROK (rshape_refl _) ND EG).
        + (* [comment removed for export] *)
          destruct (vr_kind x0) as [c fl| | | |] eqn:Kx; try exact I.
          assert (Efl : nu' fl = nu fl).
          { apply EXT. pose proof (proj2 (proj2 (BR x0 Hx0))) as X. rewrite Kx in X. exact X. }
          rewrite Efl. destruct (region_desc _ _ _ _ PO2 A nu regs mem x0 HG2 Hx0 ND) as (d & V & M & D).
          unfold desc_matches in M. rewrite Kx in M. destruct d as [c' px| | | |]; try contradiction.
          destruct M as (Ec & RBx & FLx & NLx). subst c'. cbn in V.
          pose proof (flag_addr_range (e_fs E) c px (proj1 V) (proj2 V)) as FR. rewrite FLx.
          apply BYTE1; [clear -FR FSlo FS47; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; lia|].
          intros IB. unfold in_blocks in IB. fold ffa fla in IB. destruct IB as [Bk|[Bk|[Bk|[Bk|Bk]]]].
          * clear -Bk FR HNT. unfold FS_FLAGS in *. lia.
          * destruct (flag_addr_inj (e_fs E) c px cid p (proj1 V) (proj2 V) Hcid PRG Bk) as [-> ->]. exact (OWN1 x0 cid fl Hx0 Kx FLx).
          * clear -Bk FR FF1 CL5. unfold FS_FRAMES in *. lia.
          * clear -Bk FR FF1 CL5 SZB. unfold FS_FRAMES in *. lia.
          * clear -Bk FR SHR FSlo FFR FFD; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *. unfold FS_FLAGS in *. lia.
        + (* [comment removed for export] *)
          intros s ro G _ _. cbn [vs_rgn] in G. exact (GETrg s ro G).
        + destruct (vr_kind x0) eqn:Kx; try exact I. unfold AZ. cbn [vs_live]. right.
          apply (proj2 (LV1 (vr_base x0))). exists x0. rewrite Kx. auto.
        + destruct (vr_kind x0) eqn:Kx; try exact I. unfold kind_ok in KIND. rewrite Kx in KIND. exact (proj1 (proj2 (proj2 (proj2 KIND)))).
        + intros off w v Hin. destruct (CELLS off w v Hin) as (CB1 & CB2 & CB3 & RC). split; [exact CB1|]. split; [exact CB2|]. split; [exact CB3|].
          eapply (rcell_holds_ext (is_shadow x0) nu' nu' mem mZ _ w v FF (ext_refl _ _)); try (clear -CB1 CB2 CB3 B1 B2; lia).
          * destruct v; [apply lin_below_mono with (b := FF); [apply Pos.le_refl|]|exact I].
            exact (proj1 (proj2 (BR x0 Hx0)) _ _ _ Hin).
          * intros i2 Hi2. replace (rbase nu' x0 + off + i2) with (rbase nu' x0 + (off + i2)) by lia. apply EXTB. clear -Hi2 CB1 CB3; lia.
          * apply rdn_ext; [rewrite u_wordZ; clear -CB1 CB2 CB3 B1 B2; lia|]. intros xx Hxx. rewrite u_wordZ in Hxx by (clear -CB1 CB2 CB3 B1 B2; lia).
            rewrite <- (wordZ_u xx). apply E0; [clear -Hxx CB1 CB2 CB3 B1 B2; lia|].
            replace (bv_unsigned xx) with (rbase nu x0 + (bv_unsigned xx - rbase nu x0)) by lia.
            apply (OUTB x0 _ Hx0 NB ND). clear -Hxx CB1 CB3 RB. lia.
          * exact RC.
        + intros lo' hi' Hin. destruct (NUL lo' hi' Hin) as (off & b & N1 & N2 & N3 & N4). exists off, b.
          split; [exact N1|]. split; [exact N2|]. split; [|exact N4]. rewrite (EXTB off N2). exact N3. }
    (* [comment removed for export] *)
    assert (FSROK : region_ok SEGS P E nu' AZ mZ fsr').
    { pose proof (RF fsr Hfsr) as ROK. pose proof ROK as (B1 & B2 & B3 & DS & CELLS & PERM & NUL & KIND).
      pose proof (REB fsr Hfsr) as RB. rewrite Frb in RB.
      assert (EXTP : forall o, 0 <= o < 88 -> ~ (8 * cid <= o < 8 * cid + 8) -> mZ (wordZ (rbase nu' fsr + o)) = mem (wordZ (rbase nu' fsr + o))).
      { intros o Ho No. rewrite RB. apply E0; [clear -Ho FSlo FS47; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG, FS_FRAMES, FS_NCLASSES, FS_SSL in *; lia|].
        intros IB. unfold in_blocks in IB. fold ffa fla in IB. destruct IB as [Bk|[Bk|[Bk|[Bk|Bk]]]].
        - clear -Bk No Ho. lia.
        - clear -Bk FL1 Ho. unfold FS_FLAGS in *. lia.
        - clear -Bk FF1 CL5 Ho. unfold FS_FRAMES in *. lia.
        - clear -Bk FF1 CL5 SZB Ho. unfold FS_FRAMES in *. lia.
        - clear -Bk SHR FSlo FFR FFD Ho; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *. unfold FS_FLAGS in *. lia. }
      assert (EXTB : forall o, 0 <= o < 88 -> ~ (8 * cid <= o < 8 * cid + 8) ->
                rdn SEGS mZ (wordZ (rbase nu' fsr + o)) 1 = rdn SEGS mem (wordZ (rbase nu' fsr + o)) 1).
      { intros o Ho No. cbn [rdn]. rewrite (EXTP o Ho No). reflexivity. }
      apply (region_ok_self SEGS P E (with_v1 A A6) AZ nu' mem mZ fsr fsr' HE ROK SHf NDF EG).
      + rewrite Kfsr. exact I.
      + intros s ro G _ _. cbn [vs_rgn] in G. exact (GETrg s ro G).
      + rewrite Kfsr. exact I.
      + rewrite Kfsr. exact I.
      + intros off w v Hin. unfold fsr' in Hin. cbn [vr_cells set_rnul set_cells] in Hin.
        pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin) as DJ. apply cm_kill_sub in Hin.
        destruct (CELLS off w v Hin) as (CB1 & CB2 & CB3 & RC). split; [exact CB1|]. split; [exact CB2|]. split; [exact CB3|].
        rewrite Flo in CB1. rewrite Fhi in CB3.
        eapply (rcell_holds_ext (is_shadow fsr) nu' nu' mem mZ _ w v FF (ext_refl _ _)); try (clear -CB1 CB2 CB3 B1 B2 Flo Fhi; lia).
        * destruct v; [apply lin_below_mono with (b := FF); [apply Pos.le_refl|]|exact I]. exact (proj1 (proj2 (BR fsr Hfsr)) _ _ _ Hin).
        * intros i2 Hi2. replace (rbase nu' fsr + off + i2) with (rbase nu' fsr + (off + i2)) by lia. apply EXTB; clear -Hi2 CB1 CB3 DJ; lia.
        * apply rdn_ext; [rewrite u_wordZ; clear -CB1 CB2 CB3 B1 B2 Flo Fhi; lia|]. intros xx Hxx. rewrite u_wordZ in Hxx by (clear -CB1 CB2 CB3 B1 B2 Flo Fhi; lia).
          rewrite <- (wordZ_u xx). rewrite Z2Nat.id in Hxx by lia.
          replace (bv_unsigned xx) with (rbase nu' fsr + (bv_unsigned xx - rbase nu' fsr)) by lia.
          apply EXTP; clear -Hxx CB1 CB3 DJ; lia.
        * exact RC.
      + intros lo' hi' Hin. unfold fsr' in Hin. cbn [vr_nul set_rnul set_cells] in Hin. apply filter_In in Hin as [Hin Hf].
        destruct (NUL lo' hi' Hin) as (off & b & N1 & N2 & N3 & N4). exists off, b.
        split; [exact N1|]. split; [exact N2|]. split; [|exact N4]. rewrite Flo in N2. rewrite Fhi in N2.
        rewrite (EXTB off N2); [exact N3|]. cbn [fst snd] in Hf. apply Bool.orb_prop in Hf.
        destruct Hf as [Hf|Hf]; [apply Z.ltb_lt in Hf|apply Z.leb_le in Hf]; clear -Hf N1; lia. }
    (* [comment removed for export] *)
    assert (NSP0 : nu' SP0 = e_sp0 E1).
    { rewrite EXT by (unfold SP0, LAST_FIXED2 in *; lia). exact (proj1 (proj2 (proj2 HG1)) SP0 (e_sp0 E1) eq_refl). }
    assert (USPR : 0 <= usp < 2 ^ 64) by (clear -USP U1; unfold HIGH_MEM_BEG in *; lia).
    assert (FLAR : 0 <= fla < 2 ^ 64) by (clear -FL1 FSlo FS47; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; lia).
    assert (RGfake : rgn_get rg FF = Some fake0).
    { unfold rg. cbn [rgn_get vr_base flag0 shad0 fake0].
      rewrite (proj2 (Pos.eqb_neq FLs FF)) by (unfold FLs; lia). rewrite (proj2 (Pos.eqb_neq F8 FF)) by (unfold F8, FLs; lia).
      rewrite Pos.eqb_refl. reflexivity. }
    assert (FAKEOK : region_ok SEGS P E nu' AZ mZ fake0).
    { unfold fake0, region_ok, region_cells_ok, region_perm_ok, region_nul_ok, kind_ok.
      unfold rbase. cbn [vr_disp vr_base vr_lo vr_hi vr_cells vr_w vr_nul vr_kind vr_b8 is_data_shadow is_shadow]. rewrite NFF, Z.add_0_l.
      split; [clear -FFR; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG in *; lia|]. split; [clear -FFR; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; lia|]. split; [clear -SZB; lia|].
      split; [intros X; discriminate X|]. split.
      { intros off w v Hin. destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <- <-.
        - split; [lia|]. split; [lia|]. split; [clear -SZB; lia|]. cbn [rcell_holds andb]. unfold cell_holds.
          exists (word_to_le_bytes 8 (wordZ usp)). split; [exact E24|]. rewrite bytes_le_to_Z_8, u_wordZ by exact USPR.
          rewrite eval_lsymc, NSP0. symmetry. apply zwrap_id. exact USPR.
        - split; [clear -SZB; lia|]. split; [lia|]. split; [lia|]. cbn [rcell_holds andb lin_is_const lsym]. unfold cell_holds.
          replace (ffa + (fake_size cid - 8)) with (ffa + fake_size cid - 8) by lia.
          exists (word_to_le_bytes 8 (wordZ fla)). split; [exact Esz|]. rewrite bytes_le_to_Z_8, u_wordZ by exact FLAR.
          rewrite eval_lsym, NFL. symmetry. apply zwrap_id. exact FLAR. }
      split.
      { intros _. split.
        - intros off Hoff. destruct (ZFR off Hoff) as (Y1 & Y2 & Y3 & Y4). split; [apply rw_any; exact Y1|exact Y2].
        - intros lo' hi' off [Hin|[]] Hoff. injection Hin as <- <-. destruct (ZFR off Hoff) as (Y1 & Y2 & Y3 & Y4). auto. }
      split; [intros lo' hi' []|].
      split; [exact FSnz'|]. split; [exact Hcid|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact BF|].
      exists p. split; [exact PRG|]. split; [reflexivity|]. split; [exact NFL|]. split.
      - exists (Z_to_bv 8 1). rewrite NFL. split; [exact Eflag|reflexivity].
      - split; [exact NLIVE|]. unfold AZ. cbn [vs_live]. left. reflexivity. }
    assert (SHADOK : region_ok SEGS P E nu' AZ mZ shad0).
    { unfold shad0, region_ok, region_cells_ok, region_perm_ok, region_nul_ok, kind_ok.
      unfold rbase. cbn [vr_disp vr_base vr_lo vr_hi vr_cells vr_w vr_nul vr_kind vr_b8 is_data_shadow is_shadow]. rewrite NF8, SHOFF.
      assert (NDATA : Pos.eqb FF DATA = false) by (apply Pos.eqb_neq; unfold DATA, LAST_FIXED2 in *; lia). rewrite NDATA.
      split; [clear -SHR FFR FFD; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold SBz, HIGH_MEM_BEG in *; lia|]. split; [clear -SHR; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG in *; lia|]. split; [clear -SZ8b; lia|].
      split; [intros X; discriminate X|]. split.
      { intros off w v [Hin|[]]. injection Hin as <- <- <-. split; [lia|]. split; [clear -SZ8b; lia|]. split; [lia|].
        cbn [rcell_holds andb lin_is_const lconst lc]. intros i2 Hi2. exists (Z_to_bv 8 0). split; [|reflexivity].
        rewrite Z.add_0_r. exact (Esh i2 Hi2). }
      split.
      { intros _. split.
        - intros off Hoff. destruct (ZSH off Hoff) as (Y1 & Y2 & Y3 & Y4). split; [apply rw_any; exact Y1|exact Y2].
        - intros lo' hi' off [Hin|[]] Hoff. injection Hin as <- <-. destruct (ZSH off Hoff) as (Y1 & Y2 & Y3 & Y4). auto. }
      split; [intros lo' hi' []|].
      split; [exact FSnz'|]. split; [reflexivity|].
      split; [intros X; exfalso; unfold SP0, LAST_FIXED2 in *; lia|].
      split; [intros X; exfalso; unfold DATA, LAST_FIXED2 in *; lia|].
      split; [unfold FSB, LAST_FIXED2 in *; lia|].
      intros _ _ _. exists fake0. split; [unfold AZ; cbn [vs_rgn]; exact RGfake|]. split; [reflexivity|].
      unfold fake0, rbase. cbn [vr_kind vr_disp vr_base]. rewrite NFF. split; [clear -FFD; lia|]. split; [lia|]. clear -SZ8; lia. }
    assert (FLAGOK : region_ok SEGS P E nu' AZ mZ flag0).
    { unfold flag0, region_ok, region_cells_ok, region_perm_ok, region_nul_ok, kind_ok.
      unfold rbase. cbn [vr_disp vr_base vr_lo vr_hi vr_cells vr_w vr_nul vr_kind vr_b8 is_data_shadow is_shadow]. rewrite NFL, Z.add_0_l.
      destruct ZFL as (W1 & W2 & W3).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [intros X; discriminate X|]. split; [intros off w v []|]. split.
      { intros _. split.
        - intros off Hoff. replace (fla + off) with fla by lia. split; [apply rw_any; exact W1|]. exists (Z_to_bv 8 1). exact Eflag.
        - intros lo' hi' off [Hin|[]] Hoff. injection Hin as <- <-. replace (fla + off) with fla by lia. auto. }
      split; [intros lo' hi' []|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists fake0, cid, FLs. split; [unfold AZ; cbn [vs_rgn]; exact RGfake|]. split; reflexivity. }
    assert (RGNZ : forall r, In r rg -> region_ok SEGS P E nu' AZ mZ r).
    { intros r Hr. apply INrg in Hr as [->|[->|[->|Hr]]]; [exact FLAGOK|exact SHADOK|exact FAKEOK|].
      destruct (MEM r Hr) as [->|[Ir NBr]]; [exact FSROK|exact (OLDOK r Ir NBr)]. }
    (* [comment removed for export] *)
    assert (Kfsr' : vr_kind fsr' = RK_fs) by (unfold fsr'; cbn; exact Kfsr).
    assert (OLDRB : forall x c fl, In x (vs_rgn A) -> vr_kind x = RK_fake c fl -> rbase nu x <> ffa).
    { intros x c fl Hx Kx EQ. pose proof (RGN x Hx) as (_ & _ & _ & _ & _ & _ & _ & KIND). unfold kind_ok in KIND. rewrite Kx in KIND.
      destruct KIND as (_ & Hc & _ & _ & _ & pos & Hpos & RBx & FLx & _).
      destruct (Z.eq_dec c cid) as [->|NE].
      - rewrite RBx in EQ. pose proof (FRINJ pos Hpos EQ) as ->. exact (OWN1 x cid fl Hx Kx FLx).
      - destruct (frames_disjoint (e_fs E) c pos cid p ltac:(clear -Hc; lia) Hpos ltac:(clear -Hcid; lia) PRG ltac:(left; exact NE)) as [D|D];
          fold ffa in D; rewrite <- RBx, EQ in D; pose proof (fake_size_bounds c Hc); clear -D SZB H; lia. }
    assert (LIVEZ : live_ok nu' AZ).
    { unfold AZ. split; [|split; [|split]]; cbn [vs_rgn vs_live].
      - intros s. split.
        + intros [<-|Hs].
          * exists fake0. split; [apply INrg; auto|]. split; [reflexivity|]. unfold fake0. cbn. exact I.
          * destruct (proj1 (LV1 s) Hs) as (x & Hx & Bx & Kx). exists x. split; [|auto]. apply INrg. right; right; right.
            apply rgn_upd_keep; [exact Hx|]. rewrite SBf, Bfsr. intros EB.
            rewrite (live_ok_base_inj nu A x fsr LIVE Hx Hfsr ltac:(rewrite EB, Bfsr; reflexivity)) in Kx. rewrite Kfsr in Kx. exact Kx.
        + intros (x & Hx & Bx & Kx). apply INrg in Hx as [->|[->|[->|Hx]]].
          * unfold flag0 in Kx. cbn in Kx. destruct Kx.
          * unfold shad0 in Kx. cbn in Kx. destruct Kx.
          * left. unfold fake0 in Bx. cbn in Bx. exact Bx.
          * right. destruct (MEM x Hx) as [->|[Ix _]]; [rewrite Kfsr' in Kx; destruct Kx|].
            apply (proj2 (LV1 s)). exists x. auto.
      - apply (proj2 (NoDup_ListNoDup _)). constructor; [|apply (proj1 (NoDup_ListNoDup _)); exact LV2].
        intros IN. pose proof (BL FF IN). lia.
      - intros r1 r2 H1 H2.
        assert (CASE : forall r, In r rg -> match vr_kind r with RK_fake _ _ => True | _ => False end ->
                  r = fake0 \/ (In r (vs_rgn A) /\ vr_base r <> FSB)).
        { intros r Hr Kr. apply INrg in Hr as [->|[->|[->|Hr]]].
          - unfold flag0 in Kr. cbn in Kr. destruct Kr. - unfold shad0 in Kr. cbn in Kr. destruct Kr. - left; reflexivity.
          - destruct (MEM r Hr) as [->|X]; [rewrite Kfsr' in Kr; destruct Kr|right; exact X]. }
        destruct (vr_kind r1) as [c1 f1| | | |] eqn:KR1; try exact I. destruct (vr_kind r2) as [c2 f2| | | |] eqn:KR2; try exact I.
        intros NB12.
        destruct (CASE r1 H1 ltac:(rewrite KR1; exact I)) as [->|[I1 _]]; destruct (CASE r2 H2 ltac:(rewrite KR2; exact I)) as [->|[I2 _]].
        + exfalso. exact (NB12 eq_refl).
        + unfold fake0 at 1. unfold rbase at 1. cbn [vr_disp vr_base]. rewrite NFF, Z.add_0_l, (REB r2 I2). intros EQ. exact (OLDRB r2 c2 f2 I2 KR2 (eq_sym EQ)).
        + unfold fake0. unfold rbase at 2. cbn [vr_disp vr_base]. rewrite NFF, Z.add_0_l, (REB r1 I1). intros EQ. exact (OLDRB r1 c1 f1 I1 KR1 EQ).
        + rewrite (REB r1 I1), (REB r2 I2). pose proof (LV3 r1 r2 I1 I2) as X. rewrite KR1, KR2 in X. exact (X NB12).
      - unfold rg. cbn [map vr_base flag0 shad0 fake0]. rewrite (shape_map_bases _ _ SM).
        assert (NOld : forall s, (FF <= s)%positive -> ~ In s (map vr_base (vs_rgn A))).
        { intros s Hs IN. apply in_map_iff in IN as (x & <- & Hx). pose proof (OLDB x Hx). lia. }
        constructor; [|constructor; [|constructor; [|exact ND0]]].
        + intros [X|[X|X]]; [unfold F8, FLs in X; (ltac2:(LK.k [@E11; @Bfsr; @NX2; @NX3; @NX4; @NX5; @NX6; @SBf; @X]); lia)|unfold FLs in X; (ltac2:(LK.k [@E11; @Bfsr; @NX2; @NX3; @NX4; @NX5; @NX6; @SBf; @X]); lia)|exact (NOld FLs ltac:(unfold FLs; (ltac2:(LK.k [@E11; @Bfsr; @NX2; @NX3; @NX4; @NX5; @NX6; @SBf; @X]); lia)) X)].
        + intros [X|X]; [unfold F8, FLs in X; lia|exact (NOld F8 ltac:(unfold F8, FLs; lia) X)].
        + exact (NOld FF ltac:(lia)). }
    (* [comment removed for export] *)
    assert (BELZ : state_below2 AZ).
    { unfold AZ, state_below2. cbn [v1 vs_rgn vs_live vs_divdef vs_memo]. rewrite NX6.
      split; [clear -BF; unfold F8, FLs, LAST_FIXED2 in *; lia|].
      split.
      { intros r Hr. apply INrg in Hr as [->|[->|[->|Hr]]].
        - unfold flag0. cbn [vr_base vr_cells vr_kind]. split; [unfold F8, FLs; clear; lia|]. split; [intros k w e []|exact I].
        - unfold shad0. cbn [vr_base vr_cells vr_kind]. split; [clear; lia|]. split; [|exact I].
          intros k w e [Hin|[]]. injection Hin as <- <- <-. apply lin_below_lconst.
        - unfold fake0. cbn [vr_base vr_cells vr_kind]. split; [unfold F8, FLs; clear; lia|]. split; [|unfold F8, FLs; clear; lia].
          intros k w e [Hin|[Hin|[]]]; injection Hin as <- <- <-.
          + apply lin_below_lsymc. clear -BF. unfold F8, FLs, SP0, LAST_FIXED2 in *. lia.
          + apply lin_below_lsym. unfold F8; clear; lia.
        - destruct (MEM r Hr) as [->|[Ir _]].
          + unfold fsr'. cbn [vr_base vr_cells vr_kind set_rnul set_cells]. rewrite Kfsr.
            destruct (BR fsr Hfsr) as (Bq1 & Bq2 & _). split; [clear -Bq1; unfold F8, FLs; lia|]. split; [|exact I].
            intros k w e Hin. apply cm_kill_sub in Hin. eapply lin_below_mono; [|exact (Bq2 k w e Hin)]. unfold F8, FLs; clear; lia.
          + destruct (BR r Ir) as (Bq1 & Bq2 & Bq3). split; [clear -Bq1; unfold F8, FLs; lia|]. split.
            * intros k w e Hin. eapply lin_below_mono; [|exact (Bq2 k w e Hin)]. unfold F8, FLs; clear; lia.
            * destruct (vr_kind r); try exact I. clear -Bq3; unfold F8, FLs; lia. }
      split.
      { intros s [<-|Hs]; [unfold F8, FLs; clear; lia|]. pose proof (BL s Hs) as X. clear -X. unfold F8, FLs; lia. }
      split; [|intros a n v []].
      intros q x m Hq. rewrite pm_get_set in Hq. destruct (Pos.eqb_spec q F8) as [->|NE].
      - injection Hq as <- <-. split; [clear; lia|]. apply lin_below_lsym. unfold F8, FLs; clear; lia.
      - destruct (BD q x m Hq) as [Dq1 Dq2]. split; [clear -Dq1; unfold F8, FLs; lia|]. eapply lin_below_mono; [|exact Dq2]. unfold F8, FLs; clear; lia. }
    Time (assert (GLZ : globs_ok2 P AZ) by (unfold globs_ok2, AZ; cbn [v1]; rewrite SG6; exact GL2)).
    Time (assert (FIXZ : gamma_fix2 E nu') by (eapply gamma_fix2_ext; [|exact EXT|exact HF2]; clear -BF; unfold LAST_FIXED2 in *; lia)).
    assert (DIVZ : gamma_divdef nu' AZ).
    { intros q x m Hq. unfold AZ in Hq. cbn [vs_divdef] in Hq. rewrite pm_get_set in Hq.
      destruct (Pos.eqb_spec q F8) as [->|NE].
      - injection Hq as <- <-. split; [clear; lia|]. rewrite NF8, eval_lsym, NFF. reflexivity.
      - destruct (HDD q x m Hq) as [Y1 Y2]. destruct (BD q x m Hq) as [Dq1 Dq2]. split; [exact Y1|].
        rewrite EXT by exact Dq1. rewrite (eval_ext_below FF nu nu' x EXT Dq2). exact Y2. }
    assert (OWNZ : own_flags AZ nu' = fla :: own_flags A nu).
    { unfold AZ, rg. rewrite own_flags_cons3.
      change (vr_kind flag0) with (RK_flag FF). change (vr_kind shad0) with (RK_shadow FF). change (vr_kind fake0) with (RK_fake cid FLs).
      cbn [app]. rewrite NFL, (own_flags_shape A A6 _ nu' _ _ _ SM), (own_flags_nu_ext A nu nu' EXT BEL2'). reflexivity. }
    assert (FIZ : flags_inv P E AZ nu' mZ).
    { intros _ c q Hc Hq NL NO. rewrite OWNZ in NO.
      destruct (FI2 FSnz' c q Hc Hq NL ltac:(intros IN; apply NO; right; exact IN)) as (b & Hb & Hb0).
      exists b. split; [|exact Hb0]. rewrite <- Hb.
      pose proof (flag_addr_range (e_fs E) c q Hc Hq) as FR.
      apply E0; [clear -FR FSlo FS47; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; lia|].
      intros IB. unfold in_blocks in IB. fold ffa fla in IB. destruct IB as [B|[B|[B|[B|B]]]].
      - clear -B FR HNT. unfold FS_FLAGS in *. lia.
      - destruct (flag_addr_inj (e_fs E) c q cid p Hc Hq Hcid PRG B) as [-> ->]. apply NO. left. reflexivity.
      - clear -B FR FF1 CL5. unfold FS_FRAMES in *. lia.
      - clear -B FR FF1 CL5 SZB. unfold FS_FRAMES in *. lia.
      - clear -B FR SHR FSlo FFR FFD; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *. unfold FS_FLAGS in *. lia. }
    assert (G2Z : gamma2 SEGS P E mem0 AZ nu' regs mZ).
    { split; [exact GZ1|]. split; [exact HE|]. split; [exact MC2Z|]. split; [exact FIXZ|]. split; [exact DIVZ|].
      split; [unfold AZ at 1; cbn [vs_rgn]; exact RGNZ|]. split; [exact LIVEZ|]. split; [exact BELZ|]. split; [exact GLZ|]. split; [exact FIZ|].
      intros a n v []. }
    (* [comment removed for export] *)
    assert (JG : forall x, mZ x <> None -> m' x <> None).
    { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (usp - K208)) as [X|X]; [rewrite (JM x (or_introl X)); exact Hx|].
      destruct (Z_le_gt_dec usp (bv_unsigned x)) as [Y|Y]; [rewrite (JM x (or_intror Y)); exact Hx|].
      apply JG0. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
      rewrite <- (wordZ_u x), (E0 (bv_unsigned x) ltac:(clear -Rx; lia)) in Hx; [rewrite wordZ_u in Hx; exact Hx|].
      intros IB. unfold in_blocks in IB. fold ffa fla in IB. destruct IB as [B|[B|[B|[B|B]]]].
      - clear -B X Y FSAP HNT Hcid. unfold FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL, K208 in *. lia.
      - clear -B X Y FSAP FL1. unfold FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL, K208 in *. lia.
      - clear -B X Y FSAP FF1 FF2 CL5 SZB. unfold FS_FRAMES, FS_NCLASSES, FS_SSL, K208 in *. lia.
      - clear -B X Y FSAP FF1 FF2 CL5 SZB. unfold FS_FRAMES, FS_NCLASSES, FS_SSL, K208 in *. lia.
      - clear -B X Y SHR U1; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *. unfold K208 in *. lia. }
    (* [comment removed for export] *)
    pose proof (gamma_junk SEGS P1 E1 (zpatch P E mem0 mZ) PO A6 nu' regs mZ m' spoff 208 K208 GZ1 JM JG
                  ltac:(unfold K208; clear; lia) K1 K2) as GJ.
    set (v := Some (lsym FF)).
    set (Bst := contract_frame C_memset (killK 208 A6 spoff) spoff v).
    assert (EFR : frame_rule 208 A6 spoff v = Bst) by (apply frame_rule_killK; clear; lia).
    destruct (killK_shape 208 A6 spoff) as (KS1 & KS2 & KS3 & KS4 & KS5 & KS6 & KS7 & KS8 & KS9).
    destruct (contract_frame_shape C_memset (killK 208 A6 spoff) spoff v) as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7 & CF8 & CFR).
    assert (HLB : lgamma Bst nu').
    { apply lgamma_contract_frame; [apply lgamma_killK; exact L6|]. unfold v. cbn [vbelow]. rewrite KS4, NX6. apply lin_below_lsym. unfold F8, FLs; clear; lia. }
    assert (FFW : 0 <= ffa < 2 ^ 64) by (clear -FFR SZB; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG in *; lia).
    destruct (gamma_call_post SEGS P1 E1 (zpatch P E mem0 mZ) rom PO (killK 208 A6 spoff) Bst nu' nu' regs regs' m' m' []
                GJ (ext_refl _ _) ltac:(unfold Bst; rewrite CF5; apply Pos.le_refl) HLB) as [GB _].
    { eapply (gamma_regs_contract_frame SEGS P1 E1 (zpatch P E mem0 mZ) C_memset (killK 208 A6 spoff) (killK 208 A6 spoff) spoff v nu' nu' regs regs');
        [right; pose proof GJ as (_&_&_&_&_&_&_&KRg&_&_&_&KBl); split; [exact KRg|destruct KBl as (_&_&KRB&_); exact KRB]
        |apply ext_refl|reflexivity|exact QK|].
      unfold v. rewrite Q10, u_wordZ, eval_lsym, NFF by exact FFW. symmetry. apply zwrap_id. exact FFW. }
    { intros off' w' v' Hin. left. unfold Bst in Hin. rewrite CF1 in Hin. cbn in Hin. split; [exact Hin|]. intros x _. exact I. }
    { intros g w' v' Hin. unfold Bst in Hin. rewrite CF2 in Hin. split; [exact Hin|]. intros x _. exact I. }
    { intros lo' hi' Hin. left. unfold Bst in Hin. destruct (CF3 _ Hin) as [Hin' _]. split; [exact Hin'|]. intros x _. exact I. }
    { apply frame_mod_refl. }
    { intros x Hx. exfalso. apply Hx. exact I. }
    (* [comment removed for export] *)
    assert (FMU : frame_mod mZ m' (unit_regions P1 E1)).
    { split; [|exact JG]. intros a Ha. apply JM.
      destruct (Z_lt_le_dec (bv_unsigned a) (usp - K208)) as [X|X]; [left; exact X|].
      destruct (Z_le_gt_dec usp (bv_unsigned a)) as [Y|Y]; [right; exact Y|]. exfalso.
      refine (proj1 (stack_R_ok SEGS P1 E1 (zpatch P E mem0 mZ) PO (spoff - 208) (spoff - 208) spoff 208 K1 K2 ltac:(clear; lia) ltac:(clear; lia) KW HEV1 a _) Ha).
      cbn [outside]. unfold in_rng. rewrite u_wordZ by (clear -USP U1 U2; unfold usp, K208, HIGH_MEM_BEG in *; lia).
      intros [Z1 _]. apply Z1. clear -X Y. unfold usp, K208 in *. lia. }
    destruct (gamma2_lift SEGS P E mem0 PO2 AZ Bst nu' nu' regs regs' mZ m' G2Z GB (ext_refl _ _)
                ltac:(unfold AZ, Bst; cbn [v1]; rewrite CF5, KS4; apply Pos.le_refl) FMU
                ltac:(unfold globs_ok2, AZ, Bst; cbn [v1 with_v1]; rewrite CF2, KS2, SG6; exact GL2) ltac:(right; reflexivity))
      as (G3 & FM3 & FST3).
    (* [comment removed for export] *)
    assert (FMZ : frame_mod mem mZ (unit_regions2 P E)).
    { split; [|exact EG]. intros a Ha. rewrite <- (wordZ_u a). pose proof (bv_unsigned_in_range 64 a) as Ra. change (bv_modulus 64) with (2 ^ 64) in Ra.
      apply E0; [exact Ra|]. intros IB.
      assert (COV : covered (unit_regions2 P E) (bv_unsigned a) 1).
      { unfold in_blocks in IB. fold ffa fla in IB. destruct IB as [B|[B|[B|[B|B]]]].
        - apply (covered_in _ (e_fs E) 88); try (clear -B Hcid FSlo FS47; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG, FS_FRAMES, FS_NCLASSES, FS_SSL in *; lia).
          unfold unit_regions2. rewrite !in_app_iff. right; right; right. unfold fs_regions. rewrite Efs. apply in_app_iff. left. left. reflexivity.
        - rewrite B. exact (proj2 (proj2 ZFL)).
        - replace (bv_unsigned a) with (ffa + (bv_unsigned a - ffa)) by (clear; lia).
          exact (proj2 (proj2 (proj2 (ZFR (bv_unsigned a - ffa) ltac:(clear -B SZB; lia))))).
        - replace (bv_unsigned a) with (ffa + (bv_unsigned a - ffa)) by (clear; lia).
          exact (proj2 (proj2 (proj2 (ZFR (bv_unsigned a - ffa) ltac:(clear -B SZB; lia))))).
        - replace (bv_unsigned a) with (SBz + ffa / 8 + (bv_unsigned a - (SBz + ffa / 8))) by (clear; lia).
          exact (proj2 (proj2 (proj2 (ZSH (bv_unsigned a - (SBz + ffa / 8)) ltac:(clear -B; lia))))). }
      apply (covered_not_outside mem0 _ _ COV Ra). rewrite wordZ_u. exact Ha. }
    assert (FSZ : flags_step P E A AZ nu nu' mem mZ).
    { intros a Ha. unfold in_flags_zone in Ha. rewrite Efs in Ha. rewrite OWNZ. destruct (Z.eq_dec a fla) as [->|NE].
      - right; left. split; [left; reflexivity|]. split; [exact NOWN|exact FLB0].
      - left. split.
        + split; [intros X; right; exact X|]. intros [X|X]; [exfalso; exact (NE (eq_sym X))|exact X].
        + apply E0; [clear -Ha FSlo FS47; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; lia|].
          intros IB. unfold in_blocks in IB. fold ffa fla in IB. destruct IB as [B|[B|[B|[B|B]]]].
          * clear -B Ha HNT. unfold FS_FLAGS in *. lia.
          * exact (NE B).
          * clear -B Ha FF1 CL5. unfold FS_FLAGS, FS_FRAMES in *. lia.
          * clear -B Ha FF1 CL5 SZB. unfold FS_FLAGS, FS_FRAMES in *. lia.
          * clear -B Ha SHR FSlo FFR FFD; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *. unfold FS_FLAGS, HIGH_MEM_BEG, SBz in *. lia. }
    (* [comment removed for export] *)
    assert (ECF : contract_frame2 (C_stack_malloc cid) AZ spoff v = with_v1 AZ Bst).
    { unfold contract_frame2. change (v1 AZ) with A6. cbn [contract2_K]. unfold K_stack_malloc. rewrite EFR. reflexivity. }
    exists AZ, v, regs', m', nu'. rewrite ECF.
    split; [rewrite El; left; reflexivity|]. split; [exact MS|]. split; [exact G3|].
    split; [exact Q1|]. split; [exact EXT|]. split.
    { unfold vs2_next. change (v1 (with_v1 AZ Bst)) with Bst. change (v1 A) with A1. unfold Bst. rewrite CF5, KS4, NX6. apply pos_le_s3. }
    split; [exact (frame_mod_trans_same _ _ _ _ FMZ FM3)|].
    eapply flags_step_then_same; [exact FSZ|]. intros y Hy.
    change (own_flags (with_v1 AZ Bst) nu') with (own_flags AZ nu'). split; [reflexivity|].
    unfold in_flags_zone in Hy. rewrite Efs in Hy.
    apply JM. rewrite u_wordZ by (clear -Hy FSlo FS47; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG, SBz, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; unfold HIGH_MEM_BEG, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *; lia).
    clear -Hy FSAP. unfold FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL, K208 in *. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem stack_malloc_dead : contract_dead2 SEGS P E mem0 CI (C_stack_malloc cid).
  Proof.
    intros A spoff nu regs mem HC _. revert HC. cbn [contract_apply2]. unfold of_ca, ca_stack_malloc.
    destruct (asan_mode P); cbn [negb]; [|discriminate].
    destruct ((0 <=? cid) && (cid <=? 4)); cbn [negb]; [|discriminate].
    destruct (get_reg2 A 4) as [etp|]; cbn [negb]; [|discriminate].
    destruct (lin_eqb etp (lconst (ci_tp CI))); cbn [negb]; [|discriminate].
    destruct (get_reg2 A A0r) as [ea|]; [|discriminate].
    destruct (lin_is_const ea && (0 <? lc ea) && (lc ea <=? Z.shiftl 64 cid)); cbn [negb]; [|discriminate].
    destruct (rgn_get (vs_rgn A) FSB) as [fsr|]; [|discriminate].
    destruct (vr_kind fsr); cbn [negb]; try discriminate.
    destruct (8 <=? Z.of_nat (length (vs_live A))); [discriminate|].
    destruct (vp_fdepth P + Z.of_nat (length (vs_live A)) + 1 <=? Z.shiftl 1 (14 - cid)); cbn [negb]; [|discriminate].
    destruct (aassume2 _ _ _) as [ok1 A3]. destruct (ameet_cong A3 _ _ _) as [ok2 A4].
    destruct (aassume2 A4 _ _) as [ok3 A5]. destruct (aassume2 A5 _ _) as [ok4 A6].
    destruct (ok1 && ok2 && ok3 && ok4); cbn [negb]; discriminate.
  Qed.
End S.
