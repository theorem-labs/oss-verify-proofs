(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "of_nat"; "modulo"; "div"; "sub"; "leb"; "to_nat"; "lt"; "ltb"; "eqb"; "@Corelib.Init.Datatypes"; "nat"; "length"; "bool"; "app"; "list"; "andb"; "true"; "nil"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_mapped_user"; "class_state"; "cs_free_array"; "cs_cache"; "cs_allocated_user"; "cs_mapped_free_array"; "cs_n_allocated"; "cs_n_freed"; "mkCS"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cls"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_geom"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "cs_empty"; "list_upd"; "mkAA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "new_ids"; "cls_pure"; "kchunks"; "needs_populate"; "populate_cs"; "refill_cs"; "take_cs"; "kch_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kUserMapSize"; "Size"; "kFreeArrayMapSize"; "max_count"; "round_up"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "MUCAP"; "FACAP"; "CLS30"; "@Stdlib.Lists.List"; "In"; "NoDup"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "add"; "sub"; "@Corelib.Init.Peano"; "lt"; "le"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "nth"; "seq"; "skipn"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model PrimCredit PrimCreditLaws.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition kchunks (c : Z) : Z := max_count c / 2.

Definition new_ids (au S : Z) (new : nat) : list Z := ltac2:(tb__ "0|0|
S4eS11S0S11SaS6Vau;S7SbSbS8Vnew;A1Z1A2S8R1A1A2VS;A2A2Z10A2Lj;S50U0Vnew;A2A4").

Definition populate_cs (c : Z) (cs : class_state) : class_state := ltac2:(tb__ "0|2|
S3eVc;A1S0S6S1bVcs;A1S3dA2S0SdSaSbR1S1fVcs;A1M0A2R2A2A1S11S14S0S1dVcs;A1S35G0R3R1A3A3S15S0A1S7Z4S8S12S0R1A2A1A2S0S13S0L_;SfS20Vcs;A1M1R1A2S41R1S3fA2G1X13x2S0S23R5S6G0S7S8R4A1R6A2A2R3R1S1eVcs;A1S21Vcs;A1S22Vcs;A1A7Tmfa';Tneed;Tfa';Tnew;Tmu';TS;").
Definition take_cs (k : nat) (cs : class_state) : class_state := ltac2:(tb__ "0|2|
S12S0S1dVcs;A1M0A2S11S23S1bVcs;A1S1fVcs;A1S4dS0S4aR1Vk;A2M1G0A3S20Vcs;A1S51S0G1G0A3S6S21Vcs;A1S8Vk;A1A2S22Vcs;A1A7Tnf;").
Definition needs_populate (c : Z) (cs : class_state) : bool := ltac2:(tb__ "0|0|
SfS8S12S0S1dVcs;A1A2A1S37Vc;A1A2").
Definition refill_cs (c : Z) (cs : class_state) : class_state := ltac2:(tb__ "0|0|
S3bSdS37Vc;A1A1S13S1cL_;S38Vc;Vcs;A2S39Vc;Vcs;A2Vcs;X13x2A2").
Definition refillA (A : AA) (c : Z) : AA := ltac2:(tb__ "0|2|
S34S2bVA;A1S33S1cS27VA;A1M0SdVc;A1M1S3aVc;S4fS1cG1G0S32A4A2A4S17S31VA;A1S2eVA;A1S2dVA;A1S30VA;A1S2fVA;A1S28VA;A1S2aVA;A1S29VA;A1S2cVA;A1S26VA;A1S25VA;A1S24VA;A1Af").

Definition kch_okb (c : Z) : bool := ltac2:(tb__ "0|1|
S16S16S16ScZ1S37Vc;A1M0A2ScG0Z8A2A2S10S7Z2G0A2S40Vc;A1A2A2ScS7G0S3eVc;A1A2Z10000A2A2").
Lemma kch_okb_all : ltac2:(tb__ "0|0|
S2S13S47S0S3cS44A3S17A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma kchunks_facts : ltac2:(tb__ "0|2|
S0S1S5Z1M0R1A2S5R1Z1eA2A2S1S1S5G0S37R2A1M1A2S5G1Z8A2A2S1S2S0S7Z2G1A2S40R2A1A3S5S7G1S3eR2A1A2Z10000A2A2A2F_;Fc;").
Proof.
  intros c Hc. pose proof (proj1 (forallb_forall _ _) kch_okb_all c (proj2 (In_CLS30 c) Hc)) as H. unfold kch_okb in H.
  repeat (apply andb_prop in H as [H ?]).
  repeat match goal with X : (_ <=? _) = true |- _ => apply Z.leb_le in X | X : (_ =? _) = true |- _ => apply Z.eqb_eq in X end. lia.
Qed.

Lemma new_ids_length : ltac2:(tb__ "0|0|
S0S0S11S2S11S12S0S35R3R2R1A3A2R1A3Fnew;FS;Fau;").
Proof. intros. unfold new_ids. rewrite length_map, length_seq. reflexivity. Qed.
Lemma new_ids_in : ltac2:(tb__ "0|0|
S0S0S11S0S45S0R1S35R4R3R2A3A3S3S0S0S1S1S5Z0R1A2SeR1S8R4A1A2A2S2S0R3SaS6R6S7R1R5A2A2Z10A2A3A2Li;A2F_;Fx;Fnew;FS;Fau;").
Proof.
  intros au S new x Hin. unfold new_ids in Hin. apply in_map_iff in Hin as (j & <- & Hj). apply in_seq in Hj.
  exists (Z.of_nat new - 1 - Z.of_nat j). split; [lia | reflexivity].
Qed.
Lemma new_ids_nth : ltac2:(tb__ "0|0|
S0S0S11S11S4bR1R2A2S2S1aS0A1S48S0S35R5R4R3A3R2A3S19S0SaS6R5S7SbSbS8R3A1Z1A2S8R2A1A2R4A2A2Z10A2A2A3F_;Fj;Fnew;FS;Fau;").
Proof.
  intros au S new j Hj. unfold new_ids. rewrite nth_error_map, nth_error_seq.
  replace (j <? new)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). reflexivity.
Qed.

Lemma id16 : ltac2:(tb__ "0|3|
S0S0S0S2S0S9R3Z10M0A2Z0A3M1G1S2S0S7G0SaS6R5S7R3R4A2A2M2G0A2A2G2A3F_;F_;Fi;FS;Fau;").
Proof.
  intros au S i Ha HS. symmetry. apply Z.div_exact; [lia|]. rewrite Z.add_mod, Ha by lia. rewrite Z.mul_mod, HS by lia. rewrite Z.mul_0_r. reflexivity.
Qed.
Lemma new_ids_valid : ltac2:(tb__ "0|3|
S0S0S11S0S5Z10M0R3A2S2S0S9R4G0A2Z0M1A3S5G1R6A2S2S0S9R7R6A2G1A3S45S0R5S35R8R7R6A3A3S1S5R9S7G0R6A2M2A2S1S2S0S9G2R8A2G1A3S5S6G2R8A2S6R9S7S8R7A1R8A2A2A2A2A2F_;F_;F_;F_;F_;Fx;Fnew;FS;Fau;").
Proof.
  intros au S new x HS HS16 Hau Hmod Hin. destruct (new_ids_in _ _ _ _ Hin) as (i & Hi & ->).
  assert (Ha16 : au mod 16 = 0).
  { destruct (proj1 (Z.mod_divide au S ltac:(lia)) Hmod) as [q Hq]. destruct (proj1 (Z.mod_divide S 16 ltac:(lia)) HS16) as [r Hr].
    rewrite Hq, Hr. rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
  rewrite (id16 au S i Ha16 HS16). split; [nia|]. split; [|nia].
  rewrite Z.add_mod, Hmod by lia. rewrite Z.mod_mul by lia. reflexivity.
Qed.
Lemma new_ids_NoDup : ltac2:(tb__ "0|2|
S0S0S11S5Z10M0R2A2S2S0S9R3G0A2Z0M1A3S2S0S9R5G0A2G1A3S46S0S35R6R5R4A3A2F_;F_;F_;Fnew;FS;Fau;").
Proof.
  intros au S new HS HS16 Ha16. unfold new_ids.
  assert (G : forall l : list nat, List.NoDup l -> (forall j, In j l -> (j < new)%nat) ->
              List.NoDup (map (fun j => (au + (Z.of_nat new - 1 - Z.of_nat j) * S) / 16) l)).
  { induction l as [|j l IH]; intros ND Hl; cbn [map]; [constructor|]. inversion ND as [|? ? Hj ND']; subst. constructor.
    - intros Hin. apply in_map_iff in Hin as (j2 & E & Hj2). apply Hj.
      assert (E16 : 16 * ((au + (Z.of_nat new - 1 - Z.of_nat j2) * S) / 16) = 16 * ((au + (Z.of_nat new - 1 - Z.of_nat j) * S) / 16)) by (rewrite E; reflexivity).
      rewrite !id16 in E16 by assumption. assert (j2 = j) by nia. subst j2. exact Hj2.
    - apply IH; [exact ND' | intros j2 Hj2; apply Hl; right; exact Hj2]. }
  apply G; [apply seq_NoDup | intros j Hj; apply in_seq in Hj; lia].
Qed.
Lemma new_ids_NoDup_unused : True. Proof. exact I. Qed.
Lemma new_ids_NoDup' : ltac2:(tb__ "0|2|
S0S0S11S5Z10M0R2A2S2S0S9R3G0A2Z0M1A3S2S0S9R5G0A2G1A3S46S0S35R6R5R4A3A2F_;F_;F_;Fnew;FS;Fau;").
Proof.
  intros au S new HS HS16 Ha16. apply new_ids_NoDup; assumption.
Qed.

Definition cls_pure (c : Z) (cs : class_state) (out : list Z) : Prop := ltac2:(tb__ "0|a|
S1S2S0S9S1bVcs;A1M0S3dA2Z0M1A3S1S1S5G1S1fVcs;A1M2A2S5G2G0A2A2S1S2S0S9G2S3eVc;A1M3A2G1A3S1S2S0S9S20Vcs;A1M4S3fA2G1A3S1S5G1G4A2S1S5S7Z4S8S12S0S1dVcs;A1M5A2M6A1A2G4A2S1S0S45S0R1S14S0G5S14S0S1eVcs;A1M7Vout;A3A3M8A3S1S5G1R2A2S1S2S0S9S7Z10R2A2M9G3A2G1A3S5S6G9G3A2G2A2A2A2F_;Fx;S1S46S0G8A2S1SeG0S6G2G3A2A2S1S2S0SaG2G3A2S8S49S49G6S12S0G7A2A2S12S0Vout;A2A2A1A3S1S5G0S42Vc;A1A2S5G4S43Vc;A1A2A2A2A2A2A2A2A2A2A2A2A2").

Lemma populate_pure : ltac2:(tb__ "0|8|
S0S1cS15S0A1M0S1S5Z1M1R3A2S5R3Z1eA2A2S36R4R3R2A3S5S6S1bR4A1S3dA2S42R5A1A2S39R6R5A2S1cS1S36R7R1R5A3S1S2S0S1bR1A1S6S1bR6A1S3dA2A3S1S3S11S11S1S4bU0R1A2S1S2S0SaSbS1bR2A1S1fR7A1M2A2S3eR8A1M3A2S8R1A1M4A3S1S2S0S1fR2A1S6G2S7G4G3A2A2A3S1S2G0S1dR2A1S14S0S1dR7A1S35G2G3R1A3A3A3S1S5G4S6SaS3dG3A2M5G1A2A2S5G5G4A2A2A2A2A2A2Lnew;A2S1S2G0S1eR1A1S1eR6A1A3S1S4S2S0S20R1A1M6S20R6A1M7A3S2S0G6S6G7S3fA2A3A2S5G6S43R7A1A2A2A2A2A2A2Tcs';F_;F_;F_;Fout;Fcs;Fc;").
Proof.
  intros c cs out Hc (P1 & P2 & P3 & P4 & P4' & P5 & P6 & P7 & P8 & P9 & P10 & P11) Hcap cs'.
  destruct (cap_facts c Hc) as (HS & HS16 & MCU & _ & FCU & _ & FCL & _).
  set (S := Size c) in *. set (au := cs_allocated_user cs) in *. set (mu := cs_mapped_user cs) in *. set (mfa := cs_mapped_free_array cs) in *.
  set (newZ := (mu + kUserMapSize - au) / S).
  assert (Hr : 0 <= mu - au < S) by (clear -P2 P8; lia).
  assert (HnewL : kUserMapSize / S <= newZ).
  { unfold newZ. apply Z.div_le_mono; [clear -HS; lia | clear -Hr; lia]. }
  assert (HnewU : newZ <= kUserMapSize / S + 1).
  { unfold newZ. replace (mu + kUserMapSize - au) with (kUserMapSize + (mu - au)) by lia.
    assert (X : (kUserMapSize + (mu - au)) / S <= (kUserMapSize + 1 * S) / S) by (apply Z.div_le_mono; [clear -HS; lia | clear -Hr; lia]).
    rewrite Z.div_add in X by (clear -HS; lia). exact X. }
  assert (Hq : 4 <= kUserMapSize / S) by (unfold kUserMapSize; apply Z.div_le_lower_bound; [clear -HS; lia | clear -HS; lia]).
  assert (Hnew0 : 0 < newZ) by (clear -HnewL Hq; lia).
  set (new := Z.to_nat newZ). assert (Enew : Z.of_nat new = newZ) by (unfold new; rewrite Z2Nat.id; clear -Hnew0; lia).
  assert (Ecs' : cs' = mkCS (mu + kUserMapSize) (au + Z.of_nat new * S) (cs_free_array cs ++ new_ids au S new)
                            (if mfa <? 4 * Z.of_nat (length (cs_free_array cs ++ new_ids au S new)) then round_up (4 * Z.of_nat (length (cs_free_array cs ++ new_ids au S new))) kFreeArrayMapSize else mfa)
                            (cs_cache cs) (cs_n_allocated cs) (cs_n_freed cs)) by reflexivity.

  assert (DM : mu + kUserMapSize - au = S * newZ + (mu + kUserMapSize - au) mod S) by (apply Z.div_mod; clear -HS; lia).
  assert (MB : 0 <= (mu + kUserMapSize - au) mod S < S) by (apply Z.mod_pos_bound; clear -HS; lia).

  set (fa' := cs_free_array cs ++ new_ids au S new) in *.
  assert (Lfa' : Z.of_nat (length fa') = Z.of_nat (length (cs_free_array cs)) + newZ) by (unfold fa'; rewrite length_app, new_ids_length, Nat2Z.inj_add, Enew; reflexivity).
  set (need := 4 * Z.of_nat (length fa')) in *.
  assert (Hneed : need <= mfa + kFreeArrayMapSize).
  { unfold need. rewrite Lfa'. unfold kFreeArrayMapSize, kUserMapSize in *.
    assert (2 ^ 18 / S <= 8192) by (apply Z.div_le_upper_bound; [clear -HS; lia | clear -HS; lia]). clear -P5 HnewU H. lia. }
  set (mfa' := if mfa <? need then round_up need kFreeArrayMapSize else mfa) in *.
  assert (Hmfa' : (mfa' = mfa \/ (mfa' = mfa + kFreeArrayMapSize /\ mfa' < need + kFreeArrayMapSize)) /\ need <= mfa' /\ mfa' mod kFreeArrayMapSize = 0).
  { unfold mfa'. destruct (Z.ltb_spec mfa need) as [L|L]; [|split; [left; reflexivity | split; [exact L | exact P4]]].
    unfold round_up, kFreeArrayMapSize in *. destruct (proj1 (Z.mod_divide mfa (2 ^ 18) ltac:(clear; lia)) P4) as [q Hq'].
    assert (E : (need + 2 ^ 18 - 1) / 2 ^ 18 = q + 1).
    { symmetry. apply Z.div_unique with (need + 2 ^ 18 - 1 - (q + 1) * 2 ^ 18); [left|]; clear -L Hneed Hq'; lia. }
    rewrite E. split; [right; clear -Hq' L; lia|]. split; [clear -L Hneed Hq'; lia | apply Z.mod_mul; clear; lia]. }
  destruct Hmfa' as (Hmfa1 & Hmfa2 & Hmfa3).

  assert (Esl' : (au + Z.of_nat new * S) / S = au / S + newZ).
  { rewrite Enew. replace (au + newZ * S) with ((au / S + newZ) * S); [apply Z.div_mul; clear -HS; lia|].
    pose proof (Z.div_exact au S ltac:(clear -HS; lia)) as DE. rewrite (proj2 DE P3) at 2. lia. }
  assert (HFC : mfa' <= FACAP c).
  { destruct Hmfa1 as [E|[_ E]]; [rewrite E; exact P11|].
    apply (facap_of_mucap c (au + Z.of_nat new * S) (mu + kUserMapSize) mfa' (Z.of_nat (length fa')) Hc); fold S.
    - rewrite Enew. clear -P2 DM MB Hnew0 HS. nia.
    - exact Hcap.
    - apply Nat2Z.is_nonneg.
    - rewrite Esl', P9, Lfa'. lia.
    - exact E. }
  split; [|split; [reflexivity|split; [|split; [reflexivity|split; [destruct Hmfa1 as [E|[E _]]; [left | right]; exact E | exact HFC]]]]].
  -
    rewrite Ecs'. unfold cls_pure. cbn [cs_mapped_user cs_allocated_user cs_free_array cs_mapped_free_array cs_cache]. fold S. fold fa' need mfa'.
    split; [unfold kUserMapSize in *; rewrite Z.add_mod, P1 by (clear; lia); reflexivity|].
    split; [rewrite Enew; clear -P2 DM MB Hnew0 HS; nia|].
    split; [rewrite Z.add_mod by (clear -HS; lia); rewrite P3, Z.mod_mul by (clear -HS; lia); reflexivity|].
    split; [exact Hmfa3|]. split; [clear -Hmfa1 P4'; unfold kFreeArrayMapSize in *; lia|]. split; [exact Hmfa2|].
    split.
    { intros x Hx. unfold fa' in Hx. rewrite <- app_assoc in Hx. apply in_app_or in Hx as [Hx|Hx].
      - destruct (P6 x ltac:(apply in_or_app; left; exact Hx)) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. rewrite Enew. clear -X3 Hnew0 HS. nia.
      - apply in_app_or in Hx as [Hx|Hx].
        + destruct (new_ids_valid au S new x ltac:(clear -HS; lia) HS16 (proj1 P2) P3 Hx) as (V1 & V2 & V3). split; [clear -V1 P2; lia|]. split; [exact V2 | exact V3].
        + destruct (P6 x ltac:(apply in_or_app; right; exact Hx)) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. rewrite Enew. clear -X3 Hnew0 HS. nia. }
    split.
    {
      unfold fa'. rewrite <- app_assoc.
      assert (Ha16 : au mod 16 = 0).
      { destruct (proj1 (Z.mod_divide au S ltac:(clear -HS; lia)) P3) as [q Hq']. destruct (proj1 (Z.mod_divide S 16 ltac:(clear; lia)) HS16) as [r Hr'].
        rewrite Hq', Hr'. rewrite Z.mul_assoc. apply Z.mod_mul. clear; lia. }
      apply NoDup_app_remove_r in P7 as P7a. pose proof P7 as P7c.
      apply (proj2 (NoDup_app_iff' _ _)) || idtac.

      assert (OLD : forall x, In x (cs_free_array cs ++ cs_cache cs ++ out) -> 16 * x < au).
      { intros x Hx. destruct (P6 x Hx) as (_ & _ & X3). clear -X3 HS. lia. }
      assert (NEW : forall x, In x (new_ids au S new) -> au <= 16 * x).
      { intros x Hx. exact (proj1 (new_ids_valid au S new x ltac:(clear -HS; lia) HS16 (proj1 P2) P3 Hx)). }
      clear P7a. revert P7c OLD. generalize (cs_cache cs ++ out) as rest. generalize (cs_free_array cs) as fa0.
      induction fa0 as [|y fa0 IH]; intros rest ND OLD; cbn [app] in *.
      -
        pose proof (new_ids_NoDup au S new ltac:(clear -HS; lia) HS16 Ha16) as NDn.
        revert NDn NEW. generalize (new_ids au S new) as nl. induction nl as [|z nl IHn]; intros NDn NEW; cbn [app]; [exact ND|].
        inversion NDn as [|? ? Hz NDn']; subst. constructor.
        + intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hz Hin)|]. pose proof (OLD z Hin). pose proof (NEW z (or_introl eq_refl)). lia.
        + apply IHn; [exact NDn' | intros x Hx; apply NEW; right; exact Hx].
      - inversion ND as [|? ? Hy ND']; subst. constructor.
        + intros Hin. apply in_app_or in Hin as [Hin|Hin]; [apply Hy; apply in_or_app; left; exact Hin|].
          apply in_app_or in Hin as [Hin|Hin]; [|apply Hy; apply in_or_app; right; exact Hin].
          pose proof (OLD y (or_introl eq_refl)). pose proof (NEW y Hin). lia.
        + apply IH; [exact ND' | intros x Hx; apply OLD; right; exact Hx]. }
    split; [rewrite Enew; clear -DM MB; lia|].
    split.
    { rewrite Esl', P9. unfold fa'. rewrite !length_app, new_ids_length. rewrite !Nat2Z.inj_add, Enew. lia. }
    split; [exact Hcap | exact HFC].
  - exists new. split; [clear -Enew Hnew0; lia|]. split; [rewrite Ecs'; cbn [cs_mapped_user]; fold newZ; rewrite Enew; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. rewrite Enew. split; [exact HnewU | exact HnewL].
Qed.

Lemma take_pure : ltac2:(tb__ "0|4|
S0S1cS15S0A1M0S11S36R4R3R2A3S2G0S1eR4A1S18S0A1A3S4cR3S12S0S1dR5A1A2A2S3bR4R6A2S1cS1S36R8R1R6A3S1S2G0S14S0S1dR1A1M1S1eR1A1M2A3S1dR7A1M3A3S1S2S11S12S0G2A2R5A3S1S2S11S12S0G1A2S4aS12S0G3A2R5A2A3S1S2S0S1bR1A1S1bR7A1A3S1S2S0S1fR1A1S1fR7A1A3S2S0S20R1A1S20R7A1A3A2A2A2A2A2A2Tcs';F_;F_;F_;Fk;Fout;Fcs;Fc;").
Proof.
  intros c cs out k (P1 & P2 & P3 & P4 & P4' & P5 & P6 & P7 & P8 & P9 & P10 & P11) Hc0 Hk cs'.
  unfold cs', take_cs. set (fa := cs_free_array cs) in *. set (nf := length fa) in *.
  assert (E : firstn (nf - k) fa ++ skipn (nf - k) fa = fa) by apply firstn_skipn.
  assert (L1 : length (firstn (nf - k) fa) = (nf - k)%nat) by (rewrite firstn_length_le; [reflexivity | unfold nf; lia]).
  assert (L2 : length (skipn (nf - k) fa) = k) by (rewrite length_skipn; unfold nf in *; lia).
  split; [|cbn [cs_free_array cs_cache cs_mapped_user cs_allocated_user cs_mapped_free_array]; repeat split; assumption].
  unfold cls_pure. cbn [cs_free_array cs_cache cs_mapped_user cs_allocated_user cs_mapped_free_array].
  rewrite Hc0 in P6, P7, P9. cbn [app length] in P6, P7, P9.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P4'|].
  split; [rewrite L1; fold nf in P5; lia|].
  rewrite app_assoc, E. split; [exact P6|]. split; [exact P7|]. split; [exact P8|].
  split; [rewrite P9, L1, L2; fold nf; f_equal; unfold nf in *; lia|]. exact (conj P10 P11).
Qed.

Lemma refill_pure : ltac2:(tb__ "0|1|
S0S1cS15S0A1M0S1S5Z1R3A2S5R3Z1eA2A2S36R4R3R2A3S2G0S1eR4A1S18S0A1A3S2S13S38R6R5A2S17A3S5S6S1bR6A1S3dA2S42R7A1A2F_;S3aR7R6A2S1cS1S36R8R1R6A3S2S0S8S12S0S1eR1A1A2A1S37R8A1A3A2Tcs';F_;F_;F_;F_;Fout;Fcs;Fc;").
Proof.
  intros c cs out Hc HP Hc0 Hroom cs'. destruct (kchunks_facts c Hc) as (K1 & K2 & K3).
  unfold cs', refill_cs. destruct (needs_populate c cs) eqn:NP.
  - destruct (populate_pure c cs out Hc HP (Hroom eq_refl)) as (HP' & _ & (new & Hn0 & _ & _ & Efa & _ & HnL) & Ec & _).
    assert (Hk : (Z.to_nat (kchunks c) <= length (cs_free_array (populate_cs c cs)))%nat).
    { rewrite Efa, length_app, new_ids_length. destruct (cap_facts c Hc) as (HS & _).
      assert (kchunks c <= kUserMapSize / Size c).
      { apply Z.div_le_lower_bound; [clear -HS; lia|]. unfold kUserMapSize. clear -K3. lia. }
      lia. }
    destruct (take_pure c (populate_cs c cs) out (Z.to_nat (kchunks c)) HP' ltac:(rewrite Ec; exact Hc0) Hk) as (T1 & _ & T3 & _).
    split; [exact T1 | rewrite T3; lia].
  - unfold needs_populate in NP. apply Z.ltb_ge in NP.
    destruct (take_pure c cs out (Z.to_nat (kchunks c)) HP Hc0 ltac:(lia)) as (T1 & _ & T3 & _).
    split; [exact T1 | rewrite T3; lia].
Qed.
