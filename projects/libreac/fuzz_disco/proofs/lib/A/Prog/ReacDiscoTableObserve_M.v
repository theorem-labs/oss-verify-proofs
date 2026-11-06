From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_observe_c reac_disco_table_observe.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDOC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Module DT := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table.
Module FM := OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib.Mem.
Import ListNotations.
Unset Lia Cache.
Open Scope Z_scope.

Definition ent (X : list byte) (r : Z) : list byte := DTC.sub X (48 * r) 48.

Ltac tm_vl := repeat first
  [ rewrite FM.length_Z_to_le_bytes
  | rewrite DT.length_sub by lia
  | rewrite RDO.upd_len by (tm_vl; lia)
  | rewrite RDO.len_if by (tm_vl; lia)
  | progress cbn [length] ].

Ltac tm_sp := repeat match goal with |- _ /\ _ => split end.

Ltac tm_so := repeat first
  [ rewrite RDO.sub_upd_other by (tm_vl; lia)
  | rewrite RDO.sub_if_other by (tm_vl; lia) ].

Ltac tm_dn := tm_so; repeat (first
  [ progress unfold RDO.kG
  | progress unfold RDO.kF
  | progress unfold RDO.kE
  | progress unfold RDO.kD
  | match goal with |- context [RDO.kC ?a ?b ?c ?d] => unfold RDO.kC; destruct (RDO.cD a b d); cbv iota end
  | progress unfold RDO.kB
  | progress unfold RDO.kA ]; tm_so).

Lemma upd_nth_out : forall (X v : list byte) k j, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length X) -> 0 <= j ->
  ~ (k <= j < k + Z.of_nat (length v)) -> nth_error (DTC.upd X k v) (Z.to_nat j) = nth_error X (Z.to_nat j).
Proof.
  intros X v k j Hk Hv Hj N.
  assert (L : length (DTC.upd X k v) = length X) by (apply RDO.upd_len; assumption).
  destruct (Nat.ltb_spec (Z.to_nat j) (length X)) as [Lt|Ge].
  - unfold DTC.upd. rewrite FM.upd_bytes_nth by lia.
    destruct (Nat.leb_spec (Z.to_nat k) (Z.to_nat j)); destruct (Nat.ltb_spec (Z.to_nat j) (Z.to_nat k + length v));
      cbn [andb]; try reflexivity; lia.
  - assert (E1 : nth_error (DTC.upd X k v) (Z.to_nat j) = None) by (apply nth_error_None; lia).
    assert (E2 : nth_error X (Z.to_nat j) = None) by (apply nth_error_None; lia).
    rewrite E1, E2. reflexivity.
Qed.

Lemma upd_nth_in : forall (X v : list byte) k j, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length X) ->
  k <= j < k + Z.of_nat (length v) -> nth_error (DTC.upd X k v) (Z.to_nat j) = nth_error v (Z.to_nat (j - k)).
Proof.
  intros X v k j Hk Hv Hj. unfold DTC.upd. rewrite FM.upd_bytes_nth by lia.
  destruct (Nat.leb_spec (Z.to_nat k) (Z.to_nat j)); destruct (Nat.ltb_spec (Z.to_nat j) (Z.to_nat k + length v));
    cbn [andb]; try lia.
  f_equal. lia.
Qed.

Lemma ent_len : forall X r, length X = 400%nat -> 0 <= r < 8 -> length (ent X r) = 48%nat.
Proof. intros X r LX Hr. unfold ent. apply DT.length_sub; lia. Qed.

Lemma ent_nth : forall X r i, length X = 400%nat -> 0 <= r < 8 -> 0 <= i < 48 ->
  nth_error (ent X r) (Z.to_nat i) = nth_error X (Z.to_nat (48 * r + i)).
Proof. intros X r i LX Hr Hi. unfold ent. rewrite RDO.nth_sub by lia. f_equal. lia. Qed.

Lemma ent_upd : forall (X v : list byte) r k, length X = 400%nat -> 0 <= r < 8 -> 0 <= k -> k + Z.of_nat (length v) <= 48 ->
  ent (DTC.upd X (48 * r + k) v) r = DTC.upd (ent X r) k v.
Proof.
  intros X v r k LX Hr Hk Hv.
  assert (LU : length (DTC.upd X (48 * r + k) v) = 400%nat) by (rewrite RDO.upd_len; lia).
  assert (LE : length (ent X r) = 48%nat) by (apply ent_len; assumption).
  apply RDO.list_ext_nth.
  - rewrite ent_len by assumption. rewrite RDO.upd_len by lia. lia.
  - intros i Hi. rewrite ent_len in Hi by assumption.
    rewrite <- (Nat2Z.id i).
    rewrite ent_nth by lia.
    assert (D : (k <= Z.of_nat i < k + Z.of_nat (length v)) \/ ~ (k <= Z.of_nat i < k + Z.of_nat (length v))) by lia.
    destruct D as [D|D].
    + rewrite (upd_nth_in X v (48 * r + k) (48 * r + Z.of_nat i)) by lia.
      rewrite (upd_nth_in (ent X r) v k (Z.of_nat i)) by lia.
      f_equal. lia.
    + rewrite (upd_nth_out X v (48 * r + k) (48 * r + Z.of_nat i)) by lia.
      rewrite (upd_nth_out (ent X r) v k (Z.of_nat i)) by lia.
      rewrite ent_nth by lia. reflexivity.
Qed.

Lemma sub_ent : forall X r k n, length X = 400%nat -> 0 <= r < 8 -> 0 <= k -> k + Z.of_nat n <= 48 ->
  DTC.sub (ent X r) k n = DTC.sub X (48 * r + k) n.
Proof.
  intros X r k n LX Hr Hk Hn.
  assert (LE : length (ent X r) = 48%nat) by (apply ent_len; assumption).
  apply RDO.list_ext_nth.
  - rewrite !DT.length_sub by lia. reflexivity.
  - intros i Hi. rewrite DT.length_sub in Hi by lia.
    rewrite !RDO.nth_sub by lia. unfold ent. rewrite RDO.nth_sub by lia. f_equal. lia.
Qed.

Lemma u_at_ent : forall X r k n, length X = 400%nat -> 0 <= r < 8 -> 0 <= k -> k + Z.of_nat n <= 48 ->
  DTC.u_at (ent X r) k n = DTC.u_at X (48 * r + k) n.
Proof. intros X r k n LX Hr Hk Hn. unfold DTC.u_at. rewrite sub_ent by assumption. reflexivity. Qed.

Lemma stage_len : forall T G ow now r, length T = 400%nat -> length G = 24%nat -> 0 <= r < 8 ->
  length (RDO.kA T now r) = 400%nat /\ length (RDO.kB T G now r) = 400%nat /\ length (RDO.kC T G now r) = 400%nat /\
  length (RDO.kD T G now r) = 400%nat /\ length (RDO.kE T G now r) = 400%nat /\ length (RDO.kF T G now r) = 400%nat /\
  length (RDO.kG T G ow now r) = 400%nat.
Proof.
  intros T G ow now r LT LG Hr.
  assert (LA : length (RDO.kA T now r) = 400%nat) by (unfold RDO.kA; tm_vl; lia).
  assert (LB : length (RDO.kB T G now r) = 400%nat) by (unfold RDO.kB; tm_vl; lia).
  assert (LC : length (RDO.kC T G now r) = 400%nat) by (unfold RDO.kC; destruct (RDO.cD T G r); cbv iota; tm_vl; lia).
  assert (LD : length (RDO.kD T G now r) = 400%nat) by (unfold RDO.kD; tm_vl; lia).
  assert (LE : length (RDO.kE T G now r) = 400%nat) by (unfold RDO.kE; tm_vl; lia).
  assert (LF : length (RDO.kF T G now r) = 400%nat) by (unfold RDO.kF; tm_vl; lia).
  assert (LG7 : length (RDO.kG T G ow now r) = 400%nat) by (unfold RDO.kG; tm_vl; lia).
  exact (conj LA (conj LB (conj LC (conj LD (conj LE (conj LF LG7)))))).
Qed.

Lemma ent_kA : forall T now r, length T = 400%nat -> 0 <= r < 8 ->
  ent (RDO.kA T now r) r = DTC.upd (ent T r) 40 (Z_to_le_bytes 8 now).
Proof.
  intros T now r LT Hr. unfold RDO.kA.
  apply ent_upd; [exact LT | exact Hr | lia | tm_vl; lia].
Qed.

Lemma ent_kB : forall T G now r, length T = 400%nat -> length G = 24%nat -> 0 <= r < 8 ->
  ent (RDO.kB T G now r) r =
  if RDO.cR T G r then DTC.upd (ent (RDO.kA T now r) r) 8 (DTC.sub G 8 4) else ent (RDO.kA T now r) r.
Proof.
  intros T G now r LT LG Hr.
  destruct (stage_len T G 0 now r LT LG Hr) as (LA & _).
  unfold RDO.kB. destruct (RDO.cR T G r); cbv iota; [|reflexivity].
  apply ent_upd; [exact LA | exact Hr | lia | tm_vl; lia].
Qed.

Lemma ent_kC : forall T G now r, length T = 400%nat -> length G = 24%nat -> 0 <= r < 8 ->
  ent (RDO.kC T G now r) r =
  if RDO.cD T G r then DTC.upd (DTC.upd (DTC.upd (ent (RDO.kB T G now r) r) 12 [Z_to_bv 8 1]) 13 (DTC.sub G 13 1)) 14 (DTC.sub G 14 1)
  else ent (RDO.kB T G now r) r.
Proof.
  intros T G now r LT LG Hr.
  destruct (stage_len T G 0 now r LT LG Hr) as (LA & LB & _).
  unfold RDO.kC. destruct (RDO.cD T G r); cbv iota; [|reflexivity].
  rewrite !ent_upd by (tm_vl; lia). reflexivity.
Qed.

Lemma ent_kD : forall T G now r, length T = 400%nat -> length G = 24%nat -> 0 <= r < 8 ->
  ent (RDO.kD T G now r) r = if RDO.cS T G r then DTC.upd (ent (RDO.kC T G now r) r) 16 (DTC.sub G 16 1) else ent (RDO.kC T G now r) r.
Proof.
  intros T G now r LT LG Hr.
  destruct (stage_len T G 0 now r LT LG Hr) as (_ & _ & LC & _).
  unfold RDO.kD. destruct (RDO.cS T G r); cbv iota; [|reflexivity].
  apply ent_upd; [exact LC | exact Hr | lia | tm_vl; lia].
Qed.

Lemma ent_kE : forall T G now r, length T = 400%nat -> length G = 24%nat -> 0 <= r < 8 ->
  ent (RDO.kE T G now r) r = if RDO.cF T G r then DTC.upd (ent (RDO.kD T G now r) r) 15 (DTC.sub G 15 1) else ent (RDO.kD T G now r) r.
Proof.
  intros T G now r LT LG Hr.
  destruct (stage_len T G 0 now r LT LG Hr) as (_ & _ & _ & LD & _).
  unfold RDO.kE. destruct (RDO.cF T G r); cbv iota; [|reflexivity].
  apply ent_upd; [exact LD | exact Hr | lia | tm_vl; lia].
Qed.

Lemma ent_kF : forall T G now r, length T = 400%nat -> length G = 24%nat -> 0 <= r < 8 ->
  ent (RDO.kF T G now r) r = if RDO.cC T G r then DTC.upd (ent (RDO.kE T G now r) r) 20 (DTC.sub G 20 4) else ent (RDO.kE T G now r) r.
Proof.
  intros T G now r LT LG Hr.
  destruct (stage_len T G 0 now r LT LG Hr) as (_ & _ & _ & _ & LE & _).
  unfold RDO.kF. destruct (RDO.cC T G r); cbv iota; [|reflexivity].
  apply ent_upd; [exact LE | exact Hr | lia | tm_vl; lia].
Qed.

Lemma ent_kG : forall T G ow now r, length T = 400%nat -> length G = 24%nat -> 0 <= r < 8 ->
  ent (RDO.kG T G ow now r) r =
  if RDO.cO T ow r then DTC.upd (ent (RDO.kF T G now r) r) 24 (Z_to_le_bytes 4 1) else ent (RDO.kF T G now r) r.
Proof.
  intros T G ow now r LT LG Hr.
  destruct (stage_len T G ow now r LT LG Hr) as (_ & _ & _ & _ & _ & LF & _).
  unfold RDO.kG. destruct (RDO.cO T ow r); cbv iota; [|reflexivity].
  apply ent_upd; [exact LF | exact Hr | lia | tm_vl; lia].
Qed.

Lemma stage_out : forall T G ow now r j, length T = 400%nat -> length G = 24%nat -> 0 <= r < 8 -> 0 <= j < 400 ->
  ~ (48 * r <= j < 48 * r + 48) ->
  nth_error (RDO.kA T now r) (Z.to_nat j) = nth_error T (Z.to_nat j) /\
  nth_error (RDO.kB T G now r) (Z.to_nat j) = nth_error T (Z.to_nat j) /\
  nth_error (RDO.kC T G now r) (Z.to_nat j) = nth_error T (Z.to_nat j) /\
  nth_error (RDO.kD T G now r) (Z.to_nat j) = nth_error T (Z.to_nat j) /\
  nth_error (RDO.kE T G now r) (Z.to_nat j) = nth_error T (Z.to_nat j) /\
  nth_error (RDO.kF T G now r) (Z.to_nat j) = nth_error T (Z.to_nat j) /\
  nth_error (RDO.kG T G ow now r) (Z.to_nat j) = nth_error T (Z.to_nat j).
Proof.
  intros T G ow now r j LT LG Hr Hj N.
  destruct (stage_len T G ow now r LT LG Hr) as (LA & LB & LC & LD & LE & LF & LG7).
  assert (OA : nth_error (RDO.kA T now r) (Z.to_nat j) = nth_error T (Z.to_nat j)).
  { unfold RDO.kA. rewrite upd_nth_out by (tm_vl; lia). reflexivity. }
  assert (OB : nth_error (RDO.kB T G now r) (Z.to_nat j) = nth_error T (Z.to_nat j)).
  { unfold RDO.kB. destruct (RDO.cR T G r); cbv iota; repeat (rewrite upd_nth_out by (tm_vl; lia)); exact OA. }
  assert (OC : nth_error (RDO.kC T G now r) (Z.to_nat j) = nth_error T (Z.to_nat j)).
  { unfold RDO.kC. destruct (RDO.cD T G r); cbv iota; repeat (rewrite upd_nth_out by (tm_vl; lia)); exact OB. }
  assert (OD : nth_error (RDO.kD T G now r) (Z.to_nat j) = nth_error T (Z.to_nat j)).
  { unfold RDO.kD. destruct (RDO.cS T G r); cbv iota; repeat (rewrite upd_nth_out by (tm_vl; lia)); exact OC. }
  assert (OE : nth_error (RDO.kE T G now r) (Z.to_nat j) = nth_error T (Z.to_nat j)).
  { unfold RDO.kE. destruct (RDO.cF T G r); cbv iota; repeat (rewrite upd_nth_out by (tm_vl; lia)); exact OD. }
  assert (OF : nth_error (RDO.kF T G now r) (Z.to_nat j) = nth_error T (Z.to_nat j)).
  { unfold RDO.kF. destruct (RDO.cC T G r); cbv iota; repeat (rewrite upd_nth_out by (tm_vl; lia)); exact OE. }
  assert (OG : nth_error (RDO.kG T G ow now r) (Z.to_nat j) = nth_error T (Z.to_nat j)).
  { unfold RDO.kG. destruct (RDO.cO T ow r); cbv iota; repeat (rewrite upd_nth_out by (tm_vl; lia)); exact OF. }
  exact (conj OA (conj OB (conj OC (conj OD (conj OE (conj OF OG)))))).
Qed.

Lemma stage_reads : forall T G ow now r, length T = 400%nat -> length G = 24%nat -> 0 <= r < 8 ->
  DTC.u_at (RDO.kA T now r) (48 * r + 8) 4 = DTC.u_at T (48 * r + 8) 4 /\
  DTC.u_at (RDO.kB T G now r) (48 * r + 12) 1 = DTC.u_at T (48 * r + 12) 1 /\
  DTC.u_at (RDO.kB T G now r) (48 * r + 13) 1 = DTC.u_at T (48 * r + 13) 1 /\
  DTC.u_at (RDO.kB T G now r) (48 * r + 14) 1 = DTC.u_at T (48 * r + 14) 1 /\
  DTC.u_at (RDO.kC T G now r) (48 * r + 16) 1 = DTC.u_at T (48 * r + 16) 1 /\
  DTC.u_at (RDO.kD T G now r) (48 * r + 15) 1 = DTC.u_at T (48 * r + 15) 1 /\
  DTC.u_at (RDO.kE T G now r) (48 * r + 20) 4 = DTC.u_at T (48 * r + 20) 4 /\
  DTC.u_at (RDO.kF T G now r) (48 * r + 24) 4 = DTC.u_at T (48 * r + 24) 4 /\
  DTC.u_at (RDO.kG T G ow now r) 392 4 = DTC.u_at T 392 4.
Proof.
  intros T G ow now r LT LG Hr.
  destruct (stage_len T G ow now r LT LG Hr) as (LA & LB & LC & LD & LE & LF & LG7).
  unfold DTC.u_at. tm_sp; tm_dn; reflexivity.
Qed.

Lemma mac_bytes : forall T G j, length T = 400%nat -> length G = 24%nat -> 0 <= j < 8 ->
  (DTC.mac_of T j = DTC.s_mac G <-> forall i, 0 <= i < 6 -> nth_error T (Z.to_nat (48 * j + i)) = nth_error G (Z.to_nat i)).
Proof.
  intros T G j LT LG Hj. unfold DTC.mac_of, DTC.s_mac. split.
  - intros E i Hi.
    assert (E' : nth_error (DTC.sub T (48 * j) 6) (Z.to_nat i) = nth_error (DTC.sub G 0 6) (Z.to_nat i))
      by (rewrite E; reflexivity).
    rewrite !RDO.nth_sub in E' by lia.
    replace (Z.to_nat (48 * j + i)) with (Z.to_nat (48 * j) + Z.to_nat i)%nat by lia.
    rewrite E'. f_equal; lia.
  - intros H. apply RDO.list_ext_nth.
    + rewrite !DT.length_sub by lia. reflexivity.
    + intros i Hi. rewrite DT.length_sub in Hi by lia. rewrite !RDO.nth_sub by lia.
      pose proof (H (Z.of_nat i) ltac:(lia)) as Hi'. rewrite Nat2Z.id in Hi'.
      replace (Z.to_nat (48 * j) + i)%nat with (Z.to_nat (48 * j + Z.of_nat i)) by lia.
      rewrite Hi'. f_equal; lia.
Qed.

Lemma model_known : forall T G ow now r, length T = 400%nat -> length G = 24%nat ->
  0 <= r < DTC.n_of T -> DTC.mac_of T r = DTC.s_mac G -> (forall j, 0 <= j < r -> DTC.mac_of T j <> DTC.s_mac G) ->
  RDOC.observe_model T G ow now (fst (RDOC.observe_known T G ow now r)) (snd (RDOC.observe_known T G ow now r)).
Proof.
  intros T G ow now r LT LG Hr Hm Hb. unfold RDOC.observe_model, DTC.find_res. exists r. split.
  - right. split; [exact Hr|]. split; [exact Hm | exact Hb].
  - left. split; [lia|]. symmetry. apply surjective_pairing.
Qed.

Lemma model_full : forall T G ow now, (forall j, 0 <= j < DTC.n_of T -> DTC.mac_of T j <> DTC.s_mac G) -> 8 <= DTC.n_of T ->
  RDOC.observe_model T G ow now (fst (RDOC.observe_full T)) (snd (RDOC.observe_full T)).
Proof.
  intros T G ow now Hb Hn. unfold RDOC.observe_model, DTC.find_res. exists (-1). split.
  - left. split; [reflexivity | exact Hb].
  - right. left. split; [reflexivity|]. split; [exact Hn|]. symmetry. apply surjective_pairing.
Qed.

Lemma model_new : forall T G ow now, (forall j, 0 <= j < DTC.n_of T -> DTC.mac_of T j <> DTC.s_mac G) -> DTC.n_of T < 8 ->
  RDOC.observe_model T G ow now (fst (RDOC.observe_new T G ow now)) (snd (RDOC.observe_new T G ow now)).
Proof.
  intros T G ow now Hb Hn. unfold RDOC.observe_model, DTC.find_res. exists (-1). split.
  - left. split; [reflexivity | exact Hb].
  - right. right. split; [reflexivity|]. split; [exact Hn|]. symmetry. apply surjective_pairing.
Qed.

Lemma model_len : forall T G ow now T' ret, length T = 400%nat -> length G = 24%nat -> DTC.tbl_T1 T ->
  RDOC.observe_model T G ow now T' ret -> length T' = 400%nat.
Proof.
  intros T G ow now T' ret LT LG H1 [r [F [[Hr E] | [[Hr [Hn E]] | [Hr [Hn E]]]]]]; unfold DTC.tbl_T1 in H1.
  - assert (Rr : 0 <= r < DTC.n_of T) by (destruct F as [[? _] | [? _]]; lia).
    exact (proj1 (RDO.mf_known T G ow now r T' ret LT LG ltac:(lia) E)).
  - exact (proj1 (RDO.mf_full T T' ret LT E)).
  - exact (proj1 (RDO.mf_new T G ow now T' ret LT LG ltac:(lia) E)).
Qed.

Definition new_steps (G : list byte) (ow now : Z) : list byte :=
  DTC.upd (DTC.upd (DTC.upd (DTC.upd (DTC.upd (DTC.upd (DTC.upd (DTC.upd (DTC.upd (DTC.upd (DTC.upd
    (repeat (Z_to_bv 8 0) 48) 0 (DTC.sub G 0 6)) 8 (DTC.sub G 8 4)) 12 (DTC.sub G 12 1)) 13 (DTC.sub G 13 1))
    14 (DTC.sub G 14 1)) 15 (DTC.sub G 15 1)) 16 (DTC.sub G 16 1)) 20 (DTC.sub G 20 4))
    24 (Z_to_le_bytes 4 (if ow =? 0 then 0 else 1))) 32 (Z_to_le_bytes 8 now)) 40 (Z_to_le_bytes 8 now).

Lemma new_steps_eq : forall G ow now, length G = 24%nat -> new_steps G ow now = RDOC.new_entry G ow now.
Proof.
  intros G ow now L.
  do 24 (destruct G as [|? G]; [discriminate|]). destruct G; [|discriminate].
  reflexivity.
Qed.

Lemma new_table : forall T G ow now, length T = 400%nat -> length G = 24%nat -> 0 <= DTC.n_of T < 8 ->
  let Th := DTC.upd T 384 (Z_to_le_bytes 4 (DTC.n_of T + 1)) in
  let Tn := DTC.upd Th (48 * DTC.n_of T) (RDOC.new_entry G ow now) in
  length Tn = 400%nat /\ DTC.u_at Tn 392 4 = DTC.u_at T 392 4 /\
  RDOC.observe_new T G ow now = (DTC.upd Tn 392 (Z_to_le_bytes 4 (DTC.seq_of T + 1)), 1) /\
  (forall j, 0 <= j < 400 -> ~ (48 * DTC.n_of T <= j < 48 * DTC.n_of T + 48) -> ~ (384 <= j < 388) ->
     nth_error Tn (Z.to_nat j) = nth_error T (Z.to_nat j)) /\
  ent Tn (DTC.n_of T) = RDOC.new_entry G ow now /\ DTC.sub Tn 384 4 = Z_to_le_bytes 4 (DTC.n_of T + 1).
Proof.
  intros T G ow now LT LG Hn. cbv zeta.
  destruct (RDO.mf_ne G ow now LG) as (LN & _).
  split; [tm_vl; lia|].
  split.
  { unfold DTC.u_at. rewrite !RDO.sub_upd_other by (tm_vl; lia). reflexivity. }
  split; [reflexivity|].
  split.
  { intros j Hj N1 N2. repeat (rewrite upd_nth_out by (tm_vl; lia)). reflexivity. }
  split.
  { unfold ent. apply RDO.mf_sub_upd_at; [lia | tm_vl; lia | exact LN]. }
  rewrite RDO.sub_upd_other by (tm_vl; lia).
  apply RDO.mf_sub_upd_at; [lia | tm_vl; lia | apply FM.length_Z_to_le_bytes].
Qed.
