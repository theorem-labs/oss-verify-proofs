From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem LibcNeeds_c plain_c expected_m.
Import ListNotations.
Open Scope Z_scope.

Lemma nth_error_skipn' : forall (L : list byte) k i, nth_error (skipn k L) i = nth_error L (k + i).
Proof. induction L as [|x L IH]; intros [|k] i; cbn; try reflexivity; [destruct i; reflexivity|apply IH]. Qed.

Lemma nth_error_firstn' : forall (L : list byte) n i, (i < n)%nat -> nth_error (firstn n L) i = nth_error L i.
Proof. induction L as [|x L IH]; intros [|n] [|i] H; cbn; try reflexivity; try lia. apply IH. lia. Qed.

Lemma bytes_at_skip : forall m a L k, bytes_at rsegs m a L -> (k <= length L)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k L).
Proof.
  intros m a L k (Ha & Hl & H) Hk. split; [lia|]. rewrite length_skipn. split; [lia|].
  intros i Hi. replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  rewrite H by lia. symmetry. apply nth_error_skipn'.
Qed.

Lemma bytes_at_first : forall m a L n, bytes_at rsegs m a L -> bytes_at rsegs m a (firstn n L).
Proof.
  intros m a L n (Ha & Hl & H). split; [lia|]. rewrite length_firstn. split; [lia|].
  intros i Hi. rewrite H by lia. symmetry. apply nth_error_firstn'. lia.
Qed.

Lemma firstn1_skipn : forall (L : list byte) k d, (k < length L)%nat -> firstn 1 (skipn k L) = [nth k L d].
Proof. induction L as [|x L IH]; intros [|k] d H; cbn in *; try lia; try reflexivity. apply IH. lia. Qed.

Lemma nth_map_bv : forall (l : list byte) k, nth k (map bv_unsigned l) 0 = bv_unsigned (nth k l (Z_to_bv 8 0)).
Proof. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma zbytes_skipn : forall (l : list byte) k, zbytes (skipn k l) = skipn k (zbytes l).
Proof. unfold zbytes. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

Lemma zbytes_firstn : forall (l : list byte) k, zbytes (firstn k l) = firstn k (zbytes l).
Proof. unfold zbytes. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma in_skipn' : forall (l : list byte) k x, In x (skipn k l) -> In x l.
Proof. induction l as [|y l IH]; intros [|k] x H; cbn in *; try tauto. right. eapply IH. exact H. Qed.

Lemma zbytes_length : forall (l : list byte), length (zbytes l) = length l.
Proof. intros. unfold zbytes. apply length_map. Qed.

Lemma zbytes_app : forall (l l' : list byte), zbytes (l ++ l') = zbytes l ++ zbytes l'.
Proof. intros. unfold zbytes. apply map_app. Qed.

Lemma noz_zbytes : forall l : list byte, Forall (fun b => bv_unsigned b <> 0) l -> Forall (fun c => c <> 0) (zbytes l).
Proof. intros l H. unfold zbytes. apply Forall_map. exact H. Qed.

Section E.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (lo : Z) (tx ux : word) (tb ts ub us : list byte).
Hypotheses (NT : Forall (fun b => bv_unsigned b <> 0) tb) (NU : Forall (fun b => bv_unsigned b <> 0) ub)
  (LT : (- (bv_unsigned tx + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length ts))
  (LU : (- (bv_unsigned ux + Z.of_nat (length ub) + 1)) mod 8 <= Z.of_nat (length us))
  (T0 : 4096 <= bv_unsigned tx) (U0 : 4096 <= bv_unsigned ux)
  (TL : Z.of_nat (length tb) + 1 < 2^62) (UL : Z.of_nat (length ub) + 1 < 2^62)
  (TB : bv_unsigned tx + Z.of_nat (length tb + 1 + length ts) <= 2^64)
  (UB : bv_unsigned ux + Z.of_nat (length ub + 1 + length us) <= 2^64)
  (LO : lo + 240 <= bv_unsigned sp) (LO0 : 0 <= lo) (RSP : bv_unsigned sp < 2^64)
  (DT : bv_unsigned tx + Z.of_nat (length tb + 1 + length ts) <= bv_unsigned sp - 240 \/ bv_unsigned sp <= bv_unsigned tx)
  (DU : bv_unsigned ux + Z.of_nat (length ub + 1 + length us) <= bv_unsigned sp - 240 \/ bv_unsigned sp <= bv_unsigned ux)
  (DP : 66582 + 7 <= bv_unsigned sp - 240 \/ bv_unsigned sp <= 66582).

Hypotheses (STRLEN_C : strlen_contract) (STRCHR_C : strchr_contract) (STRNCMP_C : strncmp_contract)
  (BCMP_C : bcmp_contract) (PLAIN_C : plain_contract).

Abbreviation PFB := [Z_to_bv 8 112; Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 102; Z_to_bv 8 105; Z_to_bv 8 120;
  Z_to_bv 8 0].

Definition SAVED : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition Q : machine_state -> Prop :=
  kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 240 m0 []
    (fun r => r = Z_to_bv 64 (names (zbytes tb) (zbytes ub))).

Definition MI (m : word -> option byte) : Prop :=
  bytes_at rsegs m (bv_unsigned tx) (tb ++ Z_to_bv 8 0 :: ts) /\
  bytes_at rsegs m (bv_unsigned ux) (ub ++ Z_to_bv 8 0 :: us) /\
  bytes_at rsegs m 66582 PFB /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp + -208) /\
  munch [(bv_unsigned sp - 240, bv_unsigned sp)] m0 m /\
  wmono rsegs m0 m.

Definition tbyte (k : nat) : byte := nth k tb (Z_to_bv 8 0).
Definition ubyte (k : nat) : byte := nth k ub (Z_to_bv 8 0).

Lemma tbyte_val : forall k, bv_unsigned (tbyte k) = byte_at (zbytes tb) k.
Proof. intros k. unfold tbyte, byte_at, zbytes. rewrite nth_map_bv. reflexivity. Qed.

Lemma ubyte_val : forall k, bv_unsigned (ubyte k) = byte_at (zbytes ub) k.
Proof. intros k. unfold ubyte, byte_at, zbytes. rewrite nth_map_bv. reflexivity. Qed.

Lemma tb_nz : forall k, (k < length tb)%nat -> byte_at (zbytes tb) k <> 0.
Proof.
  intros k Hk. rewrite <- tbyte_val. unfold tbyte. rewrite Forall_forall in NT. apply NT. apply nth_In. exact Hk.
Qed.

Lemma tb_range : forall k, 0 <= byte_at (zbytes tb) k < 256.
Proof. intros k. rewrite <- tbyte_val. apply byte_range. Qed.

Lemma rd_t : forall m k, bytes_at rsegs m (bv_unsigned tx) (tb ++ Z_to_bv 8 0 :: ts) -> (k <= length tb)%nat ->
  ov_read_bytes rsegs m (wa (bv_unsigned tx + Z.of_nat k)) 1 = Some [tbyte k].
Proof.
  intros m k H Hk. rewrite (bytes_at_read rsegs m _ _ (Z.of_nat k) 1 H) by (rewrite ?length_app; cbn; lia).
  rewrite Nat2Z.id. rewrite (firstn1_skipn _ _ (Z_to_bv 8 0)) by (rewrite length_app; cbn; lia).
  unfold tbyte. destruct (Nat.lt_ge_cases k (length tb)).
  - rewrite app_nth1 by lia. reflexivity.
  - rewrite app_nth2 by lia. replace (k - length tb)%nat with O by lia. rewrite (nth_overflow tb) by lia. reflexivity.
Qed.

Lemma cstr_t : forall m k, bytes_at rsegs m (bv_unsigned tx) (tb ++ Z_to_bv 8 0 :: ts) -> (k <= length tb)%nat ->
  cstr_at m (bv_unsigned tx + Z.of_nat k) (skipn k tb) ts.
Proof.
  intros m k H Hk. split; [|split].
  - replace (skipn k tb ++ Z_to_bv 8 0 :: ts) with (skipn k (tb ++ Z_to_bv 8 0 :: ts)).
    + apply bytes_at_skip; [exact H|]. rewrite length_app. lia.
    + rewrite skipn_app. replace (k - length tb)%nat with O by lia. reflexivity.
  - rewrite Forall_forall in NT |- *. intros x Hx. apply NT. eapply in_skipn'. exact Hx.
  - rewrite length_skipn. replace (bv_unsigned tx + Z.of_nat k + Z.of_nat (length tb - k)) with
      (bv_unsigned tx + Z.of_nat (length tb)) by lia. exact LT.
Qed.

Lemma cstr0_t : forall m k, bytes_at rsegs m (bv_unsigned tx) (tb ++ Z_to_bv 8 0 :: ts) -> (k <= length tb)%nat ->
  cstr0 m (bv_unsigned tx + Z.of_nat k) (skipn k tb).
Proof.
  intros m k H Hk. destruct (cstr_t m k H Hk) as [B [N _]]. split; [|exact N].
  replace (skipn k tb ++ [Z_to_bv 8 0]) with (firstn (length (skipn k tb) + 1) (skipn k tb ++ Z_to_bv 8 0 :: ts)).
  - apply bytes_at_first. exact B.
  - rewrite firstn_app, firstn_all2 by lia. replace (length (skipn k tb) + 1 - length (skipn k tb))%nat with 1%nat by lia.
    reflexivity.
Qed.

Lemma cstr_u : forall m k, bytes_at rsegs m (bv_unsigned ux) (ub ++ Z_to_bv 8 0 :: us) -> (k <= length ub)%nat ->
  cstr_at m (bv_unsigned ux + Z.of_nat k) (skipn k ub) us.
Proof.
  intros m k H Hk. split; [|split].
  - replace (skipn k ub ++ Z_to_bv 8 0 :: us) with (skipn k (ub ++ Z_to_bv 8 0 :: us)).
    + apply bytes_at_skip; [exact H|]. rewrite length_app. lia.
    + rewrite skipn_app. replace (k - length ub)%nat with O by lia. reflexivity.
  - rewrite Forall_forall in NU |- *. intros x Hx. apply NU. eapply in_skipn'. exact Hx.
  - rewrite length_skipn. replace (bv_unsigned ux + Z.of_nat k + Z.of_nat (length ub - k)) with
      (bv_unsigned ux + Z.of_nat (length ub)) by lia. exact LU.
Qed.

Lemma cstr0_u : forall m, bytes_at rsegs m (bv_unsigned ux) (ub ++ Z_to_bv 8 0 :: us) -> cstr0 m (bv_unsigned ux) ub.
Proof.
  intros m H. destruct (cstr_u m 0 H ltac:(lia)) as [B [N _]]. rewrite Z.add_0_r in B. cbn [skipn] in B, N.
  split; [|exact N].
  replace (ub ++ [Z_to_bv 8 0]) with (firstn (length ub + 1) (ub ++ Z_to_bv 8 0 :: us)).
  - apply bytes_at_first. exact B.
  - rewrite firstn_app, firstn_all2 by lia. replace (length ub + 1 - length ub)%nat with 1%nat by lia. reflexivity.
Qed.

Lemma cstr0_pf : forall m, bytes_at rsegs m 66582 PFB -> cstr0 m 66582 (map (Z_to_bv 8) prefix_lc).
Proof.
  intros m H. split.
  - exact H.
  - repeat constructor; vm_compute; discriminate.
Qed.

Lemma sp_u : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -208)) = bv_unsigned sp + -208.
Proof. apply unsigned_lit. lia. Qed.

Lemma epi : forall m low (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27
    x28 x29 x30 x31 : word) (r : Z),
  MI m -> rw_cells rsegs m (bv_unsigned sp + -208) (low ++ SAVED) -> cells_size low = 104%nat ->
  r = names (zbytes tb) (zbytes ub) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -208)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x19 x20 x21 x22 (Z_to_bv 64 r) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1394c) fc None m
    (seg_rom rsegs)).
Proof.
  intros m low x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30
    x31 r HM FR HL HR.
  destruct HM as (BT & BU & PF & MEM & ST & MU & WM). clear BT BU PF.
  apply (rw_cells_merge rsegs m _ [] low SAVED) in FR. cbn [app] in FR. rewrite HL in FR. unfold SAVED in FR.
  do 15 zstep.
  release_frame FR ST (bv_unsigned sp). zstep.
  finish. rewrite HR. reflexivity.
Qed.

Abbreviation MST x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 pc m :=
  (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Abbreviation SPV := (Z_to_bv 64 (bv_unsigned sp + -208)).
Abbreviation tt := (zbytes tb).
Abbreviation uu := (zbytes ub).

Ltac mi := unfold MI; repeat match goal with |- _ /\ _ => split end; try assumption.

Ltac xpost :=
  lazymatch goal with
  | |- forall _, kret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m _ _ _ -> _ =>
      let ms' := fresh "ms'" in let PO := fresh "PO" in intros ms' PO;
      unfold kret in PO; rewrite ?sp_u in PO; unfold STRCHR_K, PLAIN_K in PO; revert ms' PO;
      post_call rsegs m
  end.

Lemma ncmp_u : forall x : list Z,
  firstn (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (length ub))))) (x ++ [0]) =
  firstn (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (length ub))))) (uu ++ [0]) <->
  firstn (length uu) x = uu.
Proof.
  intros x. rewrite unsigned_lit by lia. rewrite Nat2Z.id.
  rewrite <- (zbytes_length ub). rewrite firstn_app_len. apply firstn_noz. apply noz_zbytes. exact NU.
Qed.

Lemma len_tt : length tt = length tb.
Proof. apply zbytes_length. Qed.

Lemma len_uu : length uu = length ub.
Proof. apply zbytes_length. Qed.

Lemma wl : forall (k : nat) m j (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30
    x31 : word),
  MI m -> rw_cells rsegs m (bv_unsigned sp + -208) (CB 104 j :: SAVED) ->
  (k < length tb)%nat -> byte_at tt k = 60 ->
  (forall j', (j' < k)%nat -> whole_at tt uu j' = false) ->
  (length ub <> 0)%nat ->
  (whole tt uu = false -> forall m' j' (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y27
     y28 y29 y30 y31 : word),
     MI m' -> rw_cells rsegs m' (bv_unsigned sp + -208) (CB 104 j' :: SAVED) ->
     evt rsegs Q (MST y1 SPV gp tp y5 y6 y7 y8 ux y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.of_nat (length ub)))
       y19 y20 y21 y22 y23 y24 y25 tx y27 y28 y29 y30 y31 0x135e4 m')) ->
  evt rsegs Q (MST x1 SPV gp tp x5 x6 x7 (Z_to_bv 64 62) ux x10 x11 x12 x13 x14 x15 x16 x17
    (Z_to_bv 64 (Z.of_nat (length ub))) (Z_to_bv 64 (bv_unsigned tx + Z.of_nat k)) x20 x21 x22 x23 x24 x25 tx x27 x28
    x29 x30 x31 0x135ac m).
Proof.
  intros k. remember (length tb - k)%nat as meas eqn:Emeas. revert k Emeas.
  induction meas as [meas IH] using lt_wf_ind.
  intros k Emeas m j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
    HM FR Hk Hlt Hbefore Hu MAIN.
  destruct HM as (BT & BU & PF & MEM & ST & MU & WM). unfold SAVED in FR.
  assert (NEXT : whole_at tt uu k = false -> forall m' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23
      y24 y25 y27 y28 y29 y30 y31 : word),
      MI m' -> rw_cells rsegs m' (bv_unsigned sp + -208) (CB 104 j :: SAVED) ->
      evt rsegs Q (MST y1 SPV gp tp y5 y6 y7 (Z_to_bv 64 62) ux y10 y11 y12 y13 y14 y15 y16 y17
        (Z_to_bv 64 (Z.of_nat (length ub))) y19 (Z_to_bv 64 (bv_unsigned tx + Z.of_nat k + 1)) y21 y22 y23 y24 y25 tx
        y27 y28 y29 y30 y31 0x135d0 m')).
  { intros HW m' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y27 y28 y29 y30 y31 HM' FR'.
    clear BT BU PF MEM ST MU WM FR.
    destruct HM' as (BT & BU & PF & MEM & ST & MU & WM). unfold SAVED in FR'.
    do 3 zstep.
    eapply evt_cut; [eapply STRCHR_C | xpost].
    { rewrite unsigned_lit by lia. replace (bv_unsigned tx + Z.of_nat k + 1) with (bv_unsigned tx + Z.of_nat (S k)) by lia.
      apply cstr_t; [exact BT|lia]. }
    { rewrite unsigned_lit by lia. lia. }
    { exact MEM. }
    { rewrite sp_u. exact ST. }
    { unfold STRCHR_K. rewrite sp_u. lia. }
    { unfold off_stack, STRCHR_K. rewrite sp_u, unsigned_lit by lia. rewrite length_skipn. lia. }
    change (bv_unsigned (Z_to_bv 64 60)) with 60 in POST. rewrite zbytes_skipn in POST.
    destruct (find_idx (fun x => x =? 60) (skipn (S k) tt)) as [o|] eqn:Ef; subst.
    - apply find_idx_some in Ef as (Ho & Ho60 & Hbef). rewrite length_skipn, len_tt in Ho.
      apply Z.eqb_eq in Ho60. rewrite nth_skipn0 in Ho60.
      zstep. zstep. if_cases HC; zify_cond HC; [|lia].
      replace (Z_to_bv 64 (bv_unsigned tx + Z.of_nat k + 1 + Z.of_nat o))
        with (Z_to_bv 64 (bv_unsigned tx + Z.of_nat (S k + o))) by (f_equal; lia).
      eapply (IH (length tb - (S k + o))%nat); [lia | reflexivity | mi | exact FR' | lia | exact Ho60 | | exact Hu
        | exact MAIN].
      intros j' Hj'. destruct (Nat.lt_trichotomy j' k) as [Hl'|[He'|Hg']].
      + apply Hbefore. exact Hl'.
      + subst j'. exact HW.
      + apply whole_at_not_lt. pose proof (Hbef (j' - S k)%nat ltac:(lia)) as X. rewrite nth_skipn0 in X.
        replace (S k + (j' - S k))%nat with j' in X by lia. apply Z.eqb_neq in X. exact X.
    - zstep. zstep. if_cases HC; zify_cond HC; [lia|].
      eapply MAIN; [|mi|exact FR'].
      apply whole_false_of. intros k' Hk'. rewrite len_tt in Hk'.
      destruct (Nat.lt_trichotomy k' k) as [Hl'|[He'|Hg']].
      + apply Hbefore. exact Hl'.
      + subst k'. exact HW.
      + apply whole_at_not_lt. destruct (Nat.lt_ge_cases k' (length tb)) as [Hk2|Hk2].
        * pose proof (find_idx_none _ _ Ef (k' - S k)) as X. rewrite length_skipn, len_tt in X.
          specialize (X ltac:(lia)). rewrite nth_skipn0 in X. replace (S k + (k' - S k))%nat with k' in X by lia.
          apply Z.eqb_neq in X. exact X.
        * rewrite byte_at_ge by (rewrite len_tt; lia). lia. }
  do 5 zstep.
  eapply evt_cut; [eapply STRNCMP_C | xpost].
  { rewrite unsigned_lit by lia. replace (bv_unsigned tx + Z.of_nat k + 1) with (bv_unsigned tx + Z.of_nat (S k)) by lia.
    apply cstr0_t; [exact BT|lia]. }
  { apply cstr0_u. exact BU. }
  { exact MEM. }
  { rewrite sp_u. exact ST. }
  rewrite ncmp_u, zbytes_skipn in POST.
  zstep. if_cases HC.
  - zify_cond HC. assert (HW : whole_at tt uu k = false).
    { destruct (whole_at tt uu k) eqn:E; [|reflexivity]. apply whole_at_spec in E as (_ & E & _).
      apply POST in E. contradiction. }
    eapply NEXT; [exact HW| mi | exact FR].
  - zify_cond HC. apply POST in HC. rename HC into HE.
    assert (HL : (S k + length ub <= length tb)%nat).
    { apply (f_equal (@length Z)) in HE. rewrite length_firstn, length_skipn, len_tt, len_uu in HE. lia. }
    pose proof (rd_t _ (S k + length ub) BT HL) as RD.
    zstep. zstep. zstep. if_cases HC; zify_cond HC; rewrite ?tbyte_val in HC.
    + assert (HW : whole_at tt uu k = true).
      { apply whole_at_spec. split; [exact Hlt|]. split; [exact HE|]. rewrite len_uu. exact HC. }
      zstep. zstep. eapply (epi _ [CB 104 j]); [mi | exact FR | reflexivity |].
      symmetry. apply names_whole; [rewrite len_uu; exact Hu|]. apply (whole_true_of _ _ k); [rewrite len_tt; lia|exact HW].
    + assert (HW : whole_at tt uu k = false).
      { destruct (whole_at tt uu k) eqn:E; [|reflexivity]. apply whole_at_spec in E as (_ & _ & E).
        rewrite len_uu in E. contradiction. }
      eapply NEXT; [exact HW| mi | exact FR].
Qed.

End E.
