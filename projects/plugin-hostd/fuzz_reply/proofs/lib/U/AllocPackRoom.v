From Stdlib Require Import ZArith List Bool Lia Arith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0g YO0s YO0u YO0x YO10 YO0q YO0d YO03 YO0j YO0m YO0n YO0o YO04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import PlaceCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocSI AllocGS AllocMB AllocCount AllocBound AllocSlots AllocPack.
Import ListNotations.
Local Open Scope Z_scope.

Lemma zsumZ_nil f : zsumZ f [] = 0.
Proof. reflexivity. Qed.

Lemma zsumZ_cons f x l : zsumZ f (x :: l) = f x + zsumZ f l.
Proof. reflexivity. Qed.

Lemma zsumZ_ext f g l : (forall x, In x l -> f x = g x) -> zsumZ f l = zsumZ g l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. rewrite !zsumZ_cons, (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy. apply H. right. exact Hy.
Qed.

Lemma zsumZ_zero f l : (forall x, In x l -> f x = 0) -> zsumZ f l = 0.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. rewrite zsumZ_cons, (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy. apply H. right. exact Hy.
Qed.

Lemma zsumZ_le f g l : (forall x, In x l -> f x <= g x) -> zsumZ f l <= zsumZ g l.
Proof.
  induction l as [|x l IH]; intros H; [rewrite !zsumZ_nil; lia|]. rewrite !zsumZ_cons.
  pose proof (H x (or_introl eq_refl)).
  assert (zsumZ f l <= zsumZ g l) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

Lemma zsumZ_nonneg f l : (forall x, In x l -> 0 <= f x) -> 0 <= zsumZ f l.
Proof.
  induction l as [|x l IH]; intros H; [rewrite zsumZ_nil; lia|]. rewrite zsumZ_cons.
  pose proof (H x (or_introl eq_refl)).
  assert (0 <= zsumZ f l) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

Lemma zsumZ_add f g l : zsumZ (fun x => f x + g x) l = zsumZ f l + zsumZ g l.
Proof. induction l as [|x l IH]; [reflexivity|]. rewrite !zsumZ_cons, IH. cbv beta. ring. Qed.

Lemma zsumZ_mul_l a f l : zsumZ (fun x => a * f x) l = a * zsumZ f l.
Proof. induction l as [|x l IH]; [rewrite !zsumZ_nil; ring|]. rewrite !zsumZ_cons, IH. cbv beta. ring. Qed.

Lemma zsumZ_single (f : Z -> Z) c l : NoDup l -> In c l -> zsumZ (fun k => if k =? c then f k else 0) l = f c.
Proof.
  induction l as [|x l IH]; intros Hnd Hin; [destruct Hin|].
  apply NoDup_cons_iff in Hnd as [Hx Hnd]. rewrite zsumZ_cons. cbv beta.
  destruct (Z.eqb_spec x c) as [<-|N]; cbv iota.
  - rewrite (zsumZ_zero (fun k => if k =? x then f k else 0) l); [lia|].
    intros y Hy. cbv beta. destruct (Z.eqb_spec y x) as [->|]; [contradiction|reflexivity].
  - destruct Hin as [E|Hin]; [congruence|]. rewrite IH by assumption. lia.
Qed.

Definition pk_lin (a caps : list Z) : Z := zsumZ (fun k => znth k a * znth k caps) (zseq 0 49).

Lemma pk_lin_sum (p : Z -> bool) (R : Z -> list Z) caps l :
  zsumZ (fun c => if p c then pk_lin (R c) caps else 0) l =
  zsumZ (fun k => zsumZ (fun c => if p c then znth k (R c) else 0) l * znth k caps) (zseq 0 49).
Proof.
  induction l as [|c l IH].
  - change (0 = zsumZ (fun k => 0 * znth k caps) (zseq 0 49)). symmetry. apply zsumZ_zero. intros; reflexivity.
  - rewrite zsumZ_cons, IH. cbv beta.
    transitivity (zsumZ (fun k => (if p c then znth k (R c) * znth k caps else 0) +
      zsumZ (fun c0 => if p c0 then znth k (R c0) else 0) l * znth k caps) (zseq 0 49)).
    + rewrite zsumZ_add. apply (f_equal2 Z.add); [|reflexivity].
      destruct (p c); [reflexivity|]. symmetry. apply zsumZ_zero. intros; reflexivity.
    + apply zsumZ_ext. intros k _. cbv beta. rewrite zsumZ_cons. cbv beta. destruct (p c); ring.
Qed.

Lemma FC_pos c : 0 <= c < 48 -> 8 <= FC c <= 32.
Proof.
  intros Hc. pose proof FC_tab as T. rewrite forallb_forall in T.
  specialize (T c (proj2 (In_zseq 0 48 c) ltac:(lia))). apply andb_true_iff in T as [T1 T2].
  apply Z.leb_le in T1, T2. lia.
Qed.

Lemma nfb_len caps k : length (nf_build caps k) = k.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [nf_build]. rewrite length_app, IH. cbn [length]. lia. Qed.

Lemma nfb_ext caps k m : exists l, nf_build caps (k + m) = nf_build caps k ++ l.
Proof.
  induction m as [|m [l IH]]; [exists []; rewrite Nat.add_0_r, app_nil_r; reflexivity|].
  rewrite Nat.add_succ_r. cbn [nf_build]. rewrite IH. eexists. rewrite <- app_assoc. reflexivity.
Qed.

Lemma nfb_nth caps k m i : (i < k)%nat -> nth i (nf_build caps (k + m)) 0 = nth i (nf_build caps k) 0.
Proof. intros Hi. destruct (nfb_ext caps k m) as [l ->]. apply app_nth1. rewrite nfb_len. exact Hi. Qed.

Lemma nfb_last caps k : nth k (nf_build caps (S k)) 0 = nf_next caps (nf_build caps k) (Z.of_nat k).
Proof. cbn [nf_build]. rewrite app_nth2 by (rewrite nfb_len; lia). rewrite nfb_len, Nat.sub_diag. reflexivity. Qed.

Lemma NF_next caps c : 0 <= c < 48 -> znth c (NF caps) = nf_next caps (nf_build caps (Z.to_nat c)) c.
Proof.
  intros Hc. unfold NF, znth.
  replace 48%nat with (S (Z.to_nat c) + (47 - Z.to_nat c))%nat by lia.
  rewrite nfb_nth by lia. rewrite nfb_last, Z2Nat.id by lia. reflexivity.
Qed.

Lemma NF_prefix caps c c' : 0 <= c' < c -> c <= 48 -> znth c' (nf_build caps (Z.to_nat c)) = znth c' (NF caps).
Proof.
  intros H1 H2. unfold NF, znth.
  replace 48%nat with (Z.to_nat c + (48 - Z.to_nat c))%nat by lia.
  rewrite nfb_nth by lia. reflexivity.
Qed.

Lemma znth_nonneg i l : Forall (fun x => 0 <= x) l -> 0 <= znth i l.
Proof.
  intros H. unfold znth. destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)) as [L|L].
  - rewrite Forall_forall in H. apply H. apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.

Lemma nfb_nonneg caps k : (forall j, 0 <= j < 48 -> 0 <= znth j caps) -> (k <= 48)%nat ->
  Forall (fun x => 0 <= x) (nf_build caps k).
Proof.
  intros Hc. induction k as [|k IH]; intros Hk; [constructor|]. cbn [nf_build].
  apply Forall_app. split; [apply IH; lia|]. constructor; [|constructor].
  pose proof (FC_pos (Z.of_nat k) ltac:(lia)) as HF. pose proof (Hc (Z.of_nat k) ltac:(lia)) as C.
  unfold nf_next. set (T := zsumZ _ _).
  assert (S0 : 0 <= T).
  { unfold T. apply zsumZ_nonneg. intros x _. cbv beta.
    destruct (jof x (FC x) =? Z.of_nat k); [apply znth_nonneg; apply IH; lia | lia]. }
  assert (0 <= (znth (Z.of_nat k) caps + COARSE + T + RED * Z.of_nat k) / FC (Z.of_nat k))
    by (apply Z.div_pos; unfold COARSE, RED; lia).
  lia.
Qed.

Lemma NF_nonneg caps c : (forall j, 0 <= j < 48 -> 0 <= znth j caps) -> 0 <= znth c (NF caps).
Proof. intros H. apply znth_nonneg. apply nfb_nonneg; [exact H | lia]. Qed.

Lemma NF_mono caps caps' : (forall k, 0 <= k < 49 -> znth k caps <= znth k caps') ->
  forall c, 0 <= c < 48 -> znth c (NF caps) <= znth c (NF caps').
Proof.
  intros Hc.
  assert (MAIN : forall n c, (Z.to_nat c < n)%nat -> 0 <= c < 48 -> znth c (NF caps) <= znth c (NF caps')).
  { induction n as [|n IH]; intros c Hn Hc48; [lia|].
    rewrite (NF_next caps c Hc48), (NF_next caps' c Hc48). unfold nf_next.
    pose proof (FC_pos c Hc48) as HF. pose proof (Hc c ltac:(lia)) as Hcc.
    assert (HS : zsumZ (fun c' => if jof c' (FC c') =? c then znth c' (nf_build caps (Z.to_nat c)) else 0) (zseq 0 c) <=
                 zsumZ (fun c' => if jof c' (FC c') =? c then znth c' (nf_build caps' (Z.to_nat c)) else 0) (zseq 0 c)).
    { apply zsumZ_le. intros x Hx. apply In_zseq in Hx. cbv beta.
      destruct (jof x (FC x) =? c); [|lia]. rewrite (NF_prefix caps c x), (NF_prefix caps' c x) by lia. apply IH; lia. }
    apply Z.add_le_mono_r. apply Z.div_le_mono; [lia|]. lia. }
  intros c Hc'. apply (MAIN (S (Z.to_nat c))); lia.
Qed.

Lemma GALL_mono caps caps' : (forall k, 0 <= k < 49 -> znth k caps <= znth k caps') -> GALL caps <= GALL caps'.
Proof.
  intros H. unfold GALL. pose proof (H 48 ltac:(lia)).
  assert (zsumZ (fun c => znth c (NF caps) + RED) (zseq 0 48) <= zsumZ (fun c => znth c (NF caps') + RED) (zseq 0 48)).
  { apply zsumZ_le. intros c Hc. apply In_zseq in Hc. cbv beta. pose proof (NF_mono caps caps' H c ltac:(lia)). lia. }
  lia.
Qed.

Lemma GMAP_mono caps caps' : (forall k, 0 <= k < 49 -> znth k caps <= znth k caps') -> GMAP caps <= GMAP caps'.
Proof.
  intros H. unfold GMAP. pose proof (H 48 ltac:(lia)).
  assert (zsumZ (fun c => if nestF c then 0 else znth c (NF caps) + RED) (zseq 0 48) <=
          zsumZ (fun c => if nestF c then 0 else znth c (NF caps') + RED) (zseq 0 48)).
  { apply zsumZ_le. intros c Hc. apply In_zseq in Hc. cbv beta. pose proof (NF_mono caps caps' H c ltac:(lia)).
    destruct (nestF c); lia. }
  lia.
Qed.

Definition pk_D : Z := 199987200.

Definition pk_row_next (acc : list (list Z)) (c : Z) : list Z :=
  map (fun k => ((if k =? c then pk_D else 0) +
    zsumZ (fun c' => if jof c' (FC c') =? c then znth k (nth (Z.to_nat c') acc []) else 0) (zseq 0 c)) / FC c)
    (zseq 0 49).

Fixpoint pk_rows (k : nat) : list (list Z) :=
  match k with
  | O => []
  | S k' => let acc := pk_rows k' in acc ++ [pk_row_next acc (Z.of_nat k')]
  end.

Definition pk_b_next (acc : list Z) (c : Z) : Z :=
  (pk_D * (COARSE + RED * c) + zsumZ (fun c' => if jof c' (FC c') =? c then znth c' acc else 0) (zseq 0 c)) / FC c + pk_D.

Fixpoint pk_bs (k : nat) : list Z :=
  match k with
  | O => []
  | S k' => let acc := pk_bs k' in acc ++ [pk_b_next acc (Z.of_nat k')]
  end.

Definition pk_A : list (list Z) := pk_rows 48.

Definition pk_B : list Z := pk_bs 48.

Definition pk_row (A : list (list Z)) (c : Z) : list Z := nth (Z.to_nat c) A [].

Definition pk_chk1 (A : list (list Z)) (c : Z) : bool :=
  forallb (fun k => (if k =? c then pk_D else 0) +
    zsumZ (fun c' => if jof c' (FC c') =? c then znth k (pk_row A c') else 0) (zseq 0 c) <=? FC c * znth k (pk_row A c))
    (zseq 0 49).

Definition pk_chk2 (B : list Z) (c : Z) : bool :=
  pk_D * (COARSE + RED * c) + zsumZ (fun c' => if jof c' (FC c') =? c then znth c' B else 0) (zseq 0 c) + pk_D * FC c <=?
  FC c * znth c B.

Definition pk_chk (A : list (list Z)) (B : list Z) : bool :=
  forallb (fun c => pk_chk1 A c && pk_chk2 B c) (zseq 0 48).

Lemma pk_cert : pk_chk pk_A pk_B = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pk_class caps : (forall k, 0 <= k < 49 -> 0 <= znth k caps) ->
  forall c, 0 <= c < 48 -> pk_D * znth c (NF caps) <= pk_lin (pk_row pk_A c) caps + znth c pk_B.
Proof.
  intros Hc.
  assert (MAIN : forall n c, (Z.to_nat c < n)%nat -> 0 <= c < 48 ->
    pk_D * znth c (NF caps) <= pk_lin (pk_row pk_A c) caps + znth c pk_B).
  { induction n as [|n IH]; intros c Hn Hc48; [lia|].
    pose proof pk_cert as CERT. unfold pk_chk in CERT. rewrite forallb_forall in CERT.
    specialize (CERT c (proj2 (In_zseq 0 48 c) ltac:(lia))). cbv beta in CERT.
    apply andb_true_iff in CERT as [C1 C2].
    unfold pk_chk1 in C1. rewrite forallb_forall in C1. unfold pk_chk2 in C2. apply Z.leb_le in C2.
    pose proof (FC_pos c Hc48) as HF.
    rewrite (NF_next caps c Hc48). unfold nf_next.
    rewrite (zsumZ_ext (fun c' => if jof c' (FC c') =? c then znth c' (nf_build caps (Z.to_nat c)) else 0)
      (fun c' => if jof c' (FC c') =? c then znth c' (NF caps) else 0)).
    2: { intros x Hx. apply In_zseq in Hx. cbv beta. rewrite (NF_prefix caps c x) by lia. reflexivity. }
    remember (zsumZ (fun c' => if jof c' (FC c') =? c then znth c' (NF caps) else 0) (zseq 0 c)) as SS eqn:ESS.
    assert (HS : pk_D * SS <= zsumZ (fun c' => if jof c' (FC c') =? c then pk_lin (pk_row pk_A c') caps else 0) (zseq 0 c)
                 + zsumZ (fun c' => if jof c' (FC c') =? c then znth c' pk_B else 0) (zseq 0 c)).
    { rewrite ESS, <- zsumZ_mul_l, <- zsumZ_add. apply zsumZ_le. intros x Hx. apply In_zseq in Hx. cbv beta.
      destruct (jof x (FC x) =? c); [|lia]. apply IH; lia. }
    assert (HL : pk_D * znth c caps + zsumZ (fun c' => if jof c' (FC c') =? c then pk_lin (pk_row pk_A c') caps else 0) (zseq 0 c)
                 <= FC c * pk_lin (pk_row pk_A c) caps).
    { pose proof (pk_lin_sum (fun c' => jof c' (FC c') =? c) (pk_row pk_A) caps (zseq 0 c)) as E1. cbv beta in E1. rewrite E1.
      pose proof (zsumZ_single (fun k => pk_D * znth k caps) c (zseq 0 49) (zseq_NoDup 0 49)
        (proj2 (In_zseq 0 49 c) ltac:(lia))) as E2.
      cbv beta in E2. rewrite <- E2.
      unfold pk_lin. rewrite <- zsumZ_mul_l, <- zsumZ_add. apply zsumZ_le. intros k Hk. cbv beta.
      pose proof (C1 k Hk) as Ck. cbv beta in Ck. apply Z.leb_le in Ck.
      apply In_zseq in Hk. pose proof (Hc k ltac:(lia)) as Ek. revert Ck. destruct (k =? c); intros Ck.
      - pose proof (Z.mul_le_mono_nonneg_r _ _ _ Ek Ck). lia.
      - pose proof (Z.mul_le_mono_nonneg_r _ _ _ Ek Ck). lia. }
    pose proof (Z.mul_div_le (znth c caps + COARSE + SS + RED * c) (FC c) ltac:(lia)) as HX.
    pose proof (Z.mul_le_mono_nonneg_l _ _ pk_D ltac:(unfold pk_D; lia) HX) as HX'.
    apply (Z.mul_le_mono_pos_l _ _ (FC c) ltac:(lia)).
    lia. }
  intros c Hc'. apply (MAIN (S (Z.to_nat c))); lia.
Qed.

Definition pk_chkW (skip : Z -> bool) (W : list Z) (W0 : Z) (A : list (list Z)) (B : list Z) : bool :=
  forallb (fun k => zsumZ (fun c => if negb (skip c) then znth k (pk_row A c) else 0) (zseq 0 48) +
    (if k =? 48 then pk_D else 0) <=? znth k W) (zseq 0 49) &&
  (zsumZ (fun c => if negb (skip c) then znth c B + pk_D * RED else 0) (zseq 0 48) <=? W0).

Lemma pk_linW skip W W0 caps : (forall k, 0 <= k < 49 -> 0 <= znth k caps) -> pk_chkW skip W W0 pk_A pk_B = true ->
  pk_D * (zsumZ (fun c => if skip c then 0 else znth c (NF caps) + RED) (zseq 0 48) + znth 48 caps) <=
  zsumZ (fun k => znth k W * znth k caps) (zseq 0 49) + W0.
Proof.
  intros Hc HW. unfold pk_chkW in HW. apply andb_true_iff in HW as [W1 W2]. rewrite forallb_forall in W1.
  apply Z.leb_le in W2.
  assert (H1 : pk_D * zsumZ (fun c => if skip c then 0 else znth c (NF caps) + RED) (zseq 0 48) <=
     zsumZ (fun c => if negb (skip c) then pk_lin (pk_row pk_A c) caps else 0) (zseq 0 48) +
     zsumZ (fun c => if negb (skip c) then znth c pk_B + pk_D * RED else 0) (zseq 0 48)).
  { rewrite <- zsumZ_mul_l, <- zsumZ_add. apply zsumZ_le. intros c Hc'. apply In_zseq in Hc'. cbv beta.
    destruct (skip c); cbn [negb]; [lia|]. pose proof (pk_class caps Hc c ltac:(lia)). lia. }
  pose proof (pk_lin_sum (fun c => negb (skip c)) (pk_row pk_A) caps (zseq 0 48)) as E1. cbv beta in E1.
  rewrite E1 in H1.
  pose proof (zsumZ_single (fun k => pk_D * znth k caps) 48 (zseq 0 49) (zseq_NoDup 0 49)
    (proj2 (In_zseq 0 49 48) ltac:(lia))) as E2. cbv beta in E2.
  assert (H2 : zsumZ (fun k => zsumZ (fun c => if negb (skip c) then znth k (pk_row pk_A c) else 0) (zseq 0 48) * znth k caps) (zseq 0 49)
     + zsumZ (fun k => if k =? 48 then pk_D * znth k caps else 0) (zseq 0 49) <= zsumZ (fun k => znth k W * znth k caps) (zseq 0 49)).
  { rewrite <- zsumZ_add. apply zsumZ_le. intros k Hk. cbv beta.
    pose proof (W1 k Hk) as Wk. cbv beta in Wk. apply Z.leb_le in Wk.
    apply In_zseq in Hk. pose proof (Hc k ltac:(lia)) as Ek. revert Wk. destruct (k =? 48); intros Wk.
    - pose proof (Z.mul_le_mono_nonneg_r _ _ _ Ek Wk). lia.
    - pose proof (Z.mul_le_mono_nonneg_r _ _ _ Ek Wk). lia. }
  rewrite E2 in H2. lia.
Qed.

Definition pk_BETA : list Z := [6881070;6659100;10321605;6665400;8265096;9839400;11479300;6678000;7393500;8625750;
  10350900;6444900;7365600;8593200;10311840;6444900;7365600;8593200;10311840;6444900;7365600;8593200;10311840;6640200;
  7588800;8853600;10624320;7030800;8035200;9374400;11249280;6249600;7142400;8332800;9999360;6249600;7142400;8332800;
  9999360;6249600;7142400;8332800;9999360;12499200;14284800;16665600;19998720;24998400;199987200].

Definition pk_G0 : Z := 2714345287885.

Definition pk_MU : list Z := [214830;207900;322245;214200;265608;316200;368900;6678000;7393500;8625750;10350900;
  6444900;7365600;8593200;10311840;6444900;7365600;8593200;10311840;6444900;7365600;8593200;10311840;6640200;7588800;
  8853600;10624320;7030800;8035200;9374400;11249280;6249600;7142400;8332800;9999360;6249600;7142400;8332800;9999360;
  6249600;7142400;8332800;9999360;12499200;14284800;16665600;19998720;24998400;199987200].

Definition pk_M0 : Z := 2508414008525.

Lemma pk_certG : pk_chkW (fun _ => false) pk_BETA pk_G0 pk_A pk_B = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pk_certM : pk_chkW nestF pk_MU pk_M0 pk_A pk_B = true.
Proof. vm_compute. reflexivity. Qed.

Theorem GALL_lin : forall caps, length caps = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k caps) ->
  pk_D * GALL caps <= zsumZ (fun k => znth k pk_BETA * znth k caps) (zseq 0 49) + pk_G0.
Proof. intros caps _ Hc. exact (pk_linW (fun _ => false) pk_BETA pk_G0 caps Hc pk_certG). Qed.

Theorem GMAP_lin : forall caps, length caps = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k caps) ->
  pk_D * GMAP caps <= zsumZ (fun k => znth k pk_MU * znth k caps) (zseq 0 49) + pk_M0.
Proof. intros caps _ Hc. exact (pk_linW nestF pk_MU pk_M0 caps Hc pk_certM). Qed.

Definition pk_gkeys (s : astate) (f : ameta -> bool) : list sptr :=
  filter (fun g => match MTX [] s g with Some (MUsed am) => f am | _ => false end) (keys s).

Definition pk_small (s : astate) (skip : Z -> bool) : list sptr :=
  flat_map (fun c => if skip c then [] else pk_gkeys s (gfull c) ++ pk_gkeys s (gred c)) (zseq 0 48).

Definition pk_ub48 (s : astate) : list (sptr * Z) := filter (fun b => band (snd b) =? 48) (user_blocks s).

Definition pk_tgt (s : astate) (skip : Z -> bool) : list (sptr * option Z) :=
  map (fun g => (g, None)) (pk_small s skip) ++ map (fun b => (fst b, Some (snd b))) (pk_ub48 s).

Definition pk_tdec (x y : sptr * option Z) : {x = y} + {x <> y}.
Proof.
  destruct x as [p o], y as [q o'].
  destruct (ac_sdec p q) as [<-|N]; [|right; congruence].
  destruct o as [n|], o' as [m|].
  - destruct (Z.eq_dec n m) as [<-|N]; [left; reflexivity|right; congruence].
  - right; congruence.
  - right; congruence.
  - left; reflexivity.
Defined.

Definition pk_RT (s : astate) (g : sptr) (x : sptr * option Z) : Prop :=
  exists ag, usedX [] s g ag /\
  match snd x with
  | None => fst x = g /\ 0 <= am_sc ag < 48
  | Some n => am_sc ag = 63 /\ find_frame_in (st_metas s) (fst x) = Some (g, 0) /\
      exists fr, ss_fr (nth_slot ag 0) = Some fr /\ n = fr_n fr
  end.

Definition pk_RR (s : astate) (k : nat) (x : sptr * option Z) : Prop :=
  exists g ag, usedX [] s g ag /\ prid (am_mem ag) = k /\ pk_RT s g x.

Lemma pk_RT_inj s g g' x : pk_RT s g x -> pk_RT s g' x -> g = g'.
Proof.
  intros (a & U & H) (a' & U' & H'). destruct x as [p [n|]]; cbn [fst snd] in H, H'.
  - destruct H as (_ & F & _), H' as (_ & F' & _). rewrite F in F'. congruence.
  - destruct H as (E & _), H' as (E' & _). congruence.
Qed.

Lemma pk_keys s g ag : WF s -> usedX [] s g ag -> In g (keys s).
Proof.
  intros HW U. apply (used_metas_usedX s g ag HW) in U. unfold used_metas in U.
  apply in_flat_map in U as ([p x] & Hin & Hx). unfold keys. apply in_map_iff. exists (p, x). split; [|exact Hin].
  cbn [fst]. destruct x as [a b| |am]; cbn in Hx; try contradiction. destruct Hx as [E|[]]. congruence.
Qed.

Lemma pk_tgt_ex s skip g ag : WF s -> PKS [] s -> usedX [] s g ag ->
  (0 <= am_sc ag < 48 -> skip (am_sc ag) = false) -> exists x, In x (pk_tgt s skip) /\ pk_RT s g x.
Proof.
  intros HW HP U Hsk. pose proof (inv_groups HW g ag U) as (_ & _ & _ & Gc & _).
  destruct (sc_range s HW g ag U) as [E63 | E48].
  - destruct Gc as [(_ & L0 & _ & _ & _ & [E0 | (fr & F & K & Big)]) | (C & _)]; [discriminate | | lia].
    exists (frame_ptr ag 0 fr, Some (fr_n fr)). split.
    + unfold pk_tgt. apply in_app_iff. right. apply in_map_iff. exists (frame_ptr ag 0 fr, fr_n fr). split; [reflexivity|].
      unfold pk_ub48. apply filter_In. split; [exact (ub_pair s HW g ag 0 fr U ltac:(lia) F K)|].
      cbn [snd]. unfold band. replace (MMAP_THRESHOLD <=? fr_n fr) with true by (symmetry; apply Z.leb_le; exact Big).
      reflexivity.
    + exists ag. split; [exact U|]. cbn [fst snd]. split; [exact E63|]. split.
      * exact (find_frame_in_spec [] None U0 s HW g ag 0 fr U ltac:(lia) F).
      * exists fr. split; [exact F | reflexivity].
  - pose proof HP as (_ & _ & P3 & _). pose proof (P3 g ag U ltac:(lia)) as Hl.
    exists (g, None). split.
    + unfold pk_tgt. apply in_app_iff. left. apply in_map_iff. exists g. split; [reflexivity|].
      unfold pk_small. apply in_flat_map. exists (am_sc ag). split; [apply In_zseq; lia|].
      rewrite (Hsk E48). apply in_app_iff. pose proof (pk_keys s g ag HW U) as Hk.
      unfold usedX in U.
      destruct (Z.eq_dec (am_last ag + 1) (FC (am_sc ag))) as [Eq|Ne]; [left|right];
        unfold pk_gkeys; apply filter_In; (split; [exact Hk|]); cbv beta; rewrite U; cbv iota.
      * unfold gfull. apply andb_true_iff. split; apply Z.eqb_eq; lia.
      * unfold gred. apply andb_true_iff. split; [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia].
    + exists ag. split; [exact U|]. cbn [fst snd]. split; [reflexivity | exact E48].
Qed.

Lemma pk_len_flat (f : Z -> list sptr) l : Z.of_nat (length (flat_map f l)) = zsumZ (fun c => Z.of_nat (length (f c))) l.
Proof. induction l as [|c l IH]; [reflexivity|]. cbn [flat_map]. rewrite length_app, Nat2Z.inj_add, IH. reflexivity. Qed.

Lemma pk_small_le s skip caps : PKC [] caps s ->
  Z.of_nat (length (pk_small s skip)) <= zsumZ (fun c => if skip c then 0 else znth c (NF caps) + RED) (zseq 0 48).
Proof.
  intros HC. unfold pk_small. rewrite pk_len_flat. apply zsumZ_le. intros c Hc. apply In_zseq in Hc. cbv beta.
  destruct (skip c); cbv iota; [cbn [length]; lia|].
  rewrite length_app, Nat2Z.inj_add. destruct (HC c ltac:(lia)) as [H1 H2].
  change (gcountX [] s (gfull c)) with (Z.of_nat (length (pk_gkeys s (gfull c)))) in H1.
  change (gcountX [] s (gred c)) with (Z.of_nat (length (pk_gkeys s (gred c)))) in H2.
  lia.
Qed.

Lemma pk_tgt_len s skip : Z.of_nat (length (pk_tgt s skip)) = Z.of_nat (length (pk_small s skip)) + bcount s 48.
Proof. unfold pk_tgt, bcount, pk_ub48. rewrite length_app, !length_map. lia. Qed.

Lemma pk_b48 s caps L : UPB s L -> (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps) -> bcount s 48 <= znth 48 caps.
Proof. intros (U1 & _) HB. pose proof (U1 48 ltac:(lia)). pose proof (HB 48 ltac:(lia)). lia. Qed.

Theorem nused_pack : forall s caps L, WF s -> SI s -> PKS [] s -> PKC [] caps s -> UPB s L ->
  length caps = 49%nat -> length L = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps) ->
  nused s <= GALL caps.
Proof.
  intros s caps L HW HS HP HC HU _ _ HB.
  assert (Hl : (length (map fst (used_metas s)) <= length (pk_tgt s (fun _ => false)))%nat).
  { apply (ac_count pk_tdec (pk_RT s)).
    - apply NoDup_used_metas_keys. exact (proj1 (inv_keys HW)).
    - intros g Hg. apply in_map_iff in Hg as ([g' ag] & E & Hin). cbn [fst] in E. subst g'.
      apply (used_metas_usedX s g ag HW) in Hin.
      exact (pk_tgt_ex s (fun _ => false) g ag HW HP Hin (fun _ => eq_refl)).
    - intros g g' x _ _ R1 R2. exact (pk_RT_inj s g g' x R1 R2). }
  rewrite length_map in Hl. pose proof (pk_tgt_len s (fun _ => false)) as E.
  pose proof (pk_small_le s (fun _ => false) caps HC) as Hs. cbv beta iota in Hs.
  pose proof (pk_b48 s caps L HU HB) as Hb.
  unfold nused, GALL. lia.
Qed.

Theorem mapped_pack : forall s caps L, WF s -> SI s -> PKS [] s -> PKC [] caps s -> UPB s L ->
  length caps = 49%nat -> length L = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps) ->
  map_count s <= GMAP caps.
Proof.
  intros s caps L HW HS HP HC HU _ _ HB. unfold map_count. rewrite mapc_count.
  match goal with |- Z.of_nat (length ?l) <= _ => assert (Hl : (length l <= length (pk_tgt s nestF))%nat) end.
  { apply (ac_count pk_tdec (pk_RR s)).
    - apply NoDup_filter. apply seq_NoDup.
    - intros k Hk. apply filter_In in Hk as [_ Hk]. cbv beta in Hk.
      destruct (nth_error (st_regions s) k) as [rg|] eqn:Hr; [|discriminate].
      apply andb_true_iff in Hk as [Lv Mp].
      assert (Kd : rg_kind rg = RkMap) by (unfold is_map in Mp; destruct (rg_kind rg); try discriminate; reflexivity).
      pose proof HS as (OM & _). destruct (OM k rg Hr Kd Lv) as (g & ag & U & Mpos & Pk).
      pose proof HP as (_ & _ & _ & P4).
      destruct (pk_tgt_ex s nestF g ag HW HP U (fun Hc => P4 g ag U (proj2 Hc) Mpos)) as (x & Hx & Rx).
      exists x. split; [exact Hx|]. exists g, ag. split; [exact U|]. split; [exact Pk | exact Rx].
    - intros k k' x _ _ (g & a & U & Pk & R1) (g' & a' & U' & Pk' & R2).
      pose proof (pk_RT_inj s g g' x R1 R2) as <-. rewrite (usedX_fun _ _ _ _ _ U U') in Pk. congruence. }
  pose proof (pk_tgt_len s nestF) as E. pose proof (pk_small_le s nestF caps HC) as Hs.
  pose proof (pk_b48 s caps L HU HB) as Hb. unfold GMAP. lia.
Qed.

Definition pk_w (x : sptr * option Z) : Z := match snd x with None => MMAX | Some n => MMAX + n end.

Lemma pk_wsum s skip : zsum pk_w (pk_tgt s skip) =
  MMAX * Z.of_nat (length (pk_small s skip)) + MMAX * bcount s 48 + zsum snd (pk_ub48 s).
Proof.
  unfold pk_tgt. rewrite zsum_app.
  assert (A1 : forall l : list sptr, zsum pk_w (map (fun g => (g, None)) l) = MMAX * Z.of_nat (length l)).
  { induction l as [|g l IH]; cbn [map length]; [rewrite zsum_nil; lia|]. rewrite zsum_cons, IH. unfold pk_w at 1. cbn [snd]. lia. }
  assert (A2 : forall l : list (sptr * Z), zsum pk_w (map (fun b => (fst b, Some (snd b))) l) = MMAX * Z.of_nat (length l) + zsum snd l).
  { induction l as [|b l IH]; cbn [map length]; [rewrite !zsum_nil; lia|]. rewrite !zsum_cons, IH. unfold pk_w at 1. cbn [snd]. lia. }
  rewrite A1, A2. unfold bcount, pk_ub48. lia.
Qed.

Lemma pk_zsum_filter {A} (f : A -> Z) (p : A -> bool) l : (forall x, In x l -> 0 <= f x) -> zsum f (filter p l) <= zsum f l.
Proof.
  induction l as [|x l IH]; intros H; [cbn; lia|]. cbn [filter].
  assert (zsum f (filter p l) <= zsum f l) by (apply IH; intros y Hy; apply H; right; exact Hy).
  pose proof (H x (or_introl eq_refl)). destruct (p x); rewrite !zsum_cons; lia.
Qed.

Theorem map_bytes_pack : forall s caps L, WF s -> SI s -> GS s -> PKS [] s -> PKC [] caps s -> UPB s L ->
  length caps = 49%nat -> length L = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps) ->
  map_bytes s <= MMAX * GMAP caps + ubytes s.
Proof.
  intros s caps L HW HS HG HP HC HU _ _ HB. unfold map_bytes. rewrite rsum_idx.
  match goal with |- zsum ?c ?l <= _ => assert (Hl : zsum c l <= zsum pk_w (pk_tgt s nestF)) end.
  { apply (ac_wsum pk_tdec (pk_RR s)).
    - apply seq_NoDup.
    - intros x Hx. unfold pk_tgt in Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_map_iff in Hx as (y & <- & Hy);
        unfold pk_w; cbn [snd]; rewrite MM; [lia|].
      unfold pk_ub48 in Hy. apply filter_In in Hy as [Hy _]. pose proof (ub_nonneg s HW y Hy). lia.
    - intros k _. cbv beta.
      destruct (nth_error (st_regions s) k) as [rg|] eqn:Hr; cbv beta iota; [|left; lia].
      unfold f_mapb. destruct (rg_live rg && is_map rg) eqn:E; cbv beta iota; [right|left; lia].
      apply andb_true_iff in E as [Lv Mp].
      assert (Kd : rg_kind rg = RkMap) by (unfold is_map in Mp; destruct (rg_kind rg); try discriminate; reflexivity).
      pose proof HS as (OM & _). destruct (OM k rg Hr Kd Lv) as (g & ag & U & Mpos & Pk).
      pose proof (inv_groups HW g ag U) as (_ & _ & _ & _ & Gmp & _).
      destruct (Gmp Mpos) as (r & rg' & Em & Hr' & _ & _ & Len & _).
      rewrite Em in Pk. cbn in Pk. subst r. unfold region_of in Hr'. rewrite Hr in Hr'. injection Hr' as <-.
      rewrite Len.
      pose proof HP as (_ & _ & _ & P4).
      destruct (pk_tgt_ex s nestF g ag HW HP U (fun Hc => P4 g ag U (proj2 Hc) Mpos)) as (x & Hx & Rx).
      exists x. split; [exact Hx|]. split; [exists g, ag; split; [exact U|]; split; [rewrite Em; reflexivity | exact Rx]|].
      destruct Rx as (a & Ua & Hm). rewrite (usedX_fun _ _ _ _ _ Ua U) in Hm.
      destruct (HG g ag U Mpos) as [G48 G63].
      unfold pk_w. destruct x as [p [n|]]; cbn [fst snd] in Hm |- *.
      + destruct Hm as (E63 & _ & fr & F & ->). pose proof (G63 E63 fr F). rewrite MM. unfold PGSZ in *. lia.
      + destruct Hm as (_ & C). apply G48. lia.
    - intros k k' x _ _ (g & a & U & Pk & R1) (g' & a' & U' & Pk' & R2).
      pose proof (pk_RT_inj s g g' x R1 R2) as <-. rewrite (usedX_fun _ _ _ _ _ U U') in Pk. congruence. }
  rewrite pk_wsum in Hl.
  assert (Hsub : zsum snd (pk_ub48 s) <= ubytes s).
  { change (ubytes s) with (zsum snd (user_blocks s)). unfold pk_ub48. apply pk_zsum_filter.
    intros b Hb. exact (ub_nonneg s HW b Hb). }
  pose proof (pk_small_le s nestF caps HC) as Hs. pose proof (pk_b48 s caps L HU HB) as Hb.
  unfold GMAP. rewrite MM in *. lia.
Qed.

Lemma pack_room4 : forall A b n, WF A -> res_ok_pack A b -> room_pack b n -> ROOM4 A n.
Proof.
  intros A b n HW (HII & HSI & HGS & HNL & HNR & (MB1 & MB2) & HPK & HPC & HUP & Hub & HlL & HlC & Hbd & Hby & Hh)
    (Hn & Hcap & C1 & C2 & C3 & C4).
  pose proof (mapped_pack A (pb_cap b) (pb_live b) HW HSI HPK HPC HUP HlC HlL Hbd) as T4.
  pose proof (map_bytes_pack A (pb_cap b) (pb_live b) HW HSI HGS HPK HPC HUP HlC HlL Hbd) as T7.
  pose proof (nareas_hand A HII) as NA1.
  destruct (shift_small A (GALL (pb_cap b)) HII Hh C4) as [SH1 SH2].
  pose proof HII as (_ & Hsh & _ & _ & Hrt & _).
  assert (HD : hand A / METAS_PER_AREA <= GALL (pb_cap b) / METAS_PER_AREA).
  { apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | exact Hh]. }
  assert (BK : brk_bytes A / PGSZ <= nareas A + 1).
  { apply Z.div_le_upper_bound; [unfold PGSZ; lia|]. unfold PGSZ in *. lia. }
  pose proof (page_round_ge (n + IB + UNIT)) as PR.
  assert (MX0 : 0 < MMAX) by (unfold MMAX; reflexivity).
  assert (AR : area A <= AREA2 (GALL (pb_cap b))) by (unfold area, AREA2; unfold PGSZ in *; lia).
  assert (RQ1 : Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (area A) <= RQ2 (GALL (pb_cap b)) n).
  { unfold RQ2. lia. }
  assert (SC : slot_cap (RQ2 (GALL (pb_cap b)) n) <= slot_cap (Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (area A))).
  { apply slot_cap_anti. lia. }
  unfold ROOM4. split; [|split; [|split]].
  - unfold LIVE_UB. rewrite Hrt. unfold LIVE2, AREA2, NA2 in *. unfold PGSZ, MMAX in *. lia.
  - unfold SLOT_UB. unfold SLOTS2, NA2 in C2. lia.
  - unfold RQ2 in C3. unfold PGSZ in *. lia.
  - unfold RQ2 in C3. unfold PGSZ in *. lia.
Qed.

Lemma CAPOK2_mono H M bytes n H' M' bytes' n' :
  H' <= H -> M' <= M -> bytes' <= bytes -> n' <= n -> CAPOK2 H M bytes n -> CAPOK2 H' M' bytes' n'.
Proof.
  intros HH HM HB HN (C1 & C2 & C3 & C4).
  assert (D : H' / METAS_PER_AREA <= H / METAS_PER_AREA) by (apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | exact HH]).
  pose proof (page_round_mono (n' + IB + UNIT) (n + IB + UNIT) ltac:(lia)) as PM.
  assert (MX0 : 0 < MMAX) by (unfold MMAX; reflexivity).
  assert (R : RQ2 H' n' <= RQ2 H n) by (unfold RQ2, AREA2; unfold PGSZ in *; lia).
  assert (R0 : 0 < RQ2 H' n') by (unfold RQ2; lia).
  pose proof (slot_cap_anti (RQ2 H' n') (RQ2 H n) ltac:(lia)) as SC.
  unfold CAPOK2. split; [|split; [|split]].
  - unfold LIVE2, AREA2, NA2 in *. unfold PGSZ in *. rewrite MM in *. lia.
  - unfold SLOTS2, NA2 in *. lia.
  - lia.
  - lia.
Qed.

Lemma room_pack_of b n BMAX NMAX :
  CAPOK2 (GALL (pb_cap b)) (GMAP (pb_cap b)) BMAX NMAX -> 0 <= n <= NMAX -> pb_bytes b + n <= BMAX ->
  znth (band n) (pb_live b) + 1 <= znth (band n) (pb_cap b) -> room_pack b n.
Proof.
  intros HC Hn HB Hl. unfold room_pack. split; [lia|]. split; [exact Hl|].
  apply (CAPOK2_mono (GALL (pb_cap b)) (GMAP (pb_cap b)) BMAX NMAX); [lia | lia | exact HB | lia | exact HC].
Qed.

Lemma room_pack_n b n : room_pack b n -> 0 <= n < 2 ^ 62 /\ size_overflows n = false.
Proof.
  intros (Hn0 & _ & _ & _ & C3 & _). pose proof (page_round_ge (n + IB + UNIT)) as PG. unfold PGSZ in C3.
  assert (R : page_round (n + IB + UNIT) <= RQ2 (GALL (pb_cap b)) n) by (unfold RQ2; lia).
  split; [unfold MG_REQ, IB, UNIT in *; lia|]. unfold size_overflows. apply Z.leb_gt. unfold MG_REQ, IB, UNIT in *. lia.
Qed.

Lemma room_pack_req b n : room_pack b n -> page_round (n + IB + UNIT) + PGSZ <= MG_REQ.
Proof.
  intros (_ & _ & _ & _ & C3 & _).
  assert (R : page_round (n + IB + UNIT) <= RQ2 (GALL (pb_cap b)) n) by (unfold RQ2; lia). lia.
Qed.

Lemma res_ok_pack_init caps : length caps = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k caps) ->
  res_ok_pack init_state (PB (repeat 0 49) 0 caps).
Proof.
  intros Hlen Hc.
  assert (NU : forall X g am, ~ usedX X init_state g am).
  { intros X g am H. unfold usedX, MTX, MT in H. destruct (memb g X); cbn in H; discriminate. }
  assert (Z0 : forall k, znth k (repeat 0 49) = 0).
  { intros k. unfold znth. generalize (Z.to_nat k). generalize 49%nat.
    induction n as [|n IH]; intros [|m]; cbn; auto. }
  assert (NN : forall c, 0 <= znth c (NF caps)) by (intros c; apply NF_nonneg; intros j Hj; apply Hc; lia).
  assert (GC0 : forall f, gcountX [] init_state f = 0) by (intros f; reflexivity).
  assert (B0 : forall k, bcount init_state k = 0) by (intros k; reflexivity).
  assert (UC0 : forall c, upc init_state c = 0) by (intros c; reflexivity).
  assert (UB0 : ubytes init_state = 0) by reflexivity.
  assert (HD0 : hand init_state = 0) by reflexivity.
  assert (GA : 0 <= GALL caps).
  { unfold GALL. pose proof (Hc 48 ltac:(lia)).
    assert (0 <= zsumZ (fun c => znth c (NF caps) + RED) (zseq 0 48))
      by (apply zsumZ_nonneg; intros c _; cbv beta; pose proof (NN c); unfold RED; lia).
    lia. }
  unfold res_ok_pack. cbn [pb_live pb_bytes pb_cap].
  refine (conj II_init (conj SI_init (conj GS_init (conj NL_init (conj noraw_init (conj MB_init _)))))).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hlen (conj _ (conj (Z.le_refl 0) _)))))))).
  - split; [|split; [|split]]; intros *; intros H; exfalso; exact (NU _ _ _ H).
  - intros c Hc48. rewrite !GC0. split; [apply NN | unfold RED; lia].
  - split; intros k Hk; rewrite ?B0, ?UC0, ?Z0; try unfold COARSE; lia.
  - lia.
  - reflexivity.
  - intros k Hk. rewrite Z0. pose proof (Hc k Hk). lia.
  - lia.
Qed.

Lemma res_ok_pack_raise A b caps' : res_ok_pack A b -> length caps' = 49%nat ->
  (forall k, 0 <= k < 49 -> znth k (pb_cap b) <= znth k caps') -> res_ok_pack A (PB (pb_live b) (pb_bytes b) caps').
Proof.
  intros (HII & HSI & HGS & HNL & HNR & HMB & HPK & HPC & HUP & Hub & HlL & HlC & Hbd & Hby & Hh) Hl Hc.
  unfold res_ok_pack. cbn [pb_live pb_bytes pb_cap].
  refine (conj HII (conj HSI (conj HGS (conj HNL (conj HNR (conj HMB (conj HPK _))))))).
  refine (conj _ (conj HUP (conj Hub (conj HlL (conj Hl (conj _ (conj Hby _))))))).
  - intros c Hc48. destruct (HPC c Hc48) as [P1 P2]. pose proof (NF_mono _ _ Hc c Hc48). split; lia.
  - intros k Hk. pose proof (Hbd k Hk). pose proof (Hc k Hk). lia.
  - pose proof (GALL_mono _ _ Hc). lia.
Qed.

Lemma band_range n : 0 <= n -> 0 <= band n < 49.
Proof.
  intros Hn. unfold band. destruct (Z.leb_spec MMAP_THRESHOLD n); [lia|].
  pose proof (size_to_class_range n ltac:(lia)). lia.
Qed.

Lemma lv_add_length L k d : length (lv_add L k d) = length L.
Proof. unfold lv_add. apply length_zset. Qed.

Lemma znth_lv_add L k d j : 0 <= k < Z.of_nat (length L) -> 0 <= j ->
  znth j (lv_add L k d) = if j =? k then znth k L + d else znth j L.
Proof.
  intros Hk Hj. unfold lv_add. rewrite znth_zset by lia.
  destruct (Z.eqb_spec j k) as [->|N]; cbn [andb].
  - replace (k <? Z.of_nat (length L)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - reflexivity.
Qed.

Lemma lv_add_bounds L caps k d : length L = 49%nat -> 0 <= k < 49 ->
  (forall j, 0 <= j < 49 -> 0 <= znth j L <= znth j caps) -> 0 <= znth k L + d <= znth k caps ->
  length (lv_add L k d) = 49%nat /\ (forall j, 0 <= j < 49 -> 0 <= znth j (lv_add L k d) <= znth j caps).
Proof.
  intros Hl Hk HB Hd. split; [rewrite lv_add_length; exact Hl|]. intros j Hj.
  rewrite znth_lv_add by (try rewrite Hl; lia).
  destruct (Z.eqb_spec j k) as [->|N]; cbv iota; [exact Hd | apply HB; exact Hj].
Qed.
