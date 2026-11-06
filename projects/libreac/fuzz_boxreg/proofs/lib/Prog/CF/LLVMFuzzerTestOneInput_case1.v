From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg BoxregRd BoxregStep BoxregUpd
  bcmp_c reac_boxreg_find_c lowest_free_base_c reac_boxreg_add_c reac_boxreg_add_inv range_free_c lowest_free_c
  reac_boxreg_find bcmp reac_boxreg_add lowest_free_base memset memcpy lowest_free range_free.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import SRCF.
Import ListNotations.
Open Scope Z_scope.

Definition c1_okb (k f : Z) : bool := Z.even k && (2 <=? k) && (k <=? 40) && (k <=? f).

Lemma c1_okb_spec : forall k f, c1_okb k f = true <-> add_width_ok k f.
Proof.
  intros k f. unfold c1_okb, add_width_ok. rewrite !andb_true_iff, !Z.leb_le. tauto.
Qed.

Definition c1_okx (k f : Z) : Z :=
  Z.land (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (v_slt (Z_to_bv 64 f) (Z_to_bv 64 k))) 18446744073709551615)))
    (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (v_sltiu (Z_to_bv 64 (k + -2)) 39))
       (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 k)) 1)) 1))))).

Lemma c1_okb_val : forall k f, 0 <= k < 256 -> 1 <= f <= 40 -> c1_okx k f = Z.b2z (c1_okb k f).
Proof.
  intros k f Hk Hf.
  assert (H : forallb (fun k => forallb (fun f => c1_okx k f =? Z.b2z (c1_okb k f)) (map Z.of_nat (seq 1 40)))
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  assert (Ik : In k (map Z.of_nat (seq 0 256))).
  { replace k with (Z.of_nat (Z.to_nat k)) by lia. apply in_map. apply in_seq. lia. }
  specialize (H k Ik). rewrite forallb_forall in H. apply Z.eqb_eq. apply H.
  replace f with (Z.of_nat (Z.to_nat f)) by lia. apply in_map. apply in_seq. lia.
Qed.

Definition c1_orx (z nb : Z) : Z :=
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 z)) 63))) (bv_unsigned (Z_to_bv 64 nb)).

Lemma c1_or_val : forall z nb, -1 <= z <= 38 -> 0 <= nb <= 4 ->
  Z_to_bv 64 (c1_orx z nb) = Z_to_bv 64 (if z <? 0 then -1 else nb).
Proof.
  intros z nb Hz Hn. apply bv_eq.
  assert (H : forallb (fun z => forallb (fun nb => bv_unsigned (Z_to_bv 64 (c1_orx z nb)) =?
                                                  bv_unsigned (Z_to_bv 64 (if z <? 0 then -1 else nb)))
                                        (map Z.of_nat (seq 0 5)))
                (map (fun x => Z.of_nat x - 1) (seq 0 40)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  assert (Iz : In z (map (fun x => Z.of_nat x - 1) (seq 0 40))).
  { replace z with (Z.of_nat (Z.to_nat (z + 1)) - 1) by lia. apply (in_map (fun x => Z.of_nat x - 1)).
    apply in_seq. lia. }
  specialize (H z Iz). rewrite forallb_forall in H. apply Z.eqb_eq. apply H.
  replace nb with (Z.of_nat (Z.to_nat nb)) by lia. apply in_map. apply in_seq. lia.
Qed.

Definition c1_wantP (bs M : list byte) (k lf want : Z) : Prop :=
  (~ (add_width_ok k (bx_fabric bs) /\ M <> zero6) /\ want = -1) \/
  (add_width_ok k (bx_fabric bs) /\ M <> zero6 /\ add_held bs M want) \/
  (add_width_ok k (bx_fabric bs) /\ M <> zero6 /\ add_none_held bs M /\ add_unbound bs k want) \/
  (add_width_ok k (bx_fabric bs) /\ M <> zero6 /\ add_none_held bs M /\ add_none_unbound bs k /\
   (5 <= bx_n bs \/ lowest_free_res bs k (bx_fabric bs) (-1)) /\ want = -1) \/
  (add_width_ok k (bx_fabric bs) /\ M <> zero6 /\ add_none_held bs M /\ add_none_unbound bs k /\
   bx_n bs < 5 /\ want = bx_n bs /\ 0 <= lf /\ lowest_free_res bs k (bx_fabric bs) lf).

Lemma c1_inv_n : forall bs, boxreg_inv bs -> 0 <= bx_n bs <= 5.
Proof. intros bs ((_ & H & _) & _). exact H. Qed.

Lemma c1_inv_len : forall bs, boxreg_inv bs -> length bs = 288%nat.
Proof. intros bs ((H & _) & _). exact H. Qed.

Lemma c1_inv_fab : forall bs, boxreg_inv bs -> 1 <= bx_fabric bs <= 40.
Proof. intros bs ((_ & _ & H & _) & _). exact H. Qed.

Lemma c1_lf_uniq : forall bs k z1 z2,
  lowest_free_res bs k (bx_fabric bs) z1 -> lowest_free bs k z2 -> z1 = z2.
Proof.
  intros bs k z1 z2 H1 H2. unfold lowest_free_res, range_free_ok in H1. unfold lowest_free, slice_meets in H2.
  destruct H1 as [(E1 & N1) | (R1 & (R1' & F1) & L1)]; destruct H2 as [(E2 & N2) | (R2 & R2' & F2 & L2)].
  - lia.
  - exfalso. apply (N1 z2); [lia|]. split; [lia|]. intros i Hi Hm. apply F2. exists i. split; assumption.
  - exfalso. destruct (N2 z1 ltac:(lia) ltac:(lia)) as (i & Hi & Hm). exact (F1 i Hi Hm).
  - destruct (Z.lt_trichotomy z1 z2) as [Lt | [Eq | Gt]]; [exfalso | exact Eq | exfalso].
    + destruct (L2 z1 ltac:(lia)) as (i & Hi & Hm). exact (F1 i Hi Hm).
    + apply (L1 z2 ltac:(lia)). split; [lia|]. intros i Hi Hm. apply F2. exists i. split; assumption.
Qed.

Lemma c1_held_uniq : forall bs M i j, add_held bs M i -> add_held bs M j -> i = j.
Proof.
  intros bs M i j (Hi & Mi & Ni) (Hj & Mj & Nj).
  destruct (Z.lt_trichotomy i j) as [L | [E | G]]; [exfalso | exact E | exfalso].
  - exact (Nj i ltac:(lia) Mi).
  - exact (Ni j ltac:(lia) Mj).
Qed.

Lemma c1_unb_uniq : forall bs k i j, add_unbound bs k i -> add_unbound bs k j -> i = j.
Proof.
  intros bs k i j (Hi & Mi & Ki & Ni) (Hj & Mj & Kj & Nj).
  destruct (Z.lt_trichotomy i j) as [L | [E | G]]; [exfalso | exact E | exfalso].
  - exact (Nj i ltac:(lia) (conj Mi Ki)).
  - exact (Ni j ltac:(lia) (conj Mj Kj)).
Qed.

Lemma c1_new_row : forall bs M b k, length bs = 288%nat -> 0 <= bx_n bs <= 4 -> length M = 6%nat ->
  -2^31 <= b < 2^31 -> -2^31 <= k < 2^31 ->
  bx_n (add_bytes bs M b k) = bx_n bs + 1 /\ bx_fabric (add_bytes bs M b k) = bx_fabric bs /\
  bx_base (add_bytes bs M b k) (bx_n bs) = b /\ bx_pinned (add_bytes bs M b k) (bx_n bs) = 0 /\
  bx_nch (add_bytes bs M b k) (bx_n bs) = k /\ bx_mac (add_bytes bs M b k) (bx_n bs) = M /\
  (forall i, 0 <= i < bx_n bs ->
     bx_base (add_bytes bs M b k) i = bx_base bs i /\ bx_nch (add_bytes bs M b k) i = bx_nch bs i /\
     bx_pinned (add_bytes bs M b k) i = bx_pinned bs i /\ bx_mac (add_bytes bs M b k) i = bx_mac bs i /\
     bx_name (add_bytes bs M b k) i = bx_name bs i).
Proof.
  intros bs M b k HL Hn HM Hb Hk.
  assert (HR : length (add_row M b k) = 56%nat) by (apply add_row_length; exact HM).
  change (add_bytes bs M b k) with (new_row_bytes bs (add_row M b k)).
  pose proof (new_row_new bs (add_row M b k) HL Hn HR) as Hnew.
  pose proof (new_row_old bs (add_row M b k) HL Hn HR) as Hold.
  split; [exact (new_row_n bs (add_row M b k) HL Hn HR)|].
  split; [exact (new_row_fabric bs (add_row M b k) HL Hn HR)|].
  split; [apply rd4_le4; [lia|]; rewrite Hnew by lia; apply add_row_base; exact HM|].
  split; [apply rd4_le4; [lia|]; rewrite Hnew by lia; apply add_row_pin; exact HM|].
  split; [apply rd4_le4; [lia|]; rewrite Hnew by lia; apply add_row_nch; exact HM|].
  split.
  - unfold bx_mac. replace (56 * bx_n bs) with (56 * bx_n bs + 0) by lia. rewrite Hnew by lia.
    apply add_row_mac. exact HM.
  - intros i Hi. unfold bx_base, bx_nch, bx_pinned, bx_mac, bx_name, rd4.
    rewrite !Hold by lia.
    replace (56 * i) with (56 * i + 0) by lia. rewrite Hold by lia.
    repeat split; reflexivity.
Qed.

Lemma c1_lf_bound : forall bs k b, boxreg_inv bs -> add_width_ok k (bx_fabric bs) -> 0 <= b ->
  lowest_free bs k b -> b <= 38.
Proof.
  intros bs k b HI (_ & Hk & _) Hb H. pose proof (c1_inv_fab bs HI).
  destruct H as [(E & _) | (_ & H & _)]; lia.
Qed.

Ltac c1_contra :=
  exfalso; first
  [ match goal with
    | A : ~ add_width_ok _ _ \/ _ = zero6, Wo : add_width_ok _ _, Wz : _ <> zero6 |- _ =>
        destruct A as [A|A]; [exact (A Wo) | exact (Wz A)]
    end
  | match goal with
    | W : ~ (add_width_ok _ _ /\ _ <> zero6), Ao : add_width_ok _ _, Az : _ <> zero6 |- _ => exact (W (conj Ao Az))
    end
  | match goal with
    | N : add_none_held ?bs ?M, H : add_held ?bs ?M ?i |- _ =>
        let Hi := fresh in let Mi := fresh in destruct H as (Hi & Mi & _); exact (N i Hi Mi)
    end
  | match goal with
    | N : add_none_unbound ?bs ?k, H : add_unbound ?bs ?k ?i |- _ =>
        let Hi := fresh in let Mi := fresh in let Ki := fresh in
        destruct H as (Hi & Mi & Ki & _); exact (N i Hi (conj Mi Ki))
    end
  | lia ].

Lemma c1_add_want : forall bs M k lf want z bs',
  boxreg_inv bs -> length M = 6%nat -> c1_wantP bs M k lf want -> add_out bs M k z bs' ->
  z = want /\ (want = bx_n bs -> bx_base bs' want = lf /\ bx_pinned bs' want = 0).
Proof.
  intros bs M k lf want z bs' HI HM HW HA.
  pose proof (c1_inv_n bs HI) as Hn. pose proof (c1_inv_len bs HI) as HL.
  destruct HW as [(W1 & ->) | [(Wo & Wz & Wh) | [(Wo & Wz & Wn & Wu) |
                  [(Wo & Wz & Wn & Wnu & Wd & ->) | (Wo & Wz & Wn & Wnu & Wlt & -> & Wl & Wr)]]]];
  destruct HA as [(A1 & -> & ->) | [(Ao & Az & Ah & ->) | [(Ao & Az & An & Au & ->) |
                  [(Ao & Az & An & Anu & Ad & -> & ->) | (Ao & Az & An & Anu & Alt & -> & b & Hb & Hlf & ->)]]]];
  try solve [ c1_contra ].
  - split; [reflexivity | intros E; lia].
  - split; [exact (c1_held_uniq _ _ _ _ Ah Wh) | intros E; destruct Wh as (Hw & _); lia].
  - split; [exact (c1_unb_uniq _ _ _ _ Au Wu) | intros E; destruct Wu as (Hw & _); lia].
  - split; [reflexivity | intros E; lia].
  - exfalso. destruct Wd as [Wd | Wd]; [lia|]. pose proof (c1_lf_uniq _ _ _ _ Wd Hlf). lia.
  - exfalso. destruct Ad as [Ad | Ad]; [lia|]. pose proof (c1_lf_uniq _ _ _ _ Wr Ad). lia.
  - split; [reflexivity|]. intros _. pose proof (c1_lf_uniq _ _ _ _ Wr Hlf) as <-.
    pose proof (c1_lf_bound bs k lf HI Ao Wl Hlf) as Hb38. destruct Ao as (_ & Hk & _).
    destruct (c1_new_row bs M lf k HL ltac:(lia) HM ltac:(lia) ltac:(lia)) as (_ & _ & E1 & E2 & _).
    split; assumption.
Qed.

Lemma c1_add_pos : forall bs M k z bs', boxreg_inv bs -> length M = 6%nat -> add_out bs M k z bs' -> 0 <= z ->
  M <> zero6 /\ add_width_ok k (bx_fabric bs) /\ bx_fabric bs' = bx_fabric bs /\ bx_n bs' <= 5 /\
  add_held bs' M z /\ ((add_held bs M z /\ bs' = bs) \/ (add_none_held bs M /\ bx_nch bs' z = k)).
Proof.
  intros bs M k z bs' HI HM HA Hz.
  pose proof (c1_inv_n bs HI) as Hn. pose proof (c1_inv_len bs HI) as HL.
  destruct HA as [(A1 & E & _) | [(Ao & Az & Ah & ->) | [(Ao & Az & An & Au & ->) |
                  [(Ao & Az & An & Anu & Ad & E & _) | (Ao & Az & An & Anu & Alt & -> & b & Hb & Hlf & ->)]]]];
    [ lia | | | lia | ].
  - split; [exact Az|]. split; [exact Ao|]. split; [reflexivity|]. split; [lia|].
    split; [exact Ah|]. left. split; [exact Ah | reflexivity].
  - destruct Au as (Hz' & Mz & Kz & Nz).
    replace (upd_bytes bs (Z.to_nat (56 * z)) M) with (bind_bytes bs M z) by reflexivity.
    pose proof (bind_other bs M z HL ltac:(lia) HM) as Ho.
    pose proof (bind_mac bs M z HL ltac:(lia) HM) as Hm.
    assert (En : bx_n (bind_bytes bs M z) = bx_n bs) by (unfold bx_n, rd4; rewrite Ho by lia; reflexivity).
    split; [exact Az|]. split; [exact Ao|].
    split; [unfold bx_fabric, rd4; rewrite Ho by lia; reflexivity|].
    split; [lia|].
    split.
    + split; [lia|]. split; [exact Hm|]. intros j Hj. unfold bx_mac. rewrite Ho by lia. apply An. lia.
    + right. split; [exact An|]. unfold bx_nch, rd4. rewrite Ho by lia. exact Kz.
  - destruct Ao as (Ke & Hk & Hkf).
    assert (Hb38 : b <= 38) by (apply (c1_lf_bound bs k b HI (conj Ke (conj Hk Hkf)) Hb Hlf)).
    destruct (c1_new_row bs M b k HL ltac:(lia) HM ltac:(lia) ltac:(lia)) as (N1 & N2 & _ & _ & N5 & N6 & Old).
    split; [exact Az|]. split; [split; [exact Ke | split; assumption]|].
    split; [exact N2|]. split; [lia|].
    split.
    + split; [lia|]. split; [exact N6|]. intros j Hj. destruct (Old j Hj) as (_ & _ & _ & O4 & _).
      rewrite O4. apply An. exact Hj.
    + right. split; [exact An | exact N5].
Qed.

Lemma c1_find_held : forall bs M i z, M <> zero6 -> add_held bs M i -> find_result bs M z -> z = i.
Proof.
  intros bs M i z HZ HH HF. unfold find_result, first_mac in HF.
  destruct HF as [(E & _) | [(_ & HF) | (_ & -> & N)]].
  - contradiction.
  - exact (c1_held_uniq bs M z i HF HH).
  - exfalso. destruct HH as (Hi & Mi & _). exact (N i Hi Mi).
Qed.

Lemma c1_add_again : forall bs M k z z2 bs2, M <> zero6 -> add_width_ok k (bx_fabric bs) -> add_held bs M z ->
  add_out bs M k z2 bs2 -> z2 = z /\ bs2 = bs.
Proof.
  intros bs M k z z2 bs2 HZ HO HH HA.
  destruct HA as [(A1 & _ & _) | [(_ & _ & Ah & ->) | [(_ & _ & An & _) | [(_ & _ & An & _) | (_ & _ & An & _)]]]].
  - exfalso. destruct A1 as [A1|A1]; [exact (A1 HO) | exact (HZ A1)].
  - split; [exact (c1_held_uniq _ _ _ _ Ah HH) | reflexivity].
  - exfalso. destruct HH as (Hi & Mi & _). exact (An z Hi Mi).
  - exfalso. destruct HH as (Hi & Mi & _). exact (An z Hi Mi).
  - exfalso. destruct HH as (Hi & Mi & _). exact (An z Hi Mi).
Qed.

Lemma c1_known : forall bs M k known z bs', find_result bs M known -> 0 <= known -> add_width_ok k (bx_fabric bs) ->
  add_out bs M k z bs' -> z = known.
Proof.
  intros bs M k known z bs' HF Hk HO HA. unfold find_result in HF.
  destruct HF as [(EM & E) | [(HZ & HF) | (_ & E & _)]]; [lia | | lia].
  destruct (c1_add_again bs M k known z bs' HZ HO HF HA) as [E _]. exact E.
Qed.

Lemma c1_add_zero : forall bs k z bs', add_out bs zero6 k z bs' -> z = -1.
Proof.
  intros bs k z bs' H.
  destruct H as [(_ & E & _) | [(_ & A & _) | [(_ & A & _) | [(_ & A & _) | (_ & A & _)]]]];
    [exact E | exfalso; apply A; reflexivity ..].
Qed.

Lemma c1_find_none : forall bs M z, find_result bs M z -> z < 0 -> M <> zero6 -> add_none_held bs M.
Proof.
  intros bs M z HF Hz HZ. unfold find_result, first_mac in HF.
  destruct HF as [(E & _) | [(_ & (Hi & _)) | (_ & _ & N)]]; [contradiction | lia | exact N].
Qed.

Lemma c1_kept : forall bs M k z bs', boxreg_inv bs -> length M = 6%nat -> add_out bs M k z bs' -> llvm_kept bs bs' (-1).
Proof.
  intros bs M k z bs' HI HM HA. pose proof (c1_inv_n bs HI) as Hn. pose proof (c1_inv_len bs HI) as HL.
  unfold llvm_kept.
  destruct HA as [(_ & _ & ->) | [(_ & _ & _ & ->) | [(_ & _ & _ & Au & ->) | [(_ & _ & _ & _ & _ & _ & ->) |
                  (Ao & _ & _ & _ & Alt & -> & b & Hb & Hlf & ->)]]]].
  - intros j Hj. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; right; reflexivity.
  - intros j Hj. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; right; reflexivity.
  - destruct Au as (Hz & Mz & _ & _).
    replace (upd_bytes bs (Z.to_nat (56 * z)) M) with (bind_bytes bs M z) by reflexivity.
    pose proof (bind_other bs M z HL ltac:(lia) HM) as Ho.
    intros j Hj.
    assert (D : forall o w, 6 <= o -> 0 <= w -> o + w <= 56 ->
                  bsub (bind_bytes bs M z) (56 * j + o) w = bsub bs (56 * j + o) w).
    { intros o w H1 H2 H3. apply Ho; [lia | lia | lia |]. destruct (Z.lt_ge_cases j z); [left | right]; lia. }
    unfold bx_base, bx_nch, bx_pinned, bx_name, rd4. rewrite !D by lia.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [| right; reflexivity].
    destruct (Z.eq_dec j z) as [-> | Hne]; [left; exact Mz | right].
    unfold bx_mac. apply Ho; [lia | lia | lia |]. destruct (Z.lt_ge_cases j z); [left | right]; lia.
  - intros j Hj. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; right; reflexivity.
  - destruct Ao as (Ke & Hk & Hkf).
    assert (Hb38 : b <= 38) by (apply (c1_lf_bound bs k b HI (conj Ke (conj Hk Hkf)) Hb Hlf)).
    destruct (c1_new_row bs M b k HL ltac:(lia) HM ltac:(lia) ltac:(lia)) as (_ & _ & _ & _ & _ & _ & Old).
    intros j Hj. destruct (Old j Hj) as (O1 & O2 & O3 & O4 & O5). rewrite O1, O2, O3, O4, O5.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; right; reflexivity.
Qed.

Lemma c1_memcmp : forall n (l r : list byte) v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  -256 < v < 256 /\ (v = 0 <-> l = r).
Proof.
  induction n as [|n IH]; intros [|a l] [|b r] v Hl Hr H; cbn [length memcmp_model] in *; try discriminate.
  - injection H as <-. split; [lia|]. split; intros _; reflexivity.
  - injection Hl as Hl. injection Hr as Hr.
    pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    change (bv_modulus 8) with 256 in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + assert (a = b) by (apply bv_eq; exact E). subst b.
      destruct (IH l r v Hl Hr H) as [Hv Hi]. split; [exact Hv|].
      split; [intros V; f_equal; apply Hi; exact V | intros Hc; injection Hc as Hc; apply Hi; exact Hc].
    + injection H as <-. split; [lia|].
      split; [intros; lia | intros Hc; injection Hc as Hc _; subst; lia].
Qed.

Lemma c1_cb_at : forall m A pre n l post, rw_cells rsegs m A (pre ++ CB n l :: post) ->
  bytes_at rsegs m (A + Z.of_nat (cells_size pre)) l.
Proof.
  intros m A pre n l post [[Hwf Hb] _].
  apply cells_wf_app in Hwf as [Hw1 _].
  rewrite cells_bytes_app in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by exact Hw1.
  cbn [cells_bytes cbytes] in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb as [Hb _]. exact Hb.
Qed.

Lemma c1_fr_merge : forall m A j0 f w1 w2 bs M jm2 q c,
  rw_cells rsegs m A [CB 8 j0; C8 f; C8 w1; C8 w2; CB 288 bs; CB 6 M; CB 2 jm2; C8 q; C8 c] ->
  rw_cells rsegs m A [CB 8 j0; C8 f; CB 16 (le8 w1 ++ le8 w2 ++ []); CB 288 bs; CB 8 (M ++ jm2 ++ []); C8 q; C8 c].
Proof.
  intros m A j0 f w1 w2 bs M jm2 q c H.
  pose proof (rw_cells_merge rsegs m A [CB 8 j0; C8 f] [C8 w1; C8 w2]
                [CB 288 bs; CB 6 M; CB 2 jm2; C8 q; C8 c] H) as H1.
  exact (rw_cells_merge rsegs m A [CB 8 j0; C8 f; CB 16 (le8 w1 ++ le8 w2 ++ []); CB 288 bs] [CB 6 M; CB 2 jm2]
           [C8 q; C8 c] H1).
Qed.

Lemma c1_zero : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10392 zero6.
Proof.
  intros m MI. apply ro_bytes_at; [ exact MI | lia | cbn; lia | ].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma c1_mi_stack : forall m m' a b, mem_inv rsegs m -> munch [(a, b)] m m' -> LF_RES_TOP <= a -> mem_inv rsegs m'.
Proof.
  intros m m' a b MI MU Ha x v Hx.
  pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
  destruct (Z_le_dec a (bv_unsigned x)) as [H1|H1]; [destruct (Z_lt_dec (bv_unsigned x) b) as [H2|H2]|].
  - unfold ro_addr. destruct (find_segment rsegs (bv_unsigned x) 1) as [seg|] eqn:E; [|reflexivity].
    exfalso. pose proof (lf_find_top (bv_unsigned x) 1 seg E). lia.
  - apply (MI x v). rewrite <- (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]].
  - apply (MI x v). rewrite <- (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]].
Qed.

Lemma c1_tr1 : forall m0 m m' lo X r a b cs,
  munch [(lo, X + 344); (r, r + 288)] m0 m -> wmono rsegs m0 m -> rw_cells rsegs m X cs -> wr_at rsegs m r 288 ->
  munch [(a, b)] m m' -> wmono rsegs m m' -> lo <= a -> b <= X ->
  munch [(lo, X + 344); (r, r + 288)] m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' X cs /\ wr_at rsegs m' r 288.
Proof.
  intros m0 m m' lo X r a b cs MU WM FR WR MUc WMc Ha Hb.
  pose proof (rw_cells_bound rsegs m X cs FR) as RB.
  split; [|split; [exact (wmono_trans rsegs _ _ _ WM WMc)|split]].
  - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
    intros x Hx. cbn [outside] in *. split; [lia | exact I].
  - eapply rw_cells_transport; [exact FR | exact MUc | exact WMc |]. cbn [disjoint_from]. split; [lia | exact I].
  - eapply wr_at_transport; [exact WR | exact WMc].
Qed.

Lemma c1_tr2 : forall m0 m m' lo X r cs,
  munch [(lo, X + 344); (r, r + 288)] m0 m -> wmono rsegs m0 m -> rw_cells rsegs m X cs -> wr_at rsegs m r 288 ->
  munch [(lo, X); (r, r + 288)] m m' -> wmono rsegs m m' -> lo <= X -> r + 288 <= lo ->
  munch [(lo, X + 344); (r, r + 288)] m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' X cs /\ wr_at rsegs m' r 288.
Proof.
  intros m0 m m' lo X r cs MU WM FR WR MUc WMc Ha Hb.
  pose proof (rw_cells_bound rsegs m X cs FR) as RB.
  split; [|split; [exact (wmono_trans rsegs _ _ _ WM WMc)|split]].
  - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
    intros x Hx. cbn [outside] in *. split; [lia | split; [lia | exact I]].
  - eapply rw_cells_transport; [exact FR | exact MUc | exact WMc |]. cbn [disjoint_from].
    split; [lia | split; [lia | exact I]].
  - eapply wr_at_transport; [exact WR | exact WMc].
Qed.

Lemma c1_tr0 : forall m0 m m' lo X r cs bs,
  munch [(lo, X + 344); (r, r + 288)] m0 m -> wmono rsegs m0 m -> rw_cells rsegs m X cs -> wr_at rsegs m r 288 ->
  stk rsegs m lo X -> bytes_at rsegs m r bs ->
  munch [] m m' -> wmono rsegs m m' ->
  munch [(lo, X + 344); (r, r + 288)] m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' X cs /\ wr_at rsegs m' r 288 /\
  stk rsegs m' lo X /\ bytes_at rsegs m' r bs.
Proof.
  intros m0 m m' lo X r cs bs MU WM FR WR ST HB MUc WMc.
  split; [exact (munch_trans _ _ _ _ MU (munch_weaken [] _ _ _ (fun x H => I) MUc))|].
  split; [exact (wmono_trans rsegs _ _ _ WM WMc)|].
  split; [eapply rw_cells_transport; [exact FR | exact MUc | exact WMc | exact I]|].
  split; [eapply wr_at_transport; [exact WR | exact WMc]|].
  split; [eapply stk_transport_disjoint; [exact ST | exact MUc | exact WMc | exact I]|].
  eapply bytes_at_transport; [exact HB | exact MUc | exact I].
Qed.

Lemma c1_bv : forall m A bs, bytes_at rsegs m A bs -> 0 <= A < 2 ^ 64 -> bytes_at rsegs m (bv_unsigned (Z_to_bv 64 A)) bs.
Proof. intros m A bs H HA. rewrite unsigned_lit by lia. exact H. Qed.

Definition c1_sh (bs M : list byte) (v i h : Z) : Prop :=
  (h = -1 /\ (v = 0 \/ forall j, 0 <= j < i -> bx_mac bs j <> M)) \/
  (v <> 0 /\ 0 <= h < i /\ bx_mac bs h = M /\ forall j, 0 <= j < h -> bx_mac bs j <> M).

Definition c1_su (bs : list byte) (k i u : Z) : Prop :=
  (u = -1 /\ forall j, 0 <= j < i -> ~ (bx_mac bs j = zero6 /\ bx_nch bs j = k)) \/
  (0 <= u < i /\ bx_mac bs u = zero6 /\ bx_nch bs u = k /\
   forall j, 0 <= j < u -> ~ (bx_mac bs j = zero6 /\ bx_nch bs j = k)).

Lemma c1_sh_keep : forall bs M v i h, c1_sh bs M v i h -> 0 <= h -> c1_sh bs M v (i + 1) h.
Proof.
  intros bs M v i h [(E & _) | (Hv & Hh & Hm & Hn)] H0; [lia|].
  right. split; [exact Hv|]. split; [lia|]. split; [exact Hm | exact Hn].
Qed.

Lemma c1_sh_v0 : forall bs M v i, v = 0 -> c1_sh bs M v i (-1).
Proof. intros bs M v i E. left. split; [reflexivity | left; exact E]. Qed.

Lemma c1_sh_hit : forall bs M v i, c1_sh bs M v i (-1) -> v <> 0 -> 0 <= i -> bx_mac bs i = M ->
  c1_sh bs M v (i + 1) i.
Proof.
  intros bs M v i [(_ & [E | N]) | (_ & H & _)] Hv Hi Hm; [contradiction | | lia].
  right. split; [exact Hv|]. split; [lia|]. split; [exact Hm | exact N].
Qed.

Lemma c1_sh_miss : forall bs M v i, c1_sh bs M v i (-1) -> 0 <= i -> bx_mac bs i <> M ->
  c1_sh bs M v (i + 1) (-1).
Proof.
  intros bs M v i [(_ & [E | N]) | (_ & H & _)] Hi Hm; [left; split; [reflexivity | left; exact E] | | lia].
  left. split; [reflexivity|]. right. intros j Hj.
  destruct (Z.eq_dec j i) as [-> | Hne]; [exact Hm | apply N; lia].
Qed.

Lemma c1_su_keep : forall bs k i u, c1_su bs k i u -> 0 <= u -> c1_su bs k (i + 1) u.
Proof.
  intros bs k i u [(E & _) | (H1 & H2 & H3 & H4)] H0; [lia|].
  right. split; [lia|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

Lemma c1_su_hit : forall bs k i, c1_su bs k i (-1) -> 0 <= i -> bx_mac bs i = zero6 -> bx_nch bs i = k ->
  c1_su bs k (i + 1) i.
Proof.
  intros bs k i [(_ & N) | (H & _)] Hi Hm Hn; [|lia].
  right. split; [lia|]. split; [exact Hm|]. split; [exact Hn | exact N].
Qed.

Lemma c1_su_miss : forall bs k i, c1_su bs k i (-1) -> 0 <= i -> ~ (bx_mac bs i = zero6 /\ bx_nch bs i = k) ->
  c1_su bs k (i + 1) (-1).
Proof.
  intros bs k i [(_ & N) | (H & _)] Hi Hm; [|lia]. left. split; [reflexivity|].
  intros j Hj. destruct (Z.eq_dec j i) as [-> | Hne]; [exact Hm | apply N; lia].
Qed.

Lemma c1_mac_len : forall bs i, length bs = 288%nat -> 0 <= i <= 4 -> length (bx_mac bs i) = 6%nat.
Proof. intros bs i HL Hi. unfold bx_mac. rewrite bsub_length by (rewrite ?HL; lia). reflexivity. Qed.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Hypothesis BCMP_C : bcmp_contract.
Hypothesis FIND_C : reac_boxreg_find_contract.
Hypothesis ADD_C : reac_boxreg_add_contract.
Hypothesis LOWF_C : lowest_free_contract.

Lemma c1_bcmp : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (pa pb : Z)
    (ls rs : list byte),
  a0 = Z_to_bv 64 pa -> a1 = Z_to_bv 64 pb -> a2 = Z_to_bv 64 6 ->
  bytes_at rsegs m pa ls -> bytes_at rsegs m pb rs -> length ls = 6%nat -> length rs = 6%nat -> mem_inv rsegs m ->
  (forall (v : Z) (m' : word -> option byte) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     -256 < v < 256 -> (v = 0 <-> ls = rs) -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs Q (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 BCMP) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q pa pb ls rs E0 E1 E2 HA HB LA LB MI K. subst a0 a1 a2.
  pose proof (bytes_at_bound rsegs m pa ls HA) as RA. pose proof (bytes_at_bound rsegs m pb rs HB) as RB.
  rewrite LA in RA. rewrite LB in RB.
  destruct (memcmp_model_total ls rs 6 ltac:(lia) ltac:(lia)) as [v Hv].
  destruct (c1_memcmp 6 ls rs v LA LB Hv) as [Rv Iv].
  pose proof BCMP_C as BC. unfold bcmp_contract in BC.
  eapply evt_cut.
  - eapply BC with (ls := ls) (rs := rs) (v := v).
    + rewrite unsigned_lit by lia. exact HA.
    + rewrite unsigned_lit by lia. exact HB.
    + exact Hv.
    + exact MI.
  - intros ms' PO. unfold memcmp_post in PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m'
                    & E & MU & WM & MI' & _ & _).
    subst ms'. apply K; assumption.
Qed.

Lemma c1_find : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (lo r p : Z)
    (bs M : list byte),
  a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 p ->
  bytes_at rsegs m r bs -> length bs = 288%nat -> boxreg_B1 bs -> bytes_at rsegs m p M -> length M = 6%nat ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
  (r + 288 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= r) -> (p + 6 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= p) ->
  mem_inv rsegs m ->
  (forall (z : Z) (m' : word -> option byte) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     find_result bs M z -> munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
     mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) -> bytes_at rsegs m' r bs -> bytes_at rsegs m' p M ->
     evt rsegs Q (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 z) x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_BOXREG_FIND) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q lo r p bs M E0 E1 HB HL H1 HM HLM ST LO D1 D2 MI K.
  pose proof FIND_C as FC. unfold reac_boxreg_find_contract, REAC_BOXREG_FIND_FRAME in FC.
  eapply evt_cut.
  - eapply FC; eassumption.
  - intros ms' (x5 & x6 & x7 & res & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m'
                & E & MU & WM & MI' & ST' & HB' & HM' & z & Ez & HF).
    subst ms' res. apply K; assumption.
Qed.

Lemma c1_add : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (lo r p k : Z)
    (bs M : list byte),
  a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 p -> a2 = Z_to_bv 64 k -> -2^31 <= k < 2^31 -> r mod 8 = 0 ->
  bytes_at rsegs m r bs -> wr_at rsegs m r 288 -> boxreg_inv bs ->
  bytes_at rsegs m p M -> length M = 6%nat -> (p + 6 <= r \/ r + 288 <= p) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp ->
  (bv_unsigned sp <= r \/ r + 288 <= lo) -> (bv_unsigned sp <= p \/ p + 6 <= lo) -> mem_inv rsegs m ->
  (forall (z : Z) (bs' : list byte) (m' : word -> option byte)
          (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     add_out bs M k z bs' -> bytes_at rsegs m' r bs' ->
     munch [(lo, bv_unsigned sp); (r, r + 288)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     stk rsegs m' lo (bv_unsigned sp) ->
     evt rsegs Q (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 z) x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_BOXREG_ADD) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q lo r p k bs M E0 E1 E2 Hk Hr8 HB WR HI HM HLM D0 ST LO D1 D2 MI K.
  pose proof ADD_C as AC. unfold reac_boxreg_add_contract, ADD_K in AC.
  eapply evt_cut.
  - eapply AC; eassumption.
  - intros ms' (x5 & x6 & x7 & a0' & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & z & bs'
                & E & Ea & HA & HB' & MU & WM & MI' & ST').
    subst ms' a0'. eapply K; eassumption.
Qed.

Lemma c1_lowf : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (lo t k f : Z)
    (bs : list byte),
  a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 f -> 1 <= k <= 40 -> 1 <= f <= 40 ->
  bytes_at rsegs m t bs -> length bs = 288%nat -> boxreg_B1 bs -> boxreg_B2 bs -> boxreg_B3 bs ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp ->
  (t + 288 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= t) ->
  (forall (z : Z) (m' : word -> option byte) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     lowest_free_res bs k f z -> munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
     stk rsegs m' lo (bv_unsigned sp) ->
     evt rsegs Q (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 z) x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 LOWEST_FREE) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q lo t k f bs E0 E1 E2 Hk Hf HB HL H1 H2 H3 ST LO D K.
  pose proof LOWF_C as LC. unfold lowest_free_contract, LOWEST_FREE_FRAME in LC.
  eapply evt_cut.
  - eapply LC; eassumption.
  - intros ms' (x5 & x6 & x7 & res & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m'
                & E & MU & WM & ST' & z & Ez & HF).
    subst ms' res. apply K; assumption.
Qed.

Lemma c1_add_range : forall bs M k z bs', boxreg_inv bs -> add_out bs M k z bs' -> -1 <= z <= 4.
Proof.
  intros bs M k z bs' HI HA. pose proof (c1_inv_n bs HI) as Hn.
  destruct HA as [(_ & E & _) | [(_ & _ & (Hi & _) & _) | [(_ & _ & _ & (Hi & _) & _) |
                  [(_ & _ & _ & _ & _ & E & _) | (_ & _ & _ & _ & Hl & E & _)]]]]; lia.
Qed.

Lemma c1_add_fab : forall bs M k z bs', boxreg_inv bs -> length M = 6%nat -> add_out bs M k z bs' ->
  bx_fabric bs' = bx_fabric bs.
Proof.
  intros bs M k z bs' HI HM HA. pose proof (c1_inv_n bs HI) as Hn.
  destruct (Z_lt_le_dec z 0) as [Hz | Hz].
  - destruct HA as [(_ & _ & ->) | [(_ & _ & (Hi & _) & _) | [(_ & _ & _ & (Hi & _) & _) |
                    [(_ & _ & _ & _ & _ & _ & ->) | (_ & _ & _ & _ & Hl & E & _)]]]]; try reflexivity; lia.
  - exact (proj1 (proj2 (proj2 (c1_add_pos bs M k z bs' HI HM HA Hz)))).
Qed.

Ltac c1_fin m j1 jm q c bs' :=
  apply evt_done; unfold llvm_case_Q; do 22 eexists; exists m, j1, jm, q, c, bs'; split; [reflexivity|].

Lemma c1_end :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab e q0 q c lf nb want : Z) (j0 bs M jm2 bs' : list byte),
  s0 = Z_to_bv 64 r -> s5 = Z_to_bv 64 want -> s7 = Z_to_bv 64 want ->
  -1 <= want < 5 -> 0 <= nb <= 5 ->
  rw_cells rsegs m (bv_unsigned sp)
    [CB 8 j0; C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 nb); CB 288 bs; CB 6 M; CB 2 jm2;
     C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  bytes_at rsegs m r bs' -> wr_at rsegs m r 288 -> boxreg_inv bs' -> bx_fabric bs' = fab ->
  llvm_kept bs bs' (-1) -> (want = nb -> bx_base bs' want = lf /\ bx_pinned bs' want = 0) ->
  munch [(lo, bv_unsigned sp + 344); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> 0 <= c -> q + c = e -> 0 <= r -> r + 288 <= bv_unsigned sp ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab e q0 j0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x131b4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m lo r fab e q0 q c lf nb want j0 bs M jm2 bs' E0 E5 E7 Hw Hnb FR HB WR HI HF HK HBP MU WM MI
    Hq0 Hc Hqe Hr0 Hr.
  subst s0 s5 s7.
  pose proof (c1_inv_len bs' HI) as HL.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  step. c1_if.
  step. step. step.
  destruct (Z.eq_dec want nb) as [Ew | Nw].
  - subst want. destruct (HBP eq_refl) as [Eb Ep].
    step. c1_if.
    step. step. step. rewrite bx_off56 by lia. step.
    pose proof (rd4_bytes_at m r bs' (56 * nb + 8) HB ltac:(lia) ltac:(rewrite HL; lia)) as R1.
    change (rd4 bs' (56 * nb + 8)) with (bx_base bs' nb) in R1. rewrite Eb in R1. apply bx_ov4 in R1.
    pose proof (rd4_bytes_at m r bs' (56 * nb + 20) HB ltac:(lia) ltac:(rewrite HL; lia)) as R2.
    change (rd4 bs' (56 * nb + 20)) with (bx_pinned bs' nb) in R2. rewrite Ep in R2. apply bx_ov4 in R2.
    pose proof (rd4_range bs' (56 * nb + 8)) as Rb. change (rd4 bs' (56 * nb + 8)) with (bx_base bs' nb) in Rb.
    rewrite Eb in Rb.
    step. rewrite ?bx_sx32 by lia.
    step. step. c1_if.
    step. rewrite ?bx_sx32 by lia. step. c1_if.
    step.
    c1_fin m (le8 (Z_to_bv 64 lf) ++ le8 (Z_to_bv 64 nb) ++ []) (M ++ jm2 ++ []) q c bs'.
    refine (conj MU (conj WM (conj MI (conj (c1_fr_merge _ _ _ _ _ _ _ _ _ _ _ FR)
              (conj Hq0 (conj Hc (conj Hqe (conj HB (conj WR (conj HI (conj HF HK))))))))))).
  - step. c1_if.
    c1_fin m (le8 (Z_to_bv 64 lf) ++ le8 (Z_to_bv 64 nb) ++ []) (M ++ jm2 ++ []) q c bs'.
    refine (conj MU (conj WM (conj MI (conj (c1_fr_merge _ _ _ _ _ _ _ _ _ _ _ FR)
              (conj Hq0 (conj Hc (conj Hqe (conj HB (conj WR (conj HI (conj HF HK))))))))))).
Qed.

Lemma c1_chk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab e q0 q c lf k known z : Z) (j0 bs M jm2 bs' : list byte),
  s0 = Z_to_bv 64 r -> s2 = Z_to_bv 64 k -> s5 = Z_to_bv 64 z -> s6 = Z_to_bv 64 known -> s7 = Z_to_bv 64 z ->
  0 <= k < 256 -> find_result bs M known -> -1 <= known < 5 -> add_out bs M k z bs' ->
  (z = bx_n bs -> bx_base bs' z = lf /\ bx_pinned bs' z = 0) ->
  boxreg_inv bs -> bx_fabric bs = fab -> length M = 6%nat ->
  rw_cells rsegs m (bv_unsigned sp)
    [CB 8 j0; C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 6 M; CB 2 jm2;
     C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  bytes_at rsegs m r bs' -> wr_at rsegs m r 288 -> r mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> 0 <= r -> r + 288 <= lo ->
  munch [(lo, bv_unsigned sp + 344); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> 0 <= c -> q + c = e ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab e q0 j0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13148) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m lo r fab e q0 q c lf k known z j0 bs M jm2 bs' E0 E2 E5 E6 E7 Hk HFk Hkn HA HBP HI HF HM FR HB WR Hr8
    ST LO Hr0 Hr MU WM MI Hq0 Hc Hqe.
  subst s0 s2 s5 s6 s7.
  pose proof (c1_inv_len bs HI) as HL. pose proof (c1_inv_n bs HI) as Hn.
  pose proof (reac_boxreg_add_keeps_inv_holds bs M bs' k z HI HM HA) as HI'.
  pose proof (c1_inv_len bs' HI') as HL'. pose proof (c1_inv_n bs' HI') as Hn'.
  pose proof (c1_add_range bs M k z bs' HI HA) as Hz.
  pose proof (c1_add_fab bs M k z bs' HI HM HA) as HF'.
  pose proof (c1_kept bs M k z bs' HI HM HA) as HK.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (c1_cb_at m (bv_unsigned sp) [CB 8 j0; C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (bx_n bs))]
                288 bs [CB 6 M; CB 2 jm2; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] FR) as _.
  step.
  destruct (Z_lt_le_dec z 0) as [Hz0 | Hz0].
  - c1_if.
    eapply (c1_end _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 m lo r fab e q0 q c lf
              (bx_n bs) z j0 bs M jm2 bs');
      first [ reflexivity | eassumption | lia | rewrite HF'; exact HF | idtac ].
  - c1_if.
    destruct (c1_add_pos bs M k z bs' HI HM HA Hz0) as (HZ & Ao & _ & Hn5 & Hh' & Hcase).
    pose proof (rd4_bytes_at m r bs' 280 HB ltac:(lia) ltac:(rewrite HL'; lia)) as R280.
    change (rd4 bs' 280) with (bx_n bs') in R280. apply bx_ov4 in R280.
    step. rewrite ?bx_sx32 by lia.
    pose proof Hh' as (Hzn & Hmz & _).
    step. c1_if.
    step. step. step. rewrite bx_off56 by lia. step.
    step. step. step.
    pose proof (c1_cb_at m (bv_unsigned sp)
                  [CB 8 j0; C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs]
                  6 M [CB 2 jm2; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] FR) as HMb.
    change (Z.of_nat (cells_size [CB 8 j0; C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (bx_n bs));
                                  CB 288 bs])) with 320 in HMb.
    eapply c1_bcmp with (pa := r + 56 * z) (pb := bv_unsigned sp + 320) (ls := bx_mac bs' z) (rs := M);
      [ reflexivity | reflexivity | reflexivity
      | exact (bytes_at_bsub m r bs' (56 * z) 6 HB ltac:(lia) ltac:(lia) ltac:(rewrite HL'; lia))
      | exact HMb | unfold bx_mac; rewrite bsub_length by (rewrite ?HL'; lia); reflexivity | exact HM | exact MI | ].
    intros v1 m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hv1 Iv1 MU1 WM1 MI1.
    c1_retpc.
    destruct (c1_tr0 m0 m m1 lo (bv_unsigned sp) r _ bs' MU WM FR WR ST HB MU1 WM1) as (MU' & WM' & FR' & WR' & ST' & HB').
    clear MU WM FR WR ST HB MU1 WM1 HMb MI R280.
    assert (V0 : v1 = 0) by (apply Iv1; exact Hmz).
    step. c1_if.
    step. step. step.
    pose proof (c1_cb_at m1 (bv_unsigned sp)
                  [CB 8 j0; C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs]
                  6 M [CB 2 jm2; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] FR') as HMb.
    change (Z.of_nat (cells_size [CB 8 j0; C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (bx_n bs));
                                  CB 288 bs])) with 320 in HMb.
    eapply c1_find with (lo := lo) (r := r) (p := bv_unsigned sp + 320) (bs := bs') (M := M);
      [ reflexivity | reflexivity | exact HB' | exact HL' | unfold boxreg_B1; lia | exact HMb | exact HM | exact ST'
      | lia | lia | lia | exact MI1 | ].
    intros z2 m2 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HF2 MU2 WM2 MI2 ST2 HB2 HM2.
    c1_retpc.
    pose proof (c1_find_held bs' M z z2 HZ Hh' HF2) as Ez2. subst z2.
    destruct (c1_tr1 m0 m1 m2 lo (bv_unsigned sp) r _ _ _ MU' WM' FR' WR' MU2 WM2 ltac:(lia) ltac:(lia))
      as (MU'' & WM'' & FR'' & WR'').
    clear MU' WM' FR' WR' MU2 WM2 MI1 ST' HB' HMb.
    step. c1_if.
    step. step. step. step.
    eapply c1_add with (lo := lo) (r := r) (p := bv_unsigned sp + 320) (k := k) (bs := bs') (M := M);
      [ reflexivity | reflexivity | reflexivity | lia | exact Hr8 | exact HB2 | exact WR'' | exact HI' | exact HM2
      | exact HM | lia | exact ST2 | lia | lia | lia | exact MI2 | ].
    intros z3 bs3 m3 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 HA3 HB3 MU3 WM3 MI3 ST3.
    c1_retpc.
    destruct (c1_add_again bs' M k z z3 bs3 HZ ltac:(rewrite HF'; exact Ao) Hh' HA3) as [Ez3 Eb3].
    subst z3 bs3.
    destruct (c1_tr2 m0 m2 m3 lo (bv_unsigned sp) r _ MU'' WM'' FR'' WR'' MU3 WM3 ltac:(lia) ltac:(lia))
      as (MU4 & WM4 & FR4 & WR4).
    clear MU'' WM'' FR'' WR'' MU3 WM3 MI2 ST2 HB2 HM2.
    step. c1_if.
    step.
    destruct (Z_lt_le_dec known 0) as [Kn | Kp].
    + c1_if.
      assert (Hnch : bx_nch bs' z = k).
      { destruct Hcase as [(Hh & _) | (_ & Hk')]; [exfalso | exact Hk'].
        pose proof (c1_find_none bs M known HFk Kn HZ) as NH. destruct Hh as (Hi & Mi & _). exact (NH z Hi Mi). }
      pose proof (rd4_bytes_at m3 r bs' (56 * z + 12) HB3 ltac:(lia) ltac:(rewrite HL'; lia)) as R12.
      change (rd4 bs' (56 * z + 12)) with (bx_nch bs' z) in R12. rewrite Hnch in R12. apply bx_ov4 in R12.
      step. step. step. rewrite bx_off56 by lia. step.
      step. rewrite ?bx_sx32 by lia.
      step. c1_if.
      eapply (c1_end _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 m3 lo r fab e q0 q c lf
                (bx_n bs) z j0 bs M jm2 bs');
        first [ reflexivity | eassumption | lia | rewrite HF'; exact HF | idtac ].
    + c1_if.
      eapply (c1_end _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 m3 lo r fab e q0 q c lf
                (bx_n bs) z j0 bs M jm2 bs');
        first [ reflexivity | eassumption | lia | rewrite HF'; exact HF | idtac ].
Qed.

Lemma c1_find_range : forall bs M z, find_result bs M z -> 0 <= bx_n bs <= 5 -> -1 <= z < 5.
Proof.
  intros bs M z HF Hn. unfold find_result, first_mac in HF.
  destruct HF as [(_ & ->) | [(_ & (Hi & _)) | (_ & -> & _)]]; lia.
Qed.

Lemma c1_main :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab e q0 q c lf k v want : Z) (j0 bs M jm2 : list byte),
  s0 = Z_to_bv 64 r -> s2 = Z_to_bv 64 k -> s3 = Z_to_bv 64 (Z.b2z (c1_okb k fab)) -> s4 = Z_to_bv 64 v ->
  s7 = Z_to_bv 64 want ->
  0 <= k < 256 -> -256 < v < 256 -> (v = 0 <-> M = zero6) -> c1_wantP bs M k lf want ->
  boxreg_inv bs -> bx_fabric bs = fab -> length M = 6%nat ->
  rw_cells rsegs m (bv_unsigned sp)
    [CB 8 j0; C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 6 M; CB 2 jm2;
     C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  bytes_at rsegs m r bs -> wr_at rsegs m r 288 -> r mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> 0 <= r -> r + 288 <= lo ->
  bv_unsigned sp + 448 <= 2 ^ 63 ->
  munch [(lo, bv_unsigned sp + 344); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> 0 <= c -> q + c = e ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab e q0 j0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13104) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m lo r fab e q0 q c lf k v want j0 bs M jm2 E0 E2 E3 E4 E7 Hk Hv Iv HW HI HF HM FR HB WR Hr8
    ST LO Hr0 Hr HX MU WM MI Hq0 Hc Hqe.
  subst s0 s2 s3 s4 s7.
  pose proof (c1_inv_len bs HI) as HL. pose proof (c1_inv_n bs HI) as Hn.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (c1_cb_at m (bv_unsigned sp)
                [CB 8 j0; C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs]
                6 M [CB 2 jm2; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] FR) as HMb.
  change (Z.of_nat (cells_size [CB 8 j0; C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs]))
    with 320 in HMb.
  step. step. step.
  eapply c1_find with (lo := lo) (r := r) (p := bv_unsigned sp + 320) (bs := bs) (M := M);
    [ reflexivity | reflexivity | exact HB | exact HL | unfold boxreg_B1; lia | exact HMb | exact HM | exact ST
    | lia | lia | lia | exact MI | ].
  intros known m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HF1 MU1 WM1 MI1 ST1 HB1 HM1.
  c1_retpc.
  destruct (c1_tr1 m0 m m1 lo (bv_unsigned sp) r _ _ _ MU WM FR WR MU1 WM1 ltac:(lia) ltac:(lia))
    as (MU' & WM' & FR' & WR').
  clear MU WM FR WR MU1 WM1 MI ST HB HMb.
  step. step. step. step. step.
  eapply c1_add with (lo := lo) (r := r) (p := bv_unsigned sp + 320) (k := k) (bs := bs) (M := M);
    [ reflexivity | reflexivity | reflexivity | lia | exact Hr8 | exact HB1 | exact WR' | exact HI | exact HM1
    | exact HM | lia | exact ST1 | lia | lia | lia | exact MI1 | ].
  intros z bs' m2 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HA HB2 MU2 WM2 MI2 ST2.
  c1_retpc.
  destruct (c1_tr2 m0 m1 m2 lo (bv_unsigned sp) r _ MU' WM' FR' WR' MU2 WM2 ltac:(lia) ltac:(lia))
    as (MU3 & WM3 & FR3 & WR3).
  clear MU' WM' FR' WR' MU2 WM2 MI1 ST1 HB1 HM1.
  destruct (c1_add_want bs M k lf want z bs' HI HM HW HA) as [Ezw HBP]. subst want.
  pose proof (c1_add_range bs M k z bs' HI HA) as Hz.
  step.
  destruct (Z.eq_dec v 0) as [Ev | Nv];
    [ assert (Ez : z = -1) by (apply Iv in Ev; subst M; exact (c1_add_zero _ _ _ _ HA));
      step; c1_if; step; step; c1_if
    | step; c1_if ].
  all: step; step; step; step.
  all: pose proof (c1_find_range bs M known HF1 Hn) as Hkn.
  all: destruct (c1_okb k fab) eqn:OK; destruct (Z_lt_le_dec known 0) as [Kn | Kp].
  all: try (assert (Ao : add_width_ok k (bx_fabric bs)) by (rewrite HF; apply c1_okb_spec; exact OK);
            pose proof (c1_known bs M k known z bs' HF1 Kp Ao HA) as Ekz; subst known;
            c1_if; step; c1_if).
  all: try c1_if.
  all: eapply (c1_chk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 m2 lo r fab e q0 q c lf
                k _ z j0 bs M jm2 bs');
    first [ reflexivity | eassumption | lia ].
Qed.

Lemma c1_body1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (i h v : Z)
    (bs M : list byte),
  s3 = Z_to_bv 64 i -> s4 = Z_to_bv 64 v -> s5 = Z_to_bv 64 (bv_unsigned sp + 32 + 56 * i) -> s7 = Z_to_bv 64 h ->
  0 <= i <= 4 -> length bs = 288%nat -> length M = 6%nat -> -256 < v < 256 -> c1_sh bs M v i h ->
  bytes_at rsegs m (bv_unsigned sp + 32) bs -> bytes_at rsegs m (bv_unsigned sp + 320) M -> mem_inv rsegs m ->
  (forall (h' : Z) (m' : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     c1_sh bs M v (i + 1) h' -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 (Z_to_bv 64 h') s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x13088) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13060) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q i h v bs M E3 E4 E5 E7 Hi HL HLM Hv HSH HB HM MI K.
  subst s3 s4 s5 s7.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (bytes_at_bound rsegs m _ _ HB) as BB. rewrite HL in BB.
  pose proof (bytes_at_bsub m (bv_unsigned sp + 32) bs (56 * i) 6 HB ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia))
    as HBi.
  change (bsub bs (56 * i) 6) with (bx_mac bs i) in HBi.
  pose proof (c1_mac_len bs i HL Hi) as LBi.
  step.
  destruct HSH as [(Eh & Hvh) | (Hv0 & Hh & Hmh & Hnh)].
  - subst h. c1_if. step.
    destruct (Z.eq_dec v 0) as [Ev | Nv].
    + c1_if. eapply K; [apply c1_sh_v0; exact Ev | apply munch_refl | apply wmono_refl | exact MI].
    + c1_if. step. step. step. step.
      eapply c1_bcmp with (pa := bv_unsigned sp + 32 + 56 * i) (pb := bv_unsigned sp + 320) (ls := bx_mac bs i)
        (rs := M); [ reflexivity | reflexivity | reflexivity | exact HBi | exact HM | exact LBi | exact HLM
                   | exact MI | ].
      intros v1 m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hv1 Iv1 MU1 WM1 MI1.
      c1_retpc. step. step.
      destruct (Z.eq_dec v1 0) as [E1 | N1].
      * c1_if. step.
        eapply K; [ | exact MU1 | exact WM1 | exact MI1 ].
        apply c1_sh_hit; [left; split; [reflexivity | exact Hvh] | exact Nv | lia | apply Iv1; exact E1].
      * c1_if. step. step.
        eapply K; [ | exact MU1 | exact WM1 | exact MI1 ].
        apply c1_sh_miss; [left; split; [reflexivity | exact Hvh] | lia | intros E; apply N1; apply Iv1; exact E].
  - c1_if. eapply K; [ | apply munch_refl | apply wmono_refl | exact MI ].
    apply c1_sh_keep; [right; split; [exact Hv0|]; split; [exact Hh|]; split; [exact Hmh | exact Hnh] | lia].
Qed.

Lemma c1_body2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (i u k : Z)
    (bs : list byte),
  s1 = Z_to_bv 64 u -> s2 = Z_to_bv 64 k -> s3 = Z_to_bv 64 i -> s5 = Z_to_bv 64 (bv_unsigned sp + 32 + 56 * i) ->
  0 <= i <= 4 -> length bs = 288%nat -> 0 <= k < 256 -> c1_su bs k i u ->
  bytes_at rsegs m (bv_unsigned sp + 32) bs -> mem_inv rsegs m ->
  (forall (u' : Z) (m' : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     c1_su bs k (i + 1) u' -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 u') a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x130b8) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13088) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q i u k bs E1 E2 E3 E5 Hi HL Hk SU HB MI K.
  subst s1 s2 s3 s5.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (bytes_at_bound rsegs m _ _ HB) as BB. rewrite HL in BB.
  pose proof (bytes_at_bsub m (bv_unsigned sp + 32) bs (56 * i) 6 HB ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia))
    as HBi.
  change (bsub bs (56 * i) 6) with (bx_mac bs i) in HBi.
  pose proof (c1_mac_len bs i HL Hi) as LBi.
  step.
  destruct SU as [(Eu & Hnu) | (Hu & Hmu & Hku & Hnu)].
  - subst u. c1_if. step. step. step. step. step.
    eapply c1_bcmp with (pa := bv_unsigned sp + 32 + 56 * i) (pb := 0x10392) (ls := bx_mac bs i) (rs := zero6);
      [ reflexivity | first [reflexivity | apply bv_eq; vm_compute; reflexivity] | reflexivity | exact HBi
      | exact (c1_zero m MI) | exact LBi | reflexivity | exact MI | ].
    intros v2 m2 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hv2 Iv2 MU2 WM2 MI2.
    c1_retpc. step.
    destruct (Z.eq_dec v2 0) as [E2 | N2].
    + c1_if.
      pose proof (bytes_at_transport rsegs [] m m2 _ _ HB MU2 I) as HB2.
      pose proof (rd4_bytes_at m2 (bv_unsigned sp + 32) bs (56 * i + 12) HB2 ltac:(lia) ltac:(rewrite HL; lia)) as R12.
      change (rd4 bs (56 * i + 12)) with (bx_nch bs i) in R12. apply bx_ov4 in R12.
      pose proof (rd4_range bs (56 * i + 12)) as Rn. change (rd4 bs (56 * i + 12)) with (bx_nch bs i) in Rn.
      step. rewrite ?bx_sx32 by lia. step. step.
      destruct (Z.eq_dec (bx_nch bs i) k) as [Ek | Nk].
      * c1_if. step.
        eapply K; [ | exact MU2 | exact WM2 | exact MI2 ].
        apply c1_su_hit; [left; split; [reflexivity | exact Hnu] | lia | apply Iv2; exact E2 | exact Ek].
      * c1_if. step. step.
        eapply K; [ | exact MU2 | exact WM2 | exact MI2 ].
        apply c1_su_miss; [left; split; [reflexivity | exact Hnu] | lia | intros (_ & E); exact (Nk E)].
    + c1_if.
      eapply K; [ | exact MU2 | exact WM2 | exact MI2 ].
      apply c1_su_miss; [left; split; [reflexivity | exact Hnu] | lia | intros (E & _); apply N2; apply Iv2; exact E].
  - c1_if. eapply K; [ | apply munch_refl | apply wmono_refl | exact MI ].
    apply c1_su_keep; [right; split; [exact Hu|]; split; [exact Hmu|]; split; [exact Hku | exact Hnu] | lia].
Qed.

Lemma c1_loop : forall (d : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (i h u v k : Z)
    (bs M : list byte),
  s1 = Z_to_bv 64 u -> s2 = Z_to_bv 64 k -> s3 = Z_to_bv 64 i -> s4 = Z_to_bv 64 v ->
  s5 = Z_to_bv 64 (bv_unsigned sp + 32 + 56 * i) -> s6 = Z_to_bv 64 (bx_n bs - i) -> s7 = Z_to_bv 64 h ->
  bx_n bs - i = Z.of_nat (S d) -> 0 <= i -> bx_n bs <= 5 -> length bs = 288%nat -> length M = 6%nat ->
  -256 < v < 256 -> 0 <= k < 256 -> c1_sh bs M v i h -> c1_su bs k i u ->
  bytes_at rsegs m (bv_unsigned sp + 32) bs -> bytes_at rsegs m (bv_unsigned sp + 320) M -> mem_inv rsegs m ->
  (forall (h' u' : Z) (m' : word -> option byte)
          (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' t3' t4' t5' t6' : word),
     c1_sh bs M v (bx_n bs) h' -> c1_su bs k (bx_n bs) u' -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 u') a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 s3' s4 s5' s6' (Z_to_bv 64 h') s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x130c8) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13060) fc None m (seg_rom rsegs)).
Proof.
  induction d as [|d IH]; intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m Q i h u v k bs M E1 E2 E3 E4 E5 E6 E7 Hd Hi Hn5 HL HLM Hv Hk HSH SU HB HM MI K;
    subst s6;
    (eapply c1_body1 with (i := i) (h := h) (v := v) (bs := bs) (M := M);
      [ exact E3 | exact E4 | exact E5 | exact E7 | lia | exact HL | exact HLM | exact Hv | exact HSH | exact HB
      | exact HM | exact MI | ]);
    intros h1 m1 ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 SH1 MU1 WM1 MI1;
    pose proof (bytes_at_transport rsegs [] m m1 _ _ HB MU1 I) as HB1;
    (eapply c1_body2 with (i := i) (u := u) (k := k) (bs := bs);
      [ exact E1 | exact E2 | exact E3 | exact E5 | lia | exact HL | exact Hk | exact SU | exact HB1 | exact MI1 | ]);
    intros u1 m2 ra2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62 SU1 MU2 WM2 MI2;
    subst s3 s5; pose proof (bv_unsigned_in_range 64 sp) as Rsp; change (bv_modulus 64) with (2 ^ 64) in Rsp;
    step; step; step; rewrite ?fnd_addiw by lia; step.
  - c1_if.
    replace (bx_n bs) with (i + 1) in K by lia.
    eapply K; [ exact SH1 | exact SU1 | eapply munch_trans; [exact MU1 | exact MU2]
              | eapply wmono_trans; [exact WM1 | exact WM2] | exact MI2 ].
  - c1_if.
    pose proof (bytes_at_transport rsegs [] m1 m2 _ _ HB1 MU2 I) as HB2.
    pose proof (bytes_at_transport rsegs [] m m1 _ _ HM MU1 I) as HM1.
    pose proof (bytes_at_transport rsegs [] m1 m2 _ _ HM1 MU2 I) as HM2.
    eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 Q (i + 1) h1 u1 v k bs M);
      [ reflexivity | exact E2 | first [reflexivity | rewrite fnd_addiw by lia; reflexivity]
      | exact E4 | f_equal; lia | f_equal; lia | reflexivity | lia | lia | exact Hn5 | exact HL | exact HLM
      | exact Hv | exact Hk | exact SH1 | exact SU1 | exact HB2 | exact HM2 | exact MI2 | ].
    intros h' u' m' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' t3' t4' t5' t6' SH' SU' MU' WM' MI'.
    eapply K; [ exact SH' | exact SU' | | | exact MI' ].
    + eapply munch_trans; [exact MU1 | eapply munch_trans; [exact MU2 | exact MU']].
    + eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM']].
Qed.

Lemma c1_decide :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab e q0 q c h u v k : Z) (j0 bs M jm2 : list byte),
  s0 = Z_to_bv 64 r -> s1 = Z_to_bv 64 u -> s2 = Z_to_bv 64 k -> s4 = Z_to_bv 64 v -> s7 = Z_to_bv 64 h ->
  s11 = Z_to_bv 64 fab ->
  0 <= k < 256 -> -256 < v < 256 -> (v = 0 <-> M = zero6) ->
  c1_sh bs M v (bx_n bs) h -> c1_su bs k (bx_n bs) u ->
  boxreg_inv bs -> bx_fabric bs = fab -> length M = 6%nat ->
  rw_cells rsegs m (bv_unsigned sp)
    [CB 8 j0; C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 (-1)); C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 6 M; CB 2 jm2;
     C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  bytes_at rsegs m r bs -> wr_at rsegs m r 288 -> r mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> LF_RES_TOP <= lo -> 0 <= r -> r + 288 <= lo ->
  bv_unsigned sp + 448 <= 2 ^ 63 ->
  munch [(lo, bv_unsigned sp + 344); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> 0 <= c -> q + c = e ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab e q0 j0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x130c8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m lo r fab e q0 q c h u v k j0 bs M jm2 E0 E1 E2 E4 E7 E11 Hk Hv Iv HSH SU HI HF HM FR HB WR Hr8
    ST LO HLF Hr0 Hr HX MU WM MI Hq0 Hc Hqe.
  subst s1 s2 s4 s7 s11.
  pose proof (c1_inv_len bs HI) as HL. pose proof (c1_inv_n bs HI) as Hn. pose proof (c1_inv_fab bs HI) as Hfb.
  pose proof HI as ((_ & HB1 & HB2 & HB3 & _) & _).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  step. step. step. step. step. step. step. step.
  fold (c1_okx k fab). rewrite (c1_okb_val k fab) by lia.
  pose proof (c1_okb_spec k fab) as OKS.
  destruct (c1_okb k fab) eqn:OK; [change (Z.b2z true) with 1 | change (Z.b2z false) with 0].
  2: { step. c1_if. step.
       assert (HW : c1_wantP bs M k (-1) (-1)).
       { left. split; [|reflexivity]. intros (Ao & _). rewrite HF in Ao. apply OKS in Ao. rewrite ?OK in Ao.
         discriminate. }
       eapply (c1_main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 m lo r fab e q0 q c
                 (-1) k v (-1) j0 bs M jm2);
         first [ exact E0 | reflexivity | (rewrite OK; reflexivity) | eassumption | lia ]. }
  assert (Ao : add_width_ok k (bx_fabric bs)) by (rewrite HF; apply OKS; first [reflexivity | exact OK]).
  pose proof Ao as (Ake & Ak & Akf).
  step. c1_if. step.
  destruct (Z.eq_dec v 0) as [Ev | Nv].
  { c1_if. step.
    assert (HW : c1_wantP bs M k (-1) (-1)).
    { left. split; [|reflexivity]. intros (_ & Az). apply Az. apply Iv. exact Ev. }
    eapply (c1_main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 m lo r fab e q0 q c
              (-1) k v (-1) j0 bs M jm2);
      first [ exact E0 | reflexivity | (rewrite OK; reflexivity) | eassumption | lia ]. }
  assert (Mz : M <> zero6) by (intros Ez; apply Nv; apply Iv; exact Ez).
  c1_if. step.
  destruct HSH as [(Eh & [Ev' | Hnh]) | (Hv0 & Hh & Hmh & Hnh)]; [contradiction | |].
  2: { c1_if.
       assert (HW : c1_wantP bs M k (-1) h).
       { right; left. split; [exact Ao|]. split; [exact Mz|]. split; [lia|]. split; [exact Hmh | exact Hnh]. }
       eapply (c1_main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 m lo r fab e q0 q c
                 (-1) k v h j0 bs M jm2);
         first [ exact E0 | reflexivity | (rewrite OK; reflexivity) | eassumption | lia ]. }
  subst h. c1_if. step.
  destruct SU as [(Eu & Hnu) | (Hu & Hmu & Hku & Hnu)].
  2: { c1_if. step. step.
       assert (HW : c1_wantP bs M k (-1) u).
       { right; right; left. split; [exact Ao|]. split; [exact Mz|]. split; [exact Hnh|].
         split; [lia|]. split; [exact Hmu|]. split; [exact Hku | exact Hnu]. }
       eapply (c1_main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 m lo r fab e q0 q c
                 (-1) k v u j0 bs M jm2);
         first [ exact E0 | reflexivity | (rewrite OK; reflexivity) | eassumption | lia ]. }
  subst u. c1_if. step. step. step. step.
  destruct (Z_lt_le_dec 4 (bx_n bs)) as [N5 | N4].
  { c1_if.
    assert (HW : c1_wantP bs M k (-1) (-1)).
    { right; right; right; left. split; [exact Ao|]. split; [exact Mz|]. split; [exact Hnh|].
      split; [exact Hnu|]. split; [left; lia | reflexivity]. }
    eapply (c1_main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 m lo r fab e q0 q c
              (-1) k v (-1) j0 bs M jm2);
      first [ exact E0 | reflexivity | (rewrite OK; reflexivity) | eassumption | lia ]. }
  c1_if. step. step. step. step.
  pose proof (c1_cb_at m (bv_unsigned sp) [CB 8 j0; C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 (-1));
                C8 (Z_to_bv 64 (bx_n bs))] 288 bs [CB 6 M; CB 2 jm2; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] FR) as HBc.
  change (Z.of_nat (cells_size [CB 8 j0; C8 (Z_to_bv 64 fab); C8 (Z_to_bv 64 (-1)); C8 (Z_to_bv 64 (bx_n bs))]))
    with 32 in HBc.
  eapply c1_lowf with (lo := lo) (t := bv_unsigned sp + 32) (k := k) (f := fab) (bs := bs);
    [ reflexivity | reflexivity | reflexivity | lia | lia | exact HBc | exact HL | exact HB1 | exact HB2
    | exact HB3 | exact ST | lia | right; lia | ].
  intros z m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hz MU1 WM1 ST1.
  c1_retpc.
  destruct (c1_tr1 m0 m m1 lo (bv_unsigned sp) r _ _ _ MU WM FR WR MU1 WM1 ltac:(lia) ltac:(lia))
    as (MU' & WM' & FR' & WR').
  pose proof (bytes_at_transport rsegs _ m m1 r bs HB MU1
                ltac:(cbn [disjoint_from]; rewrite HL; change (Z.of_nat 288) with 288; split; [lia | exact I])) as HB'.
  pose proof (c1_mi_stack m m1 (bv_unsigned sp - 64) (bv_unsigned sp) MI MU1 ltac:(lia)) as MI'.
  clear MU WM FR WR HB MI MU1 WM1 HBc ST.
  assert (Hzr : z = -1 \/ 0 <= z <= 38).
  { destruct Hz as [(-> & _) | (H1 & _)]; [left; reflexivity | right; lia]. }
  step. step. step. step.
  fold (c1_orx z (bx_n bs)). rewrite (c1_or_val z (bx_n bs)) by lia.
  destruct Hzr as [Ez | Hz0].
  - subst z. replace (if -1 <? 0 then -1 else bx_n bs) with (-1) by reflexivity.
    step.
    assert (HW : c1_wantP bs M k (-1) (-1)).
    { right; right; right; left. split; [exact Ao|]. split; [exact Mz|]. split; [exact Hnh|].
      split; [exact Hnu|]. split; [right; rewrite HF; exact Hz | reflexivity]. }
    eapply (c1_main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 _ lo r fab e q0 q c
              (-1) k v (-1) j0 bs M jm2);
      first [ exact E0 | reflexivity | (rewrite OK; reflexivity) | eassumption | lia ].
  - replace (if z <? 0 then -1 else bx_n bs) with (bx_n bs) by (destruct (Z.ltb_spec z 0); lia).
    step.
    assert (HW : c1_wantP bs M k z (bx_n bs)).
    { right; right; right; right. split; [exact Ao|]. split; [exact Mz|]. split; [exact Hnh|].
      split; [exact Hnu|]. split; [lia|]. split; [reflexivity|]. split; [lia | rewrite HF; exact Hz]. }
    eapply (c1_main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 _ lo r fab e q0 q c
              z k v (bx_n bs) j0 bs M jm2);
      first [ exact E0 | reflexivity | (rewrite OK; reflexivity) | eassumption | lia ].
Qed.

Ltac c1_sh0 := first [ left; split; [reflexivity | right; intros; exfalso; lia]
                     | left; split; [reflexivity | intros; exfalso; lia] ].

Lemma c1_wid2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab e q0 q c k : Z) (j0 j1a bs M jm2 : list byte),
  s0 = Z_to_bv 64 r -> s2 = Z_to_bv 64 k -> s11 = Z_to_bv 64 fab ->
  rw_cells rsegs m (bv_unsigned sp)
    [CB 8 j0; C8 (Z_to_bv 64 fab); CB 8 j1a; C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 6 M; CB 2 jm2;
     C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  0 <= k < 256 -> boxreg_inv bs -> bx_fabric bs = fab -> length M = 6%nat ->
  bytes_at rsegs m r bs -> wr_at rsegs m r 288 -> r mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> LF_RES_TOP <= lo -> 0 <= r -> r + 288 <= lo ->
  bv_unsigned sp + 448 <= 2 ^ 63 ->
  munch [(lo, bv_unsigned sp + 344); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> 0 <= c -> q + c = e ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab e q0 j0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13020) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m lo r fab e q0 q c k j0 j1a bs M jm2 E0 E2 E11 FR Hk HI HF HM HB WR Hr8 ST LO HLF Hr0 Hr HX MU WM MI
    Hq0 Hc Hqe.
  subst s2 s11.
  pose proof (c1_inv_len bs HI) as HL. pose proof (c1_inv_n bs HI) as Hn.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (c1_cb_at m (bv_unsigned sp) [CB 8 j0; C8 (Z_to_bv 64 fab); CB 8 j1a; C8 (Z_to_bv 64 (bx_n bs))] 288 bs
                [CB 6 M; CB 2 jm2; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] FR) as HBc.
  change (Z.of_nat (cells_size [CB 8 j0; C8 (Z_to_bv 64 fab); CB 8 j1a; C8 (Z_to_bv 64 (bx_n bs))])) with 32 in HBc.
  pose proof (c1_cb_at m (bv_unsigned sp) [CB 8 j0; C8 (Z_to_bv 64 fab); CB 8 j1a; C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs]
                6 M [CB 2 jm2; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] FR) as HMb.
  change (Z.of_nat (cells_size [CB 8 j0; C8 (Z_to_bv 64 fab); CB 8 j1a; C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs]))
    with 320 in HMb.
  step. step. step. step. step.
  eapply c1_bcmp with (pa := bv_unsigned sp + 320) (pb := 0x10392) (ls := M) (rs := zero6);
    [ reflexivity | first [reflexivity | apply bv_eq; vm_compute; reflexivity] | reflexivity | exact HMb
    | exact (c1_zero m MI) | exact HM | reflexivity | exact MI | ].
  intros v m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hv Iv MU1 WM1 MI1.
  c1_retpc.
  destruct (c1_tr0 m0 m m1 lo (bv_unsigned sp) r _ bs MU WM FR WR ST HB MU1 WM1)
    as (MU' & WM' & FR' & WR' & ST' & HB').
  pose proof (bytes_at_transport rsegs [] m m1 _ _ HBc MU1 I) as HBc'.
  pose proof (bytes_at_transport rsegs [] m m1 _ _ HMb MU1 I) as HMb'.
  clear MU WM FR WR ST HB MU1 WM1 HBc HMb MI.
  step.
  pose proof (rd4_bytes_at m1 (bv_unsigned sp + 32) bs 280 HBc' ltac:(lia) ltac:(rewrite HL; lia)) as R280.
  change (rd4 bs 280) with (bx_n bs) in R280. apply bx_ov4 in R280.
  match type of FR' with ?T => change T with (bx_keep T) in FR' end.
  step.
  unfold bx_keep in FR'.
  rewrite ?bx_sx32 by lia.
  step. step. step. step. step.
  destruct (Z.eq_dec (bx_n bs) 0) as [N0 | N1].
  - c1_if.
    eapply (c1_decide _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 _ lo r fab e q0 q c
              (-1) (-1) v k j0 bs M jm2);
      first [ exact E0 | reflexivity | eassumption | lia | c1_sh0 ].
  - c1_if. step. step. step. step.
    eapply (c1_loop (Z.to_nat (bx_n bs - 1)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              F fc _ _ 0 (-1) (-1) v k bs M);
      [ reflexivity | reflexivity | reflexivity | reflexivity | f_equal; lia | f_equal; lia | reflexivity | lia | lia
      | lia | exact HL | exact HM | exact Hv | exact Hk | c1_sh0 | c1_sh0
      | exact HBc' | exact HMb' | eassumption | ].
    intros h' u' mK ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' t3' t4' t5' t6' SH' SU' MUK WMK MIK.
    destruct (c1_tr0 m0 _ mK lo (bv_unsigned sp) r _ bs MU' WM' FR' WR' ST' HB' MUK WMK)
      as (MU'' & WM'' & FR'' & WR'' & ST'' & HB'').
    eapply (c1_decide _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 mK lo r fab e q0 q c
              h' u' v k j0 bs M jm2);
      first [ exact E0 | reflexivity | exact SH' | exact SU' | exact MU'' | exact WM'' | exact FR'' | exact WR''
            | exact ST'' | exact HB'' | exact MIK | eassumption | lia ].
Qed.

Lemma c1_wid :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (lo r fab e q0 q c : Z) (j0 j1 bs M jm2 rest : list byte),
  s0 = Z_to_bv 64 r -> s2 = Z_to_bv 64 c -> s3 = Z_to_bv 64 q -> s7 = Z_to_bv 64 (bx_n bs) ->
  s11 = Z_to_bv 64 fab ->
  rw_cells rsegs m (bv_unsigned sp)
    [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1; CB 288 bs; CB 6 M; CB 2 jm2; C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 c)] ->
  bytes_at rsegs m q rest -> Z.of_nat (length rest) = c ->
  boxreg_inv bs -> bx_fabric bs = fab -> length M = 6%nat ->
  bytes_at rsegs m r bs -> wr_at rsegs m r 288 -> r mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> LF_RES_TOP <= lo -> 0 <= r -> r + 288 <= lo ->
  bv_unsigned sp + 448 <= 2 ^ 63 ->
  munch [(lo, bv_unsigned sp + 344); (r, r + 288)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  q0 <= q -> q + c = e -> e <= lo -> 0 <= q ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m0 lo r fab e q0 j0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13004) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m lo r fab e q0 q c j0 j1 bs M jm2 rest E0 E2 E3 E7 E11 FR HP HPl HI HF HM HB WR Hr8 ST LO HLF Hr0 Hr
    HX MU WM MI Hq0 Hqe Hel Hq.
  subst s2 s3 s7 s11.
  pose proof (c1_inv_n bs HI) as Hn. pose proof (c1_inv_len bs HI) as HLb.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  step. step.
  destruct rest as [|x rest]; cbn [length] in HPl.
  - c1_if.
    eapply (c1_wid2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 _ lo r fab e q0 q c c j0 _
              bs M jm2);
      first [ exact E0 | reflexivity | eassumption | lia ].
  - c1_if. step. step. step. step. rd_prep. step.
    pose proof (bx_byte_range x) as Rx.
    eapply (c1_wid2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 _ lo r fab e q0 (q + 1)
              (c + -1) (bv_unsigned x) j0 _ bs M jm2);
      first [ exact E0 | reflexivity | eassumption | lia ].
Qed.

Ltac c1_pay :=
  match goal with H : bytes_at _ _ ?Q _ |- bytes_at _ _ ?q _ => replace q with Q by lia; exact H end.

Ltac c1_go HS E0 :=
  let HM := fresh "HM" in
  rd_m6 HS HM;
  eapply c1_wid;
  first [ exact E0 | reflexivity | exact HM | c1_pay | (cbn [length]; lia)
        | (rewrite ?length_app, ?length_le4; reflexivity) | eassumption | lia ].

Lemma c1_head :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo r fab ip inn e : Z)
    (j0 j1 jm bs rest : list byte),
  s0 = Z_to_bv 64 r -> s1 = Z_to_bv 64 ip -> s2 = Z_to_bv 64 (inn - 1) -> s3 = Z_to_bv 64 (ip + 1) ->
  s5 = Z_to_bv 64 inn -> s7 = Z_to_bv 64 (bx_n bs) -> s9 = Z_to_bv 64 (bv_unsigned sp + 326) ->
  s11 = Z_to_bv 64 fab ->
  rw_cells rsegs m (bv_unsigned sp)
    [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1; CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 (ip + 1));
     C8 (Z_to_bv 64 (inn - 1))] ->
  rw_cells rsegs m r [CB 288 bs] -> boxreg_inv bs -> bx_fabric bs = fab ->
  bytes_at rsegs m (ip + 1) rest -> Z.of_nat (length rest) = inn - 1 ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> LF_RES_TOP <= lo -> lo + 112 <= bv_unsigned sp ->
  bv_unsigned sp + 448 <= 2 ^ 47 -> r mod 16 = 0 -> 0 <= r -> r + 288 <= lo -> 0 <= ip -> ip + inn = e ->
  e <= lo -> 1 <= inn ->
  evt rsegs (llvm_case_Q sp gp tp s0 s8 s9 s10 s11 F fc m lo r fab e ip j0 bs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12dd8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo r fab ip inn e j0 j1 jm bs rest E0 E1 E2 E3 E5 E7 E9 E11 HS RWR HI HF HP HL MI ST HLF LO SPB Hr16
    Hr0 Hr Hip Hie Hel Hinn.
  subst s1 s2 s3 s5 s7 s9 s11.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (munch_refl [(lo, bv_unsigned sp + 344); (r, r + 288)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof RWR as [[_ HB] WR]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  change (Z.of_nat (cells_size [CB 288 bs])) with 288 in WR.
  clear RWR.
  assert (Hr8 : r mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof (c1_inv_len bs HI) as HLb.
  step. step. sg_br HC; clear HC.
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x12e58) _ _ _ _) =>
           destruct rest as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 rest]]]]]]; cbn [length] in HL;
           rd_go 0x12e60 0x13004; c1_go HS E0
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x12de0) _ _ _ _) =>
           destruct rest as [|x0 rest]; cbn [length] in HL;
           rd_go 0x12df4 0x13004; c1_go HS E0
       end.
Qed.
End S.

Lemma c1_evt : bcmp_contract -> reac_boxreg_find_contract -> reac_boxreg_add_contract -> lowest_free_contract ->
  llvm_case_evt (llvm_case_pc 1).
Proof.
  intros BCMP_C FIND_C ADD_C LOWF_C F fc regs mem spv lo r fab ip inn op i e gp tp j0 j1 jm bs rest E2 E3 E4 E8 E9
    E18 E19 E21 E22 E23 E24 E25 E26 E27 HS HR HI HF HP HL MI ST Hlo Hlo2 Hsp Hr4 Hr16 Hr Hip Hie Hel Hinn Hinn2
    Hop Hi.
  change (llvm_case_pc 1) with 0x12dd8.
  unfold Regs6ss.mkR_of.
  assert (Hspv : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  assert (G2 : reg_get regs 2 = Z_to_bv 64 spv) by exact E2.
  assert (G3 : reg_get regs 3 = gp) by exact E3.
  assert (G4 : reg_get regs 4 = tp) by exact E4.
  assert (G8 : reg_get regs 8 = Z_to_bv 64 r) by exact E8.
  assert (G9 : reg_get regs 9 = Z_to_bv 64 ip) by exact E9.
  assert (G18 : reg_get regs 18 = Z_to_bv 64 (inn - 1)) by exact E18.
  assert (G19 : reg_get regs 19 = Z_to_bv 64 (ip + 1)) by exact E19.
  assert (G21 : reg_get regs 21 = Z_to_bv 64 inn) by exact E21.
  assert (G23 : reg_get regs 23 = Z_to_bv 64 (bx_n bs)) by exact E23.
  assert (G24 : reg_get regs 24 = Z_to_bv 64 i) by exact E24.
  assert (G25 : reg_get regs 25 = Z_to_bv 64 (spv + 326)) by exact E25.
  assert (G26 : reg_get regs 26 = Z_to_bv 64 (spv + 32)) by exact E26.
  assert (G27 : reg_get regs 27 = Z_to_bv 64 fab) by exact E27.
  rewrite G2, G3, G4, G8, G9, G18, G19, G21, G23, G24, G25, G26, G27.
  eapply (c1_head BCMP_C FIND_C ADD_C LOWF_C) with (lo := lo) (r := r) (fab := fab) (ip := ip) (inn := inn) (e := e)
    (j0 := j0) (j1 := j1) (jm := jm) (bs := bs) (rest := rest);
    first [ reflexivity | exact HR | exact HI | exact HF | exact HP | exact HL | exact MI
          | (rewrite Hspv; first [ reflexivity | exact HS | exact ST | lia ]) | lia ].
Qed.

Section C1.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Theorem llvm_case1_ok : llvm_case_ok B API 1.
Proof.
  exact (llvm_case_of_evt B API 1
           (c1_evt bcmp_holds (reac_boxreg_find_holds bcmp_holds)
              (reac_boxreg_add_holds (reac_boxreg_find_holds bcmp_holds) lowest_free_base_holds memset_holds
                 memcpy_holds)
              (lowest_free_holds range_free_holds))).
Qed.

End C1.
