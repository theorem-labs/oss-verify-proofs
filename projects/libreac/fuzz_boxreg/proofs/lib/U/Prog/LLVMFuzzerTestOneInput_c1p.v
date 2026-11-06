From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd BoxregStep BoxregUpd
  reac_boxreg_find_c lowest_free_base_c reac_boxreg_add_c reac_boxreg_add_inv range_free_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
  LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv.
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

Lemma c1_land : forall z, 0 <= z < 2 ^ 31 ->
  Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_slt (Z_to_bv 64 0) (Z_to_bv 64 z)))))
    (bv_unsigned (Z_to_bv 64 z)) = z.
Proof.
  intros z Hz. unfold v_slt, c_lts. rewrite lts_lit by lia.
  destruct (Z.ltb_spec 0 z) as [Lt | Ge].
  - rewrite (unsigned_lit 1), (unsigned_lit z) by lia. rewrite unsigned_lit_wrap.
    change ((0 - 1) mod 2 ^ 64) with 18446744073709551615. rewrite Z.land_comm.
    change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
  - assert (z = 0) by lia. subst z. reflexivity.
Qed.

Definition c1_lfres (bs : list byte) (nch fabric z : Z) : Prop :=
  (z = -1 /\ forall b, 0 <= b <= fabric - nch -> ~ range_free_ok bs b nch fabric) \/
  (0 <= z <= fabric - nch /\ range_free_ok bs z nch fabric /\
   forall b, 0 <= b < z -> ~ range_free_ok bs b nch fabric).

Definition c1_wantP (bs M : list byte) (k lf want : Z) : Prop :=
  (~ (add_width_ok k (bx_fabric bs) /\ M <> zero6) /\ want = -1) \/
  (add_width_ok k (bx_fabric bs) /\ M <> zero6 /\ add_held bs M want) \/
  (add_width_ok k (bx_fabric bs) /\ M <> zero6 /\ add_none_held bs M /\ add_unbound bs k want) \/
  (add_width_ok k (bx_fabric bs) /\ M <> zero6 /\ add_none_held bs M /\ add_none_unbound bs k /\
   (5 <= bx_n bs \/ c1_lfres bs k (bx_fabric bs) (-1)) /\ want = -1) \/
  (add_width_ok k (bx_fabric bs) /\ M <> zero6 /\ add_none_held bs M /\ add_none_unbound bs k /\
   bx_n bs < 5 /\ want = bx_n bs /\ 0 <= lf /\ c1_lfres bs k (bx_fabric bs) lf).

Lemma c1_inv_n : forall bs, boxreg_inv bs -> 0 <= bx_n bs <= 5.
Proof. intros bs ((_ & H & _) & _). exact H. Qed.

Lemma c1_inv_len : forall bs, boxreg_inv bs -> length bs = 288%nat.
Proof. intros bs ((H & _) & _). exact H. Qed.

Lemma c1_inv_fab : forall bs, boxreg_inv bs -> 1 <= bx_fabric bs <= 40.
Proof. intros bs ((_ & _ & H & _) & _). exact H. Qed.

Lemma c1_lf_uniq : forall bs k z1 z2,
  c1_lfres bs k (bx_fabric bs) z1 -> lowest_free bs k z2 -> z1 = z2.
Proof.
  intros bs k z1 z2 H1 H2. unfold c1_lfres, range_free_ok in H1. unfold lowest_free, slice_meets in H2.
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

Lemma c1_fr_fin : forall m A w0 z0 f w1 ii nb bs ja M q c,
  rw_cells rsegs m A [C8 w0; C8 z0; C8 f; C8 w1; C8 ii; C8 nb; CB 288 bs; CB 2 ja; CB 6 M; C8 q; C8 c] ->
  rw_cells rsegs m A [CB 8 (le8 w0 ++ []); C8 z0; C8 f; CB 8 (le8 w1 ++ []); C8 ii; C8 nb; CB 288 bs;
                      CB 8 (ja ++ M ++ []); C8 q; C8 c].
Proof.
  intros m A w0 z0 f w1 ii nb bs ja M q c H.
  pose proof (rw_cells_merge rsegs m A [] [C8 w0]
                [C8 z0; C8 f; C8 w1; C8 ii; C8 nb; CB 288 bs; CB 2 ja; CB 6 M; C8 q; C8 c] H) as H1.
  pose proof (rw_cells_merge rsegs m A [CB 8 (le8 w0 ++ []); C8 z0; C8 f] [C8 w1]
                [C8 ii; C8 nb; CB 288 bs; CB 2 ja; CB 6 M; C8 q; C8 c] H1) as H2.
  exact (rw_cells_merge rsegs m A [CB 8 (le8 w0 ++ []); C8 z0; C8 f; CB 8 (le8 w1 ++ []); C8 ii; C8 nb;
           CB 288 bs] [CB 2 ja; CB 6 M] [C8 q; C8 c] H2).
Qed.

Lemma c1_zero : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10392 zero6.
Proof.
  intros m MI. apply ro_bytes_at; [ exact MI | lia | cbn; lia | ].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma c1_tr1 : forall m0 m m' lo X r a b cs,
  munch [(lo, X + 360); (r, r + 288)] m0 m -> wmono rsegs m0 m -> rw_cells rsegs m X cs -> wr_at rsegs m r 288 ->
  munch [(a, b)] m m' -> wmono rsegs m m' -> lo <= a -> b <= X ->
  munch [(lo, X + 360); (r, r + 288)] m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' X cs /\ wr_at rsegs m' r 288.
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
  munch [(lo, X + 360); (r, r + 288)] m0 m -> wmono rsegs m0 m -> rw_cells rsegs m X cs -> wr_at rsegs m r 288 ->
  munch [(lo, X); (r, r + 288)] m m' -> wmono rsegs m m' -> lo <= X -> r + 288 <= lo ->
  munch [(lo, X + 360); (r, r + 288)] m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' X cs /\ wr_at rsegs m' r 288.
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
  munch [(lo, X + 360); (r, r + 288)] m0 m -> wmono rsegs m0 m -> rw_cells rsegs m X cs -> wr_at rsegs m r 288 ->
  stk rsegs m lo X -> bytes_at rsegs m r bs ->
  munch [] m m' -> wmono rsegs m m' ->
  munch [(lo, X + 360); (r, r + 288)] m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' X cs /\ wr_at rsegs m' r 288 /\
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

Lemma c1_find_range : forall bs M z, find_result bs M z -> 0 <= bx_n bs <= 5 -> -1 <= z < 5.
Proof.
  intros bs M z HF Hn. unfold find_result, first_mac in HF.
  destruct HF as [(_ & ->) | [(_ & (Hi & _)) | (_ & -> & _)]]; lia.
Qed.
