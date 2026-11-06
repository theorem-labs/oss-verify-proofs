(* segconf ubsan calloc (0x172a0), from the clear decision at 0x17304 to calloc's return: the tail memset
   (n < 4096) and mal0_clear's page loop (n >= 4096, ubsan 0x1730c-0x1738c). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require RoAdapt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import memset_c memset_ro_c memset_ro.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import CallocBigC.
Import ListNotations.
Open Scope Z_scope.

(* run_entry (CallocRun.v) with the cap m * n <= CALLOC_BIG_CAP in place of m * n < 4096: calloc's prologue, the
   overflow test (mulhu) and the call of malloc(m * n) at 0x172ec. *)
Lemma run_entry_big : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo mn : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
  bv_unsigned a1 * bv_unsigned a0 = mn -> mn <= CALLOC_BIG_CAP ->
  evt rsegs
    (fun ms' => exists (a2' : word) (m1 : word -> option byte) (junk : list byte),
       ms' = MS (mkR (Z_to_bv 64 0x172f0) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 mn)
                     (Z_to_bv 64 mn) a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17518) fc None m1 (seg_rom rsegs) /\
       rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra] /\
       munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x172a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo mn ST LO HP HMN.
  unfold CALLOC_BIG_CAP in HMN.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. pose proof (zr_word a1) as Ra1. unfold inr64 in Ra0, Ra1.
  assert (Hmn0 : 0 <= mn) by (rewrite <- HP; nia).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 32%nat ST.
  do 5 step.
  assert (E1 : Z_to_bv 64 (bv_unsigned a1 * bv_unsigned a0) = Z_to_bv 64 mn) by (rewrite HP; reflexivity).
  if_cases K0.
  - do 3 step. rewrite !E1.
    apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [exact FR|]. split; [exact MU | exact WM].
  - step.
    assert (K1 : bv_eqb (Z_to_bv 64 ((bv_unsigned a1 * bv_unsigned a0) ≫ 64)) (Z_to_bv 64 0) = true).
    { rewrite HP, Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
    step. rewrite K1; cbv iota. do 3 step. rewrite !E1.
    apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [exact FR|]. split; [exact MU | exact WM].
Qed.

(* calloc's state when it returns from the clearing: ra, sp, gp, tp, s0-s11, F, fc as given, a0 = the block,
   every other register unknown; the memory changed only inside the block and the block holds mn zero bytes. *)
Definition clear_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p : word) (mn : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 p a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned p, bv_unsigned p + mn)] m m' /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned p) [CB (Z.to_nat mn) (repeat (Z_to_bv 8 0) (Z.to_nat mn))].

(* ------------------------------------------------------------------------------------------------------- *)
(* Helper lemmas (new, for the page loop).                                                                   *)
(* ------------------------------------------------------------------------------------------------------- *)

(* A run of zero bytes, as a byte list. *)
Definition zs (k : Z) : list byte := repeat (Z_to_bv 8 0) (Z.to_nat k).

Lemma zs_app : forall a b, 0 <= a -> 0 <= b -> zs a ++ zs b = zs (a + b).
Proof. intros a b Ha Hb. unfold zs. rewrite <- repeat_app. f_equal. lia. Qed.

(* One CB cell, unfolded. *)
Lemma rw_cb_iff : forall segs m A (k : nat) bs,
  rw_cells segs m A [CB k bs] <-> (length bs = k /\ bytes_at segs m A bs /\ wr_at segs m A (Z.of_nat k)).
Proof.
  intros segs m A k bs. unfold rw_cells, cells_at.
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite app_nil_r, Nat.add_0_r. tauto.
Qed.

Lemma wr_at_split : forall segs m A a b, 0 <= a <= b ->
  wr_at segs m A b <-> (wr_at segs m A a /\ wr_at segs m (A + a) (b - a)).
Proof.
  intros segs m A a b Hab. unfold wr_at. split.
  - intros (H1 & H2 & H). split.
    + split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + a + i) with (A + (a + i)) by lia. apply H. lia.
  - intros [(A1 & B1 & H1) (A2 & B2 & H2)]. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i a) as [L|L].
    + apply H1. lia.
    + replace (A + i) with (A + a + (i - a)) by lia. apply H2. lia.
Qed.

Lemma cb_split : forall segs m A (a b : Z) bs, 0 <= a <= b ->
  rw_cells segs m A [CB (Z.to_nat b) bs] ->
  rw_cells segs m A [CB (Z.to_nat a) (firstn (Z.to_nat a) bs)] /\
  rw_cells segs m (A + a) [CB (Z.to_nat (b - a)) (skipn (Z.to_nat a) bs)].
Proof.
  intros segs m A a b bs Hab H. apply rw_cb_iff in H. destruct H as (L & HB & HW).
  assert (LF : length (firstn (Z.to_nat a) bs) = Z.to_nat a) by (rewrite firstn_length, L; lia).
  assert (LS : length (skipn (Z.to_nat a) bs) = Z.to_nat (b - a)) by (rewrite skipn_length, L; lia).
  rewrite <- (firstn_skipn (Z.to_nat a) bs) in HB.
  apply bytes_at_app in HB. destruct HB as [HB1 HB2].
  rewrite LF in HB2. rewrite (Z2Nat.id a) in HB2 by lia.
  rewrite (Z2Nat.id b) in HW by lia.
  apply (wr_at_split segs m A a b ltac:(lia)) in HW. destruct HW as [HW1 HW2].
  split; apply rw_cb_iff.
  - split; [exact LF|]. split; [exact HB1|]. rewrite (Z2Nat.id a) by lia. exact HW1.
  - split; [exact LS|]. split; [exact HB2|]. rewrite (Z2Nat.id (b - a)) by lia. exact HW2.
Qed.

Lemma cb_split2 : forall segs m A (a b c : Z) bs, 0 <= a -> 0 <= b -> c = a + b ->
  rw_cells segs m A [CB (Z.to_nat c) bs] ->
  rw_cells segs m A [CB (Z.to_nat a) (firstn (Z.to_nat a) bs)] /\
  rw_cells segs m (A + a) [CB (Z.to_nat b) (skipn (Z.to_nat a) bs)].
Proof.
  intros segs m A a b c bs Ha Hb Hc H. subst c.
  destruct (cb_split segs m A a (a + b) bs ltac:(lia) H) as [H1 H2].
  split; [exact H1|]. replace (a + b - a) with b in H2 by lia. exact H2.
Qed.

Lemma cb_join : forall segs m A (a b : Z) bs cs, 0 <= a -> 0 <= b ->
  rw_cells segs m A [CB (Z.to_nat a) bs] ->
  rw_cells segs m (A + a) [CB (Z.to_nat b) cs] ->
  rw_cells segs m A [CB (Z.to_nat (a + b)) (bs ++ cs)].
Proof.
  intros segs m A a b bs cs Ha Hb H1 H2.
  apply rw_cb_iff in H1. destruct H1 as (L1 & B1 & W1).
  apply rw_cb_iff in H2. destruct H2 as (L2 & B2 & W2).
  rewrite (Z2Nat.id a) in W1 by lia. rewrite (Z2Nat.id b) in W2 by lia.
  apply rw_cb_iff. split; [rewrite app_length, L1, L2; lia|]. split.
  - apply bytes_at_app. split; [exact B1|]. rewrite L1, (Z2Nat.id a) by lia. exact B2.
  - rewrite (Z2Nat.id (a + b)) by lia.
    apply (wr_at_split segs m A a (a + b) ltac:(lia)). split; [exact W1|].
    replace (a + b - a) with b by lia. exact W2.
Qed.

Lemma cb_read : forall segs m A (k : nat) bs,
  rw_cells segs m A [CB k bs] -> ov_read_bytes segs m (wa A) k = Some bs.
Proof.
  intros segs m A k bs H.
  pose proof (rw_cells_read segs m A [CB k bs] 0%nat (CB k bs) H eq_refl) as R.
  cbn [csize cbytes Z.of_nat] in R. rewrite Z.add_0_r in R. exact R.
Qed.

Lemma cb_len : forall segs m A (k : nat) bs, rw_cells segs m A [CB k bs] -> length bs = k.
Proof. intros segs m A k bs H. apply rw_cb_iff in H. tauto. Qed.

Lemma not_ro_sub : forall segs A nn a b,
  RoAdapt.not_ro segs A nn -> A <= a -> 0 <= b -> a + b <= A + nn -> RoAdapt.not_ro segs a b.
Proof.
  intros segs A nn a b H HA Hb Hab. unfold RoAdapt.not_ro in *.
  intros i Hi. replace (a + i) with (A + (a - A + i)) by lia. apply H. lia.
Qed.

(* The little-endian value of a byte run is 0 only when every byte is 0. *)
Lemma le_val_zero : forall bs : list byte,
  le_val (map bv_unsigned bs) = 0 -> bs = repeat (Z_to_bv 8 0) (length bs).
Proof.
  induction bs as [|b bs IH]; intros H; [reflexivity|].
  cbn [map le_val length repeat] in *.
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8)%Z with 256%Z in Hb.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Hr.
  assert (Hge : 0 <= le_val (map bv_unsigned bs)) by lia.
  assert (Hb0 : bv_unsigned b = 0) by lia.
  assert (Hl : le_val (map bv_unsigned bs) = 0) by lia.
  f_equal.
  - apply bv_eq. rewrite Hb0. reflexivity.
  - apply IH. exact Hl.
Qed.

(* srli by 12: the test "pp - p < 4096?". *)
Lemma shr12_ge : forall z, 0 <= z -> Z.shiftr z 12 <> 0 -> 4096 <= z.
Proof.
  intros z Hz H. destruct (Z.lt_ge_cases z 4096) as [L|L]; [|exact L].
  exfalso. apply H. rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 12) with 4096 by (vm_compute; reflexivity).
  apply Z.div_small. lia.
Qed.

(* page alignment arithmetic *)
Lemma al_sub : forall a, a mod 4096 = 0 -> (a - 4096) mod 4096 = 0.
Proof.
  intros a H. replace (a - 4096) with (a + (-1) * 4096) by lia.
  rewrite Z.mod_add by lia. exact H.
Qed.

Lemma al_floor : forall a, (a - a mod 4096) mod 4096 = 0.
Proof.
  intros a. rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity.
Qed.

(* and with 0xfffffffffffff000 *)
Lemma land_pair : forall x a b, Z.land (Z.land x a) (Z.land x b) = Z.land x (Z.land a b).
Proof.
  intros x a b. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.testbit x i), (Z.testbit a i), (Z.testbit b i); reflexivity.
Qed.

Lemma land_lor_r : forall a b c, Z.land a (Z.lor b c) = Z.lor (Z.land a b) (Z.land a c).
Proof.
  intros a b c. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, !Z.lor_spec, !Z.land_spec.
  destruct (Z.testbit a i), (Z.testbit b i), (Z.testbit c i); reflexivity.
Qed.

Lemma land_page : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros x Hx.
  assert (O64 : Z.ones 64 = 18446744073709551615) by (vm_compute; reflexivity).
  assert (O12 : Z.ones 12 = 4095) by (vm_compute; reflexivity).
  assert (SP : Z.lor 18446744073709547520 4095 = 18446744073709551615) by (vm_compute; reflexivity).
  assert (Hx12 : Z.land x 4095 = x mod 4096).
  { rewrite <- O12. rewrite Z.land_ones by lia.
    replace (2 ^ 12) with 4096 by (vm_compute; reflexivity). reflexivity. }
  assert (Hx64 : Z.land x 18446744073709551615 = x).
  { rewrite <- O64. rewrite Z.land_ones by lia. apply Z.mod_small. exact Hx. }
  rewrite <- SP, land_lor_r in Hx64.
  assert (DIS : Z.land (Z.land x 18446744073709547520) (Z.land x 4095) = 0).
  { rewrite land_pair. replace (Z.land 18446744073709547520 4095) with 0 by (vm_compute; reflexivity).
    apply Z.land_0_r. }
  pose proof (Z.add_nocarry_lxor _ _ DIS) as AD.
  rewrite (Z.lxor_lor _ _ DIS) in AD.
  lia.
Qed.

Ltac weq := first [ exact eq_refl | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ].

(* ------------------------------------------------------------------------------------------------------- *)

Section ClearBig.
Variables (sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variables (junk blk : list byte).
Variables (rao s0o s1o : word).
Variable n : Z.

Hypothesis HFR0 : rw_cells rsegs m0 (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao].
Hypothesis Hn : 0 <= n <= CALLOC_BIG_CAP.
Hypothesis BLK : rw_cells rsegs m0 (bv_unsigned s0) [CB (Z.to_nat n) blk].
Hypothesis HSP : bv_unsigned s0 + n <= bv_unsigned sp.
Hypothesis NRO : RoAdapt.not_ro rsegs (bv_unsigned s0) n.
Hypothesis RO0 : MemNorm.ro_agree rsegs m0.

Notation Pz := (bv_unsigned s0).
Notation POST :=
  (clear_post rao (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp s0o s1o s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s0 n m0).

(* The block [p, p+n) with [p, p+k) still unknown and [p+k, p+n) already zero. *)
Definition inv (m : word -> option byte) (k : Z) : Prop :=
  0 <= k <= n /\
  (exists bs, rw_cells rsegs m Pz [CB (Z.to_nat k) bs]) /\
  rw_cells rsegs m (Pz + k) [CB (Z.to_nat (n - k)) (zs (n - k))] /\
  munch [(Pz, Pz + n)] m0 m /\ wmono rsegs m0 m /\ MemNorm.ro_agree rsegs m.

Lemma bnds : 0 <= Pz /\ 0 <= n <= 65536 /\ Pz + n + 32 <= 2^64.
Proof.
  pose proof (zr_word s0) as R0. unfold inr64 in R0.
  pose proof (rw_cells_bound rsegs m0 (bv_unsigned sp) _ HFR0) as BF.
  cbn [cells_size csize Nat.add] in BF.
  unfold CALLOC_BIG_CAP in Hn.
  lia.
Qed.

Lemma inv_rng : forall m k, inv m k -> 0 <= k <= n.
Proof. intros m k H. unfold inv in H. tauto. Qed.

Lemma inv_eq : forall m a b, inv m a -> a = b -> inv m b.
Proof. intros m a b H E. subst b. exact H. Qed.

Lemma inv_frame : forall m k,
  inv m k -> rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao].
Proof.
  intros m k H. pose proof bnds as (B0 & B1 & B2). unfold inv in H.
  destruct H as (Hk & _ & _ & MU & WM & _).
  eapply rw_cells_transport; [exact HFR0 | exact MU | exact WM |].
  cbn [disjoint_from cells_size csize Nat.add]. split; [right; lia | exact I].
Qed.

Lemma inv_init : inv m0 n.
Proof.
  pose proof bnds as (B0 & B1 & B2).
  unfold inv. split; [lia|]. split; [exists blk; exact BLK|].
  split.
  - replace (n - n) with 0 by lia. unfold zs. cbn [Z.to_nat repeat].
    apply rw_cb_iff. split; [reflexivity|]. split.
    + apply bytes_at_nil. lia.
    + unfold wr_at. split; [lia|]. split; [cbn [Z.of_nat]; lia|].
      intros i Hi. cbn [Z.of_nat] in Hi. lia.
  - split; [apply munch_refl|]. split; [apply wmono_refl | exact RO0].
Qed.

(* ---- the tail memset at 0x17390 (a0 = p, a2 = s1 = k), then calloc's return ---- *)
Lemma tail : forall (k : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
    (m : word -> option byte),
  inv m k -> x9 = Z_to_bv 64 k ->
  evt rsegs POST
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x17390) fc None m (seg_rom rsegs)).
Proof.
  intros k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m INV E9.
  pose proof bnds as (B0 & B1 & B2).
  pose proof (inv_rng m k INV) as Hk.
  pose proof (inv_frame m k INV) as FR.
  pose proof (rw_cells_bound _ _ _ _ FR) as BF. cbn [cells_size csize Nat.add] in BF.
  pose proof INV as INV0. unfold inv in INV0.
  destruct INV0 as (_ & (bsj & J) & ZR & MUi & WMi & ROi).
  subst x9.
  do 8 step.
  eapply evt_mono.
  { eapply memset_ro_holds.
    - rewrite unsigned_lit by lia. exact J.
    - rewrite unsigned_lit by lia.
      replace (Z.of_nat (cells_size [CB (Z.to_nat k) bsj])) with k by (cbn [cells_size csize]; lia).
      apply (not_ro_sub rsegs Pz n Pz k NRO); lia.
    - exact ROi. }
  intros ms' PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' &
                  -> & MU' & WM' & RO' & CL').
  rewrite !unsigned_lit in MU' by lia.
  rewrite !unsigned_lit in CL' by lia.
  replace (Z_to_bv 8 (0 mod 256)) with (Z_to_bv 8 0) in CL' by (f_equal; reflexivity).
  assert (ZR' : rw_cells rsegs m' (Pz + k) [CB (Z.to_nat (n - k)) (zs (n - k))]).
  { eapply rw_cells_transport; [exact ZR | exact MU' | exact WM' |].
    cbn [disjoint_from cells_size csize Nat.add]. split; [right; lia | exact I]. }
  assert (CZ : rw_cells rsegs m' Pz [CB (Z.to_nat k) (zs k)]) by (unfold zs; exact CL').
  pose proof (cb_join rsegs m' Pz k (n - k) (zs k) (zs (n - k)) ltac:(lia) ltac:(lia) CZ ZR') as JJ.
  rewrite zs_app in JJ by lia.
  replace (k + (n - k)) with n in JJ by lia.
  unfold zs in JJ.
  unfold clear_post.
  exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m'.
  split; [reflexivity|].
  split.
  { eapply munch_trans; [exact MUi|].
    eapply (munch_weaken [(Pz, Pz + k)] [(Pz, Pz + n)]); [|exact MU'].
    unfold sub_fp. cbn [outside]. intros x [HX _]. split; [lia | exact I]. }
  split; [eapply wmono_trans; [exact WMi | exact WM']|].
  split; [exact RO' | exact JJ].
Qed.

(* ---- a call of memset(p + z, 0, k - z) that turns inv m k into inv m' z ---- *)
Lemma ms_call : forall (z k ret : Z) (Q : machine_state -> Prop)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : word -> option byte),
  inv m k -> 0 <= z <= k ->
  x10 = Z_to_bv 64 (Pz + z) -> x11 = Z_to_bv 64 0 -> x12 = Z_to_bv 64 (k - z) ->
  x1 = Z_to_bv 64 ret -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
  (forall (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : word -> option byte),
     inv m' z ->
     evt rsegs Q
       (MS (mkR (Z_to_bv 64 ret) sp gp tp y5 y6 y7 s0 x9 (Z_to_bv 64 (Pz + z)) y11 y12 y13 y14 y15 y16 y17
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
           F (Z_to_bv 64 ret) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros z k ret Q x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
    INV Hzk E10 E11 E12 E1 Hret Hret2 K.
  pose proof bnds as (B0 & B1 & B2).
  pose proof (inv_rng m k INV) as Hk.
  pose proof INV as INV0. unfold inv in INV0.
  destruct INV0 as (_ & (bsj & J) & ZR & MUi & WMi & ROi).
  destruct (cb_split2 rsegs m Pz z (k - z) k bsj ltac:(lia) ltac:(lia) ltac:(lia) J) as [J1 J2].
  subst x1 x10 x11 x12.
  eapply evt_cut.
  { eapply memset_ro_holds.
    - rewrite !unsigned_lit by lia. exact J2.
    - rewrite !unsigned_lit by lia.
      replace (Z.of_nat (cells_size [CB (Z.to_nat (k - z)) (skipn (Z.to_nat z) bsj)])) with (k - z)
        by (cbn [cells_size csize]; lia).
      apply (not_ro_sub rsegs Pz n (Pz + z) (k - z) NRO); lia.
    - exact ROi. }
  intros ms' PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' &
                  -> & MU' & WM' & RO' & CL').
  rewrite !unsigned_lit in MU' by lia.
  rewrite !unsigned_lit in CL' by lia.
  replace (Z_to_bv 8 (0 mod 256)) with (Z_to_bv 8 0) in CL' by (f_equal; reflexivity).
  rewrite (ret_pc_even ret Hret Hret2).
  apply K.
  assert (ZR2 : rw_cells rsegs m' (Pz + z + (k - z)) [CB (Z.to_nat (n - k)) (zs (n - k))]).
  { replace (Pz + z + (k - z)) with (Pz + k) by lia.
    eapply rw_cells_transport; [exact ZR | exact MU' | exact WM' |].
    cbn [disjoint_from cells_size csize Nat.add]. split; [right; lia | exact I]. }
  assert (CZ : rw_cells rsegs m' (Pz + z) [CB (Z.to_nat (k - z)) (zs (k - z))]) by (unfold zs; exact CL').
  pose proof (cb_join rsegs m' (Pz + z) (k - z) (n - k) (zs (k - z)) (zs (n - k))
                ltac:(lia) ltac:(lia) CZ ZR2) as JJ.
  rewrite zs_app in JJ by lia.
  replace (k - z + (n - k)) with (n - z) in JJ by lia.
  unfold inv. split; [lia|]. split.
  { exists (firstn (Z.to_nat z) bsj).
    eapply rw_cells_transport; [exact J1 | exact MU' | exact WM' |].
    cbn [disjoint_from cells_size csize Nat.add]. split; [left; lia | exact I]. }
  split; [exact JJ|].
  split.
  { eapply munch_trans; [exact MUi|].
    eapply (munch_weaken [(Pz + z, Pz + z + (k - z))] [(Pz, Pz + n)]); [|exact MU'].
    unfold sub_fp. cbn [outside]. intros x [HX _]. split; [lia | exact I]. }
  split; [eapply wmono_trans; [exact WMi | exact WM'] | exact RO'].
Qed.

(* ---- the outer loop head 0x17350 ---- *)
Definition Sat (z : Z) : Prop :=
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : word -> option byte),
    x10 = Z_to_bv 64 (Pz + z) -> inv m z ->
    evt rsegs POST
      (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x17350) fc None m (seg_rom rsegs)).

(* ---- the three "pp - p < 4096?" decisions ---- *)
Lemma dec0 : forall (z : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
    (m : word -> option byte),
  inv m z -> x10 = Z_to_bv 64 (Pz + z) -> (4096 <= z -> Sat z) ->
  evt rsegs POST
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x17328) fc None m (seg_rom rsegs)).
Proof.
  intros z x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m INV E10 HS.
  pose proof bnds as (B0 & B1 & B2). pose proof (inv_rng m z INV) as Hz.
  subst x10. do 3 zstep. if_cases K; zify_cond K.
  - assert (Hge : 4096 <= z) by (apply shr12_ge in K; lia).
    apply (HS Hge); [weq | exact INV].
  - zstep. eapply (tail z); [exact INV | weq].
Qed.

Lemma dec1 : forall (z : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
    (m : word -> option byte),
  inv m z -> x10 = Z_to_bv 64 (Pz + z) -> (4096 <= z -> Sat z) ->
  evt rsegs POST
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x17344) fc None m (seg_rom rsegs)).
Proof.
  intros z x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m INV E10 HS.
  pose proof bnds as (B0 & B1 & B2). pose proof (inv_rng m z INV) as Hz.
  subst x10. do 3 zstep. if_cases K; zify_cond K.
  - eapply (tail z); [exact INV | weq].
  - assert (Hge : 4096 <= z) by (apply shr12_ge in K; lia).
    apply (HS Hge); [weq | exact INV].
Qed.

Lemma dec2 : forall (z : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
    (m : word -> option byte),
  inv m z -> x10 = Z_to_bv 64 (Pz + z) -> (4096 <= z -> Sat z) ->
  evt rsegs POST
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x17384) fc None m (seg_rom rsegs)).
Proof.
  intros z x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m INV E10 HS.
  pose proof bnds as (B0 & B1 & B2). pose proof (inv_rng m z INV) as Hz.
  subst x10. do 3 zstep. if_cases K; zify_cond K.
  - assert (Hge : 4096 <= z) by (apply shr12_ge in K; lia).
    apply (HS Hge); [weq | exact INV].
  - eapply (tail z); [exact INV | weq].
Qed.

(* ---- the scan's break at 0x17338: memset(pp' - i, 0, i) ---- *)
Lemma brk : forall (z0 i : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
    (m : word -> option byte),
  0 < i <= 4096 -> 4096 <= z0 <= n ->
  (4096 <= z0 - 4096 -> Sat (z0 - 4096)) ->
  inv m (z0 - 4096 + i) ->
  x10 = Z_to_bv 64 (Pz + (z0 - 4096 + i)) -> x12 = Z_to_bv 64 i ->
  evt rsegs POST
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x17338) fc None m (seg_rom rsegs)).
Proof.
  intros z0 i x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
    Hi Hz0 HS INV E10 E12.
  pose proof bnds as (B0 & B1 & B2). pose proof (inv_rng m _ INV) as Hc.
  subst x10 x12. do 3 zstep.
  eapply (ms_call (z0 - 4096) (z0 - 4096 + i) 0x17344);
    [ exact INV | lia | weq | weq | weq | weq | lia | reflexivity | ].
  intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m' INV'.
  eapply (dec1 (z0 - 4096)); [exact INV' | weq | exact HS].
Qed.

(* ---- a whole zero page at 0x17378: memset(pp - 4096, 0, 0) ---- *)
Lemma full : forall (z0 : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
    (m : word -> option byte),
  4096 <= z0 <= n ->
  (4096 <= z0 - 4096 -> Sat (z0 - 4096)) ->
  inv m (z0 - 4096) ->
  x11 = Z_to_bv 64 (Pz + z0 - 4096) -> x12 = Z_to_bv 64 0 ->
  evt rsegs POST
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x17378) fc None m (seg_rom rsegs)).
Proof.
  intros z0 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
    Hz0 HS INV E11 E12.
  pose proof bnds as (B0 & B1 & B2). pose proof (inv_rng m _ INV) as Hc.
  subst x11 x12. do 3 zstep.
  eapply (ms_call (z0 - 4096) (z0 - 4096) 0x17384);
    [ exact INV | lia | weq | weq | weq | weq | lia | reflexivity | ].
  intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m' INV'.
  eapply (dec2 (z0 - 4096)); [exact INV' | weq | exact HS].
Qed.

(* ---- the two words the scan reads at [p + c - 16, p + c) ---- *)
Lemma scan_read : forall (m : word -> option byte) (c : Z),
  16 <= c -> inv m c ->
  exists b1 b2,
    length b1 = 8%nat /\ length b2 = 8%nat /\
    ov_read_bytes rsegs m (wa (Pz + (c - 16))) 8 = Some b1 /\
    ov_read_bytes rsegs m (wa (Pz + (c - 16) + 8)) 8 = Some b2 /\
    (b1 = zs 8 -> b2 = zs 8 -> inv m (c - 16)).
Proof.
  intros m c Hc INV.
  pose proof bnds as (B0 & B1 & B2).
  pose proof (inv_rng m c INV) as Hrng.
  pose proof INV as INV0. unfold inv in INV0.
  destruct INV0 as (_ & (bsj & J) & ZR & MUi & WMi & ROi).
  destruct (cb_split2 rsegs m Pz (c - 16) 16 c bsj ltac:(lia) ltac:(lia) ltac:(lia) J) as [J1 J2].
  remember (skipn (Z.to_nat (c - 16)) bsj) as w eqn:Hw. clear Hw.
  destruct (cb_split2 rsegs m (Pz + (c - 16)) 8 8 16 w ltac:(lia) ltac:(lia) ltac:(lia) J2) as [J3 J4].
  exists (firstn (Z.to_nat 8) w), (skipn (Z.to_nat 8) w).
  split; [exact (cb_len _ _ _ _ _ J3)|].
  split; [exact (cb_len _ _ _ _ _ J4)|].
  split; [exact (cb_read _ _ _ _ _ J3)|].
  split; [exact (cb_read _ _ _ _ _ J4)|].
  intros H1 H2. rewrite H1 in J3. rewrite H2 in J4.
  unfold zs in J3, J4.
  pose proof (cb_join rsegs m (Pz + (c - 16)) 8 8 (repeat (Z_to_bv 8 0) (Z.to_nat 8))
                (repeat (Z_to_bv 8 0) (Z.to_nat 8)) ltac:(lia) ltac:(lia) J3 J4) as J16.
  change (repeat (Z_to_bv 8 0) (Z.to_nat 8)) with (zs 8) in J16.
  rewrite zs_app in J16 by lia.
  replace (8 + 8) with 16 in J16 by lia.
  assert (ZR2 : rw_cells rsegs m (Pz + (c - 16) + 16) [CB (Z.to_nat (n - c)) (zs (n - c))])
    by (replace (Pz + (c - 16) + 16) with (Pz + c) by lia; exact ZR).
  pose proof (cb_join rsegs m (Pz + (c - 16)) 16 (n - c) (zs 16) (zs (n - c))
                ltac:(lia) ltac:(lia) J16 ZR2) as JJ.
  rewrite zs_app in JJ by lia.
  replace (16 + (n - c)) with (n - (c - 16)) in JJ by lia.
  unfold inv. split; [lia|]. split; [exists (firstn (Z.to_nat (c - 16)) bsj); exact J1|].
  split; [exact JJ|]. split; [exact MUi|]. split; [exact WMi | exact ROi].
Qed.

(* ---- the inner scan at 0x1735c ---- *)
Lemma scan : forall (j : nat) (z0 i : Z)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : word -> option byte),
  Z.to_nat i = (16 * j)%nat -> 0 < i <= 4096 ->
  4096 <= z0 <= n ->
  (4096 <= z0 - 4096 -> Sat (z0 - 4096)) ->
  inv m (z0 - 4096 + i) ->
  x10 = Z_to_bv 64 (Pz + (z0 - 4096 + i)) ->
  x11 = Z_to_bv 64 (Pz + z0 - 4096) -> x12 = Z_to_bv 64 i ->
  evt rsegs POST
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1735c) fc None m (seg_rom rsegs)).
Proof.
  induction j as [j IH] using lt_wf_ind.
  intros z0 i x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
    Hj Hi Hz0 HS INV E10 E11 E12.
  pose proof bnds as (B0 & B1 & B2).
  pose proof (inv_rng m _ INV) as Hc.
  destruct j as [|j']; [exfalso; lia|].
  assert (Hi16 : 16 <= i) by lia.
  subst x10 x11 x12.
  destruct (scan_read m (z0 - 4096 + i) ltac:(lia) INV) as (b1 & b2 & L1 & L2 & RD1 & RD2 & ZB).
  pose proof (le_val_range (map bv_unsigned b1) (bytes_ok_map b1)) as WR1.
  pose proof (le_val_range (map bv_unsigned b2) (bytes_ok_map b2)) as WR2.
  rewrite length_map, L1 in WR1. rewrite length_map, L2 in WR2.
  change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR1, WR2.
  do 3 zstep.
  rewrite (load8_le_val b1 L1), (load8_le_val b2 L2).
  zstep. if_cases K; zify_cond K.
  - (* a non-zero 16 bytes: break to 0x17338 *)
    eapply (brk z0 i); [lia | lia | exact HS | exact INV | weq | weq].
  - (* 16 zero bytes *)
    apply Z.lor_eq_0_iff in K. destruct K as [K1 K2].
    pose proof (le_val_zero b1 K1) as Hz1. rewrite L1 in Hz1.
    pose proof (le_val_zero b2 K2) as Hz2. rewrite L2 in Hz2.
    assert (INV' : inv m (z0 - 4096 + i - 16)) by (apply ZB; [exact Hz1 | exact Hz2]).
    do 3 zstep. if_cases K3; zify_cond K3.
    + (* more to scan *)
      eapply (IH j' ltac:(lia) z0 (i - 16));
        [ lia | lia | lia | exact HS
        | eapply inv_eq; [exact INV' | lia]
        | weq | weq | weq ].
    + (* the whole page was zero *)
      eapply (full z0); [lia | exact HS | eapply inv_eq; [exact INV' | lia] | weq | weq].
Qed.

(* ---- the outer loop: Sat z for every aligned z >= 4096 ---- *)
Lemma outer : forall (jb : nat) (z : Z),
  (Z.to_nat z <= jb)%nat -> 4096 <= z <= n -> (Pz + z) mod 4096 = 0 -> Sat z.
Proof.
  induction jb as [jb IH] using lt_wf_ind.
  intros z Hjb Hz Hal.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m E10 INV.
  pose proof bnds as (B0 & B1 & B2).
  subst x10.
  assert (HS : 4096 <= z - 4096 -> Sat (z - 4096)).
  { intros HH. apply (IH (Z.to_nat (z - 4096)) ltac:(lia) (z - 4096) ltac:(lia) ltac:(lia)).
    replace (Pz + (z - 4096)) with (Pz + z - 4096) by lia. apply al_sub. exact Hal. }
  do 3 zstep.
  eapply (scan 256%nat z 4096);
    [ reflexivity | lia | lia | exact HS | eapply inv_eq; [exact INV | lia] | weq | weq | weq ].
Qed.

(* ---- 0x17304: the clear decision, then either the tail memset or mal0_clear's page loop ---- *)
Lemma clear_main : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  evt rsegs POST
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x17304) fc None m0 (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
  pose proof bnds as (B0 & B1 & B2).
  pose proof inv_init as INV.
  do 2 zstep. if_cases K0; zify_cond K0.
  - eapply (tail n); [exact INV | reflexivity].
  - assert (Hge : 4096 <= n) by (apply shr12_ge in K0; lia).
    do 7 zstep.
    eapply (ms_call (n - (Pz + n) mod 4096) n 0x17328);
      [ exact INV | lia
      | rewrite ?unsigned_lit by lia; rewrite land_page by lia; weq
      | weq | weq | weq | lia | reflexivity | ].
    intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m' INV'.
    eapply (dec0 (n - (Pz + n) mod 4096)); [exact INV' | weq |].
    intros HH.
    apply (outer (Z.to_nat (n - (Pz + n) mod 4096)) (n - (Pz + n) mod 4096) ltac:(lia) ltac:(lia)).
    replace (Pz + (n - (Pz + n) mod 4096)) with (Pz + n - (Pz + n) mod 4096) by lia.
    apply al_floor.
Qed.

End ClearBig.

(* At 0x17304: s0 = the block p, s1 = mn = m * n; calloc's frame [sp, sp + 32) holds (junk, s1o, s0o, rao). *)
Lemma run_clear_big : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk blk : list byte) (rao s0o s1o : word) (mn : Z),
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  0 <= mn <= CALLOC_BIG_CAP ->
  rw_cells rsegs m (bv_unsigned s0) [CB (Z.to_nat mn) blk] ->
  bv_unsigned s0 + mn <= bv_unsigned sp ->
  RoAdapt.not_ro rsegs (bv_unsigned s0) mn ->
  MemNorm.ro_agree rsegs m ->
  evt rsegs (clear_post rao (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp s0o s1o s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s0 mn m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 mn) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17304) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk blk rao s0o s1o mn FR Hmn BLK HSP NRO RO.
  eapply clear_main; eassumption.
Qed.
