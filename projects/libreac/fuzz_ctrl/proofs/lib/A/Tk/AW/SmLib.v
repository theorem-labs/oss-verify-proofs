From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Tac Image ZBridge Arr SysStep.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AK Require Import StepFast StoreFast LiaFix.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn.
Local Unset Lia Cache. Local Unset Nia Cache. Local Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

#[local] Abbreviation mem := (word -> option byte).

Lemma ul_msteps : forall s s', msteps rsegs s s' -> LE.msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply LE.msteps_refl|].
  eapply LE.msteps_cons; [exact Hs| exact IH].
Qed.

Lemma ul_entry : forall Q R F pc fc (m : mem),
  evt rsegs Q (MS R F pc fc None m (seg_rom rsegs)) -> LE.evt rsegs Q (LM.MS R F pc fc None m (seg_rom rsegs)).
Proof. intros Q R F pc fc m (ms' & H & HQ). exists ms'. split; [exact (ul_msteps _ _ H)| exact HQ]. Qed.

Lemma mkR_ul : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  LF.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 =
  mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof. reflexivity. Qed.

Lemma ro8 (m : mem) a v : bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma ro4 (m : mem) a v : bytes_at rsegs m a (le4 v) -> ro_cells rsegs m a [C4 v].
Proof. intros H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma ro1 (m : mem) a b : bytes_at rsegs m a [b] -> ro_cells rsegs m a [C1 b].
Proof. intros H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes app]. exact H. Qed.

Lemma ro_cons8 (m : mem) a v cs : bytes_at rsegs m a (le8 v) -> ro_cells rsegs m (a + 8) cs -> ro_cells rsegs m a (C8 v :: cs).
Proof.
  intros H [W B]. split; [exact (conj I W)|]. cbn [cells_bytes cbytes].
  apply (proj2 (bytes_at_app rsegs m a (le8 v) (cells_bytes cs))). split; [exact H|]. rewrite length_le8. exact B.
Qed.

Lemma ro_bound (m : mem) a cs : ro_cells rsegs m a cs -> 0 <= a /\ a + Z.of_nat (cells_size cs) <= 2^64.
Proof. intros [W B]. apply bytes_at_bound in B. rewrite cells_bytes_length in B by exact W. exact B. Qed.

Lemma m2s_of_asan (m : mem) : asan_cells m -> m2s_cells m.
Proof.
  intros (K1 & K2 & _ & _ & _ & _ & _ & _ & K9 & K10 & K11 & K12 & K13 & K14 & _).
  split; [|split].
  - apply ro_cons8; [exact K2|]. apply ro_cons8; [exact K12|]. apply ro_cons8; [exact K14|]. apply ro8. exact K10.
  - apply ro8. exact K1.
  - apply ro_cons8; [exact K9|]. apply ro_cons8; [exact K11|]. apply ro8. exact K13.
Qed.

Lemma tls_leaf (m : mem) TP DT TS C T DB k : asan_cells m -> asan_tls_cells m TP DT TS C T DB k ->
  exists tb te, leaf_cells TP (bv_unsigned DT) (bv_unsigned TS) (bv_unsigned C) (bv_unsigned T) (bv_unsigned DB) k tb te m.
Proof.
  intros (_ & _ & INI & _).
  intros (H1 & H2 & H3 & H4 & H5 & Hk & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15 & H16 & H17 & HDB & H19).
  exists tb, te.
  assert (R1 : ro_cells rsegs m 0xa07b0 [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (2^64 - 2048))]).
  { replace (Z_to_bv 64 (2^64 - 2048)) with (Z_to_bv 64 (-2048)) by (apply bv_eq; vm_compute; reflexivity).
    pose proof (H1 : bytes_at rsegs m 0xa07b0 (le8 (Z_to_bv 64 1) ++ le8 (Z_to_bv 64 (-2048)))) as B.
    apply (proj1 (bytes_at_app rsegs m _ _ _)) in B as [B1 B2]. rewrite length_le8 in B2.
    apply ro_cons8; [exact B1|]. apply ro8. exact B2. }
  assert (R2 : ro_cells rsegs m (TP + -8) [C8 (Z_to_bv 64 (bv_unsigned DT))]) by (rewrite Z_to_bv_lit_self; apply ro8; exact H3).
  assert (R3 : ro_cells rsegs m (bv_unsigned DT + 8) [C8 (Z_to_bv 64 (TP + 2048))]) by (apply ro8; exact H4).
  assert (R4 : ro_cells rsegs m 0xa9558 [C1 (Z_to_bv 8 1)]) by (apply ro1; exact INI).
  assert (R5 : ro_cells rsegs m 0xa80e0 [C1 (Z_to_bv 8 1)]) by (apply ro1; exact H5).
  assert (R6 : ro_cells rsegs m 0xa80e4 [C4 (Z_to_bv 64 k)]) by (apply ro4; exact H7).
  assert (R7 : ro_cells rsegs m (TP + -88) [C8 (Z_to_bv 64 (bv_unsigned TS))]) by (rewrite Z_to_bv_lit_self; apply ro8; exact H8).
  assert (R8 : ro_cells rsegs m (bv_unsigned TS + 8 * k) [C8 (Z_to_bv 64 (bv_unsigned C))]) by (rewrite Z_to_bv_lit_self; apply ro8; exact H9).
  assert (R9 : ro_cells rsegs m (bv_unsigned C + 152) [C8 (Z_to_bv 64 (bv_unsigned T))]) by (rewrite Z_to_bv_lit_self; apply ro8; exact H10).
  assert (R10 : ro_cells rsegs m (bv_unsigned T + 48) [C8 tb; C8 te]).
  { pose proof (H11 : bytes_at rsegs m (bv_unsigned T + 48) (le8 tb ++ le8 te)) as B.
    apply (proj1 (bytes_at_app rsegs m _ _ _)) in B as [B1 B2]. rewrite length_le8 in B2.
    apply ro_cons8; [exact B1|]. apply ro8. exact B2. }
  assert (R11 : ro_cells rsegs m 0xa1870 [C8 (Z_to_bv 64 0x98800)]) by (apply ro8; exact H2).
  assert (R12 : ro_cells rsegs m 0x9fac0 [C8 (Z_to_bv 64 0x13a3a8)]) by (apply ro8; exact H12).
  assert (R13 : ro_cells rsegs m 0x13a431 [C1 (Z_to_bv 8 1)]) by (apply ro1; exact H13).
  assert (R14 : ro_cells rsegs m 0x9fb20 [C8 (Z_to_bv 64 0x138318)]) by (apply ro8; exact H14).
  assert (R15 : ro_cells rsegs m 0x138318 [C4 (Z_to_bv 64 0)]) by (apply ro4; exact H15).
  assert (R16 : ro_cells rsegs m 0xa07c0 [C8 (Z_to_bv 64 8)]) by (apply ro8; exact H16).
  assert (R17 : ro_cells rsegs m (TP + 8) [C8 (Z_to_bv 64 (bv_unsigned DB))]) by (rewrite Z_to_bv_lit_self; apply ro8; exact H17).
  assert (R18 : ro_cells rsegs m (bv_unsigned DB + 24) [C8 (Z_to_bv 64 TP)]) by (apply ro8; exact H19).
  pose proof (ro_bound _ _ _ R2) as X2. pose proof (ro_bound _ _ _ R3) as X3. pose proof (ro_bound _ _ _ R7) as X7.
  pose proof (ro_bound _ _ _ R8) as X8. pose proof (ro_bound _ _ _ R9) as X9. pose proof (ro_bound _ _ _ R10) as X10.
  pose proof (ro_bound _ _ _ R17) as X17. pose proof (ro_bound _ _ _ R18) as X18.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X2, X3, X7, X8, X9, X10, X17, X18.
  pose proof (bv_unsigned_in_range 64 DT) as UDT. pose proof (bv_unsigned_in_range 64 TS) as UTS.
  pose proof (bv_unsigned_in_range 64 C) as UC. pose proof (bv_unsigned_in_range 64 T) as UT.
  pose proof (bv_unsigned_in_range 64 DB) as UDB.
  unfold bv_modulus in UDT, UTS, UC, UT, UDB. cbn in UDT, UTS, UC, UT, UDB.
  unfold leaf_cells. repeat (split; [eassumption|]). lia.
Qed.

Lemma stk_rw (m : mem) lo hi A cs : stk rsegs m lo hi -> ro_cells rsegs m A cs -> lo <= A ->
  A + Z.of_nat (cells_size cs) <= hi -> rw_cells rsegs m A cs.
Proof.
  intros (S0 & S1 & S) R H1 H2. split; [exact R|].
  pose proof (ro_bound _ _ _ R) as B.
  split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (S (A + i) ltac:(lia))).
Qed.

Lemma stk_junk (m : mem) lo hi A (n : nat) : stk rsegs m lo hi -> lo <= A -> A + Z.of_nat n <= hi ->
  exists bs, rw_cells rsegs m A [CB n bs].
Proof.
  intros S H1 H2. destruct (stk_split rsegs m lo (A + Z.of_nat n) hi S ltac:(lia)) as [S1 _].
  destruct (stk_carve rsegs m lo (A + Z.of_nat n) n S1 ltac:(lia)) as [_ (bs & R)].
  replace (A + Z.of_nat n - Z.of_nat n) with A in R by lia. exists bs. exact R.
Qed.

Lemma stk_sub (m : mem) lo hi a b : stk rsegs m lo hi -> lo <= a -> a <= b -> b <= hi -> stk rsegs m a b.
Proof.
  intros S H1 H2 H3. destruct (stk_split rsegs m lo a hi S ltac:(lia)) as [_ S1].
  destruct (stk_split rsegs m a b hi S1 ltac:(lia)) as [S2 _]. exact S2.
Qed.

Lemma mrd_read1 (m : mem) x b : mrd rsegs m (wa x) = Some b -> 0 <= x -> x + 1 <= 2^64 ->
  ov_read_bytes rsegs m (wa x) 1 = Some [b].
Proof.
  intros H H0 H1.
  assert (B : bytes_at rsegs m x [b]).
  { split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. assert (i = 0)%nat as -> by lia. cbn. rewrite Z.add_0_r. exact H. }
  pose proof (bytes_at_ov_read rsegs m x [b] 0 1 B ltac:(cbn; lia)) as R.
  cbn [firstn skipn] in R. rewrite Nat2Z.inj_0, Z.add_0_r in R. exact R.
Qed.

Lemma flag_read (m : mem) A (flags : list byte) pos : bytes_at rsegs m A flags -> 0 <= pos < Z.of_nat (length flags) ->
  Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
  exists b, nth_error flags (Z.to_nat pos) = Some b /\ (b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1)
    /\ ov_read_bytes rsegs m (wa (A + pos)) 1 = Some [b].
Proof.
  intros (B0 & B1 & B) Hp F01.
  destruct (nth_error flags (Z.to_nat pos)) as [b|] eqn:E.
  2:{ apply nth_error_None in E. lia. }
  exists b. split; [reflexivity|]. split.
  - rewrite Forall_forall in F01. apply F01. eapply nth_error_In. exact E.
  - apply mrd_read1; [| lia | lia]. pose proof (B (Z.to_nat pos) ltac:(lia)) as R.
    rewrite Z2Nat.id in R by lia. rewrite R. exact E.
Qed.

Lemma app_in_shadow a : app_mem a -> in_shadow (shadow_addr a).
Proof.
  unfold app_mem, in_shadow, shadow_addr, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END.
  intros [H|H]; [left|right]; Z.div_mod_to_equations; lia.
Qed.

Lemma shadow_addr_add a x : shadow_addr (a + 8 * x) = shadow_addr a + x.
Proof. unfold shadow_addr. rewrite (Z.mul_comm 8 x), Z.div_add by lia. lia. Qed.

(* route (C): the shadow bytes shadow_stk READS -- the n shadow bytes of the 8 * n application bytes at A.  Its proof
   reads the premise at exactly these addresses (`SRW y _ (S y Hy)` under `shadow_addr A <= y < shadow_addr A + n`, the
   stk range it returns) and nowhere else. *)
Definition shadow_stk_shadow_R (A n : Z) : Z -> Prop := fun y => shadow_addr A <= y < shadow_addr A + n.

Lemma shadow_stk_on (m : mem) A n : A.ShadowRwOn.shadow_rw_on (shadow_stk_shadow_R A n) m -> 0 <= A -> A mod 8 = 0 ->
  0 < n -> (forall x, A <= x < A + 8 * n -> app_mem x) -> stk rsegs m (shadow_addr A) (shadow_addr A + n).
Proof.
  intros SRW HA HM Hn APP.
  assert (E : forall y, shadow_addr A <= y < shadow_addr A + n -> shadow_addr (A + 8 * (y - shadow_addr A)) = y).
  { intros y Hy. rewrite shadow_addr_add. lia. }
  assert (S : forall y, shadow_addr A <= y < shadow_addr A + n -> in_shadow y).
  { intros y Hy. rewrite <- (E y Hy). apply app_in_shadow, APP. lia. }
  pose proof (app_in_shadow _ (APP (A + 8 * (n - 1)) ltac:(lia))) as SL. rewrite shadow_addr_add in SL.
  assert (S0 : 0 <= shadow_addr A) by (unfold shadow_addr, ASAN_K; pose proof (Z.div_pos A 8 HA ltac:(lia)); lia).
  split; [exact S0|]. split.
  - unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in SL. change (2 ^ 64) with 18446744073709551616. lia.
  - intros y Hy. exact (SRW y Hy (S y Hy)).
Qed.

Lemma shadow_stk (m : mem) A n : shadow_rw m -> 0 <= A -> A mod 8 = 0 -> 0 < n ->
  (forall x, A <= x < A + 8 * n -> app_mem x) -> stk rsegs m (shadow_addr A) (shadow_addr A + n).
Proof. intros SRW. exact (shadow_stk_on m A n (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m SRW)). Qed.

Lemma app_shadow_apart lo hi a n : (forall x, lo <= x < hi -> app_mem x) -> lo < hi ->
  (forall y, a <= y < a + n -> in_shadow y) -> 0 < n -> hi <= a \/ a + n <= lo.
Proof.
  intros APP Hlh SH Hn.
  assert (G1 : ~ (lo <= 0x7fff8000 < hi)).
  { intros G. pose proof (APP _ G) as X. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X. lia. }
  assert (G2 : ~ (a <= 0x8fff7000 < a + n)).
  { intros G. pose proof (SH _ G) as X. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
  pose proof (APP lo ltac:(lia)) as A1. pose proof (APP (hi - 1) ltac:(lia)) as A2.
  pose proof (SH a ltac:(lia)) as S1. pose proof (SH (a + n - 1) ltac:(lia)) as S2.
  unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *.
  lia.
Qed.

Lemma shadow_range_in A n : 0 <= A -> A mod 8 = 0 -> 0 < n -> (forall x, A <= x < A + 8 * n -> app_mem x) ->
  forall y, shadow_addr A <= y < shadow_addr A + n -> in_shadow y.
Proof.
  intros HA HM Hn APP y Hy.
  replace y with (shadow_addr (A + 8 * (y - shadow_addr A))) by (rewrite shadow_addr_add; lia).
  apply app_in_shadow, APP. lia.
Qed.

Lemma pow_split c : (c <= 14)%nat -> 2 ^ Z.of_nat c * 2 ^ (14 - Z.of_nat c) = 2 ^ 14.
Proof. intros Hc. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma fs_frame_bounds FS c j : (c <= 14)%nat -> 0 <= j < fs_M c ->
  FS + 36864 + Z.of_nat c * 2^20 <= fs_frame FS c j /\ fs_frame FS c j + fs_B c <= FS + 36864 + (Z.of_nat c + 1) * 2^20.
Proof.
  intros Hc Hj. unfold fs_frame, fs_B, fs_M in *. pose proof (pow_split c Hc) as P.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat c) ltac:(lia) ltac:(lia)) as P1.
  set (p := 2 ^ Z.of_nat c) in *. set (q := 2 ^ (14 - Z.of_nat c)) in *.
  assert (Q1 : (j + 1) * p <= q * p) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Q2 : 0 <= j * p) by (apply Z.mul_nonneg_nonneg; lia).
  replace (j * (64 * p)) with (64 * (j * p)) by ring.
  assert (Q3 : j * p + p <= 2 ^ 14) by lia.
  change (2 ^ 20) with 1048576. change (2 ^ 14) with 16384 in Q3. lia.
Qed.

Lemma fs_frames_apart FS c j c' j' : (c <= 14)%nat -> (c' <= 14)%nat -> 0 <= j < fs_M c -> 0 <= j' < fs_M c' ->
  (c' <> c \/ j' <> j) ->
  fs_frame FS c' j' + fs_B c' <= fs_frame FS c j \/ fs_frame FS c j + fs_B c <= fs_frame FS c' j'.
Proof.
  intros Hc Hc' Hj Hj' D.
  pose proof (fs_frame_bounds FS c j Hc Hj) as [A1 A2]. pose proof (fs_frame_bounds FS c' j' Hc' Hj') as [B1 B2].
  destruct (Nat.eq_dec c c') as [<-|NE].
  - destruct D as [D|D]; [exfalso; apply D; reflexivity|].
    unfold fs_frame, fs_B. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat c) ltac:(lia) ltac:(lia)) as P1.
    set (p := 2 ^ Z.of_nat c) in *.
    destruct (Z_lt_ge_dec j j') as [L|L].
    + right. assert ((j + 1) * p <= j' * p) by (apply Z.mul_le_mono_nonneg_r; lia).
      replace (j * (64 * p)) with (64 * (j * p)) by ring. replace (j' * (64 * p)) with (64 * (j' * p)) by ring. lia.
    + left. assert ((j' + 1) * p <= j * p) by (apply Z.mul_le_mono_nonneg_r; lia).
      replace (j * (64 * p)) with (64 * (j * p)) by ring. replace (j' * (64 * p)) with (64 * (j' * p)) by ring. lia.
  - assert (Z.of_nat c < Z.of_nat c' \/ Z.of_nat c' < Z.of_nat c) by lia. lia.
Qed.

Lemma addressable_zero (m : mem) fr L n : 0 <= fr -> fr mod 8 = 0 -> 0 <= L <= 8 * n -> fr + L <= APPMEM_END ->
  (forall i, 0 <= i < L -> app_mem (fr + i)) ->
  bytes_at rsegs m (shadow_addr fr) (repeat (Z_to_bv 8 0) (Z.to_nat n)) -> addressable m fr L.
Proof.
  intros H0 HM HL HE APP (B0 & B1 & B). split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply APP; lia|]. exists (Z_to_bv 8 0).
  assert (E : shadow_addr (fr + i) = shadow_addr fr + Z.of_nat (Z.to_nat (i / 8))).
  { rewrite Z2Nat.id by (apply Z.div_pos; lia). unfold shadow_addr.
    rewrite (Z.div_mod fr 8) at 1 by lia. rewrite HM, Z.add_0_r, (Z.mul_comm 8 (fr / 8)), Z.div_add_l by lia. lia. }
  pose proof (B (Z.to_nat (i / 8))) as R. rewrite repeat_length in R.
  assert (LT : (Z.to_nat (i / 8) < Z.to_nat n)%nat).
  { assert (i / 8 < n) by (apply Z.div_lt_upper_bound; lia). pose proof (Z.div_pos i 8 ltac:(lia) ltac:(lia)). lia. }
  specialize (R LT). rewrite nth_error_repeat in R by exact LT.
  split.
  - rewrite E. exact R.
  - left. reflexivity.
Qed.

Lemma frame_ok (c : nat) K (sp : word) L FS j (m m' : mem) :
  (c <= 6)%nat -> 0 <= j < fs_M c -> 1 <= L <= fs_B c ->
  FS mod 4096 = 0 -> ASAN_GT <= FS -> (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  stk rsegs m' FS (FS + FS_SIZE) -> FS + FS_SIZE <= bv_unsigned sp - K ->
  bytes_at rsegs m' (fs_flag FS c j) [Z_to_bv 8 1] ->
  bytes_at rsegs m' (fs_frame FS c j + 24) (le8 sp) ->
  bytes_at rsegs m' (fs_frame FS c j + fs_B c - 8) (le8 (Z_to_bv 64 (fs_flag FS c j))) ->
  bytes_at rsegs m' (shadow_addr (fs_frame FS c j)) (repeat (Z_to_bv 8 0) (Z.to_nat (fs_B c / 8))) ->
  munch [(fs_hint FS c, fs_hint FS c + 8); (fs_flag FS c j, fs_flag FS c j + 1); (fs_frame FS c j + 24, fs_frame FS c j + 32);
         (fs_frame FS c j + fs_B c - 8, fs_frame FS c j + fs_B c);
         (shadow_addr (fs_frame FS c j), shadow_addr (fs_frame FS c j) + fs_B c / 8);
         (bv_unsigned sp - K, bv_unsigned sp)] m m' ->
  asan_stack_malloc_frame c K sp L FS j (Z_to_bv 64 (fs_frame FS c j)) m m'.
Proof.
  intros Hc Hj HL HFS HGT APP STK ROOM FLG SPW FLW SHZ MU.
  pose proof (fs_frame_bounds FS c j ltac:(lia) Hj) as [FB1 FB2].
  assert (HB : 64 <= fs_B c) by (unfold fs_B; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat c) ltac:(lia) ltac:(lia)); lia).
  assert (HB8 : fs_B c = 8 * (fs_B c / 8)).
  { unfold fs_B. replace (64 * 2 ^ Z.of_nat c) with (8 * 2 ^ Z.of_nat c * 8) by ring. rewrite Z.div_mul by lia. ring. }
  assert (HM64 : fs_frame FS c j mod 64 = 0).
  { unfold fs_frame, fs_B. replace (j * (64 * 2 ^ Z.of_nat c)) with (64 * (j * 2 ^ Z.of_nat c)) by ring.
    change (2 ^ 20) with 1048576. lia. }
  assert (EN : fs_shadow_n c L = fs_B c / 8).
  { unfold fs_shadow_n. replace (Nat.leb c 6) with true by (symmetry; apply Nat.leb_le; lia). reflexivity. }
  unfold asan_stack_malloc_frame. cbv zeta. rewrite EN.
  unfold FS_SIZE, ASAN_GT in *.
  split; [reflexivity|]. split; [exact HM64|]. split.
  { intros H6. assert (c = 6%nat) by lia. subst c. unfold fs_frame, fs_B in *. change (2 ^ Z.of_nat 6) with 64.
    change (Z.of_nat 6) with 6. change (2 ^ 20) with 1048576. lia. }
  split; [exact FLG|]. split; [exact SPW|]. split; [exact FLW|]. split; [exact SHZ|].
  split.
  { apply (addressable_zero m' (fs_frame FS c j) L (fs_B c / 8)); [lia| lia| lia| | |exact SHZ].
    - pose proof (APP (fs_frame FS c j + fs_B c - 1) ltac:(change (2 ^ 20) with 1048576 in *; lia)) as X.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
    - intros i Hi. apply APP. change (2 ^ 20) with 1048576 in *. lia. }
  change (2 ^ 20) with 1048576 in *.
  split; [exact (stk_sub m' FS (FS + 11571200) (fs_frame FS c j) (fs_frame FS c j + fs_B c) STK ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [intros a Ha; apply APP; lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros c' j' Hc' Hj' D; apply fs_frames_apart; [lia| lia| exact Hj| exact Hj'| exact D]|].
  exact MU.
Qed.

Lemma all_ones (flags : list byte) M h : 0 < M -> Z.of_nat (length flags) = M ->
  (forall i, 0 <= i < M -> nth_error flags (Z.to_nat ((h + i) mod M)) = Some (Z_to_bv 8 1)) ->
  Forall (fun b => b = Z_to_bv 8 1) flags.
Proof.
  intros HM HL H. apply Forall_forall. intros b Hb.
  apply In_nth_error in Hb as (n & Hn).
  assert (LT : (n < length flags)%nat) by (apply nth_error_Some; congruence).
  specialize (H ((Z.of_nat n - h) mod M) ltac:(apply Z.mod_pos_bound; lia)).
  rewrite Zplus_mod_idemp_r in H. replace (h + (Z.of_nat n - h)) with (Z.of_nat n) in H by lia.
  rewrite Z.mod_small in H by lia. rewrite Nat2Z.id in H. congruence.
Qed.

Lemma post_found (c : nat) K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc L FS (h : word) flags lo
    (m m' : mem) i t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 h' :
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
  0 < FS -> FS mod 4096 = 0 -> ASAN_GT <= FS -> (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  stk rsegs m' FS (FS + FS_SIZE) -> bytes_at rsegs m' (fs_hint FS c) (le8 h') ->
  0 <= i < fs_M c ->
  (forall i', 0 <= i' < i -> nth_error flags (Z.to_nat ((bv_unsigned h + i') mod fs_M c)) = Some (Z_to_bv 8 1)) ->
  nth_error flags (Z.to_nat ((bv_unsigned h + i) mod fs_M c)) = Some (Z_to_bv 8 0) ->
  asan_stack_malloc_frame c K sp L FS ((bv_unsigned h + i) mod fs_M c) a0 m m' ->
  asan_stack_malloc_post c K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS h flags lo m
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom rsegs)).
Proof.
  intros WM MI ST P1 P2 P3 P4 P5 HH Hi H1 H0 FR. unfold asan_stack_malloc_post.
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  split; [reflexivity|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact P4| exact P5]|].
  split; [exists h'; exact HH|].
  right. exists i. split; [exact Hi|]. split; [exact H1|]. split; [exact H0| exact FR].
Qed.

Lemma post_full (c : nat) K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc L FS (h : word) flags lo
    (m m' : mem) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 h' :
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
  0 < FS -> FS mod 4096 = 0 -> ASAN_GT <= FS -> (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  stk rsegs m' FS (FS + FS_SIZE) -> bytes_at rsegs m' (fs_hint FS c) (le8 h') ->
  0 < fs_M c -> Z.of_nat (length flags) = fs_M c ->
  (forall i', 0 <= i' < fs_M c -> nth_error flags (Z.to_nat ((bv_unsigned h + i') mod fs_M c)) = Some (Z_to_bv 8 1)) ->
  munch [(fs_hint FS c, fs_hint FS c + 8); (bv_unsigned sp - K, bv_unsigned sp)] m m' ->
  asan_stack_malloc_post c K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS h flags lo m
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom rsegs)).
Proof.
  intros WM MI ST P1 P2 P3 P4 P5 HH HM HL H1 MU. unfold asan_stack_malloc_post.
  exists t0, t1, t2, (Z_to_bv 64 0), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  split; [reflexivity|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact P4| exact P5]|].
  split; [exists h'; exact HH|].
  left. split; [exact (all_ones flags (fs_M c) (bv_unsigned h) HM HL H1)|]. split; [reflexivity| exact MU].
Qed.

Lemma bytes_at_one (m : mem) A bs i b : bytes_at rsegs m A bs -> nth_error bs i = Some b ->
  bytes_at rsegs m (A + Z.of_nat i) [b].
Proof.
  intros (H0 & H1 & H) N. assert (LT : (i < length bs)%nat) by (apply nth_error_Some; congruence).
  split; [lia|]. split; [cbn [length]; lia|]. intros n Hn. cbn [length] in Hn. assert (n = 0%nat) by lia. subst n.
  replace (A + Z.of_nat i + Z.of_nat 0) with (A + Z.of_nat i) by lia. rewrite H by exact LT. exact N.
Qed.

Lemma rw_c8_bytes (m : mem) A v : rw_cells rsegs m A [C8 v] -> bytes_at rsegs m A (le8 v).
Proof. intros [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

Lemma rw_c1_bytes (m : mem) A b : rw_cells rsegs m A [C1 b] -> bytes_at rsegs m A [b].
Proof. intros [[_ B] _]. exact B. Qed.

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof.
  first [ reflexivity | vm_compute; reflexivity
        | unfold le8; cbn; repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]); reflexivity ].
Qed.

Lemma cells_bytes_zero n : cells_bytes (repeat (C8 (Z_to_bv 64 0)) n) = repeat (Z_to_bv 8 0) (8 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat cells_bytes cbytes]. rewrite IH, le8_zero.
  replace (8 * S n)%nat with (8 + 8 * n)%nat by lia. rewrite repeat_app. reflexivity.
Qed.

Lemma rw_zero_cells (m : mem) A n : rw_cells rsegs m A (repeat (C8 (Z_to_bv 64 0)) n) ->
  bytes_at rsegs m A (repeat (Z_to_bv 8 0) (8 * n)).
Proof. intros [[_ B] _]. rewrite cells_bytes_zero in B. exact B. Qed.

Lemma land_mod_low x k M N : 0 <= k <= 64 -> M = 2 ^ k - 1 -> N = 2 ^ k ->
  Z.land (x mod 18446744073709551616) M = x mod N.
Proof.
  intros Hk -> ->. rewrite zb_land_mask by lia. change 18446744073709551616 with (2 ^ 64).
  symmetry. rewrite (Z.div_mod x (2 ^ 64)) at 1 by lia.
  replace (2 ^ 64 * (x / 2 ^ 64)) with ((x / 2 ^ 64 * 2 ^ (64 - k)) * 2 ^ k)
    by (rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia; replace (64 - k + k) with 64 by lia; ring).
  rewrite Z.add_comm, Z_mod_plus_full. reflexivity.
Qed.
