(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names and numbers changed; 537 of its 623 lines of code are new or changed and 1143 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/relay_finish_seg.v, with its module paths and module names changed; 498 of its 739 lines of code are new or changed and 382 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI04 YO0x YO10 YK1j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c RelayFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import KindB RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma sb_rsegs_rw : forallb (fun s => implb (seg_writable s) (seg_readable s)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sb_wr_rd : forall m a, YP09.writable_at rsegs m a -> exists b, YP09.mbyte rsegs m a = Some b.
Proof.
  intros m a W. unfold YP09.writable_at, wview in W. unfold YP09.mbyte.
  destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|].
  destruct (find_segment rsegs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Fs; [|congruence].
  destruct (seg_writable seg) eqn:Ws; [|congruence].
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base seg))))
    as [b|] eqn:Sb; [|congruence].
  exists b.
  assert (R : seg_readable seg = true).
  { pose proof (proj1 (forallb_forall _ rsegs) sb_rsegs_rw seg (YK1j.find_segment_in _ _ _ _ Fs)) as H.
    cbv beta in H. rewrite Ws in H. exact H. }
  try unfold YK11.seg_rom; try unfold PropExec.seg_rom. unfold memory_read.
  change (Z.of_N 1) with 1. rewrite Fs, R.
  change (N.to_nat 1) with 1%nat. cbn beta iota zeta delta [segment_read_bytes]. rewrite Sb. reflexivity.
Qed.

Lemma sb_bytes_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [pose proof (bv_unsigned_in_range 8 b); lia | apply Z.shiftl_nonneg; exact IH].
Qed.

Lemma sb_le_rt : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  pose proof (sb_bytes_nonneg bs) as Nn.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
    rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
    destruct (Z.lt_ge_cases i 8) as [Hl|Hg].
    + rewrite Z.ones_spec_low by lia. rewrite (Z.testbit_neg_r _ (i - 8)) by lia.
      rewrite orb_false_r, andb_true_r. reflexivity.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r. symmetry.
      rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. apply Z.mod_pow2_bits_high. lia.
  - replace (Z.shiftr (Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) 8) with (bytes_le_to_Z bs); [exact IH|].
    rewrite Z.shiftr_lor. rewrite (Z.shiftr_div_pow2 (bv_unsigned b)) by lia. rewrite Z.div_small by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. rewrite Z.lor_0_l. reflexivity.
Qed.

Lemma sb_c4 : forall m a, 0 <= a -> a + 4 <= 2 ^ 64 ->
  (forall i, 0 <= i < 4 -> YP09.writable_at rsegs m (a + i)) -> exists v, rw_cells rsegs m a [C4 v].
Proof.
  intros m a H0 H1 W.
  destruct (sb_wr_rd m (a + 0) (W 0 ltac:(lia))) as [b0 E0].
  destruct (sb_wr_rd m (a + 1) (W 1 ltac:(lia))) as [b1 E1].
  destruct (sb_wr_rd m (a + 2) (W 2 ltac:(lia))) as [b2 E2].
  destruct (sb_wr_rd m (a + 3) (W 3 ltac:(lia))) as [b3 E3].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])).
  assert (L4 : le4 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])) = [b0; b1; b2; b3]).
  { unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z_to_le_bytes_mod by lia. exact (sb_le_rt [b0; b1; b2; b3]). }
  split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, L4. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error]; [exact E0 | exact E1 | exact E2 | exact E3 | lia].
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. exact (W i Hi).
Qed.

Lemma sb_rw_tr : forall m m' A cs, rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> YP09.mbyte rsegs m' (A + i) = YP09.mbyte rsegs m (A + i) /\
     (YP09.writable_at rsegs m (A + i) -> YP09.writable_at rsegs m' (A + i))) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hn & Hb)] (Wa & Wn & Hw)] E.
  pose proof (cells_bytes_length cs Hwf) as Lc.
  split; [split; [exact Hwf|]|].
  - split; [exact Ha|]. split; [exact Hn|]. intros i Hi.
    change (YP09.mbyte rsegs m' (A + Z.of_nat i) = nth_error (cells_bytes cs) i).
    rewrite (proj1 (E (Z.of_nat i) ltac:(lia))). exact (Hb i Hi).
  - split; [exact Wa|]. split; [exact Wn|]. intros i Hi. exact (proj2 (E i Hi) (Hw i Hi)).
Qed.

Lemma sb_ro_low : forall A n, forallb (fun i => negb (ro_addr rsegs (wa (A + Z.of_nat i)))) (seq 0 n) = true ->
  forall i, 0 <= i < Z.of_nat n -> ro_addr rsegs (wa (A + i)) = false.
Proof.
  intros A n H i Hi.
  pose proof (proj1 (forallb_forall _ _) H (Z.to_nat i) ltac:(apply in_seq; lia)) as E.
  cbv beta in E. rewrite Z2Nat.id in E by lia. apply negb_true_iff in E. exact E.
Qed.

Lemma sb_ro_g1 : forall i, 0 <= i < 128 -> ro_addr rsegs (wa (200640 + i)) = false.
Proof. apply (sb_ro_low 200640 128). vm_compute. reflexivity. Qed.

Lemma sb_ro_g2 : forall i, 0 <= i < 8 -> ro_addr rsegs (wa (134456 + i)) = false.
Proof. apply (sb_ro_low 134456 8). vm_compute. reflexivity. Qed.

Lemma sb_rsegs_wtop : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x20d10)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sb_ro_ge : forall a, 0x20d10 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite wa_unsigned by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:Fs; [|reflexivity].
  destruct (find_segment_in _ _ _ _ Fs) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ rsegs) sb_rsegs_wtop seg Hin) as W. cbv beta in W.
  apply orb_true_iff in W as [W|W]; [rewrite W; reflexivity|]. apply Z.leb_le in W. lia.
Qed.

Lemma sb_norm_eq : forall m a, ro_addr rsegs a = false -> normalize rsegs m a = m a.
Proof. intros m a H. unfold normalize. rewrite H. reflexivity. Qed.

Lemma sb_rw_norm : forall m A cs, ro_agree rsegs m -> rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros m A cs Hro [[Hwf Hb] Hw] Hra.
  split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m A _ Hro Hb)]|].
  exact (wr_at_norm rsegs m (normalize rsegs m) A _ (mem_rel_normalize rsegs m Hro) Hw Hra).
Qed.

Lemma sb_rw_back : forall m1 m0 A cs, mem_rel rsegs m1 m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m1 A cs.
Proof.
  intros m1 m0 A cs HR [[Hwf Hb] Hw].
  split; [split; [exact Hwf | exact (proj2 (bytes_at_rel rsegs m1 m0 A _ HR) Hb)]|].
  exact (wr_at_rel rsegs m1 m0 A _ HR Hw).
Qed.

Lemma sb_back : forall m m0' m1 W, ro_agree rsegs m -> mem_rel rsegs m1 m0' -> ro_same rsegs m m1 ->
  munch W (normalize rsegs m) m0' -> wmono rsegs (normalize rsegs m) m0' ->
  munch W m m1 /\ wmono rsegs m m1 /\ ro_agree rsegs m1.
Proof.
  intros m m0' m1 W Hro HR Hs MU WM. pose proof (mem_rel_normalize rsegs m Hro) as HR0.
  split; [exact (munch_rel rsegs W m (normalize rsegs m) m1 m0' HR0 HR Hs MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m1 m0' HR0 HR Hs WM)|].
  exact (ro_agree_same rsegs m m1 Hro Hs).
Qed.

Lemma sb_vm_vm : forall a b md, with_vmmaps a (with_vmmaps b md) = with_vmmaps a md.
Proof. intros a b [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma sb_vm_id : forall md, with_vmmaps (m_vmmaps md) md = md.
Proof. intros [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma sb_ub_nonneg : forall s p n, WF s -> In (p, n) (user_blocks s) -> 0 <= n.
Proof.
  intros s p n HW Hin.
  destruct (YO0x.user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & En & Ep).
  pose proof (YO10.block_in_slot s g am idx fr HW Hu Hi Hfr) as (_ & _ & H). lia.
Qed.

Lemma sb_nodup_fst : forall {X Y : Type} (l : list (X * Y)) x a b,
  List.NoDup (map fst l) -> In (x, a) l -> In (x, b) l -> a = b.
Proof.
  intros X Y l. induction l as [|[x0 y0] l IH]; intros x a b ND Ha Hb; [destruct Ha|].
  cbn [map fst] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [Hn ND'].
  destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
  - rewrite Ea in Eb. injection Eb as E. exact E.
  - exfalso. apply Hn. replace x0 with x by congruence. exact (in_map fst _ _ Hb).
  - exfalso. apply Hn. replace x0 with x by congruence. exact (in_map fst _ _ Ha).
  - exact (IH x a b ND' Ha Hb).
Qed.

Lemma sb_apart : forall (P : Z -> Prop) x n g m, 0 < n -> 0 < m ->
  (forall i, 0 <= i < n -> ~ P (x + i)) -> (forall j, 0 <= j < m -> P (g + j)) -> x + n <= g \/ g + m <= x.
Proof.
  intros P x n g m Hn Hm H1 H2.
  destruct (Z_le_gt_dec (x + n) g) as [?|G1]; [left; lia|].
  destruct (Z_le_gt_dec (g + m) x) as [?|G2]; [right; lia|].
  exfalso. destruct (Z_le_gt_dec x g) as [L|L].
  - apply (H1 (g - x) ltac:(lia)). replace (x + (g - x)) with (g + 0) by lia. apply H2. lia.
  - apply (H1 0 ltac:(lia)). replace (x + 0) with (g + (x - g)) by lia. apply H2. lia.
Qed.

(* The bytes one round of sl_run sends when rem bytes remain. *)
Definition sl_n (mx rem : Z) : Z := if negb (mx =? 0) && (mx <? rem) then mx else rem.

Lemma sl_n_eq : forall mx rem, sl_n mx rem = if mx =? 0 then rem else Z.min rem mx.
Proof.
  intros mx rem. unfold sl_n.
  destruct (Z.eqb_spec mx 0); destruct (Z.ltb_spec mx rem); cbn [negb andb]; lia.
Qed.

Lemma sl_n_bounds : forall mx rem, 0 <= mx -> 0 < rem -> 1 <= sl_n mx rem <= rem.
Proof. intros mx rem Hm Hr. rewrite sl_n_eq. destruct (Z.eqb_spec mx 0); lia. Qed.

Lemma sl_run_S : forall f mx no cap rem j o, sl_run (S f) mx no cap rem j o =
  if rem <=? 0 then ([], (cap, o)) else
  if cap <? no + sl_n mx rem then
    ((if cap =? 0 then RMalloc ((no + sl_n mx rem) * 2) else RRealloc cap ((no + sl_n mx rem) * 2) o) ::
       fst (sl_run f mx (no + sl_n mx rem) ((no + sl_n mx rem) * 2) (rem - sl_n mx rem) (S j) (Ret j)),
     snd (sl_run f mx (no + sl_n mx rem) ((no + sl_n mx rem) * 2) (rem - sl_n mx rem) (S j) (Ret j)))
  else sl_run f mx (no + sl_n mx rem) cap (rem - sl_n mx rem) j o.
Proof. reflexivity. Qed.

Lemma sl_run_fuel : forall f1 f2 mx no cap rem j o, 0 <= mx ->
  (Z.to_nat rem <= f1)%nat -> (Z.to_nat rem <= f2)%nat -> sl_run f1 mx no cap rem j o = sl_run f2 mx no cap rem j o.
Proof.
  induction f1 as [|f1 IH]; intros f2 mx no cap rem j o Hmx H1 H2; destruct f2 as [|f2].
  - reflexivity.
  - rewrite sl_run_S. rewrite (proj2 (Z.leb_le rem 0)) by lia. reflexivity.
  - rewrite sl_run_S. rewrite (proj2 (Z.leb_le rem 0)) by lia. reflexivity.
  - rewrite !sl_run_S. destruct (Z.leb_spec rem 0) as [R|R]; [reflexivity|].
    pose proof (sl_n_bounds mx rem Hmx R) as Hn.
    rewrite (IH f2 mx (no + sl_n mx rem) ((no + sl_n mx rem) * 2) (rem - sl_n mx rem) (S j) (Ret j)) by lia.
    rewrite (IH f2 mx (no + sl_n mx rem) cap (rem - sl_n mx rem) j o) by lia.
    reflexivity.
Qed.

Lemma sl_run_fits : forall f mx no cap rem j o, 0 <= mx -> no + rem <= cap ->
  sl_run f mx no cap rem j o = ([], (cap, o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hmx H; [reflexivity|].
  rewrite sl_run_S. destruct (Z.leb_spec rem 0) as [R|R]; [reflexivity|].
  pose proof (sl_n_bounds mx rem Hmx R) as Hn.
  rewrite (proj2 (Z.ltb_ge cap (no + sl_n mx rem))) by lia.
  apply IH; lia.
Qed.

(* The final capacity does not depend on the addresses. *)
Lemma sl_run_cap : forall f mx no cap rem j o j' o',
  fst (snd (sl_run f mx no cap rem j o)) = fst (snd (sl_run f mx no cap rem j' o')).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o j' o'; [reflexivity|].
  rewrite !sl_run_S. destruct (rem <=? 0); [reflexivity|].
  destruct (cap <? no + sl_n mx rem); cbn [snd]; apply IH.
Qed.

(* What sl_run still requests, the final capacity and the final buffer, when k of the LEN bytes are sent from
   g_nout = NO + k with capacity c and the buffer at o, j addresses returned so far. *)
Definition sl_rest (mx LEN NO k c : Z) (j : nat) (o : adrF) : trF * (Z * adrF) :=
  sl_run (Z.to_nat (LEN - k)) mx (NO + k) c (LEN - k) j o.

Lemma sl_rest_0 : forall mx LEN NO c j o, sl_rest mx LEN NO 0 c j o = sl_run (Z.to_nat LEN) mx NO c LEN j o.
Proof. intros mx LEN NO c j o. unfold sl_rest. rewrite Z.sub_0_r, Z.add_0_r. reflexivity. Qed.

Lemma sl_rest_fin : forall mx LEN NO k c j o, 0 <= mx -> NO + LEN <= c -> sl_rest mx LEN NO k c j o = ([], (c, o)).
Proof. intros mx LEN NO k c j o Hmx H. unfold sl_rest. apply sl_run_fits; lia. Qed.

Lemma sl_rest_fit : forall mx LEN NO k c j o n, 0 <= mx -> 0 <= k < LEN -> n = sl_n mx (LEN - k) -> NO + k + n <= c ->
  sl_rest mx LEN NO k c j o = sl_rest mx LEN NO (k + n) c j o.
Proof.
  intros mx LEN NO k c j o n Hmx Hk Hn Hfit. unfold sl_rest.
  pose proof (sl_n_bounds mx (LEN - k) Hmx ltac:(lia)) as B. rewrite <- Hn in B.
  destruct (Z.to_nat (LEN - k)) as [|f] eqn:EF; [lia|].
  rewrite sl_run_S, <- Hn.
  rewrite (proj2 (Z.leb_gt (LEN - k) 0)) by lia.
  rewrite (proj2 (Z.ltb_ge c (NO + k + n))) by lia.
  replace (NO + k + n) with (NO + (k + n)) by lia. replace (LEN - k - n) with (LEN - (k + n)) by lia.
  apply sl_run_fuel; lia.
Qed.

Lemma sl_rest_grow : forall mx LEN NO k c j o n, 0 <= mx -> 0 <= k < LEN -> n = sl_n mx (LEN - k) -> c < NO + k + n ->
  sl_rest mx LEN NO k c j o =
  ((if c =? 0 then RMalloc (2 * (NO + k + n)) else RRealloc c (2 * (NO + k + n)) o) ::
     fst (sl_rest mx LEN NO (k + n) (2 * (NO + k + n)) (S j) (Ret j)),
   snd (sl_rest mx LEN NO (k + n) (2 * (NO + k + n)) (S j) (Ret j))).
Proof.
  intros mx LEN NO k c j o n Hmx Hk Hn Hgrow. unfold sl_rest.
  pose proof (sl_n_bounds mx (LEN - k) Hmx ltac:(lia)) as B. rewrite <- Hn in B.
  destruct (Z.to_nat (LEN - k)) as [|f] eqn:EF; [lia|].
  rewrite sl_run_S, <- Hn.
  rewrite (proj2 (Z.leb_gt (LEN - k) 0)) by lia.
  rewrite (proj2 (Z.ltb_lt c (NO + k + n))) by lia.
  replace ((NO + k + n) * 2) with (2 * (NO + k + n)) by lia.
  replace (LEN - k - n) with (LEN - (k + n)) by lia. replace (NO + (k + n)) with (NO + k + n) by lia.
  rewrite (sl_run_fuel f (Z.to_nat (LEN - (k + n))) mx (NO + k + n) (2 * (NO + k + n)) (LEN - (k + n)) (S j) (Ret j))
    by lia.
  reflexivity.
Qed.

Lemma sl_rest_steps : forall mx LEN NO c j o (t : nat) k, 0 < mx -> 0 <= k ->
  k + Z.of_nat t * mx < LEN -> NO + k + Z.of_nat t * mx <= c ->
  sl_rest mx LEN NO k c j o = sl_rest mx LEN NO (k + Z.of_nat t * mx) c j o.
Proof.
  intros mx LEN NO c j o t. induction t as [|t IH]; intros k Hmx Hk HL HC.
  - cbn [Z.of_nat]. rewrite Z.mul_0_l, Z.add_0_r. reflexivity.
  - rewrite Nat2Z.inj_succ, Z.mul_succ_l in *.
    pose proof (Z.mul_nonneg_nonneg (Z.of_nat t) mx ltac:(lia) ltac:(lia)) as P.
    rewrite (sl_rest_fit mx LEN NO k c j o mx) by (try rewrite sl_n_eq; try destruct (Z.eqb_spec mx 0); lia).
    rewrite (IH (k + mx)) by lia.
    replace (k + mx + Z.of_nat t * mx) with (k + (Z.of_nat t * mx + mx)) by lia.
    reflexivity.
Qed.

Lemma sl_rest_path : forall mx LEN NO c j o t k k', 0 <= mx -> 0 <= k -> k' = k + t * mx -> k <= k' < LEN ->
  NO + k' <= c -> sl_rest mx LEN NO k c j o = sl_rest mx LEN NO k' c j o.
Proof.
  intros mx LEN NO c j o t k k' Hmx Hk Ht Hk' HC.
  destruct (Z.eq_dec mx 0) as [M|M].
  - subst mx. replace k' with k by lia. reflexivity.
  - assert (T : 0 <= t) by nia. subst k'.
    pose proof (sl_rest_steps mx LEN NO c j o (Z.to_nat t) k) as S. rewrite Z2Nat.id in S by lia.
    apply S; lia.
Qed.

(* A trace address that names a start block or an address returned among the first j. *)
Definition p3a_ok (a : adrF) (j : nat) : Prop := match a with Known _ => True | Ret i => (i < j)%nat end.

Lemma p3a_ok_mono : forall a j j', p3a_ok a j -> (j <= j')%nat -> p3a_ok a j'.
Proof. intros [p|i] j j' H L; cbn in *; [exact I | lia]. Qed.

Lemma p3a_wf_app : forall (t1 t2 : trF) j,
  wf_from sptr j (t1 ++ t2) <-> wf_from sptr j t1 /\ wf_from sptr (j + nretF t1) t2.
Proof.
  induction t1 as [|e t1 IH]; intros t2 j.
  - change (nretF []) with 0%nat. rewrite Nat.add_0_r. cbn [app wf_from]. tauto.
  - change (nretF (e :: t1)) with (rets sptr e + nretF t1)%nat. cbn [app wf_from].
    rewrite IH. rewrite Nat.add_assoc. tauto.
Qed.

Lemma p3a_resolve_app : forall (qs post : list sptr) a, p3a_ok a (length qs) ->
  resolveF (qs ++ post) a = resolveF qs a.
Proof. intros qs post [p|i] H; cbn in H |- *; [reflexivity | apply app_nth1; exact H]. Qed.

Lemma p3a_nth_last : forall (qp : list sptr) q i, i = length qp -> nth i (qp ++ [q]) (SP 0 0) = q.
Proof. intros qp q i ->. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

(* The run of a well-formed trace reads only the addresses it returned. *)
Lemma p3a_run_app : forall (R : Type) rmal rfre rrea (qs post : list sptr) (b : R) j (tr : trF),
  wf_from sptr j tr -> (j + nretF tr <= length qs)%nat ->
  run_from R sptr (SP 0 0) rmal rfre rrea (qs ++ post) b j tr = run_from R sptr (SP 0 0) rmal rfre rrea qs b j tr.
Proof.
  intros R rmal rfre rrea qs post b j tr. revert b j.
  induction tr as [|e tr IH]; intros b j Hw Hn; [reflexivity|].
  change (nretF (e :: tr)) with (rets sptr e + nretF tr)%nat in Hn.
  destruct Hw as [He Hw].
  destruct e as [n|n a|k n a]; cbn [run_from rets] in Hn, Hw, He |- *.
  - apply IH; [replace (S j) with (j + 1)%nat by lia; exact Hw | lia].
  - rewrite p3a_resolve_app by (apply (p3a_ok_mono a j); [exact He | lia]).
    apply IH; [rewrite Nat.add_0_r in Hw; exact Hw | lia].
  - rewrite p3a_resolve_app by (apply (p3a_ok_mono a j); [exact He | lia]).
    rewrite app_nth1 by lia.
    apply IH; [replace (S j) with (j + 1)%nat by lia; exact Hw | lia].
Qed.

Section P3aF.
Variable F : ResFormT.

(* One more request at the end of a well-formed trace whose returned addresses are qp. *)
Lemma p3a_runF_mal : forall qp q b (tp : trF) n, wf_from sptr 0 tp -> nretF tp = length qp ->
  runF F (qp ++ [q]) b (tp ++ [RMalloc n]) = rt_malloc F (runF F qp b tp) n.
Proof using.
  intros qp q b tp n Hw Hn. unfold runF, run_tr. rewrite run_from_app.
  rewrite (p3a_run_app _ _ _ _ qp [q] b 0 tp) by (exact Hw || lia). reflexivity.
Qed.

Lemma p3a_runF_rea : forall qp q b (tp : trF) k n a, wf_from sptr 0 tp -> nretF tp = length qp ->
  p3a_ok a (length qp) ->
  runF F (qp ++ [q]) b (tp ++ [RRealloc k n a]) = rt_realloc F (runF F qp b tp) k n (resolveF qp a) q.
Proof using.
  intros qp q b tp k n a Hw Hn Ha. unfold runF, run_tr. rewrite run_from_app.
  rewrite (p3a_run_app _ _ _ _ qp [q] b 0 tp) by (exact Hw || lia). cbn [run_from].
  rewrite p3a_resolve_app by exact Ha. rewrite p3a_nth_last by lia. reflexivity.
Qed.

(* The room for the next request of a trace, from the premise over every address list. *)
Lemma p3a_room_next : forall qp b (tp : trF) e rest n, wf_from sptr 0 tp -> nretF tp = length qp ->
  (forall qs, length qs = nretF (tp ++ e :: rest) -> roomF F qs b (tp ++ e :: rest)) ->
  (e = RMalloc n \/ exists k a, e = RRealloc k n a) ->
  rt_room F (runF F qp b tp) n.
Proof using.
  intros qp b tp e rest n Hw Hn HR He.
  pose proof (HR (qp ++ repeat (SP 0 0) (nretF (e :: rest)))) as R.
  rewrite length_app, repeat_length, nret_app, Hn in R. specialize (R eq_refl).
  unfold roomF, room_run in R. apply room_from_app in R. destruct R as [_ R].
  rewrite (p3a_run_app _ _ _ _ qp (repeat (SP 0 0) (nretF (e :: rest))) b 0 tp) in R by (exact Hw || lia).
  destruct He as [->|(k & a & ->)]; cbn [room_from] in R; exact (proj1 R).
Qed.
End P3aF.

Lemma p3a_wf_snoc : forall (tp : trF) e, wf_from sptr 0 tp ->
  match e with RMalloc _ => True | RFree _ a | RRealloc _ _ a => p3a_ok a (nretF tp) end ->
  wf_from sptr 0 (tp ++ [e]).
Proof.
  intros tp e Hw He. apply p3a_wf_app. split; [exact Hw|]. cbn [wf_from].
  split; [|exact I].
  destruct e as [n|n a|k n a]; cbn in He |- *; [exact I | refine (p3a_ok_mono a _ _ He _); lia
    | refine (p3a_ok_mono a _ _ He _); lia].
Qed.

Lemma p3a_room_app : forall (R : Type) rmal rfre rrea rroom (qs post : list sptr) (b : R) j (tr : trF),
  wf_from sptr j tr -> (j + nretF tr <= length qs)%nat ->
  room_from R sptr (SP 0 0) rmal rfre rrea rroom (qs ++ post) b j tr <->
  room_from R sptr (SP 0 0) rmal rfre rrea rroom qs b j tr.
Proof.
  intros R rmal rfre rrea rroom qs post b j tr. revert b j.
  induction tr as [|e tr IH]; intros b j Hw Hn; [split; intros _; exact I|].
  change (nretF (e :: tr)) with (rets sptr e + nretF tr)%nat in Hn.
  destruct Hw as [He Hw].
  destruct e as [n|n a|k n a]; cbn [room_from rets] in Hn, Hw, He |- *.
  - rewrite IH; [tauto | replace (S j) with (j + 1)%nat by lia; exact Hw | lia].
  - rewrite p3a_resolve_app by (apply (p3a_ok_mono a j); [exact He | lia]).
    apply IH; [rewrite Nat.add_0_r in Hw; exact Hw | lia].
  - rewrite p3a_resolve_app by (apply (p3a_ok_mono a j); [exact He | lia]).
    rewrite app_nth1 by lia.
    rewrite IH; [tauto | replace (S j) with (j + 1)%nat by lia; exact Hw | lia].
Qed.

Lemma p3a_nret_cons1 : forall (e : rev sptr) (t : trF), rets sptr e = 1%nat -> nretF (e :: t) = S (nretF t).
Proof. intros e t H. change (rets sptr e + nretF t = S (nretF t))%nat. rewrite H. reflexivity. Qed.

(* sl_run's trace is well formed, and its final buffer is a start block or an address it returned. *)
Lemma p3a_sl_run_wf : forall f mx no cap rem j o, p3a_ok o j ->
  wf_from sptr j (fst (sl_run f mx no cap rem j o)) /\
  p3a_ok (snd (snd (sl_run f mx no cap rem j o))) (j + nretF (fst (sl_run f mx no cap rem j o))).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Ho.
  - cbn [sl_run fst snd]. split; [exact I|]. change (nretF []) with 0%nat. rewrite Nat.add_0_r. exact Ho.
  - rewrite sl_run_S. destruct (rem <=? 0).
    + cbn [fst snd]. split; [exact I|]. change (nretF []) with 0%nat. rewrite Nat.add_0_r. exact Ho.
    + destruct (cap <? no + sl_n mx rem); [|exact (IH _ _ _ _ _ _ Ho)].
      cbn [fst snd].
      destruct (IH mx (no + sl_n mx rem) ((no + sl_n mx rem) * 2) (rem - sl_n mx rem) (S j) (Ret j)) as [W P];
        [cbn; lia|].
      destruct (cap =? 0); cbn [wf_from rets].
      * split; [split; [exact I | rewrite Nat.add_1_r; exact W]|].
        rewrite p3a_nret_cons1 by reflexivity. refine (p3a_ok_mono _ _ _ P _). lia.
      * split; [split; [exact Ho | rewrite Nat.add_1_r; exact W]|].
        rewrite p3a_nret_cons1 by reflexivity. refine (p3a_ok_mono _ _ _ P _). lia.
Qed.

Lemma p3a_slt_wf : forall live mx NO CAP LEN j o, p3a_ok o j ->
  wf_from sptr j (send_line_tr live mx NO CAP LEN j o) /\
  p3a_ok (send_line_out live mx NO CAP LEN j o) (j + nretF (send_line_tr live mx NO CAP LEN j o)).
Proof.
  intros live mx NO CAP LEN j o Ho. unfold send_line_tr, send_line_out. destruct live; [exact (p3a_sl_run_wf _ _ _ _ _ _ _ Ho)|].
  split; [exact I|]. change (nretF []) with 0%nat. rewrite Nat.add_0_r. exact Ho.
Qed.

Section P3aShift.
Variable F : ResFormT.
Local Notation RUNF qs b j tr := (run_from (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) qs b j tr).
Local Notation ROOMF qs b j tr :=
  (room_from (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) (rt_room F) qs b j tr).

(* sl_run from base length pre + i with buffer o, in an address list pre ++ qs, does what it does from base i with
   buffer o' in qs when o and o' name the same block (needed only while the capacity is not 0). *)
Lemma p3a_sl_run_shift : forall f mx no cap rem (pre qs : list sptr) b i o o',
  (cap <> 0 -> resolveF (pre ++ qs) o = resolveF qs o') ->
  nretF (fst (sl_run f mx no cap rem (length pre + i) o)) = nretF (fst (sl_run f mx no cap rem i o')) /\
  RUNF (pre ++ qs) b (length pre + i) (fst (sl_run f mx no cap rem (length pre + i) o)) =
    RUNF qs b i (fst (sl_run f mx no cap rem i o')) /\
  (ROOMF (pre ++ qs) b (length pre + i) (fst (sl_run f mx no cap rem (length pre + i) o)) <->
    ROOMF qs b i (fst (sl_run f mx no cap rem i o'))) /\
  (fst (snd (sl_run f mx no cap rem i o')) <> 0 ->
    resolveF (pre ++ qs) (snd (snd (sl_run f mx no cap rem (length pre + i) o))) =
    resolveF qs (snd (snd (sl_run f mx no cap rem i o')))).
Proof using.
  induction f as [|f IH]; intros mx no cap rem pre qs b i o o' Ho.
  - cbn [sl_run fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [split; intros _; exact I | exact Ho].
  - rewrite !sl_run_S. destruct (rem <=? 0).
    + cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [split; intros _; exact I | exact Ho].
    + destruct (cap <? no + sl_n mx rem); [|exact (IH mx (no + sl_n mx rem) cap (rem - sl_n mx rem) pre qs b i o o' Ho)].
      assert (HR : ((no + sl_n mx rem) * 2 <> 0 -> resolveF (pre ++ qs) (Ret (length pre + i)) = resolveF qs (Ret i))).
      { intros _. cbn [resolve]. rewrite app_nth2 by lia. f_equal. lia. }
      destruct (cap =? 0) eqn:Ec.
      * destruct (IH mx (no + sl_n mx rem) ((no + sl_n mx rem) * 2) (rem - sl_n mx rem) pre qs
                    (rt_malloc F b ((no + sl_n mx rem) * 2)) (S i) (Ret (length pre + i)) (Ret i) HR)
          as (N & Rn & Rm & Fa).
        cbn [fst snd run_from room_from].
        replace (S (length pre + i)) with (length pre + S i)%nat by lia.
        split; [rewrite !p3a_nret_cons1 by reflexivity; f_equal; exact N|].
        split; [exact Rn|]. split; [rewrite Rm; tauto | exact Fa].
      * assert (E1 : resolveF (pre ++ qs) o = resolveF qs o') by (apply Ho; apply Z.eqb_neq; exact Ec).
        assert (E2 : nth (length pre + i) (pre ++ qs) (SP 0 0) = nth i qs (SP 0 0))
          by (rewrite app_nth2 by lia; f_equal; lia).
        destruct (IH mx (no + sl_n mx rem) ((no + sl_n mx rem) * 2) (rem - sl_n mx rem) pre qs
                    (rt_realloc F b cap ((no + sl_n mx rem) * 2) (resolveF qs o') (nth i qs (SP 0 0)))
                    (S i) (Ret (length pre + i)) (Ret i) HR) as (N & Rn & Rm & Fa).
        cbn [fst snd run_from room_from]. rewrite E1, E2.
        replace (S (length pre + i)) with (length pre + S i)%nat by lia.
        split; [rewrite !p3a_nret_cons1 by reflexivity; f_equal; exact N|].
        split; [exact Rn|]. split; [rewrite Rm; tauto | exact Fa].
Qed.

(* The same for send_line's trace, from base length pre in the caller and 0 in the callee. *)
Lemma p3a_slt_shift : forall live mx NO CAP LEN (pre qs : list sptr) b o o',
  (CAP <> 0 -> resolveF (pre ++ qs) o = resolveF qs o') ->
  nretF (send_line_tr live mx NO CAP LEN (length pre) o) = nretF (send_line_tr live mx NO CAP LEN 0 o') /\
  RUNF (pre ++ qs) b (length pre) (send_line_tr live mx NO CAP LEN (length pre) o) =
    runF F qs b (send_line_tr live mx NO CAP LEN 0 o') /\
  (ROOMF (pre ++ qs) b (length pre) (send_line_tr live mx NO CAP LEN (length pre) o) <->
    roomF F qs b (send_line_tr live mx NO CAP LEN 0 o')) /\
  (live = true -> send_line_cap live mx NO CAP LEN <> 0 ->
    resolveF (pre ++ qs) (send_line_out live mx NO CAP LEN (length pre) o) =
    resolveF qs (send_line_out live mx NO CAP LEN 0 o')).
Proof using.
  intros live mx NO CAP LEN pre qs b o o' Ho. unfold send_line_tr, send_line_out, send_line_cap, runF, roomF, run_tr,
    room_run.
  destruct live.
  - pose proof (p3a_sl_run_shift (Z.to_nat LEN) mx NO CAP LEN pre qs b 0 o o' Ho) as X.
    rewrite Nat.add_0_r in X. rewrite (sl_run_cap (Z.to_nat LEN) mx NO CAP LEN 0 adr0 0 o').
    destruct X as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. intros _. exact X4.
  - split; [reflexivity|]. split; [reflexivity|]. split; [split; intros _; exact I|]. intros X; discriminate X.
Qed.
End P3aShift.

Lemma p3a_nodup_inj : forall {X Y : Type} (f : X -> Y) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y ->
  x = y.
Proof.
  intros X Y f l. induction l as [|z l IH]; intros x y HN Hx Hy E; [destruct Hx|].
  cbn [map] in HN. apply List.NoDup_cons_iff in HN as [Hz HN].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - reflexivity.
  - exfalso. apply Hz. rewrite E. apply in_map. exact Hy.
  - exfalso. apply Hz. rewrite <- E. apply in_map. exact Hx.
  - exact (IH x y HN Hx Hy E).
Qed.

(* With the block addresses distinct, sptr_of at a live block's address is that block's model pointer. *)
Lemma p3a_sptr_of_eq : forall L A p n, NoDup (map fst (blocks L A)) -> In (p, n) (user_blocks A) ->
  sptr_of L A (ptr_addr L p) = p.
Proof.
  intros L A p n HN Hp.
  assert (Hb : In (ptr_addr L p, n) (blocks L A))
    by (unfold blocks; exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (p, n) Hp)).
  destruct (sptr_of_spec L A _ n HN Hb) as [Hq Eq].
  apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HN. unfold blocks in HN. rewrite map_map in HN.
  assert (E : (sptr_of L A (ptr_addr L p), n) = (p, n)) by exact (p3a_nodup_inj _ _ _ _ HN Hq Hp Eq).
  injection E as E. exact E.
Qed.

(* With the block addresses distinct, the start-state name of a live block is its model pointer. *)
Lemma p3a_live_known : forall L A p a n, NoDup (map fst (blocks L A)) -> live_at L A p a n ->
  resolveF [] (known_at L A a) = p.
Proof. intros L A p a n HN [Hp <-]. exact (p3a_sptr_of_eq L A p n HN Hp). Qed.

Section P3aCat.
Variable F : ResFormT.

(* The room for a prefix of a trace, from the room for the whole. *)
Lemma p3a_room_pre : forall (b : rt_R F) (t1 t2 : trF), wf_from sptr 0 t1 ->
  (forall qs, length qs = nretF (t1 ++ t2) -> roomF F qs b (t1 ++ t2)) ->
  forall qs1, length qs1 = nretF t1 -> roomF F qs1 b t1.
Proof using.
  intros b t1 t2 Hw HR qs1 L1. pose proof (HR (qs1 ++ repeat (SP 0 0) (nretF t2))) as R.
  rewrite length_app, repeat_length, nret_app, L1 in R. specialize (R eq_refl).
  unfold roomF, room_run in R |- *. apply room_from_app in R. destruct R as [R _].
  rewrite p3a_room_app in R by (exact Hw || lia). exact R.
Qed.

(* send_line after a prefix t1 whose returned addresses are qs1, its buffer o1 naming the block p: the room, the
   run and the final buffer of the whole are the callee's, run from where t1 left the resource state. *)
Lemma p3a_cat_room : forall (b : rt_R F) (t1 : trF) qs1 o1 live mx NO CAP LEN p,
  wf_from sptr 0 t1 -> p3a_ok o1 (nretF t1) -> length qs1 = nretF t1 ->
  (CAP <> 0 -> resolveF qs1 o1 = p) ->
  (forall qs, length qs = nretF (t1 ++ send_line_tr live mx NO CAP LEN (nretF t1) o1) ->
     roomF F qs b (t1 ++ send_line_tr live mx NO CAP LEN (nretF t1) o1)) ->
  forall qs2, length qs2 = nretF (send_line_tr live mx NO CAP LEN 0 (Known p)) ->
    roomF F qs2 (runF F qs1 b t1) (send_line_tr live mx NO CAP LEN 0 (Known p)).
Proof using.
  intros b t1 qs1 o1 live mx NO CAP LEN p Hw Ho LQ Hp HR qs2 LQ2.
  assert (Hr : CAP <> 0 -> resolveF (qs1 ++ qs2) o1 = resolveF qs2 (Known p)).
  { intros C. rewrite p3a_resolve_app by (rewrite LQ; exact Ho). exact (Hp C). }
  destruct (p3a_slt_shift F live mx NO CAP LEN qs1 qs2 (runF F qs1 b t1) o1 (Known p) Hr) as (N & _ & Rm & _).
  rewrite LQ in N, Rm.
  pose proof (HR (qs1 ++ qs2)) as R. rewrite length_app, nret_app, LQ, LQ2, N in R. specialize (R eq_refl).
  unfold roomF, room_run in R. apply room_from_app in R. destruct R as [_ R].
  rewrite (p3a_run_app _ _ _ _ qs1 qs2 b 0 t1) in R by (exact Hw || lia).
  apply Rm. exact R.
Qed.

Lemma p3a_cat_run : forall (b : rt_R F) (t1 : trF) qs1 qs2 o1 live mx NO CAP LEN p,
  wf_from sptr 0 t1 -> p3a_ok o1 (nretF t1) -> length qs1 = nretF t1 ->
  (CAP <> 0 -> resolveF qs1 o1 = p) ->
  nretF (t1 ++ send_line_tr live mx NO CAP LEN (nretF t1) o1) =
    (length qs1 + nretF (send_line_tr live mx NO CAP LEN 0 (Known p)))%nat /\
  runF F (qs1 ++ qs2) b (t1 ++ send_line_tr live mx NO CAP LEN (nretF t1) o1) =
    runF F qs2 (runF F qs1 b t1) (send_line_tr live mx NO CAP LEN 0 (Known p)) /\
  (live = true -> send_line_cap live mx NO CAP LEN <> 0 ->
    resolveF (qs1 ++ qs2) (send_line_out live mx NO CAP LEN (nretF t1) o1) =
    resolveF qs2 (send_line_out live mx NO CAP LEN 0 (Known p))).
Proof using.
  intros b t1 qs1 qs2 o1 live mx NO CAP LEN p Hw Ho LQ Hp.
  assert (Hr : CAP <> 0 -> resolveF (qs1 ++ qs2) o1 = resolveF qs2 (Known p)).
  { intros C. rewrite p3a_resolve_app by (rewrite LQ; exact Ho). exact (Hp C). }
  destruct (p3a_slt_shift F live mx NO CAP LEN qs1 qs2 (runF F qs1 b t1) o1 (Known p) Hr) as (N & Rn & _ & Fa).
  rewrite LQ in N, Rn, Fa.
  split; [rewrite nret_app, N, LQ; reflexivity|].
  split; [|exact Fa].
  unfold runF at 1, run_tr at 1. rewrite run_from_app.
  rewrite (p3a_run_app _ _ _ _ qs1 qs2 b 0 t1) by (exact Hw || lia). exact Rn.
Qed.
End P3aCat.

Section FR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTXO : ctx_owned Bm API.
Hypothesis EU : errno_unowned Bm API.
Hypothesis BW : blocks_writable Bm API.
Hypothesis SEGS : ms_segs Bm = rsegs.

Lemma sb_low : forall L A mem md a, aa_MR API L A mem md -> owned Bm L A a -> 0 <= a < YM05.alloc_ceiling.
Proof using. intros L A mem md a HM Ho. exact (mr_owned_low Bm _ (aa_laws API) L A mem md a HM Ho). Qed.

Lemma sb_not_owned_img : forall L A mem md a, aa_MR API L A mem md -> img_plain Bm a -> ~ owned Bm L A a.
Proof using AX.
  intros L A mem md a HM (Hi & Hs & Hc & _) [Ho|Ho].
  - exact (Hc (ax_img AX L A mem md a HM Hi Ho)).
  - exact (Hs Ho).
Qed.

Lemma sb_owned_img : forall L A mem md L' A' mem' md' a, aa_MR API L A mem md -> aa_MR API L' A' mem' md' ->
  in_img Bm a -> owned Bm L' A' a -> owned Bm L A a.
Proof using AX CTXO.
  intros L A mem md L' A' mem' md' a HM HM' Hi [Ho|Ho].
  - exact (CTXO L A mem md a HM (ax_img AX L' A' mem' md' a HM' Hi Ho)).
  - right. exact Ho.
Qed.

Lemma sb_comp : forall K E F L0 A0 R0 m0 md0 L1 A1 m1 md1 K2 Rc E2 F2 L2 A2 R2 m2 md2,
  relay_post Bm API K E F L0 A0 R0 m0 md0 L1 A1 R0 m1 md1 ->
  relay_post Bm API K2 E2 F2 L1 A1 Rc m1 md1 L2 A2 R2 m2 md2 ->
  (forall a, spZ R0 - K <= a < spZ R0 -> YM05.alloc_ceiling <= a < 2 ^ 64) ->
  (forall a, scratch_k Bm K2 Rc a -> scratch_k Bm K R0 a) ->
  (forall a, scratch_k Bm K R0 a -> ~ scratch_k Bm K2 Rc a -> ~ E2 a) ->
  (forall p n, In (p, n) (user_blocks A0) -> In (p, n) (user_blocks A1) -> 0 < n -> ~ F (ptr_addr L0 p) ->
     ~ F2 (ptr_addr L0 p)) ->
  (forall a, (YM05.alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) -> ~ owned Bm L0 A0 a -> ~ scratch_k Bm K R0 a ->
     E2 a -> E a) ->
  (forall p n i, In (p, n) (user_blocks A0) -> In (p, n) (user_blocks A1) -> ~ F (ptr_addr L0 p) -> 0 <= i < n ->
     E2 (ptr_addr L0 p + i) -> E (ptr_addr L0 p + i)) ->
  relay_post Bm API K E F L0 A0 R0 m0 md0 L2 A2 R0 m2 md2.
Proof using.
  intros K E F L0 A0 R0 m0 md0 L1 A1 m1 md1 K2 Rc E2 F2 L2 A2 R2 m2 md2 P1 P2 SCA SCK SCE CF CE CB.
  destruct P1 as (M1 & W1 & B1 & LL1 & LN1 & AD1 & SV1 & Z1 & OW1 & RP1 & MD1 & FR1 & BY1 & SC1).
  destruct P2 as (M2 & W2 & B2 & LL2 & LN2 & AD2 & SV2 & Z2 & OW2 & RP2 & MD2 & FR2 & BY2 & SC2).
  assert (KEEP : forall p n, In (p, n) (user_blocks A0) -> 0 < n -> ~ F (ptr_addr L0 p) ->
            In (p, n) (user_blocks A1) /\ ptr_addr L1 p = ptr_addr L0 p).
  { intros p n H0 Hn NF. pose proof (SV1 p n H0 Hn NF) as H1. split; [exact H1 | exact (AD1 p n H0 H1 NF)]. }
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split.
  { destruct LL1 as (C1 & S1 & K1 & R1'). destruct LL2 as (C2 & S2 & K2' & R2').
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite R2' by lia. apply R1'. exact Hr. }
  split; [lia|].
  split.
  { intros p n H0 H2 NF.
    pose proof (sb_ub_nonneg A2 p n W2 H2) as Hn.
    destruct (Z.eq_dec n 0) as [->|Hn0].
    - destruct (Z1 p H0) as [H1 E1]. destruct (Z2 p H1) as [_ E2']. congruence.
    - destruct (KEEP p n H0 ltac:(lia) NF) as [H1 E1].
      rewrite (AD2 p n H1 H2 ltac:(rewrite E1; exact (CF p n H0 H1 ltac:(lia) NF))). exact E1. }
  split.
  { intros p n H0 Hn NF. destruct (KEEP p n H0 Hn NF) as [H1 E1].
    apply (SV2 p n H1 Hn). rewrite E1. exact (CF p n H0 H1 Hn NF). }
  split.
  { intros p H0. destruct (Z1 p H0) as [H1 E1]. destruct (Z2 p H1) as [H2 E2']. split; [exact H2 | congruence]. }
  split.
  { intros a Hi Ho. exact (OW1 a Hi (OW2 a Hi Ho)). }
  split; [intros r Hr; reflexivity|].
  split.
  { destruct MD1 as [v1 ->]. destruct MD2 as [v2 ->]. exists v2. apply sb_vm_vm. }
  split.
  { intros a Ha NO0 NO2 NS NE.
    assert (NO1 : ~ owned Bm L1 A1 a).
    { destruct Ha as [Ha|Ha].
      - intros Ho. pose proof (sb_low L1 A1 m1 md1 a M1 Ho). lia.
      - intros Ho. exact (NO0 (OW1 a Ha Ho)). }
    destruct (FR1 a Ha NO0 NO1 NS NE) as [E1 W1'].
    destruct (FR2 a Ha NO1 NO2 (fun H => NS (SCK a H)) (fun H => NE (CE a Ha NO0 NS H))) as [E2' W2'].
    split; [congruence | tauto]. }
  split.
  { intros p n i H0 H2 NF Hi NE.
    destruct (KEEP p n H0 ltac:(lia) NF) as [H1 E1].
    pose proof (BY2 p n i H1 H2) as B2'. rewrite E1 in B2'.
    rewrite (B2' (CF p n H0 H1 ltac:(lia) NF) Hi (fun H => NE (CB p n i H0 H1 NF Hi H))).
    exact (BY1 p n i H0 H1 NF Hi NE). }
  intros a Ha.
  assert (D : scratch_k Bm K2 Rc a \/ ~ scratch_k Bm K2 Rc a) by (unfold scratch_k; lia).
  destruct D as [D|D]; [exact (SC2 a D)|].
  pose proof (SC1 a Ha) as Wm.
  destruct Ha as [Ha|Ha]; [|exfalso; apply D; right; exact Ha].
  pose proof (SCA a Ha) as Hc.
  assert (N1 : ~ owned Bm L1 A1 a) by (intros Ho; pose proof (sb_low L1 A1 m1 md1 a M1 Ho); lia).
  assert (N2 : ~ owned Bm L2 A2 a) by (intros Ho; pose proof (sb_low L2 A2 m2 md2 a M2 Ho); lia).
  apply (proj2 (FR2 a (or_introl Hc) N1 N2 D (SCE a (or_introl Ha) D))). exact Wm.
Qed.

Lemma sb_kA : forall K E F L0 A0 R0 m0 md0 L1 A1 m1 md1 m2 W,
  relay_post Bm API K E F L0 A0 R0 m0 md0 L1 A1 R0 m1 md1 ->
  munch W m1 m2 -> wmono (ms_segs Bm) m1 m2 ->
  (forall a, errno_addr Bm <= a < errno_addr Bm + 4 -> in_img Bm a) ->
  (forall a, 0 <= a < 2 ^ 64 -> outside W a \/
     (spZ R0 - K <= a < spZ R0 /\ YM05.alloc_ceiling <= a) \/ (img_plain Bm a /\ E a) \/
     (errno_addr Bm <= a < errno_addr Bm + 4) \/
     (~ in_img Bm a /\ (exists q k, In (q, k) (blocks L1 A1) /\ q <= a < q + k) /\
      forall p n i, In (p, n) (user_blocks A0) -> In (p, n) (user_blocks A1) -> ~ F (ptr_addr L0 p) -> 0 <= i < n ->
        ~ E (ptr_addr L0 p + i) -> ptr_addr L0 p + i <> a)) ->
  relay_post Bm API K E F L0 A0 R0 m0 md0 L1 A1 R0 m2 md1.
Proof using AX EU BW SEGS.
  intros K E F L0 A0 R0 m0 md0 L1 A1 m1 md1 m2 W P1 MU WM IME HW.
  destruct P1 as (M1 & W1 & B1 & LL1 & LN1 & AD1 & SV1 & Z1 & OW1 & RP1 & MD1 & FR1 & BY1 & SC1).
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_lt as ACL.
  assert (SAME : forall a, 0 <= a < 2 ^ 64 -> outside W a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
  { intros a Ha Ho. apply MU. rewrite unsigned_lit by lia. exact Ho. }
  assert (BADDR : forall p n i, In (p, n) (user_blocks A1) -> 0 <= i < n ->
            4096 <= ptr_addr L1 p /\ ptr_addr L1 p + n <= YM05.alloc_ceiling /\ ~ in_img Bm (ptr_addr L1 p + i) /\
            ~ owned Bm L1 A1 (ptr_addr L1 p + i)).
  { intros p n i Hp Hi.
    destruct (mr_blocks Bm _ LAWS L1 A1 m1 md1 p n i M1 Hp Hi) as (_ & H4 & Hc & Ho).
    split; [exact H4|]. split; [exact Hc|]. split; [exact (ax_blocks_img AX L1 A1 m1 md1 p n i M1 Hp Hi)|]. exact Ho. }
  assert (OWN : forall a, owned Bm L1 A1 a -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros a Ho. pose proof (sb_low L1 A1 m1 md1 a M1 Ho) as LOWa.
    split; [lia|].
    destruct (HW a ltac:(lia)) as [H|[H|[H|[H|(_ & (q & k & Hq & Hqa) & _)]]]]; [exact H | lia | |
      exfalso; exact (EU L1 A1 m1 md1 a M1 H Ho) | ].
    - exfalso. exact (sb_not_owned_img L1 A1 m1 md1 a M1 (proj1 H) Ho).
    - exfalso. unfold blocks in Hq. apply in_map_iff in Hq as ([p k'] & Eq & Hp). cbn [fst snd] in Eq. injection Eq as <- <-.
      destruct (BADDR p k' (a - ptr_addr L1 p) Hp ltac:(lia)) as (_ & _ & _ & No).
      replace (ptr_addr L1 p + (a - ptr_addr L1 p)) with a in No by lia. exact (No Ho). }
  destruct (mr_model Bm _ LAWS L1 A1 m1 md1 M1) as (Hh & Hl & Hm).
  assert (M2 : aa_MR API L1 A1 m2 md1).
  { apply (mr_frame Bm _ LAWS L1 A1 m1 m2 md1 md1 M1).
    - intros a Ho. destruct (OWN a Ho) as [Ha Hout]. unfold mbyte. rewrite (SAME a Ha Hout). reflexivity.
    - intros a Ho [b Hb]. destruct (OWN a Ho) as [Ha Hout]. exists b. rewrite (SAME a Ha Hout). exact Hb.
    - intros p n i Hp Hi. destruct (BADDR p n i Hp Hi) as (H4 & Hc & NI & _).
      assert (Wr : writable_at (ms_segs Bm) m1 (ptr_addr L1 p + i)).
      { apply (BW L1 A1 m1 md1 (ptr_addr L1 p) n i M1); [|exact Hi].
        unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact Hp]. }
      apply (present_of_writable_out Bm SEGS m2 (ptr_addr L1 p + i) ltac:(lia) NI). rewrite <- SEGS. apply WM. exact Wr.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hm. }
  split; [exact M2|]. split; [exact W1|]. split; [exact B1|]. split; [exact LL1|]. split; [exact LN1|].
  split; [exact AD1|]. split; [exact SV1|]. split; [exact Z1|]. split; [exact OW1|]. split; [exact RP1|].
  split; [exact MD1|].
  split.
  { intros a Ha NO0 NO1 NS NE.
    assert (AR : 0 <= a < 2 ^ 64).
    { destruct Ha as [Ha|Ha]; [pose proof (@YM05.alloc_ceiling_value rc); lia|].
      pose proof (in_img_low Bm SEGS a Ha). lia. }
    assert (Hout : outside W a).
    { destruct (HW a AR) as [H|[(H & _)|[(_ & H)|[H|(NI & (q & k & Hq & Hqa) & _)]]]];
        [exact H | exfalso; apply NS; left; exact H | exfalso; exact (NE H) | exfalso; apply NS; right; exact H |].
      exfalso. unfold blocks in Hq. apply in_map_iff in Hq as ([p k'] & Eq & Hp). cbn [fst snd] in Eq. injection Eq as <- <-.
      destruct (BADDR p k' (a - ptr_addr L1 p) Hp ltac:(lia)) as (_ & Hc & _ & _).
      destruct Ha as [Ha|Ha]; [lia | exact (NI Ha)]. }
    destruct (FR1 a Ha NO0 NO1 NS NE) as [E1 W1'].
    split.
    - unfold mbyte. rewrite (SAME a AR Hout). exact E1.
    - unfold writable_at, wview in *. rewrite (SAME a AR Hout). exact W1'. }
  split.
  { intros p n i H0 H1 NF Hi NE.
    pose proof (AD1 p n H0 H1 NF) as EA.
    destruct (BADDR p n i H1 Hi) as (H4 & Hc & NI & _). rewrite EA in H4, Hc, NI.
    assert (Hout : outside W (ptr_addr L0 p + i)).
    { destruct (HW (ptr_addr L0 p + i) ltac:(lia)) as [H|[(H & H')|[(H & _)|[H|(_ & _ & Hne)]]]];
        [exact H | lia | exfalso; exact (NI (proj1 H)) | exfalso; exact (NI (IME _ H)) |].
      exfalso. exact (Hne p n i H0 H1 NF Hi NE eq_refl). }
    unfold mbyte at 1. rewrite (SAME (ptr_addr L0 p + i) ltac:(lia) Hout). fold (mbyte (ms_segs Bm) m1 (ptr_addr L0 p + i)).
    exact (BY1 p n i H0 H1 NF Hi NE). }
  intros a Ha. apply WM. exact (SC1 a Ha).
Qed.

Lemma sb_realloc_rp : forall L A R m md L' A' R' m' md' p n,
  WF A -> In (p, n) (user_blocks A) -> 0 < n -> aa_MR API L A m md ->
  call_post_k Bm (aa_MR API) REALLOC_STACK L A R m md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' R' m' md' ->
  (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')) ->
  (length (st_regions A) <= length (st_regions A'))%nat ->
  relay_post Bm API REALLOC_STACK (fun a => ptr_addr L p <= a < ptr_addr L p + n) (fun q => q = ptr_addr L p)
    L A R m md L' A' R' m' md'.
Proof using AX CTXO.
  intros L A R m md L' A' R' m' md' p n HW Hp Hn HM CP SURV LN.
  destruct CP as (M' & W' & B' & LL & AD & RP & MD & FR & BY & SC).
  split; [exact M'|]. split; [exact W'|]. split; [exact B'|]. split; [exact LL|]. split; [exact LN|].
  split; [intros q k H1 H2 _; exact (AD q k H1 H2)|].
  split; [intros q k H1 _ NF; apply SURV; [exact H1|]; intros ->; exact (NF eq_refl)|].
  split.
  { intros q H1.
    assert (Q : q <> p).
    { intros ->. pose proof (sb_nodup_fst _ p 0 n (YO10.user_block_ptrs_NoDup A HW) H1 Hp). lia. }
    pose proof (SURV q 0 H1 Q) as H2. split; [exact H2 | exact (AD q 0 H1 H2)]. }
  split; [intros a Hi Ho; exact (sb_owned_img L A m md L' A' m' md' a HM M' Hi Ho)|].
  split; [exact RP|]. split; [exact MD|].
  split; [intros a Ha N1 N2 NS NE; apply FR; [exact Ha | exact N1 | exact N2 | exact NS | exact NE]|].
  split; [intros q k i H1 H2 _ Hi _; exact (BY q k i H1 H2 Hi)|].
  exact SC.
Qed.

Lemma sb_null_rp : forall L A R m md L' A' R' m' md',
  aa_MR API L A m md ->
  call_post_k Bm (aa_MR API) REALLOC_STACK L A R m md (fun _ => False) L' A' R' m' md' ->
  (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) ->
  (length (st_regions A) <= length (st_regions A'))%nat ->
  relay_post Bm API REALLOC_STACK (fun _ => False) (fun _ => False) L A R m md L' A' R' m' md'.
Proof using AX CTXO.
  intros L A R m md L' A' R' m' md' HM CP SURV LN.
  destruct CP as (M' & W' & B' & LL & AD & RP & MD & FR & BY & SC).
  split; [exact M'|]. split; [exact W'|]. split; [exact B'|]. split; [exact LL|]. split; [exact LN|].
  split; [intros q k H1 H2 _; exact (AD q k H1 H2)|].
  split; [intros q k H1 _ _; exact (SURV q k H1)|].
  split; [intros q H1; pose proof (SURV q 0 H1) as H2; split; [exact H2 | exact (AD q 0 H1 H2)]|].
  split; [intros a Hi Ho; exact (sb_owned_img L A m md L' A' m' md' a HM M' Hi Ho)|].
  split; [exact RP|]. split; [exact MD|].
  split; [intros a Ha N1 N2 NS NE; apply FR; [exact Ha | exact N1 | exact N2 | exact NS | exact NE]|].
  split; [intros q k i H1 H2 _ Hi _; exact (BY q k i H1 H2 Hi)|].
  exact SC.
Qed.

End FR.
