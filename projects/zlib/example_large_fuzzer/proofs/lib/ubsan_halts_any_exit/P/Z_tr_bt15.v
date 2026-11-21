(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_scan1 Z_tr_cb3 Z_tr_bt1 Z_tr_bt2 Z_tr_bt10 Z_tr_bt12 Z_tr_bt13 Z_tr_bt14.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma g3i_model : forall s t FC DL HP HL HM DP BC OL SL MC f bits n h R m_,
  R = gen_bitlen_loop3i (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits n h -> n <> 0 -> m_ = arr_get HP (h - 1) ->
  R = (if MC <? m_ then gen_bitlen_loop3i f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits n (h - 1)
       else if arr_get DL m_ =? bits then gen_bitlen_loop3i f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits (n - 1) (h - 1)
       else gen_bitlen_loop3i f (bt_upd s t FC (arr_set DL m_ (wrap16 bits)) HP HL HM DP BC (wrap64 (OL + (bits - arr_get DL m_) * arr_get FC m_)) SL MC) t MC bits (n - 1) (h - 1)).
Proof.
  intros until m_. intros ER Hn Em. rewrite GL3i_step in ER. rewrite (proj2 (Z.eqb_neq n 0) Hn) in ER. cbn [negb] in ER.
  rewrite GB3i_flat in ER. rewrite <- Em in ER.
  destruct (MC <? m_); [exact ER|]. destruct (arr_get DL m_ =? bits); exact ER.
Qed.

Lemma g3i_ok_step : forall s t FC DL HP HL HM DP BC OL SL MC f bits n h m_,
  gb3i_ok t MC (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) bits n h -> n <> 0 -> m_ = arr_get HP (h - 1) ->
  1 <= h <= 573 /\ 0 <= m_ < 573
  /\ (if MC <? m_ then gb3i_ok t MC f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) bits n (h - 1)
      else if arr_get DL m_ =? bits then gb3i_ok t MC f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) bits (n - 1) (h - 1)
      else gb3i_ok t MC f (bt_upd s t FC (arr_set DL m_ (wrap16 bits)) HP HL HM DP BC (wrap64 (OL + (bits - arr_get DL m_) * arr_get FC m_)) SL MC) bits (n - 1) (h - 1)).
Proof.
  intros until m_. intros OK Hn Em. cbn [gb3i_ok] in OK. rewrite (proj2 (Z.eqb_neq n 0) Hn) in OK. cbn [negb] in OK.
  destruct OK as (A & B & C). rewrite bt_heap_get in B. rewrite <- Em in B. split; [exact A|]. split; [exact B|].
  rewrite GB3i_flat in C. rewrite <- Em in C.
  destruct (MC <? m_); [exact C|]. destruct (arr_get DL m_ =? bits); exact C.
Qed.

Lemma if_negb_false : forall (A : Type) (a b : A), (if negb false then a else b) = a.
Proof. reflexivity. Qed.

Lemma gb3_ok_S : forall t MC f X bits h,
  gb3_ok t MC (S f) X bits h =
  (if negb (bits =? 0) then
     gb3i_ok t MC 574 X bits (bl_count_get X bits) h
     /\ (let '(X', h') := gen_bitlen_loop3i 574 X t MC bits (bl_count_get X bits) h in gb3_ok t MC f X' (bits - 1) h')
   else True).
Proof. reflexivity. Qed.

Lemma g3_model : forall s t FC DL HP HL HM DP BC OL SL MC f bits h R,
  R = gen_bitlen_loop3 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits h -> bits <> 0 ->
  R = (let '(X', h') := gen_bitlen_loop3i 574 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits (arr_get BC bits) h in gen_bitlen_loop3 f X' t MC (bits - 1) h').
Proof.
  intros until R. intros ER Hb. rewrite GL3_step in ER. rewrite (proj2 (Z.eqb_neq bits 0) Hb) in ER. rewrite if_negb_false in ER.
  rewrite bt_bl_count_get in ER. exact ER.
Qed.

Lemma g3_ok_step : forall s t FC DL HP HL HM DP BC OL SL MC f bits h,
  gb3_ok t MC (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) bits h -> bits <> 0 ->
  gb3i_ok t MC 574 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) bits (arr_get BC bits) h
  /\ (let '(X', h') := gen_bitlen_loop3i 574 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits (arr_get BC bits) h in gb3_ok t MC f X' (bits - 1) h').
Proof.
  intros until h. intros OK Hb. rewrite gb3_ok_S in OK. rewrite (proj2 (Z.eqb_neq bits 0) Hb) in OK. rewrite if_negb_false in OK.
  rewrite bt_bl_count_get in OK. exact OK.
Qed.

Definition g3_DL (DL : arr) (mc m_ bits : Z) : arr := if (mc <? m_) || (arr_get DL m_ =? bits) then DL else arr_set DL m_ (wrap16 bits).
Definition g3_OL (FC DL : arr) (OL mc m_ bits : Z) : Z :=
  if (mc <? m_) || (arr_get DL m_ =? bits) then OL else wrap64 (OL + (bits - arr_get DL m_) * arr_get FC m_).
Definition g3_n (mc m_ n : Z) : Z := if mc <? m_ then n else n - 1.

Lemma g3i_model' : forall s t FC DL HP HL HM DP BC OL SL MC f bits n h R m_,
  R = gen_bitlen_loop3i (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t MC bits n h -> n <> 0 -> m_ = arr_get HP (h - 1) ->
  R = gen_bitlen_loop3i f (bt_upd s t FC (g3_DL DL MC m_ bits) HP HL HM DP BC (g3_OL FC DL OL MC m_ bits) SL MC) t MC bits (g3_n MC m_ n) (h - 1).
Proof.
  intros until m_. intros ER Hn Em. pose proof (g3i_model _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ER Hn Em) as E. unfold g3_DL, g3_OL, g3_n.
  destruct (MC <? m_); [exact E|]. destruct (arr_get DL m_ =? bits); exact E.
Qed.
Lemma g3i_ok_step' : forall s t FC DL HP HL HM DP BC OL SL MC f bits n h m_,
  gb3i_ok t MC (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) bits n h -> n <> 0 -> m_ = arr_get HP (h - 1) ->
  1 <= h <= 573 /\ 0 <= m_ < 573
  /\ gb3i_ok t MC f (bt_upd s t FC (g3_DL DL MC m_ bits) HP HL HM DP BC (g3_OL FC DL OL MC m_ bits) SL MC) bits (g3_n MC m_ n) (h - 1).
Proof.
  intros until m_. intros OK Hn Em. destruct (g3i_ok_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OK Hn Em) as (A & B & C). split; [exact A|]. split; [exact B|].
  unfold g3_DL, g3_OL, g3_n. destruct (MC <? m_); [exact C|]. destruct (arr_get DL m_ =? bits); exact C.
Qed.

Definition g3R (L : dlay) (T bits n h mc A3 : Z) (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) s1 (wz (dl_As L + 3004)) (wz h) (wz n) (wz A3) a4 a5 a6 a7
      (wz T) (wz mc) (wz (dl_As L + 5300)) s5 s6 (wz T) (wz mc) (wz bits) s10 s11 t3 t4 t5 t6.

Notation Wg3 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 5881, dl_As L + 5968)] (only parsing).

Definition g3_trip_post (L : dlay) (s : deflate_state) (T N bits n' h mc : Z) (FC DL' : arr) (OL' SL : Z)
    (ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a4 a5 a6 A3' h0 h1 h2 h3 h4 pcx m',
    ms' = MS (g3R L T bits n' (h - 1) mc A3' ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wg3 L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL' N)) /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL h0 h1 h2 h3 h4)
    /\ ((pcx = 0x1c338 /\ n' <> 0 /\ A3' = dl_As L + 3004 + 4 * (h - 1)) \/ (pcx = 0x1c30c /\ n' = 0)).

Lemma wz_mulmod : forall a b c, wz (a mod 18446744073709551616 * b + c) = wz (wrap64 (c + a * b)).
Proof.
  intros a b c. apply Z_to_bv_eqm. rewrite wrap64_mod, Z.mod_mod by lia. change 18446744073709551616 with (2^64).
  rewrite (Z.add_comm c). rewrite Z.add_mod by lia. rewrite (Z.mul_mod (a mod 2^64) b) by lia. rewrite Z.mod_mod by lia.
  rewrite <- Z.mul_mod by lia. rewrite <- Z.add_mod by lia. reflexivity.
Qed.

Ltac g3_latch L h n MU WM ARR GD :=
  let K3 := fresh "K3" in
  zs2; zstep; br_cases K3;
  [ reg_as (h + -1) (h - 1); reg_as (n + -1) (n - 1);
    apply evt_done; unfold g3_trip_post, g3R, bD_cells; do 11 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
    split; [exact ARR|]; split; [close_cells GD|]; right; split; [reflexivity| lia]
  | zs2; shl_norm; zs2; reg_as (h + -1) (h - 1); reg_as (n + -1) (n - 1);
    apply evt_done; unfold g3_trip_post, g3R, bD_cells; do 11 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
    split; [exact ARR|]; split; [close_cells GD|]; left; split; [reflexivity|]; split; [lia| lia] ].

Lemma g3_trip : forall (L : dlay) (s : deflate_state) (T N bits n h mc A3 m_ OL SL : Z) (FC DL HP : arr) (h0 h1 h2 h3 h4 : list byte)
    (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv psegs m -> dlay_ok L -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 ->
  A3 = dl_As L + 3004 + 4 * h -> 1 <= n < 65536 -> 1 <= h <= 573 -> m_ = arr_get HP (h - 1) -> 0 <= m_ < 573 -> -1 <= mc < N -> 1 <= bits <= 15 ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 ->
  evt psegs (g3_trip_post L s T N bits (g3_n mc m_ n) h mc FC (g3_DL DL mc m_ bits) (g3_OL FC DL OL mc m_ bits) SL
               ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (g3R L T bits n h mc A3 ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1c338) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA GD MI LAY RT1 RT2 RN LFC LDL LHP EA3 Rn Rh Em Rm Rmc Rb RDL RFC ROL. subst A3.
  pose proof (munch_refl (Wg3 L T N) m) as MU. pose proof (wmono_refl psegs m) as WM. lay_open LAY. unfold bD_cells in GD.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32.
  pose proof (u32arr_read psegs m _ (av32 HP 573) (h - 1) _ (wa (dl_As L + 3004 + 4 * h)) HPA (av32_nth HP 573 (h - 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDm. rewrite <- Em in RDm.
  unfold g3R. zs2. zs2. zs2. zstep. br_cases K.
  -
    assert (EDL : g3_DL DL mc m_ bits = DL) by (unfold g3_DL; rewrite (proj2 (Z.ltb_lt mc m_)) by lia; reflexivity).
    assert (EOL : g3_OL FC DL OL mc m_ bits = OL) by (unfold g3_OL; rewrite (proj2 (Z.ltb_lt mc m_)) by lia; reflexivity).
    assert (En' : g3_n mc m_ n = n) by (unfold g3_n; rewrite (proj2 (Z.ltb_lt mc m_)) by lia; reflexivity).
    rewrite EDL, EOL, En'. reg_as (h + -1) (h - 1).
    apply evt_done. unfold g3_trip_post, g3R, bD_cells. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact ARR|]. split; [exact GD|]. left. split; [reflexivity|]. split; [lia|]. lia.
  - assert (En' : g3_n mc m_ n = n - 1) by (unfold g3_n; rewrite (proj2 (Z.ltb_ge mc m_)) by lia; reflexivity). rewrite En'.
    pose proof (u16arr_read psegs m T (avct FC DL N) (2 * m_ + 1) _ (wa (T + m_ * 4 + 2)) ARR (avct_nth_dl FC DL N m_ ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDl.
    pose proof (u16arr_read psegs m T (avct FC DL N) (2 * m_) _ (wa (T + m_ * 4)) ARR (avct_nth_fc FC DL N m_ ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDf.
    pose proof (RDL m_ ltac:(lia)) as Rl. pose proof (RFC m_ ltac:(lia)) as Rf.
    zs2. shl_norm. zs2. zs2. rewrite zx16_small by lia. zstep. br_cases K2.
    +
      assert (EDL : g3_DL DL mc m_ bits = DL) by (unfold g3_DL; rewrite (proj2 (Z.eqb_eq (arr_get DL m_) bits)) by lia; rewrite orb_true_r; reflexivity).
      assert (EOL : g3_OL FC DL OL mc m_ bits = OL) by (unfold g3_OL; rewrite (proj2 (Z.eqb_eq (arr_get DL m_) bits)) by lia; rewrite orb_true_r; reflexivity).
      rewrite EDL, EOL.
      g3_latch L h n MU WM ARR GD.
    + zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zs2.
      rewrite wz_mulmod. zs2.
      ct_store_dl ARR FC DL N T m_ (wrap16 bits) ltac:(apply le2_wrap16; reflexivity).
      zs2.
      assert (NEb : (arr_get DL m_ =? bits) = false) by (apply Z.eqb_neq; lia).
      assert (EDL : g3_DL DL mc m_ bits = arr_set DL m_ (wrap16 bits)) by (unfold g3_DL; rewrite (proj2 (Z.ltb_ge mc m_)), NEb by lia; reflexivity).
      assert (EOL : g3_OL FC DL OL mc m_ bits = wrap64 (OL + (bits - arr_get DL m_) * arr_get FC m_)) by (unfold g3_OL; rewrite (proj2 (Z.ltb_ge mc m_)), NEb by lia; reflexivity).
      rewrite EDL, EOL.
      g3_latch L h n MU WM ARR GD.
Qed.

Lemma g3_DL_len : forall DL mc m_ bits, arr_len (g3_DL DL mc m_ bits) = arr_len DL.
Proof. intros. unfold g3_DL. destruct (_ || _); [reflexivity| apply arr_len_set]. Qed.
Lemma g3_DL_range : forall DL mc m_ bits n, (forall j, 0 <= j < n -> 0 <= arr_get DL j < 65536) -> forall j, 0 <= j < n -> 0 <= arr_get (g3_DL DL mc m_ bits) j < 65536.
Proof. intros DL mc m_ bits n H. unfold g3_DL. destruct (_ || _); [exact H| apply arr_set_range16; exact H]. Qed.
Lemma g3_OL_range : forall FC DL OL mc m_ bits, 0 <= OL < 2^64 -> 0 <= g3_OL FC DL OL mc m_ bits < 2^64.
Proof. intros. unfold g3_OL. destruct (_ || _); [assumption| apply wrap64_range]. Qed.

Definition g3i_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T N bits mc : Z) (FC HP : arr) (HL HM : Z) (DP BC : arr) (SL : Z) (R : deflate_state * Z)
    (ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists a4 a5 a6 A3' h0 h1 h2 h3 h4 DL' OL' h' m',
    ms' = MS (g3R L T bits 0 h' mc A3' ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1c30c) fc None m' (seg_rom psegs)
    /\ munch (Wg3 L T N) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL' N)) /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL h0 h1 h2 h3 h4)
    /\ R = (bt_upd s t FC DL' HP HL HM DP BC OL' SL mc, h')
    /\ arr_len DL' = N /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64 /\ 0 <= h' <= 573.

Lemma g3i_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N bits n h mc A3 OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R : deflate_state * Z) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv psegs m -> dlay_ok L -> munch (Wg3 L T N) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 ->
  A3 = dl_As L + 3004 + 4 * h -> 1 <= n < 65536 -> 0 <= h -> h < Z.of_nat f -> -1 <= mc < N -> 1 <= bits <= 15 ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 ->
  R = gen_bitlen_loop3i f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc bits n h ->
  gb3i_ok t mc f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) bits n h ->
  evt psegs (g3i_loop_post L s t T N bits mc FC HP HL HM DP BC SL R ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (g3R L T bits n h mc A3 ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1c338) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA GD MI LAY MU WM RT1 RT2 RN LFC LDL LHP EA3 Rn Rh0 Hf Rmc Rb RDL RFC ROL ER OK.
  { exfalso. lia. }
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32.
  destruct (g3i_ok_step' s t FC DL HP HL HM DP BC OL SL mc f bits n h (arr_get HP (h - 1)) OK ltac:(lia) eq_refl) as (Rh & Rm & OK').
  pose proof (g3i_model' s t FC DL HP HL HM DP BC OL SL mc f bits n h R (arr_get HP (h - 1)) ER ltac:(lia) eq_refl) as ER'. clear ER OK.
  set (m_ := arr_get HP (h - 1)) in *.
  pose proof (avct_zlength FC (g3_DL DL mc m_ bits) N ltac:(lia)) as LCT'.
  call (g3_trip L s T N bits n h mc A3 m_ OL SL FC DL HP h0 h1 h2 h3 h4).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact GD. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. }
  1:{ exact EA3. } 1:{ exact Rn. } 1:{ exact Rh. } 1:{ reflexivity. } 1:{ exact Rm. } 1:{ exact Rmc. } 1:{ exact Rb. } 1:{ exact RDL. } 1:{ exact RFC. } 1:{ exact ROL. }
  match goal with H : _ \/ _ |- _ => destruct H as [(-> & K & EA')|(-> & K)] end.
  - assert (Rn' : 1 <= g3_n mc m_ n < 65536) by (revert K; unfold g3_n; destruct (mc <? m_); lia).
    match goal with HT : u8arr psegs ?mm T _, HG : rw_cells psegs ?mm (dl_As L + 5881) (bD_cells L s _ SL ?g0 ?g1 ?g2 ?g3 ?g4) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N bits (g3_n mc m_ n) (h - 1) mc _ (g3_OL FC DL OL mc m_ bits) SL FC (g3_DL DL mc m_ bits) HP HL HM DP BC g0 g1 g2 g3 g4 R m0);
        [exact HT| exact HPA| exact HG| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact RN| exact LFC| rewrite g3_DL_len; exact LDL| exact LHP
        | exact EA'| exact Rn'| lia| lia| exact Rmc| exact Rb| apply g3_DL_range; exact RDL| exact RFC| apply g3_OL_range; exact ROL| exact ER'| exact OK'] end.
  - rewrite K in ER'. rewrite GL3i_done in ER'.
    rewrite K.
    apply evt_done. unfold g3i_loop_post. do 9 eexists. exists (g3_DL DL mc m_ bits), (g3_OL FC DL OL mc m_ bits), (h - 1). eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact ER'|].
    split; [rewrite g3_DL_len; exact LDL|]. split; [apply g3_DL_range; exact RDL|]. split; [apply g3_OL_range; exact ROL|]. lia.
Qed.

Definition g3oR (L : dlay) (T bits h mc : Z) (ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) s1 (wz (dl_As L + 3004)) (wz h) a2 a3 a4 a5 a6 a7
      (wz T) (wz mc) (wz (dl_As L + 5300)) s5 s6 (wz T) (wz mc) (wz bits) s10 s11 t3 t4 t5 t6.

Definition g3_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T N mc : Z) (FC HP : arr) (HL HM : Z) (DP BC : arr) (SL : Z) (R : deflate_state)
    (ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists a2 a3 a4 a5 a6 h0 h1 h2 h3 h4 DL' OL' h' m',
    ms' = MS (g3oR L T 0 h' mc ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1c378) fc None m' (seg_rom psegs)
    /\ munch (Wg3 L T N) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL' N)) /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL h0 h1 h2 h3 h4)
    /\ R = bt_upd s t FC DL' HP HL HM DP BC OL' SL mc
    /\ arr_len DL' = N /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64.

Lemma g3_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N bits h mc OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R : deflate_state) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv psegs m -> dlay_ok L -> munch (Wg3 L T N) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  Z.of_nat f = bits -> 1 <= bits <= 15 -> 0 <= h <= 573 -> -1 <= mc < N ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 ->
  R = gen_bitlen_loop3 f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc bits h ->
  gb3_ok t mc f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) bits h ->
  evt psegs (g3_loop_post L s t T N mc FC HP HL HM DP BC SL R ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (g3oR L T bits h mc ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1c314) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA BLC GD MI LAY MU WM RT1 RT2 RN LFC LDL LHP LBC Ef Rb Rh Rmc RBC RDL RFC ROL ER OK.
  { exfalso. lia. }
  pose proof (g3_model s t FC DL HP HL HM DP BC OL SL mc f bits h R ER ltac:(lia)) as ER'.
  destruct (g3_ok_step s t FC DL HP HL HM DP BC OL SL mc f bits h OK ltac:(lia)) as [OKi OKo]. clear ER OK.

  assert (TAIL : forall (DL' : arr) (OL' h' : Z) (g0 g1 g2 g3 g4 : list byte) (b2 b3 b4 b5 b6 : word) (m' : mem),
    u8arr psegs m' T (u16s (avct FC DL' N)) -> u32arr psegs m' (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC 16)) ->
    rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL g0 g1 g2 g3 g4) -> mem_inv psegs m' -> munch (Wg3 L T N) m0 m' -> wmono psegs m0 m' ->
    arr_len DL' = N -> (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) -> 0 <= OL' < 2^64 -> 0 <= h' <= 573 ->
    R = gen_bitlen_loop3 f (bt_upd s t FC DL' HP HL HM DP BC OL' SL mc) t mc (bits - 1) h' ->
    gb3_ok t mc f (bt_upd s t FC DL' HP HL HM DP BC OL' SL mc) (bits - 1) h' ->
    evt psegs (g3_loop_post L s t T N mc FC HP HL HM DP BC SL R ra sp gp tp t0 t1 t2 s1 a7 s5 s6 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (g3oR L T bits h' mc ra sp gp tp t0 t1 t2 s1 b2 b3 b4 b5 b6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1c30c) fc None m' (seg_rom psegs))).
  { intros DL' OL' h' g0 g1 g2 g3 g4 b2 b3 b4 b5 b6 m' ARR' HPA' BLC' GD' MI' MU' WM' LDL' RDL' ROL' Rh' ER2 OK2.
    unfold g3oR. zs2. zstep. br_cases K; reg_as (bits + -1) (bits - 1).
    - replace (bits - 1) with 0 in * by lia. rewrite GL3_done in ER2.
      apply evt_done. unfold g3_loop_post, g3oR. do 10 eexists. exists DL', OL', h'. eexists.
      split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ARR'|]. split; [exact GD'|]. split; [exact ER2|].
      split; [exact LDL'|]. split; [exact RDL'| exact ROL'].
    - eapply (IH L s t T N (bits - 1) h' mc OL' SL FC DL' HP HL HM DP BC g0 g1 g2 g3 g4 R m0);
        [exact ARR'| exact HPA'| exact BLC'| exact GD'| exact MI'| exact LAY| exact MU'| exact WM'| exact RT1| exact RT2| exact RN| exact LFC| exact LDL'| exact LHP| exact LBC
        | lia| lia| exact Rh'| exact Rmc| exact RBC| exact RDL'| exact RFC| exact ROL'| exact ER2| exact OK2]. }
  pose proof LAY as LAY0. lay_open LAY0.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  pose proof (u16arr_read psegs m _ (av16 BC 16) bits _ (wa (dl_As L + 2976 + bits * 2)) BLC (av16_nth BC 16 bits ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDn.
  pose proof (RBC bits ltac:(lia)) as Rn.
  unfold g3oR. zs2. shl_norm. zs2. zs2. rewrite zx16_small by lia. zstep. br_cases K.
  - zs2. shl_norm. zs2.
    call (g3i_loop 574 L s t T N bits (arr_get BC bits) h mc _ OL SL FC DL HP HL HM DP BC h0 h1 h2 h3 h4
            (gen_bitlen_loop3i 574 (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc bits (arr_get BC bits) h) m).
    1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact GD. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
    1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ change (Z.of_nat 574) with 574. lia. } 1:{ exact Rmc. } 1:{ exact Rb. } 1:{ exact RDL. } 1:{ exact RFC. }
    1:{ exact ROL. } 1:{ reflexivity. } 1:{ exact OKi. }
    match goal with E : gen_bitlen_loop3i 574 _ _ _ _ _ _ = (_, _) |- _ => rewrite E in ER', OKo end.
    match goal with HT : u8arr psegs ?mm T (u16s (avct FC ?dl' N)), HG : rw_cells psegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' SL ?g0 ?g1 ?g2 ?g3 ?g4) |- evt _ _ (MS (g3R _ _ _ _ ?hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mm _) =>
      eapply (TAIL dl' ol' hh g0 g1 g2 g3 g4); [exact HT| eassumption| eassumption| exact HG| eassumption| exact MU| exact WM| assumption| assumption| assumption| lia| exact ER'| exact OKo] end.
  -
    rewrite K in ER', OKo. rewrite GL3i_done in ER', OKo.
    zs2.
    eapply (TAIL DL OL h h0 h1 h2 h3 h4); [exact ARR| exact HPA| exact BLC| exact GD| exact MI| exact MU| exact WM| exact LDL| exact RDL| exact ROL| exact Rh| exact ER'| exact OKo].
Qed.
