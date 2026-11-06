(* Tight size bounds for the read-back tree t of json_read and for crt_tree t (M4 tb_read and M5 crt_zl_lin of
   a Theorem Labs lane's internal file LIVE-BYTES-PEAK.md section 5). Both are linear in |x| and charge each block of rtsz t to the input
   bytes that rtw counts (PackReparse.v). rtw_read (PackReparse.v) gives rtw t <= |x|: the reader consumes a disjoint
   segment of x for each value and key, and a string with decoded length E consumed at least ceil(E/3) + 2 bytes
   (jr_string_esc, rsl_le). That is the "raw string bodies are disjoint segments of x" fact the route needs. *)
From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import ReaderRes PackReparse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require check_round_trip_c.
Import ListNotations.
Local Open Scope Z_scope.

(* The bytes of one block: its size and its 16-byte head. *)
Definition tg_w (n : nat) : Z := Z.of_nat n + 16.

Lemma tg_app : forall (f : nat -> Z) a b, zl (map f (a ++ b)) = zl (map f a) + zl (map f b).
Proof. intros f a b. rewrite map_app. apply zl_app. Qed.

Lemma tg_nn : forall L, 0 <= zl (map Z.of_nat L).
Proof. induction L as [|a L IH]; cbn [map zl]; lia. Qed.

Lemma tg_w_zl : forall L, zl (map tg_w L) = zl (map Z.of_nat L) + 16 * Z.of_nat (length L).
Proof. induction L as [|a L IH]; cbn [map zl length]; [lia|]. rewrite IH. unfold tg_w. lia. Qed.

(* The kids and keys arrays of a container with N members: at most 258 bytes per unit of rkw. *)
Lemma tg_kb : forall o N, zl (map tg_w (rkb o (rfcap N 0 0))) <= 258 * Z.of_nat (rkw o N).
Proof.
  intros o [|N]; [cbn; lia|].
  destruct (rfcap_shape (S N) ltac:(lia)) as (j & E & H1 & H2). rewrite E.
  pose proof (Nat.pow_nonzero 2 j ltac:(discriminate)) as P.
  rewrite rkb_S by lia.
  destruct H2 as [->|H2]; [rewrite Nat.pow_0_r in *|];
    destruct o; cbv iota; cbn [map zl rkw]; unfold tg_w; lia.
Qed.

Lemma tg_str : forall s, tg_w (S (elen s)) <= 258 * Z.of_nat (rsl s).
Proof. intros s. rewrite rsl_z. unfold tg_w. lia. Qed.

Lemma tg_arr : forall items, Forall (fun u => zl (map tg_w (rtsz u)) <= 258 * Z.of_nat (rtw u)) items ->
  zl (map tg_w (flat_map rtsz items)) <= 258 * Z.of_nat (list_sum (map rtw items)).
Proof.
  induction items as [|u r IH]; intros H; [cbn; lia|].
  apply Forall_cons_iff in H as [H1 H2]. cbn [flat_map map]. rewrite tg_app, lsum_cons.
  specialize (IH H2). lia.
Qed.

Lemma tg_obj : forall ms, Forall (fun m => zl (map tg_w (rtsz (snd m))) <= 258 * Z.of_nat (rtw (snd m))) ms ->
  zl (map tg_w (flat_map (fun '(k, u) => S (elen k) :: rtsz u) ms)) <=
    258 * Z.of_nat (list_sum (map (fun '(k, u) => (rsl k + rtw u)%nat) ms)).
Proof.
  induction ms as [|[k u] r IH]; intros H; [cbn; lia|].
  apply Forall_cons_iff in H as [H1 H2]. cbn [snd] in H1. cbn [flat_map map]. rewrite tg_app, lsum_cons.
  cbn [map zl]. specialize (IH H2). pose proof (tg_str k). lia.
Qed.

(* Every block of rtsz t, head included, costs at most 258 bytes per unit of rtw t. *)
Theorem tb_rtw : forall t, zl (map tg_w (rtsz t)) <= 258 * Z.of_nat (rtw t).
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'.
  1-3: cbn; lia.
  - cbn [rtsz map zl rtw]. rewrite Nat2Z.inj_max. unfold tg_w. lia.
  - cbn [rtsz map zl rtw]. pose proof (tg_str s). lia.
  - rewrite rtsz_arr, rtw_arr, tg_app. pose proof (tg_kb false (length items)). pose proof (tg_arr items IH). lia.
  - rewrite rtsz_obj, rtw_obj, tg_app. pose proof (tg_kb true (length ms)). pose proof (tg_obj ms IH). lia.
Qed.

(* M4. *)
Theorem tb_read : forall sm x t, json_read sm x = Some t ->
  zl (map Z.of_nat (rtsz t)) + 16 * Z.of_nat (length (rtsz t)) <= 258 * Z.of_nat (length x) + 16448.
Proof.
  intros sm x t H. rewrite <- tg_w_zl. pose proof (tb_rtw t). pose proof (rtw_read sm x t H). lia.
Qed.

(* ["ab",{"k":7}]: blocks [448; 3; 448; 64; 2; 2], so 967 + 16 * 6 = 1063 <= 258 * 14 + 16448 = 20060. *)
Definition tg_ex1 : list Z := [91; 34; 97; 98; 34; 44; 123; 34; 107; 34; 58; 55; 125; 93].

Example tb_read_ex :
  match json_read jr_strtod tg_ex1 with
  | Some t => (zl (map Z.of_nat (rtsz t)) + 16 * Z.of_nat (length (rtsz t)), 258 * Z.of_nat (length tg_ex1) + 16448)
  | None => (0, 0)
  end = (1063, 20060).
Proof. vm_compute. reflexivity. Qed.

(* An object with N members has rtw at least 2N (its rkw). *)
Lemma tg_members : forall ms, (2 * length ms <= rtw (JObj ms))%nat.
Proof. intros ms. rewrite rtw_obj. destruct (length ms) as [|N]; cbn [rkw]; lia. Qed.

(* One more member grows the kids and keys arrays by at most 64 bytes per member, or 512 from empty. *)
Lemma tg_kb_step : forall N, zl (map Z.of_nat (rkb true (rfcap (S N) 0 0))) <=
  zl (map Z.of_nat (rkb true (rfcap N 0 0))) + 64 * Z.of_nat N + 512.
Proof.
  intros [|N]; [cbn; lia|].
  rewrite (rfcap_S (S N) 0 0). cbn [Nat.add].
  destruct (rfcap_shape (S N) ltac:(lia)) as (j & E & H1 & _). rewrite E.
  pose proof (Nat.pow_nonzero 2 j ltac:(discriminate)) as P. unfold gcap.
  destruct (Nat.ltb_spec (S N) (8 * 2 ^ j)) as [L|L]; cbv iota; [lia|].
  rewrite (proj2 (Nat.eqb_neq (8 * 2 ^ j) 0)) by lia. cbv iota.
  rewrite !rkb_S by lia. cbv iota. cbn [map zl]. lia.
Qed.

Lemma tg_set_cases : forall ms kname tv,
  (exists A v B, ms = A ++ (kname, v) :: B /\ pj_set_model ms kname tv = A ++ (kname, tv) :: B) \/
  pj_set_model ms kname tv = ms ++ [(kname, tv)].
Proof.
  induction ms as [|[k v] r IH]; intros kname tv; cbn [pj_set_model].
  - right. reflexivity.
  - destruct (list_eq_dec Z.eq_dec k kname) as [->|N].
    + left. exists [], v, r. split; reflexivity.
    + destruct (IH kname tv) as [(A & w & B & E1 & E2)|E].
      * left. exists ((k, v) :: A), w, B. rewrite E2, E1. split; reflexivity.
      * right. rewrite E. reflexivity.
Qed.

Lemma tg_mid : forall A k v w B,
  zl (map Z.of_nat (rtsz (JObj (A ++ (k, w) :: B)))) + zl (map Z.of_nat (rtsz v)) =
  zl (map Z.of_nat (rtsz (JObj (A ++ (k, v) :: B)))) + zl (map Z.of_nat (rtsz w)).
Proof.
  intros A k v w B. rewrite !rtsz_obj, !length_app. cbn [length]. rewrite !flat_map_app. cbn [flat_map].
  rewrite !tg_app. cbn [map zl]. lia.
Qed.

Lemma tg_snoc : forall ms k u,
  zl (map Z.of_nat (rtsz (JObj (ms ++ [(k, u)])))) =
  zl (map Z.of_nat (rkb true (rfcap (S (length ms)) 0 0))) - zl (map Z.of_nat (rkb true (rfcap (length ms) 0 0))) +
  zl (map Z.of_nat (rtsz (JObj ms))) + Z.of_nat (S (elen k)) + zl (map Z.of_nat (rtsz u)).
Proof.
  intros ms k u. rewrite !rtsz_obj, length_app, flat_map_app. cbn [length flat_map].
  rewrite Nat.add_1_r, app_nil_r, !tg_app. cbn [map zl]. lia.
Qed.

(* M5. *)
Theorem crt_zl_lin : forall sm x t, json_read sm x = Some t ->
  zl (map Z.of_nat (rtsz (check_round_trip_c.crt_tree t))) <=
    zl (map Z.of_nat (rtsz t)) + 32 * Z.of_nat (length x) + 544.
Proof.
  intros sm x t H. pose proof (rtw_read sm x t H) as Hw.
  destruct t as [| | | | | | ms]; try (cbn [check_round_trip_c.crt_tree]; lia).
  cbn [check_round_trip_c.crt_tree].
  assert (Hs : zl (map Z.of_nat (rtsz (JStr check_round_trip_c.STAMP))) = 21) by (vm_compute; reflexivity).
  destruct (tg_set_cases ms check_round_trip_c.MOD_AT (JStr check_round_trip_c.STAMP)) as [(A & v & B & E1 & E2)|E].
  - rewrite E2. pose proof (tg_mid A check_round_trip_c.MOD_AT v (JStr check_round_trip_c.STAMP) B) as M.
    rewrite <- E1 in M. pose proof (tg_nn (rtsz v)). lia.
  - rewrite E, tg_snoc.
    assert (Hk : Z.of_nat (S (elen check_round_trip_c.MOD_AT)) = 11) by (vm_compute; reflexivity).
    pose proof (tg_kb_step (length ms)). pose proof (tg_members ms). lia.
Qed.

(* {"k":7}: crt adds "modifiedAt" and the stamp, so 548 <= 516 + 32 * 7 + 544 = 1284. *)
Definition tg_ex2 : list Z := [123; 34; 107; 34; 58; 55; 125].

Example crt_zl_lin_ex :
  match json_read jr_strtod tg_ex2 with
  | Some t => (zl (map Z.of_nat (rtsz (check_round_trip_c.crt_tree t))),
               zl (map Z.of_nat (rtsz t)) + 32 * Z.of_nat (length tg_ex2) + 544)
  | None => (0, 0)
  end = (548, 1284).
Proof. vm_compute. reflexivity. Qed.
