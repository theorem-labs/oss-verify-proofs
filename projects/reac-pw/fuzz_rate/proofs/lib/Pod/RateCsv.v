(** The drivable list: what reac_rate_drivable_csv(mask, buf, buflen) returns and writes (src/reac_rate_cfg.c:49-75),
    and what check_csv (fuzz_rate.c:217-229, csv_holds :103-128) compares it with. Shared by the plain and the UBSan
    contracts (it names no image address). Statement text; no function of a binary is proved here.

    [csv_list mask] is the drivable rates in ascending order, "," between two of them, each rate's decimal digits as
    musl's printf writes "%d" for it ([csv_dec]: the same text as the printf model's pf_dec, disco
    Prog/printf_facts_c.v:48-54, so drivable_csv's snprintf post, T = sep ++ pf_dec rate, gives it). Rate i
    (i = 0, 1, 2: 44100, 48000, 96000, the `ordered` table) is drivable when bit i of mask is set: the code tests
    `reac_rate_bit(ordered[i]) & mask` with a 64-bit `and` (plain 0x14b30, UBSan 0x14e88), and reac_rate_bit of
    ordered[i] is 2^i ([csv_bit]). The separator is "" while the list is empty (`len ? "," : ""`, plain 0x14b38-0x14b40)
    and "," after. The whole list is at most 17 bytes ("44100,48000,96000"), so the code's `n < 0` and
    `len + n >= 32` branches never fire and every set bit appends ([csv_list_length]).

    [csv_cut L n] is the part of L the buffer of n > 0 bytes holds before its NUL: the first min(|L|, n - 1) bytes
    (reac_rate_cfg.c:69-73: copy = len < buflen - 1 ? len : buflen - 1). [csv_bytes] turns a list of byte values into
    bytes (the printf model's pf_bytes, the same map).

    Computation check against the compiled functions (2026-10-30, both images, unstripped twins sha256 4ecf851e...,
    593a406e...): an emulator run (unicorn 2.1.0 in docker rl3-check:1;
    snprintf's whole musl chain, memcpy and bcmp/memcmp run as compiled; abort and every unimp hooked;
    rate_lib_check.py sha256 da5a2038b58f copies these definitions line by line). All PASS in its plain result
    (sha256 e6135ed10fb9) and its UBSan result (e77cfeea3d55) on all 256 masks x all 24 buflens (6144 runs per
    image): reac_rate_drivable_csv returns |csv_list mask|; for buflen > 0 buf holds csv_cut L buflen and a NUL and
    its other bytes keep main's 0x5a; for buflen = 0 buf is untouched; s0-s11, ra, sp, gp, tp come back; every write
    lands in [sp - 6112, sp) or in buf (deepest stack measured: 1536 bytes); frm stays 0. check_csv then returns on
    every one of the 6144 states, and aborts on every one with len + 1. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg.
Import ListNotations.
Open Scope Z_scope.

(** "%d" of v, as musl writes it: the printf model's pf_digits / pf_dec, the same text. *)
Fixpoint csv_digits (fuel : nat) (x : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if x <? 10 then (48 + x) :: acc else csv_digits f (x / 10) ((48 + x mod 10) :: acc)
  end.

Definition csv_dec (v : Z) : list Z := if v <? 0 then 45 :: csv_digits 11 (- v) [] else csv_digits 11 v [].

(** One pass of the loop (reac_rate_cfg.c:56-68) at index i: append sep ++ "%d" of ordered[i] when bit i is set. *)
Definition csv_step (mask : Z) (acc : list Z) (i : nat) : list Z :=
  if Z.testbit mask (Z.of_nat i) then
    acc ++ (match acc with [] => [] | _ :: _ => [44] end) ++ csv_dec (nth i closed_list 0)
  else acc.

(** tmp after the passes 0 .. i - 1. *)
Fixpoint csv_prefix (mask : Z) (i : nat) : list Z :=
  match i with
  | O => []
  | S j => csv_step mask (csv_prefix mask j) j
  end.

Definition csv_list (mask : Z) : list Z := csv_prefix mask 3.

Definition csv_cut (L : list Z) (n : Z) : list Z := firstn (Z.to_nat (Z.min (Z.of_nat (length L)) (n - 1))) L.

Definition csv_bytes (l : list Z) : list byte := map (Z_to_bv 8) l.

(** ** Facts the callers use *)

(** The code's bit test is bit i of the mask. *)
Lemma csv_bit : forall mask i, (i < 3)%nat ->
  (Z.land (rate_bit (nth i closed_list 0)) mask =? 0) = negb (Z.testbit mask (Z.of_nat i)).
Proof.
  intros mask i Hi. rewrite Z.land_comm.
  destruct i as [|[|[|i]]]; [| | |lia]; cbn [nth closed_list];
    [change (rate_bit RATE_44K1) with (2 ^ 0) | change (rate_bit RATE_48K) with (2 ^ 1)
    | change (rate_bit RATE_96K) with (2 ^ 2)]; apply testbit_land_pow; lia.
Qed.

Definition CSV_44K1 : list Z := [52; 52; 49; 48; 48].
Definition CSV_48K : list Z := [52; 56; 48; 48; 48].
Definition CSV_96K : list Z := [57; 54; 48; 48; 48].

Lemma csv_dec_rates : csv_dec RATE_44K1 = CSV_44K1 /\ csv_dec RATE_48K = CSV_48K /\ csv_dec RATE_96K = CSV_96K.
Proof. repeat split; reflexivity. Qed.

(** The eight lists, by mask mod 8 (computation). *)
Definition CSV_TABLE : list (list Z) :=
  [ [];
    CSV_44K1;
    CSV_48K;
    CSV_44K1 ++ [44] ++ CSV_48K;
    CSV_96K;
    CSV_44K1 ++ [44] ++ CSV_96K;
    CSV_48K ++ [44] ++ CSV_96K;
    CSV_44K1 ++ [44] ++ CSV_48K ++ [44] ++ CSV_96K ].

Lemma csv_prefix_bits : forall mask i, (i <= 3)%nat -> 0 <= mask ->
  csv_prefix mask i = csv_prefix (mask mod 8) i.
Proof.
  intros mask i Hi Hm. induction i as [|i IH]; [reflexivity|].
  cbn [csv_prefix]. rewrite IH by lia. unfold csv_step.
  replace (Z.testbit (mask mod 8) (Z.of_nat i)) with (Z.testbit mask (Z.of_nat i)); [reflexivity|].
  change 8 with (2 ^ 3). rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.

Lemma csv_list_mod8 : forall mask, 0 <= mask -> csv_list mask = csv_list (mask mod 8).
Proof. intros mask Hm. apply csv_prefix_bits; lia. Qed.

Lemma csv_list_table : forall mask, 0 <= mask -> csv_list mask = nth (Z.to_nat (mask mod 8)) CSV_TABLE [].
Proof.
  intros mask Hm. rewrite csv_list_mod8 by exact Hm.
  assert (0 <= mask mod 8 < 8) as H by (apply Z.mod_pos_bound; lia).
  assert (mask mod 8 = 0 \/ mask mod 8 = 1 \/ mask mod 8 = 2 \/ mask mod 8 = 3 \/ mask mod 8 = 4 \/
          mask mod 8 = 5 \/ mask mod 8 = 6 \/ mask mod 8 = 7) as C by lia.
  destruct C as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; reflexivity.
Qed.

(** tmp holds at most 17 bytes after any number of passes of the loop (i <= 3). *)
Lemma csv_prefix_length : forall mask i, (i <= 3)%nat -> 0 <= mask -> (length (csv_prefix mask i) <= 17)%nat.
Proof.
  intros mask j Hj Hm. rewrite csv_prefix_bits by lia.
  assert (0 <= mask mod 8 < 8) as H by (apply Z.mod_pos_bound; lia).
  assert (mask mod 8 = 0 \/ mask mod 8 = 1 \/ mask mod 8 = 2 \/ mask mod 8 = 3 \/ mask mod 8 = 4 \/
          mask mod 8 = 5 \/ mask mod 8 = 6 \/ mask mod 8 = 7) as C by lia.
  apply Nat.leb_le.
  destruct j as [|[|[|[|j]]]]; [| | | |lia];
    destruct C as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; vm_compute; reflexivity.
Qed.

Lemma csv_list_length : forall mask, 0 <= mask -> (length (csv_list mask) <= 17)%nat.
Proof. intros mask Hm. apply csv_prefix_length; [lia | exact Hm]. Qed.

(** One pass appends sep ++ "%d" of the rate when the bit is set: the loop body's effect on tmp. *)
Lemma csv_prefix_S : forall mask i,
  csv_prefix mask (S i) =
  if Z.testbit mask (Z.of_nat i) then
    csv_prefix mask i ++ (match csv_prefix mask i with [] => [] | _ :: _ => [44] end) ++ csv_dec (nth i closed_list 0)
  else csv_prefix mask i.
Proof. reflexivity. Qed.

(** Every byte is a digit or a comma: no NUL, each below 256. *)
Lemma csv_list_chars : forall mask, 0 <= mask -> Forall (fun c => 44 <= c <= 57) (csv_list mask).
Proof.
  intros mask Hm. apply Forall_forall. intros c Hc. rewrite csv_list_table in Hc by exact Hm.
  assert (0 <= mask mod 8 < 8) as H by (apply Z.mod_pos_bound; lia).
  assert (mask mod 8 = 0 \/ mask mod 8 = 1 \/ mask mod 8 = 2 \/ mask mod 8 = 3 \/ mask mod 8 = 4 \/
          mask mod 8 = 5 \/ mask mod 8 = 6 \/ mask mod 8 = 7) as C by lia.
  destruct C as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E in Hc; cbn in Hc;
    repeat (destruct Hc as [Hc|Hc]; [subst c; lia|]); destruct Hc.
Qed.

Lemma csv_cut_length : forall L n, 1 <= n ->
  length (csv_cut L n) = Z.to_nat (Z.min (Z.of_nat (length L)) (n - 1)).
Proof. intros L n Hn. unfold csv_cut. rewrite length_firstn. lia. Qed.

Lemma csv_cut_firstn : forall L n, csv_cut L n = firstn (length (csv_cut L n)) L.
Proof.
  intros L n. unfold csv_cut. rewrite length_firstn. f_equal. lia.
Qed.

Lemma csv_bytes_app : forall l1 l2, csv_bytes (l1 ++ l2) = csv_bytes l1 ++ csv_bytes l2.
Proof. intros. apply map_app. Qed.

Lemma csv_bytes_length : forall l, length (csv_bytes l) = length l.
Proof. intros. apply length_map. Qed.

(** Examples: mask 7 is the whole list (17 bytes), mask 0 the empty one; a 5-byte buffer holds "4410". *)
Example csv_ex : csv_list 7 = [52; 52; 49; 48; 48; 44; 52; 56; 48; 48; 48; 44; 57; 54; 48; 48; 48]
  /\ csv_list 0 = [] /\ csv_list 0x105 = CSV_44K1 ++ [44] ++ CSV_96K /\ csv_cut (csv_list 1) 5 = [52; 52; 49; 48]
  /\ csv_cut (csv_list 7) 1 = [] /\ csv_cut (csv_list 2) 23 = CSV_48K.
Proof. repeat split; reflexivity. Qed.
