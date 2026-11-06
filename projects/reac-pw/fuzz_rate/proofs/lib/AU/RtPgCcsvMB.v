(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvM.v at b929052adf57; the same model for
   image B (fuzz_rate.asan-ubsan): only the comments change, to image B's addresses and registers; every
   statement and proof is the image-A file's (no term reads an image). *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on its unstripped twin sha256
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the value model of check_csv (0x837c0), that is
   of the inlined csv_holds (fuzz_rate.c:103-128), in the form the walk of its three passes (0x83948 .. 0x83a90) and of
   its tail (0x83a90 .. 0x83b38) uses. Proves no function (kind: model lemma): every lemma here is a fact about the
   Pod model lib/Pod/RateCsv.v (csv_digits, csv_dec, csv_step, csv_prefix, csv_list, csv_cut) and lib/Pod/RateCfg.v
   (closed_list, rate_bit), about the machine's integer operations on words, or about byte lists read through garr8 /
   aview. No machine state is run here.

   The code, by address (registers: a2 = i, t3 = n, s6 = mask, s8 = want (frame + 32, 40 bytes), a3 = d (frame + 112,
   8 bytes), s3 = d - 1):
   - 0x83948 `srlw a0,s6,a2; andi a0,a0,1; beqz a0`: bit i of the low 32 bits of mask ([ccsv_bit_word], [ccsv_bit_sv],
     [ccsv_bit_v], [ccsv_bit_vi]; [ccsv_bit_mod8] and [ccsv_bit_rate] relate it to RateCsv's csv_step / csv_bit).
   - bit set: v := closed_list[i] by an instrumented 4-byte load (44100, 48000, 96000: [ccsv_rate_range]).
   - 0x83978 .. 0x839bc, the do-while digit loop: turn j stores 48 + (v_j mod 10) at d + j, v_{j+1} = v_j / 10, and
     loops while v_j >= 10 ([ccsv_rdig], [ccsv_rdig_nth]; 5 turns for each rate, [ccsv_rdig_rates], [ccsv_rdig_len]).
   - 0x839d0 `beqz t3`: the comma ',' (44) at want + n exactly when n <> 0 ([ccsv_sep], [ccsv_sep_bridge],
     [ccsv_len0], [ccsv_empty]).
   - 0x839fc .. 0x83a4c, the reverse copy: want + n' + j := d + k - 1 - j for the k digits, so the bytes at want + n'
     are csv_dec v ([ccsv_dec_rdig], [ccsv_copy_nth], [ccsv_rev_garr8], [ccsv_copy_garr8]).
   - after pass i the bytes at want are csv_prefix mask (i + 1) and t3 is their count ([ccsv_pass_set],
     [ccsv_pass_clear], [ccsv_pass_len], [ccsv_pass_bytes], [ccsv_pass_garr8], the invariant [ccsv_inv] with
     [ccsv_inv_0], [ccsv_inv_set], [ccsv_inv_clear], [ccsv_inv_3]); every byte a pass writes lies in want[0 .. 17)
     ([ccsv_pass_room], [ccsv_pass_in_want]), so the 40-byte buffer never overflows.
   - the eight values of mask mod 8 ([ccsv_mod8_cases], [ccsv_case0] .. [ccsv_case7]): the three bits, the per-pass
     prefixes, csv_list mask and their lengths, each a closed computation.
   - the tail: `bne s3,t3` compares |csv_list mask| with the built n; n = 0 reads buf[0] ([ccsv_buf0]); n > 0 takes
     c = min(|csv_list mask|, n - 1) (`bltu s3,a0`, [ccsv_c_min], [ccsv_c_lt], [ccsv_c_ge], [ccsv_c_bound]), calls the
     bcmp wrapper on (buf, want, c) and reads buf[c]: the first c bytes of buf and of want agree in the form of the
     bcmp contract's answer (YG0d.v abcmp_realizes: `v = w64 0 <-> forall i, 0 <= i < n -> aview .. (x + i) = aview ..
     (y + i)`; [ccsv_bcmp_eq], [ccsv_bcmp_eq_av], [ccsv_bcmp_mask]) and buf[c] is the NUL ([ccsv_last],
     [ccsv_last_min]). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YP09 YK04 YI04 YI00 YP0m YG0n YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ===================================== the digit loop and the reverse copy ===================================== *)
(* The bytes the do-while digit loop (0x83978 .. 0x839bc) stores at d, d + 1, ...: turn j stores 48 + (v_j mod 10)
   and stops after the turn whose v_j is below 10 (`bltu t1,s5` with s5 = v_j + 9, t1 = 18); least significant first. *)
Fixpoint ccsv_rdig (fuel : nat) (v : Z) : list Z :=
  match fuel with
  | O => []
  | S f => (48 + v mod 10) :: (if v <? 10 then [] else ccsv_rdig f (v / 10))
  end.

(* RateCsv's csv_digits is the reverse of the digit loop's bytes, put in front of acc. *)
Lemma ccsv_digits_rdig : forall f x acc, 0 <= x -> csv_digits f x acc = rev (ccsv_rdig f x) ++ acc.
Proof.
  induction f as [|f IH]; intros x acc Hx; [reflexivity|].
  cbn [csv_digits ccsv_rdig]. destruct (Z.ltb_spec x 10) as [Hlt|Hge]; cbv iota.
  - rewrite Z.mod_small by lia. reflexivity.
  - rewrite IH by (apply Z.div_pos; lia). cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

(* "%d" of a nonnegative v is the digit loop's bytes reversed: what the reverse copy writes. *)
Lemma ccsv_dec_rdig : forall v, 0 <= v -> csv_dec v = rev (ccsv_rdig 11 v).
Proof.
  intros v Hv. unfold csv_dec. destruct (Z.ltb_spec v 0) as [Hlt|Hge]; [lia|]. cbv iota.
  rewrite ccsv_digits_rdig by exact Hv. apply app_nil_r.
Qed.

(* Turn j of the digit loop stores 48 + ((v / 10^j) mod 10). *)
Lemma ccsv_rdig_nth : forall f v j, 0 <= v -> (j < length (ccsv_rdig f v))%nat ->
  nth j (ccsv_rdig f v) 0 = 48 + (v / 10 ^ Z.of_nat j) mod 10.
Proof.
  induction f as [|f IH]; intros v j Hv Hj; cbn [ccsv_rdig length] in Hj |- *; [lia|].
  destruct j as [|j].
  - cbn [nth Z.of_nat]. rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
  - cbn [nth]. revert Hj. destruct (Z.ltb_spec v 10) as [Hlt|Hge]; cbv iota; intros Hj.
    + cbn [length] in Hj. lia.
    + rewrite IH by (try apply Z.div_pos; lia).
      rewrite Z.div_div; [| lia | apply Z.pow_pos_nonneg; lia].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
Qed.

(* The three rates: the bytes the digit loop leaves in d (5 turns each) and their reverse, "%d" of the rate. *)
Lemma ccsv_rdig_rates :
  ccsv_rdig 11 RATE_44K1 = [48; 48; 49; 52; 52] /\ ccsv_rdig 11 RATE_48K = [48; 48; 48; 56; 52] /\
  ccsv_rdig 11 RATE_96K = [48; 48; 48; 54; 57] /\
  csv_dec RATE_44K1 = [52; 52; 49; 48; 48] /\ csv_dec RATE_48K = [52; 56; 48; 48; 48] /\
  csv_dec RATE_96K = [57; 54; 48; 48; 48].
Proof. repeat split; vm_compute; reflexivity. Qed.

(* closed_list[i] for i = 0, 1, 2 is one of the three rates, positive and below 2^31 (the `lw` sign extension keeps it). *)
Lemma ccsv_rate_range : forall i, (i < 3)%nat ->
  (nth i closed_list 0 = RATE_44K1 \/ nth i closed_list 0 = RATE_48K \/ nth i closed_list 0 = RATE_96K) /\
  0 < nth i closed_list 0 < 2 ^ 31.
Proof.
  intros i Hi. destruct i as [|[|[|i]]]; [| | | lia]; cbn [nth closed_list]; unfold RATE_44K1, RATE_48K, RATE_96K;
    split; lia.
Qed.

(* Each rate has 5 digits: the digit loop runs 5 turns and the reverse copy moves 5 bytes. *)
Lemma ccsv_rdig_len : forall i, (i < 3)%nat -> length (ccsv_rdig 11 (nth i closed_list 0)) = 5%nat.
Proof. intros i Hi. destruct i as [|[|[|i]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia]. Qed.

Lemma ccsv_dec_len : forall i, (i < 3)%nat -> length (csv_dec (nth i closed_list 0)) = 5%nat.
Proof. intros i Hi. destruct i as [|[|[|i]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | lia]. Qed.

(* The reverse copy: byte j of "%d" of v is byte k - 1 - j of the digit loop's bytes (k of them). *)
Lemma ccsv_copy_nth : forall v j, 0 <= v -> (j < length (ccsv_rdig 11 v))%nat ->
  nth j (csv_dec v) 0 = nth (length (ccsv_rdig 11 v) - S j) (ccsv_rdig 11 v) 0.
Proof. intros v j Hv Hj. rewrite ccsv_dec_rdig by exact Hv. apply rev_nth. exact Hj. Qed.

(* The reverse copy in memory: if byte j at w is byte |l| - 1 - j at dd and dd holds l, then w holds rev l. *)
Lemma ccsv_rev_garr8 : forall segs mem dd w l, garr8 segs mem dd l ->
  (forall j, (j < length l)%nat -> mbyte segs mem (w + Z.of_nat j) = mbyte segs mem (dd + Z.of_nat (length l - S j))) ->
  garr8 segs mem w (rev l).
Proof.
  intros segs mem dd w l G Hc j Hj. rewrite length_rev in Hj. rewrite rev_nth by exact Hj.
  destruct (G (length l - S j)%nat ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
  intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite Hc by exact Hj. specialize (Hv 0%nat Hk). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. exact Hv.
Qed.

(* So when d holds the digit loop's bytes for v and the copy has run, want + n' holds csv_dec v. *)
Lemma ccsv_copy_garr8 : forall segs mem dd w v, 0 <= v -> garr8 segs mem dd (ccsv_rdig 11 v) ->
  (forall j, (j < length (ccsv_rdig 11 v))%nat ->
     mbyte segs mem (w + Z.of_nat j) = mbyte segs mem (dd + Z.of_nat (length (ccsv_rdig 11 v) - S j))) ->
  garr8 segs mem w (csv_dec v).
Proof.
  intros segs mem dd w v Hv G Hc. rewrite ccsv_dec_rdig by exact Hv. exact (ccsv_rev_garr8 segs mem dd w _ G Hc).
Qed.

(* ========================================= the comma and one pass ========================================= *)
(* The separator as the code decides it, by the register n (`beqz a4`): ',' (44) when n <> 0. *)
Definition ccsv_sep (n : Z) : list Z := if n =? 0 then [] else [44].

(* RateCsv's csv_step tests the list (`match acc with [] => [] | _ :: _ => [44] end`), the code tests its length. *)
Lemma ccsv_sep_bridge : forall acc : list Z,
  (match acc with [] => [] | _ :: _ => [44] end) = ccsv_sep (Z.of_nat (length acc)).
Proof. intros [|c acc]; reflexivity. Qed.

Lemma ccsv_len0 : forall l : list Z, Z.of_nat (length l) = 0 <-> l = [].
Proof. intros [|c l]; cbn [length]; split; intros H; try reflexivity; try lia; discriminate. Qed.

(* n = 0 exactly when the want buffer after the passes 0 .. i - 1 is empty. *)
Lemma ccsv_empty : forall mask i, Z.of_nat (length (csv_prefix mask i)) = 0 <-> csv_prefix mask i = [].
Proof. intros mask i. apply ccsv_len0. Qed.

Lemma ccsv_sep_len : forall n, length (ccsv_sep n) = if n =? 0 then 0%nat else 1%nat.
Proof. intros n. unfold ccsv_sep. destruct (n =? 0); reflexivity. Qed.

(* Pass i with bit i set appends the separator and "%d" of closed_list[i]; with bit i clear it changes nothing. *)
Lemma ccsv_pass_set : forall mask i, Z.testbit mask (Z.of_nat i) = true ->
  csv_prefix mask (S i) =
  csv_prefix mask i ++ ccsv_sep (Z.of_nat (length (csv_prefix mask i))) ++ csv_dec (nth i closed_list 0).
Proof. intros mask i Hb. rewrite csv_prefix_S, Hb. destruct (csv_prefix mask i); reflexivity. Qed.

Lemma ccsv_pass_clear : forall mask i, Z.testbit mask (Z.of_nat i) = false -> csv_prefix mask (S i) = csv_prefix mask i.
Proof. intros mask i Hb. rewrite csv_prefix_S, Hb. reflexivity. Qed.

(* The register a4 after a pass with bit i set: n + (n <> 0) + 5. *)
Lemma ccsv_pass_len : forall mask i, (i < 3)%nat -> Z.testbit mask (Z.of_nat i) = true ->
  Z.of_nat (length (csv_prefix mask (S i))) =
  Z.of_nat (length (csv_prefix mask i)) + (if Z.of_nat (length (csv_prefix mask i)) =? 0 then 0 else 1) + 5.
Proof.
  intros mask i Hi Hb. rewrite ccsv_pass_set by exact Hb. rewrite !length_app, ccsv_dec_len by exact Hi.
  unfold ccsv_sep. destruct (Z.of_nat (length (csv_prefix mask i)) =? 0); cbn [length]; lia.
Qed.

(* The per-pass bound (from RateCsv's csv_prefix_length): what a pass with bit i set writes ends at most 17 bytes
   into want. *)
Lemma ccsv_pass_room : forall mask i, (i < 3)%nat -> 0 <= mask -> Z.testbit mask (Z.of_nat i) = true ->
  Z.of_nat (length (csv_prefix mask i)) + (if Z.of_nat (length (csv_prefix mask i)) =? 0 then 0 else 1) + 5 <= 17.
Proof.
  intros mask i Hi Hm Hb. pose proof (ccsv_pass_len mask i Hi Hb) as E.
  pose proof (csv_prefix_length mask (S i) ltac:(lia) Hm) as L. lia.
Qed.

(* Every byte a pass writes lies in want[0 .. 17), inside the 40-byte want: the comma at n (when n <> 0) and digit j
   at n + (n <> 0) + j. *)
Lemma ccsv_pass_in_want : forall mask i, (i < 3)%nat -> 0 <= mask -> Z.testbit mask (Z.of_nat i) = true ->
  (Z.of_nat (length (csv_prefix mask i)) <> 0 -> 0 <= Z.of_nat (length (csv_prefix mask i)) < 17) /\
  (forall j, 0 <= j < 5 ->
     0 <= Z.of_nat (length (csv_prefix mask i)) + (if Z.of_nat (length (csv_prefix mask i)) =? 0 then 0 else 1) + j
       < 17) /\
  17 <= 40.
Proof.
  intros mask i Hi Hm Hb. pose proof (ccsv_pass_room mask i Hi Hm Hb) as R. revert R.
  destruct (Z.of_nat (length (csv_prefix mask i)) =? 0); intros R;
    (split; [intros _; lia | split; [intros j Hj; lia | lia]]).
Qed.

(* The bytes of the want buffer after a pass with bit i set, by index: the old ones, the comma, the digits. *)
Lemma ccsv_pass_bytes : forall mask i, Z.testbit mask (Z.of_nat i) = true ->
  (forall k, (k < length (csv_prefix mask i))%nat -> nth k (csv_prefix mask (S i)) 0 = nth k (csv_prefix mask i) 0) /\
  (csv_prefix mask i <> [] -> nth (length (csv_prefix mask i)) (csv_prefix mask (S i)) 0 = 44) /\
  (forall j, nth (length (csv_prefix mask i) + length (ccsv_sep (Z.of_nat (length (csv_prefix mask i)))) + j)
               (csv_prefix mask (S i)) 0 = nth j (csv_dec (nth i closed_list 0)) 0).
Proof.
  intros mask i Hb. rewrite ccsv_pass_set by exact Hb.
  generalize (csv_dec (nth i closed_list 0)) as D. generalize (csv_prefix mask i) as P. intros P D.
  split; [|split].
  - intros k Hk. apply app_nth1. exact Hk.
  - intros HP. rewrite app_nth2 by lia. rewrite Nat.sub_diag.
    destruct P as [|c P']; [exfalso; apply HP; reflexivity|]. reflexivity.
  - intros j. rewrite app_nth2 by lia.
    replace (length P + length (ccsv_sep (Z.of_nat (length P))) + j - length P)%nat
      with (length (ccsv_sep (Z.of_nat (length P))) + j)%nat by lia.
    rewrite app_nth2 by lia.
    replace (length (ccsv_sep (Z.of_nat (length P))) + j - length (ccsv_sep (Z.of_nat (length P))))%nat
      with j by lia.
    reflexivity.
Qed.

(* One pass in memory: the old bytes, the separator at w + n and the digits after it give the next prefix. *)
Lemma ccsv_pass_garr8 : forall segs mem w mask i, Z.testbit mask (Z.of_nat i) = true ->
  garr8 segs mem w (csv_prefix mask i) ->
  garr8 segs mem (w + Z.of_nat (length (csv_prefix mask i))) (ccsv_sep (Z.of_nat (length (csv_prefix mask i)))) ->
  garr8 segs mem (w + Z.of_nat (length (csv_prefix mask i)) +
                  Z.of_nat (length (ccsv_sep (Z.of_nat (length (csv_prefix mask i))))))
    (csv_dec (nth i closed_list 0)) ->
  garr8 segs mem w (csv_prefix mask (S i)).
Proof.
  intros segs mem w mask i Hb H1 H2 H3. rewrite ccsv_pass_set by exact Hb.
  apply (proj2 (garr8_app segs mem w _ _)). split; [exact H1|].
  apply (proj2 (garr8_app segs mem _ _ _)). split; [exact H2 | exact H3].
Qed.

(* The loop invariant at the pass head 0x83948: want holds csv_prefix mask i and a4 (the count t3) is its length. *)
Definition ccsv_inv (segs : list Segment) (mem : word -> option byte) (w : Z) (mask : Z) (i : nat) (a4 : word) : Prop :=
  garr8 segs mem w (csv_prefix mask i) /\ a4 = Z_to_bv 64 (Z.of_nat (length (csv_prefix mask i))).

Lemma ccsv_inv_0 : forall segs mem w mask, ccsv_inv segs mem w mask 0 (Z_to_bv 64 0).
Proof. intros segs mem w mask. unfold ccsv_inv. cbn [csv_prefix]. split; [apply garr8_nil | reflexivity]. Qed.

Lemma ccsv_inv_set : forall segs mem mem' w mask i a4, (i < 3)%nat -> Z.testbit mask (Z.of_nat i) = true ->
  ccsv_inv segs mem w mask i a4 ->
  (forall a, w <= a < w + Z.of_nat (length (csv_prefix mask i)) -> mbyte segs mem' a = mbyte segs mem a) ->
  garr8 segs mem' (w + Z.of_nat (length (csv_prefix mask i))) (ccsv_sep (Z.of_nat (length (csv_prefix mask i)))) ->
  garr8 segs mem' (w + Z.of_nat (length (csv_prefix mask i)) +
                   Z.of_nat (length (ccsv_sep (Z.of_nat (length (csv_prefix mask i))))))
    (csv_dec (nth i closed_list 0)) ->
  ccsv_inv segs mem' w mask (S i)
    (Z_to_bv 64 (Z.of_nat (length (csv_prefix mask i)) +
                 Z.of_nat (length (ccsv_sep (Z.of_nat (length (csv_prefix mask i))))) + 5)).
Proof.
  intros segs mem mem' w mask i a4 Hi Hb [G E] Hfr Hs Hd. split.
  - apply (ccsv_pass_garr8 segs mem' w mask i Hb); [| exact Hs | exact Hd].
    exact (garr8_frame segs mem mem' w _ G Hfr).
  - f_equal. rewrite ccsv_pass_set by exact Hb. rewrite !length_app, ccsv_dec_len by exact Hi. lia.
Qed.

Lemma ccsv_inv_clear : forall segs mem mem' w mask i a4, Z.testbit mask (Z.of_nat i) = false ->
  ccsv_inv segs mem w mask i a4 ->
  (forall a, w <= a < w + Z.of_nat (length (csv_prefix mask i)) -> mbyte segs mem' a = mbyte segs mem a) ->
  ccsv_inv segs mem' w mask (S i) a4.
Proof.
  intros segs mem mem' w mask i a4 Hb [G E] Hfr. unfold ccsv_inv. rewrite (ccsv_pass_clear mask i Hb).
  split; [exact (garr8_frame segs mem mem' w _ G Hfr) | exact E].
Qed.

(* After the three passes (0x83a90): want holds csv_list mask and a4 (the count t3) is |csv_list mask|. *)
Lemma ccsv_inv_3 : forall segs mem w mask a4, ccsv_inv segs mem w mask 3 a4 ->
  garr8 segs mem w (csv_list mask) /\ a4 = Z_to_bv 64 (Z.of_nat (length (csv_list mask))).
Proof. intros segs mem w mask a4 [G E]. split; [exact G | exact E]. Qed.

(* ============================================== the bit test ============================================== *)
Lemma ccsv_land1 : forall z, Z.land z 1 = z mod 2.
Proof. intros z. change (Z.land z 1) with (Z.land z (Z.ones 1)). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma ccsv_mod2_wrap64 : forall z, bv_wrap 64 z mod 2 = z mod 2.
Proof.
  intros z. rewrite bv_wrap64_mod. change (2 ^ 64) with 18446744073709551616.
  rewrite (Z.mod_eq z 18446744073709551616) by lia.
  replace (z - 18446744073709551616 * (z / 18446744073709551616))
    with (z + (-9223372036854775808 * (z / 18446744073709551616)) * 2) by ring.
  apply Z_mod_plus_full.
Qed.

Lemma ccsv_mod2_swrap32 : forall z, bv_swrap 32 z mod 2 = z mod 2.
Proof.
  intros z. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  rewrite (Z.mod_eq (z + 2147483648) 4294967296) by lia.
  replace (z + 2147483648 - 4294967296 * ((z + 2147483648) / 4294967296) - 2147483648)
    with (z + (-2147483648 * ((z + 2147483648) / 4294967296)) * 2) by ring.
  apply Z_mod_plus_full.
Qed.

(* `srlw a0,s6,a2; andi a0,a0,1` with s6 = mask and a2 = i (0 <= i < 32): the value is bit i of mask, as 1 or 0.
   The shift reads only the low 32 bits of mask; bit i of those is bit i of mask. *)
Lemma ccsv_bit_v : forall mask i, 0 <= i < 32 ->
  v_and (v_srlw (Z_to_bv 64 mask) (Z_to_bv 64 i)) (Z_to_bv 64 1) = Z_to_bv 64 (if Z.testbit mask i then 1 else 0).
Proof.
  intros mask i Hi. unfold v_and, v_srlw. f_equal. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 64 1) with 1.
  rewrite ccsv_land1, ccsv_mod2_wrap64, ccsv_mod2_swrap32.
  rewrite !bv_wrap64_mod, bv_wrap32_mod.
  rewrite (Z.mod_small i (2 ^ 64)) by lia. rewrite (Z.mod_small i 32) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite <- Z.testbit_spec' by lia.
  rewrite !Z.mod_pow2_bits_low by lia.
  destruct (Z.testbit mask i); reflexivity.
Qed.

(* The same value in the form the kit's sv denotation gives it (YP0m sv_denot of SAlu / SAluw). *)
Lemma ccsv_bit_word : forall mask i, 0 <= i < 32 ->
  alu64 ALU_AND (sext 64 (alu32 ALU_SRL (low32 (Z_to_bv 64 mask)) (low32 (Z_to_bv 64 i)))) (Z_to_bv 64 1) =
  Z_to_bv 64 (if Z.testbit mask i then 1 else 0).
Proof. intros mask i Hi. rewrite w_srlw, alu_and. exact (ccsv_bit_v mask i Hi). Qed.

(* The same value with the `andi` as the step lemma writes it (YK11 v_andi). *)
Lemma ccsv_bit_vi : forall mask i, 0 <= i < 32 ->
  v_andi (v_srlw (Z_to_bv 64 mask) (Z_to_bv 64 i)) 1 = Z_to_bv 64 (if Z.testbit mask i then 1 else 0).
Proof. intros mask i Hi. rewrite <- (ccsv_bit_v mask i Hi). unfold v_andi, v_and. reflexivity. Qed.

(* The same value for an sv of the engine whose denotation is mask (the register s6). *)
Lemma ccsv_bit_sv : forall E e mask i, 0 <= i < 32 -> sv_denot E e = Z_to_bv 64 mask ->
  sv_denot E (SAlu ALU_AND (SAluw ALU_SRL e (SLit i)) (SLit 1)) = Z_to_bv 64 (if Z.testbit mask i then 1 else 0).
Proof. intros E e mask i Hi He. cbn [sv_denot]. rewrite He. exact (ccsv_bit_word mask i Hi). Qed.

(* Bits 0, 1, 2 of mask are those of mask mod 8. *)
Lemma ccsv_bit_mod8 : forall mask i, 0 <= i < 3 -> Z.testbit mask i = Z.testbit (mask mod 8) i.
Proof. intros mask i Hi. change 8 with (2 ^ 3). rewrite Z.mod_pow2_bits_low by lia. reflexivity. Qed.

(* The machine's bit test, by mask mod 8 (each of the eight walks pins it to a literal). *)
Lemma ccsv_bit_word8 : forall mask i, 0 <= i < 3 ->
  alu64 ALU_AND (sext 64 (alu32 ALU_SRL (low32 (Z_to_bv 64 mask)) (low32 (Z_to_bv 64 i)))) (Z_to_bv 64 1) =
  Z_to_bv 64 (if Z.testbit (mask mod 8) i then 1 else 0).
Proof. intros mask i Hi. rewrite ccsv_bit_word by lia. rewrite (ccsv_bit_mod8 mask i Hi). reflexivity. Qed.

(* RateCsv states the drivable test over rate_bit (csv_bit); the machine's 1 / 0 is that test. *)
Lemma ccsv_bit_rate : forall mask i, (i < 3)%nat ->
  (if Z.testbit mask (Z.of_nat i) then 1 else 0) =
  (if Z.land (rate_bit (nth i closed_list 0)) mask =? 0 then 0 else 1).
Proof. intros mask i Hi. rewrite (csv_bit mask i Hi). destruct (Z.testbit mask (Z.of_nat i)); reflexivity. Qed.

(* =========================================== the eight values of mask mod 8 =========================================== *)
Lemma ccsv_mod8_cases : forall mask,
  mask mod 8 = 0 \/ mask mod 8 = 1 \/ mask mod 8 = 2 \/ mask mod 8 = 3 \/
  mask mod 8 = 4 \/ mask mod 8 = 5 \/ mask mod 8 = 6 \/ mask mod 8 = 7.
Proof. intros mask. pose proof (Z.mod_pos_bound mask 8 ltac:(lia)). lia. Qed.

Ltac ccsv_case_tac mask Hm E :=
  unfold csv_list;
  rewrite (csv_prefix_bits mask 1), (csv_prefix_bits mask 2), (csv_prefix_bits mask 3) by lia;
  rewrite (ccsv_bit_mod8 mask 0), (ccsv_bit_mod8 mask 1), (ccsv_bit_mod8 mask 2) by lia;
  rewrite E; repeat split; vm_compute; reflexivity.

Lemma ccsv_case0 : forall mask, 0 <= mask -> mask mod 8 = 0 ->
Z.testbit mask 0 = false /\ Z.testbit mask 1 = false /\ Z.testbit mask 2 = false /\
csv_prefix mask 1 = [] /\
csv_prefix mask 2 = [] /\
csv_list mask = [] /\
length (csv_prefix mask 1) = 0%nat /\ length (csv_prefix mask 2) = 0%nat /\ length (csv_list mask) = 0%nat.
Proof. intros mask Hm E. ccsv_case_tac mask Hm E. Qed.
Lemma ccsv_case1 : forall mask, 0 <= mask -> mask mod 8 = 1 ->
Z.testbit mask 0 = true /\ Z.testbit mask 1 = false /\ Z.testbit mask 2 = false /\
csv_prefix mask 1 = [52; 52; 49; 48; 48] /\
csv_prefix mask 2 = [52; 52; 49; 48; 48] /\
csv_list mask = [52; 52; 49; 48; 48] /\
length (csv_prefix mask 1) = 5%nat /\ length (csv_prefix mask 2) = 5%nat /\ length (csv_list mask) = 5%nat.
Proof. intros mask Hm E. ccsv_case_tac mask Hm E. Qed.
Lemma ccsv_case2 : forall mask, 0 <= mask -> mask mod 8 = 2 ->
Z.testbit mask 0 = false /\ Z.testbit mask 1 = true /\ Z.testbit mask 2 = false /\
csv_prefix mask 1 = [] /\
csv_prefix mask 2 = [52; 56; 48; 48; 48] /\
csv_list mask = [52; 56; 48; 48; 48] /\
length (csv_prefix mask 1) = 0%nat /\ length (csv_prefix mask 2) = 5%nat /\ length (csv_list mask) = 5%nat.
Proof. intros mask Hm E. ccsv_case_tac mask Hm E. Qed.
Lemma ccsv_case3 : forall mask, 0 <= mask -> mask mod 8 = 3 ->
Z.testbit mask 0 = true /\ Z.testbit mask 1 = true /\ Z.testbit mask 2 = false /\
csv_prefix mask 1 = [52; 52; 49; 48; 48] /\
csv_prefix mask 2 = [52; 52; 49; 48; 48; 44; 52; 56; 48; 48; 48] /\
csv_list mask = [52; 52; 49; 48; 48; 44; 52; 56; 48; 48; 48] /\
length (csv_prefix mask 1) = 5%nat /\ length (csv_prefix mask 2) = 11%nat /\ length (csv_list mask) = 11%nat.
Proof. intros mask Hm E. ccsv_case_tac mask Hm E. Qed.
Lemma ccsv_case4 : forall mask, 0 <= mask -> mask mod 8 = 4 ->
Z.testbit mask 0 = false /\ Z.testbit mask 1 = false /\ Z.testbit mask 2 = true /\
csv_prefix mask 1 = [] /\
csv_prefix mask 2 = [] /\
csv_list mask = [57; 54; 48; 48; 48] /\
length (csv_prefix mask 1) = 0%nat /\ length (csv_prefix mask 2) = 0%nat /\ length (csv_list mask) = 5%nat.
Proof. intros mask Hm E. ccsv_case_tac mask Hm E. Qed.
Lemma ccsv_case5 : forall mask, 0 <= mask -> mask mod 8 = 5 ->
Z.testbit mask 0 = true /\ Z.testbit mask 1 = false /\ Z.testbit mask 2 = true /\
csv_prefix mask 1 = [52; 52; 49; 48; 48] /\
csv_prefix mask 2 = [52; 52; 49; 48; 48] /\
csv_list mask = [52; 52; 49; 48; 48; 44; 57; 54; 48; 48; 48] /\
length (csv_prefix mask 1) = 5%nat /\ length (csv_prefix mask 2) = 5%nat /\ length (csv_list mask) = 11%nat.
Proof. intros mask Hm E. ccsv_case_tac mask Hm E. Qed.
Lemma ccsv_case6 : forall mask, 0 <= mask -> mask mod 8 = 6 ->
Z.testbit mask 0 = false /\ Z.testbit mask 1 = true /\ Z.testbit mask 2 = true /\
csv_prefix mask 1 = [] /\
csv_prefix mask 2 = [52; 56; 48; 48; 48] /\
csv_list mask = [52; 56; 48; 48; 48; 44; 57; 54; 48; 48; 48] /\
length (csv_prefix mask 1) = 0%nat /\ length (csv_prefix mask 2) = 5%nat /\ length (csv_list mask) = 11%nat.
Proof. intros mask Hm E. ccsv_case_tac mask Hm E. Qed.
Lemma ccsv_case7 : forall mask, 0 <= mask -> mask mod 8 = 7 ->
Z.testbit mask 0 = true /\ Z.testbit mask 1 = true /\ Z.testbit mask 2 = true /\
csv_prefix mask 1 = [52; 52; 49; 48; 48] /\
csv_prefix mask 2 = [52; 52; 49; 48; 48; 44; 52; 56; 48; 48; 48] /\
csv_list mask = [52; 52; 49; 48; 48; 44; 52; 56; 48; 48; 48; 44; 57; 54; 48; 48; 48] /\
length (csv_prefix mask 1) = 5%nat /\ length (csv_prefix mask 2) = 11%nat /\ length (csv_list mask) = 17%nat.
Proof. intros mask Hm E. ccsv_case_tac mask Hm E. Qed.

(* ================================================= the tail ================================================= *)
(* c = min(|L|, n - 1) (`addi a0,a0,-1; bltu s3,a0; mv s3,a0`): csv_cut L n is the first c bytes of L. *)
Lemma ccsv_c_min : forall L n, 1 <= n ->
  csv_cut L n = firstn (Z.to_nat (Z.min (Z.of_nat (length L)) (n - 1))) L /\
  Z.of_nat (length (csv_cut L n)) = Z.min (Z.of_nat (length L)) (n - 1).
Proof. intros L n Hn. split; [reflexivity|]. rewrite csv_cut_length by exact Hn. lia. Qed.

(* `bltu s3,a0` taken (|L| < n - 1): c = |L| and csv_cut L n is all of L. *)
Lemma ccsv_c_lt : forall L n, Z.of_nat (length L) < n - 1 -> csv_cut L n = L.
Proof. intros L n H. unfold csv_cut. rewrite Z.min_l by lia. rewrite Nat2Z.id. apply firstn_all. Qed.

(* `bltu s3,a0` not taken (n - 1 <= |L|): c = n - 1. *)
Lemma ccsv_c_ge : forall L n, 1 <= n -> n - 1 <= Z.of_nat (length L) -> Z.of_nat (length (csv_cut L n)) = n - 1.
Proof. intros L n H1 H2. rewrite csv_cut_length by exact H1. lia. Qed.

Lemma ccsv_c_bound : forall mask n, 0 <= mask -> 1 <= n ->
  0 <= Z.of_nat (length (csv_cut (csv_list mask) n)) <= 17 /\ Z.of_nat (length (csv_cut (csv_list mask) n)) < n.
Proof. intros mask n Hm Hn. rewrite csv_cut_length by exact Hn. pose proof (csv_list_length mask Hm). lia. Qed.

Lemma ccsv_firstn_nth : forall (l : list Z) k j, (j < k)%nat -> nth j (firstn k l) 0 = nth j l 0.
Proof.
  induction l as [|x l IH]; intros k j Hj; destruct k as [|k]; try lia; cbn [firstn].
  - destruct j; reflexivity.
  - destruct j as [|j]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

(* The first c bytes of the bytes the contract puts at buf are those of L; byte c is the NUL. *)
Lemma ccsv_cut_nth : forall L n j, (j < length (csv_cut L n))%nat -> nth j (csv_cut L n ++ [0]) 0 = nth j L 0.
Proof.
  intros L n j Hj. rewrite app_nth1 by exact Hj. unfold csv_cut in *. rewrite length_firstn in Hj.
  apply ccsv_firstn_nth. lia.
Qed.

Lemma ccsv_cut_nul : forall L n, nth (length (csv_cut L n)) (csv_cut L n ++ [0]) 0 = 0.
Proof. intros L n. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Section av. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* garr8 over the restricted memory read through aview (the bcmp contract's reader). *)
Lemma ccsv_garr8_aview : forall segs hid mem b l j, garr8 segs (mrestrict hid mem) b l -> (j < length l)%nat ->
  aview segs hid mem (b + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros segs hid mem b l j G Hj. unfold aview. cbv beta.
  rewrite (garr8_mbyte segs (mrestrict hid mem) b l j G Hj). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. exact (proj2 (G j Hj)).
Qed.

Lemma ccsv_garr8_aviewZ : forall segs hid mem b l i, garr8 segs (mrestrict hid mem) b l ->
  0 <= i < Z.of_nat (length l) -> aview segs hid mem (b + i) = Some (nth (Z.to_nat i) l 0).
Proof.
  intros segs hid mem b l i G Hi. rewrite <- (Z2Nat.id i) at 1 by lia. apply ccsv_garr8_aview; [exact G | lia].
Qed.

(* The n = 0 arm (0x83b04): buf[0] reads 0x5a. *)
Lemma ccsv_buf0 : forall segs hid mem b, garr8 segs (mrestrict hid mem) b [0x5a] -> aview segs hid mem b = Some 90.
Proof.
  intros segs hid mem b G. pose proof (ccsv_garr8_aview segs hid mem b [0x5a] 0 G ltac:(cbn [length]; lia)) as E.
  cbn [Z.of_nat nth] in E. rewrite Z.add_0_r in E. exact E.
Qed.

(* The n > 0 arm, the bcmp wrapper on (buf, want, c): the first c bytes agree, the right side of the bcmp contract's
   `v = w64 0 <-> forall i, 0 <= i < n -> aview .. (x + i) = aview .. (y + i)` (YG0d.v abcmp_realizes), with x = buf
   holding csv_cut L n ++ [0] and y = want holding L. *)
Lemma ccsv_bcmp_eq : forall segs hid mem b w L n,
  garr8 segs (mrestrict hid mem) b (csv_cut L n ++ [0]) -> garr8 segs (mrestrict hid mem) w L ->
  forall i, 0 <= i < Z.of_nat (length (csv_cut L n)) -> aview segs hid mem (b + i) = aview segs hid mem (w + i).
Proof.
  intros segs hid mem b w L n Gb Gw i Hi.
  assert (Hc : (length (csv_cut L n) <= length L)%nat) by (unfold csv_cut; rewrite length_firstn; lia).
  rewrite (ccsv_garr8_aviewZ segs hid mem b _ i Gb) by (rewrite length_app; cbn [length]; lia).
  rewrite (ccsv_garr8_aviewZ segs hid mem w _ i Gw) by lia.
  f_equal. apply ccsv_cut_nth. lia.
Qed.

(* The same with want given byte by byte through aview. *)
Lemma ccsv_bcmp_eq_av : forall segs hid mem b w L n,
  garr8 segs (mrestrict hid mem) b (csv_cut L n ++ [0]) ->
  (forall i, 0 <= i < Z.of_nat (length L) -> aview segs hid mem (w + i) = Some (nth (Z.to_nat i) L 0)) ->
  forall i, 0 <= i < Z.of_nat (length (csv_cut L n)) -> aview segs hid mem (b + i) = aview segs hid mem (w + i).
Proof.
  intros segs hid mem b w L n Gb Gw i Hi.
  assert (Hc : (length (csv_cut L n) <= length L)%nat) by (unfold csv_cut; rewrite length_firstn; lia).
  rewrite (ccsv_garr8_aviewZ segs hid mem b _ i Gb) by (rewrite length_app; cbn [length]; lia).
  rewrite (Gw i) by lia.
  f_equal. apply ccsv_cut_nth. lia.
Qed.

(* The contract's form: L = csv_list mask, c = min(|csv_list mask|, n - 1) as the code computes it. *)
Lemma ccsv_bcmp_mask : forall segs hid mem b w mask n, 1 <= n ->
  garr8 segs (mrestrict hid mem) b (csv_cut (csv_list mask) n ++ [0]) ->
  garr8 segs (mrestrict hid mem) w (csv_list mask) ->
  forall i, 0 <= i < Z.min (Z.of_nat (length (csv_list mask))) (n - 1) ->
  aview segs hid mem (b + i) = aview segs hid mem (w + i).
Proof.
  intros segs hid mem b w mask n Hn Gb Gw i Hi. apply (ccsv_bcmp_eq segs hid mem b w (csv_list mask) n Gb Gw).
  rewrite (proj2 (ccsv_c_min (csv_list mask) n Hn)). exact Hi.
Qed.

(* `lbu a0,0(buf + c)` reads the NUL. *)
Lemma ccsv_last : forall segs hid mem b L n, garr8 segs (mrestrict hid mem) b (csv_cut L n ++ [0]) ->
  aview segs hid mem (b + Z.of_nat (length (csv_cut L n))) = Some 0.
Proof.
  intros segs hid mem b L n G.
  rewrite (ccsv_garr8_aview segs hid mem b _ _ G) by (rewrite length_app; cbn [length]; lia).
  rewrite ccsv_cut_nul. reflexivity.
Qed.

Lemma ccsv_last_min : forall segs hid mem b L n, 1 <= n -> garr8 segs (mrestrict hid mem) b (csv_cut L n ++ [0]) ->
  aview segs hid mem (b + Z.min (Z.of_nat (length L)) (n - 1)) = Some 0.
Proof.
  intros segs hid mem b L n Hn G. rewrite <- (proj2 (ccsv_c_min L n Hn)). exact (ccsv_last segs hid mem b L n G).
Qed.

End av.

Print Assumptions ccsv_digits_rdig.
Print Assumptions ccsv_dec_rdig.
Print Assumptions ccsv_rdig_nth.
Print Assumptions ccsv_rdig_rates.
Print Assumptions ccsv_rate_range.
Print Assumptions ccsv_rdig_len.
Print Assumptions ccsv_dec_len.
Print Assumptions ccsv_copy_nth.
Print Assumptions ccsv_rev_garr8.
Print Assumptions ccsv_copy_garr8.
Print Assumptions ccsv_sep_bridge.
Print Assumptions ccsv_len0.
Print Assumptions ccsv_empty.
Print Assumptions ccsv_sep_len.
Print Assumptions ccsv_pass_set.
Print Assumptions ccsv_pass_clear.
Print Assumptions ccsv_pass_len.
Print Assumptions ccsv_pass_room.
Print Assumptions ccsv_pass_in_want.
Print Assumptions ccsv_pass_bytes.
Print Assumptions ccsv_pass_garr8.
Print Assumptions ccsv_inv_0.
Print Assumptions ccsv_inv_set.
Print Assumptions ccsv_inv_clear.
Print Assumptions ccsv_inv_3.
Print Assumptions ccsv_land1.
Print Assumptions ccsv_mod2_wrap64.
Print Assumptions ccsv_mod2_swrap32.
Print Assumptions ccsv_bit_v.
Print Assumptions ccsv_bit_word.
Print Assumptions ccsv_bit_vi.
Print Assumptions ccsv_bit_sv.
Print Assumptions ccsv_bit_mod8.
Print Assumptions ccsv_bit_word8.
Print Assumptions ccsv_bit_rate.
Print Assumptions ccsv_mod8_cases.
Print Assumptions ccsv_case0.
Print Assumptions ccsv_case1.
Print Assumptions ccsv_case2.
Print Assumptions ccsv_case3.
Print Assumptions ccsv_case4.
Print Assumptions ccsv_case5.
Print Assumptions ccsv_case6.
Print Assumptions ccsv_case7.
Print Assumptions ccsv_c_min.
Print Assumptions ccsv_c_lt.
Print Assumptions ccsv_c_ge.
Print Assumptions ccsv_c_bound.
Print Assumptions ccsv_firstn_nth.
Print Assumptions ccsv_cut_nth.
Print Assumptions ccsv_cut_nul.
Print Assumptions ccsv_garr8_aview.
Print Assumptions ccsv_garr8_aviewZ.
Print Assumptions ccsv_buf0.
Print Assumptions ccsv_bcmp_eq.
Print Assumptions ccsv_bcmp_eq_av.
Print Assumptions ccsv_bcmp_mask.
Print Assumptions ccsv_last.
Print Assumptions ccsv_last_min.
