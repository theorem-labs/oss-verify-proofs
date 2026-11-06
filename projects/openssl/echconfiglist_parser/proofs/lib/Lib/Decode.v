(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem ITree Nodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma errno_ret_unsigned : forall e,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  bv_unsigned (errno_ret e) = (two_pow_64 - e)%Z.
Proof.
  intros e H1 H2. unfold errno_ret, two_pow_64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (Z.of_N 64) with 64%Z.
  replace (- e)%Z with (2 ^ 64 - e + (-1) * 2 ^ 64)%Z by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Fixpoint listNN_eqb (l1 l2 : list (word * word)) : bool :=
  match l1, l2 with
  | [], [] => true
  | (a1, n1) :: r1, (a2, n2) :: r2 =>
      bv_eqb a1 a2 && bv_eqb n1 n2 && listNN_eqb r1 r2
  | _, _ => false
  end.

Lemma listNN_eqb_eq : forall l1 l2, listNN_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|[a1 n1] r1 IH]; destruct l2 as [|[a2 n2] r2]; cbn;
    try (split; congruence).
  rewrite !Bool.andb_true_iff, !bv_eqb_eq, IH.
  split; [intros [[-> ->] ->]; auto | intro H; inversion H; auto].
Qed.

(* [comment removed for export] *)
Definition errno_of (r : word) : option Z :=
  if (2^64 - 4095 <=? bv_unsigned r)%Z then Some (2^64 - bv_unsigned r)%Z else None.

Lemma errno_of_Some : forall r e, errno_of r = Some e -> r = errno_ret e /\ (1 <= e <= 4095)%Z.
Proof.
  intros r e H. unfold errno_of in H. pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [|discriminate]. inversion H; subst.
  split; [|lia]. apply bv_eq. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
  replace (- (2 ^ 64 - bv_unsigned r))%Z with (bv_unsigned r + (-1) * 2^64)%Z by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma errno_of_errno_ret : forall e, (1 <= e <= 4095)%Z -> errno_of (errno_ret e) = Some e.
Proof.
  intros e He. unfold errno_of. rewrite errno_ret_unsigned by lia. unfold two_pow_64.
  destruct (Z.leb_spec0 (2^64 - 4095) (2^64 - e)); [|lia]. f_equal. lia.
Qed.

Lemma errno_of_small : forall r, (bv_unsigned r <= 2^64 - 4096)%Z -> errno_of r = None.
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [lia|reflexivity]. Qed.

Lemma errno_of_lit : forall z, (0 <= z <= 2^64 - 4096)%Z -> errno_of (Z_to_bv 64 z) = None.
Proof. intros. apply errno_of_small. rewrite unsigned_lit by lia. lia. Qed.

(* [comment removed for export] *)
Inductive sret : Type := SErr (e : Z) | SVal (v : Z).

(* [comment removed for export] *)
Definition no_cc (rsp : resp) : bool :=
  match eff_copies rsp, eff_copyins rsp with [], [] => true | _, _ => false end.

Ltac dec_cc cs ci H := cbn [no_cc eff_copies eff_copyins] in H; destruct cs; [|discriminate H]; destruct ci; [|discriminate H]; cbv iota in H.

(* [comment removed for export] *)
Definition dec_plain (ok : Z -> bool) (rsp : resp) : option sret :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ =>
      match errno_of r with
      | Some e => Some (SErr e)
      | None => if ok (bv_unsigned r) then Some (SVal (bv_unsigned r)) else None
      end
  | _ => None
  end else None.

Lemma dec_plain_Some : forall ok rsp a, dec_plain ok rsp = Some a ->
  match a with
  | SErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | SVal v => rsp = eff0 (Z_to_bv 64 v) /\ ok v = true /\ (0 <= v <= 2^64 - 4096)%Z
  end.
Proof.
  intros ok [r ws zs us cs ci] a H. unfold dec_plain in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct (errno_of r) as [e|] eqn:E.
  - inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
  - destruct (ok (bv_unsigned r)) eqn:Hok; [|discriminate]. inversion H; subst.
    pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
    unfold errno_of in E. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [discriminate|].
    unfold eff0. rewrite Z_to_bv_bv_unsigned. repeat split; try reflexivity; try exact Hok; lia.
Qed.

Lemma dec_plain_err : forall ok e, (1 <= e <= 4095)%Z -> dec_plain ok (efferr e) = Some (SErr e).
Proof. intros ok e He. unfold dec_plain, efferr, eff0. rewrite errno_of_errno_ret by lia. reflexivity. Qed.

Lemma dec_plain_val : forall ok z, (0 <= z <= 2^64 - 4096)%Z -> ok z = true ->
  dec_plain ok (eff0 (Z_to_bv 64 z)) = Some (SVal z).
Proof.
  intros ok z Hz Hok. unfold dec_plain, eff0. rewrite errno_of_lit by lia.
  rewrite unsigned_lit by lia. rewrite Hok. reflexivity.
Qed.

(* [comment removed for export] *)
Inductive read_ans : Type := RdErr (e : Z) | RdData (bs : list byte).

Definition dec_read (buf count : Z) (rsp : resp) : option read_ans :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ =>
      match errno_of r with
      | Some e => Some (RdErr e)
      | None => if (bv_unsigned r =? 0)%Z then Some (RdData []) else None
      end
  | mkEffectU r [(a, bs)] [] [] _ _ =>
      if bv_eqb a (Z_to_bv 64 buf) && (1 <=? Z.of_nat (length bs))%Z
         && (Z.of_nat (length bs) <=? count)%Z && (bv_unsigned r =? Z.of_nat (length bs))%Z
      then Some (RdData bs) else None
  | _ => None
  end else None.

Lemma dec_read_Some : forall buf count rsp a, (0 <= count)%Z -> dec_read buf count rsp = Some a ->
  match a with
  | RdErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | RdData bs => rsp = mkEffect (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) []
                 /\ (Z.of_nat (length bs) <= count)%Z
  end.
Proof.
  intros buf count [r ws zs us cs ci] a Hc H. unfold dec_read in H. dec_cc cs ci H.
  destruct ws as [|[a0 bs] [|? ?]]; try discriminate.
  - destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct (errno_of r) as [e|] eqn:E.
    + inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
    + destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst. cbn.
      split; [|lia]. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct (bv_eqb a0 (Z_to_bv 64 buf)) eqn:E1; [|discriminate].
    destruct (Z.leb_spec0 1 (Z.of_nat (length bs))); [|discriminate].
    destruct (Z.leb_spec0 (Z.of_nat (length bs)) count); [|discriminate].
    destruct (Z.eqb_spec (bv_unsigned r) (Z.of_nat (length bs))); [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. subst a0.
    destruct bs as [|b bs']; [cbn in *; lia|]. cbn [delivered_writes]. split; [|lia].
    f_equal. apply bv_eq. rewrite unsigned_lit. { assumption. }
    pose proof (bv_unsigned_in_range 64 r). unfold bv_modulus in *. lia.
Qed.

(* [comment removed for export] *)
Definition dec_count (count : Z) (rsp : resp) : option Z :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ => if (bv_unsigned r =? count)%Z then Some count else None
  | _ => None
  end else None.
Definition dec_write := dec_count.
Definition dec_writev := dec_count.

Lemma dec_count_Some : forall count rsp a, dec_count count rsp = Some a ->
  a = count /\ rsp = eff0 (Z_to_bv 64 count) /\ (0 <= count < 2^64)%Z.
Proof.
  intros count [r ws zs us cs ci] a H. unfold dec_count in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct (Z.eqb_spec (bv_unsigned r) count); [|discriminate]. inversion H; subst.
  pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  split; [reflexivity|]. split; [|lia]. unfold eff0. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dec_open : resp -> option sret := dec_plain (fun v => (3 <=? v)%Z && (v <=? 4096)%Z).
(* [comment removed for export] *)
Definition dec_close : resp -> option sret := dec_plain (fun v => (v =? 0)%Z).
(* [comment removed for export] *)
Definition dec_ioctl : resp -> option sret := dec_plain (fun _ => false).
(* [comment removed for export] *)
Definition dec_set_tid (rsp : resp) : option Z :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ =>
      if (0 <? bv_unsigned r)%Z && (bv_unsigned r <? PID_MAX_ENVELOPE)%Z then Some (bv_unsigned r) else None
  | _ => None
  end else None.
(* [comment removed for export] *)
Definition dec_exit (rsp : resp) : option Empty_set := None.

Lemma dec_set_tid_Some : forall rsp t, dec_set_tid rsp = Some t ->
  rsp = eff0 (Z_to_bv 64 t) /\ (0 < t < PID_MAX_ENVELOPE)%Z.
Proof.
  intros [r ws zs us cs ci] t H. unfold dec_set_tid in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct (Z.ltb_spec0 0 (bv_unsigned r)); [|discriminate].
  destruct (Z.ltb_spec0 (bv_unsigned r) PID_MAX_ENVELOPE); [|discriminate]. inversion H; subst.
  unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

(* [comment removed for export] *)
Definition dec_brk0 (rsp : resp) : option Z :=
  if no_cc rsp then match rsp with mkEffectU r [] [] [] _ _ => Some (bv_unsigned r) | _ => None end else None.

Lemma dec_brk0_Some : forall rsp b, dec_brk0 rsp = Some b -> rsp = eff0 (Z_to_bv 64 b) /\ (0 <= b < 2^64)%Z.
Proof.
  intros [r ws zs us cs ci] b H. unfold dec_brk0 in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. inversion H; subst.
  pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

(* [comment removed for export] *)
Definition brk_new_pages (cur req : Z) : option (Z * Z) :=
  let lo := page_round_up_Z cur in let hi := page_round_up_Z req in
  if (lo <? hi)%Z then Some (lo, hi - lo)%Z else None.

Definition zeros_of (p : option (Z * Z)) : list (word * word) :=
  match p with Some (lo, n) => [(wa lo, Z_to_bv 64 n)] | None => [] end.

Inductive brk_ans : Type := BrkGrown | BrkSame.

Definition dec_brk (cur req : Z) (rsp : resp) : option brk_ans :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] zs [] _ _ =>
      if (bv_unsigned r =? cur)%Z && match zs with [] => true | _ => false end then Some BrkSame
      else if (bv_unsigned r =? req)%Z && listNN_eqb zs (zeros_of (brk_new_pages cur req)) then Some BrkGrown
      else None
  | _ => None
  end else None.

Lemma dec_brk_Some : forall cur req rsp a, dec_brk cur req rsp = Some a ->
  match a with
  | BrkSame => rsp = eff0 (Z_to_bv 64 cur)
  | BrkGrown => rsp = mkEffect (Z_to_bv 64 req) [] (zeros_of (brk_new_pages cur req))
  end.
Proof.
  intros cur req [r ws zs us cs ci] a H. unfold dec_brk in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct (Z.eqb_spec (bv_unsigned r) cur).
  - destruct zs.
    + cbn [andb] in H. inversion H; subst. unfold eff0. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
      destruct (listNN_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listNN_eqb_eq in E.
      rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
    destruct (listNN_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listNN_eqb_eq in E.
    rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Definition CEIL_MIN : Z := 0x7fff7f800000.
Definition CEIL_MAX : Z := 0x7fffff800000.
Definition CEIL_BAND : Z := 0x800000000000.
Definition alloc_ceiling : Z := 0x7fffff800000.

(* [comment removed for export] *)
Inductive mmap_ans : Type := MmErr (e : Z) | MmOk (a : Z).

Definition avoids (a n : Z) (avoid : list (Z * Z)) : bool :=
  forallb (fun iv => (a + n <=? fst iv)%Z || (snd iv <=? a)%Z) avoid.

Definition mmap_len (len : Z) : Z := page_round_up_Z len.

(* [comment removed for export] *)
Section HC.
Context {HC : HeapCeil}.

Definition mmap_addr_ok (len : Z) (avoid : list (Z * Z)) (a : Z) : bool :=
  (a mod page_size =? 0)%Z && (0 <? a)%Z && (a + mmap_len len <=? hceil)%Z && avoids a (mmap_len len) avoid.

Definition dec_mmap (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ => match errno_of r with Some e => Some (MmErr e) | None => None end
  | mkEffectU r [] [(a, n)] [] _ _ =>
      if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
      then Some (MmOk (bv_unsigned r)) else None
  | _ => None
  end else None.

Definition dec_mmap_none (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ => match errno_of r with Some e => Some (MmErr e) | None => None end
  | mkEffectU r [] [] [(a, n)] _ _ =>
      if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
      then Some (MmOk (bv_unsigned r)) else None
  | _ => None
  end else None.

Lemma avoids_In : forall a n avoid lo hi, avoids a n avoid = true -> In (lo, hi) avoid -> (a + n <= lo \/ hi <= a)%Z.
Proof.
  intros a n avoid lo hi H Hin. unfold avoids in H. rewrite forallb_forall in H.
  specialize (H _ Hin). cbn in H. apply orb_prop in H as [H|H]; [left|right]; apply Z.leb_le; exact H.
Qed.

Lemma mmap_addr_ok_true : forall len avoid a, mmap_addr_ok len avoid a = true ->
  (a mod page_size = 0 /\ 0 < a /\ a + mmap_len len <= hceil)%Z /\ avoids a (mmap_len len) avoid = true.
Proof.
  intros len avoid a H. unfold mmap_addr_ok in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma dec_mmap_Some : forall len avoid rsp x, dec_mmap len avoid rsp = Some x ->
  match x with
  | MmErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | MmOk a => rsp = mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] /\ mmap_addr_ok len avoid a = true
  end.
Proof.
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst.
    apply errno_of_Some in E as [-> He]. auto.
  - destruct us; [|discriminate].
    destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

Lemma dec_mmap_none_Some : forall len avoid rsp x, dec_mmap_none len avoid rsp = Some x ->
  match x with
  | MmErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | MmOk a => rsp = mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] /\ mmap_addr_ok len avoid a = true
  end.
Proof.
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap_none in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst. apply errno_of_Some in E as [-> He]. auto.
  - destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.
End HC.

(* [comment removed for export] *)
Inductive range_ans : Type := RgErr (e : Z) | RgDone (changed : bool).

Definition dec_munmap (addr len : Z) (rsp : resp) : option range_ans :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ =>
      match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | mkEffectU r [] [] [(a, n)] _ _ =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end else None.

Definition dec_mprotect (addr len : Z) (rsp : resp) : option range_ans :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ =>
      match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | mkEffectU r [] [(a, n)] [] _ _ =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end else None.

Lemma dec_munmap_Some : forall addr len rsp x, dec_munmap addr len rsp = Some x ->
  match x with
  | RgErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | RgDone false => rsp = eff0 (Z_to_bv 64 0)
  | RgDone true => rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] []
  end.
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_munmap in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

Lemma dec_mprotect_Some : forall addr len rsp x, dec_mprotect addr len rsp = Some x ->
  match x with
  | RgErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | RgDone false => rsp = eff0 (Z_to_bv 64 0)
  | RgDone true => rsp = mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))]
  end.
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_mprotect in H. dec_cc cs ci H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate].
    destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct us; [|discriminate]. destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
