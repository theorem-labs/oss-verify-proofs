(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem ITree Nodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
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
Definition dec_plain (ok : Z -> bool) (rsp : resp) : option sret :=
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      match errno_of r with
      | Some e => Some (SErr e)
      | None => if ok (bv_unsigned r) then Some (SVal (bv_unsigned r)) else None
      end
  | _ => None
  end.

Lemma dec_plain_Some : forall ok rsp a, dec_plain ok rsp = Some a ->
  match a with
  | SErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | SVal v => rsp = eff0 (Z_to_bv 64 v) /\ ok v = true /\ (0 <= v <= 2^64 - 4096)%Z
  end.
Proof.
  intros ok [r ws zs us cs ci] a H. unfold dec_plain in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct cs; [|discriminate]. destruct ci; [|discriminate].
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
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      match errno_of r with
      | Some e => Some (RdErr e)
      | None => if (bv_unsigned r =? 0)%Z then Some (RdData []) else None
      end
  | mkEffectU r [(a, bs)] [] [] [] [] =>
      if bv_eqb a (Z_to_bv 64 buf) && (1 <=? Z.of_nat (length bs))%Z
         && (Z.of_nat (length bs) <=? count)%Z && (bv_unsigned r =? Z.of_nat (length bs))%Z
      then Some (RdData bs) else None
  | _ => None
  end.

Lemma dec_read_Some : forall buf count rsp a, (0 <= count)%Z -> dec_read buf count rsp = Some a ->
  match a with
  | RdErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | RdData bs => rsp = mkEffect (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) []
                 /\ (Z.of_nat (length bs) <= count)%Z
  end.
Proof.
  intros buf count [r ws zs us cs ci] a Hc H. unfold dec_read in H.
  destruct ws as [|[a0 bs] [|? ?]]; try discriminate.
  - destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_of r) as [e|] eqn:E.
    + inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
    + destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst. cbn.
      split; [|lia]. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
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
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      if ((count =? 0)%Z && (bv_unsigned r =? 0)%Z) || ((1 <=? bv_unsigned r)%Z && (bv_unsigned r <=? count)%Z)
      then Some (bv_unsigned r) else None
  | _ => None
  end.
Definition dec_write := dec_count.
Definition dec_writev := dec_count.

Lemma dec_count_Some : forall count rsp a, dec_count count rsp = Some a ->
  rsp = eff0 (Z_to_bv 64 a) /\ (0 <= a <= Z.max count 0)%Z /\ (0 < count -> 1 <= a)%Z /\ (a < 2^64)%Z.
Proof.
  intros count [r ws zs us cs ci] a H. unfold dec_count in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct cs; [|discriminate]. destruct ci; [|discriminate].
  pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  destruct (((count =? 0)%Z && (bv_unsigned r =? 0)%Z) || ((1 <=? bv_unsigned r)%Z && (bv_unsigned r <=? count)%Z)) eqn:E; [|discriminate].
  inversion H; subst. unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|].
  apply orb_prop in E as [E|E]; apply andb_prop in E as [E1 E2].
  - apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. lia.
  - apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

Lemma dec_count_full : forall count, (0 <= count < 2^64)%Z -> dec_count count (eff0 (Z_to_bv 64 count)) = Some count.
Proof.
  intros count Hc. unfold dec_count, eff0. rewrite unsigned_lit by lia.
  destruct (Z.eq_dec count 0) as [->|Hne]; [reflexivity|].
  replace (1 <=? count)%Z with true by (symmetry; apply Z.leb_le; lia). rewrite Z.leb_refl, orb_true_r. reflexivity.
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
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      if (0 <? bv_unsigned r)%Z && (bv_unsigned r <? PID_MAX_ENVELOPE)%Z then Some (bv_unsigned r) else None
  | _ => None
  end.
(* [comment removed for export] *)
Definition dec_exit (rsp : resp) : option Empty_set := None.

Lemma dec_set_tid_Some : forall rsp t, dec_set_tid rsp = Some t ->
  rsp = eff0 (Z_to_bv 64 t) /\ (0 < t < PID_MAX_ENVELOPE)%Z.
Proof.
  intros [r ws zs us cs ci] t H. unfold dec_set_tid in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (Z.ltb_spec0 0 (bv_unsigned r)); [|discriminate].
  destruct (Z.ltb_spec0 (bv_unsigned r) PID_MAX_ENVELOPE); [|discriminate]. inversion H; subst.
  unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

(* [comment removed for export] *)
Definition dec_brk0 (rsp : resp) : option Z :=
  match rsp with mkEffectU r [] [] [] [] [] => Some (bv_unsigned r) | _ => None end.

Lemma dec_brk0_Some : forall rsp b, dec_brk0 rsp = Some b -> rsp = eff0 (Z_to_bv 64 b) /\ (0 <= b < 2^64)%Z.
Proof.
  intros [r ws zs us cs ci] b H. unfold dec_brk0 in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct cs; [|discriminate]. destruct ci; [|discriminate]. inversion H; subst.
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
  match rsp with
  | mkEffectU r [] zs [] [] [] =>
      if (bv_unsigned r =? cur)%Z && match zs with [] => true | _ => false end then Some BrkSame
      else if (bv_unsigned r =? req)%Z && listNN_eqb zs (zeros_of (brk_new_pages cur req)) then Some BrkGrown
      else None
  | _ => None
  end.

Lemma dec_brk_Some : forall cur req rsp a, dec_brk cur req rsp = Some a ->
  match a with
  | BrkSame => rsp = eff0 (Z_to_bv 64 cur)
  | BrkGrown => rsp = mkEffect (Z_to_bv 64 req) [] (zeros_of (brk_new_pages cur req))
  end.
Proof.
  intros cur req [r ws zs us cs ci] a H. unfold dec_brk in H.
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
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
Inductive mmap_ans : Type := MmErr (e : Z) | MmOk (a : Z).

Definition avoids (a n : Z) (avoid : list (Z * Z)) : bool :=
  forallb (fun iv => (a + n <=? fst iv)%Z || (snd iv <=? a)%Z) avoid.

Definition mmap_len (len : Z) : Z := page_round_up_Z len.

Definition mmap_addr_ok (len : Z) (avoid : list (Z * Z)) (a : Z) : bool :=
  (a mod page_size =? 0)%Z && (0 <? a)%Z && (a + mmap_len len <=? alloc_ceiling)%Z && avoids a (mmap_len len) avoid.

Definition dec_mmap (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] [] => match errno_of r with Some e => Some (MmErr e) | None => None end
  | mkEffectU r [] [(a, n)] [] [] [] =>
      if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
      then Some (MmOk (bv_unsigned r)) else None
  | _ => None
  end.

Definition dec_mmap_none (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] [] => match errno_of r with Some e => Some (MmErr e) | None => None end
  | mkEffectU r [] [] [(a, n)] [] [] =>
      if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
      then Some (MmOk (bv_unsigned r)) else None
  | _ => None
  end.

Lemma avoids_In : forall a n avoid lo hi, avoids a n avoid = true -> In (lo, hi) avoid -> (a + n <= lo \/ hi <= a)%Z.
Proof.
  intros a n avoid lo hi H Hin. unfold avoids in H. rewrite forallb_forall in H.
  specialize (H _ Hin). cbn in H. apply orb_prop in H as [H|H]; [left|right]; apply Z.leb_le; exact H.
Qed.

Lemma mmap_addr_ok_true : forall len avoid a, mmap_addr_ok len avoid a = true ->
  (a mod page_size = 0 /\ 0 < a /\ a + mmap_len len <= alloc_ceiling)%Z /\ avoids a (mmap_len len) avoid = true.
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
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap in H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst.
    apply errno_of_Some in E as [-> He]. auto.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
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
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap_none in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst. apply errno_of_Some in E as [-> He]. auto.
  - destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

(* [comment removed for export] *)
Inductive range_ans : Type := RgErr (e : Z) | RgDone (changed : bool).

Definition dec_munmap (addr len : Z) (rsp : resp) : option range_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | mkEffectU r [] [] [(a, n)] [] [] =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end.

Definition dec_mprotect (addr len : Z) (rsp : resp) : option range_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | mkEffectU r [] [(a, n)] [] [] [] =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end.

Lemma dec_munmap_Some : forall addr len rsp x, dec_munmap addr len rsp = Some x ->
  match x with
  | RgErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | RgDone false => rsp = eff0 (Z_to_bv 64 0)
  | RgDone true => rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] []
  end.
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_munmap in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate;
    (destruct cs; [|discriminate]); (destruct ci; [|discriminate]).
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
  intros addr len [r ws zs us cs ci] x H. unfold dec_mprotect in H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma length_file_read_le_count : forall data off count,
  (0 <= count < 2^64)%Z -> (Z.of_nat (length (file_read data off (Z_to_bv 64 count))) <= count)%Z.
Proof.
  intros data off count Hc. rewrite file_read_unguarded. rewrite firstn_length.
  unfold word_to_nat. rewrite unsigned_lit by lia. lia.
Qed.

Lemma nstep_dec_read : forall fd buf count mo rsp mo' evs,
  (0 <= count < 2^64)%Z ->
  nstep (NRead fd buf count) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_read buf count rsp = Some a /\
  match a with
  | RdErr e => mo' = mo /\
      ((e = EBADF /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None)
       \/ (e = EISDIR /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir))
  | RdData bs => exists p off data,
      fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) /\
      fs_lookup (m_fs mo) p = Some data /\
      bs = file_read data off (Z_to_bv 64 count) /\
      mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
  end.
Proof.
  intros fd buf count mo rsp mo' evs Hc [-> H]. split; [reflexivity|].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|id w|drd dwr| ]|] eqn:Hlk; try contradiction.  (* [comment removed for export] *)
  - destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|contradiction]. destruct H as [-> ->].
    set (bs := file_read data off (Z_to_bv 64 count)).
    pose proof (length_file_read_le_count data off count Hc) as Hl. fold bs in Hl.
    exists (RdData bs). split.
    + unfold dec_read. destruct bs as [|b bs'] eqn:Ebs; cbn [delivered_writes].
      * unfold len_word. cbn [length Z.of_nat]. rewrite errno_of_lit by lia. reflexivity.
      * rewrite bv_eqb_refl. unfold len_word. rewrite unsigned_lit by (cbn [length] in *; lia).
        rewrite Z.eqb_refl.
        replace (1 <=? Z.of_nat (length (b :: bs')))%Z with true by (symmetry; apply Z.leb_le; cbn; lia).
        replace (Z.of_nat (length (b :: bs')) <=? count)%Z with true by (symmetry; apply Z.leb_le; lia).
        reflexivity.
    + exists p, off, data. auto.
  - destruct H as [-> ->]. exists (RdErr EISDIR). split; [reflexivity| auto].
  - destruct H as [-> ->]. exists (RdErr EBADF). split; [reflexivity| auto].
Qed.

Lemma nstep_dec_write : forall fd bs mo rsp mo' evs,
  (0 < Z.of_nat (length bs) < 2^64)%Z ->
  nstep (NWrite fd bs) mo rsp mo' evs ->
  exists k, dec_write (Z.of_nat (length bs)) rsp = Some k /\ (1 <= k <= Z.of_nat (length bs))%Z
            /\ mo' = mo /\ evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) bs).
Proof.
  intros fd bs mo rsp mo' evs Hl [-> [(Hbs & -> & ->) | (k & Hk & -> & ->)]].
  { exfalso. subst bs. cbn in Hl. lia. }
  exists k. split; [|auto]. unfold dec_write, dec_count, eff0. rewrite unsigned_lit by lia.
  replace (1 <=? k)%Z with true by (symmetry; apply Z.leb_le; lia).
  replace (k <=? Z.of_nat (length bs))%Z with true by (symmetry; apply Z.leb_le; lia).
  rewrite orb_true_r. reflexivity.
Qed.

Lemma nstep_dec_writev : forall fd bufs mo rsp mo' evs,
  (Z.of_nat (length (concat bufs)) < 2^64)%Z ->
  nstep (NWritev fd bufs) mo rsp mo' evs ->
  exists k, dec_writev (Z.of_nat (length (concat bufs))) rsp = Some k
            /\ (0 <= k <= Z.of_nat (length (concat bufs)))%Z
            /\ (concat bufs <> [] -> 1 <= k)%Z
            /\ mo' = mo /\ evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) (concat bufs)).
Proof.
  intros fd bufs mo rsp mo' evs Hl [-> [(Hbs & -> & ->) | (k & Hk & -> & ->)]].
  - exists 0%Z. rewrite Hbs. cbn. repeat split; auto; try lia. congruence.
  - exists k. split; [|repeat split; auto; lia]. unfold dec_writev, dec_count, eff0. rewrite unsigned_lit by lia.
    replace (1 <=? k)%Z with true by (symmetry; apply Z.leb_le; lia).
    replace (k <=? Z.of_nat (length (concat bufs)))%Z with true by (symmetry; apply Z.leb_le; lia).
    rewrite orb_true_r. reflexivity.
Qed.

Lemma openat_errnos_range : forall e, In e openat_errnos -> (1 <= e <= 4095)%Z.
Proof. intros e H. cbn in H. unfold ENOMEM, EACCES, EMFILE, ENFILE in H. lia. Qed.

Lemma nstep_dec_open : forall path mo rsp mo' evs,
  minv mo ->
  nstep (NOpen path) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_open rsp = Some a /\
  match a with
  | SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
  | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z
      /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
      /\ exists ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0))
         /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) ent) mo
  end.
Proof.
  intros path mo rsp mo' evs Hminv [-> H]. split; [reflexivity|].
  assert (Herr : forall e, (1 <= e <= 4095)%Z -> rsp = efferr e -> mo' = mo ->
            exists a, dec_open rsp = Some a /\
            match a with SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
            | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
                /\ exists ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0)) /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) ent) mo end).
  { intros e He -> ->. exists (SErr e). split; [apply dec_plain_err; exact He| auto]. }
  assert (Hres : forall ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0)) -> open_result mo ent rsp mo' ->
            exists a, dec_open rsp = Some a /\
            match a with SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
            | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
                /\ exists ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0)) /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) ent) mo end).
  { intros ent Hent [(e & HIn & -> & ->) | (Hlk & -> & ->)].
    - apply (Herr e); [apply openat_errnos_range; exact HIn | reflexivity | reflexivity].
    - pose proof (alloc_fd_range mo Hminv Hlk) as Hr.
      exists (SVal (bv_unsigned (alloc_fd (m_fds mo)))). split.
      + unfold dec_open. rewrite <- (Z_to_bv_bv_unsigned (alloc_fd (m_fds mo))) at 1.
        apply dec_plain_val; [lia|]. apply andb_true_intro; split; apply Z.leb_le; lia.
      + rewrite Z_to_bv_bv_unsigned. split; [reflexivity|]. split; [lia|]. split; [exact Hlk|]. exists ent. auto. }
  destruct (path_max <=? length path)%nat. { destruct H as [-> ->]. apply (Herr ENAMETOOLONG); try reflexivity. unfold ENAMETOOLONG; lia. }
  destruct path as [|c path']. { destruct H as [-> ->]. apply (Herr ENOENT); try reflexivity. unfold ENOENT; lia. }
  destruct (path_is_dirref (c :: path')). { apply (Hres FdDir); [left; reflexivity| exact H]. }  (* [comment removed for export] *)
  destruct (fs_lookup (m_fs mo) (c :: path')).
  - apply (Hres (FdFile (c :: path') (Z_to_bv 64 0))); [right; reflexivity| exact H].
  - destruct H as [-> ->]. apply (Herr ENOENT); try reflexivity. unfold ENOENT; lia.
Qed.

Lemma nstep_dec_close : forall fd mo rsp mo' evs,
  nstep (NClose fd) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_close rsp = Some a /\
  match a with
  | SErr e => e = EBADF /\ mo' = mo /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
  | SVal v => v = 0%Z /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) <> None
      /\ mo' = with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo
  end.
Proof.
  intros fd mo rsp mo' evs (-> & _ & H). split; [reflexivity|].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) eqn:Hlk; destruct H as [-> ->].
  - exists (SVal 0). split; [apply dec_plain_val; [lia|reflexivity]|]. repeat split; congruence.
  - exists (SErr EBADF). split; [apply dec_plain_err; unfold EBADF; lia|]. auto.
Qed.

Lemma nstep_dec_ioctl : forall fd req mo rsp mo' evs,
  nstep (NIoctl fd req) mo rsp mo' evs ->
  dec_ioctl rsp = Some (SErr ENOTTY) /\ mo' = mo /\ evs = [].
Proof.
  intros fd req mo rsp mo' evs (-> & -> & ->). split; [|auto]. apply dec_plain_err. unfold ENOTTY; lia.
Qed.

Lemma nstep_dec_set_tid : forall mo rsp mo' evs,
  minv mo ->
  nstep NSetTid mo rsp mo' evs ->
  evs = [] /\
  exists t, dec_set_tid rsp = Some t /\ (0 < t < PID_MAX_ENVELOPE)%Z /\
  ((m_tid mo = Some (Z_to_bv 64 t) /\ mo' = mo) \/ (m_tid mo = None /\ mo' = with_tid (Z_to_bv 64 t) mo)).
Proof.
  intros mo rsp mo' evs Hminv (-> & tw & -> & H). split; [reflexivity|].
  exists (bv_unsigned tw). rewrite Z_to_bv_bv_unsigned.
  assert (Hr : (0 < bv_unsigned tw < PID_MAX_ENVELOPE)%Z).
  { destruct (m_tid mo) as [t0|] eqn:E.
    - destruct H as [-> _]. destruct Hminv as (_ & _ & _ & _ & _ & _ & MT & _). exact (MT _ E).
    - exact (proj1 H). }
  split.
  - unfold dec_set_tid, eff0. destruct Hr as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. rewrite H1, H2. reflexivity.
  - split; [exact Hr|]. destruct (m_tid mo) as [t0|]; destruct H as [H0 ->]; [left; subst; auto| right; auto].
Qed.

Lemma nstep_exit_none : forall c mo rsp mo' evs, nstep (NExit c) mo rsp mo' evs -> False.
Proof. intros c mo rsp mo' evs H. exact H. Qed.

(* [comment removed for export] *)
Lemma m_vmmaps_with_vm_backing : forall l p m, m_vmmaps (with_vm_backing l p m) = m_vmmaps m.
Proof. intros l p m; destruct m; reflexivity. Qed.

Lemma m_vmmaps_forget_vm_ranges : forall ranges m, m_vmmaps (forget_vm_ranges ranges m) = m_vmmaps m.
Proof.
  induction ranges as [|[a n] ranges IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|].
  rewrite IH. unfold vm_forget_range. apply m_vmmaps_with_vm_backing.
Qed.

Lemma m_vmmaps_with_brk_next : forall m req r,
  m_vmmaps (with_brk_next m req r) = brk_model_next (m_vmmaps m) req r.
Proof.
  intros. unfold with_brk_next. cbv zeta. rewrite m_vmmaps_forget_vm_ranges, m_vmmaps_with_vmmaps. reflexivity.
Qed.

Lemma nstep_dec_brk0 : forall mo rsp mo' evs,
  nstep (NBrk 0) mo rsp mo' evs ->
  evs = [] /\ dec_brk0 rsp = Some (bv_unsigned (vm_brk (m_vmmaps mo))) /\ vm_only mo mo'
  /\ vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo).
Proof.
  intros mo rsp mo' evs H.
  pose proof (nstep_mm_vm_only (NBrk 0) mo rsp mo' evs I H) as [[Hv _] ->]. split; [reflexivity|].
  apply nstep_brk_iff in H. destruct rsp as [r ws zs us cs ci]. unfold check_brk in H.
  destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (brk_r_ok mo (Z_to_bv 64 0) r && listNN_eqb zs _ && listNN_eqb us _) eqn:E; [|discriminate].
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  unfold brk_r_ok in E1. change (w_is0 (Z_to_bv 64 0)) with true in E1. cbn [orb] in E1. apply bv_eqb_eq in E1. subst r.
  apply listNN_eqb_eq in E2. apply listNN_eqb_eq in E3.
  unfold brk_zeros, brk_is_grow in E2. change (w_is0 (Z_to_bv 64 0)) with true in E2. cbn [negb andb] in E2. subst zs.
  unfold brk_unmaps, brk_page_range in E3. rewrite Z.ltb_irrefl in E3. destruct (0 <? _)%Z; subst us.
  all: inversion H; subst; split; [reflexivity|]; split; [exact Hv|];
       rewrite m_vmmaps_with_brk_next; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_brk : forall req mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_brk h) <= req < 2^64)%Z ->
  nstep (NBrk req) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists a, dec_brk (bv_unsigned (vm_brk h)) req rsp = Some a /\
  match a with
  | BrkSame => vm_brk (m_vmmaps mo') = vm_brk h
  | BrkGrown => vm_brk (m_vmmaps mo') = Z_to_bv 64 req
  end.
Proof.
  intros req mo rsp mo' evs h Hb Hsb Hreq H.
  pose proof (nstep_mm_vm_only (NBrk req) mo rsp mo' evs I H) as [[Hv _] ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_brk_iff in H. destruct rsp as [r ws zs us cs ci]. unfold check_brk in H.
  destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (brk_r_ok mo (Z_to_bv 64 req) r && listNN_eqb zs _ && listNN_eqb us _) eqn:E; [|discriminate].
  inversion H; subst; clear H. rewrite m_vmmaps_with_brk_next. cbn [brk_model_next vm_brk].
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply listNN_eqb_eq in E2. apply listNN_eqb_eq in E3. subst zs us.
  fold h in E1 |- *.
  unfold brk_r_ok in E1. rewrite w_is0_lit in E1 by lia.
  replace (req =? 0)%Z with false in E1 by (symmetry; apply Z.eqb_neq; lia).
  unfold min_brk in E1. rewrite unsigned_lit in E1 by lia. fold h in E1.
  replace (req <? bv_unsigned (vm_start_brk h))%Z with false in E1 by (symmetry; apply Z.ltb_ge; lia).
  replace (req <? bv_unsigned (vm_brk h))%Z with false in E1 by (symmetry; apply Z.ltb_ge; lia).
  cbn [orb] in E1. apply andb_prop in E1 as [E1 _].
  assert (Hr : r = Z_to_bv 64 req \/ r = vm_brk h).
  { apply orb_prop in E1 as [E1|E1]; apply bv_eqb_eq in E1; auto. }
  assert (Hus : brk_unmaps r (vm_brk h) = []).
  { unfold brk_unmaps, brk_page_range.
    assert (Hle : (page_round_up_Z (bv_unsigned (vm_brk h)) <= page_round_up_Z (bv_unsigned r))%Z).
    { apply page_round_up_Z_mono. destruct Hr as [-> | ->]; [rewrite unsigned_lit by lia|]; lia. }
    replace (page_round_up_Z (bv_unsigned r) <? page_round_up_Z (bv_unsigned (vm_brk h)))%Z with false
      by (symmetry; apply Z.ltb_ge; lia).
    destruct (0 <? _)%Z; reflexivity. }
  rewrite Hus.
  destruct (Z.eq_dec req (bv_unsigned (vm_brk h))) as [Ereq | Hne].
  - (* [comment removed for export] *)
    assert (Hr' : r = vm_brk h). { destruct Hr as [-> | ->]; [subst req; apply Z_to_bv_bv_unsigned| reflexivity]. }
    subst r. exists BrkSame. split; [|reflexivity].
    unfold dec_brk. rewrite Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
  - destruct Hr as [-> | ->].
    + exists BrkGrown. split; [|reflexivity].
      unfold dec_brk. rewrite unsigned_lit by lia.
      replace (req =? bv_unsigned (vm_brk h))%Z with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [andb]. rewrite Z.eqb_refl.
      unfold brk_zeros, brk_is_grow. rewrite w_is0_lit by lia.
      replace (req =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (0 <? bv_unsigned (vm_brk h))%Z with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite unsigned_lit by lia.
      replace (bv_unsigned (vm_brk h) <? req)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [negb andb]. unfold brk_page_range, brk_new_pages, zeros_of, wa.
      destruct (_ <? _)%Z; rewrite (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
    + exists BrkSame. split; [|reflexivity].
      unfold dec_brk. rewrite Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition covered (maps : list (word * word)) (iv : Z * Z) : Prop :=
  exists e sz, In (e, sz) maps /\ (bv_unsigned e <= fst iv)%Z /\ (snd iv <= bv_unsigned e + bv_unsigned sz)%Z.

Lemma region_free_In : forall maps a n e sz,
  region_free maps a n = true -> In (e, sz) maps ->
  (bv_unsigned a + bv_unsigned n <= bv_unsigned e \/ bv_unsigned e + bv_unsigned sz <= bv_unsigned a)%Z.
Proof.
  induction maps as [|[e0 sz0] maps IH]; intros a n e sz H Hin; [destruct Hin|].
  cbn [region_free] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [E|Hin]; [|exact (IH _ _ _ _ H2 Hin)].
  inversion E; subst. unfold iv_overlap in H1.
  destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned e + bv_unsigned sz));
  destruct (Z.ltb_spec0 (bv_unsigned e) (bv_unsigned a + bv_unsigned n)); cbn in H1; try discriminate; lia.
Qed.

Lemma avoids_of_region_free : forall maps a n avoid,
  region_free maps a n = true ->
  Forall (covered maps) avoid ->
  avoids (bv_unsigned a) (bv_unsigned n) avoid = true.
Proof.
  intros maps a n avoid Hrf Hc. unfold avoids. apply forallb_forall. intros [lo hi] Hin.
  pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as (e & sz & He & H1 & H2). cbn in H1, H2. cbn [fst snd].
  pose proof (region_free_In _ _ _ _ _ Hrf He) as [H|H].
  - apply orb_true_intro. left. apply Z.leb_le. lia.
  - apply orb_true_intro. right. apply Z.leb_le. lia.
Qed.

Lemma mmap_len_bound : forall len, (0 < len)%Z -> (len <= mmap_len len < len + 4096)%Z.
Proof. intros len H. unfold mmap_len, page_round_up_Z, page_size. split; [|]; nia || lia. Qed.

(* [comment removed for export] *)
Lemma nstep_dec_mmap : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  minv mo ->   (* [comment removed for export] *)
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros len avoid mo rsp mo' evs h Hminv Hlen Hlen2 Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb. pose proof (minv_alloc_top mo Hminv) as Htop.
  pose proof (nstep_mm_vm_only (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ltac:(reflexivity) H) as [[Hv _] ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mmap_iff in H. destruct rsp as [r ws zs us cs ci]. unfold check_mmap in H.
  change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false in H.
  change (negb (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)))) with false in H. cbv iota in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with true in H.
  cbv iota beta in H. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  fold h in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  destruct (errno_ret_in mmap_errnos r) eqn:Herr.
  - destruct zs; [|discriminate]. inversion H; subst.
    apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    change (mmap_noreserve_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with false in H.
    unfold with_mmap_backing in H. change (mmap_noreserve_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with false in H. cbv iota in H.
    inversion H; subst; clear H.
    apply andb_prop in E as [E E6]. apply andb_prop in E as [E E5]. apply andb_prop in E as [E E4].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply listNN_eqb_eq in E6. subst zs. fold h in Htop. rewrite Htop in E3.
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned r) = true).
    { unfold mmap_addr_ok. rewrite E1, E2, E3. cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
    exists (MmOk (bv_unsigned r)). split.
    + unfold dec_mmap. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E4|]. rewrite m_vmmaps_with_vmmaps. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_mmap_none : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  minv mo ->   (* [comment removed for export] *)
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap_none len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess h)
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros len avoid mo rsp mo' evs h Hminv Hlen Hlen2 Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb. pose proof (minv_alloc_top mo Hminv) as Htop.
  pose proof (nstep_mm_vm_only (NMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ltac:(reflexivity) H) as [[Hv _] ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mmap_iff in H. destruct rsp as [r ws zs us cs ci]. unfold check_mmap in H.
  change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false in H.
  change (negb (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)))) with false in H. cbv iota in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with false in H.
  change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with true in H.
  cbv iota beta in H. destruct ws; [|discriminate]. destruct zs; [|destruct us; discriminate].
  destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
  fold h in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  destruct (errno_ret_in mmap_errnos r) eqn:Herr.
  - destruct us; [|discriminate]. inversion H; subst.
    apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap_none. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    unfold with_mmap_backing in H. change (mmap_noreserve_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with false in H. cbv iota in H.
    inversion H; subst; clear H.
    apply andb_prop in E as [E E5]. apply andb_prop in E as [E E4].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply listNN_eqb_eq in E5. subst us. fold h in Htop. rewrite Htop in E3.
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned r) = true).
    { unfold mmap_addr_ok. rewrite E1, E2, E3. cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
    exists (MmOk (bv_unsigned r)). split.
    + unfold dec_mmap_none. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E4|]. rewrite m_vmmaps_with_vmmaps. reflexivity.
Qed.

Lemma nstep_dec_munmap : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  nstep (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_munmap addr len rsp = Some x /\
  match x with
  | RgErr e => e = EINVAL /\ mo' = mo
  | RgDone false => mo' = mo /\ region_free (vm_reserved h ++ vm_maps h) a n = true
  | RgDone true => map_has (vm_maps h) a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMunmap addr len) mo rsp mo' evs I H) as [[Hv _] ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_munmap_iff in H. destruct rsp as [r ws zs us cs ci]. unfold check_munmap in H.
  fold a in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H.
  destruct (negb (bv_unsigned a mod page_size =? 0)%Z || w_is0 (Z_to_bv 64 len)).
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_munmap. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  cbv zeta in H. destruct (TASK_SIZE <? _)%Z.   (* [comment removed for export] *)
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_munmap. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  fold h in H.
  destruct (map_has (vm_maps h) a n) eqn:Hhas.
  - destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    destruct (w_is0 r && listNN_eqb us [(a, n)]) eqn:E; [|discriminate]. inversion H; subst; clear H.
    apply andb_prop in E as [E1 E2]. apply listNN_eqb_eq in E2. subst us. unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
    exists (RgDone true). split; [|split; [reflexivity|]].
    + unfold dec_munmap. subst a n. rewrite !bv_eqb_refl. reflexivity.
    + unfold with_mmap_destroyed, vm_forget_range. rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps. reflexivity.
  - unfold munmap_free_ok in H. fold n in H. destruct (region_free _ a n) eqn:Hrf; [|discriminate]. cbn [andb] in H.
    destruct (_ <=? _)%Z; [|discriminate].
    apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgDone false). split; [reflexivity| auto].
Qed.

Lemma nstep_dec_mprotect : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  nstep (NMprotect addr len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mprotect addr len rsp = Some x /\
  match x with
  | RgErr e => (e = EINVAL \/ e = ENOMEM) /\ mo' = mo
  | RgDone false => mo' = mo
  | RgDone true => map_contains (vm_noaccess h) a n = true /\ map_contains (vm_maps h) a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMprotect addr len _) mo rsp mo' evs I H) as [[Hv _] ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mprotect_iff in H. destruct rsp as [r ws zs us cs ci]. unfold check_mprotect in H.
  fold a in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H.
  change (mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with false in H.
  change (mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with true in H. cbn [negb] in H. cbv iota in H.
  destruct (negb (bv_unsigned a mod page_size =? 0)%Z).
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  destruct (two_pow_64 <=? _)%Z.
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr ENOMEM). split; [|auto].
    unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity. }
  cbv zeta in H. fold h in H.
  destruct (map_contains (vm_noaccess h) a n && map_contains (vm_maps h) a n) eqn:Hc.
  - destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
    destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    destruct (errno_ret_in mprotect_errnos r) eqn:Herr.
    + destruct zs; [|discriminate]. inversion H; subst.
      apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
      exists (RgErr ENOMEM). split; [|auto]. unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
    + destruct (mprotect_budget_ok mo a n && w_is0 r && listNN_eqb zs [(a, n)]) eqn:E; [|discriminate]. inversion H; subst; clear H.
      apply andb_prop in E as [E E2]. apply andb_prop in E as [_ E1]. apply listNN_eqb_eq in E2. subst zs.
      unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
      apply andb_prop in Hc as [Hc1 Hc2].
      exists (RgDone true). split; [| split; [exact Hc1| split; [exact Hc2|]]].
      * unfold dec_mprotect. subst a n. rewrite !bv_eqb_refl. reflexivity.
      * unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps. reflexivity.
  - destruct (map_contains (vm_maps h) a n && region_free (vm_noaccess h) a n); [|discriminate].
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r) eqn:E; [|discriminate]. inversion H; subst. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
    exists (RgDone false). split; [reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive mremap_ans : Type := MrErr (e : Z) | MrSame | MrMoved (d : Z).

Definition mremap_dst_ok (nsz : Z) (avoid : list (Z * Z)) (old d : Z) : bool :=
  (d mod page_size =? 0)%Z && (0 <? d)%Z && (d + nsz <=? alloc_ceiling)%Z && negb (d =? old)%Z && avoids d nsz avoid.

Definition dec_mremap (old osz nsz : Z) (avoid : list (Z * Z)) (rsp : resp) : option mremap_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      match errno_of r with
      | Some e => Some (MrErr e)
      | None => if bv_eqb r (Z_to_bv 64 old) && (osz =? nsz)%Z then Some MrSame else None
      end
  | mkEffectU r [] [] [(ua, un)] [] [] =>
      if bv_eqb r (Z_to_bv 64 old) && (nsz <? osz)%Z
         && bv_eqb ua (Z_to_bv 64 (old + nsz)) && bv_eqb un (Z_to_bv 64 (osz - nsz))
      then Some MrSame else None
  | mkEffectU r [] [(za, zn)] [] [] [] =>
      if bv_eqb r (Z_to_bv 64 old) && (osz <? nsz)%Z
         && bv_eqb za (Z_to_bv 64 (old + osz)) && bv_eqb zn (Z_to_bv 64 (nsz - osz))
      then Some MrSame else None
  | mkEffectU r [] [(za, zn)] [(ua, un)] [mkCopy cs cd cl] [] =>
      if (osz <? nsz)%Z && mremap_dst_ok nsz avoid old (bv_unsigned r)
         && bv_eqb za (Z_to_bv 64 (bv_unsigned r + osz)) && bv_eqb zn (Z_to_bv 64 (nsz - osz))
         && bv_eqb ua (Z_to_bv 64 old) && bv_eqb un (Z_to_bv 64 osz)
         && bv_eqb cs (Z_to_bv 64 old) && bv_eqb cd r && bv_eqb cl (Z_to_bv 64 osz)
      then Some (MrMoved (bv_unsigned r)) else None
  | _ => None
  end.

Lemma mremap_dst_ok_true : forall nsz avoid old d, mremap_dst_ok nsz avoid old d = true ->
  (d mod page_size = 0 /\ 0 < d /\ d + nsz <= alloc_ceiling /\ d <> old)%Z /\ avoids d nsz avoid = true.
Proof.
  intros nsz avoid old d H. unfold mremap_dst_ok in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply negb_true_iff in H4. apply Z.eqb_neq in H4. auto 6.
Qed.

Lemma dec_mremap_Some : forall old osz nsz avoid rsp x, dec_mremap old osz nsz avoid rsp = Some x ->
  match x with
  | MrErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | MrSame =>
      (osz = nsz /\ rsp = eff0 (Z_to_bv 64 old))
      \/ (nsz < osz /\ rsp = mkEffectU (Z_to_bv 64 old) [] [] [(Z_to_bv 64 (old + nsz), Z_to_bv 64 (osz - nsz))] [] [])%Z
      \/ (osz < nsz /\ rsp = mkEffectU (Z_to_bv 64 old) [] [(Z_to_bv 64 (old + osz), Z_to_bv 64 (nsz - osz))] [] [] [])%Z
  | MrMoved d => (osz < nsz)%Z /\ mremap_dst_ok nsz avoid old d = true /\
      rsp = mkEffectU (Z_to_bv 64 d) [] [(Z_to_bv 64 (d + osz), Z_to_bv 64 (nsz - osz))] [(Z_to_bv 64 old, Z_to_bv 64 osz)]
                      [mkCopy (Z_to_bv 64 old) (Z_to_bv 64 d) (Z_to_bv 64 osz)] []
  end.
Proof.
  intros old osz nsz avoid [r ws zs us cs ci] x H. unfold dec_mremap in H.
  destruct ws; [|discriminate].
  destruct zs as [|[za zn] [|? ?]]; destruct us as [|[ua un] [|? ?]]; destruct cs as [|[c1 c2 c3] [|? ?]]; destruct ci; try discriminate.
  - destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
    destruct (bv_eqb r (Z_to_bv 64 old)) eqn:E1; [|discriminate]. destruct (Z.eqb_spec osz nsz); [|discriminate].
    inversion H; subst. apply bv_eqb_eq in E1. subst r. left. auto.
  - destruct (bv_eqb r (Z_to_bv 64 old)) eqn:E1; [|discriminate]. destruct (Z.ltb_spec0 nsz osz); [|discriminate].
    destruct (bv_eqb ua _) eqn:E2; [|discriminate]. destruct (bv_eqb un _) eqn:E3; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. apply bv_eqb_eq in E3. subst. right; left. auto.
  - destruct (bv_eqb r (Z_to_bv 64 old)) eqn:E1; [|discriminate]. destruct (Z.ltb_spec0 osz nsz); [|discriminate].
    destruct (bv_eqb za _) eqn:E2; [|discriminate]. destruct (bv_eqb zn _) eqn:E3; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. apply bv_eqb_eq in E3. subst. right; right. auto.
  - destruct (Z.ltb_spec0 osz nsz); [|discriminate]. destruct (mremap_dst_ok nsz avoid old (bv_unsigned r)) eqn:E0; [|discriminate].
    destruct (bv_eqb za _) eqn:E2; [|discriminate]. destruct (bv_eqb zn _) eqn:E3; [|discriminate].
    destruct (bv_eqb ua _) eqn:E4; [|discriminate]. destruct (bv_eqb un _) eqn:E5; [|discriminate].
    destruct (bv_eqb c1 _) eqn:E6; [|discriminate]. destruct (bv_eqb c2 _) eqn:E7; [|discriminate]. destruct (bv_eqb c3 _) eqn:E8; [|discriminate].
    cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E2. apply bv_eqb_eq in E3. apply bv_eqb_eq in E4. apply bv_eqb_eq in E5.
    apply bv_eqb_eq in E6. apply bv_eqb_eq in E7. apply bv_eqb_eq in E8. subst.
    rewrite Z_to_bv_bv_unsigned. auto.
Qed.

Lemma page_round_up_Z_id : forall z, (0 <= z)%Z -> (z mod 4096 = 0)%Z -> page_round_up_Z z = z.
Proof. intros z Hz Hm. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.

Lemma m_vmmaps_mremap_model_next : forall m old old_n dst new_n,
  m_vmmaps (mremap_model_next m old old_n dst new_n) = mremap_maps_next (m_vmmaps m) old dst new_n.
Proof.
  intros. unfold mremap_model_next, vm_resize_backing. cbv zeta. rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_mremap : forall old osz nsz avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  let oldw := Z_to_bv 64 old in let on := Z_to_bv 64 osz in let nn := Z_to_bv 64 nsz in
  minv mo ->
  (0 <= old)%Z -> (old mod 4096 = 0)%Z ->
  (0 < osz)%Z -> (osz mod 4096 = 0)%Z -> (0 < nsz)%Z -> (nsz mod 4096 = 0)%Z ->
  (old + Z.max osz nsz < 2^64)%Z ->
  mremap_source_b h oldw on osz = true ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMremap old osz nsz MREMAP_MAYMOVE) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mremap old osz nsz avoid rsp = Some x /\
  match x with
  | MrErr e => e = ENOMEM /\ mo' = mo /\ osz <> nsz
  | MrSame => (osz = nsz /\ mo' = mo)
              \/ (nsz < osz /\ m_vmmaps mo' = mremap_maps_next h oldw oldw nn)%Z
              \/ (osz < nsz /\ mremap_inplace_grow_b mo oldw on nn osz nsz = true
                            /\ m_vmmaps mo' = mremap_maps_next h oldw oldw nn)%Z
  | MrMoved d => (osz < nsz)%Z /\ mremap_dst_ok nsz avoid old d = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 d) nn = true
      /\ m_vmmaps mo' = mremap_maps_next h oldw (Z_to_bv 64 d) nn
  end.
Proof.
  intros old osz nsz avoid mo rsp mo' evs h oldw on nn Hminv Hold Holda Hosz Hosza Hnsz Hnsza Hhi Hsrc Hcov H.
  assert (Htop : alloc_top h = alloc_ceiling) by (subst h; apply minv_alloc_top; exact Hminv).   (* [comment removed for export] *)
  pose proof (nstep_mm_vm_only (NMremap old osz nsz MREMAP_MAYMOVE) mo rsp mo' evs I H) as [[Hv _] ->].
  split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mremap_iff in H. destruct rsp as [r ws zs us cs ci]. unfold check_mremap in H.
  change (bv_unsigned (Z_to_bv 64 MREMAP_MAYMOVE)) with MREMAP_MAYMOVE in H. cbn [Z.eqb Pos.eqb negb MREMAP_MAYMOVE] in H.
  rewrite (unsigned_lit old) in H by lia.
  replace (old mod page_size =? 0)%Z with true in H by (symmetry; apply Z.eqb_eq; exact Holda). cbn [negb] in H.
  assert (Hpa : forall z, (0 < z)%Z -> (z mod 4096 = 0)%Z -> (z < 2^64)%Z -> page_align_is0_b (Z_to_bv 64 z) = false).
  { intros z Hz Hzm Hzh. unfold page_align_is0_b. rewrite w_is0_lit by lia. rewrite unsigned_lit by lia.
    rewrite page_round_up_Z_id by lia. replace (z =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [orb]. apply Z.leb_gt. unfold two_pow_64. lia. }
  rewrite (Hpa nsz) in H by lia. rewrite (Hpa osz) in H by lia. cbv zeta in H.
  rewrite !unsigned_lit in H by lia. rewrite !page_round_up_Z_id in H by lia. fold oldw on nn h in H.
  rewrite Hsrc in H.
  replace (mremap_backing_uniform_b mo oldw on) with true in H.
  2:{ symmetry. unfold mremap_backing_uniform_b. rewrite (minv_lazy _ Hminv). cbn. destruct (region_free [] oldw on) eqn:E; [reflexivity|]. cbn in E. discriminate. }
  cbn [andb negb] in H.
  destruct (Z.eqb_spec osz nsz) as [Heq|Hne].
  { (* [comment removed for export] *)
    apply check_ret_only_ok_iff in H as (-> & -> & _). exists MrSame. split; [|left; auto].
    unfold dec_mremap. subst oldw. rewrite errno_of_lit. 2:{ unfold mremap_source_b in Hsrc.
      apply andb_prop in Hsrc as [Hsrc _]. apply andb_prop in Hsrc as [Hsrc _]. apply andb_prop in Hsrc as [Hsrc _].
      apply Z.leb_le in Hsrc. rewrite unsigned_lit in Hsrc by lia. subst h; rewrite Htop in Hsrc. unfold alloc_ceiling in Hsrc. lia. }
    rewrite bv_eqb_refl. rewrite (proj2 (Z.eqb_eq _ _) Heq). reflexivity. }
  assert (Hsrc' := Hsrc). unfold mremap_source_b in Hsrc'.
  apply andb_prop in Hsrc' as [Hsrc' _]. apply andb_prop in Hsrc' as [Hsrc' _]. apply andb_prop in Hsrc' as [Hceil _].
  apply Z.leb_le in Hceil. subst oldw. rewrite unsigned_lit in Hceil by lia. rewrite Htop in Hceil.
  assert (Hac : (alloc_ceiling < 2^64 - 4096)%Z) by (unfold alloc_ceiling; lia).
  replace (osz =? nsz)%Z with false in H by (symmetry; apply Z.eqb_neq; exact Hne).
  destruct ws; [|discriminate]. destruct ci; [|discriminate].
  destruct (errno_ret_in mremap_errnos r) eqn:Herr.
  - destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. inversion H; subst.
    apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
    exists (MrErr ENOMEM). split; [|auto]. unfold dec_mremap. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - destruct (bv_eqb r (Z_to_bv 64 old)) eqn:Er.
    + apply bv_eqb_eq in Er. subst r.
      destruct (Z.ltb_spec0 nsz osz).
      * (* [comment removed for export] *)
        destruct (listNN_eqb zs [] && listNN_eqb us _ && listCopy_eqb cs []) eqn:E; [|discriminate]. inversion H; subst; clear H.
        apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
        apply listNN_eqb_eq in E1. apply listNN_eqb_eq in E2. apply listCopy_eqb_eq in E3. subst zs us cs.
        exists MrSame. split.
        -- unfold dec_mremap. rewrite bv_eqb_refl. replace (nsz <? osz)%Z with true by (symmetry; apply Z.ltb_lt; lia).
           subst nn on. rewrite lit_add_lit, bv_eqb_refl. cbn [andb].
           match goal with |- (if bv_eqb ?x ?y then _ else _) = _ => replace (bv_eqb x y) with true; [reflexivity|] end.
           symmetry. apply bv_eqb_eq. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
        -- right; left. split; [lia|]. rewrite m_vmmaps_mremap_model_next. reflexivity.
      * (* [comment removed for export] *)
        assert (Hlt : (osz < nsz)%Z) by lia.
        destruct (mremap_inplace_grow_b mo (Z_to_bv 64 old) on nn osz nsz) eqn:Hg; [|discriminate].
        destruct (listNN_eqb zs _ && listNN_eqb us [] && listCopy_eqb cs []) eqn:E; [|discriminate]. inversion H; subst; clear H.
        apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
        apply listNN_eqb_eq in E1. apply listNN_eqb_eq in E2. apply listCopy_eqb_eq in E3. subst zs us cs.
        exists MrSame. split.
        -- unfold dec_mremap, mremap_tail. replace (osz <? nsz)%Z with true by (symmetry; apply Z.ltb_lt; lia).
           subst on nn. rewrite lit_add_lit, !bv_eqb_refl. reflexivity.
        -- right; right. split; [lia|]. split; [first [exact Hg | reflexivity]|]. rewrite m_vmmaps_mremap_model_next. reflexivity.
    + destruct ((osz <? nsz)%Z && mremap_fresh_b mo osz nsz (Z_to_bv 64 old) on r nn && listNN_eqb zs _ && listNN_eqb us _ && listCopy_eqb cs _) eqn:E; [|discriminate].
      inversion H; subst; clear H.
      apply andb_prop in E as [E E5]. apply andb_prop in E as [E E4]. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
      apply Z.ltb_lt in E1. apply listNN_eqb_eq in E3. apply listNN_eqb_eq in E4. apply listCopy_eqb_eq in E5. subst zs us cs.
      pose proof E2 as Hf. unfold mremap_fresh_b in E2. cbv zeta in E2. fold h in E2.
      apply andb_prop in E2 as [E2 F6]. apply andb_prop in E2 as [E2 F5].
      apply andb_prop in E2 as [E2 F4]. apply andb_prop in E2 as [E2 F3]. apply andb_prop in E2 as [F1 F2].
      apply negb_true_iff in F1. apply Z.eqb_eq in F2. apply Z.ltb_lt in F3. apply Z.leb_le in F4. rewrite Htop in F4.
      assert (Hne' : bv_unsigned r <> old).
      { intros E. apply Bool.not_true_iff_false in F1. apply F1. apply bv_eqb_eq. apply bv_eq. rewrite unsigned_lit by lia. exact E. }
      assert (Hok : mremap_dst_ok nsz avoid old (bv_unsigned r) = true).
      { unfold mremap_dst_ok. rewrite F2. cbn [Z.eqb andb].
        replace (0 <? bv_unsigned r)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (bv_unsigned r + nsz <=? alloc_ceiling)%Z with true by (symmetry; apply Z.leb_le; lia).
        replace (bv_unsigned r =? old)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb].
        rewrite <- (unsigned_lit nsz) by lia. fold nn. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact F5| exact Hcov]. }
      exists (MrMoved (bv_unsigned r)). split.
      * unfold dec_mremap, mremap_tail. replace (osz <? nsz)%Z with true by (symmetry; apply Z.ltb_lt; lia). rewrite Hok.
        subst on nn. rewrite <- (Z_to_bv_bv_unsigned r) at 1. rewrite lit_add_lit. rewrite !bv_eqb_refl. reflexivity.
      * split; [lia|]. split; [exact Hok|]. rewrite Z_to_bv_bv_unsigned. split; [exact F5|]. rewrite m_vmmaps_mremap_model_next. reflexivity.
Qed.
End RC__1.
