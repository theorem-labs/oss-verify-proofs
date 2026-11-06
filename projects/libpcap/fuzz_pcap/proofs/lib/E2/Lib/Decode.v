(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem ITree Nodes RelSpecMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Export Ceiling.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
Definition mm_errno_of (r : word) : option Z :=
  match errno_of r with Some e => if (e =? ENOMEM)%Z then Some e else None | None => None end.

Lemma mm_errno_of_Some : forall r e, mm_errno_of r = Some e -> errno_of r = Some e /\ e = ENOMEM.
Proof.
  intros r e H. unfold mm_errno_of in H. destruct (errno_of r) as [e'|] eqn:E; [|discriminate].
  destruct (Z.eqb_spec e' ENOMEM); [|discriminate]. inversion H; subst. auto.
Qed.

Lemma mm_errno_of_enomem : mm_errno_of (errno_ret ENOMEM) = Some ENOMEM.
Proof. unfold mm_errno_of. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). rewrite Z.eqb_refl. reflexivity. Qed.

Lemma mm_errno_of_small : forall r, (bv_unsigned r <= 2^64 - 4096)%Z -> mm_errno_of r = None.
Proof. intros r H. unfold mm_errno_of. rewrite errno_of_small by exact H. reflexivity. Qed.

Lemma mm_errno_of_lit : forall z, (0 <= z <= 2^64 - 4096)%Z -> mm_errno_of (Z_to_bv 64 z) = None.
Proof. intros. apply mm_errno_of_small. rewrite unsigned_lit by lia. lia. Qed.

(* [comment removed for export] *)
Definition core (rsp : resp) : option (word * list (word * list byte) * list (word * word) * list (word * word)) :=
  match rsp with
  | mkEffectU r ws zs us [] [] => Some (r, ws, zs, us)
  | _ => None
  end.

(* [comment removed for export] *)
Inductive sret : Type := SErr (e : Z) | SVal (v : Z).

(* [comment removed for export] *)
Definition dec_plain (ok : Z -> bool) (rsp : resp) : option sret :=
  match core rsp with
  | Some (r, [], [], []) =>
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
  intros ok [r ws zs us [|? ?] [|? ?]] a H; try discriminate H. unfold dec_plain in H. cbn [core] in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct (errno_of r) as [e|] eqn:E.
  - inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
  - destruct (ok (bv_unsigned r)) eqn:Hok; [|discriminate]. inversion H; subst.
    pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
    unfold errno_of in E. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [discriminate|].
    unfold eff0. rewrite Z_to_bv_bv_unsigned. repeat split; try reflexivity; try exact Hok; lia.
Qed.

Lemma dec_plain_err : forall ok e, (1 <= e <= 4095)%Z -> dec_plain ok (efferr e) = Some (SErr e).
Proof. intros ok e He. unfold dec_plain, efferr, eff0. cbn [core]. rewrite errno_of_errno_ret by lia. reflexivity. Qed.

Lemma dec_plain_val : forall ok z, (0 <= z <= 2^64 - 4096)%Z -> ok z = true ->
  dec_plain ok (eff0 (Z_to_bv 64 z)) = Some (SVal z).
Proof.
  intros ok z Hz Hok. unfold dec_plain, eff0. cbn [core]. rewrite errno_of_lit by lia.
  rewrite unsigned_lit by lia. rewrite Hok. reflexivity.
Qed.

(* [comment removed for export] *)
Inductive read_ans : Type := RdErr (e : Z) | RdData (bs : list byte).

Definition dec_read (buf count : Z) (rsp : resp) : option read_ans :=
  match core rsp with
  | Some (r, [], [], []) =>
      match errno_of r with
      | Some e => Some (RdErr e)
      | None => if (bv_unsigned r =? 0)%Z then Some (RdData []) else None
      end
  | Some (r, [(a, bs)], [], []) =>
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
  intros buf count [r ws zs us [|? ?] [|? ?]] a Hc H; try discriminate H. unfold dec_read in H. cbn [core] in H.
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
  match core rsp with
  | Some (r, [], [], []) =>
      if (1 <=? bv_unsigned r)%Z && (bv_unsigned r <=? count)%Z then Some (bv_unsigned r) else None
  | _ => None
  end.
Definition dec_write := dec_count.

(* [comment removed for export] *)
Definition dec_writev (total : Z) (rsp : resp) : option Z :=
  match core rsp with
  | Some (r, [], [], []) =>
      let k := bv_unsigned r in
      if (total =? 0)%Z then (if (k =? 0)%Z then Some 0%Z else None)
      else if (1 <=? k)%Z && (k <=? total)%Z then Some k else None
  | _ => None
  end.

Lemma dec_writev_Some : forall total rsp a, dec_writev total rsp = Some a ->
  ((total = 0 /\ a = 0) \/ (1 <= a <= total))%Z /\ rsp = eff0 (Z_to_bv 64 a) /\ (0 <= a < 2^64)%Z.
Proof.
  intros total [r ws zs us [|? ?] [|? ?]] a H; try discriminate H. unfold dec_writev in H. cbn [core] in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. cbv zeta in H.
  pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  destruct (Z.eqb_spec total 0).
  - destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    split; [left; auto|]. split; [|lia]. unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia.
    match goal with H' : bv_unsigned r = 0%Z |- _ => exact H' end.
  - destruct (Z.leb_spec0 1 (bv_unsigned r)); [|discriminate].
    destruct (Z.leb_spec0 (bv_unsigned r) total); [|discriminate]. cbn [andb] in H. inversion H; subst.
    split; [right; lia|]. split; [|lia]. unfold eff0. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma dec_writev_val : forall total k, (0 <= total < 2^64)%Z ->
  ((total = 0 /\ k = 0) \/ (1 <= k <= total))%Z ->
  dec_writev total (eff0 (Z_to_bv 64 k)) = Some k.
Proof.
  intros total k Ht Hk. unfold dec_writev, eff0. cbn [core]. rewrite unsigned_lit by lia. cbv zeta.
  destruct Hk as [[-> ->] | Hk]; [reflexivity|].
  replace (total =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  replace (1 <=? k)%Z with true by (symmetry; apply Z.leb_le; lia).
  replace (k <=? total)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma dec_count_Some : forall count rsp a, dec_count count rsp = Some a ->
  (1 <= a <= count)%Z /\ rsp = eff0 (Z_to_bv 64 a) /\ (a < 2^64)%Z.
Proof.
  intros count [r ws zs us [|? ?] [|? ?]] a H; try discriminate H. unfold dec_count in H. cbn [core] in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct (Z.leb_spec0 1 (bv_unsigned r)); [|discriminate].
  destruct (Z.leb_spec0 (bv_unsigned r) count); [|discriminate]. cbn [andb] in H. inversion H; subst.
  pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  split; [lia|]. split; [|lia]. unfold eff0. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma dec_count_val : forall count k, (1 <= k <= count)%Z -> (count < 2^64)%Z ->
  dec_count count (eff0 (Z_to_bv 64 k)) = Some k.
Proof.
  intros count k Hk Hc. unfold dec_count, eff0. cbn [core]. rewrite unsigned_lit by lia.
  replace (1 <=? k)%Z with true by (symmetry; apply Z.leb_le; lia).
  replace (k <=? count)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dec_open : resp -> option sret := dec_plain (fun v => (3 <=? v)%Z && (v <=? 4096)%Z).
(* [comment removed for export] *)
Definition dec_close : resp -> option sret := dec_plain (fun v => (v =? 0)%Z).
(* [comment removed for export] *)
Definition dec_ioctl : resp -> option sret := dec_plain (fun _ => false).
(* [comment removed for export] *)
Definition dec_openw : resp -> option sret := dec_open.
(* [comment removed for export] *)
Definition dec_writevf (count : Z) : resp -> option sret := dec_plain (fun v => (v =? count)%Z).
(* [comment removed for export] *)
Definition dec_lseek : resp -> option sret := dec_plain (fun _ => true).

(* [comment removed for export] *)
Fixpoint match_scatter (iovs : list (Z * Z)) (ws : list (word * list byte)) (n : Z)
  : option (list byte) :=
  match iovs with
  | [] => match ws with [] => if (n =? 0)%Z then Some [] else None | _ :: _ => None end
  | (a, l) :: rest =>
      let k := Z.min n l in
      if (k <=? 0)%Z then match_scatter rest ws n
      else match ws with
           | [] => None
           | (x, bs) :: ws' =>
               if bv_eqb x (Z_to_bv 64 a) && (Z.of_nat (length bs) =? k)%Z then
                 match match_scatter rest ws' (n - k)%Z with
                 | Some tl => Some (bs ++ tl)
                 | None => None
                 end
               else None
           end
  end.

Definition iovs_total_Z (iovs : list (Z * Z)) : Z := fold_right (fun p acc => (snd p + acc)%Z) 0%Z iovs.

Definition dec_readv (iovs : list (Z * Z)) (rsp : resp) : option read_ans :=
  match core rsp with
  | Some (r, ws, [], []) =>
      match errno_of r with
      | Some e => match ws with [] => Some (RdErr e) | _ :: _ => None end
      | None =>
          let n := bv_unsigned r in
          if (n <=? iovs_total_Z iovs)%Z then
            match match_scatter iovs ws n with
            | Some bs => Some (RdData bs)
            | None => None
            end
          else None
      end
  | _ => None
  end.
(* [comment removed for export] *)
Definition dec_unlink : resp -> option sret := dec_plain (fun v => (v =? 0)%Z).
(* [comment removed for export] *)
Definition dec_set_tid (rsp : resp) : option Z :=
  match core rsp with
  | Some (r, [], [], []) =>
      if (0 <? bv_unsigned r)%Z && (bv_unsigned r <? PID_MAX_ENVELOPE)%Z then Some (bv_unsigned r) else None
  | _ => None
  end.
(* [comment removed for export] *)
Definition dec_exit (rsp : resp) : option Empty_set := None.

Lemma dec_set_tid_Some : forall rsp t, dec_set_tid rsp = Some t ->
  rsp = eff0 (Z_to_bv 64 t) /\ (0 < t < PID_MAX_ENVELOPE)%Z.
Proof.
  intros [r ws zs us [|? ?] [|? ?]] t H; try discriminate H. unfold dec_set_tid in H. cbn [core] in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct (Z.ltb_spec0 0 (bv_unsigned r)); [|discriminate].
  destruct (Z.ltb_spec0 (bv_unsigned r) PID_MAX_ENVELOPE); [|discriminate]. inversion H; subst.
  unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

(* [comment removed for export] *)
Definition dec_brk0 (rsp : resp) : option Z :=
  match core rsp with Some (r, [], [], []) => Some (bv_unsigned r) | _ => None end.

Lemma dec_brk0_Some : forall rsp b, dec_brk0 rsp = Some b -> rsp = eff0 (Z_to_bv 64 b) /\ (0 <= b < 2^64)%Z.
Proof.
  intros [r ws zs us [|? ?] [|? ?]] b H; try discriminate H. unfold dec_brk0 in H. cbn [core] in H.
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
  match core rsp with
  | Some (r, [], zs, []) =>
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
  intros cur req [r ws zs us [|? ?] [|? ?]] a H; try discriminate H. unfold dec_brk in H. cbn [core] in H.
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
Section WithCeil.
Context {CE : CEIL}.

(* [comment removed for export] *)
Inductive mmap_ans : Type := MmErr (e : Z) | MmOk (a : Z).

Definition avoids (a n : Z) (avoid : list (Z * Z)) : bool :=
  forallb (fun iv => (a + n <=? fst iv)%Z || (snd iv <=? a)%Z) avoid.

Definition mmap_len (len : Z) : Z := page_round_up_Z len.

Definition mmap_addr_ok (len : Z) (avoid : list (Z * Z)) (a : Z) : bool :=
  (a mod page_size =? 0)%Z && (0 <? a)%Z && (a + mmap_len len <=? alloc_ceiling)%Z && avoids a (mmap_len len) avoid.

Definition dec_mmap (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  match core rsp with
  | Some (r, [], [], []) => match mm_errno_of r with Some e => Some (MmErr e) | None => None end
  | Some (r, [], [(a, n)], []) =>
      if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
      then Some (MmOk (bv_unsigned r)) else None
  | _ => None
  end.

Definition dec_mmap_none (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  match core rsp with
  | Some (r, [], [], []) => match mm_errno_of r with Some e => Some (MmErr e) | None => None end
  | Some (r, [], [], [(a, n)]) =>
      if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
      then Some (MmOk (bv_unsigned r)) else None
  | _ => None
  end.

#[using="Type"] Lemma avoids_In : forall a n avoid lo hi, avoids a n avoid = true -> In (lo, hi) avoid -> (a + n <= lo \/ hi <= a)%Z.
Proof.
  intros a n avoid lo hi H Hin. unfold avoids in H. rewrite forallb_forall in H.
  specialize (H _ Hin). cbn in H. apply orb_prop in H as [H|H]; [left|right]; apply Z.leb_le; exact H.
Qed.

#[using="Type"] Lemma mmap_addr_ok_true : forall len avoid a, mmap_addr_ok len avoid a = true ->
  (a mod page_size = 0 /\ 0 < a /\ a + mmap_len len <= alloc_ceiling)%Z /\ avoids a (mmap_len len) avoid = true.
Proof.
  intros len avoid a H. unfold mmap_addr_ok in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.

#[using="Type"] Lemma dec_mmap_Some : forall len avoid rsp x, dec_mmap len avoid rsp = Some x ->
  match x with
  | MmErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | MmOk a => rsp = mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] /\ mmap_addr_ok len avoid a = true
  end.
Proof.
  intros len avoid [r ws zs us [|? ?] [|? ?]] x H; try discriminate H. unfold dec_mmap in H. cbn [core] in H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct (mm_errno_of r) eqn:E; [|discriminate]. inversion H; subst.
    apply mm_errno_of_Some in E as [E _]. apply errno_of_Some in E as [-> He]. auto.
  - destruct us; [|discriminate].
    destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

#[using="Type"] Lemma dec_mmap_none_Some : forall len avoid rsp x, dec_mmap_none len avoid rsp = Some x ->
  match x with
  | MmErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | MmOk a => rsp = mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] /\ mmap_addr_ok len avoid a = true
  end.
Proof.
  intros len avoid [r ws zs us [|? ?] [|? ?]] x H; try discriminate H. unfold dec_mmap_none in H. cbn [core] in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct (mm_errno_of r) eqn:E; [|discriminate]. inversion H; subst. apply mm_errno_of_Some in E as [E _]. apply errno_of_Some in E as [-> He]. auto.
  - destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

(* [comment removed for export] *)
Inductive range_ans : Type := RgErr (e : Z) | RgDone (changed : bool).

Definition dec_munmap (addr len : Z) (rsp : resp) : option range_ans :=
  match core rsp with
  | Some (r, [], [], []) =>
      match mm_errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | Some (r, [], [], [(a, n)]) =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end.

Definition dec_mprotect (addr len : Z) (rsp : resp) : option range_ans :=
  match core rsp with
  | Some (r, [], [], []) =>
      match mm_errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | Some (r, [], [(a, n)], []) =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition dec_mmapnr (addr len : Z) (rsp : resp) : option range_ans :=
  match core rsp with
  | Some (r, [], [], []) => match mm_errno_of r with Some e => Some (RgErr e) | None => None end
  | Some (r, [], [(a, n)], []) =>
      if bv_eqb r (Z_to_bv 64 addr) && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end.

#[using="Type"] Lemma dec_mmapnr_Some : forall addr len rsp x, dec_mmapnr addr len rsp = Some x ->
  match x with
  | RgErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | RgDone false => False
  | RgDone true => rsp = mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))]
  end.
Proof.
  intros addr len [r ws zs us [|? ?] [|? ?]] x H; try discriminate H. unfold dec_mmapnr in H. cbn [core] in H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate].
    destruct (mm_errno_of r) eqn:E; [|discriminate]. inversion H; subst.
    apply mm_errno_of_Some in E as [E _]. apply errno_of_Some in E as [-> He]. auto.
  - destruct us; [|discriminate].
    destruct (bv_eqb r _) eqn:E0; [|discriminate]. destruct (bv_eqb a _) eqn:E1; [|discriminate].
    destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E0. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    reflexivity.
Qed.

#[using="Type"] Lemma dec_munmap_Some : forall addr len rsp x, dec_munmap addr len rsp = Some x ->
  match x with
  | RgErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | RgDone false => rsp = eff0 (Z_to_bv 64 0)
  | RgDone true => rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] []
  end.
Proof.
  intros addr len [r ws zs us [|? ?] [|? ?]] x H; try discriminate H. unfold dec_munmap in H. cbn [core] in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct (mm_errno_of r) eqn:E. { inversion H; subst. apply mm_errno_of_Some in E as [E _]. apply errno_of_Some in E as [-> He]. auto. }
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

#[using="Type"] Lemma dec_mprotect_Some : forall addr len rsp x, dec_mprotect addr len rsp = Some x ->
  match x with
  | RgErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | RgDone false => rsp = eff0 (Z_to_bv 64 0)
  | RgDone true => rsp = mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))]
  end.
Proof.
  intros addr len [r ws zs us [|? ?] [|? ?]] x H; try discriminate H. unfold dec_mprotect in H. cbn [core] in H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate].
    destruct (mm_errno_of r) eqn:E. { inversion H; subst. apply mm_errno_of_Some in E as [E _]. apply errno_of_Some in E as [-> He]. auto. }
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct us; [|discriminate]. destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive mremap_ans : Type := MrErr (e : Z) | MrSame | MrMoved (a : Z).

Definition dec_mremap (old oldlen newlen : Z) (avoid_same avoid : list (Z * Z)) (rsp : resp) : option mremap_ans :=
  let on := mmap_len oldlen in
  let nn := mmap_len newlen in
  match rsp with
  | mkEffectU r [] zs us cps [] =>
      match mm_errno_of r with
      | Some e => match zs, us, cps with [], [], [] => Some (MrErr e) | _, _, _ => None end
      | None =>
          if bv_eqb r (Z_to_bv 64 old) then
            match zs, us, cps with
            | [], [], [] => if (on =? nn)%Z then Some MrSame else None
            | [], [(ua, un)], [] =>
                if (nn <? on)%Z && bv_eqb ua (Z_to_bv 64 (old + nn)) && bv_eqb un (Z_to_bv 64 (on - nn))
                then Some MrSame else None
            | [(za, zn)], [], [] =>
                if (on <? nn)%Z && bv_eqb za (Z_to_bv 64 (old + on)) && bv_eqb zn (Z_to_bv 64 (nn - on))
                   && (old + nn <=? alloc_ceiling)%Z && avoids old nn avoid_same
                then Some MrSame else None
            | _, _, _ => None
            end
          else
            match zs, us, cps with
            | [(za, zn)], [(ua, un)], [mkCopy cs cd cl] =>
                let a := bv_unsigned r in
                if (on <? nn)%Z && bv_eqb za (Z_to_bv 64 (a + on)) && bv_eqb zn (Z_to_bv 64 (nn - on))
                   && bv_eqb ua (Z_to_bv 64 old) && bv_eqb un (Z_to_bv 64 on)
                   && bv_eqb cs (Z_to_bv 64 old) && bv_eqb cd r && bv_eqb cl (Z_to_bv 64 on)
                   && mmap_addr_ok newlen avoid a
                then Some (MrMoved a) else None
            | _, _, _ => None
            end
      end
  | _ => None
  end.

#[using="Type"] Lemma dec_mremap_Some : forall old oldlen newlen avoid_same avoid rsp x,
  let on := mmap_len oldlen in
  let nn := mmap_len newlen in
  dec_mremap old oldlen newlen avoid_same avoid rsp = Some x ->
  match x with
  | MrErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
  | MrSame =>
         (on = nn /\ rsp = eff0 (Z_to_bv 64 old))
      \/ ((nn < on)%Z /\ rsp = mkEffectU (Z_to_bv 64 old) [] [] [(Z_to_bv 64 (old + nn), Z_to_bv 64 (on - nn))] [] [])
      \/ ((on < nn)%Z /\ (old + nn <= alloc_ceiling)%Z /\ avoids old nn avoid_same = true
          /\ rsp = mkEffect (Z_to_bv 64 old) [] [(Z_to_bv 64 (old + on), Z_to_bv 64 (nn - on))])
  | MrMoved a =>
      (on < nn)%Z /\ mmap_addr_ok newlen avoid a = true /\ (0 <= a < 2^64)%Z /\ Z_to_bv 64 a <> Z_to_bv 64 old
      /\ rsp = mkEffectU (Z_to_bv 64 a) [] [(Z_to_bv 64 (a + on), Z_to_bv 64 (nn - on))]
                         [(Z_to_bv 64 old, Z_to_bv 64 on)] [mkCopy (Z_to_bv 64 old) (Z_to_bv 64 a) (Z_to_bv 64 on)] []
  end.
Proof.
  intros old oldlen newlen avoid_same avoid [r ws zs us cps [|? ?]] x on nn H; [|destruct ws; discriminate H].
  unfold dec_mremap in H. destruct ws; [|discriminate H]. fold on nn in H.
  destruct (mm_errno_of r) as [e|] eqn:E.
  { destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cps; [|discriminate].
    inversion H; subst. apply mm_errno_of_Some in E as [E _]. apply errno_of_Some in E as [-> He]. auto. }
  pose proof (bv_unsigned_in_range 64 r) as Hr. unfold bv_modulus in Hr. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hr.
  destruct (bv_eqb r (Z_to_bv 64 old)) eqn:Er.
  - apply bv_eqb_eq in Er. subst r.
    destruct zs as [|[za zn] [|? ?]]; destruct us as [|[ua un] [|? ?]]; destruct cps as [|? ?]; try discriminate H.
    + destruct (Z.eqb_spec on nn); [|discriminate]. inversion H; subst. left. auto.
    + destruct (Z.ltb_spec0 nn on); [|discriminate]. destruct (bv_eqb ua _) eqn:E1; [|discriminate].
      destruct (bv_eqb un _) eqn:E2; [|discriminate]. cbn [andb] in H. inversion H; subst.
      apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. right; left. auto.
    + destruct (Z.ltb_spec0 on nn); [|discriminate]. destruct (bv_eqb za _) eqn:E1; [|discriminate].
      destruct (bv_eqb zn _) eqn:E2; [|discriminate]. destruct (Z.leb_spec0 (old + nn) alloc_ceiling); [|discriminate].
      destruct (avoids old nn avoid_same) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
      apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. right; right. auto.
  - destruct zs as [|[za zn] [|? ?]]; try discriminate H. destruct us as [|[ua un] [|? ?]]; try discriminate H.
    destruct cps as [|[cs cd cl] [|? ?]]; try discriminate H.
    destruct (Z.ltb_spec0 on nn); [|discriminate].
    destruct (bv_eqb za _) eqn:E1; [|discriminate]. destruct (bv_eqb zn _) eqn:E2; [|discriminate].
    destruct (bv_eqb ua _) eqn:E3; [|discriminate]. destruct (bv_eqb un _) eqn:E4; [|discriminate].
    destruct (bv_eqb cs _) eqn:E5; [|discriminate]. destruct (bv_eqb cd _) eqn:E6; [|discriminate].
    destruct (bv_eqb cl _) eqn:E7; [|discriminate]. destruct (mmap_addr_ok newlen avoid (bv_unsigned r)) eqn:E8; [|discriminate].
    cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. apply bv_eqb_eq in E3. apply bv_eqb_eq in E4.
    apply bv_eqb_eq in E5. apply bv_eqb_eq in E6. apply bv_eqb_eq in E7. subst.
    rewrite !Z_to_bv_bv_unsigned. split; [assumption|]. split; [exact E8|]. split; [lia|]. split; [|reflexivity].
    intros Ee. rewrite <- Ee in Er. rewrite bv_eqb_refl in Er. discriminate Er.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma length_file_read_le_count : forall data off count,
  (0 <= count < 2^64)%Z -> (Z.of_nat (length (file_read data off (Z_to_bv 64 count))) <= count)%Z.
Proof.
  intros data off count Hc. rewrite file_read_unguarded. rewrite length_firstn.
  unfold word_to_nat. rewrite unsigned_lit by lia. lia.
Qed.

#[using="Type"] Lemma nstep_dec_read : forall fd buf count mo rsp mo' evs,
  (0 <= count < 2^64)%Z ->
  nstep (NRead fd buf count) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_read buf count rsp = Some a /\
  match a with
  | RdErr e => mo' = mo /\
      ((e = EBADF /\ (fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
                      \/ (exists p off, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFileW p off))
                      \/ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdNull))   (* [comment removed for export] *)
       \/ (e = EISDIR /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir))
  | RdData bs => exists p off data,
      fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) /\
      fs_lookup (m_fs mo) p = Some data /\
      bs = file_read data off (Z_to_bv 64 count) /\
      mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
  end.
Proof.
  intros fd buf count mo rsp mo' evs Hc [-> H]. split; [reflexivity|].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try contradiction.
  - destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|contradiction]. destruct H as [-> ->].
    set (bs := file_read data off (Z_to_bv 64 count)).
    pose proof (length_file_read_le_count data off count Hc) as Hl. fold bs in Hl.
    exists (RdData bs). split.
    + unfold dec_read. cbn [core]. destruct bs as [|b bs'] eqn:Ebs; cbn [delivered_writes].
      * unfold len_word. cbn [length Z.of_nat]. rewrite errno_of_lit by lia. reflexivity.
      * rewrite bv_eqb_refl. unfold len_word. rewrite unsigned_lit by (cbn [length] in *; lia).
        rewrite Z.eqb_refl.
        replace (1 <=? Z.of_nat (length (b :: bs')))%Z with true by (symmetry; apply Z.leb_le; cbn; lia).
        replace (Z.of_nat (length (b :: bs')) <=? count)%Z with true by (symmetry; apply Z.leb_le; lia).
        reflexivity.
    + exists p, off, data. auto.
  - destruct H as [-> ->]. exists (RdErr EBADF). split; [reflexivity|]. split; [reflexivity|]. left. split; [reflexivity|]. right; left. eauto.
  - destruct H as [-> ->]. exists (RdErr EISDIR). split; [reflexivity| auto].
  - destruct H as [-> ->]. exists (RdErr EBADF). split; [reflexivity|]. split; [reflexivity|]. left. split; [reflexivity|]. right; right. reflexivity.
  - destruct H as [-> ->]. exists (RdErr EBADF). split; [reflexivity| auto].
Qed.

#[using="Type"] Lemma nstep_dec_write : forall fd bs mo rsp mo' evs,
  (1 <= Z.of_nat (length bs) < 2^64)%Z ->
  nstep (NWrite fd bs) mo rsp mo' evs ->
  exists k, (1 <= k <= Z.of_nat (length bs))%Z /\
    dec_write (Z.of_nat (length bs)) rsp = Some k /\ mo' = mo /\
    evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) bs).
Proof.
  intros fd bs mo rsp mo' evs Hl (-> & k & Hk & -> & ->). unfold wr_range in Hk. exists (Z.of_nat k). split; [lia|]. split; [|split; [reflexivity|]].
  - unfold dec_write. apply dec_count_val; lia.
  - rewrite Nat2Z.id. reflexivity.
Qed.

#[using="Type"] Lemma nstep_dec_writev : forall fd bufs mo rsp mo' evs,
  (Z.of_nat (length (concat bufs)) < 2^64)%Z ->
  nstep (NWritev fd bufs) mo rsp mo' evs ->
  exists k, ((length (concat bufs) = 0%nat /\ k = 0) \/ (1 <= k <= Z.of_nat (length (concat bufs))))%Z /\
    dec_writev (Z.of_nat (length (concat bufs))) rsp = Some k /\ mo' = mo /\
    evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) (concat bufs)).
Proof.
  intros fd bufs mo rsp mo' evs Hl (-> & k & Hk & -> & ->). unfold wr_range in Hk. exists (Z.of_nat k). split; [lia|]. split; [|split; [reflexivity|]].
  - apply dec_writev_val; lia.
  - rewrite Nat2Z.id. reflexivity.
Qed.

#[using="Type"] Lemma openat_errnos_range : forall e, In e openat_errnos -> (1 <= e <= 4095)%Z.
Proof. intros e H. cbn in H. unfold ENOMEM, EACCES, EMFILE, ENFILE in H. lia. Qed.

#[using="Type"] Lemma nstep_dec_open : forall path mo rsp mo' evs,
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
  destruct (path_eqb (c :: path') dot_path). { apply (Hres FdDir); [left; reflexivity| exact H]. }
  destruct (fs_lookup (m_fs mo) (c :: path')).
  - apply (Hres (FdFile (c :: path') (Z_to_bv 64 0))); [right; reflexivity| exact H].
  - destruct H as [-> ->]. apply (Herr ENOENT); try reflexivity. unfold ENOENT; lia.
Qed.

#[using="Type"] Lemma nstep_dec_close : forall fd mo rsp mo' evs,
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

#[using="Type"] Lemma nstep_dec_ioctl : forall fd req mo rsp mo' evs,
  nstep (NIoctl fd req) mo rsp mo' evs ->
  exists e, dec_ioctl rsp = Some (SErr e) /\ mo' = mo /\ evs = [] /\
    ((e = ENOTTY /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) <> None)
     \/ (e = EBADF /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None)).
Proof.
  intros fd req mo rsp mo' evs (-> & -> & H).
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) eqn:Hlk; rewrite H.
  - exists ENOTTY. split; [apply dec_plain_err; unfold ENOTTY; lia|]. split; [reflexivity|]. split; [reflexivity|]. left. split; [reflexivity|congruence].
  - exists EBADF. split; [apply dec_plain_err; unfold EBADF; lia|]. split; [reflexivity|]. split; [reflexivity|]. right. auto.
Qed.

#[using="Type"] Lemma nstep_dec_set_tid : forall mo rsp mo' evs,
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
    - destruct H as [-> _]. exact (minv_tid _ _ Hminv E).
    - exact (proj1 H). }
  split.
  - unfold dec_set_tid, eff0. cbn [core]. destruct Hr as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. rewrite H1, H2. reflexivity.
  - split; [exact Hr|]. destruct (m_tid mo) as [t0|]; destruct H as [H0 ->]; [left; subst; auto| right; auto].
Qed.

#[using="Type"] Lemma nstep_exit_none : forall c mo rsp mo' evs, nstep (NExit c) mo rsp mo' evs -> False.
Proof. intros c mo rsp mo' evs H. exact H. Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma m_vmmaps_vm_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. reflexivity. Qed.

#[using="Type"] Lemma m_vmmaps_forget_vm_ranges : forall rs m, m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|]. cbn [forget_vm_ranges].
  rewrite IH. apply m_vmmaps_vm_forget_range.
Qed.

#[using="Type"] Lemma m_vmmaps_with_brk_next : forall m req r, m_vmmaps (with_brk_next m req r) = brk_model_next (m_vmmaps m) req r.
Proof.
  intros. unfold with_brk_next. cbv zeta. rewrite m_vmmaps_forget_vm_ranges. apply m_vmmaps_with_vmmaps.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_dec_brk0 : forall mo rsp mo' evs,
  nstep (NBrk 0) mo rsp mo' evs ->
  evs = [] /\ dec_brk0 rsp = Some (bv_unsigned (vm_brk (m_vmmaps mo))) /\ vm_only mo mo'
  /\ vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo).
Proof.
  intros mo rsp mo' evs H.
  pose proof (nstep_mm_vm_only (NBrk 0) mo rsp mo' evs I H) as (Hv & -> & _). split; [reflexivity|].
  apply nstep_brk_iff in H as (_ & r & Hr & -> & -> & _).
  unfold brk_r_ok in Hr. change (w_is0 (Z_to_bv 64 0)) with true in Hr. cbn [orb] in Hr. apply bv_eqb_eq in Hr. subst r.
  unfold brk_zeros, brk_is_grow. change (w_is0 (Z_to_bv 64 0)) with true. cbn [negb andb].
  unfold brk_unmaps. cbv zeta. unfold brk_page_range. rewrite Z.ltb_irrefl.
  split; [destruct (0 <? _)%Z; reflexivity|]. split; [exact Hv|].
  rewrite m_vmmaps_with_brk_next. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_dec_brk : forall req mo rsp mo' evs,
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
  pose proof (nstep_mm_vm_only (NBrk req) mo rsp mo' evs I H) as (Hv & -> & _). split; [reflexivity|]. split; [exact Hv|].
  apply nstep_brk_iff in H as (_ & r & E1 & -> & -> & _). rewrite m_vmmaps_with_brk_next. fold h. cbn [brk_model_next vm_brk].
  unfold brk_r_ok in E1. cbv zeta in E1. fold h in E1. rewrite w_is0_lit in E1 by lia.
  replace (req =? 0)%Z with false in E1 by (symmetry; apply Z.eqb_neq; lia).
  unfold min_brk in E1. rewrite unsigned_lit in E1 by lia.
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
    unfold dec_brk. cbn [core]. rewrite Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
  - destruct Hr as [-> | ->].
    + exists BrkGrown. split; [|reflexivity].
      unfold dec_brk. cbn [core]. rewrite unsigned_lit by lia.
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
      unfold dec_brk. cbn [core]. rewrite Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition covered (maps : list (word * word)) (iv : Z * Z) : Prop :=
  exists e sz, In (e, sz) maps /\ (bv_unsigned e <= fst iv)%Z /\ (snd iv <= bv_unsigned e + bv_unsigned sz)%Z.

#[using="Type"] Lemma region_free_In : forall maps a n e sz,
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

#[using="Type"] Lemma avoids_of_region_free : forall maps a n avoid,
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

#[using="Type"] Lemma mmap_len_bound : forall len, (0 < len)%Z -> (len <= mmap_len len < len + 4096)%Z.
Proof. intros len H. unfold mmap_len, page_round_up_Z, page_size. split; [|]; nia || lia. Qed.

#[using="Type"] Lemma mmap_errnos_when_In : forall b e, In e (mmap_errnos_when b) -> e = ENOMEM.
Proof. intros [|] e H; cbn in H; [destruct H as [<-|[]]; reflexivity | destruct H]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_dec_mmap : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  (page_round_down_Z (alloc_top h) <= alloc_ceiling)%Z ->     (* [comment removed for export] *)
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
  intros len avoid mo rsp mo' evs h Hlen Hlen2 Hceil Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMmap 0 len _ (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ltac:(reflexivity) H) as (Hv & -> & _). split; [reflexivity|]. split; [exact Hv|].
  destruct H as [_ [H _]]. cbn [node_input] in H. rewrite syscall_spec_222 in H by reflexivity. cbn [in_arg in_args pure_input nth] in H.
  apply mmap_rw_outcome in H; [|reflexivity|reflexivity|rewrite w_is0_lit by lia; apply Z.eqb_neq; lia|reflexivity].
  fold h in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  destruct H as [(e & HIn & Heq) | (a & (A1 & A2 & A3 & A4 & A5) & Heq)]; apply Ok_inj in Heq as (-> & -> & _).
  - apply mmap_errnos_when_In in HIn. subst e.
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap. cbn [core]. rewrite mm_errno_of_enomem. reflexivity.
  - assert (A3' : (bv_unsigned a + mmap_len len <= alloc_ceiling)%Z).
    { eapply Z.le_trans; [| exact Hceil]. apply page_round_down_Z_ge_aligned; [| exact A3].
      unfold page_size in A1. rewrite Z.add_mod, A1 by lia. unfold mmap_len, page_round_up_Z, page_size.
      rewrite Z_mod_mult. reflexivity. }
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned a) = true).
    { unfold mmap_addr_ok. rewrite (proj2 (Z.eqb_eq _ _) A1), (proj2 (Z.ltb_lt _ _) A2), (proj2 (Z.leb_le _ _) A3'). cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact A4| exact Hcov]. }
    exists (MmOk (bv_unsigned a)). split.
    + unfold dec_mmap. cbn [core]. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact A4|].
      rewrite with_mmap_backing_id by reflexivity. apply m_vmmaps_with_vmmaps.
Qed.

#[using="Type"] Lemma nstep_dec_mmap_none : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  (page_round_down_Z (alloc_top h) <= alloc_ceiling)%Z ->     (* [comment removed for export] *)
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
  intros len avoid mo rsp mo' evs h Hlen Hlen2 Hceil Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMmap 0 len _ (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ltac:(reflexivity) H) as (Hv & -> & _). split; [reflexivity|]. split; [exact Hv|].
  destruct H as [_ [H _]]. cbn [node_input] in H. rewrite syscall_spec_222 in H by reflexivity. cbn [in_arg in_args pure_input nth] in H.
  apply mmap_noaccess_outcome in H; [|reflexivity|reflexivity|rewrite w_is0_lit by lia; apply Z.eqb_neq; lia|reflexivity|reflexivity].
  fold h in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  destruct H as [(e & HIn & Heq) | (a & (A1 & A2 & A3 & A4) & Heq)]; apply Ok_inj in Heq as (-> & -> & _).
  - apply mmap_errnos_when_In in HIn. subst e.
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap_none. cbn [core]. rewrite mm_errno_of_enomem. reflexivity.
  - assert (A3' : (bv_unsigned a + mmap_len len <= alloc_ceiling)%Z).
    { eapply Z.le_trans; [| exact Hceil]. apply page_round_down_Z_ge_aligned; [| exact A3].
      unfold page_size in A1. rewrite Z.add_mod, A1 by lia. unfold mmap_len, page_round_up_Z, page_size.
      rewrite Z_mod_mult. reflexivity. }
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned a) = true).
    { unfold mmap_addr_ok. rewrite (proj2 (Z.eqb_eq _ _) A1), (proj2 (Z.ltb_lt _ _) A2), (proj2 (Z.leb_le _ _) A3'). cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact A4| exact Hcov]. }
    exists (MmOk (bv_unsigned a)). split.
    + unfold dec_mmap_none. cbn [core]. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact A4|].
      rewrite with_mmap_backing_id by reflexivity. apply m_vmmaps_with_vmmaps.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_dec_munmap : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len < 2^64)%Z -> (addr mod page_size = 0)%Z ->
  (addr + mmap_len len <= TASK_SIZE)%Z ->     (* [comment removed for export] *)
  map_has (vm_maps h) a n = true ->
  nstep (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  dec_munmap addr len rsp = Some (RgDone true) /\
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
                              (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                              (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hal Hnw Hhas H.
  pose proof (mmap_len_bound len (proj1 Hlen)) as Hb.
  pose proof (nstep_mm_vm_only (NMunmap addr len) mo rsp mo' evs I H) as (Hv & -> & _). split; [reflexivity|]. split; [exact Hv|].
  assert (Hnw' : (addr + mmap_len len < 2^64)%Z) by (unfold TASK_SIZE in Hnw; lia).
  destruct H as [_ [H _]]. cbn [node_input] in H. rewrite syscall_spec_215 in H by reflexivity. cbn [in_arg in_args pure_input nth] in H.
  apply munmap_exact_outcome in H;
    [| rewrite unsigned_lit by lia; exact Hal
     | rewrite w_is0_lit by lia; apply Z.eqb_neq; lia
     | rewrite !unsigned_lit by lia; unfold mmap_len in *; lia
     | rewrite unsigned_lit by lia; exact Hhas ].
  fold a in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) n h in H.
  apply Ok_inj in H as (-> & -> & _). split.
  - unfold dec_munmap. cbn [core]. subst a n. rewrite !bv_eqb_refl. reflexivity.
  - unfold with_mmap_destroyed. rewrite m_vmmaps_vm_forget_range. apply m_vmmaps_with_vmmaps.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_dec_mprotect : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len < 2^64)%Z -> (addr mod page_size = 0)%Z ->
  (addr + mmap_len len < 2^64)%Z ->
  map_contains (vm_noaccess h) a n = true -> map_contains (vm_maps h) a n = true ->
  nstep (NMprotect addr len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mprotect addr len rsp = Some x /\
  match x with
  | RgErr e => e = ENOMEM /\ mo' = mo
  | RgDone false => False
  | RgDone true => mprotect_budget_ok mo a n = true /\ mo' = mprotect_model_next mo a n
  end.
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hal Hnw Hna Hmc H.
  pose proof (mmap_len_bound len (proj1 Hlen)) as Hb.
  pose proof (nstep_mm_vm_only (NMprotect addr len _) mo rsp mo' evs I H) as (Hv & -> & _). split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mprotect_expose_outcome in H;
    [| reflexivity
     | rewrite unsigned_lit by lia; exact Hal
     | rewrite w_is0_lit by lia; apply Z.eqb_neq; lia
     | rewrite !unsigned_lit by lia; unfold two_pow_64, mmap_len in *; lia
     | reflexivity
     | rewrite unsigned_lit by lia; exact Hna
     | rewrite unsigned_lit by lia; exact Hmc ].
  cbv zeta in H. fold a in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) n h in H.
  destruct H as [(e & HIn & Heq) | (Hbud & Heq)]; apply Ok_inj in Heq as (-> & -> & _).
  - assert (He : e = ENOMEM).
    { unfold mprotect_errnos_when in HIn. destruct (mprotect_refusable _ _ _); cbn in HIn; [destruct HIn as [<-|[]]; reflexivity|destruct HIn]. }
    subst e. exists (RgErr ENOMEM). split; [|auto].
    unfold dec_mprotect. cbn [core]. rewrite mm_errno_of_enomem. reflexivity.
  - exists (RgDone true). split; [|auto].
    unfold dec_mprotect. cbn [core]. subst a n. rewrite !bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma nstep_dec_openw : forall path mode mo rsp mo' evs,
  minv mo ->
  nstep (NOpenW path mode) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_openw rsp = Some a /\
  match a with
  | SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
  | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z
      /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
      /\ (path_max <=? length path)%nat = false /\ path <> []
      /\ (* [comment removed for export] *)
         ((path = devnull_path /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) FdNull) mo)
          \/ (path <> devnull_path /\ write_dirref path mo = false /\ path <> dot_path
              /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFileW path (Z_to_bv 64 0)))
                         (with_fs (fs_set (m_fs mo) path []) mo)))
  end.
Proof.
  intros path mode mo rsp mo' evs Hminv [-> H]. split; [reflexivity|].
  assert (Herr : forall e P, (1 <= e <= 4095)%Z -> rsp = efferr e -> mo' = mo ->
            exists a, dec_openw rsp = Some a /\ match a with SErr e => mo' = mo /\ (1 <= e <= 4095)%Z | SVal fd => P fd end).
  { intros e P He -> ->. exists (SErr e). split; [apply dec_plain_err; exact He| auto]. }
  destruct (path_max <=? length path)%nat eqn:Elong. { destruct H as [-> ->]. eapply Herr; try reflexivity. unfold ENAMETOOLONG; lia. }
  destruct path as [|c path']. { destruct H as [-> ->]. eapply Herr; try reflexivity. unfold ENOENT; lia. }
  assert (Hval : forall mo1, fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None -> rsp = eff0 (alloc_fd (m_fds mo)) ->
            forall (P : Z -> Prop), P (bv_unsigned (alloc_fd (m_fds mo))) ->
            exists a, dec_openw rsp = Some a /\ match a with SErr e => mo1 = mo /\ (1 <= e <= 4095)%Z
                                                         | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z
                                                                      /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None /\ P fd end).
  { intros mo1 Hlk -> P HP. pose proof (alloc_fd_range mo Hminv Hlk) as Hr.
    exists (SVal (bv_unsigned (alloc_fd (m_fds mo)))). split.
    - unfold dec_openw, dec_open. rewrite <- (Z_to_bv_bv_unsigned (alloc_fd (m_fds mo))) at 1.
      apply dec_plain_val; [lia|]. apply andb_true_intro; split; apply Z.leb_le; lia.
    - rewrite Z_to_bv_bv_unsigned. split; [reflexivity|]. split; [lia|]. split; [exact Hlk|exact HP]. }
  destruct (path_eqb (c :: path') devnull_path) eqn:Edn.
  { apply path_eqb_eq in Edn. destruct H as [(e & HIn & -> & ->) | (Hlk & Hr & ->)].
    - eapply Herr; [apply openat_errnos_range; exact HIn | reflexivity | reflexivity].
    - eapply (Hval _ Hlk Hr). rewrite Z_to_bv_bv_unsigned. split; [reflexivity|]. split; [discriminate|]. left. auto. }
  destruct (path_has_slash (c :: path')) eqn:Ehs. { destruct H. }   (* [comment removed for export] *)
  destruct (write_dirref (c :: path') mo) eqn:Edir. { destruct H as [-> ->]. eapply Herr; try reflexivity. unfold EISDIR; lia. }
  destruct H as [(e & HIn & -> & ->) | (Hlk & Hr & ->)].
  - eapply Herr; [apply openat_errnos_range; exact HIn | reflexivity | reflexivity].
  - eapply (Hval _ Hlk Hr). rewrite Z_to_bv_bv_unsigned. split; [reflexivity|]. split; [discriminate|]. right.
    split; [intros E; rewrite E, path_eqb_refl in Edn; discriminate|]. split; [reflexivity|]. split; [|reflexivity].
    intros E. rewrite E in Edir. discriminate Edir.
Qed.

#[using="Type"] Lemma nstep_dec_writevf : forall fd bufs mo rsp mo' evs,
  (Z.of_nat (length (concat bufs)) <= 2^64 - 4096)%Z ->
  nstep (NWritevF fd bufs) mo rsp mo' evs ->
  evs = [] /\ dec_writevf (Z.of_nat (length (concat bufs))) rsp = Some (SVal (Z.of_nat (length (concat bufs)))) /\
  ((exists p off data,
      fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFileW p off) /\ fs_lookup (m_fs mo) p = Some data /\
      mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFileW p (off + len_word (concat bufs))%bv))
              (with_fs (fs_set (m_fs mo) p (file_write data off (concat bufs))) mo))
   \/ (* [comment removed for export] *)
      (fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdNull /\ mo' = mo)).
Proof.
  intros fd bufs mo rsp mo' evs Hl [-> H]. split; [reflexivity|].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try contradiction.
  - destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|contradiction]. cbv zeta in H. destruct H as [-> ->].
    split; [apply dec_plain_val; [lia| apply Z.eqb_refl]|]. left. exists p, off, data. auto.
  - destruct H as [-> ->]. split; [apply dec_plain_val; [lia| apply Z.eqb_refl]|]. right. auto.
Qed.

#[using="Type"] Lemma nstep_dec_lseek : forall fd off whence mo rsp mo' evs,
  nstep (NLseek fd off whence) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_lseek rsp = Some a /\
  match a with
  | SErr e => mo' = mo /\ ((e = EBADF /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None) \/ e = EINVAL)
  | SVal r => (0 <= r < 2^63)%Z /\
      ((exists (isw : bool) p cur data b,
          fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (if isw then FdFileW p cur else FdFile p cur) /\
          fs_lookup (m_fs mo) p = Some data /\
          lseek_base (Z_to_bv 64 whence) cur (len_word data) = Some b /\
          (bv_unsigned b + bv_signed (Z_to_bv 64 off) = r)%Z /\
          mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (if isw then FdFileW p (Z_to_bv 64 r) else FdFile p (Z_to_bv 64 r))) mo)
       \/ (* [comment removed for export] *)
          (fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdNull /\ r = 0%Z /\ mo' = mo))
  end.
Proof.
  intros fd off whence mo rsp mo' evs [-> H]. split; [reflexivity|].
  assert (Hres : forall (isw : bool) p cur data,
            fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (if isw then FdFileW p cur else FdFile p cur) ->
            fs_lookup (m_fs mo) p = Some data ->
            lseek_result mo fd (fun r => if isw then FdFileW p r else FdFile p r) (lseek_base (Z_to_bv 64 whence) cur (len_word data)) off rsp mo' ->
            exists a, dec_lseek rsp = Some a /\
            match a with
            | SErr e => mo' = mo /\ ((e = EBADF /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None) \/ e = EINVAL)
            | SVal r => (0 <= r < 2^63)%Z /\
                ((exists (isw : bool) p cur data b,
                    fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (if isw then FdFileW p cur else FdFile p cur) /\
                    fs_lookup (m_fs mo) p = Some data /\
                    lseek_base (Z_to_bv 64 whence) cur (len_word data) = Some b /\
                    (bv_unsigned b + bv_signed (Z_to_bv 64 off) = r)%Z /\
                    mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (if isw then FdFileW p (Z_to_bv 64 r) else FdFile p (Z_to_bv 64 r))) mo)
                 \/ (fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdNull /\ r = 0%Z /\ mo' = mo))
            end).
  { intros isw p cur data Hlk Hfs HR. unfold lseek_result in HR.
    destruct (lseek_base (Z_to_bv 64 whence) cur (len_word data)) as [b|] eqn:Hb; [|contradiction].
    unfold lseek_dest in HR.
    destruct ((0 <=? bv_unsigned b + bv_signed (Z_to_bv 64 off)) && (bv_unsigned b + bv_signed (Z_to_bv 64 off) <? 2 ^ 63))%Z eqn:E.
    - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. destruct HR as [-> ->].
      exists (SVal (bv_unsigned b + bv_signed (Z_to_bv 64 off))%Z). split.
      + apply dec_plain_val; [lia|reflexivity].
      + split; [lia|]. left. exists isw, p, cur, data, b. repeat split; try assumption; try reflexivity.
    - destruct HR as [-> ->]. exists (SErr EINVAL). split; [apply dec_plain_err; unfold EINVAL; lia|]. auto. }
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p cur|p cur|p cur|p cur| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try contradiction.
  - destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|contradiction]. exact (Hres false p cur data eq_refl Hfs H).
  - destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|contradiction]. exact (Hres true p cur data eq_refl Hfs H).
  - destruct H as [-> ->]. exists (SVal 0). split; [apply dec_plain_val; [lia|reflexivity]|]. split; [lia|]. right. auto.
  - destruct H as [-> ->]. exists (SErr EBADF). split; [apply dec_plain_err; unfold EBADF; lia|]. auto.
Qed.

#[using="Type"] Lemma unlinkat_errnos_range' : forall e, In e unlinkat_errnos -> (1 <= e <= 4095)%Z.
Proof. intros e H. cbn in H. unfold ENOMEM, EACCES, EPERM, EROFS, EBUSY in H. lia. Qed.

#[using="Type"] Lemma nstep_dec_unlink : forall path rmdir mo rsp mo' evs,
  nstep (NUnlink path rmdir) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_unlink rsp = Some a /\
  match a with
  | SErr e => mo' = mo /\
      ((fs_under (m_fs mo) path = true /\ e = (if rmdir then ENOTEMPTY else EISDIR))
       \/ (fs_under (m_fs mo) path = false /\ fs_lookup (m_fs mo) path = None /\ e = ENOENT)
       \/ (fs_under (m_fs mo) path = false /\ fs_lookup (m_fs mo) path <> None /\ rmdir = true /\ e = ENOTDIR)
       \/ (fs_under (m_fs mo) path = false /\ fs_lookup (m_fs mo) path <> None /\ rmdir = false /\ In e unlinkat_errnos))
  | SVal v => v = 0%Z /\ fs_under (m_fs mo) path = false /\ fs_lookup (m_fs mo) path <> None /\ rmdir = false
      /\ fd_names_path (m_fds mo) path = false /\ mo' = with_fs (fs_remove (m_fs mo) path) mo
  end.
Proof.
  intros path rmdir mo rsp mo' evs [-> H]. split; [reflexivity|].
  destruct (path_has_slash path) eqn:Hps.
  { destruct H. (* [comment removed for export] *) }
  destruct (fs_under (m_fs mo) path) eqn:Hu.
  { destruct H. (* [comment removed for export] *) }
  destruct (fs_lookup (m_fs mo) path) eqn:Hl.
  2:{ destruct H as [-> ->]. exists (SErr ENOENT). split; [apply dec_plain_err; unfold ENOENT; lia|]. split; [reflexivity|]. right; left. auto. }
  destruct rmdir.
  { destruct H as [-> ->]. exists (SErr ENOTDIR). split; [apply dec_plain_err; unfold ENOTDIR; lia|]. split; [reflexivity|].
    right; right; left. repeat split; congruence. }
  destruct H as [(e & HIn & -> & ->) | (Hn & -> & ->)].
  - exists (SErr e). split; [apply dec_plain_err; apply unlinkat_errnos_range'; exact HIn|]. split; [reflexivity|].
    right; right; right. repeat split; try congruence; exact HIn.
  - exists (SVal 0). split; [apply dec_plain_val; [lia|reflexivity]|]. repeat split; try congruence; exact Hn.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma match_scatter_nil : forall dsts,
  Forall (fun d => 0 <= snd d)%Z dsts -> match_scatter dsts [] 0 = Some [].
Proof.
  induction dsts as [|[a l] rest IH]; intros H; [reflexivity|].
  apply Forall_cons_iff in H as [H1 Hr]. cbn [snd] in H1. cbn [match_scatter].
  replace (Z.min 0 l <=? 0)%Z with true by (symmetry; apply Z.leb_le; lia). apply IH. exact Hr.
Qed.

#[using="Type"] Lemma match_scatter_scatterw : forall dsts bs,
  Forall (fun d => 0 <= fst d < 2^64 /\ 0 <= snd d < 2^64)%Z dsts ->
  (Z.of_nat (length bs) <= dsts_total dsts)%Z ->
  match_scatter dsts (scatterw (iovs_of dsts) bs) (Z.of_nat (length bs)) = Some bs.
Proof.
  induction dsts as [|[a l] rest IH]; intros bs Hd Hlen.
  - cbn in Hlen. destruct bs; [reflexivity| cbn in Hlen; lia].
  - apply Forall_cons_iff in Hd as [[Ha Hl] Hr]. cbn [fst snd] in Ha, Hl. cbn [dsts_total] in Hlen.
    pose proof (dsts_total_nonneg rest ltac:(apply Forall_impl with (2 := Hr); intros [? ?] [_ ?]; cbn in *; lia)) as Hrn.
    destruct bs as [|b bs'].
    { cbn [scatterw iovs_of map length Z.of_nat]. apply match_scatter_nil. constructor; [cbn; lia|].
      apply Forall_impl with (2 := Hr). intros [? ?] [_ ?]; cbn in *; lia. }
    cbn [iovs_of map fst snd scatterw match_scatter]. fold (iovs_of rest).
    rewrite word_to_nat_bounded_eq_min. unfold word_to_nat. rewrite unsigned_lit by lia.
    set (n := Nat.min (Z.to_nat l) (length (b :: bs'))).
    assert (Hk : Z.min (Z.of_nat (length (b :: bs'))) l = Z.of_nat n) by (subst n; cbn [length]; lia).
    rewrite Hk.
    destruct (Z.eq_dec l 0) as [->|Hl0].
    + replace n with 0%nat by (subst n; cbn; lia). cbn [firstn skipn]. replace (Z.of_nat 0 <=? 0)%Z with true by reflexivity.
      apply IH; [exact Hr|]. clear Hk; subst n. lia.
    + assert (Hn : (1 <= n <= length (b :: bs'))%nat) by (subst n; cbn [length] in *; lia).
      replace (Z.of_nat n <=? 0)%Z with false by (symmetry; apply Z.leb_gt; clear -Hn; lia).
      destruct (firstn n (b :: bs')) as [|h here'] eqn:Eh.
      { exfalso. assert (length (firstn n (b :: bs')) = n) by (apply firstn_length_le; lia). rewrite Eh in H. cbn in H. lia. }
      rewrite bv_eqb_refl. rewrite <- Eh at 1. rewrite firstn_length_le by lia. rewrite Z.eqb_refl. cbn [andb].
      specialize (IH (skipn n (b :: bs')) Hr). rewrite length_skipn in IH.
      replace (Z.of_nat (length (b :: bs')) - Z.of_nat n)%Z with (Z.of_nat (length (b :: bs') - n)) by lia.
      rewrite IH by lia. rewrite <- Eh. rewrite firstn_skipn. reflexivity.
Qed.

#[using="Type"] Lemma iovs_total_Z_dsts : forall dsts, iovs_total_Z dsts = dsts_total dsts.
Proof. unfold iovs_total_Z. induction dsts as [|[a l] r IH]; [reflexivity|]. cbn [fold_right dsts_total snd]. rewrite IH. reflexivity. Qed.

#[using="Type"] Lemma nstep_dec_readv : forall fd dsts mo rsp mo' evs,
  Forall (fun d => 0 <= fst d < 2^64 /\ 0 <= snd d < 2^64)%Z dsts ->
  (dsts_total dsts <= 2^64 - 4096)%Z ->
  nstep (NReadv fd dsts) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_readv dsts rsp = Some a /\
  match a with
  | RdErr e => mo' = mo /\
      ((e = EBADF /\ (fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
                      \/ (exists p off, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFileW p off))
                      \/ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdNull))   (* [comment removed for export] *)
       \/ (e = EISDIR /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir))
  | RdData bs => exists p off data,
      fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) /\
      fs_lookup (m_fs mo) p = Some data /\
      bs = file_read data off (Z_to_bv 64 (dsts_total dsts)) /\
      mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
  end.
Proof.
  intros fd dsts mo rsp mo' evs Hd Htot [-> H]. split; [reflexivity|].
  pose proof (dsts_total_nonneg dsts ltac:(apply Forall_impl with (2 := Hd); intros [? ?] [_ ?]; cbn in *; lia)) as Hnn.
  assert (Htotal : iovs_total (iovs_of dsts) = dsts_total dsts).
  { apply iovs_total_of. apply Forall_impl with (2 := Hd). intros [a l] [H1 H2]; cbn in *. lia. }
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid w|[|] [|]| ]|] eqn:Hlk; try contradiction.
  - destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|contradiction]. cbv zeta in H. rewrite Htotal in H. destruct H as [-> ->].
    set (bs := file_read data off (Z_to_bv 64 (dsts_total dsts))).
    assert (Hl : (Z.of_nat (length bs) <= dsts_total dsts)%Z).
    { subst bs. rewrite file_read_unguarded, length_firstn. unfold word_to_nat. rewrite unsigned_lit by lia. lia. }
    exists (RdData bs). split.
    + unfold dec_readv. cbn [core]. unfold len_word. rewrite errno_of_lit by lia. rewrite unsigned_lit by lia.
      rewrite iovs_total_Z_dsts. replace (Z.of_nat (length bs) <=? dsts_total dsts)%Z with true by (symmetry; apply Z.leb_le; lia).
      rewrite (match_scatter_scatterw dsts bs Hd Hl). reflexivity.
    + exists p, off, data. auto.
  - destruct H as [-> ->]. exists (RdErr EBADF). split; [|split; [reflexivity| left; split; [reflexivity| right; left; eauto]]].
    unfold dec_readv, efferr, eff0. cbn [core]. rewrite errno_of_errno_ret by (unfold EBADF; lia). reflexivity.
  - destruct H as [-> ->]. exists (RdErr EISDIR). split; [|split; [reflexivity| right; auto]].
    unfold dec_readv, efferr, eff0. cbn [core]. rewrite errno_of_errno_ret by (unfold EISDIR; lia). reflexivity.
  - destruct H as [-> ->]. exists (RdErr EBADF). split; [|split; [reflexivity| left; split; [reflexivity| right; right; reflexivity]]].
    unfold dec_readv, efferr, eff0. cbn [core]. rewrite errno_of_errno_ret by (unfold EBADF; lia). reflexivity.
  - destruct H as [-> ->]. exists (RdErr EBADF). split; [|split; [reflexivity| left; auto]].
    unfold dec_readv, efferr, eff0. cbn [core]. rewrite errno_of_errno_ret by (unfold EBADF; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma m_vmmaps_mremap_model_next : forall m o on d nn,
  m_vmmaps (mremap_model_next m o on d nn) = mremap_maps_next (m_vmmaps m) o d nn.
Proof. intros. unfold mremap_model_next, vm_resize_backing, with_vm_backing. cbn. reflexivity. Qed.

#[using="Type"] Lemma mremap_errnos_In : forall e, In e mremap_errnos -> e = ENOMEM.
Proof. intros e H. cbn in H. destruct H as [<-|[]]. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dec_mremap_err : forall old oldlen newlen avoid_same avoid e,
  e = ENOMEM -> dec_mremap old oldlen newlen avoid_same avoid (efferr e) = Some (MrErr e).
Proof.
  intros old oldlen newlen avoid_same avoid e ->. unfold dec_mremap, efferr, eff0. cbv beta iota zeta.
  rewrite mm_errno_of_enomem. reflexivity.
Qed.

#[using="Type"] Lemma dec_mremap_same : forall old oldlen newlen avoid_same avoid,
  (0 <= old <= 2^64 - 4096)%Z -> mmap_len oldlen = mmap_len newlen ->
  dec_mremap old oldlen newlen avoid_same avoid (eff0 (Z_to_bv 64 old)) = Some MrSame.
Proof.
  intros old oldlen newlen avoid_same avoid Ho Heq. unfold dec_mremap, eff0. cbv beta iota zeta.
  rewrite mm_errno_of_lit by lia. rewrite bv_eqb_refl, (proj2 (Z.eqb_eq _ _) Heq). reflexivity.
Qed.

#[using="Type"] Lemma dec_mremap_shrink : forall old oldlen newlen avoid_same avoid,
  let on := mmap_len oldlen in let nn := mmap_len newlen in
  (0 <= old <= 2^64 - 4096)%Z -> (nn < on)%Z ->
  dec_mremap old oldlen newlen avoid_same avoid
    (mkEffectU (Z_to_bv 64 old) [] [] [(Z_to_bv 64 (old + nn), Z_to_bv 64 (on - nn))] [] []) = Some MrSame.
Proof.
  intros old oldlen newlen avoid_same avoid on nn Ho Hlt. unfold dec_mremap. cbv beta iota zeta. fold on nn.
  rewrite mm_errno_of_lit by lia. rewrite bv_eqb_refl, (proj2 (Z.ltb_lt _ _) Hlt), !bv_eqb_refl. reflexivity.
Qed.

#[using="Type"] Lemma dec_mremap_grow : forall old oldlen newlen avoid_same avoid,
  let on := mmap_len oldlen in let nn := mmap_len newlen in
  (0 <= old)%Z -> (0 < newlen)%Z -> (on < nn)%Z -> (old + nn <= alloc_ceiling)%Z -> avoids old nn avoid_same = true ->
  dec_mremap old oldlen newlen avoid_same avoid
    (mkEffect (Z_to_bv 64 old) [] [(Z_to_bv 64 (old + on), Z_to_bv 64 (nn - on))]) = Some MrSame.
Proof.
  intros old oldlen newlen avoid_same avoid on nn Ho Hnl Hlt Hce Hav. unfold dec_mremap. cbv beta iota zeta. fold on nn.
  pose proof (mmap_len_bound newlen Hnl) as Hb. fold nn in Hb.
  rewrite mm_errno_of_lit by (ceil_bounds; lia).
  rewrite bv_eqb_refl. replace (nn <? on)%Z with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (proj2 (Z.ltb_lt _ _) Hlt), !bv_eqb_refl, (proj2 (Z.leb_le _ _) Hce), Hav. reflexivity.
Qed.

#[using="Type"] Lemma dec_mremap_moved : forall old oldlen newlen avoid_same avoid a,
  let on := mmap_len oldlen in let nn := mmap_len newlen in
  (0 <= old < 2^64)%Z -> (0 < newlen)%Z -> a <> old -> (on < nn)%Z -> mmap_addr_ok newlen avoid a = true ->
  dec_mremap old oldlen newlen avoid_same avoid
    (mkEffectU (Z_to_bv 64 a) [] [(Z_to_bv 64 (a + on), Z_to_bv 64 (nn - on))]
               [(Z_to_bv 64 old, Z_to_bv 64 on)] [mkCopy (Z_to_bv 64 old) (Z_to_bv 64 a) (Z_to_bv 64 on)] []) = Some (MrMoved a).
Proof.
  intros old oldlen newlen avoid_same avoid a on nn Ho Hnl Hne Hlt Hok. unfold dec_mremap. cbv beta iota zeta. fold on nn.
  pose proof (mmap_addr_ok_true _ _ _ Hok) as [(A1 & A2 & A3) A4]. fold nn in A3.
  pose proof (mmap_len_bound newlen Hnl) as Hb. fold nn in Hb.
  assert (Ha2 : (0 <= a <= 2^64 - 4096)%Z) by (ceil_bounds; lia).
  rewrite mm_errno_of_lit by lia.
  replace (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 old)) with false.
  2:{ symmetry. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact Hne. }
  rewrite (proj2 (Z.ltb_lt _ _) Hlt). rewrite (unsigned_lit a) by lia. rewrite !bv_eqb_refl, Hok. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_dec_mremap : forall old oldlen newlen avoid_same avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  let on := mmap_len oldlen in
  let nn := mmap_len newlen in
  let ow := Z_to_bv 64 old in
  (0 <= old)%Z -> (old mod page_size = 0)%Z -> (0 < oldlen)%Z -> (0 < newlen)%Z ->
  (old + on <= alloc_ceiling)%Z -> (nn < 2^64)%Z ->
  alloc_ceiling = page_round_down_Z (alloc_top h) ->     (* [comment removed for export] *)
  m_vm_lazy mo = [] ->
  region_free (vm_reserved h) ow (Z_to_bv 64 on) = true ->
  map_has (vm_maps h) ow (Z_to_bv 64 on) = true ->
  region_free (vm_noaccess h) ow (Z_to_bv 64 on) = true ->
  Forall (covered (vm_reserved h ++ map_remove (vm_maps h) ow)) avoid_same ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMremap old oldlen newlen) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mremap old oldlen newlen avoid_same avoid rsp = Some x /\
  match x with
  | MrErr e => e = ENOMEM /\ on <> nn /\ mo' = mo
  | MrSame =>
         (on = nn /\ mo' = mo)
      \/ ((nn < on)%Z /\ m_vmmaps mo' = mremap_maps_next h ow ow (Z_to_bv 64 nn))
      \/ ((on < nn)%Z /\ (old + nn <= alloc_ceiling)%Z
          /\ region_free (vm_reserved h ++ map_remove (vm_maps h) ow) ow (Z_to_bv 64 nn) = true
          /\ m_vmmaps mo' = mremap_maps_next h ow ow (Z_to_bv 64 nn))
  | MrMoved a =>
      (on < nn)%Z /\ mmap_addr_ok newlen avoid a = true /\ a <> old
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 nn) = true
      /\ m_vmmaps mo' = mremap_maps_next h ow (Z_to_bv 64 a) (Z_to_bv 64 nn)
  end.
Proof.
  intros old oldlen newlen avoid_same avoid mo rsp mo' evs h on nn ow Ho Hal Hol Hnl Hce Hnw Htop Hlazy Hrf Hhas Hna Hcs Hcv H.
  pose proof (mmap_len_bound oldlen Hol) as Hbo. pose proof (mmap_len_bound newlen Hnl) as Hbn.
  assert (Hctop : (alloc_ceiling <= alloc_top h)%Z).
  { rewrite Htop. unfold page_round_down_Z, page_size.
    pose proof (Z.div_mod (alloc_top h) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (alloc_top h) 4096 ltac:(lia)). lia. }
  assert (Hdown : forall x, (x mod 4096 = 0)%Z -> (x <= alloc_top h)%Z -> (x <= alloc_ceiling)%Z).
  { intros x Hx Hle. rewrite Htop. apply page_round_down_Z_ge_aligned; assumption. }
  assert (Hon_al : (on mod 4096 = 0)%Z /\ (nn mod 4096 = 0)%Z).
  { unfold on, nn, mmap_len, page_round_up_Z, page_size. rewrite !Z_mod_mult. auto. }
  assert (Hold : (old <= 2^64 - 4096)%Z) by (ceil_bounds; unfold mmap_len, page_round_up_Z, page_size in *; lia).
  assert (Holr : (oldlen < 2^64)%Z) by (ceil_bounds; lia).
  assert (Hnlr : (newlen < 2^64)%Z) by lia.
  pose proof (nstep_mm_vm_only (NMremap old oldlen newlen) mo rsp mo' evs I H) as (Hv & -> & _).
  split; [reflexivity|]. split; [exact Hv|].
  destruct H as [_ [H _]]. cbn [node_input] in H. rewrite syscall_spec_216 in H by reflexivity.
  cbn [in_arg in_args pure_input nth] in H.
  apply (proj1 (mremap_exact_outcome ow (Z_to_bv 64 oldlen) (Z_to_bv 64 newlen) _ mo _
           ltac:(subst ow; rewrite unsigned_lit by lia; exact Hal)
           ltac:(rewrite w_is0_lit by lia; apply Z.eqb_neq; lia)
           ltac:(rewrite w_is0_lit by lia; apply Z.eqb_neq; lia)
           ltac:(subst ow; rewrite !unsigned_lit by lia; fold (mmap_len oldlen); fold on; fold h; lia)
           ltac:(rewrite unsigned_lit by lia; unfold two_pow_64; exact Hnw)
           Hlazy
           ltac:(rewrite unsigned_lit by lia; exact Hrf)
           ltac:(rewrite unsigned_lit by lia; exact Hhas)
           ltac:(rewrite unsigned_lit by lia; exact Hna))) in H.
  rewrite !(unsigned_lit oldlen), !(unsigned_lit newlen) in H by lia.
  fold (mmap_len oldlen) (mmap_len newlen) in H. fold on nn h in H.
  assert (Eow : bv_unsigned ow = old) by (subst ow; apply unsigned_lit; lia).
  destruct H as [[Heq HO] | [(Hne & e & He & HO) | [[Hlt HO] | [(Hlt & Hg & HO) | (dst & Hlt & Hfr & HO)]]]];
    apply Ok_inj in HO as (-> & -> & _).
  - (* [comment removed for export] *) exists MrSame. split; [|left; auto]. subst ow. apply dec_mremap_same; [lia|exact Heq].
  - (* [comment removed for export] *) apply mremap_errnos_In in He. subst e. exists (MrErr ENOMEM). split; [|auto].
    apply dec_mremap_err. unfold ENOMEM; lia.
  - (* [comment removed for export] *) exists MrSame. split.
    + subst ow. rewrite lit_add_lit. apply dec_mremap_shrink; [lia|exact Hlt].
    + right; left. split; [exact Hlt|]. apply m_vmmaps_mremap_model_next.
  - (* [comment removed for export] *)
    assert (Hrf2 : region_free (vm_reserved h ++ map_remove (vm_maps h) ow) ow (Z_to_bv 64 nn) = true).
    { unfold mremap_inplace_grow_b in Hg. fold h in Hg. apply andb_prop in Hg as [Hg _]. apply andb_prop in Hg as [_ Hg]. exact Hg. }
    assert (Hce2 : (old + nn <= alloc_ceiling)%Z).
    { unfold mremap_inplace_grow_b in Hg. apply andb_prop in Hg as [Hg _]. apply andb_prop in Hg as [Hg _].
      rewrite Eow in Hg. apply Z.leb_le in Hg. apply Hdown; [|exact Hg].
      unfold page_size in Hal. rewrite Z.add_mod, Hal, (proj2 Hon_al) by lia. reflexivity. }
    assert (Hav : avoids old nn avoid_same = true).
    { rewrite <- Eow. rewrite <- (unsigned_lit nn) by lia. apply (avoids_of_region_free _ _ _ _ Hrf2 Hcs). }
    exists MrSame. split.
    + subst ow. rewrite lit_add_lit. apply dec_mremap_grow; assumption.
    + right; right. split; [exact Hlt|]. split; [exact Hce2|]. split; [exact Hrf2|]. apply m_vmmaps_mremap_model_next.
  - (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 dst) as Hd. unfold bv_modulus in Hd. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hd.
    unfold mremap_fresh_b in Hfr. fold h in Hfr.
    apply andb_prop in Hfr as [Hfr A7]. apply andb_prop in Hfr as [Hfr A5].
    apply andb_prop in Hfr as [Hfr A4]. apply andb_prop in Hfr as [Hfr A3]. apply andb_prop in Hfr as [A1 A2].
    apply Z.eqb_eq in A2. apply Z.ltb_lt in A3. apply Z.leb_le in A4.
    assert (Hne : bv_unsigned dst <> old).
    { intros E. apply negb_true_iff in A1. unfold bv_eqb in A1. apply Z.eqb_neq in A1. rewrite Eow in A1. exact (A1 E). }
    assert (A4' : (bv_unsigned dst + nn <= alloc_ceiling)%Z).
    { apply Hdown; [|exact A4]. unfold page_size in A2. rewrite Z.add_mod, A2, (proj2 Hon_al) by lia. reflexivity. }
    assert (Hok : mmap_addr_ok newlen avoid (bv_unsigned dst) = true).
    { unfold mmap_addr_ok. fold nn. rewrite (proj2 (Z.eqb_eq _ _) A2), (proj2 (Z.ltb_lt _ _) A3), (proj2 (Z.leb_le _ _) A4'). cbn [andb].
      rewrite <- (unsigned_lit nn) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact A5|exact Hcv]. }
    set (a := bv_unsigned dst) in *.
    assert (Edst : dst = Z_to_bv 64 a) by (subst a; symmetry; apply Z_to_bv_bv_unsigned).
    clearbody a. subst dst.
    exists (MrMoved a). split.
    + subst ow. rewrite lit_add_lit.
      apply dec_mremap_moved; [lia|exact Hnl|exact Hne|exact Hlt|exact Hok].
    + split; [exact Hlt|]. split; [exact Hok|]. split; [exact Hne|].
      split; [exact A5|]. apply m_vmmaps_mremap_model_next.
Qed.

End WithCeil.
