(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import PropExec MState Mem ITree Nodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithCeiling.
Context {CE : Ceiling}.

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

Inductive sret : Type := SErr (e : Z) | SVal (v : Z).

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
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
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

Definition dec_writev (total : Z) (rsp : resp) : option Z :=
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      if ((total =? 0)%Z && (bv_unsigned r =? 0)%Z)
         || ((1 <=? bv_unsigned r)%Z && (bv_unsigned r <=? total)%Z)
      then Some (bv_unsigned r) else None
  | _ => None
  end.

Lemma dec_writev_Some : forall total rsp k, dec_writev total rsp = Some k ->
  rsp = eff0 (Z_to_bv 64 k) /\ ((total = 0 /\ k = 0) \/ (1 <= k <= total))%Z /\ (0 <= k < 2^64)%Z.
Proof.
  intros total [r ws zs us cs ci] k H. unfold dec_writev in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  destruct (Z.eqb_spec total 0); destruct (Z.eqb_spec (bv_unsigned r) 0);
  destruct (Z.leb_spec0 1 (bv_unsigned r)); destruct (Z.leb_spec0 (bv_unsigned r) total); cbn [andb orb] in H;
  try discriminate; inversion H; subst; unfold eff0; rewrite Z_to_bv_bv_unsigned; (split; [reflexivity| lia]).
Qed.

Definition dec_open : resp -> option sret := dec_plain (fun v => (3 <=? v)%Z && (v <=? 4096)%Z).

Definition dec_close : resp -> option sret := dec_plain (fun v => (v =? 0)%Z).

Definition dec_ioctl : resp -> option sret := dec_plain (fun _ => false).

Definition dec_set_tid (rsp : resp) : option Z :=
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      if (0 <? bv_unsigned r)%Z && (bv_unsigned r <? PID_MAX_ENVELOPE)%Z then Some (bv_unsigned r) else None
  | _ => None
  end.

Definition dec_exit (rsp : resp) : option Empty_set := None.

Lemma dec_set_tid_Some : forall rsp t, dec_set_tid rsp = Some t ->
  rsp = eff0 (Z_to_bv 64 t) /\ (0 < t < PID_MAX_ENVELOPE)%Z.
Proof.
  intros [r ws zs us cs ci] t H. unfold dec_set_tid in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (Z.ltb_spec0 0 (bv_unsigned r)); [|discriminate].
  destruct (Z.ltb_spec0 (bv_unsigned r) PID_MAX_ENVELOPE); [|discriminate]. inversion H; subst.
  unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

Definition dec_brk0 (rsp : resp) : option Z :=
  match rsp with mkEffectU r [] [] [] [] [] => Some (bv_unsigned r) | _ => None end.

Lemma dec_brk0_Some : forall rsp b, dec_brk0 rsp = Some b -> rsp = eff0 (Z_to_bv 64 b) /\ (0 <= b < 2^64)%Z.
Proof.
  intros [r ws zs us cs ci] b H. unfold dec_brk0 in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. inversion H; subst.
  pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

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
      else if (bv_unsigned r =? req)%Z && (req <=? alloc_ceiling)%Z && listNN_eqb zs (zeros_of (brk_new_pages cur req)) then Some BrkGrown
      else None
  | _ => None
  end.

Lemma dec_brk_Some : forall cur req rsp a, dec_brk cur req rsp = Some a ->
  match a with
  | BrkSame => rsp = eff0 (Z_to_bv 64 cur)
  | BrkGrown => rsp = mkEffect (Z_to_bv 64 req) [] (zeros_of (brk_new_pages cur req)) /\ (req <= alloc_ceiling)%Z
  end.
Proof.
  intros cur req [r ws zs us cs ci] a H. unfold dec_brk in H.
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  destruct (Z.eqb_spec (bv_unsigned r) cur).
  - destruct zs.
    + cbn [andb] in H. inversion H; subst. unfold eff0. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
      destruct (Z.leb_spec req alloc_ceiling); [|discriminate]. cbn [andb] in H.
      destruct (listNN_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listNN_eqb_eq in E.
      rewrite <- E, Z_to_bv_bv_unsigned. split; [reflexivity| assumption].
  - cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
    destruct (Z.leb_spec req alloc_ceiling); [|discriminate]. cbn [andb] in H.
    destruct (listNN_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listNN_eqb_eq in E.
    rewrite <- E, Z_to_bv_bv_unsigned. split; [reflexivity| assumption].
Qed.

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
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst.
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
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate; destruct cs; try discriminate; destruct ci; try discriminate.
  - destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst. apply errno_of_Some in E as [-> He]. auto.
  - destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

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
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate; destruct cs; try discriminate; destruct ci; try discriminate.
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
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

Lemma length_file_read_le_count : forall data off count,
  (0 <= count < 2^64)%Z -> (Z.of_nat (length (file_read data off (Z_to_bv 64 count))) <= count)%Z.
Proof.
  intros data off count Hc. rewrite file_read_unguarded, firstn_length.
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
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pi pw|rd wr| ]|] eqn:Hlk; try contradiction.
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

Lemma nstep_dec_writev : forall fd bufs mo rsp mo' evs,
  (Z.of_nat (length (concat bufs)) < 2^64)%Z ->
  nstep (NWritev fd bufs) mo rsp mo' evs ->
  mo' = mo /\
  exists k, dec_writev (Z.of_nat (length (concat bufs))) rsp = Some (Z.of_nat k)
    /\ (k <= length (concat bufs))%nat
    /\ (k = 0%nat <-> concat bufs = [])
    /\ evs = map (WriteEv (Z_to_bv 64 fd)) (firstn k (concat bufs)).
Proof.
  intros fd bufs mo rsp mo' evs Hl [-> H]. split; [reflexivity|].
  destruct H as [(Hnil & -> & ->) | (k & Hk & -> & ->)].
  - exists 0%nat. rewrite Hnil. cbn [length Z.of_nat firstn map]. split; [|split; [lia| split; [tauto|reflexivity]]].
    unfold dec_writev, eff0. cbn. reflexivity.
  - exists k. split; [|split; [lia| split; [|reflexivity]]].
    + unfold dec_writev, eff0. rewrite unsigned_lit by lia.
      replace ((1 <=? Z.of_nat k)%Z && (Z.of_nat k <=? Z.of_nat (length (concat bufs)))%Z) with true
        by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
      rewrite orb_true_r. reflexivity.
    + split; [intros ->; exfalso; lia|]. intros E. rewrite E in Hk. cbn in Hk. lia.
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
  destruct (path_eqb (c :: path') dot_path). { apply (Hres FdDir); [left; reflexivity| exact H]. }
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
    - destruct H as [-> _]. destruct Hminv as (_ & _ & _ & _ & _ & _ & _ & _ & MT & _). exact (MT _ E).
    - exact (proj1 H). }
  split.
  - unfold dec_set_tid, eff0. destruct Hr as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. rewrite H1, H2. reflexivity.
  - split; [exact Hr|]. destruct (m_tid mo) as [t0|]; destruct H as [H0 ->]; [left; subst; auto| right; auto].
Qed.

Lemma nstep_exit_none : forall c mo rsp mo' evs, nstep (NExit c) mo rsp mo' evs -> False.
Proof. intros c mo rsp mo' evs H. exact H. Qed.

Lemma m_vmmaps_vm_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. reflexivity. Qed.

Lemma m_vmmaps_forget_vm_ranges : forall rs m, m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|].
  rewrite IH. apply m_vmmaps_vm_forget_range.
Qed.

Lemma m_vmmaps_with_brk_next : forall m req r,
  m_vmmaps (with_brk_next m req r) = brk_model_next (m_vmmaps m) req r.
Proof. intros. unfold with_brk_next. rewrite m_vmmaps_forget_vm_ranges. reflexivity. Qed.

Lemma m_vmmaps_with_mmap_destroyed : forall a n h m, m_vmmaps (with_mmap_destroyed a n h m) = h.
Proof. intros. unfold with_mmap_destroyed. rewrite m_vmmaps_vm_forget_range. reflexivity. Qed.

Lemma m_vmmaps_with_mmap_backing_plain : forall flags a n m,
  mmap_noreserve_b flags = false -> m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof. intros flags a n m H. unfold with_mmap_backing. rewrite H. reflexivity. Qed.

Lemma nstep_dec_brk0 : forall mo rsp mo' evs,
  nstep (NBrk 0) mo rsp mo' evs ->
  evs = [] /\ dec_brk0 rsp = Some (bv_unsigned (vm_brk (m_vmmaps mo))) /\ vm_only mo mo'
  /\ vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo).
Proof.
  intros mo rsp mo' evs H.
  pose proof (nstep_mm_vm_only (NBrk 0) mo rsp mo' evs I H) as (Hv & -> & _). split; [reflexivity|].
  apply nstep_brk_check in H. destruct rsp as [r ws zs us cs ci]. unfold check_brk in H.
  destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (brk_r_ok mo (Z_to_bv 64 0) r && listNN_eqb zs _ && listNN_eqb us _) eqn:E; [|discriminate].
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  unfold brk_r_ok in E1. change (w_is0 (Z_to_bv 64 0)) with true in E1. cbn [orb] in E1. apply bv_eqb_eq in E1. subst r.
  apply listNN_eqb_eq in E2. apply listNN_eqb_eq in E3.
  unfold brk_zeros, brk_is_grow in E2. change (w_is0 (Z_to_bv 64 0)) with true in E2. cbn [negb andb] in E2. subst zs.
  unfold brk_unmaps, brk_page_range in E3. rewrite Z.ltb_irrefl in E3. destruct (0 <? _)%Z; subst us.
  all: inversion H; subst; split; [reflexivity|]; split; [exact Hv|]; rewrite m_vmmaps_with_brk_next; reflexivity.
Qed.

Lemma nstep_dec_brk : forall req mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_brk h) <= req < 2^64)%Z ->
  alloc_top h = alloc_ceiling ->
  (bv_unsigned (vm_brk h) mod 4096 = 0)%Z -> (req mod 4096 = 0)%Z ->
  nstep (NBrk req) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists a, dec_brk (bv_unsigned (vm_brk h)) req rsp = Some a /\
  match a with
  | BrkSame => vm_brk (m_vmmaps mo') = vm_brk h
  | BrkGrown => vm_brk (m_vmmaps mo') = Z_to_bv 64 req
  end.
Proof.
  intros req mo rsp mo' evs h Hb Hsb Hreq Htop Hbal Hral H.
  pose proof (nstep_mm_vm_only (NBrk req) mo rsp mo' evs I H) as (Hv & -> & _). split; [reflexivity|]. split; [exact Hv|].
  apply nstep_brk_check in H. destruct rsp as [r ws zs us cs ci]. unfold check_brk in H.
  destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (brk_r_ok mo (Z_to_bv 64 req) r && listNN_eqb zs _ && listNN_eqb us _) eqn:E; [|discriminate].
  inversion H; subst; clear H. rewrite m_vmmaps_with_brk_next. cbn [brk_model_next vm_brk].
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply listNN_eqb_eq in E2. apply listNN_eqb_eq in E3. subst zs us.
  fold h in E1 |- *.
  unfold brk_r_ok in E1. fold h in E1. rewrite w_is0_lit in E1 by lia.
  replace (req =? 0)%Z with false in E1 by (symmetry; apply Z.eqb_neq; lia).
  unfold min_brk in E1. rewrite unsigned_lit in E1 by lia.
  replace (req <? bv_unsigned (vm_start_brk h))%Z with false in E1 by (symmetry; apply Z.ltb_ge; lia).
  replace (req <? bv_unsigned (vm_brk h))%Z with false in E1 by (symmetry; apply Z.ltb_ge; lia).
  cbn [orb] in E1. apply andb_prop in E1 as [E1 Hgo].
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
  -
    assert (Hr' : r = vm_brk h). { destruct Hr as [-> | ->]; [subst req; apply Z_to_bv_bv_unsigned| reflexivity]. }
    subst r. exists BrkSame. split; [|reflexivity].
    unfold dec_brk. rewrite Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
  - destruct Hr as [-> | ->].
    + exists BrkGrown. split; [|reflexivity].

      assert (Hceil : (req <= alloc_ceiling)%Z).
      { unfold brk_grow_ok, brk_budget_ok in Hgo. fold h in Hgo. rewrite unsigned_lit in Hgo by lia.
        replace (0 <? bv_unsigned (vm_brk h))%Z with true in Hgo by (symmetry; apply Z.ltb_lt; lia).
        replace (bv_unsigned (vm_brk h) <? req)%Z with true in Hgo by (symmetry; apply Z.ltb_lt; lia).
        cbn [andb] in Hgo.
        assert (Eu : page_round_up_Z req = req).
        { unfold page_round_up_Z, page_size. rewrite (Z.div_mod req 4096) at 1 by lia. rewrite Hral, Z.add_0_r.
          replace (4096 * (req / 4096) + 4096 - 1)%Z with ((req / 4096) * 4096 + 4095)%Z by lia.
          rewrite Z.div_add_l by lia. change (4095 / 4096)%Z with 0%Z. lia. }
        assert (El : page_round_up_Z (bv_unsigned (vm_brk h)) = bv_unsigned (vm_brk h)).
        { set (b := bv_unsigned (vm_brk h)) in *.
          unfold page_round_up_Z, page_size. rewrite (Z.div_mod b 4096) at 1 by lia. rewrite Hbal, Z.add_0_r.
          replace (4096 * (b / 4096) + 4096 - 1)%Z with ((b / 4096) * 4096 + 4095)%Z by lia.
          rewrite Z.div_add_l by lia. change (4095 / 4096)%Z with 0%Z. lia. }
        rewrite Eu, El in Hgo.
        replace (bv_unsigned (vm_brk h) <? req)%Z with true in Hgo by (symmetry; apply Z.ltb_lt; lia).
        apply andb_prop in Hgo as [Hgo _]. apply andb_prop in Hgo as [Hgo _].
        apply Z.leb_le in Hgo. rewrite <- Htop. exact Hgo. }
      unfold dec_brk. rewrite unsigned_lit by lia.
      replace (req =? bv_unsigned (vm_brk h))%Z with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [andb]. rewrite Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) Hceil).
      unfold brk_zeros, brk_is_grow. rewrite w_is0_lit by lia.
      replace (req =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (0 <? bv_unsigned (vm_brk h))%Z with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite unsigned_lit by lia.
      replace (bv_unsigned (vm_brk h) <? req)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [negb andb]. unfold brk_page_range, brk_new_pages, zeros_of, wa.
      destruct (_ <? _)%Z; rewrite (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
    + exists BrkSame. split; [|reflexivity].
      unfold dec_brk. rewrite Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.

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

Lemma errno_ret_in_mmap_when : forall b r, errno_ret_in (mmap_errnos_when b) r = true -> errno_ret_in mmap_errnos r = true.
Proof. intros [] r H; [exact H| cbv in H; discriminate H]. Qed.

Lemma errno_ret_in_mprotect_when : forall b r, errno_ret_in (mprotect_errnos_when b) r = true -> errno_ret_in mprotect_errnos r = true.
Proof. intros [] r H; [exact H| cbv in H; discriminate H]. Qed.

Lemma mmap_errnos_range : forall r e, errno_ret_in mmap_errnos r = true ->
  errno_of r = Some e -> e = ENOMEM.
Proof.
  intros r e H He. apply errno_ret_in_true in H as (e' & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
  rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). inversion He. reflexivity.
Qed.

Lemma nstep_dec_mmap : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  alloc_top h = alloc_ceiling ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ (vm_backing_used mo + mmap_len len <= vm_limit h)%Z
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros len avoid mo rsp mo' evs h Hlen Hlen2 Htop Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) = false) by reflexivity.
  pose proof (nstep_mm_vm_only (NMmap 0 len _ _) mo rsp mo' evs Hnr H) as (Hv & -> & _). split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mmap_check in H; [|exact Hnr]. destruct rsp as [r ws zs us cs ci]. unfold check_mmap in H.
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H.
  change (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true in H. cbn [negb] in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with true in H.
  cbv iota beta in H. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  fold h in H. rewrite Htop in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  match type of H with context [errno_ret_in ?es r] => destruct (errno_ret_in es r) eqn:Herr end.
  - destruct zs; [|discriminate]. inversion H; subst.
    apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    inversion H; subst; clear H.
    apply andb_prop in E as [E E7]. apply andb_prop in E as [E E5].
    apply andb_prop in E as [E E4]. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply listNN_eqb_eq in E7. subst zs.
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned r) = true).
    { unfold mmap_addr_ok. rewrite E1, E2, E3. cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
    exists (MmOk (bv_unsigned r)). split.
    + unfold dec_mmap. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E4|]. split.
      * unfold mmap_noreserve_backed_ok in E5. rewrite Hnr in E5. apply Z.leb_le in E5. exact E5.
      * rewrite m_vmmaps_with_mmap_backing_plain by exact Hnr. reflexivity.
Qed.

Lemma nstep_dec_mmap_none : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  alloc_top h = alloc_ceiling ->
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
  intros len avoid mo rsp mo' evs h Hlen Hlen2 Htop Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) = false) by reflexivity.
  pose proof (nstep_mm_vm_only (NMmap 0 len _ _) mo rsp mo' evs Hnr H) as (Hv & -> & _). split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mmap_check in H; [|exact Hnr]. destruct rsp as [r ws zs us cs ci]. unfold check_mmap in H.
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H.
  change (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true in H. cbn [negb] in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with false in H.
  change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with true in H.
  cbv iota beta in H. destruct ws; [|discriminate]. destruct zs; [|destruct us; discriminate].
  destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
  fold h in H. rewrite Htop in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  match type of H with context [errno_ret_in ?es r] => destruct (errno_ret_in es r) eqn:Herr end.
  - destruct us; [|discriminate]. inversion H; subst.
    apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap_none. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    inversion H; subst; clear H.
    apply andb_prop in E as [E E6]. apply andb_prop in E as [E E4].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply listNN_eqb_eq in E6. subst us.
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned r) = true).
    { unfold mmap_addr_ok. rewrite E1, E2, E3. cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
    exists (MmOk (bv_unsigned r)). split.
    + unfold dec_mmap_none. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E4|].
      rewrite m_vmmaps_with_mmap_backing_plain by exact Hnr. reflexivity.
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
  | RgDone false => mo' = mo /\ munmap_free_ok h a (mmap_len len) = true
  | RgDone true => map_has (vm_maps h) a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMunmap addr len) mo rsp mo' evs I H) as (Hv & -> & _). split; [reflexivity|]. split; [exact Hv|].
  apply nstep_munmap_iff in H. destruct rsp as [r ws zs us cs ci]. unfold check_munmap in H.
  fold a h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H.
  destruct (negb (bv_unsigned a mod page_size =? 0)%Z || w_is0 (Z_to_bv 64 len)).
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_munmap. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  cbv zeta in H. destruct (TASK_SIZE <? _)%Z.
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_munmap. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  destruct (map_has (vm_maps h) a n) eqn:Hhas.
  - destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r && listNN_eqb us [(a, n)]) eqn:E; [|discriminate]. inversion H; subst; clear H.
    apply andb_prop in E as [E1 E2]. apply listNN_eqb_eq in E2. subst us. unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
    exists (RgDone true). split; [|split; [reflexivity| rewrite m_vmmaps_with_mmap_destroyed; reflexivity]].
    unfold dec_munmap. subst a n. rewrite !bv_eqb_refl. reflexivity.
  - destruct (munmap_free_ok h a (mmap_len len)) eqn:Hrf; [|discriminate].
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
      /\ mprotect_budget_ok mo a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMprotect addr len _) mo rsp mo' evs I H) as (Hv & -> & _). split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mprotect_check in H. destruct rsp as [r ws zs us cs ci]. unfold check_mprotect in H.
  fold a h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H.
  change (mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with false in H.
  change (mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with true in H. cbn [negb] in H. cbv iota in H.
  destruct (negb (bv_unsigned a mod page_size =? 0)%Z).
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  destruct (two_pow_64 <=? _)%Z.
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr ENOMEM). split; [|auto].
    unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity. }
  cbv zeta in H.
  destruct (map_contains (vm_noaccess h) a n && map_contains (vm_maps h) a n) eqn:Hc.
  - destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
    destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    match type of H with context [errno_ret_in ?es r] => destruct (errno_ret_in es r) eqn:Herr end.
    + destruct zs; [|discriminate]. inversion H; subst.
      apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
      exists (RgErr ENOMEM). split; [|auto]. unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
    + destruct (mprotect_budget_ok mo a n && w_is0 r && listNN_eqb zs [(a, n)]) eqn:E; [|discriminate]. inversion H; subst; clear H.
      apply andb_prop in E as [E E2]. apply andb_prop in E as [E0 E1]. apply listNN_eqb_eq in E2. subst zs.
      unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
      apply andb_prop in Hc as [Hc1 Hc2].
      exists (RgDone true). split; [| auto].
      unfold dec_mprotect. subst a n. rewrite !bv_eqb_refl. reflexivity.
  - destruct (map_contains (vm_maps h) a n && region_free (vm_noaccess h) a n); [|discriminate].
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r) eqn:E; [|discriminate]. inversion H; subst. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
    exists (RgDone false). split; [reflexivity| reflexivity].
Qed.

End WithCeiling.
