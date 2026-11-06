(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem ITree RelSpec RelSpecX Nodes.
Import ListNotations.
Open Scope bv_scope.

Fixpoint listWW_eqb (l1 l2 : list (word * word)) : bool :=
  match l1, l2 with
  | [], [] => true
  | (a, b) :: r1, (c, d) :: r2 => bv_eqb a c && bv_eqb b d && listWW_eqb r1 r2
  | _, _ => false
  end.

Lemma listWW_eqb_eq : forall l1 l2, listWW_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|[a b] r1 IH]; intros [|[c d] r2]; cbn; try (split; [discriminate|discriminate]); [tauto|].
  rewrite !andb_true_iff, !bv_eqb_eq, IH. split; [intros [[-> ->] ->]; reflexivity| intros H; inversion H; auto].
Qed.

Lemma listWW_eqb_refl : forall l, listWW_eqb l l = true.
Proof. intros. apply listWW_eqb_eq. reflexivity. Qed.

Fixpoint forallb {A} (f : A -> bool) (l : list A) : bool :=
  match l with [] => true | x :: r => f x && forallb f r end.

Lemma forallb_forall : forall {A} (f : A -> bool) l, forallb f l = true <-> (forall x, In x l -> f x = true).
Proof.
  intros A f l. induction l as [|x r IH]; cbn.
  - split; [intros _ ? []|reflexivity].
  - rewrite andb_true_iff, IH. split.
    + intros [H1 H2] y [<-|Hy]; auto.
    + intros H. split; [apply H; auto|]. intros y Hy. apply H. auto.
Qed.

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
  | mkEffectU r [] [] [] [] _ =>
      match errno_of r with
      | Some e => Some (SErr e)
      | None => if ok (bv_unsigned r) then Some (SVal (bv_unsigned r)) else None
      end
  | _ => None
  end.

Lemma dec_plain_Some : forall ok rsp a, dec_plain ok rsp = Some a ->
  match a with
  | SErr e => strip rsp = efferr e /\ (1 <= e <= 4095)%Z
  | SVal v => strip rsp = eff0 (Z_to_bv 64 v) /\ ok v = true /\ (0 <= v <= 2^64 - 4096)%Z
  end.
Proof.
  intros ok [r ws zs us cs ci] a H. unfold dec_plain in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  destruct (errno_of r) as [e|] eqn:E.
  - inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
  - destruct (ok (bv_unsigned r)) eqn:Hok; [|discriminate]. inversion H; subst.
    pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
    unfold errno_of in E. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [discriminate|].
    unfold eff0. rewrite strip_mk. rewrite Z_to_bv_bv_unsigned. repeat split; try reflexivity; try exact Hok; lia.
Qed.

Lemma dec_plain_strip : forall ok rsp, dec_plain ok (strip rsp) = dec_plain ok rsp.
Proof. intros ok [r ws zs us cs ci]. reflexivity. Qed.

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
  | mkEffectU r [] [] [] [] _ =>
      match errno_of r with
      | Some e => Some (RdErr e)
      | None => if (bv_unsigned r =? 0)%Z then Some (RdData []) else None
      end
  | mkEffectU r [(a, bs)] [] [] [] _ =>
      if bv_eqb a (Z_to_bv 64 buf) && (1 <=? Z.of_nat (length bs))%Z
         && (Z.of_nat (length bs) <=? count)%Z && (bv_unsigned r =? Z.of_nat (length bs))%Z
      then Some (RdData bs) else None
  | _ => None
  end.

Lemma dec_read_strip : forall buf count rsp, dec_read buf count (strip rsp) = dec_read buf count rsp.
Proof. intros buf count [r ws zs us cs ci]. reflexivity. Qed.

Lemma dec_read_Some : forall buf count rsp a, (0 <= count)%Z -> dec_read buf count rsp = Some a ->
  match a with
  | RdErr e => strip rsp = efferr e /\ (1 <= e <= 4095)%Z
  | RdData bs => strip rsp = mkEffect (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) []
                 /\ (Z.of_nat (length bs) <= count)%Z
  end.
Proof.
  intros buf count [r ws zs us cs ci] a Hc H. unfold dec_read in H.
  destruct ws as [|[a0 bs] [|? ?]]; try discriminate.
  - destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct (errno_of r) as [e|] eqn:E.
    + inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
    + destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst. rewrite strip_mk. cbn [delivered_writes length Z.of_nat].
      split; [|lia]. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct (bv_eqb a0 (Z_to_bv 64 buf)) eqn:E1; [|discriminate].
    destruct (Z.leb_spec0 1 (Z.of_nat (length bs))); [|discriminate].
    destruct (Z.leb_spec0 (Z.of_nat (length bs)) count); [|discriminate].
    destruct (Z.eqb_spec (bv_unsigned r) (Z.of_nat (length bs))); [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. subst a0.
    destruct bs as [|b bs']; [cbn in *; lia|]. rewrite strip_mk. cbn [delivered_writes]. split; [|lia].
    f_equal. apply bv_eq. rewrite unsigned_lit. { assumption. }
    pose proof (bv_unsigned_in_range 64 r). unfold bv_modulus in *. lia.
Qed.

Definition dec_writev (total : Z) (rsp : resp) : option Z :=
  match rsp with
  | mkEffectU r [] [] [] [] _ =>
      let k := bv_unsigned r in
      if ((total =? 0)%Z && (k =? 0)%Z) || ((1 <=? k)%Z && (k <=? total)%Z) then Some k else None
  | _ => None
  end.

Lemma dec_writev_strip : forall total rsp, dec_writev total (strip rsp) = dec_writev total rsp.
Proof. intros total [r ws zs us cs ci]. reflexivity. Qed.

Lemma dec_writev_Some : forall total rsp k, dec_writev total rsp = Some k ->
  strip rsp = eff0 (Z_to_bv 64 k) /\ (0 <= k <= total)%Z /\ (k = 0 <-> total = 0)%Z /\ (k < 2^64)%Z.
Proof.
  intros total [r ws zs us cs ci] k H. unfold dec_writev in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  cbv zeta in H. pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R. cbn in R.
  destruct (Z.eqb_spec total 0); destruct (Z.eqb_spec (bv_unsigned r) 0);
    destruct (Z.leb_spec0 1 (bv_unsigned r)); destruct (Z.leb_spec0 (bv_unsigned r) total); cbn [andb orb] in H;
    try discriminate; inversion H; subst; unfold eff0; rewrite strip_mk; rewrite Z_to_bv_bv_unsigned; repeat split; try reflexivity; lia.
Qed.

Definition dec_open : resp -> option sret := dec_plain (fun v => (3 <=? v)%Z && (v <=? 4096)%Z).

Definition dec_close : resp -> option sret := dec_plain (fun v => (v =? 0)%Z).

Definition dec_ioctl : resp -> option sret := dec_plain (fun _ => false).

Definition dec_set_tid (rsp : resp) : option Z :=
  match rsp with
  | mkEffectU r [] [] [] [] _ =>
      if (0 <? bv_unsigned r)%Z && (bv_unsigned r <? PID_MAX_ENVELOPE)%Z then Some (bv_unsigned r) else None
  | _ => None
  end.

Definition dec_exit (rsp : resp) : option Empty_set := None.

Lemma dec_set_tid_Some : forall rsp t, dec_set_tid rsp = Some t ->
  strip rsp = eff0 (Z_to_bv 64 t) /\ (0 < t < PID_MAX_ENVELOPE)%Z.
Proof.
  intros [r ws zs us cs ci] t H. unfold dec_set_tid in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  destruct (Z.ltb_spec0 0 (bv_unsigned r)); [|discriminate].
  destruct (Z.ltb_spec0 (bv_unsigned r) PID_MAX_ENVELOPE); [|discriminate]. inversion H; subst.
  unfold eff0. rewrite strip_mk. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

Definition dec_brk0 (rsp : resp) : option Z :=
  match rsp with mkEffectU r [] [] [] [] _ => Some (bv_unsigned r) | _ => None end.

Lemma dec_brk0_Some : forall rsp b, dec_brk0 rsp = Some b -> strip rsp = eff0 (Z_to_bv 64 b) /\ (0 <= b < 2^64)%Z.
Proof.
  intros [r ws zs us cs ci] b H. unfold dec_brk0 in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  inversion H; subst. pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  unfold eff0. rewrite strip_mk. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

Definition brk_new_pages (cur req : Z) : option (Z * Z) :=
  let lo := page_round_up_Z cur in let hi := page_round_up_Z req in
  if (lo <? hi)%Z then Some (lo, hi - lo)%Z else None.

Definition zeros_of (p : option (Z * Z)) : list (word * word) :=
  match p with Some (lo, n) => [(wa lo, Z_to_bv 64 n)] | None => [] end.

Inductive brk_ans : Type := BrkGrown | BrkSame.

Definition dec_brk (cur req : Z) (rsp : resp) : option brk_ans :=
  match rsp with
  | mkEffectU r [] zs [] [] _ =>
      if (bv_unsigned r =? cur)%Z && match zs with [] => true | _ => false end then Some BrkSame
      else if (bv_unsigned r =? req)%Z && listWW_eqb zs (zeros_of (brk_new_pages cur req)) then Some BrkGrown
      else None
  | _ => None
  end.

Lemma dec_brk_Some : forall cur req rsp a, dec_brk cur req rsp = Some a ->
  match a with
  | BrkSame => strip rsp = eff0 (Z_to_bv 64 cur)
  | BrkGrown => strip rsp = mkEffect (Z_to_bv 64 req) [] (zeros_of (brk_new_pages cur req))
  end.
Proof.
  intros cur req [r ws zs us cs ci] a H. unfold dec_brk in H.
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate]. rewrite ?strip_mk.
  destruct (Z.eqb_spec (bv_unsigned r) cur).
  - destruct zs.
    + cbn [andb] in H. inversion H; subst. unfold eff0. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
      destruct (listWW_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listWW_eqb_eq in E.
      rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
    destruct (listWW_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listWW_eqb_eq in E.
    rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Inductive mmap_ans : Type := MmErr (e : Z) | MmOk (a : Z).

Definition avoids (a n : Z) (avoid : list (Z * Z)) : bool :=
  forallb (fun iv => (a + n <=? fst iv)%Z || (snd iv <=? a)%Z) avoid.

Definition mmap_len (len : Z) : Z := page_round_up_Z len.

Definition mmap_addr_ok (len : Z) (avoid : list (Z * Z)) (a : Z) : bool :=
  (a mod page_size =? 0)%Z && (0 <? a)%Z && (a + mmap_len len <=? alloc_ceiling_max)%Z && avoids a (mmap_len len) avoid.

Definition dec_mmap (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] _ => match errno_of r with Some e => Some (MmErr e) | None => None end
  | mkEffectU r [] [(a, n)] [] [] _ =>
      if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
      then Some (MmOk (bv_unsigned r)) else None
  | _ => None
  end.

Definition dec_mmap_none (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] _ => match errno_of r with Some e => Some (MmErr e) | None => None end
  | mkEffectU r [] [] [(a, n)] [] _ =>
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
  (a mod page_size = 0 /\ 0 < a /\ a + mmap_len len <= alloc_ceiling_max)%Z /\ avoids a (mmap_len len) avoid = true.
Proof.
  intros len avoid a H. unfold mmap_addr_ok in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma dec_mmap_Some : forall len avoid rsp x, dec_mmap len avoid rsp = Some x ->
  match x with
  | MmErr e => strip rsp = efferr e /\ (1 <= e <= 4095)%Z
  | MmOk a => strip rsp = mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] /\ mmap_addr_ok len avoid a = true
  end.
Proof.
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap in H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst.
    apply errno_of_Some in E as [-> He]. rewrite ?strip_mk. auto.
  - destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite ?strip_mk. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

Lemma dec_mmap_none_Some : forall len avoid rsp x, dec_mmap_none len avoid rsp = Some x ->
  match x with
  | MmErr e => strip rsp = efferr e /\ (1 <= e <= 4095)%Z
  | MmOk a => strip rsp = mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] /\ mmap_addr_ok len avoid a = true
  end.
Proof.
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap_none in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct cs; [|discriminate]. destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst. apply errno_of_Some in E as [-> He]. rewrite ?strip_mk. auto.
  - destruct cs; [|discriminate]. destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite ?strip_mk. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

Inductive range_ans : Type := RgErr (e : Z) | RgDone (changed : bool).

Definition dec_munmap (addr len : Z) (rsp : resp) : option range_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] _ =>
      match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | mkEffectU r [] [] [(a, n)] [] _ =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end.

Definition dec_mprotect (addr len : Z) (rsp : resp) : option range_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] _ =>
      match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | mkEffectU r [] [(a, n)] [] [] _ =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end.

Lemma dec_munmap_Some : forall addr len rsp x, dec_munmap addr len rsp = Some x ->
  match x with
  | RgErr e => strip rsp = efferr e /\ (1 <= e <= 4095)%Z
  | RgDone false => strip rsp = eff0 (Z_to_bv 64 0)
  | RgDone true => strip rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] []
  end.
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_munmap in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate; rewrite ?strip_mk.
  - destruct cs; [|discriminate]. destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct cs; [|discriminate]. destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

Lemma dec_mprotect_Some : forall addr len rsp x, dec_mprotect addr len rsp = Some x ->
  match x with
  | RgErr e => strip rsp = efferr e /\ (1 <= e <= 4095)%Z
  | RgDone false => strip rsp = eff0 (Z_to_bv 64 0)
  | RgDone true => strip rsp = mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))]
  end.
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_mprotect in H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate; rewrite ?strip_mk.
  - destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

Inductive mremap_ans : Type := MrErr (e : Z) | MrSame | MrMoved (dst : Z).

Definition dec_mremap (old old_len new_len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mremap_ans :=
  let on := mmap_len old_len in let nn := mmap_len new_len in
  let OLD := Z_to_bv 64 old in let ON := Z_to_bv 64 on in let NN := Z_to_bv 64 nn in
  match rsp with
  | mkEffectU r [] zs us cs _ =>
      match errno_of r with
      | Some e => match zs, us, cs with [], [], [] => Some (MrErr e) | _, _, _ => None end
      | None =>
          if bv_eqb r OLD then
            (if listWW_eqb zs (eff_zeros (mremap_inplace_effect OLD ON NN on nn))
                && listWW_eqb us (eff_unmaps (mremap_inplace_effect OLD ON NN on nn))
                && match cs with [] => true | _ => false end
                && ((nn <=? on)%Z || ((old + nn <=? alloc_ceiling_max)%Z && avoids old nn avoid))
             then Some MrSame else None)
          else
            if listWW_eqb zs (mremap_tail r ON on nn)
               && listWW_eqb us [(OLD, ON)]
               && match cs with
                  | [mkCopy s d n] => bv_eqb s OLD && bv_eqb d r && bv_eqb n ON
                  | _ => false end
               && (bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
               && (bv_unsigned r + nn <=? alloc_ceiling_max)%Z && (on <? nn)%Z
               && avoids (bv_unsigned r) nn avoid
            then Some (MrMoved (bv_unsigned r)) else None
      end
  | _ => None
  end.

Lemma dec_mremap_Some : forall old old_len new_len avoid rsp x, dec_mremap old old_len new_len avoid rsp = Some x ->
  let on := mmap_len old_len in let nn := mmap_len new_len in let OLD := Z_to_bv 64 old in
  match x with
  | MrErr e => strip rsp = efferr e /\ (1 <= e <= 4095)%Z
  | MrSame => strip rsp = mremap_inplace_effect OLD (Z_to_bv 64 on) (Z_to_bv 64 nn) on nn
      /\ (nn <= on \/ (old + nn <= alloc_ceiling_max /\ avoids old nn avoid = true))%Z
  | MrMoved dst => strip rsp = mremap_move_effect OLD (Z_to_bv 64 on) (Z_to_bv 64 dst) on nn
      /\ (dst mod page_size = 0 /\ 0 < dst /\ dst + nn <= alloc_ceiling_max /\ on < nn)%Z /\ avoids dst nn avoid = true
  end.
Proof.
  intros old old_len new_len avoid [r ws zs us cs ci] x H. cbv zeta. unfold dec_mremap in H. cbv zeta in H.
  destruct ws; [|discriminate].
  destruct (errno_of r) as [e|] eqn:E.
  - destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
    inversion H; subst. apply errno_of_Some in E as [-> He]. rewrite strip_mk. auto.
  - destruct (bv_eqb r (Z_to_bv 64 old)) eqn:Er.
    + apply bv_eqb_eq in Er. subst r.
      destruct (listWW_eqb zs _) eqn:E1; [|discriminate]. destruct (listWW_eqb us _) eqn:E2; [|discriminate].
      destruct cs; [|discriminate].
      destruct ((mmap_len new_len <=? mmap_len old_len)%Z || ((old + mmap_len new_len <=? alloc_ceiling_max)%Z && avoids old (mmap_len new_len) avoid)) eqn:E3; [|discriminate].
      cbn [andb] in H. inversion H; subst.
      apply listWW_eqb_eq in E1. apply listWW_eqb_eq in E2. subst. rewrite strip_mk. split.
      * unfold mremap_inplace_effect. destruct (_ <? _)%Z; reflexivity.
      * apply orb_prop in E3 as [E3|E3]; [left; apply Z.leb_le; exact E3|right].
        apply andb_prop in E3 as [E3 E4]. apply Z.leb_le in E3. auto.
    + destruct (listWW_eqb zs _) eqn:E1; [|discriminate]. destruct (listWW_eqb us _) eqn:E2; [|discriminate].
      destruct cs as [|[s0 d n] [|? ?]]; try discriminate.
      destruct (bv_eqb s0 _) eqn:E3; [|discriminate]. destruct (bv_eqb d r) eqn:E4; [|discriminate]. destruct (bv_eqb n _) eqn:E5; [|discriminate].
      destruct (Z.eqb_spec (bv_unsigned r mod page_size) 0); [|discriminate]. destruct (Z.ltb_spec0 0 (bv_unsigned r)); [|discriminate].
      destruct (Z.leb_spec0 (bv_unsigned r + mmap_len new_len) alloc_ceiling_max); [|discriminate].
      destruct (Z.ltb_spec0 (mmap_len old_len) (mmap_len new_len)); [|discriminate].
      destruct (avoids (bv_unsigned r) (mmap_len new_len) avoid) eqn:E6; [|discriminate].
      cbn [andb] in H. inversion H; subst.
      apply listWW_eqb_eq in E1. apply listWW_eqb_eq in E2. apply bv_eqb_eq in E3. apply bv_eqb_eq in E4. apply bv_eqb_eq in E5. subst.
      rewrite strip_mk. rewrite Z_to_bv_bv_unsigned. unfold mremap_move_effect. split; [reflexivity|]. repeat split; assumption.
Qed.

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
       \/ (e = EISDIR /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir)
       \/ (e = EBADF /\ exists p off, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFileW p off)))
  | RdData bs => exists p off data,
      fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) /\
      fs_lookup (m_fs mo) p = Some data /\
      bs = file_read data off (Z_to_bv 64 count) /\
      mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
  end.
Proof.
  intros fd buf count mo rsp mo' evs Hc [-> H]. split; [reflexivity|]. rewrite <- dec_read_strip.
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid wr|dnr dnw| ]|] eqn:Hlk; try contradiction.
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
  - destruct H as [-> ->]. exists (RdErr EBADF). split; [reflexivity|]. split; [reflexivity|]. right; right. split; [reflexivity|]. eexists _, _; reflexivity.
  - destruct H as [-> ->]. exists (RdErr EISDIR). split; [reflexivity| auto].
  - destruct H as [-> ->]. exists (RdErr EBADF). split; [reflexivity| auto].
Qed.

Lemma nstep_dec_writev : forall fd bufs mo rsp mo' evs,
  (Z.of_nat (length (concat bufs)) < 2^64)%Z ->
  nstep (NWritev fd bufs) mo rsp mo' evs ->
  mo' = mo /\
  exists k, dec_writev (Z.of_nat (length (concat bufs))) rsp = Some k /\
    (0 <= k <= Z.of_nat (length (concat bufs)))%Z /\
    (k = 0 <-> length (concat bufs) = 0%nat)%Z /\
    evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) (concat bufs)).
Proof.
  intros fd bufs mo rsp mo' evs Hl [-> H]. split; [reflexivity|]. rewrite <- dec_writev_strip.
  destruct H as [(E & -> & ->)|(k & Hk & -> & ->)].
  - exists 0%Z. rewrite E. cbn. repeat split; auto; lia.
  - exists (Z.of_nat k). unfold dec_writev, eff0. cbv zeta. rewrite unsigned_lit by lia.
    replace (1 <=? Z.of_nat k)%Z with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.of_nat k <=? Z.of_nat (length (concat bufs)))%Z with true by (symmetry; apply Z.leb_le; lia).
    rewrite orb_true_r. split; [reflexivity|]. split; [lia|]. split; [lia|]. rewrite Nat2Z.id. reflexivity.
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
  intros path mo rsp mo' evs Hminv [-> H]. split; [reflexivity|]. unfold dec_open. rewrite <- dec_plain_strip.
  set (G := fun (r : resp) (m1 : Model) => exists a, dec_plain (fun v => (3 <=? v)%Z && (v <=? 4096)%Z) r = Some a /\
            match a with SErr e => m1 = mo /\ (1 <= e <= 4095)%Z
            | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
                /\ exists ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0)) /\ m1 = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) ent) mo end).
  change (G (strip rsp) mo').
  assert (Herr : forall e, (1 <= e <= 4095)%Z -> G (efferr e) mo).
  { intros e He. exists (SErr e). split; [apply dec_plain_err; exact He| auto]. }
  assert (Hres : forall ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0)) -> open_result mo ent rsp mo' -> G (strip rsp) mo').
  { intros ent Hent [(e & HIn & -> & ->) | (Hlk & -> & ->)].
    - apply (Herr e). apply openat_errnos_range; exact HIn.
    - pose proof (alloc_fd_range mo Hminv Hlk) as Hr.
      exists (SVal (bv_unsigned (alloc_fd (m_fds mo)))). split.
      + rewrite <- (Z_to_bv_bv_unsigned (alloc_fd (m_fds mo))) at 1.
        apply dec_plain_val; [lia|]. apply andb_true_intro; split; apply Z.leb_le; lia.
      + rewrite Z_to_bv_bv_unsigned. split; [reflexivity|]. split; [lia|]. split; [exact Hlk|]. exists ent. auto. }
  destruct (path_max <=? length path)%nat. { destruct H as [-> ->]. apply (Herr ENAMETOOLONG). unfold ENAMETOOLONG; lia. }
  destruct path as [|c path']. { destruct H as [-> ->]. apply (Herr ENOENT). unfold ENOENT; lia. }
  destruct (path_is_dirref (c :: path')). { apply (Hres FdDir); [left; reflexivity| exact H]. }
  destruct (fs_lookup (m_fs mo) (c :: path')).
  - apply (Hres (FdFile (c :: path') (Z_to_bv 64 0))); [right; reflexivity| exact H].
  - destruct H as [-> ->]. apply (Herr ENOENT). unfold ENOENT; lia.
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
  intros fd mo rsp mo' evs (-> & _ & H). split; [reflexivity|]. unfold dec_close. rewrite <- dec_plain_strip.
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) eqn:Hlk; destruct H as [-> ->].
  - exists (SVal 0). split; [apply dec_plain_val; [lia|reflexivity]|]. repeat split; congruence.
  - exists (SErr EBADF). split; [apply dec_plain_err; unfold EBADF; lia|]. auto.
Qed.

Lemma nstep_dec_ioctl : forall fd req mo rsp mo' evs,
  nstep (NIoctl fd req) mo rsp mo' evs ->
  dec_ioctl rsp = Some (SErr ENOTTY) /\ mo' = mo /\ evs = [].
Proof.
  intros fd req mo rsp mo' evs (-> & Hs & ->). split; [|auto]. unfold dec_ioctl. rewrite <- dec_plain_strip, Hs.
  apply dec_plain_err. unfold ENOTTY; lia.
Qed.

Lemma nstep_dec_set_tid : forall mo rsp mo' evs,
  minv mo ->
  nstep NSetTid mo rsp mo' evs ->
  evs = [] /\
  exists t, dec_set_tid rsp = Some t /\ (0 < t < PID_MAX_ENVELOPE)%Z /\
  ((m_tid mo = Some (Z_to_bv 64 t) /\ mo' = mo) \/ (m_tid mo = None /\ mo' = with_tid (Z_to_bv 64 t) mo)).
Proof.
  intros mo rsp mo' evs Hminv (-> & tw & Hs & H). split; [reflexivity|].
  exists (bv_unsigned tw). rewrite Z_to_bv_bv_unsigned.
  assert (Hr : (0 < bv_unsigned tw < PID_MAX_ENVELOPE)%Z).
  { destruct (m_tid mo) as [t0|] eqn:E.
    - destruct H as [-> _]. destruct Hminv as (_ & _ & _ & _ & _ & _ & MT & _). exact (MT _ E).
    - exact (proj1 H). }
  split.
  - destruct rsp as [r ws zs us cs ci]. rewrite strip_mk in Hs. unfold eff0 in Hs. inversion Hs; subst.
    unfold dec_set_tid. destruct Hr as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. rewrite H1, H2. reflexivity.
  - split; [exact Hr|]. destruct (m_tid mo) as [t0|]; destruct H as [H0 ->]; [left; subst; auto| right; auto].
Qed.

Lemma nstep_exit_none : forall c mo rsp mo' evs, nstep (NExit c) mo rsp mo' evs -> False.
Proof. intros c mo rsp mo' evs H. exact H. Qed.

Lemma w_is0_lit : forall z, (0 <= z < 2^64)%Z -> w_is0 (Z_to_bv 64 z) = (z =? 0)%Z.
Proof. intros z Hz. unfold w_is0, bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma brk_zeros_query : forall r b, brk_zeros (Z_to_bv 64 0) r b = [].
Proof. intros. unfold brk_zeros, brk_is_grow. change (w_is0 (Z_to_bv 64 0)) with true. reflexivity. Qed.

Lemma brk_unmaps_same : forall b, brk_unmaps b b = [].
Proof. intros. unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. destruct (0 <? _)%Z; reflexivity. Qed.

Lemma nstep_dec_brk0 : forall mo rsp mo' evs,
  nstep (NBrk 0) mo rsp mo' evs ->
  evs = [] /\ dec_brk0 rsp = Some (bv_unsigned (vm_brk (m_vmmaps mo))) /\ mm_frame mo mo'
  /\ vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo).
Proof.
  intros mo rsp mo' evs H. pose proof H as H0. destruct H as (-> & (r & Hr & Hs & ->) & _). split; [reflexivity|].
  unfold brk_r_ok in Hr. change (w_is0 (Z_to_bv 64 0)) with true in Hr. cbn [orb] in Hr. apply bv_eqb_eq in Hr. subst r.
  rewrite brk_zeros_query, brk_unmaps_same in Hs.
  split; [|split].
  - destruct rsp as [r ws zs us cs ci]. rewrite strip_mk in Hs. inversion Hs; subst. reflexivity.
  - apply mm_frame_with_brk_next.
  - unfold with_brk_next.

    assert (E : forall rs m, m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m).
    { induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH. reflexivity. }
    rewrite E, m_vmmaps_with_vmmaps. reflexivity.
Qed.

Lemma nstep_dec_brk : forall req mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_brk h) <= req < 2^64)%Z ->
  nstep (NBrk req) mo rsp mo' evs ->
  evs = [] /\ mm_frame mo mo' /\
  exists a, dec_brk (bv_unsigned (vm_brk h)) req rsp = Some a /\
  match a with
  | BrkSame => vm_brk (m_vmmaps mo') = vm_brk h
  | BrkGrown => vm_brk (m_vmmaps mo') = Z_to_bv 64 req
  end.
Proof.
  intros req mo rsp mo' evs h Hb Hsb Hreq H. destruct H as (-> & (r & Hr & Hs & ->) & _). split; [reflexivity|].
  split; [apply mm_frame_with_brk_next|].
  assert (E : forall rs m, m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m).
  { induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH. reflexivity. }
  assert (Hbrk' : forall r', vm_brk (m_vmmaps (with_brk_next mo (Z_to_bv 64 req) r')) = r').
  { intros r'. unfold with_brk_next. rewrite E, m_vmmaps_with_vmmaps. reflexivity. }
  rewrite Hbrk'. fold h in Hr, Hs |- *.
  unfold brk_r_ok in Hr. rewrite w_is0_lit in Hr by lia.
  replace (req =? 0)%Z with false in Hr by (symmetry; apply Z.eqb_neq; lia).
  unfold min_brk in Hr. fold h in Hr. rewrite unsigned_lit in Hr by lia.
  replace (req <? bv_unsigned (vm_start_brk h))%Z with false in Hr by (symmetry; apply Z.ltb_ge; lia).
  replace (req <? bv_unsigned (vm_brk h))%Z with false in Hr by (symmetry; apply Z.ltb_ge; lia).
  cbn [orb] in Hr. apply andb_prop in Hr as [Hr _].
  assert (Hr' : r = Z_to_bv 64 req \/ r = vm_brk h).
  { apply orb_prop in Hr as [Hr|Hr]; apply bv_eqb_eq in Hr; auto. }
  assert (Hus : brk_unmaps r (vm_brk h) = []).
  { unfold brk_unmaps, brk_page_range.
    assert (Hle : (page_round_up_Z (bv_unsigned (vm_brk h)) <= page_round_up_Z (bv_unsigned r))%Z).
    { apply page_round_up_Z_mono. destruct Hr' as [-> | ->]; [rewrite unsigned_lit by lia|]; lia. }
    replace (page_round_up_Z (bv_unsigned r) <? page_round_up_Z (bv_unsigned (vm_brk h)))%Z with false
      by (symmetry; apply Z.ltb_ge; lia).
    destruct (0 <? _)%Z; reflexivity. }
  rewrite Hus in Hs. destruct rsp as [r0 ws zs us cs ci]. rewrite strip_mk in Hs. inversion Hs; subst. clear Hs.
  destruct (Z.eq_dec req (bv_unsigned (vm_brk h))) as [Ereq | Hne].
  -
    assert (Hr0 : r = vm_brk h). { destruct Hr' as [-> | ->]; [rewrite Ereq; apply Z_to_bv_bv_unsigned| reflexivity]. }
    subst r. exists BrkSame. split; [|reflexivity].
    unfold dec_brk. rewrite Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
  - destruct Hr' as [-> | ->].
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
      destruct (_ <? _)%Z; rewrite (proj2 (listWW_eqb_eq _ _) eq_refl); reflexivity.
    + exists BrkSame. split; [|reflexivity].
      unfold dec_brk. rewrite Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
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

Lemma mmap_errnos_ENOMEM : forall {c} e, In e (mmap_errnos_when c) -> e = ENOMEM.
Proof. intros c e H. exact (proj2 (mmap_errnos_when_In c e H)). Qed.
Lemma mmap_errnos_when_forced : forall c e, In e (mmap_errnos_when c) -> c = true.
Proof. intros c e H. exact (proj1 (mmap_errnos_when_In c e H)). Qed.
Lemma mmap_destructive_errnos_False : forall e, In e mmap_destructive_errnos -> False.
Proof. exact mmap_destructive_errnos_In. Qed.
Lemma mprotect_errnos_when_forced : forall c e, In e (mprotect_errnos_when c) -> c = true.
Proof. intros c e H. exact (proj1 (mprotect_errnos_when_In c e H)). Qed.

Lemma m_vmmaps_forget_vm_ranges : forall rs m, m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof. induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma m_vmmaps_vm_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. reflexivity. Qed.

Lemma nstep_dec_mmap : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ mm_frame mo mo' /\
  exists x, dec_mmap len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros len avoid mo rsp mo' evs h Hlen Hlen2 Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  assert (MM := nstep_mm_frame (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs I).
  destruct H as [-> H]. split; [reflexivity|]. cbv zeta in H.
  rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold h in H.
  destruct H as [(e & He & Hs & ->)|[(_ & a & (Q1 & Q2 & Q3 & Q4 & Q5) & _ & Hs & ->)|[(Hm & _)|(Hm & _)]]].
  - split; [apply mm_frame_refl|]. apply mmap_errnos_ENOMEM in He. subst e.
    exists (MmErr ENOMEM). split; [|auto]. rewrite <- (strip_strip rsp) in Hs. destruct rsp as [r ws zs us cs ci].
    rewrite strip_mk in Hs. unfold efferr, eff0 in Hs. inversion Hs; subst. unfold dec_mmap. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - change (mmap_noreserve_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with false.
    split. { apply mm_frame_with_mmap_backing; [reflexivity|apply mm_frame_with_vmmaps; reflexivity]. }
    rewrite (unsigned_lit len) in Q3, Q4, Q5 by lia. fold (mmap_len len) in Q3, Q4, Q5.
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned a) = true).
    { unfold mmap_addr_ok. rewrite (proj2 (Z.eqb_eq _ _) Q1), (proj2 (Z.ltb_lt _ _) Q2), (proj2 (Z.leb_le _ _) Q3). cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact Q4| exact Hcov]. }
    exists (MmOk (bv_unsigned a)). split.
    + destruct rsp as [r ws zs us cs ci]. rewrite strip_mk in Hs. inversion Hs; subst. unfold dec_mmap. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact Q4|].
      rewrite with_mmap_backing_noreserve_false by reflexivity. rewrite m_vmmaps_with_vmmaps. reflexivity.
  - exfalso. revert Hm. vm_compute. discriminate.
  - exfalso. revert Hm. vm_compute. discriminate.
Qed.

Lemma nstep_dec_mmap_none : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ mm_frame mo mo' /\
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
  intros len avoid mo rsp mo' evs h Hlen Hlen2 Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  destruct H as [-> H]. split; [reflexivity|]. cbv zeta in H.
  rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold h in H.
  destruct H as [(e & He & Hs & ->)|[(Hm & _)|[(_ & _ & a & (Q1 & Q2 & Q3 & Q4 & Q5) & Hs & ->)|(_ & Hm & _)]]].
  - split; [apply mm_frame_refl|]. apply mmap_errnos_ENOMEM in He. subst e.
    exists (MmErr ENOMEM). split; [|auto]. destruct rsp as [r ws zs us cs ci].
    rewrite strip_mk in Hs. unfold efferr, eff0 in Hs. inversion Hs; subst. unfold dec_mmap_none. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - exfalso. revert Hm. vm_compute. discriminate.
  - change (mmap_noreserve_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with false.
    split. { apply mm_frame_with_mmap_backing; [reflexivity|apply mm_frame_with_vmmaps; reflexivity]. }
    rewrite (unsigned_lit len) in Q3, Q4, Q5 by lia. fold (mmap_len len) in Q3, Q4, Q5.
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned a) = true).
    { unfold mmap_addr_ok. rewrite (proj2 (Z.eqb_eq _ _) Q1), (proj2 (Z.ltb_lt _ _) Q2), (proj2 (Z.leb_le _ _) Q3). cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact Q4| exact Hcov]. }
    exists (MmOk (bv_unsigned a)). split.
    + destruct rsp as [r ws zs us cs ci]. rewrite strip_mk in Hs. inversion Hs; subst. unfold dec_mmap_none. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact Q4|].
      rewrite with_mmap_backing_noreserve_false by reflexivity. rewrite m_vmmaps_with_vmmaps. reflexivity.
  - exfalso. revert Hm. vm_compute. discriminate.
Qed.

Lemma nstep_dec_munmap : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len < 2^64)%Z ->
  nstep (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ mm_frame mo mo' /\
  dec_munmap addr len rsp = Some (RgDone true) /\
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
                              (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                              (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen H.
  destruct H as [-> H]. cbv zeta in H. destruct H as [Hs ->]. rewrite (unsigned_lit len) in Hs |- * by lia. fold (mmap_len len) a n h in Hs |- *.
  split; [reflexivity|]. split; [apply mm_frame_with_mmap_destroyed; reflexivity|]. split.
  - destruct rsp as [r ws zs us cs ci]. rewrite strip_mk in Hs. inversion Hs; subst. unfold dec_munmap.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbn [Z.eqb]. subst a n. rewrite !bv_eqb_refl. reflexivity.
  - unfold with_mmap_destroyed. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
Qed.

Lemma mprotect_errnos_ENOMEM : forall {c} e, In e (mprotect_errnos_when c) -> e = ENOMEM.
Proof. intros c e H. exact (proj2 (mprotect_errnos_when_In c e H)). Qed.

Lemma nstep_dec_mprotect : forall addr len prot mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len < 2^64)%Z ->
  nstep (NMprotect addr len prot) mo rsp mo' evs ->
  evs = [] /\ mm_frame mo mo' /\
  exists x, dec_mprotect addr len rsp = Some x /\
  match x with
  | RgErr e => e = ENOMEM /\ mo' = mo
  | RgDone false => False
  | RgDone true => mprotect_budget_ok mo a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros addr len prot mo rsp mo' evs h a n Ha Hlen H.
  destruct H as [-> H]. cbv zeta in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) a n h in H.
  split; [reflexivity|].
  destruct H as [(e & He & Hs & ->)|(Hb & Hs & ->)].
  - split; [apply mm_frame_refl|]. apply mprotect_errnos_ENOMEM in He. subst e. exists (RgErr ENOMEM). split; [|auto].
    destruct rsp as [r ws zs us cs ci]. rewrite strip_mk in Hs. unfold efferr, eff0 in Hs. inversion Hs; subst.
    unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - split; [apply mm_frame_mprotect_model_next|]. exists (RgDone true). split.
    + destruct rsp as [r ws zs us cs ci]. rewrite strip_mk in Hs. inversion Hs; subst. unfold dec_mprotect.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbn [Z.eqb]. subst a n. rewrite !bv_eqb_refl. reflexivity.
    + split; [exact Hb|]. unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps. reflexivity.
Qed.

Lemma region_free_forall : forall maps a n,
  region_free maps a n = true <-> (forall e, In e maps -> iv_overlap a n (fst e) (snd e) = false).
Proof.
  induction maps as [|[e0 sz0] maps IH]; intros a n; cbn [region_free].
  - split; [intros _ e []|reflexivity].
  - rewrite andb_true_iff, negb_true_iff, IH. split.
    + intros [H1 H2] e [<-|Hin]; [exact H1|apply H2; exact Hin].
    + intros H. split; [exact (H _ (or_introl eq_refl))|]. intros e Hin. apply H. right; exact Hin.
Qed.

Lemma region_free_incl : forall l l' a n,
  (forall e, In e l' -> In e l) -> region_free l a n = true -> region_free l' a n = true.
Proof.
  intros l l' a n Hincl H. apply region_free_forall. intros e He. apply (proj1 (region_free_forall l a n) H). auto.
Qed.

Lemma region_free_remove : forall R maps x a n,
  region_free (R ++ maps) a n = true -> region_free (R ++ map_remove maps x) a n = true.
Proof.
  intros R maps x a n. apply region_free_incl. intros e Hin. apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin|right].
  unfold map_remove in Hin. apply filter_In in Hin as [Hin _]. exact Hin.
Qed.

Lemma nstep_dec_mremap : forall old old_len new_len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  let on := mmap_len old_len in let nn := mmap_len new_len in let OLD := Z_to_bv 64 old in
  (0 <= old <= 2^64 - 4096)%Z -> (0 < old_len < 2^64)%Z -> (0 < new_len < 2^64)%Z ->
  minv mo ->
  Forall (covered (vm_reserved h ++ map_remove (vm_maps h) OLD)) avoid ->
  nstep (NMremap old old_len new_len) mo rsp mo' evs ->
  evs = [] /\ mm_frame mo mo' /\
  exists x, dec_mremap old old_len new_len avoid rsp = Some x /\
  match x with
  | MrErr e => e = ENOMEM /\ mo' = mo /\ on <> nn
  | MrSame => (on = nn /\ mo' = mo) \/ (on <> nn /\ mo' = mremap_model_next mo OLD (Z_to_bv 64 on) OLD (Z_to_bv 64 nn))
  | MrMoved dst => (on < nn)%Z /\ mremap_fresh_b mo on nn OLD (Z_to_bv 64 on) (Z_to_bv 64 dst) (Z_to_bv 64 nn) = true
      /\ mo' = mremap_model_next mo OLD (Z_to_bv 64 on) (Z_to_bv 64 dst) (Z_to_bv 64 nn)
  end.
Proof.
  intros old old_len new_len avoid mo rsp mo' evs h on nn OLD Hold Hol Hnl Hminv Hcov H.
  pose proof (minv_nolazy _ Hminv) as Hlazy. pose proof (minv_alloc_top _ Hminv) as [_ Htop]. fold h in Htop.
  destruct H as (-> & (core & Hs & Hout) & _). split; [reflexivity|].
  assert (FR : mm_frame mo mo').
  { pose proof (mremap_out_shape _ _ _ _ _ _ _ Hout) as (_ & _ & [->|(d & k & ->)]); [apply mm_frame_refl|apply mm_frame_mremap_model_next; exact Hlazy]. }
  split; [exact FR|].
  unfold mremap_out in Hout. cbv zeta in Hout. rewrite (unsigned_lit old_len), (unsigned_lit new_len) in Hout by lia.
  fold (mmap_len old_len) (mmap_len new_len) in Hout. fold on nn OLD h in Hout.
  assert (Eold : errno_of OLD = None) by (subst OLD; apply errno_of_lit; lia).
  destruct rsp as [r ws zs us cs ci]. rewrite strip_mk in Hs. subst core. unfold dec_mremap. cbv zeta. fold on nn OLD.
  destruct Hout as [(E & H)|[(NE & e & He & H)|[(L & H)|[(L & G & H)|(L & dst & Hd & H)]]]]; apply Ok_inj in H as (H & -> & _).
  - inversion H; subst. rewrite Eold, bv_eqb_refl.
    exists MrSame. split; [|left; auto].
    unfold mremap_inplace_effect, mremap_tail. rewrite E, Z.ltb_irrefl. cbn [eff_zeros eff_unmaps listWW_eqb andb]. rewrite Z.leb_refl. reflexivity.
  - unfold efferr, eff0 in H. inversion H; subst. cbn in He. destruct He as [<-|[]].
    rewrite errno_of_errno_ret by (unfold ENOMEM; lia). exists (MrErr ENOMEM). split; [reflexivity|auto].
  - exists MrSame. split; [|right; auto with zarith].
    unfold mremap_inplace_effect in H |- *. rewrite (proj2 (Z.ltb_lt _ _) L) in H |- *. inversion H; subst.
    rewrite Eold, bv_eqb_refl. cbn [eff_zeros eff_unmaps]. rewrite !listWW_eqb_refl. rewrite (proj2 (Z.leb_le nn on) ltac:(lia)). reflexivity.
  - exists MrSame. split; [|right; split; [lia|reflexivity]].
    assert (GE : (nn <? on)%Z = false) by (apply Z.ltb_ge; lia).
    unfold mremap_inplace_effect in H |- *. rewrite GE in H |- *. inversion H; subst.
    rewrite Eold, bv_eqb_refl. cbn [eff_zeros eff_unmaps]. rewrite !listWW_eqb_refl.
    pose proof G as G'. unfold mremap_inplace_grow_b in G. cbv zeta in G. fold h in G.
    apply andb_prop in G as [G _]. apply andb_prop in G as [G1 G2]. apply Z.leb_le in G1.
    assert (AV : avoids old nn avoid = true).
    { rewrite <- (unsigned_lit old) by lia. rewrite <- (unsigned_lit nn) by (pose proof (mmap_len_bound new_len ltac:(lia)); fold nn in H0; unfold alloc_ceiling_max in Htop; subst OLD; rewrite unsigned_lit in G1 by lia; lia).
      fold OLD. apply (avoids_of_region_free (vm_reserved h ++ map_remove (vm_maps h) OLD)); [exact G2|exact Hcov]. }
    subst OLD. rewrite unsigned_lit in G1 by lia. rewrite (proj2 (Z.leb_le (old + nn) alloc_ceiling_max) ltac:(lia)), AV.
    rewrite orb_true_r. reflexivity.
  - unfold mremap_move_effect in H. inversion H; subst.
    pose proof Hd as Hd'. unfold mremap_fresh_b in Hd. cbv zeta in Hd. fold h in Hd.
    apply andb_prop in Hd as [Hd P6]. apply andb_prop in Hd as [Hd P5].
    apply andb_prop in Hd as [Hd P4]. apply andb_prop in Hd as [Hd P3]. apply andb_prop in Hd as [P1 P2].
    apply Z.leb_le in P4. apply Z.ltb_lt in P3. apply Z.eqb_eq in P2.
    pose proof (mmap_len_bound new_len ltac:(lia)) as NB. fold nn in NB.
    assert (Edst : errno_of dst = None).
    { apply errno_of_small. unfold alloc_ceiling_max in Htop. lia. }
    assert (AV : avoids (bv_unsigned dst) nn avoid = true).
    { rewrite <- (unsigned_lit nn) by (unfold alloc_ceiling_max in Htop; pose proof (bv_unsigned_in_range 64 dst); lia).
      apply (avoids_of_region_free (vm_reserved h ++ map_remove (vm_maps h) OLD)); [|exact Hcov].
      apply region_free_remove. exact P5. }
    rewrite Edst. apply negb_true_iff in P1. rewrite P1.
    rewrite !listWW_eqb_refl, !bv_eqb_refl, (proj2 (Z.eqb_eq _ _) P2), (proj2 (Z.ltb_lt _ _) P3), (proj2 (Z.leb_le (bv_unsigned dst + nn) alloc_ceiling_max) ltac:(lia)), (proj2 (Z.ltb_lt _ _) L), AV.
    cbn [andb]. exists (MrMoved (bv_unsigned dst)). split; [reflexivity|].
    rewrite Z_to_bv_bv_unsigned. split; [exact L|]. split; [exact Hd'|reflexivity].
Qed.

Definition dec_openw : resp -> option sret := dec_open.

Definition dec_ioctlf : resp -> option sret := dec_ioctl.

Definition dec_unlink : resp -> option sret := dec_plain (fun v => (v =? 0)%Z).

Definition dec_lseek : resp -> option sret := dec_plain (fun v => (v <? 2^63)%Z).

Definition dec_writevf (total : Z) (rsp : resp) : option Z :=
  match rsp with
  | mkEffectU r [] [] [] [] _ => if (bv_unsigned r =? total)%Z then Some total else None
  | _ => None
  end.

Fixpoint bytes_eqb (a b : list byte) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => bv_eqb x y && bytes_eqb a' b'
  | _, _ => false
  end.
Fixpoint writes_eqb (x y : list (word * list byte)) : bool :=
  match x, y with
  | [], [] => true
  | (a, bs) :: x', (b, cs) :: y' => bv_eqb a b && bytes_eqb bs cs && writes_eqb x' y'
  | _, _ => false
  end.
Lemma bytes_eqb_eq : forall a b, bytes_eqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn; try (split; [discriminate| discriminate]); [tauto|].
  rewrite andb_true_iff, bv_eqb_eq, IH. split; [intros [-> ->]; reflexivity| intros E; injection E; auto].
Qed.
Lemma writes_eqb_eq : forall x y, writes_eqb x y = true <-> x = y.
Proof.
  induction x as [|[a bs] x IH]; intros [|[b cs] y]; cbn; try (split; [discriminate| discriminate]); [tauto|].
  rewrite !andb_true_iff, bv_eqb_eq, bytes_eqb_eq, IH. split; [intros [[-> ->] ->]; reflexivity| intros E; injection E; auto].
Qed.
Lemma writes_eqb_refl : forall x, writes_eqb x x = true.
Proof. intros x. apply writes_eqb_eq. reflexivity. Qed.

Definition dec_readv (a1 n1 a2 n2 : Z) (rsp : resp) : option (list byte) :=
  match rsp with
  | mkEffectU r ws [] [] [] _ =>
      let bs := concat (map snd ws) in
      if writes_eqb ws (scatter2 a1 n1 a2 bs) && (Z.of_nat (length bs) <=? n1 + n2)%Z
         && (bv_unsigned r =? Z.of_nat (length bs))%Z
      then Some bs else None
  | _ => None
  end.

Lemma dec_writevf_strip : forall total rsp, dec_writevf total (strip rsp) = dec_writevf total rsp.
Proof. intros total [r ws zs us cs ci]. reflexivity. Qed.
Lemma dec_readv_strip : forall a1 n1 a2 n2 rsp, dec_readv a1 n1 a2 n2 (strip rsp) = dec_readv a1 n1 a2 n2 rsp.
Proof. intros a1 n1 a2 n2 [r ws zs us cs ci]. reflexivity. Qed.

Lemma dec_writevf_Some : forall total rsp k, (0 <= total < 2^64)%Z -> dec_writevf total rsp = Some k ->
  k = total /\ strip rsp = eff0 (Z_to_bv 64 total).
Proof.
  intros total [r ws zs us cs ci] k Ht H. unfold dec_writevf in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  destruct (Z.eqb_spec (bv_unsigned r) total); [|discriminate]. inversion H; subst. split; [reflexivity|].
  unfold eff0. rewrite strip_mk. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma concat_scatter2 : forall a1 n1 a2 bs, 0 <= n1 -> concat (map snd (scatter2 a1 n1 a2 bs)) = bs.
Proof.
  intros a1 n1 a2 bs Hn. unfold scatter2.
  rewrite <- (firstn_skipn (Z.to_nat n1) bs) at 3.
  destruct (firstn (Z.to_nat n1) bs); destruct (skipn (Z.to_nat n1) bs); cbn; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma dec_readv_Some : forall a1 n1 a2 n2 rsp bs, 0 <= n1 -> dec_readv a1 n1 a2 n2 rsp = Some bs ->
  strip rsp = mkEffect (len_word bs) (scatter2 a1 n1 a2 bs) [] /\ (Z.of_nat (length bs) <= n1 + n2)%Z.
Proof.
  intros a1 n1 a2 n2 [r ws zs us cs ci] bs Hn H. unfold dec_readv in H.
  destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. cbv zeta in H.
  destruct (writes_eqb ws (scatter2 a1 n1 a2 (concat (map snd ws)))) eqn:E1; [|discriminate].
  destruct (Z.leb_spec0 (Z.of_nat (length (concat (map snd ws)))) (n1 + n2)); [|discriminate].
  destruct (Z.eqb_spec (bv_unsigned r) (Z.of_nat (length (concat (map snd ws))))); [|discriminate].
  cbn [andb] in H. inversion H; subst. apply writes_eqb_eq in E1.
  rewrite strip_mk. split; [|lia]. rewrite <- E1. f_equal. unfold len_word. apply bv_eq. rewrite unsigned_lit; [assumption|].
  pose proof (bv_unsigned_in_range 64 r). unfold bv_modulus in *. lia.
Qed.

Lemma nstep_dec_openw : forall path mo rsp mo' evs,
  minv mo ->
  nstep (NOpenW path) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_openw rsp = Some a /\
  match a with
  | SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
  | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z
      /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
      /\ path_is_dirref path = false /\ fs_under (m_fs mo) path = false
      /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFileW path (Z_to_bv 64 0))) (with_fs (fs_set (m_fs mo) path []) mo)
  end.
Proof.
  intros path mo rsp mo' evs Hminv [-> H]. split; [reflexivity|]. unfold dec_openw, dec_open. rewrite <- dec_plain_strip.
  assert (Herr : forall e, (1 <= e <= 4095)%Z -> strip rsp = efferr e -> mo' = mo ->
            exists a, dec_plain (fun v => (3 <=? v)%Z && (v <=? 4096)%Z) (strip rsp) = Some a /\
              match a with SErr e => mo' = mo /\ (1 <= e <= 4095)%Z | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z
                /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None /\ path_is_dirref path = false /\ fs_under (m_fs mo) path = false
                /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFileW path (Z_to_bv 64 0))) (with_fs (fs_set (m_fs mo) path []) mo) end).
  { intros e He -> ->. exists (SErr e). split; [apply dec_plain_err; exact He| auto]. }
  unfold create_result in H.
  destruct (path_is_dirref path) eqn:E1. { destruct H as [Hs ->]. apply (Herr EISDIR); [unfold EISDIR; lia| exact Hs| reflexivity]. }
  destruct (fs_under (m_fs mo) path) eqn:E3. { destruct H as [Hs ->]. apply (Herr EISDIR); [unfold EISDIR; lia| exact Hs| reflexivity]. }
  destruct H as [(e & HIn & Hs & ->)|(Hlk & -> & ->)].
  - apply (Herr e); [apply openat_errnos_range; exact HIn| exact Hs| reflexivity].
  - pose proof (alloc_fd_range mo Hminv Hlk) as Hr.
    exists (SVal (bv_unsigned (alloc_fd (m_fds mo)))). split.
    + unfold eff0. rewrite <- (Z_to_bv_bv_unsigned (alloc_fd (m_fds mo))) at 1.
      apply dec_plain_val; [lia|]. apply andb_true_intro; split; apply Z.leb_le; lia.
    + rewrite Z_to_bv_bv_unsigned. repeat split; auto; lia.
Qed.

Lemma nstep_dec_ioctlf : forall fd mo rsp mo' evs,
  nstep (NIoctlF fd) mo rsp mo' evs ->
  mo' = mo /\ evs = [] /\ exists e, dec_ioctlf rsp = Some (SErr e) /\
    ((e = ENOTTY /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) <> None) \/ (e = EBADF /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None)).
Proof.
  intros fd mo rsp mo' evs (-> & -> & H). split; [reflexivity|]. split; [reflexivity|].
  unfold dec_ioctlf, dec_ioctl. rewrite <- dec_plain_strip.
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) eqn:Hlk; rewrite H.
  - exists ENOTTY. split; [apply dec_plain_err; unfold ENOTTY; lia| left; split; [reflexivity| congruence]].
  - exists EBADF. split; [apply dec_plain_err; unfold EBADF; lia| right; auto].
Qed.

Lemma nstep_dec_writevf : forall fd bufs mo rsp mo' evs,
  (Z.of_nat (length (concat bufs)) < 2^64)%Z ->
  nstep (NWritevF fd bufs) mo rsp mo' evs ->
  evs = [] /\ dec_writevf (Z.of_nat (length (concat bufs))) rsp = Some (Z.of_nat (length (concat bufs))) /\
  exists p off data, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFileW p off) /\ fs_lookup (m_fs mo) p = Some data /\
    mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFileW p (off + len_word (concat bufs))%bv))
                   (with_fs (fs_set (m_fs mo) p (file_write data off (concat bufs))) mo).
Proof.
  intros fd bufs mo rsp mo' evs Hl (-> & p & off & data & Hlk & Hfs & Hs & ->). split; [reflexivity|]. split.
  - rewrite <- dec_writevf_strip, Hs. unfold dec_writevf, eff0, len_word. cbn. rewrite unsigned_lit by lia. rewrite Z.eqb_refl. reflexivity.
  - exists p, off, data. auto.
Qed.

Lemma nstep_dec_lseek : forall fd off whence mo rsp mo' evs,
  nstep (NLseek fd off whence) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_lseek rsp = Some a /\
  exists e p cur data, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some e /\ (e = FdFile p cur \/ e = FdFileW p cur) /\
    fs_lookup (m_fs mo) p = Some data /\
    match a with
    | SErr er => er = EINVAL /\ mo' = mo /\ lseek_dest (lseek_origin whence cur data) (Z_to_bv 64 off) = None
    | SVal r => (0 <= r < 2^63)%Z /\ lseek_dest (lseek_origin whence cur data) (Z_to_bv 64 off) = Some (Z_to_bv 64 r)
        /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (reseek_ent e (Z_to_bv 64 r))) mo
    end.
Proof.
  intros fd off whence mo rsp mo' evs (-> & e & p & cur & data & Hlk & He & Hfs & H). split; [reflexivity|].
  unfold dec_lseek. rewrite <- dec_plain_strip.
  destruct (lseek_dest (lseek_origin whence cur data) (Z_to_bv 64 off)) as [r|] eqn:Hd.
  - destruct H as [Hs ->].
    assert (Hr : (0 <= bv_unsigned r < 2^63)%Z).
    { unfold lseek_dest in Hd. destruct ((0 <=? _) && (_ <? 2 ^ 63))%Z eqn:E; [|discriminate]. inversion Hd; subst.
      apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite unsigned_lit by lia. lia. }
    exists (SVal (bv_unsigned r)). split.
    + rewrite Hs. unfold eff0. rewrite <- (Z_to_bv_bv_unsigned r) at 1. apply dec_plain_val; [lia|]. apply Z.ltb_lt. lia.
    + exists e, p, cur, data. rewrite Z_to_bv_bv_unsigned. repeat split; auto; lia.
  - destruct H as [Hs ->]. exists (SErr EINVAL). split; [rewrite Hs; apply dec_plain_err; unfold EINVAL; lia|].
    exists e, p, cur, data. repeat split; auto.
Qed.

Lemma nstep_dec_readv : forall fd a1 n1 a2 n2 mo rsp mo' evs,
  (0 < n1)%Z -> (0 < n2)%Z -> (n1 + n2 < 2^63)%Z ->
  nstep (NReadv fd a1 n1 a2 n2) mo rsp mo' evs ->
  evs = [] /\
  exists bs, dec_readv a1 n1 a2 n2 rsp = Some bs /\
  exists p off data, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) /\ fs_lookup (m_fs mo) p = Some data /\
    bs = file_read data off (Z_to_bv 64 (n1 + n2)) /\
    mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo.
Proof.
  intros fd a1 n1 a2 n2 mo rsp mo' evs Hn1 Hn2 Hn (-> & p & off & data & Hlk & Hfs & Hs & ->). split; [reflexivity|].
  set (bs := file_read data off (Z_to_bv 64 (n1 + n2))) in *.
  assert (Hl : (Z.of_nat (length bs) <= n1 + n2)%Z).
  { subst bs. rewrite file_read_unguarded, firstn_length. unfold word_to_nat. rewrite unsigned_lit by lia. lia. }
  exists bs. split.
  - rewrite <- dec_readv_strip, Hs. unfold dec_readv. cbv zeta. rewrite (concat_scatter2 a1 n1 a2 bs) by lia.
    rewrite writes_eqb_refl. replace (Z.of_nat (length bs) <=? n1 + n2)%Z with true by (symmetry; apply Z.leb_le; lia).
    unfold len_word. rewrite unsigned_lit by lia. rewrite Z.eqb_refl. reflexivity.
  - exists p, off, data. auto.
Qed.

Lemma unlinkat_errnos_range : forall e, In e unlinkat_errnos -> (1 <= e <= 4095)%Z.
Proof. intros e H. cbn in H. unfold ENOMEM, EACCES, EPERM, EROFS, EBUSY in H. lia. Qed.

Lemma nstep_dec_unlink : forall path mo rsp mo' evs,
  nstep (NUnlink path) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_unlink rsp = Some a /\
  match a with
  | SErr e => mo' = mo /\ (1 <= e <= 4095)%Z /\ (e = ENOENT <-> fs_lookup (m_fs mo) path = None)
  | SVal v => v = 0%Z /\ fs_lookup (m_fs mo) path <> None /\ fd_names_path (m_fds mo) path = false
      /\ mo' = with_fs (fs_remove (m_fs mo) path) mo
  end.
Proof.
  intros path mo rsp mo' evs [-> H]. split; [reflexivity|]. unfold dec_unlink. rewrite <- dec_plain_strip.
  destruct (fs_lookup (m_fs mo) path) eqn:Hfs.
  - destruct H as [(e & HIn & Hs & ->)|(Hn & Hs & ->)].
    + exists (SErr e). pose proof (unlinkat_errnos_range e HIn) as He. rewrite Hs. split; [apply dec_plain_err; exact He|].
      split; [reflexivity|]. split; [exact He|]. split; [| intros; discriminate].
      intros ->. exfalso. cbn in HIn. unfold ENOENT, ENOMEM, EACCES, EPERM, EROFS, EBUSY in HIn. lia.
    + exists (SVal 0). rewrite Hs. split; [apply dec_plain_val; [lia| reflexivity]|]. split; [reflexivity|]. split; [congruence|]. auto.
  - destruct H as [Hs ->]. exists (SErr ENOENT). rewrite Hs. split; [apply dec_plain_err; unfold ENOENT; lia|].
    split; [reflexivity|]. split; [unfold ENOENT; lia| tauto].
Qed.
