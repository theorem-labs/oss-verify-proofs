(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem ITree Nodes.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac disc_match H :=
  repeat (first [ discriminate H
                | lazymatch type of H with
                  | check_ret_only _ _ _ _ = CheckOk _ _ =>
                      apply check_ret_only_ok_iff in H as (H & ? & ?); discriminate H
                  | context [match ?x with _ => _ end] => destruct x
                  | context [if ?x then _ else _] => destruct x
                  end
                | progress (cbv zeta in H) ]).
Ltac kill_extra cs ci H := destruct cs; [| exfalso; disc_match H]; destruct ci; [| exfalso; disc_match H].

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
  intros ok [r ws zs us cs ci] a H. unfold dec_plain in H. kill_extra cs ci H.
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
  intros buf count [r ws zs us cs ci] a Hc H. unfold dec_read in H. kill_extra cs ci H.
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
  match rsp with
  | mkEffectU r [] [] [] [] [] => if (bv_unsigned r =? count)%Z then Some count else None
  | _ => None
  end.
Definition dec_write := dec_count.
Definition dec_writev := dec_count.

Lemma dec_count_Some : forall count rsp a, dec_count count rsp = Some a ->
  a = count /\ rsp = eff0 (Z_to_bv 64 count) /\ (0 <= count < 2^64)%Z.
Proof.
  intros count [r ws zs us cs ci] a H. unfold dec_count in H. kill_extra cs ci H.
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
  intros [r ws zs us cs ci] t H. unfold dec_set_tid in H. kill_extra cs ci H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct (Z.ltb_spec0 0 (bv_unsigned r)); [|discriminate].
  destruct (Z.ltb_spec0 (bv_unsigned r) PID_MAX_ENVELOPE); [|discriminate]. inversion H; subst.
  unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

(* [comment removed for export] *)
Definition dec_brk0 (rsp : resp) : option Z :=
  match rsp with mkEffectU r [] [] [] [] [] => Some (bv_unsigned r) | _ => None end.

Lemma dec_brk0_Some : forall rsp b, dec_brk0 rsp = Some b -> rsp = eff0 (Z_to_bv 64 b) /\ (0 <= b < 2^64)%Z.
Proof.
  intros [r ws zs us cs ci] b H. unfold dec_brk0 in H. kill_extra cs ci H.
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
  intros cur req [r ws zs us cs ci] a H. unfold dec_brk in H. kill_extra cs ci H.
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
Inductive mmap_ans : Type := MmErr (e : Z) | MmOk (a : Z).

Definition avoids (a n : Z) (avoid : list (Z * Z)) : bool :=
  forallb (fun iv => (a + n <=? fst iv)%Z || (snd iv <=? a)%Z) avoid.

Definition mmap_len (len : Z) : Z := page_round_up_Z len.

(* [comment removed for export] *)
Definition grant_top_max : Z := (2^64 - stack_max_size)%Z.
Lemma grant_top_max_val : grant_top_max = 0xFFFFFFFFFF800000%Z.
Proof. reflexivity. Qed.

Definition mmap_addr_ok (len : Z) (avoid : list (Z * Z)) (a : Z) : bool :=
  (a mod page_size =? 0)%Z && (0 <? a)%Z && (a + mmap_len len <=? grant_top_max)%Z && avoids a (mmap_len len) avoid.

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
  (a mod page_size = 0 /\ 0 < a /\ a + mmap_len len <= grant_top_max)%Z /\ avoids a (mmap_len len) avoid = true.
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
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap in H. kill_extra cs ci H.
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
  intros len avoid [r ws zs us cs ci] x H. unfold dec_mmap_none in H. kill_extra cs ci H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst. apply errno_of_Some in E as [-> He]. auto.
  - destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
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
  intros addr len [r ws zs us cs ci] x H. unfold dec_munmap in H. kill_extra cs ci H.
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
  intros addr len [r ws zs us cs ci] x H. unfold dec_mprotect in H. kill_extra cs ci H.
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
(* [comment removed for export] *)

Lemma nstep_brk_inv : forall req mo rsp mo' evs,
  nstep (NBrk req) mo rsp mo' evs ->
  exists r, brk_r_ok mo (Z_to_bv 64 req) r = true
    /\ mo' = with_brk_next mo (Z_to_bv 64 req) r
    /\ rsp = mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo))) (brk_unmaps r (vm_brk (m_vmmaps mo))) [] []
    /\ evs = [].
Proof.
  intros req mo rsp mo' evs H. apply nstep_brk_iff in H as [-> H]. destruct rsp as [r ws zs us cs ci]. unfold check_brk in H.
  kill_extra cs ci H.
  destruct ws; [|discriminate].
  destruct (brk_r_ok mo (Z_to_bv 64 req) r) eqn:E1; [|discriminate].
  destruct (listNN_eqb zs _) eqn:E2; [|discriminate]. destruct (listNN_eqb us _) eqn:E3; [|discriminate].
  cbn [andb] in H. inversion H; subst. apply listNN_eqb_eq in E2. apply listNN_eqb_eq in E3. subst.
  exists r. split; [exact E1|]. repeat split; reflexivity.
Qed.

Lemma page_round_up_Z_idem_le : forall x, (page_round_up_Z x <? page_round_up_Z x)%Z = false.
Proof. intros. apply Z.ltb_irrefl. Qed.

Lemma brk_unmaps_nogrow : forall r old, (bv_unsigned old <= bv_unsigned r)%Z -> brk_unmaps r old = [].
Proof.
  intros r old H. unfold brk_unmaps, brk_page_range.
  pose proof (page_round_up_Z_mono _ _ H).
  replace (page_round_up_Z (bv_unsigned r) <? page_round_up_Z (bv_unsigned old))%Z with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (0 <? _)%Z; reflexivity.
Qed.

Lemma maps_subtract_ranges_nil : forall maps, maps_subtract_ranges maps [] = maps.
Proof. reflexivity. Qed.

Lemma with_brk_next_vmmaps_nogrow_shape : forall mo req r,
  (bv_unsigned (vm_brk (m_vmmaps mo)) <= bv_unsigned r)%Z ->
  let h := m_vmmaps mo in
  with_brk_next mo req r = with_vmmaps (mkVmMapsFull (vm_reserved h) (brk_grants req r (vm_brk h) ++ vm_maps h) (vm_noaccess h)
                                                    (vm_start_brk h) r (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.
Proof.
  intros mo req r Hle h. unfold with_brk_next. fold h. rewrite (brk_unmaps_nogrow r (vm_brk h) Hle). cbn [forget_vm_ranges].
  unfold brk_model_next. rewrite (brk_unmaps_nogrow r (vm_brk h) Hle), maps_subtract_ranges_nil.
  unfold brk_maps_next. destruct (Z.ltb_spec0 (bv_unsigned r) (bv_unsigned (vm_brk h))); [exfalso; subst h; lia|].
  rewrite andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_brk0 : forall mo rsp mo' evs,
  minv mo -> nstep (NBrk 0) mo rsp mo' evs ->
  let h := m_vmmaps mo in
  evs = [] /\ dec_brk0 rsp = Some (bv_unsigned (vm_brk h)) /\ vm_only mo mo'
  /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros mo rsp mo' evs Hm H h.
  pose proof (nstep_mm_vm_only (NBrk 0) mo rsp mo' evs Hm I H) as [Hv _].
  destruct (nstep_brk_inv _ _ _ _ _ H) as (r & Hr & -> & -> & ->). split; [reflexivity|].
  unfold brk_r_ok in Hr. change (w_is0 (Z_to_bv 64 0)) with true in Hr. cbn [orb] in Hr. apply bv_eqb_eq in Hr. subst r.
  split; [|split; [exact Hv|]].
  - unfold dec_brk0, brk_zeros, brk_is_grow. change (w_is0 (Z_to_bv 64 0)) with true. cbn [negb andb].
    rewrite brk_unmaps_nogrow by lia. reflexivity.
  - rewrite with_brk_next_vmmaps_nogrow_shape by lia. unfold brk_grants, brk_is_grow.
    change (w_is0 (Z_to_bv 64 0)) with true. cbn [negb andb app]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_brk : forall req mo rsp mo' evs,
  let h := m_vmmaps mo in
  minv mo ->
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_brk h) <= req < 2^64)%Z ->
  nstep (NBrk req) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists a, dec_brk (bv_unsigned (vm_brk h)) req rsp = Some a /\
  match a with
  | BrkSame => m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  | BrkGrown => (bv_unsigned (vm_brk h) < req)%Z /\ brk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true /\
      m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((vm_brk h, (Z_to_bv 64 req - vm_brk h)%bv) :: vm_maps h) (vm_noaccess h)
                                  (vm_start_brk h) (Z_to_bv 64 req) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros req mo rsp mo' evs h Hm Hb Hsb Hreq H.
  pose proof (nstep_mm_vm_only (NBrk req) mo rsp mo' evs Hm I H) as [Hv _].
  destruct (nstep_brk_inv _ _ _ _ _ H) as (r & E1 & Emo & -> & ->). split; [reflexivity|]. split; [exact Hv|].
  fold h in E1, Emo |- *.
  unfold brk_r_ok in E1. rewrite w_is0_lit in E1 by lia.
  replace (req =? 0)%Z with false in E1 by (symmetry; apply Z.eqb_neq; lia).
  unfold min_brk in E1. fold h in E1. rewrite unsigned_lit in E1 by lia.
  replace (req <? bv_unsigned (vm_start_brk h))%Z with false in E1 by (symmetry; apply Z.ltb_ge; lia).
  replace (req <? bv_unsigned (vm_brk h))%Z with false in E1 by (symmetry; apply Z.ltb_ge; lia).
  cbn [orb] in E1. apply andb_prop in E1 as [E1 G].
  assert (Hr : r = Z_to_bv 64 req \/ r = vm_brk h).
  { apply orb_prop in E1 as [E1|E1]; apply bv_eqb_eq in E1; auto. }
  assert (Hle : (bv_unsigned (vm_brk (m_vmmaps mo)) <= bv_unsigned r)%Z).
  { subst h. destruct Hr as [-> | ->]; [rewrite unsigned_lit by lia|]; lia. }
  rewrite (with_brk_next_vmmaps_nogrow_shape mo _ r Hle) in Emo. fold h in Emo.
  rewrite (brk_unmaps_nogrow r (vm_brk h) Hle).
  destruct (Z.eq_dec req (bv_unsigned (vm_brk h))) as [Ereq | Hne].
  - (* [comment removed for export] *)
    assert (Hr' : r = vm_brk h). { destruct Hr as [-> | ->]; [rewrite Ereq; apply Z_to_bv_bv_unsigned| reflexivity]. }
    subst r. exists BrkSame.
    unfold brk_zeros, brk_grants, brk_is_grow in *. rewrite Z.ltb_irrefl, andb_false_r in *. split; [|subst mo'; reflexivity].
    unfold dec_brk. rewrite Z.eqb_refl. reflexivity.
  - destruct Hr as [-> | ->].
    + exists BrkGrown.
      unfold brk_zeros, brk_grants, brk_is_grow in *. rewrite w_is0_lit in * by lia.
      replace (req =? 0)%Z with false in * by (symmetry; apply Z.eqb_neq; lia).
      replace (0 <? bv_unsigned (vm_brk h))%Z with true in * by (symmetry; apply Z.ltb_lt; lia).
      rewrite unsigned_lit in * by lia.
      replace (bv_unsigned (vm_brk h) <? req)%Z with true in * by (symmetry; apply Z.ltb_lt; lia).
      cbn [negb andb app] in *. split; [| split; [lia| split; [exact G| subst mo'; reflexivity]]].
      unfold dec_brk. rewrite unsigned_lit by lia.
      replace (req =? bv_unsigned (vm_brk h))%Z with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [andb]. rewrite Z.eqb_refl.
      unfold brk_page_range, brk_new_pages, zeros_of, wa.
      destruct (page_round_up_Z (bv_unsigned (vm_brk h)) <? page_round_up_Z req)%Z; cbn [andb];
        rewrite (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
    + exists BrkSame.
      unfold brk_zeros, brk_grants, brk_is_grow in *. rewrite Z.ltb_irrefl, !andb_false_r in *. split; [|subst mo'; reflexivity].
      unfold dec_brk. rewrite Z.eqb_refl. reflexivity.
Qed.

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

Lemma m_vmmaps_vm_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. intros. reflexivity. Qed.
Lemma m_vmmaps_with_vmmaps : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nstep_dec_mmap : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  minv mo -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ (a + mmap_len len <= alloc_top h)%Z   (* [comment removed for export] *)
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros len avoid mo rsp mo' evs h Hm Hlen Hlen2 Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMmap 0 len _ _) mo rsp mo' evs Hm (nsafe_mmap_rw 0 len mo ltac:(lia)) H) as [Hv ->].
  split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mmap_iff in H as [_ H]. destruct rsp as [r ws zs us cs ci]. unfold check_mmap in H. kill_extra cs ci H.
  (* [comment removed for export] *)
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H.
  change (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true in H. cbn [negb] in H. cbv iota in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with true in H.
  cbv iota beta in H. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  fold h in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  destruct (errno_ret_in mmap_errnos r) eqn:Herr.
  - destruct zs; [|discriminate]. inversion H; subst.
    apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    inversion H; subst; clear H.
    apply andb_prop in E as [E E7]. apply andb_prop in E as [E E5]. apply andb_prop in E as [E E4].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply listNN_eqb_eq in E7. subst zs.
    pose proof (proj1 (Z.leb_le _ _) E3) as E3'. pose proof (alloc_top_room h) as Hroom.
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned r) = true).
    { unfold mmap_addr_ok. rewrite E1, E2. cbn [andb].
      replace (bv_unsigned r + mmap_len len <=? grant_top_max)%Z with true
        by (symmetry; apply Z.leb_le; unfold grant_top_max; unfold two_pow_64 in Hroom; lia). cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
    exists (MmOk (bv_unsigned r)). split.
    + unfold dec_mmap. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E3'|]. split; [exact E4|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_mmap_none : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  minv mo -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap_none len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ (a + mmap_len len <= alloc_top h)%Z   (* [comment removed for export] *)
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess h)
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros len avoid mo rsp mo' evs h Hm Hlen Hlen2 Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMmap 0 len _ _) mo rsp mo' evs Hm (nsafe_mmap_none 0 len mo ltac:(lia)) H) as [Hv ->].
  split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mmap_iff in H as [_ H]. destruct rsp as [r ws zs us cs ci]. unfold check_mmap in H. kill_extra cs ci H.
  (* [comment removed for export] *)
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H.
  change (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true in H. cbn [negb] in H. cbv iota in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with false in H.
  change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with true in H.
  cbv iota beta in H. destruct ws; [|discriminate]. destruct zs; [|destruct us; discriminate].
  fold h in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  destruct (errno_ret_in mmap_errnos r) eqn:Herr.
  - destruct us; [|discriminate]. inversion H; subst.
    apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap_none. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    inversion H; subst; clear H.
    apply andb_prop in E as [E E6]. apply andb_prop in E as [E E4].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply listNN_eqb_eq in E6. subst us.
    pose proof (proj1 (Z.leb_le _ _) E3) as E3'. pose proof (alloc_top_room h) as Hroom.
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned r) = true).
    { unfold mmap_addr_ok. rewrite E1, E2. cbn [andb].
      replace (bv_unsigned r + mmap_len len <=? grant_top_max)%Z with true
        by (symmetry; apply Z.leb_le; unfold grant_top_max; unfold two_pow_64 in Hroom; lia). cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
    exists (MmOk (bv_unsigned r)). split.
    + unfold dec_mmap_none. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E3'|]. split; [exact E4|]. reflexivity.
Qed.

Lemma nstep_dec_munmap : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  minv mo -> (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  nsafe (NMunmap addr len) mo ->
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
  intros addr len mo rsp mo' evs h a n Hm Ha Hlen Hlen2 Hs H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMunmap addr len) mo rsp mo' evs Hm Hs H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_munmap_iff in H as [_ H]. destruct rsp as [r ws zs us cs ci]. unfold check_munmap in H. kill_extra cs ci H.
  fold a h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H.
  destruct (negb (bv_unsigned a mod page_size =? 0)%Z || w_is0 (Z_to_bv 64 len)).
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_munmap. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  cbv zeta in H.
  (* [comment removed for export] *)
  destruct (TASK_SIZE <? _)%Z.
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_munmap. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  destruct (map_has (vm_maps h) a n) eqn:Hhas.
  - destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct (w_is0 r && listNN_eqb us [(a, n)]) eqn:E; [|discriminate]. inversion H; subst; clear H.
    apply andb_prop in E as [E1 E2]. apply listNN_eqb_eq in E2. subst us. unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
    exists (RgDone true). split; [|split; [reflexivity|reflexivity]].
    unfold dec_munmap. subst a n. rewrite !bv_eqb_refl. reflexivity.
  - destruct (munmap_free_ok h a (mmap_len len)) eqn:Hrf; [|discriminate].
    apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgDone false). split; [reflexivity|].
    split; [reflexivity|]. unfold munmap_free_ok in Hrf. apply andb_prop in Hrf as [Hrf _]. exact Hrf.
Qed.

Lemma nstep_dec_mprotect : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  minv mo -> (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  nsafe (NMprotect addr len (PROT_READ + PROT_WRITE)) mo ->
  nstep (NMprotect addr len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mprotect addr len rsp = Some x /\
  match x with
  | RgErr e => (e = EINVAL \/ e = ENOMEM) /\ mo' = mo
  | RgDone false => mo' = mo /\ region_free (vm_noaccess h) a n = true
  | RgDone true => map_contains (vm_noaccess h) a n = true /\ map_contains (vm_maps h) a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros addr len mo rsp mo' evs h a n Hm Ha Hlen Hlen2 Hs H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMprotect addr len _) mo rsp mo' evs Hm Hs H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mprotect_iff in H as [_ H]. destruct rsp as [r ws zs us cs ci]. unfold check_mprotect in H. kill_extra cs ci H.
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
    destruct (errno_ret_in mprotect_errnos r) eqn:Herr.
    + destruct zs; [|discriminate]. inversion H; subst.
      apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
      exists (RgErr ENOMEM). split; [|auto]. unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
    + match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end. inversion H; subst; clear H.
      apply andb_prop in E as [E E2]. apply andb_prop in E as [E0 E1]. apply listNN_eqb_eq in E2. subst zs. unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
      apply andb_prop in Hc as [Hc1 Hc2].
      exists (RgDone true). split; [| auto].
      unfold dec_mprotect. subst a n. rewrite !bv_eqb_refl. reflexivity.
  - destruct (map_contains (vm_maps h) a n && region_free (vm_noaccess h) a n) eqn:Hc2; [|discriminate].
    apply andb_prop in Hc2 as [_ Hrf].
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct (w_is0 r) eqn:E; [|discriminate]. inversion H; subst. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
    exists (RgDone false). split; [|split; [reflexivity| exact Hrf]].
    unfold dec_mprotect. rewrite errno_of_lit by lia. reflexivity.
Qed.
