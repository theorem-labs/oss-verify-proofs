(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bs X1c2.

Import ListNotations.
Open Scope bv_scope.

Fixpoint listNN_eqb (l1 l2 : list (word * word)) : bool :=
match l1, l2 with
| [], [] => true
| (a1, n1) :: r1, (a2, n2) :: r2 => bv_eqb a1 a2 && bv_eqb n1 n2 && listNN_eqb r1 r2
| _, _ => false
end.

Lemma listNN_eqb_eq : forall l1 l2, listNN_eqb l1 l2 = true <-> l1 = l2.
Proof.
induction l1 as [|[a1 n1] r1 IH]; destruct l2 as [|[a2 n2] r2]; cbn; try (split; congruence).
rewrite !Bool.andb_true_iff, !bv_eqb_eq, IH.
split; [intros [[-> ->] ->]; auto | intro H; inversion H; auto].
Qed.

Lemma listNN_eqb_refl : forall l, listNN_eqb l l = true.
Proof. intros l. apply listNN_eqb_eq. reflexivity. Qed.

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
| SErr e => ecore rsp = efferr e /\ (1 <= e <= 4095)%Z
| SVal v => ecore rsp = eff0 (Z_to_bv 64 v) /\ ok v = true /\ (0 <= v <= 2^64 - 4096)%Z
end.
Proof.
intros ok [r ws zs us cs cps] a H. unfold dec_plain in H. unfold ecore; cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
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

Lemma dec_read_Some : forall buf count rsp a, (0 <= count)%Z -> dec_read buf count rsp = Some a ->
match a with
| RdErr e => ecore rsp = efferr e /\ (1 <= e <= 4095)%Z
| RdData bs => ecore rsp = mkEffect (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) []
/\ (Z.of_nat (length bs) <= count)%Z
end.
Proof.
intros buf count [r ws zs us cs cps] a Hc H. unfold dec_read in H. unfold ecore; cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
destruct ws as [|[a0 bs] [|? ?]]; try discriminate.
- destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
destruct (errno_of r) as [e|] eqn:E.
+ inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
+ destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst. cbn.
split; [|lia]. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
- destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
destruct (bv_eqb a0 (Z_to_bv 64 buf)) eqn:E1; [|discriminate].
destruct (Z.leb_spec0 1 (Z.of_nat (length bs))); [|discriminate].
destruct (Z.leb_spec0 (Z.of_nat (length bs)) count); [|discriminate].
destruct (Z.eqb_spec (bv_unsigned r) (Z.of_nat (length bs))); [|discriminate].
cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. subst a0.
destruct bs as [|b bs']; [cbn in *; lia|]. cbn [delivered_writes]. split; [|lia].
f_equal. apply bv_eq. rewrite unsigned_lit. { assumption. }
pose proof (bv_unsigned_in_range 64 r). unfold bv_modulus in *. lia.
Qed.

Definition dec_count (count : Z) (rsp : resp) : option Z :=
match rsp with
| mkEffectU r [] [] [] [] _ =>
if (bv_unsigned r <=? count)%Z && ((count =? 0)%Z || (1 <=? bv_unsigned r)%Z)
then Some (bv_unsigned r) else None
| _ => None
end.
Definition dec_write := dec_count.
Definition dec_writev := dec_count.

Lemma dec_count_Some : forall count rsp a, dec_count count rsp = Some a ->
ecore rsp = eff0 (Z_to_bv 64 a) /\ (0 <= a <= count)%Z /\ (count = 0 \/ 1 <= a)%Z /\ (a < 2^64)%Z.
Proof.
intros count [r ws zs us cs cps] a H. unfold dec_count in H. unfold ecore; cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
destruct (Z.leb_spec0 (bv_unsigned r) count); [|discriminate].
destruct (Z.eqb_spec count 0); [| destruct (Z.leb_spec0 1 (bv_unsigned r)); [|discriminate]]; cbn [andb orb] in H;
inversion H; subst; pose proof (bv_unsigned_in_range 64 r) as R; unfold bv_modulus in R;
unfold eff0; rewrite Z_to_bv_bv_unsigned; repeat split; try reflexivity; lia.
Qed.

Lemma dec_count_val : forall count k, (0 <= k <= count)%Z -> (count = 0 \/ 1 <= k)%Z -> (count < 2^64)%Z ->
forall cps, dec_count count (mkEffectU (Z_to_bv 64 k) [] [] [] [] cps) = Some k.
Proof.
intros count k Hk Hk1 Hc cps. unfold dec_count. rewrite unsigned_lit by lia.
replace (k <=? count)%Z with true by (symmetry; apply Z.leb_le; lia).
destruct Hk1 as [-> | H1]; [rewrite Z.eqb_refl; cbn; f_equal; lia|].
replace (1 <=? k)%Z with true by (symmetry; apply Z.leb_le; lia). rewrite orb_true_r. reflexivity.
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
ecore rsp = eff0 (Z_to_bv 64 t) /\ (0 < t < PID_MAX_ENVELOPE)%Z.
Proof.
intros [r ws zs us cs cps] t H. unfold dec_set_tid in H. unfold ecore; cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
destruct (Z.ltb_spec0 0 (bv_unsigned r)); [|discriminate].
destruct (Z.ltb_spec0 (bv_unsigned r) PID_MAX_ENVELOPE); [|discriminate]. inversion H; subst.
unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

Definition dec_brk0 (rsp : resp) : option Z :=
match rsp with mkEffectU r [] [] [] [] _ => Some (bv_unsigned r) | _ => None end.

Lemma dec_brk0_Some : forall rsp b, dec_brk0 rsp = Some b -> ecore rsp = eff0 (Z_to_bv 64 b) /\ (0 <= b < 2^64)%Z.
Proof.
intros [r ws zs us cs cps] b H. unfold dec_brk0 in H. unfold ecore; cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. inversion H; subst.
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
| mkEffectU r [] zs [] [] _ =>
if (bv_unsigned r =? cur)%Z && match zs with [] => true | _ => false end then Some BrkSame
else if (bv_unsigned r =? req)%Z && listNN_eqb zs (zeros_of (brk_new_pages cur req)) then Some BrkGrown
else None
| _ => None
end.

Lemma dec_brk_Some : forall cur req rsp a, dec_brk cur req rsp = Some a ->
match a with
| BrkSame => ecore rsp = eff0 (Z_to_bv 64 cur)
| BrkGrown => ecore rsp = mkEffect (Z_to_bv 64 req) [] (zeros_of (brk_new_pages cur req))
end.
Proof.
intros cur req [r ws zs us cs cps] a H. unfold dec_brk in H. unfold ecore; cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate].
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

Inductive mmap_ans : Type := MmErr (e : Z) | MmOk (a : Z).

Definition avoids (a n : Z) (avoid : list (Z * Z)) : bool :=
forallb (fun iv => (a + n <=? fst iv)%Z || (snd iv <=? a)%Z) avoid.

Definition mmap_len (len : Z) : Z := page_round_up_Z len.

Definition mmap_addr_ok (ceil len : Z) (avoid : list (Z * Z)) (a : Z) : bool :=
(a mod page_size =? 0)%Z && (0 <? a)%Z && (a + mmap_len len <=? ceil)%Z && avoids a (mmap_len len) avoid.

Definition dec_mmap (ceil len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
match rsp with
| mkEffectU r [] [] [] [] _ => match errno_of r with Some e => Some (MmErr e) | None => None end
| mkEffectU r [] [(a, n)] [] [] _ =>
if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok ceil len avoid (bv_unsigned r)
then Some (MmOk (bv_unsigned r)) else None
| _ => None
end.

Definition dec_mmap_none (ceil len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
match rsp with
| mkEffectU r [] [] [] [] _ => match errno_of r with Some e => Some (MmErr e) | None => None end
| mkEffectU r [] [] [(a, n)] [] _ =>
if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok ceil len avoid (bv_unsigned r)
then Some (MmOk (bv_unsigned r)) else None
| _ => None
end.

Lemma avoids_In : forall a n avoid lo hi, avoids a n avoid = true -> In (lo, hi) avoid -> (a + n <= lo \/ hi <= a)%Z.
Proof.
intros a n avoid lo hi H Hin. unfold avoids in H. rewrite forallb_forall in H.
specialize (H _ Hin). cbn in H. apply orb_prop in H as [H|H]; [left|right]; apply Z.leb_le; exact H.
Qed.

Lemma mmap_addr_ok_true : forall ceil len avoid a, mmap_addr_ok ceil len avoid a = true ->
(a mod page_size = 0 /\ 0 < a /\ a + mmap_len len <= ceil)%Z /\ avoids a (mmap_len len) avoid = true.
Proof.
intros ceil len avoid a H. unfold mmap_addr_ok in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma dec_mmap_Some : forall ceil len avoid rsp x, dec_mmap ceil len avoid rsp = Some x ->
match x with
| MmErr e => ecore rsp = efferr e /\ (1 <= e <= 4095)%Z
| MmOk a => ecore rsp = mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] /\ mmap_addr_ok ceil len avoid a = true
end.
Proof.
intros ceil len avoid [r ws zs us cs cps] x H. unfold dec_mmap in H. unfold ecore; cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
- destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst.
apply errno_of_Some in E as [-> He]. auto.
- destruct us; [|discriminate]. destruct cs; [|discriminate].
destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
destruct (mmap_addr_ok ceil len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

Lemma dec_mmap_none_Some : forall ceil len avoid rsp x, dec_mmap_none ceil len avoid rsp = Some x ->
match x with
| MmErr e => ecore rsp = efferr e /\ (1 <= e <= 4095)%Z
| MmOk a => ecore rsp = mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] /\ mmap_addr_ok ceil len avoid a = true
end.
Proof.
intros ceil len avoid [r ws zs us cs cps] x H. unfold dec_mmap_none in H. unfold ecore; cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
- destruct cs; [|discriminate]. destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst. apply errno_of_Some in E as [-> He]. auto.
- destruct cs; [|discriminate]. destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
destruct (mmap_addr_ok ceil len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
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
| RgErr e => ecore rsp = efferr e /\ (1 <= e <= 4095)%Z
| RgDone false => ecore rsp = eff0 (Z_to_bv 64 0)
| RgDone true => ecore rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] []
end.
Proof.
intros addr len [r ws zs us cs cps] x H. unfold dec_munmap in H. unfold ecore; cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
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
| RgErr e => ecore rsp = efferr e /\ (1 <= e <= 4095)%Z
| RgDone false => ecore rsp = eff0 (Z_to_bv 64 0)
| RgDone true => ecore rsp = mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))]
end.
Proof.
intros addr len [r ws zs us cs cps] x H. unfold dec_mprotect in H. unfold ecore; cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
- destruct us; [|discriminate]. destruct cs; [|discriminate].
destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
- destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

Lemma dec_plain_ecore : forall ok rsp, dec_plain ok (ecore rsp) = dec_plain ok rsp.
Proof. intros ok [r ws zs us cs cps]; reflexivity. Qed.
Lemma dec_read_ecore : forall buf count rsp, dec_read buf count (ecore rsp) = dec_read buf count rsp.
Proof. intros buf count [r ws zs us cs cps]; reflexivity. Qed.
Lemma dec_count_ecore : forall count rsp, dec_count count (ecore rsp) = dec_count count rsp.
Proof. intros count [r ws zs us cs cps]; reflexivity. Qed.
Lemma dec_set_tid_ecore : forall rsp, dec_set_tid (ecore rsp) = dec_set_tid rsp.
Proof. intros [r ws zs us cs cps]; reflexivity. Qed.
Lemma dec_brk0_ecore : forall rsp, dec_brk0 (ecore rsp) = dec_brk0 rsp.
Proof. intros [r ws zs us cs cps]; reflexivity. Qed.
Lemma dec_brk_ecore : forall cur req rsp, dec_brk cur req (ecore rsp) = dec_brk cur req rsp.
Proof. intros cur req [r ws zs us cs cps]; reflexivity. Qed.
Lemma dec_mmap_ecore : forall ceil len avoid rsp, dec_mmap ceil len avoid (ecore rsp) = dec_mmap ceil len avoid rsp.
Proof. intros ceil len avoid [r ws zs us cs cps]; reflexivity. Qed.
Lemma dec_mmap_none_ecore : forall ceil len avoid rsp, dec_mmap_none ceil len avoid (ecore rsp) = dec_mmap_none ceil len avoid rsp.
Proof. intros ceil len avoid [r ws zs us cs cps]; reflexivity. Qed.
Lemma dec_munmap_ecore : forall addr len rsp, dec_munmap addr len (ecore rsp) = dec_munmap addr len rsp.
Proof. intros addr len [r ws zs us cs cps]; reflexivity. Qed.
Lemma dec_mprotect_ecore : forall addr len rsp, dec_mprotect addr len (ecore rsp) = dec_mprotect addr len rsp.
Proof. intros addr len [r ws zs us cs cps]; reflexivity. Qed.

Lemma length_file_read_le_count : forall data off count,
(0 <= count < 2^64)%Z -> (Z.of_nat (length (file_read data off (Z_to_bv 64 count))) <= count)%Z.
Proof.
intros data off count Hc. rewrite file_read_unguarded. rewrite length_firstn.
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
rewrite <- dec_read_ecore.
destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|nrd nwr| ]|] eqn:Hlk; try contradiction.
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

Lemma firstn_Z_to_nat_of_nat : forall {A} (k : nat) (l : list A), firstn (Z.to_nat (Z.of_nat k)) l = firstn k l.
Proof. intros. rewrite Nat2Z.id. reflexivity. Qed.

Lemma nstep_dec_write : forall fd bs mo rsp mo' evs,
(Z.of_nat (length bs) < 2^64)%Z ->
nstep (NWrite fd bs) mo rsp mo' evs ->
exists k, dec_write (Z.of_nat (length bs)) rsp = Some k /\ (1 <= k <= Z.of_nat (length bs))%Z
/\ mo' = mo /\ evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) bs).
Proof.
intros fd bs mo rsp mo' evs Hl (-> & k & Hk & Hc & ->). exists (Z.of_nat k).
split; [| split; [lia| split; [reflexivity| rewrite firstn_Z_to_nat_of_nat; reflexivity]]].
unfold dec_write. rewrite <- dec_count_ecore, Hc. apply dec_count_val; lia.
Qed.

Lemma nstep_dec_writev : forall fd bufs mo rsp mo' evs,
(Z.of_nat (length (concat bufs)) < 2^64)%Z ->
nstep (NWritev fd bufs) mo rsp mo' evs ->
exists k, dec_writev (Z.of_nat (length (concat bufs))) rsp = Some k
/\ (0 <= k <= Z.of_nat (length (concat bufs)))%Z /\ (length (concat bufs) = 0%nat \/ (1 <= k)%Z)
/\ mo' = mo /\ evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) (concat bufs)).
Proof.
intros fd bufs mo rsp mo' evs Hl [-> H]. unfold dec_writev. rewrite <- dec_count_ecore.
destruct (Nat.eqb_spec (length (concat bufs)) 0) as [Hz|Hnz].
- destruct H as [Hc ->]. exists 0%Z. rewrite Hc, Hz. split; [apply dec_count_val; lia|].
split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|].
destruct (concat bufs); [reflexivity| cbn in Hz; lia].
- destruct H as (k & Hk & Hc & ->). exists (Z.of_nat k). rewrite Hc. split; [apply dec_count_val; lia|].
split; [lia|]. split; [right; lia|]. split; [reflexivity|]. rewrite firstn_Z_to_nat_of_nat. reflexivity.
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
intros path mo rsp mo' evs Hminv [-> H]. split; [reflexivity|]. unfold dec_open. rewrite <- dec_plain_ecore.
assert (Herr : forall e, (1 <= e <= 4095)%Z -> ecore rsp = efferr e -> mo' = mo ->
exists a, dec_plain (fun v => (3 <=? v)%Z && (v <=? 4096)%Z) (ecore rsp) = Some a /\
match a with SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
| SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
/\ exists ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0)) /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) ent) mo end).
{ intros e He -> ->. exists (SErr e). split; [apply dec_plain_err; exact He| auto]. }
assert (Hres : forall ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0)) -> open_result mo ent rsp mo' ->
exists a, dec_plain (fun v => (3 <=? v)%Z && (v <=? 4096)%Z) (ecore rsp) = Some a /\
match a with SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
| SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
/\ exists ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0)) /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) ent) mo end).
{ intros ent Hent [(e & HIn & Hc & ->) | (Hlk & Hc & ->)].
- apply (Herr e); [apply openat_errnos_range; exact HIn | exact Hc | reflexivity].
- pose proof (alloc_fd_range mo Hminv Hlk) as Hr. rewrite Hc.
exists (SVal (bv_unsigned (alloc_fd (m_fds mo)))). split.
+ rewrite <- (Z_to_bv_bv_unsigned (alloc_fd (m_fds mo))) at 1.
apply dec_plain_val; [lia|]. apply andb_true_intro; split; apply Z.leb_le; lia.
+ rewrite Z_to_bv_bv_unsigned. split; [reflexivity|]. split; [lia|]. split; [exact Hlk|]. exists ent. auto. }
destruct (path_max <=? length path)%nat. { destruct H as [Hc ->]. apply (Herr ENAMETOOLONG); [unfold ENAMETOOLONG; lia| exact Hc| reflexivity]. }
destruct path as [|c path']. { destruct H as [Hc ->]. apply (Herr ENOENT); [unfold ENOENT; lia| exact Hc| reflexivity]. }
destruct (path_eqb (c :: path') dot_path). { apply (Hres FdDir); [left; reflexivity| exact H]. }
destruct (fs_lookup (m_fs mo) (c :: path')).
- apply (Hres (FdFile (c :: path') (Z_to_bv 64 0))); [right; reflexivity| exact H].
- destruct H as [Hc ->]. apply (Herr ENOENT); [unfold ENOENT; lia| exact Hc| reflexivity].
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
intros fd mo rsp mo' evs (-> & _ & H). split; [reflexivity|]. unfold dec_close. rewrite <- dec_plain_ecore.
destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) eqn:Hlk; destruct H as [-> ->].
- exists (SVal 0). split; [apply dec_plain_val; [lia|reflexivity]|]. repeat split; congruence.
- exists (SErr EBADF). split; [apply dec_plain_err; unfold EBADF; lia|]. auto.
Qed.

Lemma nstep_dec_ioctl : forall fd req mo rsp mo' evs,
nstep (NIoctl fd req) mo rsp mo' evs ->
dec_ioctl rsp = Some (SErr ENOTTY) /\ mo' = mo /\ evs = [].
Proof.
intros fd req mo rsp mo' evs (-> & Hc & ->). split; [|auto]. unfold dec_ioctl. rewrite <- dec_plain_ecore, Hc.
apply dec_plain_err. unfold ENOTTY; lia.
Qed.

Lemma nstep_dec_set_tid : forall mo rsp mo' evs,
minv mo ->
nstep NSetTid mo rsp mo' evs ->
evs = [] /\
exists t, dec_set_tid rsp = Some t /\ (0 < t < PID_MAX_ENVELOPE)%Z /\
((m_tid mo = Some (Z_to_bv 64 t) /\ mo' = mo) \/ (m_tid mo = None /\ mo' = with_tid (Z_to_bv 64 t) mo)).
Proof.
intros mo rsp mo' evs Hminv (-> & tw & Hc & H). split; [reflexivity|].
exists (bv_unsigned tw). rewrite Z_to_bv_bv_unsigned.
assert (Hr : (0 < bv_unsigned tw < PID_MAX_ENVELOPE)%Z).
{ destruct (m_tid mo) as [t0|] eqn:E.
- destruct H as [-> _]. destruct Hminv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MT & _). exact (MT _ E).
- exact (proj1 H). }
split.
- rewrite <- dec_set_tid_ecore, Hc. unfold dec_set_tid, eff0.
destruct Hr as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. rewrite H1, H2. reflexivity.
- split; [exact Hr|]. destruct (m_tid mo) as [t0|]; destruct H as [H0 ->]; [left; subst; auto| right; auto].
Qed.

Lemma nstep_exit_none : forall c mo rsp mo' evs, nstep (NExit c) mo rsp mo' evs -> False.
Proof. intros c mo rsp mo' evs H. exact H. Qed.

Lemma m_vmmaps_forget_vm_ranges : forall rs m, m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof. induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma m_vmmaps_with_brk_next : forall m req r,
m_vmmaps (with_brk_next m req r) = brk_model_next (m_vmmaps m) req r.
Proof. intros. unfold with_brk_next. rewrite m_vmmaps_forget_vm_ranges, m_vmmaps_with_vmmaps. reflexivity. Qed.

Lemma brk_page_range_empty : forall lo hi, (hi <= lo)%Z -> brk_page_range lo hi = [].
Proof. intros lo hi H. unfold brk_page_range. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. Qed.

Lemma brk_model_next_same : forall h req, brk_model_next h req (vm_brk h) = h.
Proof.
intros h req. unfold brk_model_next, brk_maps_next, brk_grants, brk_is_grow, brk_unmaps.
rewrite Z.ltb_irrefl, !andb_false_r. cbn [app].
cbv zeta. rewrite brk_page_range_empty by lia.
destruct (0 <? bv_unsigned (vm_brk h))%Z; cbn [maps_subtract_ranges fold_left]; destruct h; reflexivity.
Qed.

Lemma nstep_dec_brk0 : forall mo rsp mo' evs,
nstep (NBrk 0) mo rsp mo' evs ->
evs = [] /\ dec_brk0 rsp = Some (bv_unsigned (vm_brk (m_vmmaps mo))) /\ vm_only mo mo'
/\ m_vmmaps mo' = m_vmmaps mo.
Proof.
intros mo rsp mo' evs H.
pose proof (nstep_mm_vm_only (NBrk 0) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|].
apply (proj1 (nstep_brk_iff _ _ _ _ _)) in H as [_ (r & Hr & _ & -> & ->)].
unfold brk_r_ok in Hr. change (w_is0 (Z_to_bv 64 0)) with true in Hr. cbn [orb] in Hr. apply bv_eqb_eq in Hr. subst r.
split; [|split; [exact Hv|]].
- unfold dec_brk0, brk_zeros, brk_is_grow. change (w_is0 (Z_to_bv 64 0)) with true. cbn [negb andb].
unfold brk_unmaps. cbv zeta. rewrite brk_page_range_empty by lia. destruct (0 <? _)%Z; reflexivity.
- rewrite m_vmmaps_with_brk_next. apply brk_model_next_same.
Qed.

Lemma nstep_dec_brk : forall req mo rsp mo' evs,
let h := m_vmmaps mo in
(0 < bv_unsigned (vm_brk h))%Z ->
(bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h))%Z ->
(bv_unsigned (vm_brk h) <= req < 2^64)%Z ->
nstep (NBrk req) mo rsp mo' evs ->
evs = [] /\ vm_only mo mo' /\
exists a, dec_brk (bv_unsigned (vm_brk h)) req rsp = Some a /\
match a with
| BrkSame => m_vmmaps mo' = h
| BrkGrown => bv_unsigned (vm_brk h) < req /\
m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (brk_grants (Z_to_bv 64 req) (Z_to_bv 64 req) (vm_brk h) ++ vm_maps h)
(vm_noaccess h) (vm_start_brk h) (Z_to_bv 64 req) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
end.
Proof.
intros req mo rsp mo' evs h Hb Hsb Hreq H.
pose proof (nstep_mm_vm_only (NBrk req) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
apply (proj1 (nstep_brk_iff _ _ _ _ _)) in H as [_ (r & Hr & _ & -> & ->)].
rewrite m_vmmaps_with_brk_next. fold h.
unfold brk_r_ok in Hr. cbv zeta in Hr. fold h in Hr. rewrite w_is0_lit in Hr by lia.
replace (req =? 0)%Z with false in Hr by (symmetry; apply Z.eqb_neq; lia).
unfold min_brk in Hr. rewrite unsigned_lit in Hr by lia.
replace (req <? bv_unsigned (vm_start_brk h))%Z with false in Hr by (symmetry; apply Z.ltb_ge; lia).
replace (req <? bv_unsigned (vm_brk h))%Z with false in Hr by (symmetry; apply Z.ltb_ge; lia).
cbn [orb] in Hr. apply andb_prop in Hr as [Hr _].
assert (Hr' : r = Z_to_bv 64 req \/ r = vm_brk h).
{ apply orb_prop in Hr as [E|E]; apply bv_eqb_eq in E; auto. }
assert (Hus : brk_unmaps r (vm_brk h) = []).
{ unfold brk_unmaps. cbv zeta. rewrite brk_page_range_empty; [destruct (0 <? _)%Z; reflexivity|].
apply page_round_up_Z_mono. destruct Hr' as [-> | ->]; [rewrite unsigned_lit by lia|]; lia. }
destruct (Z.eq_dec req (bv_unsigned (vm_brk h))) as [Ereq | Hne].
-
assert (Hr'' : r = vm_brk h). { destruct Hr' as [-> | ->]; [subst req; apply Z_to_bv_bv_unsigned| reflexivity]. }
subst r. exists BrkSame. split.
+ unfold dec_brk. rewrite Hus, Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
+ apply brk_model_next_same.
- destruct Hr' as [-> | ->].
+ exists BrkGrown. rewrite Hus. split; [|split; [lia|]].
* unfold dec_brk. rewrite unsigned_lit by lia.
replace (req =? bv_unsigned (vm_brk h))%Z with false by (symmetry; apply Z.eqb_neq; lia).
cbn [andb]. rewrite Z.eqb_refl.
unfold brk_zeros, brk_is_grow. rewrite w_is0_lit by lia.
replace (req =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
replace (0 <? bv_unsigned (vm_brk h))%Z with true by (symmetry; apply Z.ltb_lt; lia).
rewrite unsigned_lit by lia.
replace (bv_unsigned (vm_brk h) <? req)%Z with true by (symmetry; apply Z.ltb_lt; lia).
cbn [negb andb]. unfold brk_page_range, brk_new_pages, zeros_of, wa.
destruct (_ <? _)%Z; rewrite listNN_eqb_refl; reflexivity.
* unfold brk_model_next, brk_maps_next. rewrite Hus. rewrite unsigned_lit by lia.
replace (req <? bv_unsigned (vm_brk h))%Z with false by (symmetry; apply Z.ltb_ge; lia).
rewrite andb_false_r. reflexivity.
+ exists BrkSame. rewrite Hus. split.
* unfold dec_brk. rewrite Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
* apply brk_model_next_same.
Qed.

Definition covered (maps : list (word * word)) (iv : Z * Z) : Prop :=
exists e sz, In (e, sz) maps /\ (bv_unsigned e <= fst iv)%Z /\ (snd iv <= bv_unsigned e + bv_unsigned sz)%Z.

Lemma region_free_In_disj : forall maps a n e sz,
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
pose proof (region_free_In_disj _ _ _ _ _ Hrf He) as [H|H].
- apply orb_true_intro. left. apply Z.leb_le. lia.
- apply orb_true_intro. right. apply Z.leb_le. lia.
Qed.

Lemma mmap_len_bound : forall len, (0 < len)%Z -> (len <= mmap_len len < len + 4096)%Z.
Proof. intros len H. unfold mmap_len, page_round_up_Z, page_size. split; [|]; nia || lia. Qed.

Lemma mmap_errnos_ENOMEM : forall e, In e mmap_errnos -> e = ENOMEM.
Proof. intros e H. cbn in H. destruct H as [<-|[]]. reflexivity. Qed.

Lemma nstep_dec_mmap : forall ceil len avoid mo rsp mo' evs,
let h := m_vmmaps mo in
(0 < len)%Z -> (mmap_len len < 2^64)%Z ->
(alloc_top h <= ceil)%Z ->
Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
nstep (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
evs = [] /\ vm_only mo mo' /\
exists x, dec_mmap ceil len avoid rsp = Some x /\
match x with
| MmErr e => e = ENOMEM /\ mo' = mo
/\ mmap_grant_refusable (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) mo (mmap_len len) = true
| MmOk a => mmap_addr_ok ceil len avoid a = true
/\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
/\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
(vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
end.
Proof.
intros ceil len avoid mo rsp mo' evs h Hlen Hlen2 Htop Hcov H.
pose proof (mmap_len_bound len Hlen) as Hb.
pose proof (nstep_mm_vm_only (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs eq_refl H) as [Hv ->].
split; [reflexivity|]. split; [exact Hv|].
apply (proj1 (nstep_mmap_spec _ _ _ _ _ _ _ _)) in H as [_ H].
apply (proj1 (mmap_rw_outcome (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 (PROT_READ + PROT_WRITE)) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))
(Z_to_bv 64 (-1)) (Z_to_bv 64 0) _ _ _ ltac:(rewrite w_is0_lit by lia; apply Z.eqb_neq; lia) eq_refl)) in H.
fold h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H.
destruct H as [(Hforced & e & He & E) | (a & (Hal & Hpos & Hce & Hrf & _) & E)]; apply Ok_inj in E as (-> & -> & _).
- apply mmap_errnos_ENOMEM in He. subst e. exists (MmErr ENOMEM). split; [|auto].
unfold dec_mmap. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
- assert (Hok : mmap_addr_ok ceil len avoid (bv_unsigned a) = true).
{ unfold mmap_addr_ok. rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
rewrite (proj2 (Z.leb_le (bv_unsigned a + mmap_len len) ceil)) by lia. cbn [andb].
rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact Hrf| exact Hcov]. }
exists (MmOk (bv_unsigned a)). split.
+ unfold dec_mmap. rewrite !bv_eqb_refl, Hok. reflexivity.
+ rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact Hrf|].
unfold with_mmap_backing.
match goal with |- context [mmap_noreserve_b ?f] => replace (mmap_noreserve_b f) with false by reflexivity end.
cbv iota. rewrite m_vmmaps_with_vmmaps. reflexivity.
Qed.

Lemma nstep_dec_mmap_none : forall ceil len avoid mo rsp mo' evs,
let h := m_vmmaps mo in
(0 < len)%Z -> (mmap_len len < 2^64)%Z ->
(alloc_top h <= ceil)%Z ->
Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
nstep (NMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
evs = [] /\ vm_only mo mo' /\
exists x, dec_mmap_none ceil len avoid rsp = Some x /\
match x with
| MmErr e => e = ENOMEM /\ mo' = mo
/\ mmap_reserve_refusable mo (mmap_len len) = true
| MmOk a => mmap_addr_ok ceil len avoid a = true
/\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
/\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess h)
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
end.
Proof.
intros ceil len avoid mo rsp mo' evs h Hlen Hlen2 Htop Hcov H.
pose proof (mmap_len_bound len Hlen) as Hb.
pose proof (nstep_mm_vm_only (NMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs eq_refl H) as [Hv ->].
split; [reflexivity|]. split; [exact Hv|].
apply (proj1 (nstep_mmap_spec _ _ _ _ _ _ _ _)) in H as [_ H].
apply (proj1 (mmap_noaccess_outcome (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))
(Z_to_bv 64 (-1)) (Z_to_bv 64 0) _ _ _ ltac:(rewrite w_is0_lit by lia; apply Z.eqb_neq; lia) eq_refl eq_refl)) in H.
fold h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H.
destruct H as [(Hforced & e & He & E) | (a & (Hal & Hpos & Hce & Hrf) & E)]; apply Ok_inj in E as (-> & -> & _).
- apply mmap_errnos_ENOMEM in He. subst e. exists (MmErr ENOMEM). split; [|auto].
unfold dec_mmap_none. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
- assert (Hok : mmap_addr_ok ceil len avoid (bv_unsigned a) = true).
{ unfold mmap_addr_ok. rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
rewrite (proj2 (Z.leb_le (bv_unsigned a + mmap_len len) ceil)) by lia. cbn [andb].
rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact Hrf| exact Hcov]. }
exists (MmOk (bv_unsigned a)). split.
+ unfold dec_mmap_none. rewrite !bv_eqb_refl, Hok. reflexivity.
+ rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact Hrf|].
unfold with_mmap_backing.
match goal with |- context [mmap_noreserve_b ?f] => replace (mmap_noreserve_b f) with false by reflexivity end.
cbv iota. rewrite m_vmmaps_with_vmmaps. reflexivity.
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
pose proof (nstep_mm_vm_only (NMunmap addr len) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
apply (proj1 (nstep_munmap_iff _ _ _ _ _ _)) in H as [_ H]. unfold munmap_out in H.
fold a h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H. cbv zeta in H.
destruct (negb (bv_unsigned a mod page_size =? 0)%Z || w_is0 (Z_to_bv 64 len)).
{ apply Ok_inj in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
unfold dec_munmap. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
destruct (TASK_SIZE <? _)%Z.
{ apply Ok_inj in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
unfold dec_munmap. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
destruct (map_has (vm_maps h) a n) eqn:Hhas.
- apply Ok_inj in H as (-> & -> & _). exists (RgDone true). split; [| split; [reflexivity|]].
+ unfold dec_munmap. subst a n. rewrite !bv_eqb_refl. reflexivity.
+ unfold with_mmap_destroyed, vm_forget_range. unfold m_vmmaps at 1. cbn. reflexivity.
- destruct (munmap_free_ok h a (mmap_len len)) eqn:Hfree; [| exfalso; symmetry in H; exact (Unmodeled_Ok _ _ _ H)].
apply Ok_inj in H as (-> & -> & _). exists (RgDone false). split; [reflexivity|]. split; [reflexivity|].
unfold munmap_free_ok in Hfree. apply andb_prop in Hfree as [Hfree _]. subst n. exact Hfree.
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

/\ (addr mod 4096 = 0 -> addr + mmap_len len < 2^64 -> e = ENOMEM /\ mprotect_refusable mo a n = true)%Z
| RgDone false => mo' = mo
| RgDone true => map_contains (vm_noaccess h) a n = true /\ map_contains (vm_maps h) a n = true
/\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
(maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
end.
Proof.
intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 H.
pose proof (mmap_len_bound len Hlen) as Hb.
pose proof (nstep_mm_vm_only (NMprotect addr len (PROT_READ + PROT_WRITE)) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
apply (proj1 (nstep_mprotect_spec _ _ _ _ _ _ _)) in H as [_ H]. apply (proj1 (mprotect_outcome _ _ _ _ _ _)) in H. unfold mprotect_out in H.
fold a h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H. cbv zeta in H.
change (mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with false in H.
change (mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with true in H. cbv iota in H.
assert (Hau : bv_unsigned a = addr) by (subst a; apply unsigned_lit; lia).
destruct (negb (bv_unsigned a mod page_size =? 0)%Z) eqn:Hal.
{ apply Ok_inj in H as (-> & -> & _). exists (RgErr EINVAL). split; [|split; [auto|split; [reflexivity|]]].
- unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity.
- intros Hm _. exfalso. apply negb_true_iff, Z.eqb_neq in Hal. rewrite Hau in Hal. change page_size with 4096%Z in Hal. exact (Hal Hm). }
rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
destruct (two_pow_64 <=? _)%Z eqn:Hwrap.
{ apply Ok_inj in H as (-> & -> & _). exists (RgErr ENOMEM). split; [|split; [auto|split; [reflexivity|]]].
- unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
- intros _ Hw. exfalso. apply Z.leb_le in Hwrap. rewrite Hau in Hwrap. unfold two_pow_64 in Hwrap. lia. }
destruct (map_contains (vm_noaccess h) a n && map_contains (vm_maps h) a n) eqn:Hc.
- destruct H as [(Hforced & e & He & E) | (Hbud & E)]; apply Ok_inj in E as (-> & -> & _).
+ cbn in He. destruct He as [<-|[]]. exists (RgErr ENOMEM). split; [|split; [auto|split; [reflexivity|]]].
* unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
* intros _ _. split; [reflexivity| exact Hforced].
+ apply andb_prop in Hc as [Hc1 Hc2]. exists (RgDone true). split.
* unfold dec_mprotect. subst a n. rewrite !bv_eqb_refl. reflexivity.
* split; [exact Hc1|]. split; [exact Hc2|]. unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps. reflexivity.
- destruct (map_contains (vm_maps h) a n && region_free (vm_noaccess h) a n); [| exfalso; symmetry in H; exact (Unmodeled_Ok _ _ _ H)].
apply Ok_inj in H as (-> & -> & _). exists (RgDone false). split; [reflexivity| reflexivity].
Qed.
