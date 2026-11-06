(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QlEo_c1 QWxq_c1 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import QsjA QEpW QZDE QlEo_c1.Mq0 QWxq_c1.Mq1.
Import ListNotations.
Open Scope bv_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition errno_of (r : word) : option Z :=
if (2^64 - 4095 <=? bv_unsigned r)%Z then Some (2^64 - bv_unsigned r)%Z else None.

#[using="Type"] Lemma errno_of_Some : forall r e, errno_of r = Some e -> r = errno_ret e /\ (1 <= e <= 4095)%Z.
Proof.
intros r e H. unfold errno_of in H. pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [|discriminate]. inversion H; subst.
split; [|lia]. apply bv_eq. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
replace (- (2 ^ 64 - bv_unsigned r))%Z with (bv_unsigned r + (-1) * 2^64)%Z by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma errno_of_errno_ret : forall e, (1 <= e <= 4095)%Z -> errno_of (errno_ret e) = Some e.
Proof.
intros e He. unfold errno_of. rewrite errno_ret_unsigned by lia. unfold two_pow_64.
destruct (Z.leb_spec0 (2^64 - 4095) (2^64 - e)); [|lia]. f_equal. lia.
Qed.

#[using="Type"] Lemma errno_of_small : forall r, (bv_unsigned r <= 2^64 - 4096)%Z -> errno_of r = None.
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [lia|reflexivity]. Qed.

#[using="Type"] Lemma errno_of_lit : forall z, (0 <= z <= 2^64 - 4096)%Z -> errno_of (Z_to_bv 64 z) = None.
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

#[using="Type"] Lemma dec_plain_Some : forall ok rsp a, dec_plain ok rsp = Some a ->
match a with
| SErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
| SVal v => rsp = eff0 (Z_to_bv 64 v) /\ ok v = true /\ (0 <= v <= 2^64 - 4096)%Z
end.
Proof.
intros ok [r ws zs us cs cis] a H. unfold dec_plain in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct cis; [|discriminate].
destruct (errno_of r) as [e|] eqn:E.
- inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
- destruct (ok (bv_unsigned r)) eqn:Hok; [|discriminate]. inversion H; subst.
pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
unfold errno_of in E. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [discriminate|].
unfold eff0. rewrite Z_to_bv_bv_unsigned. repeat split; try reflexivity; try exact Hok; lia.
Qed.

#[using="Type"] Lemma dec_plain_err : forall ok e, (1 <= e <= 4095)%Z -> dec_plain ok (efferr e) = Some (SErr e).
Proof. intros ok e He. unfold dec_plain, efferr, eff0. rewrite errno_of_errno_ret by lia. reflexivity. Qed.

#[using="Type"] Lemma dec_plain_val : forall ok z, (0 <= z <= 2^64 - 4096)%Z -> ok z = true ->
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

#[using="Type"] Lemma dec_read_Some : forall buf count rsp a, (0 <= count)%Z -> dec_read buf count rsp = Some a ->
match a with
| RdErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
| RdData bs => rsp = mkEffect (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) []
/\ (Z.of_nat (length bs) <= count)%Z
end.
Proof.
intros buf count [r ws zs us cs cis] a Hc H. unfold dec_read in H.
destruct ws as [|[a0 bs] [|? ?]]; try discriminate.
- destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct cis; [|discriminate].
destruct (errno_of r) as [e|] eqn:E.
+ inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
+ destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst. cbn.
split; [|lia]. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
- destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct cis; [|discriminate].
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
| mkEffectU r [] [] [] [] [] => if (bv_unsigned r =? count)%Z then Some count else None
| _ => None
end.
Definition dec_write := dec_count.
Definition dec_writev := dec_count.

#[using="Type"] Lemma dec_count_Some : forall count rsp a, dec_count count rsp = Some a ->
a = count /\ rsp = eff0 (Z_to_bv 64 count) /\ (0 <= count < 2^64)%Z.
Proof.
intros count [r ws zs us cs cis] a H. unfold dec_count in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct cis; [|discriminate].
destruct (Z.eqb_spec (bv_unsigned r) count); [|discriminate]. inversion H; subst.
pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
split; [reflexivity|]. split; [|lia]. unfold eff0. rewrite Z_to_bv_bv_unsigned. reflexivity.
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

#[using="Type"] Lemma dec_set_tid_Some : forall rsp t, dec_set_tid rsp = Some t ->
rsp = eff0 (Z_to_bv 64 t) /\ (0 < t < PID_MAX_ENVELOPE)%Z.
Proof.
intros [r ws zs us cs cis] t H. unfold dec_set_tid in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct cis; [|discriminate].
destruct (Z.ltb_spec0 0 (bv_unsigned r)); [|discriminate].
destruct (Z.ltb_spec0 (bv_unsigned r) PID_MAX_ENVELOPE); [|discriminate]. inversion H; subst.
unfold eff0. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

Definition dec_brk0 (rsp : resp) : option Z :=
match rsp with mkEffectU r [] [] [] [] [] => Some (bv_unsigned r) | _ => None end.

#[using="Type"] Lemma dec_brk0_Some : forall rsp b, dec_brk0 rsp = Some b -> rsp = eff0 (Z_to_bv 64 b) /\ (0 <= b < 2^64)%Z.
Proof.
intros [r ws zs us cs cis] b H. unfold dec_brk0 in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct cis; [|discriminate]. inversion H; subst.
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
else if (bv_unsigned r =? req)%Z && listNN_eqb zs (zeros_of (brk_new_pages cur req)) then Some BrkGrown
else None
| _ => None
end.

#[using="Type"] Lemma dec_brk_Some : forall cur req rsp a, dec_brk cur req rsp = Some a ->
match a with
| BrkSame => rsp = eff0 (Z_to_bv 64 cur)
| BrkGrown => rsp = mkEffect (Z_to_bv 64 req) [] (zeros_of (brk_new_pages cur req))
end.
Proof.
intros cur req [r ws zs us cs cis] a H. unfold dec_brk in H.
destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate]. destruct cis; [|destruct zs; discriminate].
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

Definition mmap_addr_ok (len : Z) (avoid : list (Z * Z)) (a : Z) : bool :=
(a mod page_size =? 0)%Z && (0 <? a)%Z && (a + mmap_len len <=? alloc_ceiling)%Z && avoids a (mmap_len len) avoid.

Definition dec_mmap (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] => match errno_of r with Some e => if (e =? 12)%Z then Some (MmErr e) else None | None => None end

| mkEffectU r [] [(a, n)] [] [] [] =>
if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
then Some (MmOk (bv_unsigned r)) else None
| _ => None
end.

Definition dec_mmap_none (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] => match errno_of r with Some e => if (e =? 12)%Z then Some (MmErr e) else None | None => None end

| mkEffectU r [] [] [(a, n)] [] [] =>
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
| MmErr e => rsp = efferr e /\ e = 12%Z
| MmOk a => rsp = mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] /\ mmap_addr_ok len avoid a = true
end.
Proof.
intros len avoid [r ws zs us cs cis] x H. unfold dec_mmap in H.
destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
- destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct cis; [|discriminate]. destruct (errno_of r) as [e|] eqn:E; [|discriminate]. destruct (Z.eqb_spec e 12); [|discriminate]. inversion H; subst.
apply errno_of_Some in E as [-> He]. auto.
- destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct cis; [|discriminate].
destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

#[using="Type"] Lemma dec_mmap_none_Some : forall len avoid rsp x, dec_mmap_none len avoid rsp = Some x ->
match x with
| MmErr e => rsp = efferr e /\ e = 12%Z
| MmOk a => rsp = mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] /\ mmap_addr_ok len avoid a = true
end.
Proof.
intros len avoid [r ws zs us cs cis] x H. unfold dec_mmap_none in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate; destruct cs; try discriminate; destruct cis; try discriminate.
- destruct (errno_of r) as [e|] eqn:E; [|discriminate]. destruct (Z.eqb_spec e 12); [|discriminate]. inversion H; subst. apply errno_of_Some in E as [-> He]. auto.
- destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
destruct (mmap_addr_ok len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

Inductive range_ans : Type := RgErr (e : Z) | RgDone (changed : bool).

Definition dec_munmap (addr len : Z) (rsp : resp) : option range_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] =>
match errno_of r with Some e => if (e =? 12)%Z then Some (RgErr e) else None
| None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
| mkEffectU r [] [] [(a, n)] [] [] =>
if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
then Some (RgDone true) else None
| _ => None
end.

Definition dec_mprotect (addr len : Z) (rsp : resp) : option range_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] =>
match errno_of r with Some e => if (e =? 12)%Z then Some (RgErr e) else None
| None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
| mkEffectU r [] [(a, n)] [] [] [] =>
if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
then Some (RgDone true) else None
| _ => None
end.

#[using="Type"] Lemma dec_munmap_Some : forall addr len rsp x, dec_munmap addr len rsp = Some x ->
match x with
| RgErr e => rsp = efferr e /\ e = 12%Z
| RgDone false => rsp = eff0 (Z_to_bv 64 0)
| RgDone true => rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] []
end.
Proof.
intros addr len [r ws zs us cs cis] x H. unfold dec_munmap in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate; destruct cs; try discriminate; destruct cis; try discriminate.
- destruct (errno_of r) as [e|] eqn:E. { destruct (Z.eqb_spec e 12); [|discriminate]. inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
- destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

#[using="Type"] Lemma dec_mprotect_Some : forall addr len rsp x, dec_mprotect addr len rsp = Some x ->
match x with
| RgErr e => rsp = efferr e /\ e = 12%Z
| RgDone false => rsp = eff0 (Z_to_bv 64 0)
| RgDone true => rsp = mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))]
end.
Proof.
intros addr len [r ws zs us cs cis] x H. unfold dec_mprotect in H.
destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
- destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct cis; [|discriminate].
destruct (errno_of r) as [e|] eqn:E. { destruct (Z.eqb_spec e 12); [|discriminate]. inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
unfold eff0. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
- destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct cis; [|discriminate]. destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

Inductive mremap_ans : Type := MrErr (e : Z) | MrInPlace | MrMoved (a : Z).

Definition mremap_eff (old oldlen newlen : Z) (x : mremap_ans) : resp -> Prop :=
fun rsp =>
match x with
| MrErr e => rsp = efferr e
| MrInPlace =>
(newlen < oldlen /\ rsp = mkEffectU (Z_to_bv 64 old) [] [] [(wa (old + newlen), Z_to_bv 64 (oldlen - newlen))] [] [])
\/ (oldlen < newlen /\ rsp = mkEffectU (Z_to_bv 64 old) [] [(wa (old + oldlen), Z_to_bv 64 (newlen - oldlen))] [] [] [])
| MrMoved a =>
oldlen < newlen /\
rsp = mkEffectU (Z_to_bv 64 a) [] [(wa (a + oldlen), Z_to_bv 64 (newlen - oldlen))] [(wa old, Z_to_bv 64 oldlen)]
[mkCopy (wa old) (wa a) (Z_to_bv 64 oldlen)] []
end.

Definition dec_mremap (old oldlen newlen : Z) (avoid : list (Z * Z)) (rsp : resp) : option mremap_ans :=
match rsp with
| mkEffectU r [] zs us cs [] =>
match errno_of r with
| Some e => match zs, us, cs with [], [], [] => if (e =? 12)%Z then Some (MrErr e) else None | _, _, _ => None end

| None =>
if bv_eqb r (Z_to_bv 64 old) then
match zs, us, cs with
| [], [(ua, un)], [] =>
if (newlen <? oldlen)%Z && bv_eqb ua (wa (old + newlen)) && bv_eqb un (Z_to_bv 64 (oldlen - newlen))
then Some MrInPlace else None
| [(za, zn)], [], [] =>
if (oldlen <? newlen)%Z && bv_eqb za (wa (old + oldlen)) && bv_eqb zn (Z_to_bv 64 (newlen - oldlen))
then Some MrInPlace else None
| _, _, _ => None
end
else
match zs, us, cs with
| [(za, zn)], [(ua, un)], [c] =>
if (oldlen <? newlen)%Z
&& bv_eqb za (wa (bv_unsigned r + oldlen)) && bv_eqb zn (Z_to_bv 64 (newlen - oldlen))
&& bv_eqb ua (wa old) && bv_eqb un (Z_to_bv 64 oldlen)
&& bv_eqb (copy_src c) (wa old) && bv_eqb (copy_dst c) r && bv_eqb (copy_len c) (Z_to_bv 64 oldlen)
&& (bv_unsigned r mod 4096 =? 0)%Z && (0 <? bv_unsigned r)%Z
&& (bv_unsigned r + newlen <=? alloc_ceiling)%Z && avoids (bv_unsigned r) newlen avoid
then Some (MrMoved (bv_unsigned r)) else None
| _, _, _ => None
end
end
| _ => None
end.

#[using="Type"] Lemma dec_mremap_Some : forall old oldlen newlen avoid rsp x,
dec_mremap old oldlen newlen avoid rsp = Some x ->
mremap_eff old oldlen newlen x rsp /\
match x with
| MrErr e => e = 12%Z
| MrInPlace => True
| MrMoved a => (a mod 4096 = 0 /\ 0 < a /\ a + newlen <= alloc_ceiling)%Z /\ avoids a newlen avoid = true /\ a <> old mod 2^64
end.
Proof.
intros old oldlen newlen avoid [r ws zs us cs cis] x H. unfold dec_mremap in H.
destruct ws; [|discriminate]. destruct cis; [|destruct zs as [|[? ?] [|? ?]]; destruct us as [|[? ?] [|? ?]]; destruct cs as [|? [|? ?]]; discriminate].
destruct (errno_of r) as [e|] eqn:E.
- destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
destruct (Z.eqb_spec e 12) as [E12|]; [|discriminate].
inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity| reflexivity].
- destruct (bv_eqb r (Z_to_bv 64 old)) eqn:ER.
+ apply bv_eqb_eq in ER. subst r.
destruct zs as [|[za zn] [|? ?]]; destruct us as [|[ua un] [|? ?]]; destruct cs as [|? [|? ?]]; try discriminate.
* destruct (newlen <? oldlen)%Z eqn:L; [|discriminate]. apply Z.ltb_lt in L.
destruct (bv_eqb ua _) eqn:E1; [|discriminate]. destruct (bv_eqb un _) eqn:E2; [|discriminate].
cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
split; [|exact I]. left. split; [exact L| reflexivity].
* destruct (oldlen <? newlen)%Z eqn:L; [|discriminate]. apply Z.ltb_lt in L.
destruct (bv_eqb za _) eqn:E1; [|discriminate]. destruct (bv_eqb zn _) eqn:E2; [|discriminate].
cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
split; [|exact I]. right. split; [exact L| reflexivity].
+ destruct zs as [|[za zn] [|? ?]]; destruct us as [|[ua un] [|? ?]]; destruct cs as [|[csrc cdst clen] [|? ?]]; try discriminate.
cbn [copy_src copy_dst copy_len] in H.
destruct (oldlen <? newlen)%Z eqn:L; [|discriminate]. apply Z.ltb_lt in L.
destruct (bv_eqb za _) eqn:E1; [|discriminate]. destruct (bv_eqb zn _) eqn:E2; [|discriminate].
destruct (bv_eqb ua _) eqn:E3; [|discriminate]. destruct (bv_eqb un _) eqn:E4; [|discriminate].
destruct (bv_eqb csrc _) eqn:E5; [|discriminate]. destruct (bv_eqb cdst _) eqn:E6; [|discriminate].
destruct (bv_eqb clen _) eqn:E7; [|discriminate].
destruct (Z.eqb_spec (bv_unsigned r mod 4096) 0); [|discriminate].
destruct (Z.ltb_spec0 0 (bv_unsigned r)); [|discriminate].
destruct (Z.leb_spec0 (bv_unsigned r + newlen) alloc_ceiling); [|discriminate].
destruct (avoids (bv_unsigned r) newlen avoid) eqn:AV; [|discriminate].
cbn [andb] in H. inversion H; subst.
apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. apply bv_eqb_eq in E3. apply bv_eqb_eq in E4.
apply bv_eqb_eq in E5. apply bv_eqb_eq in E6. apply bv_eqb_eq in E7. subst za zn ua un csrc cdst clen.
split.
* split; [exact L|]. unfold wa. rewrite Z_to_bv_bv_unsigned. reflexivity.
* split; [auto|]. split; [exact AV|].
intros EQ. assert (X : bv_eqb r (Z_to_bv 64 old) = true); [|congruence].
unfold bv_eqb. rewrite unsigned_lit_wrap, <- EQ. apply Z.eqb_refl.
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
- destruct H as [-> _]. destruct Hminv as (_ & _ & _ & _ & _ & _ & _ & _ & MT). exact (MT _ E).
- exact (proj1 H). }
split.
- unfold dec_set_tid, eff0. destruct Hr as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. rewrite H1, H2. reflexivity.
- split; [exact Hr|]. destruct (m_tid mo) as [t0|]; destruct H as [H0 ->]; [left; subst; auto| right; auto].
Qed.

#[using="Type"] Lemma nstep_exit_none : forall c mo rsp mo' evs, nstep (NExit c) mo rsp mo' evs -> False.
Proof. intros c mo rsp mo' evs H. exact H. Qed.

#[using="Type"] Lemma nstep_dec_brk0 : forall mo rsp mo' evs,
nstep (NBrk 0) mo rsp mo' evs ->
evs = [] /\ dec_brk0 rsp = Some (bv_unsigned (vm_brk (m_vmmaps mo))) /\ vm_only mo mo'
/\ vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo).
Proof.
intros mo rsp mo' evs H.
pose proof (nstep_mm_vm_only (NBrk 0) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|].
apply nstep_brk_iff in H. destruct rsp as [r ws zs us cs cis]. unfold check_brk in H.
destruct ws; [|discriminate]. destruct cs; [|destruct zs; discriminate]. destruct cis; [|destruct zs; discriminate].
destruct (brk_r_ok mo (Z_to_bv 64 0) r && listNN_eqb zs _ && listNN_eqb us _) eqn:E; [|destruct zs; discriminate].
apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
unfold brk_r_ok in E1. change (w_is0 (Z_to_bv 64 0)) with true in E1. cbn [orb] in E1. apply bv_eqb_eq in E1. subst r.
apply listNN_eqb_eq in E2. apply listNN_eqb_eq in E3.
unfold brk_zeros, brk_is_grow in E2. change (w_is0 (Z_to_bv 64 0)) with true in E2. cbn [negb andb] in E2. subst zs.
unfold brk_unmaps, brk_page_range in E3. rewrite Z.ltb_irrefl in E3. destruct (0 <? _)%Z; subst us.
all: cbv iota beta in H; inversion H; subst; split; [reflexivity|]; split; [exact Hv|];
rewrite m_vmmaps_with_brk_next; reflexivity.
Qed.

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
pose proof (nstep_mm_vm_only (NBrk req) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
apply nstep_brk_iff in H. destruct rsp as [r ws zs us cs cis]. unfold check_brk in H.
destruct ws; [|discriminate]. destruct cs; [|destruct zs; discriminate]. destruct cis; [|destruct zs; discriminate].
destruct (brk_r_ok mo (Z_to_bv 64 req) r && listNN_eqb zs _ && listNN_eqb us _) eqn:E; [|destruct zs; discriminate].
replace mo' with (with_brk_next mo (Z_to_bv 64 req) r) by (destruct zs; inversion H; reflexivity). clear H.
rewrite m_vmmaps_with_brk_next. cbn [brk_model_next vm_brk].
apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
apply listNN_eqb_eq in E2. apply listNN_eqb_eq in E3. subst zs us.
unfold brk_r_ok in E1. fold h in E1 |- *. unfold min_brk in E1. rewrite w_is0_lit in E1 by lia.
replace (req =? 0)%Z with false in E1 by (symmetry; apply Z.eqb_neq; lia).
rewrite unsigned_lit in E1 by lia.
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
-
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

#[using="Type"] Lemma nstep_dec_mmap : forall len avoid mo rsp mo' evs,
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
/\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
(vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
end.
Proof.
intros len avoid mo rsp mo' evs h Hlen Hlen2 Hceil Hcov H.
pose proof (mmap_len_bound len Hlen) as Hb.
pose proof (nstep_mm_vm_only (NMmap 0 len _ _) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
apply nstep_mmap_iff in H as [_ H]. destruct rsp as [r ws zs us cs cis]. unfold check_mmap in H.
replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H by (vm_compute; reflexivity).
replace (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true in H by (vm_compute; reflexivity).
rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
replace (mmap_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with true in H by (vm_compute; reflexivity).
cbn [negb] in H. cbv iota beta in H. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
destruct cs; [|destruct zs; discriminate]. destruct cis; [|destruct zs; discriminate].
fold h in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.

destruct (errno_ret_in mmap_errnos r) eqn:Herr.
- destruct zs; [|discriminate]. inversion H; subst.
apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
- cbv zeta in H.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
inversion H; subst; clear H.
apply andb_prop in E as [E E7]. apply andb_prop in E as [E E6]. apply andb_prop in E as [E E4].
apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
apply listNN_eqb_eq in E7. subst zs. rewrite Hceil in E3.
assert (Hok : mmap_addr_ok len avoid (bv_unsigned r) = true).
{ unfold mmap_addr_ok. rewrite E1, E2, E3. cbn [andb].
rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
exists (MmOk (bv_unsigned r)). split.
+ unfold dec_mmap. rewrite !bv_eqb_refl, Hok. reflexivity.
+ rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E4|].
rewrite m_vmmaps_with_mmap_backing, m_vmmaps_with_vmmaps. reflexivity.
Qed.

#[using="Type"] Lemma nstep_dec_mmap_none : forall len avoid mo rsp mo' evs,
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
intros len avoid mo rsp mo' evs h Hlen Hlen2 Hceil Hcov H.
pose proof (mmap_len_bound len Hlen) as Hb.
pose proof (nstep_mm_vm_only (NMmap 0 len _ _) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
apply nstep_mmap_iff in H as [_ H]. destruct rsp as [r ws zs us cs cis]. unfold check_mmap in H.
replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H by (vm_compute; reflexivity).
replace (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true in H by (vm_compute; reflexivity).
rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
replace (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with false in H by (vm_compute; reflexivity).
replace (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with true in H by (vm_compute; reflexivity).
cbn [negb] in H. cbv iota beta in H. destruct ws; [|discriminate]. destruct zs; [|destruct us; discriminate].
destruct cs; [|destruct us; discriminate]. destruct cis; [|destruct us; discriminate].
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
apply listNN_eqb_eq in E6. subst us. rewrite Hceil in E3.
assert (Hok : mmap_addr_ok len avoid (bv_unsigned r) = true).
{ unfold mmap_addr_ok. rewrite E1, E2, E3. cbn [andb].
rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
exists (MmOk (bv_unsigned r)). split.
+ unfold dec_mmap_none. rewrite !bv_eqb_refl, Hok. reflexivity.
+ rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E4|].
rewrite m_vmmaps_with_mmap_backing, m_vmmaps_with_vmmaps. reflexivity.
Qed.

#[using="Type"] Lemma nstep_dec_munmap : forall addr len mo rsp mo' evs,
let h := m_vmmaps mo in
let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
(0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z -> (addr mod 4096 = 0)%Z ->
(addr + mmap_len len <= alloc_ceiling)%Z ->
nstep (NMunmap addr len) mo rsp mo' evs ->
evs = [] /\ vm_only mo mo' /\
exists x, dec_munmap addr len rsp = Some x /\
match x with
| RgErr e => False
| RgDone false => mo' = mo /\ munmap_free_ok h a (mmap_len len) = true
| RgDone true => map_has (vm_maps h) a n = true
/\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
(maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
end.
Proof.
intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 HAL Hceil H. pose proof alloc_ceiling_le as HCL.
pose proof (mmap_len_bound len Hlen) as Hb.
pose proof (nstep_mm_vm_only (NMunmap addr len) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
apply nstep_munmap_iff in H. destruct rsp as [r ws zs us cs cis]. unfold check_munmap in H.
fold a h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H.
replace (negb (bv_unsigned a mod page_size =? 0)%Z || w_is0 (Z_to_bv 64 len)) with false in H.
2:{ subst a. rewrite unsigned_lit by lia. unfold page_size. rewrite (proj2 (Z.eqb_eq _ _) HAL). rewrite w_is0_lit by lia. replace (len =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
cbv zeta in H.
replace (TASK_SIZE <? bv_unsigned a + mmap_len len)%Z with false in H
by (symmetry; apply Z.ltb_ge; subst a; rewrite unsigned_lit by lia; unfold TASK_SIZE; lia).
destruct (map_has (vm_maps h) a n) eqn:Hhas.
- destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|destruct us; discriminate]. destruct cis; [|destruct us; discriminate].
match type of H with (match us with _ => _ end) = _ => idtac | (if ?c then _ else _) = _ => idtac end.
destruct (w_is0 r && listNN_eqb us [(a, n)]) eqn:E; [|destruct us; discriminate].
replace mo' with (with_mmap_destroyed a n
(mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
(maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo) by (destruct us; inversion H; reflexivity).
clear H.
apply andb_prop in E as [E1 E2]. apply listNN_eqb_eq in E2. subst us. unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
exists (RgDone true). split; [|split; [reflexivity| apply m_vmmaps_with_mmap_destroyed]].
unfold dec_munmap. subst a n. rewrite !bv_eqb_refl. reflexivity.
- destruct (munmap_free_ok h a (mmap_len len)) eqn:Hrf; [|discriminate].
apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgDone false). split; [reflexivity| auto].
Qed.

#[using="Type"] Lemma nstep_dec_mprotect : forall addr len mo rsp mo' evs,
let h := m_vmmaps mo in
let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
(0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z -> (addr mod 4096 = 0)%Z ->
nstep (NMprotect addr len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
evs = [] /\ vm_only mo mo' /\
exists x, dec_mprotect addr len rsp = Some x /\
match x with
| RgErr e => e = ENOMEM /\ mo' = mo
| RgDone false => mo' = mo
| RgDone true => map_contains (vm_noaccess h) a n = true /\ map_contains (vm_maps h) a n = true
/\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
(maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
end.
Proof.
intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 HAL H.
pose proof (mmap_len_bound len Hlen) as Hb.
pose proof (nstep_mm_vm_only (NMprotect addr len _) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
apply nstep_mprotect_iff in H. destruct rsp as [r ws zs us cs cis]. unfold check_mprotect in H.
fold a h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H.
replace (mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with false in H by (vm_compute; reflexivity).
replace (mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with true in H by (vm_compute; reflexivity). cbn [negb] in H. cbv iota in H.
replace (negb (bv_unsigned a mod page_size =? 0)%Z) with false in H.
2:{ subst a. rewrite unsigned_lit by lia. unfold page_size. rewrite (proj2 (Z.eqb_eq _ _) HAL). reflexivity. }
rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
destruct (two_pow_64 <=? _)%Z.
{ apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr ENOMEM). split; [|auto].
unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity. }
cbv zeta in H.
destruct (map_contains (vm_noaccess h) a n && map_contains (vm_maps h) a n) eqn:Hc.
- destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
destruct cs; [|destruct zs; discriminate]. destruct cis; [|destruct zs; discriminate].
destruct (errno_ret_in mprotect_errnos r) eqn:Herr.
+ destruct zs; [|discriminate]. inversion H; subst.
apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
exists (RgErr ENOMEM). split; [|auto]. unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
+ destruct (mprotect_budget_ok mo a n && w_is0 r && listNN_eqb zs [(a, n)]) eqn:E; [|discriminate]. inversion H; subst; clear H.
apply andb_prop in E as [E E2]. apply andb_prop in E as [_ E1].
apply listNN_eqb_eq in E2. subst zs. unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
apply andb_prop in Hc as [Hc1 Hc2].
exists (RgDone true). split; [| split; [exact Hc1| split; [exact Hc2| unfold mprotect_model_next; rewrite m_vmmaps_with_vmmaps; reflexivity]]].
unfold dec_mprotect. subst a n. rewrite !bv_eqb_refl. reflexivity.
- destruct (map_contains (vm_maps h) a n && region_free (vm_noaccess h) a n); [|discriminate].
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct cis; [|discriminate].
destruct (w_is0 r) eqn:E; [|discriminate]. inversion H; subst. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
exists (RgDone false). split; [reflexivity| reflexivity].
Qed.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
Import ListNotations.
Open Scope bv_scope.

Fixpoint u32s (ws : list word) : list byte :=
match ws with [] => [] | w :: ws' => le4 w ++ u32s ws' end.
Fixpoint u64s (ws : list word) : list byte :=
match ws with [] => [] | w :: ws' => le8 w ++ u64s ws' end.

Lemma u32s_length : forall ws, length (u32s ws) = (4 * length ws)%nat.
Proof. induction ws; cbn -[le4]; [reflexivity|]. rewrite app_length, length_le4, IHws. lia. Qed.
Lemma u64s_length : forall ws, length (u64s ws) = (8 * length ws)%nat.
Proof. induction ws; cbn -[le8]; [reflexivity|]. rewrite app_length, length_le8, IHws. lia. Qed.

Lemma u32s_app : forall a b, u32s (a ++ b) = u32s a ++ u32s b.
Proof. induction a; intros; cbn -[le4]; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.
Lemma u64s_app : forall a b, u64s (a ++ b) = u64s a ++ u64s b.
Proof. induction a; intros; cbn -[le8]; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.

Fixpoint upd {X} (l : list X) (i : nat) (x : X) : list X :=
match l, i with
| [], _ => []
| _ :: l', O => x :: l'
| y :: l', S i' => y :: upd l' i' x
end.

Lemma upd_length : forall {X} (l : list X) i x, length (upd l i x) = length l.
Proof. induction l; intros [|i] x; cbn; auto. Qed.

Lemma upd_app_split : forall {X} (l : list X) i x, (i < length l)%nat ->
exists pre y post, l = pre ++ y :: post /\ length pre = i /\ upd l i x = pre ++ x :: post.
Proof.
induction l as [|z l IH]; intros i x Hi; cbn in Hi; [lia|].
destruct i as [|i].
- exists [], z, l. repeat split; reflexivity.
- destruct (IH i x ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
exists (z :: pre), y, post. split; [rewrite E at 1; reflexivity|]. split; [cbn; lia|].
cbn. rewrite Hupd. reflexivity.
Qed.

Lemma nth_error_split : forall {X} (l : list X) i y, nth_error l i = Some y ->
exists pre post, l = pre ++ y :: post /\ length pre = i.
Proof.
induction l as [|z l IH]; intros [|i] y H; cbn in H; try discriminate.
- inversion H; subst. exists [], l. split; reflexivity.
- destruct (IH i y H) as (pre & post & -> & Hlen). exists (z :: pre), post. split; [reflexivity| cbn; lia].
Qed.

Lemma nth_error_lt : forall {X} (l : list X) i y, nth_error l i = Some y -> (i < length l)%nat.
Proof. intros X l i y H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma upd_bytes_mid : forall (a b c bs : list byte), length bs = length b ->
upd_bytes (a ++ b ++ c) (length a) bs = a ++ bs ++ c.
Proof.
intros a b c bs H. unfold upd_bytes.
rewrite firstn_app, firstn_all2, Nat.sub_diag, firstn_O, app_nil_r by lia.
rewrite skipn_app, skipn_all2 by lia. cbn [app].
replace (length a + length bs - length a)%nat with (length b) by lia.
rewrite skipn_app, skipn_all2, Nat.sub_diag by lia. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition u8arr (m : word -> option byte) (A : Z) (bs : list byte) : Prop :=
bytes_at segs m A bs /\ wr_at segs m A (Z.of_nat (length bs)).
Definition u32arr (m : word -> option byte) (A : Z) (ws : list word) : Prop :=
bytes_at segs m A (u32s ws) /\ wr_at segs m A (4 * Z.of_nat (length ws)).
Definition u64arr (m : word -> option byte) (A : Z) (ws : list word) : Prop :=
bytes_at segs m A (u64s ws) /\ wr_at segs m A (8 * Z.of_nat (length ws)).

Definition u8ro (m : word -> option byte) (A : Z) (bs : list byte) : Prop := bytes_at segs m A bs.

#[using="Type"] Lemma u8arr_read : forall m A bs (i : Z) b a,
u8arr m A bs -> nth_error bs (Z.to_nat i) = Some b -> (0 <= i)%Z -> a = wa (A + i) ->
ov_read_bytes segs m a 1 = Some [b].
Proof.
intros m A bs i b a [Hb _] Hn Hi ->.
pose proof (nth_error_lt _ _ _ Hn).
rewrite (bytes_at_read segs m A bs i 1 Hb) by lia.
destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen). rewrite E at 1.
rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed.

#[using="Type"] Lemma u8ro_read : forall m A bs (i : Z) b a,
u8ro m A bs -> nth_error bs (Z.to_nat i) = Some b -> (0 <= i)%Z -> a = wa (A + i) ->
ov_read_bytes segs m a 1 = Some [b].
Proof.
intros m A bs i b a Hb Hn Hi ->.
pose proof (nth_error_lt _ _ _ Hn).
rewrite (bytes_at_read segs m A bs i 1 Hb) by lia.
destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen). rewrite E at 1.
rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed.

#[using="Type"] Lemma u8arr_store_ok : forall m A bs (i : Z) a,
u8arr m A bs -> (0 <= i < Z.of_nat (length bs))%Z -> a = wa (A + i) ->
store_ok segs m a 1 = true.
Proof. intros m A bs i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

#[using="Type"] Lemma u8arr_write : forall m A bs (i : Z) (b : byte),
u8arr m A bs -> (0 <= i < Z.of_nat (length bs))%Z ->
u8arr (write_to_mem m (wa (A + i)) [b]) A (upd bs (Z.to_nat i) b).
Proof.
intros m A bs i b [Hb Hw] Hi. split.
- eapply bytes_at_ext. { apply (bytes_at_write_inside segs m A bs i [b] Hb); [lia| cbn; lia]. }
destruct (upd_app_split bs (Z.to_nat i) b ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
rewrite Hupd. rewrite E at 1. unfold upd_bytes. rewrite firstn_app, firstn_all2, Hlen, Nat.sub_diag by lia. cbn.
rewrite app_nil_r. f_equal. change (y :: post) with ([y] ++ post). rewrite app_assoc, skipn_app.
rewrite skipn_all2 by (rewrite app_length, Hlen; cbn; lia). rewrite app_length, Hlen. cbn.
replace (Z.to_nat i + 1 - (Z.to_nat i + 1))%nat with 0%nat by lia. reflexivity.
- rewrite upd_length. apply wr_at_write. exact Hw.
Qed.

#[using="Type"] Lemma u32s_split : forall ws i w, nth_error ws i = Some w ->
exists pre post, ws = pre ++ w :: post /\ length pre = i /\
u32s ws = u32s pre ++ le4 w ++ u32s post /\ length (u32s pre) = (4 * i)%nat.
Proof.
intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
exists pre, post. rewrite u32s_app. cbn -[le4]. rewrite u32s_length. repeat split; lia.
Qed.

#[using="Type"] Lemma u32arr_read : forall m A ws (i : Z) w a,
u32arr m A ws -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 4 * i) ->
ov_read_bytes segs m a 4 = Some (le4 w).
Proof.
intros m A ws i w a [Hb _] Hn Hi ->.
destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
replace (4 * i)%Z with (Z.of_nat (4 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i) 4 Hb).
2:{ rewrite Eu, !app_length, length_le4, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma u32arr_store_ok : forall m A ws (i : Z) a,
u32arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z -> a = wa (A + 4 * i) ->
store_ok segs m a 4 = true.
Proof. intros m A ws i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

#[using="Type"] Lemma u32arr_write : forall m A ws (i : Z) (v : word),
u32arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z ->
u32arr (write_to_mem m (wa (A + 4 * i)) (le4 v)) A (upd ws (Z.to_nat i) v).
Proof.
intros m A ws i v [Hb Hw] Hi.
destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
split.
- eapply bytes_at_ext.
{ apply (bytes_at_write_inside segs m A (u32s ws) (4 * i) (le4 v) Hb); [lia|].
rewrite length_le4, u32s_length. lia. }
rewrite Hupd, E, !u32s_app. cbn [u32s].
replace (Z.to_nat (4 * i)) with (length (u32s pre)) by (rewrite u32s_length; lia).
apply upd_bytes_mid. rewrite !length_le4. reflexivity.
- rewrite upd_length. apply wr_at_write. exact Hw.
Qed.

#[using="Type"] Lemma u64s_split : forall ws i w, nth_error ws i = Some w ->
exists pre post, ws = pre ++ w :: post /\ length pre = i /\
u64s ws = u64s pre ++ le8 w ++ u64s post /\ length (u64s pre) = (8 * i)%nat.
Proof.
intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
exists pre, post. rewrite u64s_app. cbn -[le8]. rewrite u64s_length. repeat split; lia.
Qed.

#[using="Type"] Lemma u64arr_read : forall m A ws (i : Z) w a,
u64arr m A ws -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
ov_read_bytes segs m a 8 = Some (le8 w).
Proof.
intros m A ws i w a [Hb _] Hn Hi ->.
destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read segs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma u64arr_store_ok : forall m A ws (i : Z) a,
u64arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z -> a = wa (A + 8 * i) ->
store_ok segs m a 8 = true.
Proof. intros m A ws i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.

#[using="Type"] Lemma u64arr_write : forall m A ws (i : Z) (v : word),
u64arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z ->
u64arr (write_to_mem m (wa (A + 8 * i)) (le8 v)) A (upd ws (Z.to_nat i) v).
Proof.
intros m A ws i v [Hb Hw] Hi.
destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
split.
- eapply bytes_at_ext.
{ apply (bytes_at_write_inside segs m A (u64s ws) (8 * i) (le8 v) Hb); [lia|].
rewrite length_le8, u64s_length. lia. }
rewrite Hupd, E, !u64s_app. cbn [u64s].
replace (Z.to_nat (8 * i)) with (length (u64s pre)) by (rewrite u64s_length; lia).
apply upd_bytes_mid. rewrite !length_le8. reflexivity.
- rewrite upd_length. apply wr_at_write. exact Hw.
Qed.

#[using="Type"] Lemma u8arr_frame : forall m A bs a xs,
u8arr m A bs -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
(A + Z.of_nat (length bs) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
u8arr (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs [Hb Hw] ? ? ?. split; [apply bytes_at_write_other; assumption| apply wr_at_write; assumption]. Qed.

#[using="Type"] Lemma u32arr_frame : forall m A ws a xs,
u32arr m A ws -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
(A + 4 * Z.of_nat (length ws) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
u32arr (write_to_mem m (wa a) xs) A ws.
Proof.
intros m A ws a xs [Hb Hw] ? ? ?. split; [|apply wr_at_write; assumption].
apply bytes_at_write_other; try assumption. rewrite u32s_length. lia.
Qed.

#[using="Type"] Lemma u64arr_frame : forall m A ws a xs,
u64arr m A ws -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
(A + 8 * Z.of_nat (length ws) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
u64arr (write_to_mem m (wa a) xs) A ws.
Proof.
intros m A ws a xs [Hb Hw] ? ? ?. split; [|apply wr_at_write; assumption].
apply bytes_at_write_other; try assumption. rewrite u64s_length. lia.
Qed.

#[using="Type"] Lemma u8arr_bound : forall m A bs, u8arr m A bs -> (0 <= A /\ A + Z.of_nat (length bs) <= 2^64)%Z.
Proof. intros m A bs [Hb _]. eapply bytes_at_bound; eauto. Qed.
#[using="Type"] Lemma u32arr_bound : forall m A ws, u32arr m A ws -> (0 <= A /\ A + 4 * Z.of_nat (length ws) <= 2^64)%Z.
Proof. intros m A ws [Hb _]. pose proof (bytes_at_bound _ _ _ _ Hb). rewrite u32s_length in H. lia. Qed.
#[using="Type"] Lemma u64arr_bound : forall m A ws, u64arr m A ws -> (0 <= A /\ A + 8 * Z.of_nat (length ws) <= 2^64)%Z.
Proof. intros m A ws [Hb _]. pose proof (bytes_at_bound _ _ _ _ Hb). rewrite u64s_length in H. lia. Qed.

#[using="Type"] Lemma u8ro_frame : forall m A bs a xs,
u8ro m A bs -> (0 <= a)%Z -> (a + Z.of_nat (length xs) <= 2^64)%Z ->
(A + Z.of_nat (length bs) <= a \/ a + Z.of_nat (length xs) <= A)%Z ->
u8ro (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs Hb ? ? ?. unfold u8ro. apply bytes_at_write_other; assumption. Qed.

#[using="Type"] Lemma u8arr_of_rw_cells : forall m A n bs,
rw_cells segs m A [CB n bs] -> u8arr m A bs.
Proof.
intros m A n bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hn _].
cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. subst n.
split; assumption.
Qed.

#[using="Type"] Lemma rw_cells_of_u8arr : forall m A bs,
u8arr m A bs -> rw_cells segs m A [CB (length bs) bs].
Proof.
intros m A bs [Hb Hw]. split.
- split. { cbn. split; [reflexivity|exact I]. }
cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
- cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

#[using="Type"] Lemma upd_firstn_skipn : forall {X} (l : list X) i x, (i < length l)%nat ->
upd l i x = firstn i l ++ x :: skipn (S i) l.
Proof.
intros X l. induction l as [|y l IH]; intros [|i] x Hi; cbn in Hi |- *; try lia; [reflexivity|].
rewrite IH by lia. reflexivity.
Qed.

#[using="Type"] Lemma nth_error_upd_same : forall {X} (l : list X) i x, (i < length l)%nat ->
nth_error (upd l i x) i = Some x.
Proof.
intros X l. induction l as [|y l IH]; intros [|i] x Hi; cbn in Hi |- *; try lia; [reflexivity|].
apply IH. lia.
Qed.

#[using="Type"] Lemma nth_error_upd_other : forall {X} (l : list X) i j x, i <> j ->
nth_error (upd l i x) j = nth_error l j.
Proof.
intros X l. induction l as [|y l IH]; intros [|i] [|j] x Hij; cbn; try reflexivity; [lia|].
apply IH. lia.
Qed.

#[using="Type"] Lemma u8arr_transport : forall W m m' A bs,
u8arr m A bs -> munch W m m' -> wmono segs m m' ->
disjoint_from W A (Z.of_nat (length bs)) -> u8arr m' A bs.
Proof.
intros W m m' A bs [Hb Hw] MU WM Hd. split.
- eapply bytes_at_transport; eauto.
- eapply wr_at_transport; eauto.
Qed.
#[using="Type"] Lemma u32arr_transport : forall W m m' A ws,
u32arr m A ws -> munch W m m' -> wmono segs m m' ->
disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr m' A ws.
Proof.
intros W m m' A ws [Hb Hw] MU WM Hd. split.
- eapply bytes_at_transport; eauto. rewrite u32s_length, Nat2Z.inj_mul. exact Hd.
- eapply wr_at_transport; eauto.
Qed.
#[using="Type"] Lemma u64arr_transport : forall W m m' A ws,
u64arr m A ws -> munch W m m' -> wmono segs m m' ->
disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr m' A ws.
Proof.
intros W m m' A ws [Hb Hw] MU WM Hd. split.
- eapply bytes_at_transport; eauto. rewrite u64s_length, Nat2Z.inj_mul. exact Hd.
- eapply wr_at_transport; eauto.
Qed.
#[using="Type"] Lemma u8ro_transport : forall W m m' A bs,
u8ro m A bs -> munch W m m' ->
disjoint_from W A (Z.of_nat (length bs)) -> u8ro m' A bs.
Proof. intros W m m' A bs Hb MU Hd. eapply bytes_at_transport; eauto. Qed.

End WithSegs.
