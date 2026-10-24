(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase MemImageType RiscvSemantics StackLayout State Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK1a YK1d YK02 YK0q.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.
Definition mem_grows (m m' : word -> option byte) : Prop :=
forall x, m x <> None -> m' x <> None.
Lemma mem_grows_refl : forall m, mem_grows m m.
Proof. intros m x H. exact H. Qed.
Lemma mem_grows_trans : forall m1 m2 m3,
mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H12 H23 x Hx. apply H23, H12, Hx. Qed.
Lemma wview_grows : forall segs m m' x,
mem_grows m m' ->
wview segs m x <> None -> wview segs m' x <> None.
Proof.
intros segs m m' x Hg Hx. unfold wview in *.
destruct (m' x) as [b'|] eqn:Hm'; [discriminate|].
destruct (m x) as [b|] eqn:Hm.
- exfalso. apply (Hg x); [rewrite Hm; discriminate|exact Hm'].
- exact Hx.
Qed.
Lemma store_ok_mono : forall segs n m m' a,
mem_grows m m' ->
store_ok segs m a n = true -> store_ok segs m' a n = true.
Proof.
intros segs n; induction n as [|n IH]; intros m m' a Hg H; [reflexivity|].
cbn [store_ok] in *.
destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
destruct (wview segs m' a) as [b'|] eqn:Hv'.
- apply (IH m m'); assumption.
- exfalso. apply (wview_grows segs m m' a Hg); [rewrite Hv; discriminate|exact Hv'].
Qed.
Lemma wbytes_grows : forall bs m a, mem_grows m (wbytes m a bs).
Proof.
induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
cbn [wbytes]. apply IH.
destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.
Lemma apply_zeros_grows : forall zs m, mem_grows m (apply_zeros m zs).
Proof.
intros zs m x Hx. unfold apply_zeros.
destruct zs as [|z zs']; [exact Hx|].
destruct (zeros_cover (z :: zs') x); [discriminate|exact Hx].
Qed.
Lemma zmem_grows : forall m b l, mem_grows m (zmem m b l).
Proof.
intros m b l x Hx. unfold zmem.
destruct (Z.leb _ _ && Z.ltb _ _)%bool; [discriminate|exact Hx].
Qed.
Lemma write_to_mem_grows : forall bs m a, mem_grows m (write_to_mem m a bs).
Proof.
induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
cbn [write_to_mem]. apply IH.
destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.
Lemma apply_writes_grows : forall ws m, mem_grows m (apply_writes m ws).
Proof.
induction ws as [|w ws' IH]; intros m x Hx.
- exact Hx.
- destruct w as [a bs]. cbn [apply_writes].
apply IH. apply write_to_mem_grows. exact Hx.
Qed.
Lemma store_ok_of_all : forall segs n m a,
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
(forall x : word,
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
wview segs m x <> None) ->
store_ok segs m a n = true.
Proof.
intros segs n; induction n as [|n IH]; intros m a Hnw Hall; [reflexivity|].
cbn [store_ok].
destruct (wview segs m a) as [b|] eqn:Hv.
2: { exfalso. refine (Hall a _ Hv). rewrite Nat2Z.inj_succ. lia. }
destruct n as [|n']; [reflexivity|].
rewrite Nat2Z.inj_succ in Hnw.
assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
by (apply u_add1; rewrite Nat2Z.inj_succ in Hnw; lia).
apply IH.
- rewrite Hu1. lia.
- intros x Hx. rewrite Hu1 in Hx. apply Hall.
rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma wrap_mem_window_defined : forall ph sp argv envp (x : word) uid hw rnd,
bv_unsigned sp - stack_max_size <= bv_unsigned x ->
bv_unsigned x < bv_unsigned sp ->
wrap_mem ph sp argv envp uid hw rnd x <> None.
Proof.
intros ph sp argv envp x uid hw rnd Hlo Hhi. unfold wrap_mem.
destruct (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x) as [b|];
[discriminate|].
rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
cbn. discriminate.
Qed.
Lemma store_ok_wrap_window : forall segs ph sp argv envp a n uid hw rnd,
bv_unsigned sp - stack_max_size <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= bv_unsigned sp ->
store_ok segs (wrap_mem ph sp argv envp uid hw rnd) a n = true.
Proof.
intros segs ph sp argv envp a n uid hw rnd Hlo Hhi.
assert (Hsp : bv_unsigned sp < 2 ^ 64) by apply bv_unsigned_in_range.
apply store_ok_of_all; [lia|].
intros x Hx. unfold wview.
destruct (wrap_mem ph sp argv envp uid hw rnd x) as [b|] eqn:Hw; [discriminate|].
exfalso. revert Hw. apply wrap_mem_window_defined; lia.
Qed.
Lemma store_ok_zeros_hit : forall segs m zs a n,
zs <> [] ->
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
(forall x : word,
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
zeros_cover zs x = true) ->
store_ok segs (apply_zeros m zs) a n = true.
Proof.
intros segs m zs a n Hne Hnw Hcov.
apply store_ok_of_all; [exact Hnw|].
intros x Hx. unfold wview, apply_zeros.
destruct zs as [|z zs']; [contradiction|].
rewrite (Hcov x Hx). discriminate.
Qed.
Lemma store_ok_zmem : forall segs m (b l a : word) (n : nat),
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
bv_unsigned b <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
store_ok segs (zmem m b l) a n = true.
Proof.
intros segs m b l a n Hnw Hlo Hhi.
apply store_ok_of_all; [exact Hnw|].
intros x Hx. unfold wview, zmem.
rewrite (proj2 (Z.leb_le _ _)) by lia.
rewrite (proj2 (Z.ltb_lt _ _)) by lia.
cbn. discriminate.
Qed.
Definition store_grant_ok (segs : list Segment) (m : word -> option byte)
(b l : word) : Prop :=
forall (a : word) (n : nat),
bv_unsigned b <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
store_ok segs m a n = true.
Lemma store_grant_zmem : forall segs m b l,
bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
store_grant_ok segs (zmem m b l) b l.
Proof.
intros segs m b l Hnw a n Hlo Hhi. apply store_ok_zmem; lia.
Qed.
Lemma store_grant_zmem_prefix : forall segs m b logical physical,
(bv_unsigned logical <= bv_unsigned physical)%Z ->
(bv_unsigned b + bv_unsigned physical <= 2 ^ 64)%Z ->
store_grant_ok segs (zmem m b physical) b logical.
Proof.
intros segs m b logical physical Hle Hnw a n Hlo Hhi.
apply store_ok_zmem; lia.
Qed.
Lemma store_grant_mono : forall segs m m' b l,
mem_grows m m' -> store_grant_ok segs m b l -> store_grant_ok segs m' b l.
Proof.
intros segs m m' b l Hg H a n Hlo Hhi.
eapply store_ok_mono; [exact Hg|]. apply H; assumption.
Qed.
Lemma store_ok_seg_writable : forall segs m a n,
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
(forall x : word,
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
exists seg,
find_segment segs (bv_unsigned x) 1 = Some seg /\
seg_writable seg = true /\
segment_byte_at (seg_bytes seg)
(Z.to_N (bv_unsigned x - Z.of_N (seg_base seg))) <> None) ->
store_ok segs m a n = true.
Proof.
intros segs m a n Hnw Hall.
apply store_ok_of_all; [exact Hnw|].
intros x Hx. unfold wview.
destruct (m x) as [b|]; [discriminate|].
destruct (Hall x Hx) as [seg [Hfind [Hw Hb]]].
rewrite Hfind, Hw. exact Hb.
Qed.
Lemma store_ok_wseg : forall segs m a n,
wseg_ok segs a n = true -> store_ok segs m a n = true.
Proof.
intros segs m a n; revert a m; induction n as [|n IH]; intros a m H; [reflexivity|].
cbn [wseg_ok] in H.
destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
apply andb_true_iff in H as [H Hrec].
apply andb_true_iff in H as [Hwr Hbyte].
destruct (segment_byte_at (seg_bytes seg)
(Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
[|discriminate].
cbn [store_ok]. unfold wview at 1.
destruct (m a) as [b0|]; [apply IH, Hrec|].
rewrite Hseg, Hwr, Hb. apply IH, Hrec.
Qed.
Lemma store_ok_all : forall segs m n a,
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
store_ok segs m a n = true ->
forall x : word,
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
wview segs m x <> None.
Proof.
intros segs m n; induction n as [|n IH]; intros a Hnw H x Hx;
[cbn in Hx; lia|].
cbn [store_ok] in H.
destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
rewrite Nat2Z.inj_succ in Hnw, Hx.
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
{ assert (x = a) by (apply bv_eq; exact Heq). subst x.
rewrite Hv. discriminate. }
assert (Hn : (1 <= Z.of_nat n)%Z) by lia.
assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
eapply IH; [ | exact H | ]; lia.
Qed.
Lemma store_ok_sub : forall segs m (lo a : word) (N n : nat),
bv_unsigned lo + Z.of_nat N <= 2 ^ 64 ->
store_ok segs m lo N = true ->
bv_unsigned lo <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= bv_unsigned lo + Z.of_nat N ->
store_ok segs m a n = true.
Proof.
intros segs m lo a N n Hnw Hok Hl Hh.
apply store_ok_of_all; [lia|].
intros x Hx. apply (store_ok_all segs m N lo Hnw Hok). lia.
Qed.
Lemma store_ok_window : forall segs m (lo a : word) (N n : nat) (base hi : Z),
bv_unsigned lo = base ->
base + Z.of_nat N = hi ->
hi <= 2 ^ 64 ->
wseg_ok segs lo N = true ->
base <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= hi ->
store_ok segs m a n = true.
Proof.
intros segs m lo a N n base hi Hbase Htop Hnw Hw Hl Hh.
eapply store_ok_sub; [ | apply store_ok_wseg, Hw | | ]; lia.
Qed.
Lemma store_ok_read_aux : forall segs m n (a : word),
store_ok segs m a n = true ->
exists w, read_bytes_aux (wview segs m) a n = Some w.
Proof.
intros segs m n; induction n as [|n IH]; intros a H.
- exists []. reflexivity.
- cbn [store_ok] in H. cbn [read_bytes_aux].
destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
destruct (IH (a + 1)%bv H) as [w Hw]. rewrite Hw. exists (b :: w). reflexivity.
Qed.
Lemma store_ok_wbuf : forall segs ms (buf cnt : word),
store_ok segs (ms_mem ms) buf (word_to_nat cnt) = true ->
exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
intros segs ms buf cnt H.
rewrite read_bytes_map_eq. unfold ms_writable_byte.
apply store_ok_read_aux. exact H.
Qed.
Lemma of_nat_word_to_nat : forall w : word,
Z.of_nat (word_to_nat w) = bv_unsigned w.
Proof.
intro w. unfold word_to_nat. pose proof (u64_range w). lia.
Qed.
Lemma store_grant_wbuf : forall segs ms (b l buf cnt : word),
store_grant_ok segs (ms_mem ms) b l ->
bv_unsigned b <= bv_unsigned buf ->
bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
intros segs ms b l buf cnt Hg Hlo Hhi.
apply store_ok_wbuf, Hg; rewrite ?of_nat_word_to_nat; lia.
Qed.
Lemma heap_rg_wbuf : forall segs ms (b l buf cnt : word) (cur : Z),
store_grant_ok segs (ms_mem ms) b l ->
cur <= bv_unsigned b + bv_unsigned l - bv_unsigned b ->
covers (heap_rg b cur) buf (word_to_nat cnt) ->
exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
intros segs ms b l buf cnt cur Hg Hcur Hc.
destruct Hc as [Hlo Hhi]. cbn [heap_rg rg_lo rg_hi] in Hlo, Hhi.
rewrite of_nat_word_to_nat in Hhi.
eapply store_grant_wbuf; [exact Hg | lia | lia].
Qed.
Lemma zmem_wbuf : forall segs ms m (b l buf cnt : word),
mem_grows (zmem m b l) (ms_mem ms) ->
bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
bv_unsigned b <= bv_unsigned buf ->
bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
intros segs ms m b l buf cnt Hgr Hnw Hlo Hhi.
eapply store_grant_wbuf; [ | exact Hlo | exact Hhi ].
eapply store_grant_mono; [exact Hgr|]. apply store_grant_zmem. exact Hnw.
Qed.
Example drain_buffer_in_grant : forall segs ms m (b l buf cnt : word) a bs,
ms_mem ms = wbytes (zmem m b l) a bs ->
bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
bv_unsigned b <= bv_unsigned buf ->
bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
intros segs ms m b l buf cnt a bs Hm Hnw Hlo Hhi.
eapply zmem_wbuf;
[ rewrite Hm; apply wbytes_grows | exact Hnw | exact Hlo | exact Hhi ].
Qed.
Ltac store_ok_peel :=
repeat first
[ eapply store_ok_mono; [apply wbytes_grows|]
| eapply store_ok_mono; [apply write_to_mem_grows|]
| eapply store_ok_mono; [apply apply_zeros_grows|]
| eapply store_ok_mono; [apply apply_writes_grows|] ].
Ltac store_ok_base :=
first
[ apply store_ok_wrap_window; unfold stack_max_size; u_norm; lia
| eapply store_ok_zeros_hit;
[ discriminate | u_norm; lia | intros; u_norm; lia ]
| apply store_ok_zmem; u_norm; lia ].
Ltac solve_store_ok :=
store_ok_peel;
first [ store_ok_base
| eapply store_ok_mono; [apply zmem_grows|];
store_ok_peel; store_ok_base ].
Create HintDb store_ok_db.
Ltac store_ok_grows := solve [ eauto with store_ok_db ].
Ltac solve_store_ok_inv :=
first [ solve_store_ok
| store_ok_peel;
eapply store_ok_mono; [ store_ok_grows | ]; solve_store_ok ].
Ltac solve_mem_grows :=
repeat first
[ solve [ eauto with store_ok_db ]
| apply mem_grows_refl
| eapply mem_grows_trans; [ | apply wbytes_grows ]
| eapply mem_grows_trans; [ | apply zmem_grows ]
| eapply mem_grows_trans; [ | apply write_to_mem_grows ]
| eapply mem_grows_trans; [ | apply apply_zeros_grows ]
| eapply mem_grows_trans; [ | apply apply_writes_grows ] ].
