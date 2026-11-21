(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (adds the stack window of the launch values: stack_window_reach (2,244,095) and stack_window_depth (6,144,513, stack_window_depth_val), page_round_up_Z_fixed, mmap_gap_sv48 and mmap_gap_sv48_mod, stack_window_lo_ge_sp, launch_base_gap_le and stack_window_lo_valid, and wrap_mem_window_defined, store_ok_wrap_window and store_ok_wrap_window_valid over wrap_mem's new arguments, with stack_window_lo as the window floor). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase MemImageType RiscvSemantics StackLayout State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import PropExec CatExec StepTac StreamSim AllocSim.
Unset Lia Cache.
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
Definition stack_window_reach : Z := 2244095.

Definition stack_window_depth : Z := stack_max_size - stack_window_reach.

Lemma stack_window_depth_val : stack_window_depth = 6144513.
Proof. vm_compute. reflexivity. Qed.

Lemma page_round_up_Z_fixed : forall n,
  (n mod page_size = 0)%Z -> page_round_up_Z n = n.
Proof.
  intros n Hn. unfold page_round_up_Z, page_size in *.
  apply Z.mod_divide in Hn; [|lia]. destruct Hn as [k Hk]. subst n.
  replace (k * 4096 + 4096 - 1)%Z with (k * 4096 + 4095)%Z by lia.
  rewrite Z.div_add_l by lia.
  replace (4095 / 4096)%Z with 0%Z by reflexivity. lia.
Qed.

Lemma mmap_gap_sv48 : forall kb,
  mmap_gap Sv48 kb
  = (let g := (stack_max_size + (stack_guard_gap_bytes kb
                 + if kb_aslr kb then stack_rnd_max else 0))%Z in
     if (g <? mmap_min_gap)%Z then mmap_min_gap else g).
Proof.
  intros kb. pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  unfold mmap_gap. cbv zeta.
  rewrite Z.mod_small
    by (unfold two_pow_64, stack_max_size, stack_rnd_max;
        destruct (kb_aslr kb); lia).
  assert (Hmax : mmap_max_gap Sv48 = 117281240296105%Z)
    by (vm_compute; reflexivity).
  rewrite !Hmax.
  unfold mmap_min_gap in *. rewrite !Z.gtb_ltb.
  (* [comment removed for export] *)
  destruct (kb_aslr kb); cbv beta iota delta [andb];
  [ destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + stack_rnd_max))%Z
      eqn:Ein
  | destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + 0))%Z
      eqn:Ein ];
  try apply Z.ltb_lt in Ein; try apply Z.ltb_ge in Ein;
  cbv beta iota delta [andb];
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota delta [andb]);
  unfold stack_max_size, stack_rnd_max in *; lia.
Qed.

Lemma mmap_gap_sv48_mod : forall kb,
  (mmap_gap Sv48 kb mod page_size = 0)%Z.
Proof.
  intros kb.
  assert (H4096 : forall x : Z, ((4096 * x) mod 4096 = 0)%Z)
    by (intro x; rewrite Z.mul_comm; apply Z_mod_mult).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold stack_guard_gap_bytes, mmap_min_gap, stack_max_size,
    stack_rnd_max, page_size.
  destruct (_ <? _)%Z;
    [ replace (128 * 1024 * 1024)%Z with (4096 * 32768)%Z by reflexivity;
      apply H4096 |].
  destruct (kb_aslr kb);
    [ replace (8 * 1024 * 1024
               + (4096 * stack_guard_gap_pages kb + 1073737728))%Z
        with (4096 * (264191 + stack_guard_gap_pages kb))%Z by lia
    | replace (8 * 1024 * 1024 + (4096 * stack_guard_gap_pages kb + 0))%Z
        with (4096 * (2048 + stack_guard_gap_pages kb))%Z by lia ];
    apply H4096.
Qed.

Lemma stack_window_lo_ge_sp : forall inp (sp brk0 mbase : word) draw,
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  (bv_unsigned sp - stack_max_size
   <= stack_window_lo (in_kernel inp) mbase draw)%Z.
Proof.
  intros inp sp brk0 mbase draw (_ & Hsp & _).
  pose proof (launch_sp_le_top inp (ed_top draw) sp Hsp).
  unfold stack_window_lo.
  apply Z.le_trans with (bv_unsigned (ed_top draw) - stack_max_size)%Z;
    [lia | apply Z.le_max_l].
Qed.

Lemma launch_base_gap_le : forall kb mbase,
  valid_launch_base Sv48 kb mbase ->
  (bv_unsigned mbase + stack_guard_gap_bytes kb
   <= va_stack_top Sv48
      - (if kb_aslr kb then 0x407ff000 else 8 * 1024 * 1024))%Z.
Proof.
  intros kb mbase (r & Hr & _ & _ & Heq).
  pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  rewrite Heq. unfold mmap_base_of.
  assert (Hdiv : (page_size
                  | va_stack_top Sv48 - mmap_gap Sv48 kb - page_size * r)%Z).
  { apply Z.divide_sub_r; [apply Z.divide_sub_r|].
    - exists 34359738368%Z. vm_compute. reflexivity.
    - apply Z.mod_divide; [unfold page_size; lia|]. apply mmap_gap_sv48_mod.
    - exists r. unfold page_size. lia. }
  rewrite page_round_up_Z_fixed
    by (apply Z.mod_divide; [unfold page_size; lia | exact Hdiv]).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold mmap_min_gap, va_stack_top, sp_window_hi, stack_max_size,
    stack_rnd_max, page_size in *.
  destruct (kb_aslr kb); cbv beta iota;
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota);
  lia.
Qed.

Lemma stack_window_lo_valid : forall inp (sp brk0 mbase : word) draw,
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  stack_window_lo (in_kernel inp) mbase draw
  <= bv_unsigned sp + stack_window_reach - stack_max_size.
Proof.
  intros inp sp brk0 mbase draw Hlaunch (Htop & Hsp & Hbase).
  pose proof (launch_top_minus_sp inp (ed_top draw) sp Hlaunch Hsp) as Hd.
  pose proof (launch_base_gap_le (in_kernel inp) mbase Hbase) as Hg.
  destruct Htop as (_ & Hhi & Hlo).
  unfold stack_window_lo, stack_window_reach, stack_max_size,
    va_stack_top, sp_window_hi, stack_rnd_max, page_size in *.
  destruct (kb_aslr (in_kernel inp)); cbv beta iota in Hg, Hlo;
    apply Z.max_lub; lia.
Qed.

(* store_ok_wrap_window below applies wrap_mem_window_defined at :207 and this copy never
   declares it -- "The variable wrap_mem_window_defined was not found in the current
   environment" without it (measured). fse_read_ncount is the only one of zstd's
   four units missing it: zstd/simple_decompress AS/StoreOk.v:114, zstd/huf_decompress
   AS/StoreOk.v:114 and zstd/zstd_frame_info AS/StoreOk.v:132 all carry it, identically, in
   exactly this position. Carried verbatim, statement and proof. *)
Lemma wrap_mem_window_defined :
  forall inp mbase ph entry sp (x : word) draw,
  stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned x ->
  bv_unsigned x < bv_unsigned sp ->
  wrap_mem inp mbase ph entry sp draw x <> None.
Proof.
  intros inp mbase ph entry sp x draw Hlo Hhi. unfold wrap_mem.
  destruct (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw) x)
    as [b|]; [discriminate|].
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  cbn. discriminate.
Qed.

Lemma store_ok_wrap_window :
  forall segs inp mbase ph entry sp a n draw,
  stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned sp ->
  store_ok segs (wrap_mem inp mbase ph entry sp draw) a n = true.
Proof.
  intros segs inp mbase ph entry sp a n draw Hlo Hhi.
  assert (Hsp : bv_unsigned sp < 2 ^ 64) by apply bv_unsigned_in_range.
  apply store_ok_of_all; [lia|].
  intros x Hx. unfold wview.
  destruct (wrap_mem inp mbase ph entry sp draw x) as [b|] eqn:Hw;
    [discriminate|].
  exfalso. revert Hw. apply wrap_mem_window_defined; lia.
Qed.
Lemma store_ok_wrap_window_valid :
  forall segs inp mbase ph entry (sp brk0 : word) a n draw,
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  bv_unsigned sp + stack_window_reach - stack_max_size <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned sp ->
  store_ok segs (wrap_mem inp mbase ph entry sp draw) a n = true.
Proof.
  intros segs inp mbase ph entry sp brk0 a n draw Hvl Hlau Hlo Hhi.
  apply store_ok_wrap_window; [|exact Hhi].
  pose proof (stack_window_lo_valid inp sp brk0 mbase draw Hvl Hlau). lia.
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
Create HintDb store_ok_db.
