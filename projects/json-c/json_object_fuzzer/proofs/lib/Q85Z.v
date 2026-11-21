(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput: the scaffold section and wrap_mem over the launch's input, mmap base and entry point, with valid_launch and entry_launch_ok_va; the stack window from the model's stack_window_lo and stack_window_depth in place of the 8 MiB bound (store_ok_wrap_window_valid); the walk over run_segments segs inp sp mbase: find_segment, rdn and the machine step carried from the binary's segments to segs ++ the vDSO pair; vdso_segments_miss over vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)

From Stdlib Require NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC QgpE QU0c QJ4Q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QWTC QgpE QU0c QJ4Q.Mq0.

Import ListNotations.
Open Scope bv_scope.

Section Scaffold.

Variable segs : list Segment.
Variable v : VaSize.
Variable inp : ProcInput.
Variable mbase : word.

Variable ph : PhdrInfo.
Variable entry : word.

Variable sp brk : word.
Variable draw : EntryDraw.

Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp brk mbase draw) inp.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

Lemma sp_hi_num : (bv_unsigned sp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Definition argcN : word := len_word (in_argv inp).

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length (in_argv inp)).
Proof.
pose proof (valid_argv_len (in_argv inp) Hva).
unfold argcN, len_word. apply u_Z2bv; lia.
Qed.

Lemma bsb_nw :
(bv_unsigned sp
+ Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw)) < 2^64)%Z.
Proof.
pose proof (bsb_bound v inp mbase ph entry sp brk draw Hvl Hlau).
pose proof sp_hi_num. lia.
Qed.

Definition envp_ptr : word :=
Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat (length (in_argv inp)) + 8).

Definition wmem : word -> option byte := wrap_mem inp mbase ph entry sp draw.

End Scaffold.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qek8 Qxe5.
From LinuxProcessSemantics.LinuxProcessSem Require Vdso.
From LinuxProcessSemantics.Riscv Require DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Vdso LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import QWTC QgpE QJ4Q.Mq0 Qek8.Mq0 Qek8 Qxe5.
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

Definition stack_window_reach : Z := 2244095.

Definition stack_window_depth : Z := stack_max_size - stack_window_reach.

Lemma stack_window_depth_val : stack_window_depth = 6144513.
Proof. vm_compute. reflexivity. Qed.

Lemma page_round_up_Z_aligned : forall n,
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
rewrite page_round_up_Z_aligned
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

Lemma store_grant_mono : forall segs m m' b l,
mem_grows m m' -> store_grant_ok segs m b l -> store_grant_ok segs m' b l.
Proof.
intros segs m m' b l Hg H a n Hlo Hhi.
eapply store_ok_mono; [exact Hg|]. apply H; assumption.
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
[ eapply store_ok_wrap_window_valid;
[ eassumption | eassumption
| unfold stack_window_reach, stack_max_size; u_norm; lia
| u_norm; lia ]
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

(* ========================================================================= *)
(* Supplier walks over [Run.run_segments segs inp sp mbase] = segs ++ tail.    *)
(* [find_segment] returns the FIRST covering segment, so a range the binary's  *)
(* own segments cover reads the same over segs ++ tail; a range that misses    *)
(* every tail segment reads the same too (success AND failure).                *)
(* ========================================================================= *)

Lemma find_segment_app : forall segs tail addr n,
find_segment (segs ++ tail) addr n
= match find_segment segs addr n with
| Some s => Some s
| None => find_segment tail addr n
end.
Proof.
induction segs as [|seg rest IH]; intros tail addr n; [reflexivity|].
cbn [find_segment app].
destruct (Z.leb (Z.of_N (seg_base seg)) addr
&& Z.leb (addr + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))%bool;
[reflexivity | apply IH].
Qed.

Lemma find_segment_app_prefix : forall segs tail addr n,
find_segment segs addr n <> None ->
find_segment (segs ++ tail) addr n = find_segment segs addr n.
Proof.
intros segs tail addr n Hhit. rewrite find_segment_app.
destruct (find_segment segs addr n); [reflexivity | congruence].
Qed.

Lemma find_segment_run_segments : forall segs inp (sp mbase : word) addr n,
find_segment segs addr n <> None ->
find_segment (run_segments segs inp sp mbase) addr n = find_segment segs addr n.
Proof.
intros segs inp sp mbase addr n Hhit.
unfold run_segments. apply find_segment_app_prefix. exact Hhit.
Qed.

(* A range that misses every tail segment finds over segs ++ tail exactly what it finds over segs. *)
Lemma find_segment_app_miss : forall segs tail addr n,
find_segment tail addr n = None ->
find_segment (segs ++ tail) addr n = find_segment segs addr n.
Proof.
intros segs tail addr n Hmiss. rewrite find_segment_app.
destruct (find_segment segs addr n); [reflexivity | exact Hmiss].
Qed.

(* Disjointness from each tail segment is a miss. *)
Lemma find_segment_disjoint : forall tail addr n,
1 <= n ->
Forall (fun s => addr + n <= Z.of_N (seg_base s)
\/ Z.of_N (seg_base s) + Z.of_N (seg_size s) <= addr) tail ->
find_segment tail addr n = None.
Proof.
intros tail addr n Hn Hall.
induction Hall as [|s rest Hs _ IH]; [reflexivity|].
cbn [find_segment].
destruct Hs as [Hs|Hs].
- rewrite (proj2 (Z.leb_gt (Z.of_N (seg_base s)) addr)) by lia. exact IH.
- rewrite (proj2 (Z.leb_gt (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))) by lia.
destruct (Z.leb (Z.of_N (seg_base s)) addr); exact IH.
Qed.

Lemma memory_read_app_some : forall segs tail addr n bs,
memory_read segs addr n = Some bs ->
memory_read (segs ++ tail) addr n = Some bs.
Proof.
intros segs tail addr n bs H. unfold memory_read in *. rewrite find_segment_app. revert H.
destruct (find_segment segs (bv_unsigned addr) (Z.of_N n)); intros H; [exact H | discriminate H].
Qed.

Lemma memory_read_app_miss : forall segs tail addr n,
find_segment tail (bv_unsigned addr) (Z.of_N n) = None ->
memory_read (segs ++ tail) addr n = memory_read segs addr n.
Proof.
intros segs tail addr n Hmiss. unfold memory_read.
rewrite (find_segment_app_miss segs tail _ _ Hmiss). reflexivity.
Qed.

Lemma seg_rom_app_some : forall segs tail a b,
seg_rom segs a = Some b -> seg_rom (segs ++ tail) a = Some b.
Proof.
intros segs tail a b H. unfold seg_rom in *. revert H.
destruct (memory_read segs a 1) as [bs|] eqn:E; intros H; [|discriminate H].
rewrite (memory_read_app_some segs tail a 1 bs E). exact H.
Qed.

Lemma seg_rom_app_miss : forall segs tail a,
find_segment tail (bv_unsigned a) 1 = None ->
seg_rom (segs ++ tail) a = seg_rom segs a.
Proof.
intros segs tail a Hmiss. unfold seg_rom.
rewrite (memory_read_app_miss segs tail a 1 Hmiss). reflexivity.
Qed.

(* The vDSO pair lies in [top - vdso_len kb, top) with top the page-rounded
min of mbase and the stack window floor (the range [State.init_reserved]
reserves); a range outside it misses both tail segments. *)
Local Transparent vdso_segments.
Lemma vdso_segments_miss : forall kb (sp mbase : word) addr n,
1 <= n ->
(addr + n <= page_round_down_Z (Z.min (bv_unsigned mbase)
(page_round_down_Z (bv_unsigned sp - stack_max_size))) - vdso_len kb
\/ page_round_down_Z (Z.min (bv_unsigned mbase)
(page_round_down_Z (bv_unsigned sp - stack_max_size))) <= addr) ->
find_segment (vdso_segments kb sp mbase) addr n = None.
Proof.
intros kb sp mbase addr n Hn Hd. unfold vdso_segments. cbv zeta.
match goal with |- context [if ?c then _ else _] => destruct c eqn:Eb end; [reflexivity|].
apply Z.ltb_ge in Eb.
pose proof (N2Z.is_nonneg (LinuxProcessSemantics.LinuxProcessSem.Vdso.vi_pages (vdso_image_of kb))) as Hp.
(* LPS b84e73ef: the text segment's base is the model's own [vdso_text_base kb sp mbase], a word; it lies
   [vdso_text_pages] pages below the pair's top ([vdso_pair_top sp mbase]), which is at most [mbase] *)
pose proof (bv_unsigned_in_range 64 mbase) as HM. change (bv_modulus 64) with (2 ^ 64)%Z in HM.
pose proof (page_round_down_Z_le (Z.min (bv_unsigned mbase)
(page_round_down_Z (bv_unsigned sp - stack_max_size)))) as HR.
pose proof (Z.le_min_l (bv_unsigned mbase)
(page_round_down_Z (bv_unsigned sp - stack_max_size))) as HL.
unfold vdso_text_base, vdso_pair_top in *.
unfold vdso_len, vdso_text_pages, vdso_vvar_pages, page_size in *.
rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
apply find_segment_disjoint; [exact Hn|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
cbn [seg_base seg_size]; rewrite !Z2N.id by lia; lia.
Qed.

Section TailReads.
Local Open Scope bv_scope.

(* Every byte of [a, a+n) that the overlay [mem] does not supply misses the tail. *)
Fixpoint tail_miss (tail : list Segment) (mem : word -> option byte) (a : word) (n : nat) : Prop :=
match n with
| O => True
| S n' => (mem a = None -> find_segment tail (bv_unsigned a) 1 = None)
/\ tail_miss tail mem (a+1) n'
end.

(* A read that SUCCEEDS over segs reads the same bytes over segs ++ tail (no side condition). *)
Lemma rdn_app_some : forall segs tail mem n a bs,
rdn segs mem a n = Some bs -> rdn (segs ++ tail) mem a n = Some bs.
Proof.
intros segs tail mem n. induction n as [|n IH]; intros a bs H; [exact H|].
cbn [rdn] in H |- *. revert H.
destruct (mem a) as [b|].
- destruct (rdn segs mem (a+1) n) as [rest|] eqn:E; intros H; [|simpl in H; discriminate H].
rewrite (IH (a+1) rest E). exact H.
- destruct (seg_rom segs a) as [b|] eqn:Er; [|intros H; simpl in H; discriminate H].
rewrite (seg_rom_app_some segs tail a b Er).
destruct (rdn segs mem (a+1) n) as [rest|] eqn:E; intros H; [|simpl in H; discriminate H].
rewrite (IH (a+1) rest E). exact H.
Qed.

(* A read whose overlay-missing bytes all miss the tail reads the same over both
lists, success and failure alike. *)
Lemma rdn_app_miss : forall segs tail mem n a,
tail_miss tail mem a n -> rdn (segs ++ tail) mem a n = rdn segs mem a n.
Proof.
intros segs tail mem n. induction n as [|n IH]; intros a Hm; [reflexivity|].
destruct Hm as [Ha Hrest]. cbn [rdn].
rewrite (IH (a+1) Hrest).
destruct (mem a) as [b|] eqn:Em; [reflexivity|].
rewrite (seg_rom_app_miss segs tail a ltac:(first [exact (Ha Em) | exact (Ha eq_refl)])). reflexivity.
Qed.

Lemma rdn_run_segments_some : forall segs inp (sp mbase : word) mem n a bs,
rdn segs mem a n = Some bs -> rdn (run_segments segs inp sp mbase) mem a n = Some bs.
Proof. intros. unfold run_segments. apply rdn_app_some. assumption. Qed.

End TailReads.

(* ------------------------------------------------------------------------- *)
(* A machine step that succeeds over segs succeeds the same way over segs ++  *)
(* tail, when the tail segments are neither executable nor writable (the vDSO  *)
(* pair is "r--"): fetches and the writable view are EQUAL over both lists,    *)
(* and a load that reads over segs reads the same bytes over segs ++ tail.     *)
(* ------------------------------------------------------------------------- *)

Definition tail_inert (tail : list Segment) : Prop :=
Forall (fun s => seg_executable s = false /\ seg_writable s = false) tail.

Lemma find_segment_in : forall l addr n s, find_segment l addr n = Some s -> In s l.
Proof.
induction l as [|s0 rest IH]; intros addr n s H; [discriminate H|].
cbn [find_segment] in H.
destruct (Z.leb (Z.of_N (seg_base s0)) addr
&& Z.leb (addr + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
- injection H as <-. left. reflexivity.
- right. exact (IH addr n s H).
Qed.

Section StepTransfer.
Variables (segs tail : list Segment).
Hypothesis Hin : tail_inert tail.

Lemma tail_hit_inert : forall addr n s, find_segment tail addr n = Some s ->
seg_executable s = false /\ seg_writable s = false.
Proof.
intros addr n s H. unfold tail_inert in Hin. rewrite Forall_forall in Hin.
exact (Hin s (find_segment_in tail addr n s H)).
Qed.

Lemma code_read_app : forall a n, code_read (segs ++ tail) a n = code_read segs a n.
Proof.
intros a n. unfold code_read. rewrite find_segment_app.
destruct (find_segment segs (bv_unsigned a) (Z.of_N n)); [reflexivity|].
destruct (find_segment tail (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E; [|reflexivity].
destruct (tail_hit_inert _ _ _ E) as [Hx _]. rewrite Hx. reflexivity.
Qed.

Lemma code_read_ov_app : forall m a n, code_read_ov (segs ++ tail) m a n = code_read_ov segs m a n.
Proof.
intros m a n. unfold code_read_ov. rewrite find_segment_app.
destruct (find_segment segs (bv_unsigned a) (Z.of_N n)); [reflexivity|].
destruct (find_segment tail (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E; [|reflexivity].
destruct (tail_hit_inert _ _ _ E) as [Hx _]. rewrite Hx. reflexivity.
Qed.

Lemma fetch_word_app : forall a, fetch_word (segs ++ tail) a = fetch_word segs a.
Proof. intros a. unfold fetch_word. rewrite code_read_app. reflexivity. Qed.

Lemma fetch_word_ov_app : forall m a, fetch_word_ov (segs ++ tail) m a = fetch_word_ov segs m a.
Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_app. reflexivity. Qed.

Lemma fetch_half_app : forall a, fetch_half (segs ++ tail) a = fetch_half segs a.
Proof. intros a. unfold fetch_half. rewrite code_read_app. reflexivity. Qed.

Lemma fetch_half_any_app : forall m a, fetch_half_any (segs ++ tail) m a = fetch_half_any segs m a.
Proof.
intros m a. unfold fetch_half_any, fetch_half_ov.
rewrite fetch_half_app, code_read_ov_app. reflexivity.
Qed.

Lemma fetch_tail_any_app : forall m a, fetch_tail_any (segs ++ tail) m a = fetch_tail_any segs m a.
Proof. intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_app. reflexivity. Qed.

Lemma wview_app : forall m a, wview (segs ++ tail) m a = wview segs m a.
Proof.
intros m a. unfold wview. destruct (m a); [reflexivity|].
rewrite find_segment_app.
destruct (find_segment segs (bv_unsigned a) 1); [reflexivity|].
destruct (find_segment tail (bv_unsigned a) 1) as [s|] eqn:E; [|reflexivity].
destruct (tail_hit_inert _ _ _ E) as [_ Hw]. rewrite Hw. reflexivity.
Qed.

Lemma store_ok_app : forall n m a, store_ok (segs ++ tail) m a n = store_ok segs m a n.
Proof.
induction n as [|n IH]; intros m a; [reflexivity|].
cbn [store_ok]. rewrite wview_app.
destruct (wview segs m a); [apply IH | reflexivity].
Qed.

Lemma ov_read_bytes_app_some : forall n m a bs,
ov_read_bytes segs m a n = Some bs -> ov_read_bytes (segs ++ tail) m a n = Some bs.
Proof.
induction n as [|n IH]; intros m a bs H; [exact H|].
cbn [ov_read_bytes] in H |- *.
assert (Hb : forall b, (match m a with
| Some b => Some b
| None => match memory_read segs a 1 with Some (b :: _) => Some b | _ => None end
end) = Some b ->
(match m a with
| Some b => Some b
| None => match memory_read (segs ++ tail) a 1 with Some (b :: _) => Some b | _ => None end
end) = Some b).
{ intros b0 E. destruct (m a) as [b1|]; [exact E|].
destruct (memory_read segs a 1) as [l|] eqn:Er; [|discriminate E].
rewrite (memory_read_app_some segs tail a 1 l Er). exact E. }
destruct (match m a with
| Some b => Some b
| None => match memory_read segs a 1 with Some (b :: _) => Some b | _ => None end
end) as [b|] eqn:E0; [|discriminate H].
rewrite (Hb b eq_refl).
match type of H with context [ov_read_bytes segs m ?a1 n] =>
destruct (ov_read_bytes segs m a1 n) as [rest|] eqn:E; [|discriminate H];
rewrite (IH m a1 rest E) end.
exact H.
Qed.

Lemma interp_eff_accesses_app_ok : forall t m r,
interp_eff_accesses segs t m = MachineOk r ->
interp_eff_accesses (segs ++ tail) t m = MachineOk r.
Proof.
induction t as [c|x|x|x|x|x|n a k IHk|n a v k IHk]; intros m r Hr;
cbn [interp_eff_accesses] in Hr |- *; try discriminate Hr; try exact Hr.
- (* ELoad *)
destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|] eqn:E.
+ rewrite (ov_read_bytes_app_some _ _ _ _ E).
destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep| |] eqn:Ei;
try discriminate Hr.
rewrite (IHk _ _ _ Ei). exact Hr.
+ destruct (range_meets_vvar segs a (width_bytes n)); discriminate Hr.
- (* EStore *)
rewrite store_ok_app.
destruct (store_ok segs m a (width_bytes n)); [|discriminate Hr].
destruct (interp_eff_accesses segs k
(write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [rep| |] eqn:Ei;
try discriminate Hr.
rewrite (IHk _ _ Ei). exact Hr.
Qed.

Lemma decode_exec_accesses_app_ok : forall st w r,
decode_exec_accesses segs st w = MachineOk r ->
decode_exec_accesses (segs ++ tail) st w = MachineOk r.
Proof.
intros st w r. unfold decode_exec_accesses.
destruct (is_ecall w); [intro H; exact H|].
destruct (decode_any w) as [[i isz]|]; [|intro H; exact H].
match goal with |- context [interp_eff_accesses segs ?tt ?mm] =>
destruct (interp_eff_accesses segs tt mm) as [rep| |] eqn:Ei end;
intros H; try discriminate H.
rewrite (interp_eff_accesses_app_ok _ _ _ Ei). exact H.
Qed.

Lemma fetch_failure_not_ok : forall m a st, fetch_failure segs m a <> MachineOk st.
Proof.
intros m a st. unfold fetch_failure. cbv zeta.
repeat match goal with |- context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

Lemma step_accesses_app_ok : forall st r,
step_accesses segs st = MachineOk r -> step_accesses (segs ++ tail) st = MachineOk r.
Proof.
intros st r. unfold step_accesses.
rewrite fetch_word_app, fetch_word_ov_app, fetch_tail_any_app.
destruct (fetch_word segs (ms_pc st)); [apply decode_exec_accesses_app_ok|].
destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)); [apply decode_exec_accesses_app_ok|].
destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)); [apply decode_exec_accesses_app_ok|].
destruct (fetch_failure segs (ms_mem st) (ms_pc st)) as [x| |] eqn:Ef; intros H;
[exfalso; exact (fetch_failure_not_ok _ _ _ Ef) | discriminate H | discriminate H].
Qed.

Lemma step_app_ok : forall st st',
RiscvSemantics.step segs st = MachineOk st' -> RiscvSemantics.step (segs ++ tail) st = MachineOk st'.
Proof.
intros st st'. unfold RiscvSemantics.step, drop_access_report.
destruct (step_accesses segs st) as [rep| |] eqn:E; intros H; try discriminate H.
rewrite (step_accesses_app_ok _ _ E). exact H.
Qed.

Lemma mi_account_step_app_ok : forall ms model p,
mi_account_step segs ms model = MachineOk p ->
mi_account_step (segs ++ tail) ms model = MachineOk p.
Proof.
intros ms model p. unfold mi_account_step.
destruct (RiscvSemantics.step_accesses segs ms) as [rep| |] eqn:E; intros H; try discriminate H.
rewrite (step_accesses_app_ok _ _ E). exact H.
Qed.

End StepTransfer.
End Mq1.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI Qo8J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0.
Import ListNotations.
Open Scope bv_scope.

Ltac gres :=
repeat first [ rewrite getr_same by reg_neq_tac
| rewrite getr_other by reg_neq_tac ];
rewrite ?getr_zero.

Lemma v_add_0_r : forall x : word, v_add x (Z_to_bv 64 0) = x.
Proof.
intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
rewrite Z.add_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Lemma v_add_0_l : forall x : word, v_add (Z_to_bv 64 0) x = x.
Proof.
intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
rewrite Z.add_0_l. apply bv_eq. rewrite Z_to_bv_unsigned.
apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Ltac is_pos_lit p :=
lazymatch p with
| xH => idtac
| xO ?q => is_pos_lit q
| xI ?q => is_pos_lit q
end.
Ltac is_Z_lit z :=
lazymatch z with
| Z0 => idtac
| Zpos ?p => is_pos_lit p
| Zneg ?p => is_pos_lit p
end.

Ltac val_lit v :=
lazymatch v with
| Z_to_bv 64 ?z => tryif is_Z_lit z then fail else wlit_closed v
| @BV _ _ _ => fail
| _ => wlit_closed v
end.

Ltac vals_lit :=
repeat match goal with
| |- context [regupd _ _ ?v] => val_lit v
end.

Ltac vnorm := gres; imm_norm; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; vals_lit.

Ltac stepn F D :=
lazymatch type of D with
| decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
| _ => stepi F D; vnorm
end.

Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepv F D v := stepiv F D v vres.

Ltac stepb_tk F D tac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
| decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
| decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
| decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
| decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
| decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
end;
[ exact F | reflexivity | exact D | gres; imm_norm; tac ]
| step_simpl; vnorm ].

Ltac stepb_ft F D tac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
| decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
| decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
| decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
| decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
| decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
end;
[ exact F | reflexivity | exact D | gres; imm_norm; tac ]
| step_simpl; vnorm ].

Ltac cond_compute :=
idtac;
lazymatch goal with
| |- ?g => check_closed_term g; vm_compute; reflexivity
end.

Ltac stepb F D :=
first [ stepb_tk F D ltac:(cond_compute) | stepb_ft F D ltac:(cond_compute) ].

Ltac stepret F D k tac :=
stepjr F D k ltac:(gres; tac);
imm_norm;
try lazymatch goal with
| Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
| Hk : v_jalr k 0 = k |- _ => rewrite Hk
end;
try (wlit (v_jalr k 0)).

Ltac stepsd F D aa vv oktac :=
chain_step;
[ reflexivity
| eapply step_sd_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D
| gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
| gres; first [ reflexivity | assumption | symmetry; assumption ]
| oktac ]
| step_simpl ].

Ltac stepld F D vv rtac :=
chain_step;
[ reflexivity
| eapply step_ld with (v := vv);
[ exact F | reflexivity | exact D
| gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
| first [ apply bytes_le_to_Z_8 | reflexivity ] ]
| step_simpl; vnorm ].
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWXq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWXq.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQny.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQny. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHup.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qek8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qek8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJ4Q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJ4Q. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo8J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo8J.Mq2.

Import ListNotations.
Open Scope bv_scope.

Lemma is_prefix_nil_r {A} : forall (a : list A), is_prefix a [] -> a = [].
Proof. destruct a; cbn; [reflexivity | contradiction]. Qed.

Definition TSet := list event -> Prop.

Definition t_eq (T T' : TSet) : Prop := forall tr, T tr <-> T' tr.

Lemma t_eq_refl : forall T, t_eq T T. Proof. firstorder. Qed.
Lemma t_eq_sym : forall T T', t_eq T T' -> t_eq T' T. Proof. firstorder. Qed.
Lemma t_eq_trans : forall T1 T2 T3, t_eq T1 T2 -> t_eq T2 T3 -> t_eq T1 T3.
Proof. firstorder. Qed.

Definition t_nil : TSet := fun tr => tr = [].

Definition t_emit (evs : list event) (T : TSet) : TSet :=
fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.

Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.

Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.

Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
t_emit [ExitEv code fs] t_nil.

Definition wr_index (buf : list byte) : Type :=
{n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.

Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
: wr_index buf :=
exist _ (length buf) (conj Hnb (Nat.le_refl _)).

Definition t_write_ch (ch : word) (buf : list byte) (T : TSet) : TSet :=
t_alt (fun i : wr_index buf =>
t_emit (map (WriteEv ch) (firstn (proj1_sig i) buf)) T).

Definition t_writes_pick (bufs : list (list byte)) (T : TSet) : TSet :=
fold_right (t_write_ch (Z_to_bv 64 1)) T bufs.

Lemma t_emit_nil_eq : forall T, T [] -> t_eq (t_emit [] T) T.
Proof.
intros T H0 tr. unfold t_emit. split.
- intros [Hp | (tr' & -> & HT)];
[apply is_prefix_nil_r in Hp; subst tr; exact H0 | exact HT].
- intro HT. right. exists tr. split; [reflexivity | exact HT].
Qed.

Definition t_writes_ch (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
fold_right (fun buf acc => t_emit (map (WriteEv ch) buf) acc) T bufs.

Definition t_writes (bufs : list (list byte)) (T : TSet) : TSet :=
t_writes_ch (Z_to_bv 64 1) bufs T.

Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof. intros e T. left. apply is_prefix_nil. Qed.

Section WithSegs.
Variable segs : list Segment.

Definition node_ok (c : config) (I : Type)
(evs : I -> list event) (nx : I -> config) : Prop :=
(forall i, Run.sstep_cfg segs (Run.alloc_only_cfg false) c (evs i) (SNext (nx i)))
/\ (forall e st, Run.sstep_cfg segs (Run.alloc_only_cfg false) c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok c I evs nx ->
(forall i, realizes (nx i) (T i)) ->
realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
m_halted (cfg_model c) <> None ->
realizes c t_nil
| rz_conseq : forall c T T',
realizes c T -> t_eq T T' -> realizes c T'.

Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- apply Heq. exact IH.
Qed.

Definition rz_path (c : config) : Prop := exists T, realizes c T.

Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

Lemma rz_silent1 : forall c c' T,
node_ok c unit (fun _ => []) (fun _ => c') ->
realizes c' T ->
realizes c T.
Proof.
intros c c' T Hnode Hc.
apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
- apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
intros []; exact Hc.
- eapply t_eq_trans;
[ apply (t_alt_unit (fun _ : unit => t_emit [] T))
| apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.

Lemma rz_emit1 : forall c c' e T,
node_ok c unit (fun _ => e) (fun _ => c') ->
realizes c' T ->
realizes c (t_emit e T).
Proof.
intros c c' e T Hnode Hc.
apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
- apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
intros []; exact Hc.
- apply t_alt_unit.
Qed.

Lemma node_instr : forall ms model ms',
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
node_ok (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
intros ms model ms' Hh Hlazy Hsvc Hstep. split.
- intros []. apply (sstep_cfg_instr segs (alloc_only_cfg false) ms model ms' model);
[assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
- intros e st Hss. apply sstep_cfg_sub in Hss.
destruct (sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hss) as [-> ->].
exists tt. split; reflexivity.
Qed.

Lemma rz_step : forall ms model ms' T,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
realizes (mkCfg ms' model) T ->
realizes (mkCfg ms model) T.
Proof.
intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
eapply rz_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

Lemma rz_msteps : forall ms ms' model T,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
realizes (mkCfg ms' model) T ->
realizes (mkCfg ms model) T.
Proof.
intros ms ms' model T Hh Hlazy Hms;
induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
intro Hc; [exact Hc|].
eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
| apply IH; exact Hc].
Qed.

Lemma rz_exit : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
realizes (mkCfg ms model)
(t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros ms model x8 Hh Hsvc Hx8.
set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
unfold t_exit.
eapply (rz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
- split.
+ intros []. cbn.
replace [ExitEv code (m_fs model)]
with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
apply (sstep_cfg_exit segs (alloc_only_cfg false) ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted code model) [] code);
[exact Hh | exact Hsvc
| apply (exit_dispatch_ok (sys_input segs ms x8) model);
rewrite in_sysno_sys_input; exact Hx8
| reflexivity
| apply m_killed_with_halted ].
+ intros e st Hss. apply sstep_cfg_sub in Hss.
destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
exists tt. split; reflexivity.
- apply rz_halt. cbn. discriminate.
Qed.

End WithSegs.

Definition t_outcomes (fs : Fs.Fs)
(U : (list (list byte) * word) -> Prop) : TSet :=
fun tr => exists o, U o /\ is_prefix tr (Qek8.outcome_trace fs o).

Definition t_writes_ch_pick (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
fold_right (t_write_ch ch) T bufs.

