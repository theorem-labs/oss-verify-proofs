(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

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

Variable ph : PhdrInfo.

Variable sp : word.
Variable av ev : list (list byte).
Variable uid : word.
Variable hw : word.

Variable rnd : EntryDraw.

Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

Lemma sp_hi_num : (bv_unsigned sp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Definition argcN : word := len_word av.

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
Proof.
pose proof (valid_argv_len av Hva).
unfold argcN, len_word. apply u_Z2bv; lia.
Qed.

Lemma bsb_nw :
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z.
Proof.
pose proof (bsb_bound ph sp av ev uid hw rnd Hva Hve). pose proof sp_hi_num. lia.
Qed.

Definition envp_ptr : word :=
Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat (length av) + 8).

Definition wmem : word -> option byte := wrap_mem ph sp av ev uid hw rnd.

End Scaffold.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qek8 Qxe5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

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

