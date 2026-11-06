(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Export Decode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma evt_ecall : forall segs (Q : machine_state -> Prop) R F pc fc rv m ro w,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true ->
  Q (MSsvc R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro) ->
  evt segs Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
  intros segs Q R F pc fc rv m ro w Hf He HQ.
  eapply evt_step; [|apply evt_done; exact HQ].
  split; [reflexivity|]. rewrite (step_ecall_gen segs R F (Z_to_bv 64 pc) fc rv m ro w Hf He). reflexivity.
Qed.

(* [comment removed for export] *)
Ltac step_ecall :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w =>
          apply (evt_ecall segs Q R F pc fc rv m ro w);
          [ vm_compute; reflexivity | vm_compute; reflexivity | simp_regs ]
      | None => fail "no instruction at" pc
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nret_MSsvc : forall R F pc x8 fc rv m ro r ws zs us ci,
  nret (MSsvc R F pc x8 fc rv m ro) (mkEffectU r ws zs us [] ci)
  = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4) fc rv (apply_writes (apply_zeros (apply_unmaps m us) zs) ws) ro.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nret_MSsvc_copies : forall R F pc x8 fc rv m ro r ws zs us cs ci,
  nret (MSsvc R F pc x8 fc rv m ro) (mkEffectU r ws zs us cs ci)
  = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4) fc rv
       (apply_writes (apply_copies m (apply_zeros (apply_unmaps m us) zs) cs) ws) ro.
Proof. reflexivity. Qed.

Lemma mkR_set_a0 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v,
  bvmap_set 10 v (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
  = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma apply_mem_none : forall m, apply_writes (apply_zeros (apply_unmaps m []) []) [] = m.
Proof. reflexivity. Qed.

Lemma apply_mem_write : forall m a bs, apply_writes (apply_zeros (apply_unmaps m []) []) [(a, bs)] = write_to_mem m a bs.
Proof. reflexivity. Qed.

Lemma apply_mem_delivered : forall m a bs,
  apply_writes (apply_zeros (apply_unmaps m []) []) (delivered_writes a bs) = write_to_mem m a bs.
Proof. intros m a [|b bs]; reflexivity. Qed.

(* [comment removed for export] *)
Definition in_range (a n : Z) (x : word) : bool :=
  (a <=? bv_unsigned x)%Z && (bv_unsigned x <? a + n)%Z.

Lemma apply_zeros_spec : forall m a n x, (0 <= a < 2^64)%Z -> (0 <= n < 2^64)%Z -> (a + n <= 2^64)%Z ->
  apply_zeros m [(wa a, Z_to_bv 64 n)] x = if in_range a n x then Some (Z_to_bv 8 0) else m x.
Proof.
  intros m a n x Ha Hn Han. cbn [apply_zeros zeros_cover existsb fst snd]. unfold in_range.
  rewrite wa_unsigned by lia. rewrite unsigned_lit by lia. rewrite orb_false_r. reflexivity.
Qed.

Lemma apply_unmaps_spec : forall m a n x, (0 <= a < 2^64)%Z -> (0 <= n < 2^64)%Z -> (a + n <= 2^64)%Z ->
  apply_unmaps m [(wa a, Z_to_bv 64 n)] x = if in_range a n x then None else m x.
Proof.
  intros m a n x Ha Hn Han. cbn [apply_unmaps zeros_cover existsb fst snd]. unfold in_range.
  rewrite wa_unsigned by lia. rewrite unsigned_lit by lia. rewrite orb_false_r. reflexivity.
Qed.

Section MemEffects.
Variable segs : list Segment.

(* [comment removed for export] *)

#[using="Type"] Lemma rw_cells_CB_prefix_write : forall m A n junk bs,
  rw_cells segs m A [CB n junk] -> (length bs <= n)%nat ->
  rw_cells segs (write_to_mem m (wa A) bs) A [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)].
Proof.
  intros m A n junk bs [[Hwf Hb] Hw] Hlen. cbn in Hwf. destruct Hwf as [Hj _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  split; [split|].
  - cbn. repeat split; try reflexivity. rewrite skipn_length. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (bytes_at_write_inside segs m A junk 0 bs Hb ltac:(lia) ltac:(cbn; lia)) as W.
    rewrite Z.add_0_r in W. unfold upd_bytes in W. cbn [firstn app Nat.add] in W. exact W.
  - cbn [cells_size csize]. cbn [cells_size csize] in Hw. replace (length bs + (n - length bs + 0))%nat with (n + 0)%nat by lia.
    apply wr_at_write. exact Hw.
Qed.

#[using="Type"] Lemma rw_cells_CB_store_ok : forall m A n junk k,
  rw_cells segs m A [CB n junk] -> (k <= n)%nat -> store_ok segs m (wa A) k = true.
Proof.
  intros m A n junk k [_ Hw] Hk. cbn [cells_size csize] in Hw.
  rewrite <- (Z.add_0_r A). apply (wr_at_store_ok segs m A (Z.of_nat (n + 0))); [exact Hw|lia|lia].
Qed.

#[using="Type"] Lemma mem_inv_syswrite : forall m A n junk bs,
  mem_inv segs m -> rw_cells segs m A [CB n junk] -> (length bs <= n)%nat ->
  mem_inv segs (write_to_mem m (wa A) bs).
Proof.
  intros. apply mem_inv_store; [assumption|]. eapply rw_cells_CB_store_ok; eauto.
Qed.

(* [comment removed for export] *)

Section Zeros.
Variables (m : word -> option byte) (a n : Z).
Hypothesis Ha : (0 <= a < 2^64)%Z.
Hypothesis Hn : (0 <= n < 2^64)%Z.
Hypothesis Han : (a + n <= 2^64)%Z.
Let m' := apply_zeros m [(wa a, Z_to_bv 64 n)].

#[using="Ha Hn Han"] Lemma zeros_outside : forall x, (bv_unsigned x < a \/ a + n <= bv_unsigned x)%Z -> m' x = m x.
Proof.
  intros x Hx. unfold m'. rewrite apply_zeros_spec by assumption. unfold in_range.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity. lia.
Qed.

#[using="Ha Hn Han"] Lemma zeros_inside : forall x, (a <= bv_unsigned x < a + n)%Z -> m' x = Some (Z_to_bv 8 0).
Proof.
  intros x Hx. unfold m'. rewrite apply_zeros_spec by assumption. unfold in_range.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity; lia.
Qed.

#[using="Ha Hn Han"] Lemma wview_zeros_mono : forall x, wview segs m x <> None -> wview segs m' x <> None.
Proof.
  intros x Hx. unfold wview in *. unfold m'. rewrite apply_zeros_spec by assumption.
  destruct (in_range a n x); [discriminate| exact Hx].
Qed.

#[using="Ha Hn Han"] Lemma bytes_at_zeros_other : forall A bs,
  bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> bytes_at segs m' A bs.
Proof.
  intros A bs (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
  unfold mrd. rewrite zeros_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

#[using="Ha Hn Han"] Lemma wr_at_zeros : forall A k, wr_at segs m A k -> wr_at segs m' A k.
Proof. intros A k (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. apply wview_zeros_mono, H, Hi. Qed.

#[using="Ha Hn Han"] Lemma rw_cells_zeros_other : forall A cs,
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof.
  intros A cs [[Hwf Hb] Hw] Hd. split; [split; [exact Hwf|]|].
  - apply bytes_at_zeros_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
  - apply wr_at_zeros. exact Hw.
Qed.

#[using="Ha Hn Han"] Lemma ro_cells_zeros_other : forall A cs,
  ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof.
  intros A cs [Hwf Hb] Hd. split; [exact Hwf|].
  apply bytes_at_zeros_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

#[using="Ha Hn Han"] Lemma stk_zeros : forall lo hi, stk segs m lo hi -> stk segs m' lo hi.
Proof.
  intros lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)]. split; [apply wview_zeros_mono; exact Hw|].
  unfold mrd in *. unfold m'. rewrite apply_zeros_spec by assumption.
  destruct (in_range a n (wa x)); [eexists; reflexivity|]. exists b. exact Hb.
Qed.

#[using="Ha Hn Han"] Lemma munch_zeros : forall W m0, munch W m0 m -> inside W a n -> munch W m0 m'.
Proof.
  intros W m0 H Hin x Hx. pose proof (bv_unsigned_in_range 64 x).
  rewrite zeros_outside. { apply H. exact Hx. }
  destruct (Z.ltb_spec0 (bv_unsigned x) a); [lia|].
  destruct (Z.leb_spec0 (a + n) (bv_unsigned x)); [lia|].
  exfalso. eapply (inside_not_outside W a n (bv_unsigned x) Hin); [lia| exact Hx].
Qed.

#[using="Ha Hn Han"] Lemma wmono_zeros : forall m0, wmono segs m0 m -> wmono segs m0 m'.
Proof. intros m0 H x Hx. apply wview_zeros_mono, H, Hx. Qed.

(* [comment removed for export] *)
#[using="Ha Hn Han"] Lemma mem_inv_zeros : mem_inv segs m -> (forall x : word, (a <= bv_unsigned x < a + n)%Z -> ro_addr segs x = false) -> mem_inv segs m'.
Proof.
  intros Hinv Hro x b Hx. unfold m' in Hx. rewrite apply_zeros_spec in Hx by assumption.
  unfold in_range in Hx.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb] in Hx;
    try exact (Hinv _ _ Hx).
  apply Hro. lia.
Qed.

(* [comment removed for export] *)
#[using="Ha Hn Han"] Lemma bytes_at_zeros_new : bytes_at segs m' a (repeat (Z_to_bv 8 0) (Z.to_nat n)).
Proof.
  split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi.
  unfold mrd. rewrite zeros_inside. 2:{ rewrite wa_unsigned by lia. lia. }
  symmetry. apply nth_error_repeat. exact Hi.
Qed.

#[using="Ha Hn Han"] Lemma wr_at_zeros_new : wr_at segs m' a n.
Proof.
  split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite zeros_inside; [discriminate|].
  rewrite wa_unsigned by lia. lia.
Qed.

#[using="Ha Hn Han"] Lemma rw_cells_zeros_new : rw_cells segs m' a [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Proof.
  split; [split|].
  - cbn. split; [apply repeat_length| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_zeros_new.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply wr_at_zeros_new.
Qed.

End Zeros.

(* [comment removed for export] *)

Section Unmaps.
Variables (m : word -> option byte) (a n : Z).
Hypothesis Ha : (0 <= a < 2^64)%Z.
Hypothesis Hn : (0 <= n < 2^64)%Z.
Hypothesis Han : (a + n <= 2^64)%Z.
Let m' := apply_unmaps m [(wa a, Z_to_bv 64 n)].

#[using="Ha Hn Han"] Lemma unmaps_outside : forall x, (bv_unsigned x < a \/ a + n <= bv_unsigned x)%Z -> m' x = m x.
Proof.
  intros x Hx. unfold m'. rewrite apply_unmaps_spec by assumption. unfold in_range.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity. lia.
Qed.

#[using="Ha Hn Han"] Lemma bytes_at_unmaps_other : forall A bs,
  bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> bytes_at segs m' A bs.
Proof.
  intros A bs (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
  unfold mrd. rewrite unmaps_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

#[using="Ha Hn Han"] Lemma wr_at_unmaps_other : forall A k,
  wr_at segs m A k -> (A + k <= a \/ a + n <= A)%Z -> wr_at segs m' A k.
Proof.
  intros A k (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
  unfold wview. rewrite unmaps_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

#[using="Ha Hn Han"] Lemma rw_cells_unmaps_other : forall A cs,
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof.
  intros A cs [[Hwf Hb] Hw] Hd. split; [split; [exact Hwf|]|].
  - apply bytes_at_unmaps_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
  - apply wr_at_unmaps_other; [exact Hw| exact Hd].
Qed.

#[using="Ha Hn Han"] Lemma ro_cells_unmaps_other : forall A cs,
  ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof.
  intros A cs [Hwf Hb] Hd. split; [exact Hwf|].
  apply bytes_at_unmaps_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

#[using="Ha Hn Han"] Lemma stk_unmaps_other : forall lo hi, stk segs m lo hi -> (hi <= a \/ a + n <= lo)%Z -> stk segs m' lo hi.
Proof.
  intros lo hi (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)].
  assert (E : m' (wa x) = m (wa x)). { apply unmaps_outside. rewrite wa_unsigned by lia. lia. }
  split. { unfold wview in *. rewrite E. exact Hw. } exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

#[using="Ha Hn Han"] Lemma munch_unmaps : forall W m0, munch W m0 m -> inside W a n -> munch W m0 m'.
Proof.
  intros W m0 H Hin x Hx. pose proof (bv_unsigned_in_range 64 x).
  rewrite unmaps_outside. { apply H. exact Hx. }
  destruct (Z.ltb_spec0 (bv_unsigned x) a); [lia|].
  destruct (Z.leb_spec0 (a + n) (bv_unsigned x)); [lia|].
  exfalso. eapply (inside_not_outside W a n (bv_unsigned x) Hin); [lia| exact Hx].
Qed.

#[using="Ha Hn Han"] Lemma mem_inv_unmaps : mem_inv segs m -> mem_inv segs m'.
Proof.
  intros Hinv x b Hx. unfold m' in Hx. rewrite apply_unmaps_spec in Hx by assumption.
  destruct (in_range a n x); [discriminate|]. exact (Hinv _ _ Hx).
Qed.

(* [comment removed for export] *)
End Unmaps.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ovl (m : word -> option byte) (a n : Z) : Prop :=
  forall i, (0 <= i < n)%Z -> m (wa (a + i)) <> None.

#[using="Type"] Lemma ovl_of_wr_at : forall m a n,
  wr_at segs m a n -> (forall x : word, (a <= bv_unsigned x < a + n)%Z -> wview segs m x = m x) -> ovl m a n.
Proof.
  intros m a n (Ha & Han & H) Hwo i Hi. specialize (H i Hi). rewrite Hwo in H; [exact H|].
  rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Lemma ovl_sub : forall m a n a' n', ovl m a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> ovl m a' n'.
Proof.
  intros m a n a' n' H H1 H2 i Hi. replace (a' + i)%Z with (a + (a' - a + i))%Z by lia. apply H. lia.
Qed.

Section Copy.
Variables (m0 m : word -> option byte) (src dst n : Z).
Hypothesis Hs : (0 <= src < 2^64)%Z.
Hypothesis Hd : (0 <= dst < 2^64)%Z.
Hypothesis Hn : (0 <= n < 2^64)%Z.
Let m' := apply_copy m0 m (mkCopy (wa src) (wa dst) (Z_to_bv 64 n)).

#[using="Hs Hd Hn"] Lemma copy_outside : forall x, (bv_unsigned x < dst \/ dst + n <= bv_unsigned x)%Z -> m' x = m x.
Proof.
  intros x Hx. unfold m', apply_copy. cbn [copy_dst copy_len copy_src].
  rewrite !wa_unsigned by lia. rewrite ?unsigned_lit by lia.
  destruct (Z.leb_spec0 dst (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (dst + n)); cbn [andb]; try reflexivity. lia.
Qed.

#[using="Hs Hd Hn"] Lemma copy_inside : forall x, (dst <= bv_unsigned x < dst + n)%Z ->
  m' x = m0 (wa (src + (bv_unsigned x - dst))).
Proof.
  intros x Hx. unfold m', apply_copy. cbn [copy_dst copy_len copy_src].
  rewrite !wa_unsigned by lia. rewrite ?unsigned_lit by lia.
  destruct (Z.leb_spec0 dst (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (dst + n)); cbn [andb]; try lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hs Hd Hn"] Lemma bytes_at_copy_other : forall A bs,
  bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= dst \/ dst + n <= A)%Z -> bytes_at segs m' A bs.
Proof.
  intros A bs (H0 & H1 & H) Hdis. split; [lia|]. split; [lia|]. intros i Hi.
  unfold mrd. rewrite copy_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

#[using="Hs Hd Hn"] Lemma wr_at_copy_other : forall A k,
  wr_at segs m A k -> (A + k <= dst \/ dst + n <= A)%Z -> wr_at segs m' A k.
Proof.
  intros A k (H0 & H1 & H) Hdis. split; [lia|]. split; [lia|]. intros i Hi.
  unfold wview. rewrite copy_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

#[using="Hs Hd Hn"] Lemma rw_cells_copy_other : forall A cs,
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= dst \/ dst + n <= A)%Z -> rw_cells segs m' A cs.
Proof.
  intros A cs [[Hwf Hb] Hw] Hdis. split; [split; [exact Hwf|]|].
  - apply bytes_at_copy_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hdis.
  - apply wr_at_copy_other; [exact Hw| exact Hdis].
Qed.

#[using="Hs Hd Hn"] Lemma ro_cells_copy_other : forall A cs,
  ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= dst \/ dst + n <= A)%Z -> ro_cells segs m' A cs.
Proof.
  intros A cs [Hwf Hb] Hdis. split; [exact Hwf|].
  apply bytes_at_copy_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hdis.
Qed.

#[using="Hs Hd Hn"] Lemma stk_copy_other : forall lo hi, stk segs m lo hi -> (hi <= dst \/ dst + n <= lo)%Z -> stk segs m' lo hi.
Proof.
  intros lo hi (H0 & H1 & H) Hdis. split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)].
  assert (E : m' (wa x) = m (wa x)). { apply copy_outside. rewrite wa_unsigned by lia. lia. }
  split. { unfold wview in *. rewrite E. exact Hw. } exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
#[using="Hs Hd Hn"] Lemma stk_copy : forall lo hi, ovl m0 src n -> stk segs m lo hi -> stk segs m' lo hi.
Proof.
  intros lo hi Hov (H0 & H1 & H). split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)].
  destruct (Z.leb_spec0 dst x); destruct (Z.ltb_spec0 x (dst + n)).
  2,3,4: assert (E : m' (wa x) = m (wa x)) by (apply copy_outside; rewrite wa_unsigned by lia; lia);
         split; [unfold wview in *; rewrite E; exact Hw | exists b; unfold mrd in *; rewrite E; exact Hb].
  assert (E : m' (wa x) = m0 (wa (src + (x - dst)))).
  { rewrite <- (wa_unsigned x) at 2 by lia. apply copy_inside. rewrite wa_unsigned by lia. lia. }
  specialize (Hov (x - dst)%Z ltac:(lia)).
  destruct (m0 (wa (src + (x - dst)))) as [b'|] eqn:Eb; [|congruence].
  split. { unfold wview. rewrite E. discriminate. } exists b'. unfold mrd. rewrite E. reflexivity.
Qed.

#[using="Hs Hd Hn"] Lemma wview_copy_mono : ovl m0 src n -> forall x, wview segs m x <> None -> wview segs m' x <> None.
Proof.
  intros Hov x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx.
  destruct (Z.leb_spec0 dst (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (dst + n)).
  2,3,4: unfold wview in *; rewrite copy_outside by lia; exact Hx.
  unfold wview. rewrite copy_inside by lia.
  specialize (Hov (bv_unsigned x - dst)%Z ltac:(lia)).
  destruct (m0 (wa (src + (bv_unsigned x - dst)))); [discriminate|congruence].
Qed.

#[using="Hs Hd Hn"] Lemma wmono_copy : forall m1, ovl m0 src n -> wmono segs m1 m -> wmono segs m1 m'.
Proof. intros m1 Hov H x Hx. apply wview_copy_mono; [exact Hov|]. apply H, Hx. Qed.

#[using="Hs Hd Hn"] Lemma munch_copy : forall W m1, munch W m1 m -> inside W dst n -> munch W m1 m'.
Proof.
  intros W m1 H Hin x Hx. pose proof (bv_unsigned_in_range 64 x).
  rewrite copy_outside. { apply H. exact Hx. }
  destruct (Z.ltb_spec0 (bv_unsigned x) dst); [lia|].
  destruct (Z.leb_spec0 (dst + n) (bv_unsigned x)); [lia|].
  exfalso. eapply (inside_not_outside W dst n (bv_unsigned x) Hin); [lia| exact Hx].
Qed.

#[using="Hs Hd Hn"] Lemma mem_inv_copy : mem_inv segs m -> (forall x : word, (dst <= bv_unsigned x < dst + n)%Z -> ro_addr segs x = false) ->
  mem_inv segs m'.
Proof.
  intros Hinv Hro x b Hx. pose proof (bv_unsigned_in_range 64 x).
  destruct (Z.leb_spec0 dst (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (dst + n)).
  2,3,4: rewrite copy_outside in Hx by lia; exact (Hinv _ _ Hx).
  apply Hro. lia.
Qed.

(* [comment removed for export] *)
#[using="Hs Hd Hn"] Lemma ovl_copy_moved : forall A k, (dst + n <= 2^64)%Z ->
  ovl m0 A k -> (src <= A)%Z -> (A + k <= src + n)%Z -> (0 <= k)%Z -> ovl m' (A + (dst - src)) k.
Proof.
  intros A k Hdn Hov HA HAk Hk i Hi.
  replace (A + (dst - src) + i)%Z with (dst + (A - src + i))%Z by lia.
  rewrite copy_inside by (rewrite wa_unsigned by lia; lia). rewrite wa_unsigned by lia.
  replace (src + (dst + (A - src + i) - dst))%Z with (A + i)%Z by lia. apply Hov. exact Hi.
Qed.

#[using="Hs Hd Hn"] Lemma bytes_at_copy_moved : forall A bs, (dst + n <= 2^64)%Z ->
  bytes_at segs m0 A bs -> ovl m0 A (Z.of_nat (length bs)) ->
  (src <= A)%Z -> (A + Z.of_nat (length bs) <= src + n)%Z ->
  bytes_at segs m' (A + (dst - src)) bs.
Proof.
  intros A bs Hdn (H0 & H1 & H) Hov HA HAl. split; [lia|]. split; [lia|]. intros i Hi.
  specialize (H i Hi). specialize (Hov (Z.of_nat i) ltac:(lia)).
  unfold mrd in *. replace (A + (dst - src) + Z.of_nat i)%Z with (dst + (A - src + Z.of_nat i))%Z by lia.
  rewrite copy_inside by (rewrite wa_unsigned by lia; lia). rewrite wa_unsigned by lia.
  replace (src + (dst + (A - src + Z.of_nat i) - dst))%Z with (A + Z.of_nat i)%Z by lia.
  destruct (m0 (wa (A + Z.of_nat i))) as [b|]; [exact H| congruence].
Qed.

#[using="Hs Hd Hn"] Lemma wr_at_copy_moved : forall A k, (dst + n <= 2^64)%Z ->
  ovl m0 A k -> (src <= A)%Z -> (A + k <= src + n)%Z -> (0 <= k)%Z -> wr_at segs m' (A + (dst - src)) k.
Proof.
  intros A k Hdn Hov HA HAk Hk. split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (ovl_copy_moved A k Hdn Hov HA HAk Hk i Hi) as H. unfold wview.
  destruct (m' (wa (A + (dst - src) + i))); [discriminate| congruence].
Qed.

#[using="Hs Hd Hn"] Lemma rw_cells_copy_moved : forall A cs, (dst + n <= 2^64)%Z ->
  rw_cells segs m0 A cs -> ovl m0 A (Z.of_nat (cells_size cs)) ->
  (src <= A)%Z -> (A + Z.of_nat (cells_size cs) <= src + n)%Z ->
  rw_cells segs m' (A + (dst - src)) cs.
Proof.
  intros A cs Hdn [[Hwf Hb] Hw] Hov HA HAs. split; [split; [exact Hwf|]|].
  - apply bytes_at_copy_moved; [exact Hdn| exact Hb| | exact HA|]; rewrite cells_bytes_length by assumption; [exact Hov| exact HAs].
  - apply wr_at_copy_moved; [exact Hdn| exact Hov| exact HA| exact HAs| lia].
Qed.

(* [comment removed for export] *)
#[using="Hs Hd Hn"] Lemma rw_cells_copy_moved' : forall A cs, (dst + n <= 2^64)%Z ->
  (forall x : word, (src <= bv_unsigned x < src + n)%Z -> wview segs m0 x = m0 x) ->
  rw_cells segs m0 A cs -> (src <= A)%Z -> (A + Z.of_nat (cells_size cs) <= src + n)%Z ->
  rw_cells segs m' (A + (dst - src)) cs.
Proof.
  intros A cs Hdn Hwo H HA HAs. apply rw_cells_copy_moved; [exact Hdn| exact H| |exact HA|exact HAs].
  apply ovl_of_wr_at; [exact (proj2 H)|]. intros x Hx. apply Hwo. lia.
Qed.
End Copy.

(* [comment removed for export] *)
#[using="Type"] Lemma ovl_zeros_new : forall m a n, (0 <= a)%Z -> (0 <= n < 2^64)%Z -> (a + n <= 2^64)%Z ->
  ovl (apply_zeros m [(wa a, Z_to_bv 64 n)]) a n.
Proof.
  intros m a n Ha Hn Han i Hi. rewrite (zeros_inside m a n) by (try rewrite wa_unsigned by lia; lia). discriminate.
Qed.

#[using="Type"] Lemma ovl_zeros : forall m a n z k, (0 <= a)%Z -> (a + n <= 2^64)%Z -> (0 <= z < 2^64)%Z -> (0 <= k < 2^64)%Z -> (z + k <= 2^64)%Z ->
  ovl m a n -> ovl (apply_zeros m [(wa z, Z_to_bv 64 k)]) a n.
Proof.
  intros m a n z k Ha Han Hz Hk Hzk H i Hi. rewrite apply_zeros_spec by lia.
  destruct (in_range z k (wa (a + i))); [discriminate| apply H; exact Hi].
Qed.

#[using="Type"] Lemma ovl_unmaps_other : forall m a n u k, (0 <= a)%Z -> (a + n <= 2^64)%Z -> (0 <= u < 2^64)%Z -> (0 <= k < 2^64)%Z -> (u + k <= 2^64)%Z ->
  (a + n <= u \/ u + k <= a)%Z ->
  ovl m a n -> ovl (apply_unmaps m [(wa u, Z_to_bv 64 k)]) a n.
Proof.
  intros m a n u k Ha Han Hu Hk Huk Hdis H i Hi. rewrite (unmaps_outside m u k) by (try rewrite wa_unsigned by lia; lia).
  apply H. exact Hi.
Qed.

#[using="Type"] Lemma ovl_write : forall m a n a' bs,
  ovl m a n -> (0 <= a)%Z -> (a + n <= 2^64)%Z -> (0 <= a')%Z -> (a' + Z.of_nat (length bs) <= 2^64)%Z ->
  ovl (write_to_mem m (wa a') bs) a n.
Proof.
  intros m a n a' bs H Ha Han Ha' Hbs i Hi.
  rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a' (a + i)); destruct (Z.ltb_spec0 (a + i) (a' + Z.of_nat (length bs))); cbn [andb];
    try (apply H; exact Hi).
  destruct (nth_error bs (Z.to_nat (a + i - a'))) eqn:E; [discriminate|].
  apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
Section MremapMove.
Variables (m : word -> option byte) (old on dst nn : Z).
Hypothesis Hold : (0 <= old < 2^64)%Z.
Hypothesis Holdn : (old + on <= 2^64)%Z.
Hypothesis Hdst : (0 <= dst < 2^64)%Z.
Hypothesis Hdstn : (dst + nn < 2^64)%Z.
Hypothesis Hon : (0 <= on < 2^64)%Z.
Hypothesis Hnn : (on <= nn < 2^64)%Z.
Hypothesis Hdis : (old + on <= dst \/ dst + nn <= old)%Z.
Let m' := apply_copy m (apply_zeros (apply_unmaps m [(wa old, Z_to_bv 64 on)]) [(wa (dst + on), Z_to_bv 64 (nn - on))])
                     (mkCopy (wa old) (wa dst) (Z_to_bv 64 on)).

#[using="Hold Hdst Hon"] Lemma mremap_move_copied : forall x : word, (dst <= bv_unsigned x < dst + on)%Z ->
  m' x = m (wa (old + (bv_unsigned x - dst))).
Proof. intros x Hx. unfold m'. rewrite (copy_inside m _ old dst on) by lia. reflexivity. Qed.

#[using="Hold Hdst Hdstn Hon Hnn Hdis"] Lemma mremap_move_tail : forall x : word, (dst + on <= bv_unsigned x < dst + nn)%Z -> m' x = Some (Z_to_bv 8 0).
Proof.
  intros x Hx. unfold m'. rewrite (copy_outside m _ old dst on) by lia.
  apply (zeros_inside _ (dst + on) (nn - on)); lia.
Qed.

#[using="Hold Holdn Hdst Hdstn Hon Hnn Hdis"] Lemma mremap_move_old : forall x : word, (old <= bv_unsigned x < old + on)%Z -> m' x = None.
Proof.
  intros x Hx. unfold m'. rewrite (copy_outside m _ old dst on) by lia.
  rewrite (zeros_outside _ (dst + on) (nn - on)) by lia.
  rewrite apply_unmaps_spec by lia. unfold in_range.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

#[using="Hold Holdn Hdst Hdstn Hon Hnn"] Lemma mremap_move_outside : forall x : word,
  (bv_unsigned x < dst \/ dst + nn <= bv_unsigned x)%Z -> (bv_unsigned x < old \/ old + on <= bv_unsigned x)%Z ->
  m' x = m x.
Proof.
  intros x H1 H2. unfold m'. rewrite (copy_outside m _ old dst on) by lia.
  rewrite (zeros_outside _ (dst + on) (nn - on)) by lia. apply (unmaps_outside m old on); lia.
Qed.

(* [comment removed for export] *)
#[using="Hold Hdst Hdstn Hon Hnn"] Lemma mremap_move_rw_cells : forall A cs,
  (forall x : word, (old <= bv_unsigned x < old + on)%Z -> wview segs m x = m x) ->
  rw_cells segs m A cs -> (old <= A)%Z -> (A + Z.of_nat (cells_size cs) <= old + on)%Z ->
  rw_cells segs m' (A + (dst - old)) cs.
Proof. intros A cs Hwo H HA HAs. unfold m'. apply rw_cells_copy_moved'; try assumption; lia. Qed.

#[using="Hold Holdn Hdst Hdstn Hon Hnn"] Lemma mremap_move_mem_inv :
  mem_inv segs m -> (forall x : word, (dst <= bv_unsigned x < dst + nn)%Z -> ro_addr segs x = false) -> mem_inv segs m'.
Proof.
  intros Hinv Hro. unfold m'. apply mem_inv_copy; try lia.
  - apply mem_inv_zeros; try lia. { apply mem_inv_unmaps; try lia. exact Hinv. } intros x Hx. apply Hro. lia.
  - intros x Hx. apply Hro. lia.
Qed.

#[using="Hold Holdn Hdst Hdstn Hon Hnn"] Lemma mremap_move_stk : forall lo hi,
  (forall x : word, (old <= bv_unsigned x < old + on)%Z -> wview segs m x = m x) -> wr_at segs m old on ->
  stk segs m lo hi -> (hi <= old \/ old + on <= lo)%Z -> stk segs m' lo hi.
Proof.
  intros lo hi Hwo Hwr H Hd. unfold m'. apply stk_copy; try lia.
  - apply ovl_of_wr_at; [exact Hwr| exact Hwo].
  - apply stk_zeros; try lia. apply stk_unmaps_other; try lia. exact H.
Qed.
End MremapMove.

End MemEffects.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_wr_at : forall segs m A cs n,
  rw_cells segs m A cs -> (n <= Z.of_nat (cells_size cs))%Z -> wr_at segs m A n.
Proof. intros segs m A cs n [_ (H0 & H1 & H)] Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. Qed.

Lemma rw_cells_bytes_at : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

Lemma ro_cells_bytes_at : forall segs m A cs, ro_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [_ H]. exact H. Qed.

(* [comment removed for export] *)
Ltac at_node_solve :=
  at_node_red; split_spine;
  first [ reflexivity | lia | assumption
        | symmetry; apply Z_to_bv_bv_unsigned
        | lazymatch goal with
          | |- wr_at ?segs ?m ?A ?n =>
              match goal with H : rw_cells segs m A ?cs |- _ =>
                apply (rw_cells_wr_at segs m A cs n H); cbn [cells_size csize]; lia end
          | |- bytes_at ?segs ?m ?A ?bs =>
              match goal with
              | H : rw_cells segs m A ?cs |- _ =>
                apply (bytes_at_ext segs m A _ bs (rw_cells_bytes_at segs m A cs H));
                cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
              | H : ro_cells segs m A ?cs |- _ =>
                apply (bytes_at_ext segs m A _ bs (ro_cells_bytes_at segs m A cs H));
                cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
              end
          end
        | idtac ].

(* [comment removed for export] *)
Ltac sys_mem_write :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?ro) =>
    change (write_to_mem m (Z_to_bv 64 B) bs) with (write_to_mem m (wa B) bs);
    lazymatch goal with
    | H : rw_cells segs m B [CB ?n ?junk] |- _ =>
        let HB := fresh "HB" in
        pose proof (rw_cells_bound segs m B _ H) as HB; sl_lit_sizes_in HB; cbn [cells_size csize Nat.add] in HB;   (* [comment removed for export] *)
        (try lazymatch goal with
         | HI : mem_inv segs m |- _ =>
             let HI' := fresh "MI" in
             pose proof (mem_inv_syswrite segs m B n junk bs HI H ltac:(lia)) as HI'; clear HI; rename HI' into HI
         end);
        let H' := fresh "DST" in
        pose proof (rw_cells_CB_prefix_write segs m B n junk bs H ltac:(lia)) as H';
        clear H;
        transport_chunks segs m B bs;
        footprint_after_store segs m B bs;
        let m' := fresh "m" in
        rmx_set (write_to_mem m (wa B) bs) m';
        clear HB; try clear m; rename H' into H
    | _ => fail "sys_mem_write: no hypothesis rw_cells" segs m B "[CB _ _]"
    end
  end.

(* [comment removed for export] *)
Lemma apply_mem_zeros : forall m z, apply_writes (apply_zeros (apply_unmaps m []) [z]) [] = apply_zeros m [z].
Proof. reflexivity. Qed.
Lemma apply_mem_unmaps : forall m u, apply_writes (apply_zeros (apply_unmaps m [u]) []) [] = apply_unmaps m [u].
Proof. reflexivity. Qed.

Ltac transport_zeros segs m a n Ha Hn Han :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_zeros_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_zeros segs m a n Ha Hn Han A2 n2) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ => apply (stk_zeros segs m a n Ha Hn Han lo hi) in H
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_zeros m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "zero-filled range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => apply (wmono_zeros segs m a n Ha Hn Han m0) in H
  | H : mem_inv segs m |- _ =>
      let H' := fresh "MI" in
      assert (H' : mem_inv segs (apply_zeros m [(wa a, Z_to_bv 64 n)]))
        by (apply (mem_inv_zeros segs m a n Ha Hn Han H); first [assumption | intros; shelve]);
      clear H
  end.

Ltac sys_mem_zeros :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_zeros ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_zeros m [(A, Z_to_bv 64 n)]) with (apply_zeros m [(wa a, Z_to_bv 64 n)]);
    let Ha := fresh "Hza" in let Hn := fresh "Hzn" in let Han := fresh "Hzan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    transport_zeros segs m a n Ha Hn Han;
    let Z' := fresh "ZNEW" in
    pose proof (rw_cells_zeros_new segs m a n Ha Hn Han) as Z';
    let m' := fresh "m" in
    rmx_set (apply_zeros m [(wa a, Z_to_bv 64 n)]) m';
    clear Ha Hn Han; try clear m
  end.

Ltac transport_unmaps segs m a n Ha Hn Han :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_unmaps_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ =>
      first [ apply (wr_at_unmaps_other segs m a n Ha Hn Han A2 n2) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ =>
      first [ apply (stk_unmaps_other segs m a n Ha Hn Han lo hi) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_unmaps m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "unmapped range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => idtac "note: dropping wmono (not preserved by an unmap):" H; clear H
  | H : mem_inv segs m |- _ => apply (mem_inv_unmaps segs m a n Ha Hn Han) in H
  end.

Ltac sys_mem_unmaps :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_unmaps ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_unmaps m [(A, Z_to_bv 64 n)]) with (apply_unmaps m [(wa a, Z_to_bv 64 n)]);
    let Ha := fresh "Hua" in let Hn := fresh "Hun" in let Han := fresh "Huan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    transport_unmaps segs m a n Ha Hn Han;
    let m' := fresh "m" in
    rmx_set (apply_unmaps m [(wa a, Z_to_bv 64 n)]) m';
    clear Ha Hn Han; try clear m
  end.

(* [comment removed for export] *)
Lemma apply_mem_mremap_move : forall m u z c,
  apply_writes (apply_copies m (apply_zeros (apply_unmaps m [u]) [z]) [c]) [] = apply_copy m (apply_zeros (apply_unmaps m [u]) [z]) c.
Proof. reflexivity. Qed.

Ltac transport_copy segs m0 m src dst n Hs Hd Hn :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_copy_other segs m0 m src dst n Hs Hd Hn A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably clear of the copy destination):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ =>
      first [ apply (wr_at_copy_other segs m0 m src dst n Hs Hd Hn A2 n2) in H; [|slia]
            | idtac "note: dropping hypothesis (not provably clear of the copy destination):" H; clear H ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_copy_other segs m0 m src dst n Hs Hd Hn A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably clear of the copy destination):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_copy_other segs m0 m src dst n Hs Hd Hn A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably clear of the copy destination):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ =>
      first [ match goal with OV : ovl m0 src n |- _ => apply (stk_copy segs m0 m src dst n Hs Hd Hn lo hi OV) in H end
            | apply (stk_copy_other segs m0 m src dst n Hs Hd Hn lo hi) in H; [|slia]
            | idtac "note: dropping stk (not provably clear of the copy destination; an [ovl] fact on the source would keep it):" H; clear H ]
  | H : munch ?W ?m1 m |- _ =>
      first [ apply (munch_copy m0 m src dst n Hs Hd Hn W m1) in H; [|cbn [inside]; slia]
            | fail 100 "copy destination not inside the declared footprint" ]
  | H : wmono segs ?m1 m |- _ =>
      first [ match goal with OV : ovl m0 src n |- _ => apply (wmono_copy segs m0 m src dst n Hs Hd Hn m1 OV) in H end
            | idtac "note: dropping wmono (an [ovl] fact on the source would keep it):" H; clear H ]
  | H : mem_inv segs m |- _ =>
      let H' := fresh "MI" in
      assert (H' : mem_inv segs (apply_copy m0 m (mkCopy (wa src) (wa dst) (Z_to_bv 64 n))))
        by (apply (mem_inv_copy segs m0 m src dst n Hs Hd Hn H); first [assumption | intros; shelve]);
      clear H
  end.

(* [comment removed for export] *)
Ltac relocate_chunks segs m mX src dst n Hs Hd Hn Hdn :=
  repeat match goal with
  | H : rw_cells segs m ?A ?cs |- _ =>
      let H' := fresh "MV" in
      first [ match goal with OV : ovl m src n |- _ =>
                pose proof (rw_cells_copy_moved segs m mX src dst n Hs Hd Hn A cs Hdn H
                              (ovl_sub m src n A (Z.of_nat (cells_size cs)) OV ltac:(slia) ltac:(simpl_sizes; slia))
                              ltac:(slia) ltac:(simpl_sizes; slia)) as H'
                end
              | match goal with WO : forall x : word, _ -> wview segs m x = m x |- _ =>
                pose proof (rw_cells_copy_moved' segs m mX src dst n Hs Hd Hn A cs Hdn WO H ltac:(slia) ltac:(simpl_sizes; slia)) as H'
                end ];
      cbn [Z.add Z.sub] in H'; clear H
  end.

Ltac sys_mem_mremap_move :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv
         (apply_copy ?m (apply_zeros (apply_unmaps ?m [(?UA, Z_to_bv 64 ?un)]) [(?ZA, Z_to_bv 64 ?zn)])
                     (mkCopy ?CS ?CD (Z_to_bv 64 ?cn))) ?ro) =>
    let old := lazymatch UA with wa ?a => a | Z_to_bv 64 ?a => a end in
    let za := lazymatch ZA with wa ?a => a | Z_to_bv 64 ?a => a end in
    let dst := lazymatch CD with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_copy m (apply_zeros (apply_unmaps m [(UA, Z_to_bv 64 un)]) [(ZA, Z_to_bv 64 zn)]) (mkCopy CS CD (Z_to_bv 64 cn)))
      with (apply_copy m (apply_zeros (apply_unmaps m [(wa old, Z_to_bv 64 un)]) [(wa za, Z_to_bv 64 zn)]) (mkCopy (wa old) (wa dst) (Z_to_bv 64 cn)));
    let Hs := fresh "Hcs" in let Hd := fresh "Hcd" in let Hn := fresh "Hcn" in let Hdn := fresh "Hcdn" in
    assert (Hs : (0 <= old < 2^64)%Z) by lia;
    assert (Hd : (0 <= dst < 2^64)%Z) by lia;
    assert (Hn : (0 <= cn < 2^64)%Z) by lia;
    assert (Hdn : (dst + cn <= 2^64)%Z) by lia;
    (* [comment removed for export] *)
    relocate_chunks segs m (apply_zeros (apply_unmaps m [(wa old, Z_to_bv 64 un)]) [(wa za, Z_to_bv 64 zn)]) old dst cn Hs Hd Hn Hdn;
    (* [comment removed for export] *)
    let Hua := fresh "Hua" in let Hun := fresh "Hun" in let Huan := fresh "Huan" in
    assert (Hua : (0 <= old < 2^64)%Z) by lia;
    assert (Hun : (0 <= un < 2^64)%Z) by lia;
    assert (Huan : (old + un <= 2^64)%Z) by lia;
    transport_unmaps segs m old un Hua Hun Huan;
    let m1 := fresh "m" in
    rmx_set (apply_unmaps m [(wa old, Z_to_bv 64 un)]) m1; clear Hua Hun Huan;
    (* [comment removed for export] *)
    let Hza := fresh "Hza" in let Hzn := fresh "Hzn" in let Hzan := fresh "Hzan" in
    assert (Hza : (0 <= za < 2^64)%Z) by lia;
    assert (Hzn : (0 <= zn < 2^64)%Z) by lia;
    assert (Hzan : (za + zn <= 2^64)%Z) by lia;
    transport_zeros segs m1 za zn Hza Hzn Hzan;
    let Z' := fresh "ZNEW" in
    pose proof (rw_cells_zeros_new segs m1 za zn Hza Hzn Hzan) as Z';
    let m2 := fresh "m" in
    rmx_set (apply_zeros m1 [(wa za, Z_to_bv 64 zn)]) m2; clear Hza Hzn Hzan; try clear m1;
    (* [comment removed for export] *)
    transport_copy segs m m2 old dst cn Hs Hd Hn;
    let m3 := fresh "m" in
    rmx_set (apply_copy m m2 (mkCopy (wa old) (wa dst) (Z_to_bv 64 cn))) m3;
    clear Hs Hd Hn Hdn; try clear m2;
    repeat match goal with
           | OV : ovl m _ _ |- _ => clear OV
           | WO : forall x : word, _ -> wview segs m x = m x |- _ => clear WO
           end;
    try clear m
  end.

(* [comment removed for export] *)
Ltac sys_nret :=
  first [ rewrite nret_MSsvc | rewrite nret_MSsvc_copies ]; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   | _ => idtac
   end);
  first [ rewrite apply_mem_none
        | rewrite apply_mem_delivered; sys_mem_write
        | rewrite apply_mem_write; sys_mem_write
        | rewrite apply_mem_zeros; sys_mem_zeros
        | rewrite apply_mem_unmaps; sys_mem_unmaps
        | rewrite apply_mem_mremap_move; sys_mem_mremap_move
        | idtac ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Notation errno_addr tp := (bv_unsigned tp + (-164))%Z (only parsing).

(* [comment removed for export] *)
Definition sysret_val (r : word) : word :=
  match errno_of r with Some _ => Z_to_bv 64 (-1) | None => r end.
Definition sysret_errno (r errv : word) : word :=
  match errno_of r with Some e => Z_to_bv 64 e | None => errv end.

Lemma errno_of_big : forall r, (2^64 - 4096 < bv_unsigned r)%Z -> errno_of r = Some (2^64 - bv_unsigned r)%Z.
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [reflexivity|lia]. Qed.

(* [comment removed for export] *)
Lemma negw_errno : forall u, (2^64 - 4096 < u < 2^64)%Z -> bv_swrap 32 (0 - u) = (2^64 - u)%Z.
Proof.
  intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  replace (0 - u + 2^31)%Z with ((2^64 - u + 2^31) + (- 2^32) * 2^32)%Z by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma swrap32_small : forall z, (-2^31 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma swrap32_high : forall u, (2^64 - 2^31 <= u < 2^64)%Z -> bv_swrap 32 u = (u - 2^64)%Z.
Proof.
  intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  replace (u + 2^31)%Z with ((u - 2^64 + 2^31) + 2^32 * 2^32)%Z by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma unsigned_errno_ret : forall e, (1 <= e <= 4095)%Z -> bv_unsigned (errno_ret e) = (2^64 - e)%Z.
Proof. intros. rewrite errno_ret_unsigned by lia. reflexivity. Qed.

Lemma Z_to_bv_minus_mod : forall z, Z_to_bv 64 (z - 2^64) = Z_to_bv 64 z.
Proof.
  intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
  replace (z - 2^64)%Z with (z + (-1) * 2^64)%Z by lia. apply Z.mod_add. lia.
Qed.

Lemma errno_ret_fold : forall e, Z_to_bv 64 (- e) = errno_ret e.
Proof. reflexivity. Qed.

Lemma sextw_errno : forall e, (1 <= e <= 2^31)%Z ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (errno_ret e) + 0)) = errno_ret e.
Proof.
  intros e He. unfold errno_ret. rewrite unsigned_lit_wrap.
  replace ((- e) mod 2^64)%Z with (2^64 - e)%Z.
  2:{ replace (-e)%Z with ((2^64 - e) + (-1) * 2^64)%Z by lia. rewrite Z.mod_add; [|lia]. rewrite Z.mod_small; [reflexivity|lia]. }
  rewrite Z.add_0_r, swrap32_high by lia. f_equal. lia.
Qed.

Lemma sextw_small : forall z, (0 <= z < 2^31)%Z ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 0)) = Z_to_bv 64 z.
Proof. intros z Hz. rewrite unsigned_lit by lia. rewrite Z.add_0_r, swrap32_small by lia. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stk_lo_nonneg : forall segs m lo hi, stk segs m lo hi -> (0 <= lo)%Z.
Proof. intros segs m lo hi (H & _). exact H. Qed.

Ltac name_sp sp k :=
  let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
  remember (Z_to_bv 64 (bv_unsigned sp + k)) as sp1 eqn:E;
  assert (H : bv_unsigned sp1 = (bv_unsigned sp + k)%Z)
    by (rewrite E; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *;
        try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg _ _ _ _ ST) end;
        apply unsigned_lit; lia).

Ltac unname_sp :=
  match goal with
  | H : bv_unsigned ?sp1 = (bv_unsigned ?sp + ?k)%Z, E : ?sp1' = Z_to_bv 64 (bv_unsigned ?sp + ?k) |- _ =>
      constr_eq sp1 sp1';
      (* [comment removed for export] *)
      repeat match goal with K : context [bv_unsigned sp1] |- _ => tryif constr_eq K H then fail else rewrite H in K end;
      try rewrite H; clear H; subst sp1
  end.

Tactic Notation "call_sp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
      name_sp sp k; call SPEC; unname_sp
  | |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_sp sp k; call SPEC; unname_sp
  | _ => call SPEC
  end.

(* [comment removed for export] *)
Ltac sys_finish :=
  (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
  | |- _ = _ => cbv delta [mkR]; reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma impl_from_evt : forall {node : Type} segs (atn : node -> machine_state -> Prop)
    (npk : node -> option (machine_state -> resp)) {R} (t : itree node R) Q ms,
  evt segs (fun ms' => impl segs atn npk t Q ms') ms -> impl segs atn npk t Q ms.
Proof. intros node segs atn npk R t Q ms H. eapply impl_evt; [exact H|]. intros ms' H'; exact H'. Qed.

Ltac iprefix := apply impl_from_evt.
Ltac ihere := apply evt_done.

(* [comment removed for export] *)
Tactic Notation "icall" uconstr(SPEC) :=
  (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
  first [ eapply SPEC
        | eapply impl_epost_mono; [ eapply SPEC | ] ].

(* [comment removed for export] *)
Ltac ipost segs :=
  let a := fresh "ans" in let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros a ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ ?m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (let MIname := fresh "MI" in
       lazymatch goal with H : mem_inv segs _ |- _ => rename H into MIname; try rename MIname into MI end);
  (* [comment removed for export] *)
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
