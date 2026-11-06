(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module names, addresses and numbers changed; 893 of its 1109 lines of code are new or changed and 180 lines of the source are left out. *)
(* Segment P1 (0x81ac0, plan-asan 1) of fuzz_ctrl LLVMFuzzerTestOneInput (asan, libreac v1.9.0 image A; v1.8
   0x81a68 .. 0x81ab8, IDENTICAL: every pc +0x58): the run from the cut
   0x81ac0 to the cut 0x81b10 that marks the frame shadow of out[] unusable again.
     81ac0: beqz a0,81ac8          (a0 = 0 at the cut, so the branch is taken)
     81ac8: li   s2,-8
     81acc..81b00: 14 one-byte stores sb s2,K(s3), K = 285 286 287 288 276 282 283 284 289 290 272 273 274 275
                   (s3 = S(fr): frame shadow bytes set to 0xf8, variable out of scope)
     81b04: li   a1,187
     81b08: ld   a0,152(s1)        (a0 = Q, the spill at s1+152; S(fr) <= Q, Q+187 <= S(fr)+328)
     81b0c: jal  55008             (__asan_set_shadow_f8(Q, 187): sets 187 shadow bytes from Q to 0xf8 by musl memset)
   The code at 0x81a7c (beqz a0,81ac8) also enters the segment at 0x81ac8, so the proof has two lemmas: seg_P1_70
   (cut Inv_A81ac8 -> Inv_A81b10: the stores and the call) and seg_P1 (cut P1_entry at 0x81ac0: one beqz step, then
   seg_P1_70).  p1_evt is the Lib-level run from 0x81ac8 to the return at 0x81b10, with the call taken by its
   contract asan_set_shadow_f8_contract (a hypothesis of the segment lemmas; linking happens later).  Every write of
   the run is a frame shadow byte in [S(fr), S(fr) + 328), so FRA moves by the frame-and-shadow transport
   sl_fr_meta and PRO (aslot pushes 13 / 14; v1.9 adds its 16th conjunct, the spill [A + 32] = fr + 2880) by
   pro_fra, defined here for P1 .. P11.  All cuts are SlotInv's:
   since push 14A the entry cuts bound the call range by Q + 187 <= S(fr) + 328, below our[]'s shadow byte.
   The callee contract needs mem_inv of the memory at the call, which no cut carries (push 5d): p1_evt_ro runs
   p1_evt on the normalized memory from FRA's ro_agree (MemNorm.evt_normalize).
   v1.9: this file also holds the allocator-law projections p1_laws_store, p1_laws_fs_store, p1_laws_fs_place,
   p1_laws_blocks and p1_fs_ok_of_state (Section PRO), which take the results of AC.a_laws_store / a_laws_fs_store /
   a_laws_fs_place / a_laws_blocks / a_laws_fs_state apart in one place for P1 .. P9, because a Theorem Labs lane's generated
   laws grow by appending at every nesting level.
   Route (C) (a Theorem Labs lane's frozen form, ASSIGN.md (a working note, not in this delivery)): each lemma with a universal shadow_rw premise or
   conclusion has an X_on twin that carries the proof; X keeps its statement as a corollary of X_on.  X_on's premise
   is A.ShadowRwOn.shadow_rw_on X_shadow_R m, X_shadow_R the shadow bytes the run needs present and writable; its
   post `forall P, shadow_rw_on P m -> shadow_rw_on P m'`.  The run reads no shadow byte (no shadow check between
   0x81ac0 and 0x81b10; __asan_set_shadow_f8's contract takes its destination as rw_cells, no shadow_rw): its
   region is the 14 store targets, which store_ok needs writable, and the callee's destination [Q, Q + 187), which
   p1_rw_of_shadow_on turns into the contract's rw_cells.  p1_shadow_rw_norm / p1_shadow_rw_back are transports
   (no _on twin; the _on proofs use A.ShadowRwOnT's shadow_rw_on_rel / shadow_rw_on_of_rel). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_set_shadow_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn.
Import ListNotations.
Open Scope Z_scope.

(* ---- Lib-level run lemma p1_evt and its memory helpers. ---- *)

(* The memory invariant along the 14 shadow stores: writes only inside [Sh, Sh + 328) since m0 (the stores and the
   call stay below our[]'s shadow byte Sh + 328), writability kept, every shadow byte present and writable,
   mem_inv. *)
Definition p1_J (m0 : word -> option byte) (Sh : Z) (m : word -> option byte) : Prop :=
  munch [(Sh, Sh + 328)] m0 m /\ wmono rsegs m0 m /\ shadow_rw m /\ mem_inv rsegs m.

(* Route (C): p1_J with shadow_rw m replaced by its keep form, every region present and writable at m0 still is at
   m.  The region the stores need is the run's premise at m0, read through the keep conjunct. *)
Definition p1_J_on (m0 : word -> option byte) (Sh : Z) (m : word -> option byte) : Prop :=
  munch [(Sh, Sh + 328)] m0 m /\ wmono rsegs m0 m /\
  (forall P, A.ShadowRwOn.shadow_rw_on P m0 -> A.ShadowRwOn.shadow_rw_on P m) /\ mem_inv rsegs m.

(* No shadow byte is read: the premise is dropped. *)
Lemma p1_J_init_on : forall m Sh, mem_inv rsegs m -> p1_J_on m Sh m.
Proof.
  intros m Sh HMI. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [intros P H; exact H | exact HMI].
Qed.

Lemma p1_J_init : forall m Sh, shadow_rw m -> mem_inv rsegs m -> p1_J m Sh m.
Proof.
  intros m Sh HSW HMI. destruct (p1_J_init_on m Sh HMI) as (MU & WM & _ & MI). exact (conj MU (conj WM (conj HSW MI))).
Qed.

Lemma p1_J_store_ok : forall m0 Sh m a, p1_J m0 Sh m -> in_shadow a -> store_ok rsegs m (wa a) 1 = true.
Proof.
  intros m0 Sh m a (_ & _ & HSW & _) Ha.
  pose proof (in_shadow_range a Ha) as Hr.
  assert (WR : wr_at rsegs m a 1).
  { split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r.
    exact (proj1 (HSW a Ha)). }
  pose proof (wr_at_store_ok rsegs m a 1 0 1%nat WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

Lemma p1_J_store : forall m0 Sh m a bs, p1_J m0 Sh m -> Sh <= a < Sh + 328 -> in_shadow a -> length bs = 1%nat ->
  p1_J m0 Sh (write_to_mem m (wa a) bs).
Proof.
  intros m0 Sh m a bs HJ Hin Ha Hl.
  pose proof (in_shadow_range a Ha) as Hr.
  pose proof (p1_J_store_ok m0 Sh m a HJ Ha) as HS.
  destruct HJ as (MU & WM & HSW & HMI).
  split; [|split; [|split]].
  - apply munch_write; [exact MU | lia | rewrite Hl; lia | rewrite Hl; cbn [inside]; left; lia].
  - apply wmono_write. exact WM.
  - intros x Hx. pose proof (in_shadow_range x Hx) as Hxr. split.
    + apply wview_write_mono. exact (proj1 (HSW x Hx)).
    + unfold mrd. rewrite write_to_mem_spec by (rewrite ?Hl; lia).
      rewrite wa_unsigned by lia.
      destruct (Z.leb a x && Z.ltb x (a + Z.of_nat (length bs)))%bool eqn:E.
      * apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite Hl in E2.
        assert (x = a) by lia. subst x. rewrite Z.sub_diag.
        destruct bs as [|b [|b1 bs']]; cbn in Hl; try discriminate. exists b. reflexivity.
      * destruct (proj2 (HSW x Hx)) as (b & Hb). unfold mrd in Hb. exists b. exact Hb.
  - apply mem_inv_store; [exact HMI | rewrite Hl; exact HS].
Qed.

(* p1_J_store_ok for p1_J_on: the store target a is in a region R present and writable at m0. *)
Lemma p1_J_on_store_ok : forall (R : Z -> Prop) m0 Sh m a, p1_J_on m0 Sh m -> A.ShadowRwOn.shadow_rw_on R m0 ->
  R a -> in_shadow a -> store_ok rsegs m (wa a) 1 = true.
Proof.
  intros R m0 Sh m a (_ & _ & HK & _) HR Ra Ha.
  pose proof (in_shadow_range a Ha) as Hr.
  assert (WR : wr_at rsegs m a 1).
  { split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r.
    exact (proj1 (HK R HR a Ra Ha)). }
  pose proof (wr_at_store_ok rsegs m a 1 0 1%nat WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

(* p1_J_store for p1_J_on: a one-byte store at a frame-shadow byte keeps every present and writable region. *)
Lemma p1_J_on_store : forall m0 Sh m a bs, p1_J_on m0 Sh m -> Sh <= a < Sh + 328 -> in_shadow a ->
  length bs = 1%nat -> store_ok rsegs m (wa a) 1 = true -> p1_J_on m0 Sh (write_to_mem m (wa a) bs).
Proof.
  intros m0 Sh m a bs HJ Hin Ha Hl HS.
  pose proof (in_shadow_range a Ha) as Hr.
  destruct HJ as (MU & WM & HK & HMI).
  split; [|split; [|split]].
  - apply munch_write; [exact MU | lia | rewrite Hl; lia | rewrite Hl; cbn [inside]; left; lia].
  - apply wmono_write. exact WM.
  - intros P HP x HPx Hx. pose proof (in_shadow_range x Hx) as Hxr. destruct (HK P HP x HPx Hx) as (Hw & Hb).
    split.
    + apply wview_write_mono. exact Hw.
    + unfold mrd. rewrite write_to_mem_spec by (rewrite ?Hl; lia).
      rewrite wa_unsigned by lia.
      destruct (Z.leb a x && Z.ltb x (a + Z.of_nat (length bs)))%bool eqn:E.
      * apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite Hl in E2.
        assert (x = a) by lia. subst x. rewrite Z.sub_diag.
        destruct bs as [|b [|b1 bs']]; cbn in Hl; try discriminate. exists b. reflexivity.
      * destruct Hb as (b & Hb). unfold mrd in Hb. exists b. exact Hb.
  - apply mem_inv_store; [exact HMI | rewrite Hl; exact HS].
Qed.

(* The n shadow bytes from a that p1_sh_bytes reads. *)
Definition p1_sh_bytes_shadow_R (a : Z) (n : nat) : Z -> Prop := fun x => a <= x < a + Z.of_nat n.

(* n bytes from a, all shadow bytes present in m, are present: some list sh is at a. *)
Lemma p1_sh_bytes_on : forall m a (n : nat), A.ShadowRwOn.shadow_rw_on (p1_sh_bytes_shadow_R a n) m ->
  (forall i, 0 <= i < Z.of_nat n -> in_shadow (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists sh, bytes_at rsegs m a sh /\ length sh = n.
Proof.
  intros m a n HSW HS Ha Hn.
  exists (map (fun i : nat => match mrd rsegs m (wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end)
            (seq 0 n)).
  assert (HL : length (map (fun i : nat => match mrd rsegs m (wa (a + Z.of_nat i)) with
                                           | Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)) = n)
    by (rewrite length_map, length_seq; reflexivity).
  split; [|exact HL].
  unfold bytes_at. split; [exact Ha|]. split; [rewrite HL; exact Hn|].
  intros i Hi. rewrite HL in Hi.
  rewrite nth_error_map.
  rewrite (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; exact Hi).
  rewrite seq_nth by exact Hi. cbn [option_map Nat.add].
  destruct (HSW (a + Z.of_nat i) ltac:(unfold p1_sh_bytes_shadow_R; lia) (HS (Z.of_nat i) ltac:(lia)))
    as (_ & b & Hb).
  rewrite Hb. reflexivity.
Qed.

(* n bytes from a, all shadow bytes of a memory with shadow_rw, are present: some list sh is at a. *)
Lemma p1_sh_bytes : forall m a (n : nat), shadow_rw m ->
  (forall i, 0 <= i < Z.of_nat n -> in_shadow (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists sh, bytes_at rsegs m a sh /\ length sh = n.
Proof. intros m a n HSW. exact (p1_sh_bytes_on m a n (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW)). Qed.

(* p1_rw_of_shadow reads p1_sh_bytes's bytes and needs the same bytes writable. *)
Definition p1_rw_of_shadow_shadow_R (a : Z) (n : nat) : Z -> Prop := fun x => p1_sh_bytes_shadow_R a n x.

(* The same bytes as one writable CB cell (the callee contract's destination form). *)
Lemma p1_rw_of_shadow_on : forall m a (n : nat), A.ShadowRwOn.shadow_rw_on (p1_rw_of_shadow_shadow_R a n) m ->
  (forall i, 0 <= i < Z.of_nat n -> in_shadow (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists junk, rw_cells rsegs m a [CB n junk].
Proof.
  intros m a n HSW HS Ha Hn.
  destruct (p1_sh_bytes_on m a n HSW HS Ha Hn) as (sh & Hb & Hl).
  exists sh. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact Hl | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. unfold wr_at. split; [exact Ha|]. split; [exact Hn|].
    intros i Hi.
    exact (proj1 (HSW (a + i) ltac:(unfold p1_rw_of_shadow_shadow_R, p1_sh_bytes_shadow_R; lia) (HS i Hi))).
Qed.

(* The same bytes as one writable CB cell (the callee contract's destination form). *)
Lemma p1_rw_of_shadow : forall m a (n : nat), shadow_rw m ->
  (forall i, 0 <= i < Z.of_nat n -> in_shadow (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists junk, rw_cells rsegs m a [CB n junk].
Proof. intros m a n HSW. exact (p1_rw_of_shadow_on m a n (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW)). Qed.

(* Every region present and writable before the callee still is after it: the callee writes [Q, Q + N) and
   leaves its N bytes present (rw_cells).  No shadow byte is read: no premise. *)
Lemma p1_shadow_rw_call_on : forall m m' Q N bs, munch [(Q, Q + N)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' Q [CB (Z.to_nat N) bs] -> 0 <= N ->
  forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros m m' Q N bs MU WM RW HN P HSW x HPx Hx. pose proof (in_shadow_range x Hx) as Hxr.
  split; [exact (WM (wa x) (proj1 (HSW x HPx Hx)))|].
  destruct RW as ((Hwf & Hb) & _). cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  destruct (Z.lt_ge_cases x Q) as [Hlt|Hge]; [|destruct (Z.lt_ge_cases x (Q + N)) as [Hlt2|Hge2]].
  - destruct (proj2 (HSW x HPx Hx)) as (b & Hb0). exists b. unfold mrd in *. rewrite MU; [exact Hb0|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
  - destruct Hb as (HQ0 & _ & Hb).
    assert (Hi : (Z.to_nat (x - Q) < length bs)%nat) by (rewrite Hl; lia).
    pose proof (Hb _ Hi) as E. rewrite Z2Nat.id in E by lia. replace (Q + (x - Q)) with x in E by lia.
    destruct (nth_error bs (Z.to_nat (x - Q))) as [b|] eqn:En; [exists b; exact E|].
    apply nth_error_None in En. lia.
  - destruct (proj2 (HSW x HPx Hx)) as (b & Hb0). exists b. unfold mrd in *. rewrite MU; [exact Hb0|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

(* shadow_rw across the callee: the callee writes [Q, Q + N) and leaves its N bytes present (rw_cells). *)
Lemma p1_shadow_rw_call : forall m m' Q N bs, shadow_rw m -> munch [(Q, Q + N)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' Q [CB (Z.to_nat N) bs] -> 0 <= N -> shadow_rw m'.
Proof.
  intros m m' Q N bs HSW MU WM RW HN. exact (A.ShadowRwOn.shadow_rw_of_on_all m' (p1_shadow_rw_call_on m m' Q N bs
    MU WM RW HN (fun _ => True) (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW))).
Qed.

(* The shadow bytes p1_evt needs present and writable: the 14 store targets S(fr) + 272 .. 276 and 282 .. 290
   (store_ok), and the callee's destination [Q, Q + 187) through p1_rw_of_shadow_on's region.  The run reads no
   shadow byte. *)
Definition p1_evt_shadow_R (Sh Q : Z) : Z -> Prop :=
  fun a => Sh + 272 <= a < Sh + 277 \/ Sh + 282 <= a < Sh + 291 \/ p1_rw_of_shadow_shadow_R Q (Z.to_nat 187) a.

(* One frame-shadow store `sb s2,K(s3)` (s3 = Sh): store_ok from the invariant and the run's region, one step, the
   invariant for the written memory, which is then named. *)
Ltac p1_sb K :=
  lazymatch goal with
  | HJ : p1_J_on ?m0 ?Sh ?mc, HSW : A.ShadowRwOn.shadow_rw_on (p1_evt_shadow_R ?Sh _) ?m0,
    HSH : forall i, 0 <= i < 392 -> in_shadow (?Sh + i) |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mc (wa (Sh + K)) 1 = true)
        by exact (p1_J_on_store_ok _ m0 Sh mc (Sh + K) HJ HSW
                    ltac:(unfold p1_evt_shadow_R; first [left; lia | right; left; lia]) (HSH K ltac:(lia)));
      step;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?aa ?bb) _) =>
          let HJ' := fresh "HJ" in
          assert (HJ' : p1_J_on m0 Sh (write_to_mem mc aa bb))
            by (apply (p1_J_on_store m0 Sh mc (Sh + K) bb HJ);
                [ lia | exact (HSH K ltac:(lia))
                | first [ reflexivity | apply length_le1 | apply length_Z_to_le_bytes ] | exact HS ]);
          try clear HS; clear HJ;
          let m' := fresh "mc" in
          set (m' := write_to_mem mc aa bb) in *; clearbody m'
      end
  end.

(* The old statement of a run from its _on twin's post: every conjunct but the last is the same, and the last,
   `forall P, shadow_rw_on P m -> shadow_rw_on P m'`, gives shadow_rw m' at P := fun _ => True. *)
Ltac p1_post_old H HSW :=
  repeat lazymatch type of H with
         | _ /\ _ => let H1 := fresh "Hc" in destruct H as [H1 H]; split; [exact H1|]
         end;
  exact (A.ShadowRwOn.shadow_rw_of_on_all _ (H (fun _ => True) (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ _ HSW))).

(* The beqz at 0x81ac0 with a0 = 0: one step to 0x81ac8, registers and memory unchanged. *)
Lemma p1_beqz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 0 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6) F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ->.
  step. try if_true.
  apply evt_done. reflexivity.
Qed.

(* The run from 0x81ac8 to the return at 0x81b10: 14 frame-shadow stores, li a1,187, the spill load a0 = Q and the
   call of __asan_set_shadow_f8(Q, 187) by its contract.  The only writes are inside [Sh, Sh + 328).  Route (C):
   the shadow bytes the run needs are p1_evt_shadow_R Sh Q; every region present and writable at entry still is at
   the return. *)
Lemma p1_evt_on : asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Sh Q : Z),
    s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sh ->
    0 <= A < 2 ^ 64 -> Sh <= Q -> Q + 187 <= Sh + 328 ->
    (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 Q)) ->
    disjoint_from [(Sh, Sh + 328)] (A + 152) 8 ->
    disjoint_from [(Sh, Sh + 328)] RT_LO (RT_HI - RT_LO) ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (p1_evt_shadow_R Sh Q) m -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b10) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(Sh, Sh + 328)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         (forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Sh Q -> -> HA HQ1 HQ2 HSH HSP HSEP HDRT HAC HSW HMI.
  unfold asan_set_shadow_f8_contract, asan_set_shadow_contract, ASAN_SET_SHADOW_F8 in SET. cbv zeta in SET.
  pose proof (in_shadow_range _ (HSH 0 ltac:(lia))) as HS0. rewrite Z.add_0_r in HS0.
  pose proof (in_shadow_range _ (HSH 391 ltac:(lia))) as HS391.
  pose proof (p1_J_init_on m Sh HMI) as HJ.
  (* li s2,-8 *)
  step.
  (* the 14 frame-shadow stores *)
  p1_sb 285. p1_sb 286. p1_sb 287. p1_sb 288. p1_sb 276. p1_sb 282. p1_sb 283. p1_sb 284.
  p1_sb 289. p1_sb 290. p1_sb 272. p1_sb 273. p1_sb 274. p1_sb 275.
  (* li a1,187 *)
  step.
  (* ld a0,152(s1): the spill is outside [Sh, Sh + 328), so it is kept *)
  lazymatch goal with
  | HJc : p1_J_on m Sh ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (HR : ov_read_bytes rsegs mc (wa (A + 152)) 8 = Some (le8 (Z_to_bv 64 Q)));
      [ destruct HJc as (MUj & _ & _ & _);
        pose proof (bytes_at_transport rsegs [(Sh, Sh + 328)] m mc (A + 152) _ HSP MUj
                      ltac:(rewrite length_le8; exact HSEP)) as Hb;
        assert (HC : cells_at rsegs mc (A + 152) [C8 (Z_to_bv 64 Q)])
          by (split; [split; exact I | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]);
        pose proof (cells_at_read rsegs mc (A + 152) [C8 (Z_to_bv 64 Q)] 0%nat (C8 (Z_to_bv 64 Q)) HC eq_refl)
          as E;
        cbn [csize cbytes Z.of_nat] in E; rewrite Z.add_0_r in E; exact E
      | ]
  end.
  step.
  clear HR.
  (* jal 55008 *)
  step.
  lazymatch goal with
  | HJc : p1_J_on m Sh ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof HJc as (MUc & WMc & KPc & HMIc);
      assert (HQi : forall i, 0 <= i < Z.of_nat (Z.to_nat 187) -> in_shadow (Q + i))
        by (intros i Hi; replace (Q + i) with (Sh + (Q - Sh + i)) by lia; apply HSH; lia);
      assert (HSWq : A.ShadowRwOn.shadow_rw_on (p1_rw_of_shadow_shadow_R Q (Z.to_nat 187)) mc)
        by (apply KPc; apply (A.ShadowRwOn.shadow_rw_on_mono (p1_evt_shadow_R Sh Q)); [|exact HSW];
            intros x Hx; unfold p1_evt_shadow_R; right; right; exact Hx);
      destruct (p1_rw_of_shadow_on mc Q (Z.to_nat 187) HSWq HQi ltac:(lia) ltac:(lia)) as (junk & RWj);
      eapply evt_cut;
      [ eapply SET with (junk := junk);
        [ rewrite !MState.unsigned_lit by lia; intros i Hi; replace (Q + i) with (Sh + (Q - Sh + i)) by lia;
          apply HSH; lia
        | rewrite !MState.unsigned_lit by lia; exact RWj
        | exact (asan_cells_kept [(Sh, Sh + 328)] m mc HAC MUc HDRT)
        | exact HMIc ]
      | ]
  end.
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & MI' & RW).
  subst ms'.
  rewrite !MState.unsigned_lit in MU by lia. rewrite !MState.unsigned_lit in RW by lia.
  replace (ret_pc (Z_to_bv 64 0x81b10)) with (Z_to_bv 64 0x81b10)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { apply (munch_trans _ m _ m' MUc).
    apply (munch_weaken [(Q, Q + 187)]); [|exact MU].
    unfold sub_fp. cbn [outside]. intros x (Hx & _). split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs m _ m' WMc WM)|].
  split; [exact MI'|].
  intros P HP. exact (p1_shadow_rw_call_on _ m' Q 187 _ MU WM RW ltac:(lia) P (KPc P HP)).
Qed.

(* The run from 0x81ac8 to the return at 0x81b10: 14 frame-shadow stores, li a1,187, the spill load a0 = Q and the
   call of __asan_set_shadow_f8(Q, 187) by its contract.  The only writes are inside [Sh, Sh + 328). *)
Lemma p1_evt : asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Sh Q : Z),
    s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sh ->
    0 <= A < 2 ^ 64 -> Sh <= Q -> Q + 187 <= Sh + 328 ->
    (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 Q)) ->
    disjoint_from [(Sh, Sh + 328)] (A + 152) 8 ->
    disjoint_from [(Sh, Sh + 328)] RT_LO (RT_HI - RT_LO) ->
    asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b10) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(Sh, Sh + 328)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ shadow_rw m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Sh Q E1 E3 HA HQ1 HQ2 HSH HSP HSEP HDRT HAC HSW HMI.
  eapply evt_mono; [exact (p1_evt_on SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
    s10 s11 t3 t4 t5 t6 F fc m A Sh Q E1 E3 HA HQ1 HQ2 HSH HSP HSEP HDRT HAC
    (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW) HMI)|].
  intros s (R & m' & H). exists R, m'. p1_post_old H HSW.
Qed.

(* ---- The segment lemmas seg_P1_70 and seg_P1. ---- *)
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

Section Pre.
Context {fx : FPState}.

(* mkR_of made concrete, so that the run lemma's register file is p1_evt's mkR (Seg/P2.v p2_mkR_of). *)
Lemma p1_mkR_of : forall regs, Regs6ss.mkR_of regs = Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
  (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
  (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
  (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Two word_mem values at the same address agree mod 2^64 (Seg/P2.v p2_wm_congr). *)
Lemma p1_wm_congr : forall (m : word -> option byte) a v1 v2,
  word_mem rsegs m a v1 -> word_mem rsegs m a v2 -> v1 mod 2^64 = v2 mod 2^64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (Hb : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (E2' : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    apply (f_equal (@bv_unsigned 8)) in E2'. rewrite !kb_byte_unsigned in E2'. exact E2'. }
  apply Z.bits_inj'. intros j Hj.
  destruct (Z.ltb_spec j 64) as [Hlt|Hge].
  - set (k := Z.to_nat (j / 8)).
    assert (Hk8 : (k < 8)%nat) by (unfold k; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      apply Z.div_lt_upper_bound; lia).
    pose proof (Hb k Hk8) as Hbk.
    assert (Hoff : 8 * Z.of_nat k + (j - 8 * Z.of_nat k) = j) by lia.
    assert (Hjk : j - 8 * Z.of_nat k = j mod 8) by (unfold k; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      rewrite (Z.div_mod j 8) at 1 by lia; lia).
    assert (Hoff8 : 0 <= j - 8 * Z.of_nat k < 8) by (rewrite Hjk; apply Z.mod_pos_bound; lia).
    assert (HT : Z.testbit (le_byte v1 8 k) (j - 8 * Z.of_nat k)
               = Z.testbit (le_byte v2 8 k) (j - 8 * Z.of_nat k)) by (rewrite Hbk; reflexivity).
    rewrite !le_byte_testbit in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ 8)) in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) in HT by lia.
    rewrite Hoff in HT.
    rewrite !Z.testbit_mod_pow2 by lia.
    rewrite (proj2 (Z.ltb_lt j 64)) by lia. exact HT.
  - rewrite !Z.testbit_mod_pow2 by lia. rewrite (proj2 (Z.ltb_ge j 64)) by lia. reflexivity.
Qed.

(* Every side-stack metadata cell lies in [FS, FS + 36864) (Seg/P2.v p2_fs_meta_range). *)
Lemma p1_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* The frame-shadow byte x is the shadow byte of the frame byte fr + 8 (x - S(fr)). *)
Lemma p1_sfr_shadow : forall fr x, x = shadow_addr (fr + 8 * (x - Sfr fr)).
Proof.
  intros fr x. unfold Sfr, shadow_addr.
  replace (fr + 8 * (x - (fr / 8 + ASAN_K))) with (fr + (x - (fr / 8 + ASAN_K)) * 8) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

Lemma p1_ro_agree : forall m, mem_inv rsegs m -> ro_agree rsegs m.
Proof.
  intros m H a E. unfold mrd. destruct (m a) as [b|] eqn:Em; [|reflexivity].
  rewrite (H a b Em) in E. discriminate E.
Qed.

(* The registered globals of frame_AG lie in [0x21140, 0x9f8e8) (a Theorem Labs lane's F37.v f37_ag_range): v1.9.0's
   round_trip.box .. CTRL_FRAMES + 264 (lib/A/FrameAPI.v, equal to the v1.9 ELF's asan_globals). *)
Lemma p1_ag_range : forall a, in_globals AF.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hall : forallb (fun p => (0x21140 <=? fst p) && (fst p + snd p <=? 0x9f8e8)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall (lo, len) Hin). cbn [fst snd] in Hall.
  apply andb_true_iff in Hall as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* MemNorm.normalize drops only read-only image bytes; no shadow byte and no runtime cell is one, so the shadow's
   read/write view and the runtime cells are the same on both sides of mem_rel. *)
Lemma p1_shadow_rw_norm : forall m m0, MemNorm.mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 REL HSW a Ha. pose proof (sl_shadow_not_ro a Ha) as Hro.
  destruct (HSW a Ha) as (Hw & b & Hb). split.
  - rewrite (MemNorm.wview_rel_rw rsegs m m0 (wa a) REL Hro). exact Hw.
  - exists b. rewrite <- (MemNorm.mrd_rel rsegs m m0 (wa a) REL). exact Hb.
Qed.

Lemma p1_shadow_rw_back : forall m m0, MemNorm.mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 REL HSW a Ha. pose proof (sl_shadow_not_ro a Ha) as Hro.
  destruct (HSW a Ha) as (Hw & b & Hb). split.
  - rewrite <- (MemNorm.wview_rel_rw rsegs m m0 (wa a) REL Hro). exact Hw.
  - exists b. rewrite (MemNorm.mrd_rel rsegs m m0 (wa a) REL). exact Hb.
Qed.

Lemma p1_cells_norm : forall m m0, MemNorm.mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 REL HAC. unfold asan_cells in HAC |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    apply (proj1 (MemNorm.bytes_at_rel rsegs m m0 _ _ REL)); assumption.
Qed.

(* The shadow bytes p1_evt_ro needs: p1_evt's, on the normalized memory (normalize keeps every shadow byte). *)
Definition p1_evt_ro_shadow_R (Sh Q : Z) : Z -> Prop := fun a => p1_evt_shadow_R Sh Q a.

(* p1_evt from ro_agree instead of mem_inv (push 5d: no cut carries mem_inv): the run is taken on the normalized
   memory, where mem_inv holds (MemNorm.mem_inv_normalize), and carried back by MemNorm.evt_normalize, as
   Seg/A1.v's a1_req_evt does. Its post is about the real memory: munch / wmono by munch_rel / wmono_rel,
   ro_agree by ro_agree_same, each region present and writable across mem_rel both ways (A.ShadowRwOnT). *)
Lemma p1_evt_ro_on : asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Sh Q : Z),
    s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sh ->
    0 <= A < 2 ^ 64 -> Sh <= Q -> Q + 187 <= Sh + 328 ->
    (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 Q)) ->
    disjoint_from [(Sh, Sh + 328)] (A + 152) 8 ->
    disjoint_from [(Sh, Sh + 328)] RT_LO (RT_HI - RT_LO) ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (p1_evt_ro_shadow_R Sh Q) m -> MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b10) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(Sh, Sh + 328)] m m' /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\
         (forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Sh Q E1 E3 HA HQ1 HQ2 HSH HSP HSEP HDRT HAC HSW HRO.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  eapply evt_mono.
  - eapply MemNorm.evt_normalize; [vm_compute; reflexivity | exact HRO |].
    apply (p1_evt_on SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
             t5 t6 F fc (MemNorm.normalize rsegs m) A Sh Q E1 E3 HA HQ1 HQ2 HSH).
    + exact (proj1 (MemNorm.bytes_at_rel rsegs m _ _ _ REL) HSP).
    + exact HSEP.
    + exact HDRT.
    + exact (p1_cells_norm m _ REL HAC).
    + exact (A.ShadowRwOnT.shadow_rw_on_rel _ m _ REL HSW).
    + exact (MemNorm.mem_inv_normalize rsegs m).
  - intros s (s0' & (R & m0' & -> & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P27 & P22 & P25 & MU0 & WM0 & _ & SW0) &
      MR & RS).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    exists R, ms. split; [reflexivity|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P27|].
    split; [exact P22|]. split; [exact P25|].
    split; [exact (MemNorm.munch_rel rsegs _ m _ ms m0' REL Hmem RS MU0)|].
    split; [exact (MemNorm.wmono_rel rsegs m _ ms m0' REL Hmem RS WM0)|].
    split; [exact (MemNorm.ro_agree_same rsegs m ms HRO RS)|].
    intros P HP.
    exact (A.ShadowRwOnT.shadow_rw_on_of_rel P ms m0' Hmem (SW0 P (A.ShadowRwOnT.shadow_rw_on_rel P m _ REL HP))).
Qed.

(* p1_evt from ro_agree instead of mem_inv (push 5d: no cut carries mem_inv): the run is taken on the normalized
   memory, where mem_inv holds (MemNorm.mem_inv_normalize), and carried back by MemNorm.evt_normalize, as
   Seg/A1.v's a1_req_evt does. Its post is about the real memory: munch / wmono by munch_rel / wmono_rel,
   ro_agree by ro_agree_same, shadow_rw back across mem_rel. *)
Lemma p1_evt_ro : asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Sh Q : Z),
    s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sh ->
    0 <= A < 2 ^ 64 -> Sh <= Q -> Q + 187 <= Sh + 328 ->
    (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 Q)) ->
    disjoint_from [(Sh, Sh + 328)] (A + 152) 8 ->
    disjoint_from [(Sh, Sh + 328)] RT_LO (RT_HI - RT_LO) ->
    asan_cells m -> shadow_rw m -> MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b10) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(Sh, Sh + 328)] m m' /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\ shadow_rw m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Sh Q E1 E3 HA HQ1 HQ2 HSH HSP HSEP HDRT HAC HSW HRO.
  eapply evt_mono; [exact (p1_evt_ro_on SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
    s9 s10 s11 t3 t4 t5 t6 F fc m A Sh Q E1 E3 HA HQ1 HQ2 HSH HSP HSEP HDRT HAC
    (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW) HRO)|].
  intros s (R & m' & H). exists R, m'. p1_post_old H HSW.
Qed.

End Pre.

(* ---- PRO across a run of the P chain (aslot push 13 group B, a Theorem Labs lane's cut-gap5-81c84.md section 2 (a working note, not in this delivery)). ----
   P1 .. P11 hand on SlotInv's bundle PRO unchanged: the eight A4 prologue spills [A + 40] .. [A + 248] (v1.9: the
   seventh is [A + 208] = fr + 448, v1.8's [A + 200]), the later spills [A + 184] / [A + 256] .. [A + 272], v1.9's
   16th conjunct [A + 32] = fr + 2880 (A4's 0x813cc, first.sroa.7's pointer), our[]'s 6
   bytes addressable (shadow byte S(fr) + 328) and the input pair. pro_fra moves PRO across a run whose write set W
   is a list of intervals of three kinds (pro_iv): a callee stack window at or above stklo and below the spill base
   A, a range of the frame body [fr, fr + FRAME_BYTES), or a range of the frame shadow [S(fr), S(fr) + FRAME_SHADOW)
   apart from S(fr) + 328. The spills lie in [A + 32, A + 280): app memory above every window and above the frame
   (fr + FRAME_BYTES <= A). For 0 < n the input block is a live block of the entry heap: app memory below stklo and
   outside the frame (a_laws_blocks), so its shadow bytes lie outside the frame shadow. P2 .. P11 import this file
   for it. *)
Definition pro_iv (fr A lo : Z) (iv : Z * Z) : Prop :=
  (lo <= fst iv /\ snd iv <= A) \/
  (fr <= fst iv /\ snd iv <= fr + FRAME_BYTES) \/
  (Sfr fr <= fst iv /\ snd iv <= Sfr fr + FRAME_SHADOW /\ (snd iv <= Sfr fr + 328 \/ Sfr fr + 329 <= fst iv)).

Lemma pro_out : forall (P : Z * Z -> Prop) W x, Forall P W ->
  (forall lo hi, P (lo, hi) -> ~ (lo <= x < hi)) -> LibFr.outside W x.
Proof.
  intros P W x HF Hx. induction HF as [|[lo hi] W' Hiv HF IH]; cbn [LibFr.outside]; [exact I|].
  split; [exact (Hx lo hi Hiv) | exact IH].
Qed.

(* A spill at the base A carried across a munch W that keeps register 9 and misses its eight bytes. *)
Lemma pro_spill1 : forall (regs regs' : bvmap 5 word) m m' W off v A,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off ->
  getr regs' 9 = getr regs 9 -> LibFr.munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> LibFr.outside W x) -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v A (A' & HA' & Hq) HA Hlo Hhi Hoff E9 MU HW.
  unfold q64 in Hq. pose proof Hq as Hqb. apply bytes_at_bound in Hqb. rewrite length_le8 in Hqb.
  assert (HA'A : A' = A).
  { unfold rg in HA', HA. rewrite HA in HA'. apply (f_equal (@bv_unsigned 64)) in HA'.
    rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap, bv_modulus in HA'.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in HA'. rewrite (Z.mod_small A (2 ^ 64)) in HA' by lia.
    revert Hqb HA'. clear - Hlo Hhi Hoff. Z.div_mod_to_equations. lia. }
  subst A'. exists A. split; [unfold rg in *; rewrite E9; exact HA|].
  unfold q64. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. exact (HW x ltac:(lia)).
Qed.

(* addressable survives a run that leaves the shadow byte of each of its bytes alone. *)
Lemma pro_addr : forall W m m' p n, addressable m p n -> LibFr.munch W m m' ->
  (forall i, 0 <= i < n -> LibFr.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU Ho.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hb & Hok).
  pose proof (in_shadow_range (shadow_addr (p + i)) (shadow_of_app (p + i) Happ)) as Hr.
  split; [exact Happ|]. exists b. split; [|exact Hok].
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. exact (Ho i Hi).
Qed.

(* PRO across a munch W that keeps register 9 and misses the spill area [A + 32, A + 280), our[]'s shadow byte
   S(fr) + 328 and (for 0 < n, the block being live) the input block and its shadow bytes. *)
Lemma pro_run : forall g fr (regs regs' : bvmap 5 word) m m' W A,
  PRO g fr regs m -> rg regs 9 A -> 0 <= A -> A + 280 <= 2 ^ 64 -> fr mod 8 = 0 ->
  getr regs' 9 = getr regs 9 -> LibFr.munch W m m' ->
  (forall x, A + 32 <= x < A + 280 -> LibFr.outside W x) ->
  LibFr.outside W (Sfr fr + 328) ->
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) -> forall i, 0 <= i < g_n g ->
     LibFr.outside W (g_p g + i) /\ LibFr.outside W (shadow_addr (g_p g + i))) ->
  PRO g fr regs' m'.
Proof.
  intros g fr regs regs' m m' W A HP HA9 HA0 HA1 Hfr8 E9 MU HWA HW328 HWB.
  destruct HP as (H40 & H120 & H136 & H160 & H168 & H176 & H208 & H248 & HAD & HIN & HING &
    H184 & H256 & H264 & H272 & H32).
  assert (Hsp : forall off v, 32 <= off <= 272 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Hoff Hs. apply (pro_spill1 regs regs' m m' W off v A Hs HA9 HA0 ltac:(lia) ltac:(lia) E9 MU).
    intros x Hx. apply HWA. lia. }
  split; [exact (Hsp 40 _ ltac:(lia) H40)|].
  split; [exact (Hsp 120 _ ltac:(lia) H120)|].
  split; [exact (Hsp 136 _ ltac:(lia) H136)|].
  split; [exact (Hsp 160 _ ltac:(lia) H160)|].
  split; [exact (Hsp 168 _ ltac:(lia) H168)|].
  split; [exact (Hsp 176 _ ltac:(lia) H176)|].
  split; [exact (Hsp 208 _ ltac:(lia) H208)|].
  split; [exact (Hsp 248 _ ltac:(lia) H248)|].
  split.
  { apply (pro_addr W m m' (fr + 2624) 6 HAD MU). intros i Hi.
    replace (shadow_addr (fr + 2624 + i)) with (Sfr fr + 328); [exact HW328|].
    unfold Sfr, shadow_addr. clear - Hfr8 Hi. Z.div_mod_to_equations. lia. }
  split.
  { eapply fl_bytes; [exact HIN | exact MU |].
    intros x Hx. rewrite <- g_n_len in Hx.
    assert (Hn : 0 < g_n g) by lia.
    destruct (HING Hn) as (Hin & _).
    pose proof (proj1 (HWB Hn Hin (x - g_p g) ltac:(lia))) as Ho.
    replace (g_p g + (x - g_p g)) with x in Ho by lia. exact Ho. }
  split.
  { intros Hn. destruct (HING Hn) as (Hin & Had). split; [exact Hin|].
    apply (pro_addr W m m' (g_p g) (g_n g) Had MU). intros i Hi. exact (proj2 (HWB Hn Hin i Hi)). }
  split; [exact (Hsp 184 _ ltac:(lia) H184)|].
  split; [exact (Hsp 256 _ ltac:(lia) H256)|].
  split; [exact (Hsp 264 _ ltac:(lia) H264)|].
  split; [exact (Hsp 272 _ ltac:(lia) H272) | exact (Hsp 32 _ ltac:(lia) H32)].
Qed.

(* PRO under a register change that keeps s1 (no memory change). *)
Lemma pro_regs : forall g fr (regs regs' : bvmap 5 word) m,
  PRO g fr regs m -> getr regs' 9 = getr regs 9 -> PRO g fr regs' m.
Proof.
  intros g fr regs regs' m HP E9.
  assert (Hs : forall off v, spill regs m off v -> spill regs' m off v).
  { intros off v (A & HA & Hq). exists A. split; [unfold rg in *; rewrite E9; exact HA | exact Hq]. }
  destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16).
  split; [exact (Hs _ _ H1)|]. split; [exact (Hs _ _ H2)|]. split; [exact (Hs _ _ H3)|].
  split; [exact (Hs _ _ H4)|]. split; [exact (Hs _ _ H5)|]. split; [exact (Hs _ _ H6)|].
  split; [exact (Hs _ _ H7)|]. split; [exact (Hs _ _ H8)|].
  split; [exact H9|]. split; [exact H10|]. split; [exact H11|].
  split; [exact (Hs _ _ H12)|]. split; [exact (Hs _ _ H13)|].
  split; [exact (Hs _ _ H14)|].
  split; [exact (Hs _ _ H15) | exact (Hs _ _ H16)].
Qed.

(* The frame-shadow bytes are shadow bytes (their granules are frame bytes, app memory). *)
Lemma pro_sh_in : forall fr a, (forall x, fr <= x < fr + FRAME_BYTES -> app_mem x) ->
  Sfr fr <= a < Sfr fr + FRAME_SHADOW -> in_shadow a.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr a Happ Ha. rewrite (p1_sfr_shadow fr a). apply shadow_of_app. apply Happ. lia.
Qed.

(* A byte whose shadow byte is a frame-shadow byte is a frame byte (fr is 8-aligned). *)
Lemma pro_sh_back : forall fr y, fr mod 8 = 0 -> 0 <= y ->
  Sfr fr <= shadow_addr y < Sfr fr + FRAME_SHADOW -> fr <= y < fr + FRAME_BYTES.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr y Hm Hy H. unfold Sfr, shadow_addr, ASAN_K in H.
  revert H Hm Hy. Z.div_mod_to_equations. lia.
Qed.

Section PRO.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Variable ra : Z.
Context {SH : sink_head} {SK : sink_syms}.

(* The allocator laws' results, taken apart once (a Theorem Labs lane 15:32Z: the generated laws grow by appending at every
   nesting level, and a later generation names every inner part). P1 .. P9 use these five lemmas instead of
   destructing the results of AC.a_laws_store / a_laws_fs_store / a_laws_fs_place / a_laws_blocks / a_laws_fs_state
   at each site, so a new generation changes one destruct here. *)
Lemma p1_laws_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hmc Hwrit.
  destruct (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH Hmc Hwrit)
    as (HAH' & Hown' & Hstk' & Hhi').
  exact (conj HAH' (conj Hown' (conj Hstk' Hhi'))).
Qed.

Lemma p1_laws_fs_store : forall H mem mem' md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.a_fs_ok mem' FS ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md FS HAH Hw Hr Hmc Hwrit Hok.
  destruct (AC.a_laws_fs_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md FS HAH Hw Hr
              Hmc Hwrit Hok)
    as (HAH' & Hown' & Hstk' & Hhi').
  exact (conj HAH' (conj Hown' (conj Hstk' Hhi'))).
Qed.

Lemma p1_laws_fs_place : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ FS mod 4096 = 0 /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md FS HAH Hw Hr.
  destruct (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw Hr)
    as (HGT & Hend & Hmod & Happ).
  exact (conj HGT (conj Hend (conj Hmod Happ))).
Qed.

Lemma p1_laws_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  destruct (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md p n HAH Hin)
    as (_ & _ & Hpn & _ & Hbody).
  split; [exact Hpn|].
  intros a Ha. destruct (Hbody a Ha) as (Hap & _ & _ & _ & Hnfs). split; [exact Hap | exact Hnfs].
Qed.

Lemma p1_fs_ok_of_state : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 -> AC.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw Hr.
  exact (proj1 (AC.a_laws_fs_state _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw Hr)).
Qed.

Lemma pro_fra : forall g fr hb (regs regs' : bvmap 5 word) mem mem' md W A,
  FRA B APIf ra g fr hb regs mem md -> PRO g fr regs mem -> rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  LibFr.munch W mem mem' -> getr regs' 9 = getr regs 9 ->
  Forall (pro_iv fr A (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)) W ->
  PRO g fr regs' mem'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W A HFRA HPRO HA9 HAr MU E9 HF.
  destruct (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof HFRA as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  unfold APPMEM_END in HAPP. unfold HIGHMEM_BEG in Hhigh.
  assert (HA0 : A0 = A).
  { pose proof HA9 as HA9u. unfold rg in Hr9, HA9u.
    pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HA9u)) as E0.
    rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
    rewrite !Z.mod_small in E0 by lia. exact E0. }
  subst A0.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  (* the input block: app memory below stklo, outside the frame (real arm: frame at or above stklo; side arm: the
     frame is in the FakeStack, the block is not) *)
  assert (Hblk : 0 < g_n g -> In (g_p g, g_n g) (g_H g) -> forall i, 0 <= i < g_n g ->
            app_mem (g_p g + i) /\ g_p g + i < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
            ~ (fr <= g_p g + i < fr + FRAME_BYTES)).
  { intros Hn Hin i Hi.
    destruct (p1_laws_blocks (hb ++ g_H g) mem md (g_p g) (g_n g) HAH
                (in_or_app hb (g_H g) _ (or_intror Hin))) as (Hpn & Hbody).
    destruct (Hbody (g_p g + i) ltac:(lia)) as (Hap & Hnfs).
    split; [exact Hap|]. split; [lia|]. intros Hfr.
    destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5f [Hfsb [Hfs Hrec]]]].
    - destruct (Hreal (g_p g + i) Hfr) as (Hge & _). lia.
    - apply Hnfs. exact (Hfs (g_p g + i) Hfr). }
  pose proof (pro_sh_in fr (Sfr fr + 328) Happ ltac:(lia)) as Hs328.
  apply (pro_run g fr regs regs' mem mem' W A HPRO HA9 ltac:(lia) ltac:(lia) Hfr8 E9 MU).
  - intros x Hx. apply (pro_out _ W x HF). intros l h Hiv Hin.
    unfold pro_iv in Hiv; cbn [fst snd] in Hiv. destruct Hiv as [Hw|[Hf|Hs]]; [lia | lia |].
    apply (app_not_shadow x); [unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; lia|].
    apply (pro_sh_in fr x Happ). lia.
  - apply (pro_out _ W _ HF). intros l h Hiv Hin.
    unfold pro_iv in Hiv; cbn [fst snd] in Hiv. destruct Hiv as [Hw|[Hf|Hs]].
    + unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hs328. lia.
    + exact (app_not_shadow _ (Happ (Sfr fr + 328) ltac:(lia)) Hs328).
    + lia.
  - intros Hn Hin i Hi. destruct (Hblk Hn Hin i Hi) as (Hap & Hlt & Hnf).
    assert (Hx0 : 0 <= g_p g + i)
      by (pose proof Hap as Hap'; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap'; lia).
    pose proof (shadow_of_app _ Hap) as Hsh'.
    split.
    + apply (pro_out _ W _ HF). intros l h Hiv Hin'.
      unfold pro_iv in Hiv; cbn [fst snd] in Hiv. destruct Hiv as [Hw|[Hf|Hs]].
      * lia.
      * apply Hnf. lia.
      * exact (app_not_shadow _ Hap (pro_sh_in fr (g_p g + i) Happ ltac:(lia))).
    + apply (pro_out _ W _ HF). intros l h Hiv Hin'.
      unfold pro_iv in Hiv; cbn [fst snd] in Hiv. destruct Hiv as [Hw|[Hf|Hs]].
      * unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh'. lia.
      * exact (app_not_shadow _ (Happ (shadow_addr (g_p g + i)) ltac:(lia)) Hsh').
      * apply Hnf. apply (pro_sh_back fr (g_p g + i) Hfr8 Hx0). lia.
Qed.

End PRO.

Section P1.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* P1's two entry cuts are SlotInv's: Inv_A81ac0 and Inv_A81ac8 (its body at pc 0x81ac8), the cuts the previous
   segment (seg_R21) exits at. Since aslot push 14A they bound the set_shadow range Q (the spill [A + 152]) by
   `Q + 187 <= Sfr fr + 328`, so the call misses our[]'s shadow byte S(fr) + 328 (PRO). No cut carries mem_inv
   (push 5d); the callee's mem_inv premise is met by p1_evt_ro on the normalized memory. *)
Definition P1_entry (g : ghost) (c : config) : Prop := SlotInv.Inv_A81ac0 B APIf ra g c.

Lemma seg_P1_70 : asan_set_shadow_f8_contract ->
  Hcut B APIf ra (Inv_A81b10 B APIf ra) -> Hcut B APIf ra (Inv_A81ac8 B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros SET Hbc g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hn & Hour & HCUR & HPRO & HS144 & Ha0 &
    (Q & (A' & HA'9 & HQsp) & HQ1 & HQ2) &
    (Ac & idb & junk & HAc9 & H27 & HAcr & HC208 & HCidb & HCjunk & Hq280 & Hq240 & (jy & junk2 & HCjy & HCj2))).
  subst c.
  rewrite SEGS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  unfold rg in Hr19, Hr8, Hr9, Hr26, HA'9.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  (* frame-base bounds from the header word's bytes_at *)
  assert (Hfrb : 0 <= fr /\ fr + 8 <= 2^64).
  { unfold q64 in Hhdr1. apply bytes_at_bound in Hhdr1. rewrite length_le8 in Hhdr1. lia. }
  assert (HSfr : Sfr fr = fr / 8 + ASAN_K) by reflexivity.
  assert (HSfrlo : ASAN_K <= Sfr fr) by (rewrite HSfr; pose proof (Z.div_pos fr 8 (proj1 Hfrb) ltac:(lia)); unfold ASAN_K; lia).
  (* the real-stack low bound is in high memory *)
  assert (Hstkhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (apply (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH)).
  assert (HAlo : HIGHMEM_BEG <= A).
  { assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity. lia. }
  assert (HAhi : A + 312 <= 2^64).
  { unfold q64 in Hspill. apply bytes_at_bound in Hspill. rewrite length_le8 in Hspill. lia. }
  (* the cut's s1 = Ac is FRA's spill base A *)
  assert (HAcA : Ac = A).
  { pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HAc9)) as E0.
    rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
    rewrite (Z.mod_small A (2 ^ 64)) in E0 by (unfold HIGHMEM_BEG in HAlo; lia).
    rewrite (Z.mod_small Ac (2 ^ 64)) in E0 by lia. lia. }
  subst Ac.
  (* the frame is application memory above the image's writable data, in both arms (fra_app) *)
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ).
  (* the 392 frame shadow bytes are shadow bytes, between LOWMEM_END and HIGHMEM_BEG *)
  assert (HshIS : forall i, 0 <= i < 392 -> in_shadow (Sfr fr + i)).
  { intros i Hi. pose proof (p1_sfr_shadow fr (Sfr fr + i)) as E.
    replace (Sfr fr + i - Sfr fr) with i in E by lia.
    rewrite E. apply shadow_of_app. apply Happ. lia. }
  pose proof (HshIS 0 ltac:(lia)) as Hin0. rewrite Z.add_0_r in Hin0.
  pose proof (HshIS 391 ltac:(lia)) as Hin391.
  assert (HWlo : LOWMEM_END <= Sfr fr)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin0 |- *; lia).
  assert (HWhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin391 |- *; lia).
  (* the spill base of the cut is s1 = A *)
  assert (HAA : A' = A).
  { pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HA'9)) as E0.
    rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
    rewrite (Z.mod_small A (2 ^ 64)) in E0 by (unfold HIGHMEM_BEG in HAlo; lia).
    pose proof HQsp as HQb. unfold q64 in HQb. apply bytes_at_bound in HQb. rewrite length_le8 in HQb.
    unfold HIGHMEM_BEG in HAlo. revert E0 HQb. Z.div_mod_to_equations. lia. }
  subst A'.
  (* the premises of p1_evt *)
  assert (HAr : 0 <= A < 2 ^ 64) by (unfold HIGHMEM_BEG in HAlo; lia).
  assert (HdA : disjoint_from [(Sfr fr, Sfr fr + 328)] (A + 152) 8)
    by (cbn [disjoint_from]; split; [right; lia | exact I]).
  assert (HdRT : disjoint_from [(Sfr fr, Sfr fr + 328)] RT_LO (RT_HI - RT_LO))
    by (unfold RT_LO, RT_HI; unfold LOWMEM_END in HWlo; cbn [disjoint_from]; split; [left; lia | exact I]).
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW.
  unfold a0v, rg in Ha0.
  (* run the segment *)
  apply (sl_run_lib regs (Z_to_bv 64 0x81ac8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81b10 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 26 = getr regs 26 /\
       getr R 27 = getr regs 27 /\ getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
       Frame.munch [(Sfr fr, Sfr fr + 328)] mem mem' /\ Frame.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       shadow_rw mem')
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite p1_mkR_of.
    eapply evt_mono.
    + apply (p1_evt_ro SET) with (A := A) (Sh := Sfr fr) (Q := Q).
      all: try assumption.
    + intros ms' (R & m' & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P27 & P22 & P25 & MUq & WMq & MIq & SWq).
      exists R, (Z_to_bv 64 0x81b10), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P27|].
      split; [exact P22|]. split; [exact P25|].
      split; [exact MUq|]. split; [exact WMq|].
      split; [exact MIq | exact SWq].
  - (* the continuation: build the exit cut Inv_A81b10 *)
    intros R pc' mem' regs'' md' HK Hreg Hmat.
    destruct HK as (Hpc & HR2 & HR3 & HR4 & HR8 & HR9k & HR19k & HR26 & HR27 & HR22 & HR25 & MU328 & WM & HRO' &
      SW').
    (* the run writes only [S(fr), S(fr) + 328): below our[]'s shadow byte S(fr) + 328 (PRO), inside the frame's
       392 shadow bytes (FRA, ENT and the cells) *)
    assert (MU : Frame.munch [(Sfr fr, Sfr fr + FRAME_SHADOW)] mem mem').
    { intros x Hx. apply MU328. cbn [LibFr.outside ULFr.outside] in *. destruct Hx as (Hx & _).
      split; [lia | exact I]. }
    assert (MUL328 : LibFr.munch [(Sfr fr, Sfr fr + 328)] mem mem').
    { first [exact MU328 | exact (proj2 (fr_munch_ul _ mem mem') MU328)
                        | exact (proj1 (fr_munch_ul _ mem mem') MU328)]. }
    subst pc'. rewrite <- SEGS. apply Hbc.
    exists regs'', mem', md', fr.
    split; [reflexivity|].
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact HR3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact HR4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact HR8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact HR9k).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact HR19k).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact HR26).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact HR27).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact HR22).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact HR25).
    (* AH, the runtime's ownership and the stack bounds kept across the frame-shadow writes, by arm *)
    assert (AHSTK : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md /\
                    (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a <->
                               AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a) /\
                    AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                      = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                    AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                      = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { assert (Hwrit : forall x, 0 <= x < 2^64 -> writable_at rsegs mem x -> writable_at rsegs mem' x).
      { intros x Hx Hwx. exact (WM (Z_to_bv 64 x) Hwx). }
      destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs Hrec]]]].
      - (* real arm: a_laws_store *)
        assert (Hmc : forall x, 0 <= x < 2^64 ->
                  ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok.
          destruct (Z.lt_ge_cases x (Sfr fr)) as [Hlt|Hge];
            [|destruct (Z.lt_ge_cases x (Sfr fr + FRAME_SHADOW)) as [Hlt2|Hge2]].
          - apply MU. rewrite MState.unsigned_lit by exact Hx. cbn [outside]. split; [lia | exact I].
          - exfalso. apply Hnok. right. right. right. exists (fr + 8 * (x - Sfr fr)).
            split; [exact (p1_sfr_shadow fr x)|]. right. left.
            specialize (Hreal (fr + 8 * (x - Sfr fr)) ltac:(lia)).
            unfold APPMEM_END in *. lia.
          - apply MU. rewrite MState.unsigned_lit by exact Hx. cbn [outside]. split; [lia | exact I]. }
        exact (p1_laws_store APIf ([] ++ g_H g) mem mem' md HAH Hmc Hwrit).
      - (* side arm: a_laws_fs_store *)
        pose proof (AsanRTInv.RT_fs_cells _ _ _ HRT) as HFSC.
        destruct HFSC as (_ & _ & _ & _ & (FSw & HFSb & Hfsok) & _).
        apply bytes_at_le8_word in HFSb.
        pose proof (u64_range FSw) as HFSr.
        destruct Hfsok as (HF0 & _ & HFGT & HFapp).
        assert (Happtop : app_mem (bv_unsigned FSw + RT_FS_SIZE - 1)) by (apply HFapp; unfold RT_FS_SIZE; lia).
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, RT_FS_SIZE in Happtop.
        unfold AsanRT.RT_GT in HFGT.
        (* the frame lies in the side stack region [FS, FS + FS_SIZE) of base FS = bv_unsigned FSw *)
        assert (HinFS : forall a0, fr <= a0 < fr + FRAME_BYTES ->
                  bv_unsigned FSw <= a0 < bv_unsigned FSw + AC.FS_SIZE).
        { intros a0 Ha0'. pose proof (Happ a0 Ha0') as Hap0.
          unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap0.
          specialize (Hfs a0 Ha0'). unfold AC.a_in_fs in Hfs. destruct Hfs as (b & Hbr & Hwm & Hb1 & Hb2).
          change (AC.as_tp AC.ASYMS) with AsanRT.RT_TP in Hwm.
          pose proof (p1_wm_congr mem AsanRT.RT_TP b (bv_unsigned FSw) Hwm HFSb) as Hcong.
          unfold AC.FS_SIZE in Hb2 |- *.
          assert (Hbeq : b = bv_unsigned FSw)
            by (revert Hcong Hb1 Hb2 Happtop HFGT HFSr Ha0' Hap0 Hfrb; Z.div_mod_to_equations; lia).
          subst b. lia. }
        pose proof (p1_fs_ok_of_state APIf ([] ++ g_H g) mem md (bv_unsigned FSw) HAH HFSb ltac:(lia)) as Hfsok0.
        (* every present byte stays present: outside the frame shadow by munch, inside it by shadow_rw mem' *)
        assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                  exists b, mbyte rsegs mem' q = Some b).
        { intros q Hq (b & Hb).
          destruct (Z.lt_ge_cases q (Sfr fr)) as [Hlt|Hge];
            [|destruct (Z.lt_ge_cases q (Sfr fr + FRAME_SHADOW)) as [Hlt2|Hge2]].
          - exists b. unfold mbyte in Hb |- *. rewrite MU; [exact Hb|].
            rewrite MState.unsigned_lit by exact Hq. cbn [outside]. split; [lia | exact I].
          - pose proof (HshIS (q - Sfr fr) ltac:(lia)) as Hq'. replace (Sfr fr + (q - Sfr fr)) with q in Hq' by lia.
            destruct (proj2 (SW' q Hq')) as (b' & Hb'). exists b'. unfold mbyte. unfold mrd, wa in Hb'. exact Hb'.
          - exists b. unfold mbyte in Hb |- *. rewrite MU; [exact Hb|].
            rewrite MState.unsigned_lit by exact Hq. cbn [outside]. split; [lia | exact I]. }
        (* the side stack's metadata is application memory, so the shadow writes miss it *)
        assert (Hmeta : forall q, fs_meta (bv_unsigned FSw) q -> Frame.outside [(Sfr fr, Sfr fr + FRAME_SHADOW)] q).
        { intros q Hq. pose proof (p1_fs_meta_range _ _ Hq) as Hqr.
          assert (Hqa : app_mem q) by (apply HFapp; unfold RT_FS_SIZE; lia).
          cbn [Frame.outside]. split; [|exact I]. intros Hqt.
          pose proof (HshIS (q - Sfr fr) ltac:(lia)) as Hq'. replace (Sfr fr + (q - Sfr fr)) with q in Hq' by lia.
          exact (app_not_shadow _ Hqa Hq'). }
        assert (Hfsok' : AC.a_fs_ok mem' (bv_unsigned FSw)).
        { apply (a_fs_ok_pres [(Sfr fr, Sfr fr + FRAME_SHADOW)] mem _ (bv_unsigned FSw) Hfsok0 MU Hwrit Hpres Hmeta);
            unfold AC.FS_SIZE; lia. }
        assert (Hmc : forall x, 0 <= x < 2^64 ->
                  ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  ~ (bv_unsigned FSw <= x < bv_unsigned FSw + AC.FS_SIZE) ->
                  ~ (exists b, bv_unsigned FSw <= b < bv_unsigned FSw + AC.FS_SIZE /\ x = shadow_addr b) ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok Hnfs Hnsh.
          destruct (Z.lt_ge_cases x (Sfr fr)) as [Hlt|Hge];
            [|destruct (Z.lt_ge_cases x (Sfr fr + FRAME_SHADOW)) as [Hlt2|Hge2]].
          - apply MU. rewrite MState.unsigned_lit by exact Hx. cbn [outside]. split; [lia | exact I].
          - exfalso. apply Hnsh. exists (fr + 8 * (x - Sfr fr)).
            split; [apply HinFS; lia | exact (p1_sfr_shadow fr x)].
          - apply MU. rewrite MState.unsigned_lit by exact Hx. cbn [outside]. split; [lia | exact I]. }
        exact (p1_laws_fs_store APIf ([] ++ g_H g) mem mem' md (bv_unsigned FSw) HAH HFSb ltac:(lia) Hmc Hwrit
                 Hfsok'). }
    destruct AHSTK as (HAH' & Hown' & HSTK' & HSTKhi').
    split.
    + (* FRA B APIf ra g fr [] regs'' mem' md' *)
      apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md');
        [ | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Hmat ].
      (* s1 = A (mod 2^64) *)
      assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> A' mod 2 ^ 64 = A).
      { intros A' HA'.
        pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HA')) as E0.
        rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
        change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
        rewrite (Z.mod_small A (2 ^ 64)) in E0 by (unfold HIGHMEM_BEG in HAlo; lia).
        symmetry; exact E0. }
      apply (sl_fr_meta B APIf ra empty FF g fr [] regs regs'' mem mem' md [(Sfr fr, Sfr fr + FRAME_SHADOW)] HFRA MU
               WM);
        try assumption.
      * (* rt_disjoint W *)
        unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
          RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI,
          RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN. cbn [disjoint_from]. unfold ASAN_K in HSfrlo.
        repeat split; (lia || exact I).
      * (* the 392 shadow bytes after the run *)
        assert (Hi392 : forall i, 0 <= i < Z.of_nat (Z.to_nat FRAME_SHADOW) -> in_shadow (Sfr fr + i))
          by (intros i Hi; apply HshIS; lia).
        destruct (p1_sh_bytes mem' (Sfr fr) (Z.to_nat FRAME_SHADOW) SW' Hi392 ltac:(unfold LOWMEM_END in HWlo; lia)
                    ltac:(unfold HIGHMEM_BEG in HWhi; lia)) as (sh & Hshb & Hshl).
        exists sh. split; [exact Hshb | exact Hshl].
      * (* HWkept: outside W away from the frame body and shadow *)
        intros x Hx Hnb Hnsh. cbn [outside]. split; [exact Hnsh | exact I].
      * (* HWspill: the spill slot [A + 304, A + 312) is real stack, above the shadow *)
        intros A' HA' HA'r x Hx. cbn [outside]. split; [|exact I].
        pose proof (HA9 A' HA') as HAeq.
        unfold HIGHMEM_BEG in HAlo, HWhi. unfold LOWMEM_END in HWlo.
        revert Hx. Z.div_mod_to_equations. lia.
      * (* HWsaved: the saved registers [S - 104, S) are above A + 416 *)
        intros x Hx. cbn [outside]. split; [|exact I].
        unfold HIGHMEM_BEG in HAlo, HWhi. lia.
      * (* HWsel: the fr reload and selector spills [A + 16, A + 32) are real stack, above the shadow *)
        intros A' HA' HA'r x Hx. cbn [outside]. split; [|exact I].
        pose proof (HA9 A' HA') as HAeq.
        unfold HIGHMEM_BEG in HAlo, HWhi. unfold LOWMEM_END in HWlo.
        revert Hx. Z.div_mod_to_equations. lia.
      * (* HWwin: the entry-anchored slot window [S - SLOT_STACK, S) is at or above stklo, above the shadow *)
        intros x Hx. left. cbn [outside]. split; [|exact I].
        assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
        unfold HIGHMEM_BEG in Hstkhigh, HWhi. lia.
      * (* frame_AG stays addressable: its globals end below GT <= fr, so their shadow bytes are below S(fr) *)
        intros a Hin. apply (addr1_munch [(Sfr fr, Sfr fr + FRAME_SHADOW)] mem mem' a MU); [|exact (HAG a Hin)].
        cbn [outside]. split; [|exact I].
        pose proof (p1_ag_range a Hin) as Har. unfold AC.GT in HGT.
        unfold shadow_addr, Sfr in *. Z.div_mod_to_equations. lia.
    + split.
      { (* ENT: the run writes only the frame's 392 shadow bytes (ent_store), then the model step (ent_mat) *)
        assert (HENT1 : ENT APIf g [] mem' md).
        { eapply ent_store;
            [exact HENT | exact HFRA | exact MU | | exact HSTK' | exact HSTKhi'
            | exact (fun a _ Ho => proj2 (Hown' a) Ho)].
          intros x Hx. destruct (Z.lt_ge_cases x (Sfr fr)) as [Hlt|Hge];
            [|destruct (Z.lt_ge_cases x (Sfr fr + FRAME_SHADOW)) as [Hlt2|Hge2]].
          - left. cbn [outside]. split; [lia | exact I].
          - right. right. right. lia.
          - left. cbn [outside]. split; [lia | exact I]. }
        eapply ent_mat; [exact HENT1 | exact Hmat]. }
      split; [exact Hn|].
      split.
      { (* OURb g fr mem' : the OUR app bytes at fr + 2624 are outside the frame shadow *)
        unfold OURb in Hour |- *.
        apply (bytes_at_transport rsegs [(Sfr fr, Sfr fr + FRAME_SHADOW)] mem mem' (fr + 2624) (OUR (g_in g)) Hour
                 MU).
        assert (Hourlen : Z.of_nat (length (OUR (g_in g))) = 6).
        { unfold OUR. rewrite length_map, length_seq. reflexivity. }
        rewrite Hourlen. cbn [disjoint_from]. split; [|exact I].
        pose proof (Happ (fr + 2624) ltac:(lia)) as Happ1.
        pose proof (Happ (fr + 2629) ltac:(lia)) as Happ2.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happ1, Happ2.
        unfold LOWMEM_END in HWlo. unfold HIGHMEM_BEG in HWhi.
        lia. }
      (* CUR: the run keeps s6 / s9 (the callee keeps every s register) *)
      split.
      { destruct HCUR as (Hc & H22 & H25). split; [exact Hc|].
        unfold rg in *. rewrite E22, E25. split; [exact H22 | exact H25]. }
      (* push 13: PRO (the run writes only [S(fr), S(fr) + 328), frame shadow below our[]'s shadow byte) *)
      split.
      { apply (pro_fra B APIf ra g fr [] regs regs'' mem mem' md [(Sfr fr, Sfr fr + 328)] A HFRA HPRO Hr9 HAr
                 MUL328 E9).
        apply Forall_cons; [|apply Forall_nil]. unfold pro_iv; cbn [fst snd]. lia. }
      (* push 12: the spill [A + 144] = fr + 2688 (real stack, above HIGHMEM_BEG, so apart from the frame shadow) *)
      split.
      { destruct HS144 as (A1 & HrA1 & Hq144).
        assert (EA1 : A1 = A).
        { unfold q64 in Hq144. pose proof Hq144 as Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
          unfold rg in HrA1. rewrite HAc9 in HrA1. apply (f_equal (@bv_unsigned 64)) in HrA1.
          rewrite !Z_to_bv_unsigned in HrA1. unfold bv_wrap, bv_modulus in HrA1.
          change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in HrA1.
          rewrite (Z.mod_small A (2 ^ 64)) in HrA1 by (unfold HIGHMEM_BEG in HAlo; lia).
          revert HrA1. clear - Hb HAhi HAlo. unfold HIGHMEM_BEG in HAlo. Z.div_mod_to_equations. lia. }
        subst A1. exists A. split; [unfold rg; rewrite E9; exact HAc9|].
        unfold q64 in *.
        apply (bytes_at_transport rsegs [(Sfr fr, Sfr fr + FRAME_SHADOW)] mem mem' (A + 144) _ Hq144 MU).
        rewrite length_le8. cbn [disjoint_from]. split; [|exact I].
        unfold HIGHMEM_BEG in HWhi, HAlo. lia. }
      (* s11, s1 and the three cells Inv_A81b14 reads: the run keeps s11 and s1 and writes only the frame's shadow,
         which is apart from the real-stack spill [A + 192] (A is above HIGHMEM_BEG) and from the frame records
         (application bytes) *)
      exists A, idb, junk.
      split; [rewrite E9; exact HAc9|].
      split; [unfold rg in *; rewrite E27; exact H27|].
      split; [exact HAcr|].
      pose proof (Happ (fr + 2688) ltac:(lia)) as Hap1. pose proof (Happ (fr + 2725) ltac:(lia)) as Hap2.
      pose proof (Happ (fr + 2768) ltac:(lia)) as Hap3. pose proof (Happ (fr + 2839) ltac:(lia)) as Hap4.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap1, Hap2, Hap3, Hap4.
      assert (HWlo' : 0x7fff8000 <= Sfr fr) by (unfold LOWMEM_END in HWlo; exact HWlo).
      assert (HWhi' : Sfr fr + FRAME_SHADOW <= 0x10007fff8000) by (unfold HIGHMEM_BEG in HWhi; exact HWhi).
      assert (HAlo' : 0x10007fff8000 <= A) by (unfold HIGHMEM_BEG in HAlo; exact HAlo).
      (* rw_cells_transport is lib.Lib.Frame's; this run's munch is the UL flavour, bridged by fr_munch_ul *)
      assert (MUL : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch [(Sfr fr, Sfr fr + FRAME_SHADOW)] mem
                      mem').
      { first [exact MU | exact (proj2 (fr_munch_ul _ mem mem') MU) | exact (proj1 (fr_munch_ul _ mem mem') MU)]. }
      split.
      { eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.rw_cells_transport;
          [exact HC208 | exact MUL | exact WM |].
        simpl. repeat match goal with |- _ /\ _ => split end; try exact I.
        clear - HWhi' HAlo' HFSv. lia. }
      split.
      { eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.rw_cells_transport;
          [exact HCidb | exact MUL | exact WM |].
        simpl. repeat match goal with |- _ /\ _ => split end; try exact I.
        clear - HWlo' HWhi' Hap1 Hap2 HFSv. lia. }
      split.
      { eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.rw_cells_transport;
          [exact HCjunk | exact MUL | exact WM |].
        simpl. repeat match goal with |- _ /\ _ => split end; try exact I.
        clear - HWlo' HWhi' Hap3 Hap4 HFSv. lia. }
      (* push 9: the spills [A + 280] / [A + 240] (real stack, above the shadow) and the cells at fr + 3040 /
         fr + 3056 (frame bytes, application memory) are apart from the frame shadow too *)
      pose proof (Happ (fr + 3040) ltac:(lia)) as Hap5. pose proof (Happ (fr + 3087) ltac:(lia)) as Hap6.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap5, Hap6.
      split.
      { unfold q64 in *. eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.bytes_at_transport;
          [exact Hq280 | exact MUL |].
        rewrite length_le8. simpl. repeat match goal with |- _ /\ _ => split end; try exact I.
        clear - HWhi' HAlo' HFSv. lia. }
      split.
      { unfold q64 in *. eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.bytes_at_transport;
          [exact Hq240 | exact MUL |].
        rewrite length_le8. simpl. repeat match goal with |- _ /\ _ => split end; try exact I.
        clear - HWhi' HAlo' HFSv. lia. }
      exists jy, junk2. split.
      { eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.rw_cells_transport;
          [exact HCjy | exact MUL | exact WM |].
        simpl. repeat match goal with |- _ /\ _ => split end; try exact I.
        clear - HWlo' HWhi' Hap5 Hap6 HFSv. lia. }
      { eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.rw_cells_transport;
          [exact HCj2 | exact MUL | exact WM |].
        simpl. repeat match goal with |- _ /\ _ => split end; try exact I.
        clear - HWlo' HWhi' Hap5 Hap6 HFSv. lia. }
Qed.

Lemma seg_P1 : asan_set_shadow_f8_contract ->
  Hcut B APIf ra (Inv_A81b10 B APIf ra) -> Hcut B APIf ra P1_entry.
Proof.
  intros SET Hbc g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hbody).
  subst c.
  pose proof HFRA as HFRA2. destruct HFRA2 as (A & sp & s5 & _ & _ & _ & _ & Hhalt & _).
  pose proof Hbody as (_ & _ & _ & _ & _ & Ha0 & _). unfold a0v, rg in Ha0.
  rewrite SEGS.
  (* one step of beqz a0,81ac8 (a0 = 0): registers and memory unchanged *)
  apply (sl_run_lib regs (Z_to_bv 64 0x81ac0) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81ac8 /\ R = Regs6ss.mkR_of regs /\ mem' = mem)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite p1_mkR_of.
    eapply evt_mono; [apply p1_beqz; exact Ha0|].
    intros ms' Hms. do 3 eexists. split; [exact Hms|].
    split; [reflexivity|]. split; [reflexivity | reflexivity].
  - intros R pc' mem' regs'' md' (Hpc & HR & Hm) Hreg Hmat.
    subst pc' mem' R.
    assert (Hrr : forall r, getr regs'' r = getr regs r) by (intros r; rewrite Hreg; apply reg_mkR).
    rewrite <- SEGS. apply (seg_P1_70 SET Hbc g).
    exists regs'', mem, md', fr.
    split; [reflexivity|].
    split.
    { apply (sl_fra_move B APIf ra g fr [] regs regs'' mem md md' HFRA); try apply Hrr. exact Hmat. }
    split; [eapply ent_mat; [exact HENT | exact Hmat]|].
    destruct Hbody as (Hn & Hour & HCUR & HPRO & HS144 & _ & (Q & (A' & HA' & HQ) & HQ1 & HQ2) &
      (Ac & idb & junk & HAc9 & H27 & HAcr & HC208 & HCidb & HCjunk & Hq280 & Hq240 & HCj)).
    split; [exact Hn|]. split; [exact Hour|].
    split.
    { destruct HCUR as (Hc & H22 & H25). split; [exact Hc|].
      unfold rg in *. rewrite !Hrr. split; [exact H22 | exact H25]. }
    split; [exact (pro_regs g fr regs regs'' mem HPRO (Hrr _))|].
    split.
    { destruct HS144 as (A1 & HrA1 & Hq144). exists A1.
      split; [unfold rg in *; rewrite Hrr; exact HrA1 | exact Hq144]. }
    split; [unfold a0v, rg; rewrite Hrr; exact Ha0|].
    split.
    { exists Q. split; [|split; [exact HQ1 | exact HQ2]].
      exists A'. split; [unfold rg in *; rewrite Hrr; exact HA' | exact HQ]. }
    (* the branch step changes no register and no memory *)
    exists Ac, idb, junk.
    split; [rewrite Hrr; exact HAc9|].
    split; [unfold rg in *; rewrite Hrr; exact H27|].
    split; [exact HAcr|].
    split; [exact HC208|]. split; [exact HCidb|]. split; [exact HCjunk|].
    split; [exact Hq280|]. split; [exact Hq240 | exact HCj].
Qed.

End P1.
