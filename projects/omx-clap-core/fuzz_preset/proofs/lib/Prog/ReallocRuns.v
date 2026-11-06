(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Step.v; 242 of its 269 lines of code are new or changed and 674 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require KindBGlue.
Import ListNotations.
Open Scope Z_scope.

Lemma rr_le1_one : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. reflexivity. Qed.

Definition rr_pmono (m m' : word -> option byte) : Prop := forall x, m x <> None -> m' x <> None.

Lemma rr_pmono_write : forall m0 m a bs, rr_pmono m0 m -> rr_pmono m0 (write_to_mem m a bs).
Proof.
  intros m0 m a bs H x Hx. specialize (H x Hx). clear Hx m0. revert m a H.
  induction bs as [|b bs IH]; intros m a H; cbn; [exact H|].
  apply IH. cbv beta. destruct (bv_eqb x a); [discriminate | exact H].
Qed.

Ltac rr_mas :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    lazymatch goal with
    | H : rw_cells segs m A ?cs |- _ =>
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          change bs with (cbytes c');
          try lazymatch goal with
          | HM : munch ?W ?m0 m |- _ =>
              apply (munch_write W m0 m (A + Z.of_nat kn) (cbytes c')) in HM;
              [ | lia | simpl_sizes; lia | simpl_sizes; cbn [inside]; lia ]
          end;
          try lazymatch goal with
          | HW : wmono segs ?m0 m |- _ => apply (wmono_write segs m0 m (wa (A + Z.of_nat kn)) (cbytes c')) in HW
          end;
          try lazymatch goal with
          | HP : rr_pmono ?m0 m |- _ => apply (rr_pmono_write m0 m (wa (A + Z.of_nat kn)) (cbytes c')) in HP
          end;
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; try clear m; try rename H' into H
        end
    end
  end.

Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Step.mem_after_store_opt ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => rewrite ?rr_le1_one; fix_lit_store; rr_mas
  | _ => idtac
  end.

Lemma rr_rwc8 : forall m A v, bytes_at rsegs m A (le8 v) -> wr_at rsegs m A 8 -> rw_cells rsegs m A [C8 v].
Proof.
  intros m A v HB HW. split; [split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB] | exact HW].
Qed.

Lemma rr_carve8 : forall m lo hi a, stk rsegs m lo hi -> lo <= hi - 8 -> a = hi - 8 ->
  stk rsegs m lo a /\ exists j, rw_cells rsegs m a [CB 8 j].
Proof.
  intros m lo hi a H Hl ->. destruct (stk_carve rsegs m lo hi 8 H ltac:(lia)) as (H1 & j & H2).
  split; [exact H1|]. exists j. exact H2.
Qed.

Lemma rr_rwc8_bytes : forall m A v v', rw_cells rsegs m A [C8 v] -> v = v' -> bytes_at rsegs m A (le8 v').
Proof.
  intros m A v v' ((_ & HB) & _) <-. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
Qed.

Lemma rr_shr_range : forall n k, 0 <= n < 2 ^ 64 -> 0 <= k -> 0 <= Z.shiftr n k < 2 ^ 64.
Proof.
  intros n k Hn Hk. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply (Z.le_lt_trans _ n); [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]|lia].
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). nia.
Qed.

Lemma rr_byte_shr : forall n k, 0 <= n < 2 ^ 64 -> 0 <= k ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 n)) k))) = Z_to_bv 8 (Z.shiftr n k).
Proof.
  intros n k Hn Hk. rewrite (unsigned_lit n) by lia. rewrite unsigned_lit by (apply rr_shr_range; lia). reflexivity.
Qed.

Lemma rr_byte_0 : forall n, 0 <= n < 2 ^ 64 -> Z_to_bv 8 (bv_unsigned (Z_to_bv 64 n)) = Z_to_bv 8 n.
Proof. intros n Hn. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma rr_head_le8 : forall m b n (x0 x1 x2 x3 x4 x5 x6 x7 : byte), 0 <= n < 2 ^ 64 ->
  rw_cells rsegs m b [C1 x0; C1 x1; C1 x2; C1 x3; C1 x4; C1 x5; C1 x6; C1 x7] ->
  x0 = Z_to_bv 8 n -> x1 = Z_to_bv 8 (Z.shiftr n 8) -> x2 = Z_to_bv 8 (Z.shiftr n 16) -> x3 = Z_to_bv 8 (Z.shiftr n 24) ->
  x4 = Z_to_bv 8 (Z.shiftr n 32) -> x5 = Z_to_bv 8 (Z.shiftr n 40) -> x6 = Z_to_bv 8 (Z.shiftr n 48) ->
  x7 = Z_to_bv 8 (Z.shiftr n 56) ->
  bytes_at rsegs m b (le8 (Z_to_bv 64 n)).
Proof.
  intros m b n x0 x1 x2 x3 x4 x5 x6 x7 Hn ((_ & HB) & _) -> -> -> -> -> -> -> ->.
  cbn [cells_bytes cbytes app] in HB.
  change (le8 (Z_to_bv 64 n)) with (Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 n))).
  rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. exact HB.
Qed.

Definition hd8 (k : Z) : list byte :=
  [Z_to_bv 8 (YO0f.le_byte k 8 0); Z_to_bv 8 (YO0f.le_byte k 8 1); Z_to_bv 8 (YO0f.le_byte k 8 2);
   Z_to_bv 8 (YO0f.le_byte k 8 3); Z_to_bv 8 (YO0f.le_byte k 8 4); Z_to_bv 8 (YO0f.le_byte k 8 5);
   Z_to_bv 8 (YO0f.le_byte k 8 6); Z_to_bv 8 (YO0f.le_byte k 8 7)].

(* fuzz_realloc of the #102 plain twin (c8f4d6b8, symtab: fuzz_realloc 0x15564 size 572, fuzz_malloc 0x15454; g_fail_at
   0x24520, g_ran_out 0x347a8, g_live 0x347b0, g_peak 0x347b8, g_count 0x347c0; libc realloc 0x19144). Frame 48: the
   prologue saves ra, s0, s1, s2, s3 and s4 (s2 = &g_ran_out, s3 = &g_fail_at, s4 = k). run0: p = 0, the TAIL call
   `j fuzz_malloc` at 0x155dc. *)
Definition run0_post (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S n : Z) (ms' : machine_state) : Prop :=
  exists m' : word -> option byte,
    munch [(S + -48, S)] m m' /\ wmono rsegs m m' /\
    ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15454) fc None m' (seg_rom rsegs).

Lemma run0 : forall (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S n : Z),
  0 <= n < 2 ^ 64 -> 0 <= S + -48 -> S <= 2 ^ 63 ->
  stk rsegs m (S + -48) S ->
  evt rsegs (run0_post ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S n)
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15564) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S n
    Hn HS1 HS2 HK.
  destruct (rr_carve8 m (S + -48) S (S + -8) HK ltac:(lia) ltac:(lia)) as (HK1 & j1 & K1).
  destruct (rr_carve8 m (S + -48) (S + -8) (S + -16) HK1 ltac:(lia) ltac:(lia)) as (HK2 & j2 & K2).
  destruct (rr_carve8 m (S + -48) (S + -16) (S + -24) HK2 ltac:(lia) ltac:(lia)) as (HK3 & j3 & K3).
  destruct (rr_carve8 m (S + -48) (S + -24) (S + -32) HK3 ltac:(lia) ltac:(lia)) as (HK4 & j4 & K4).
  destruct (rr_carve8 m (S + -48) (S + -32) (S + -40) HK4 ltac:(lia) ltac:(lia)) as (HK5 & j5 & K5).
  destruct (rr_carve8 m (S + -48) (S + -40) (S + -48) HK5 ltac:(lia) ltac:(lia)) as (HK6 & j6 & K6).
  clear HK HK1 HK2 HK3 HK4 HK5 HK6.
  assert (HM : munch [(S + -48, S)] m m) by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  do 9 step.
  if_true.
  do 9 step.
  apply evt_done. eexists. split; [exact HM|]. split; [exact HW|]. reflexivity.
Qed.

(* run1: p <> 0, from the entry to the CHOSEN-FAIL return, or through disown (head k at p - 16, g_live -= k) to the
   call of libc realloc (0x15690 jal 0x19144, return address 0x15694). The TOOBIG branch (0x155e4 bltu n, -16 not
   taken: the inlined refused()) is excluded by n <= 2^64 - 17. *)
Definition run1_post (ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S p n k live cnt fail : Z) (ms' : machine_state) : Prop :=
  exists (a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
    munch [(S + -48, S); (0x347b0, 0x347b8); (0x347c0, 0x347c8); (0x24520, 0x24528)] m m' /\ wmono rsegs m m' /\
    bytes_at rsegs m' 0x347c0 (le8 (Z_to_bv 64 (cnt + 1))) /\
    ( (cnt = fail /\ bytes_at rsegs m' 0x24520 (le8 (Z_to_bv 64 (2 ^ 64 - 1))) /\
       bytes_at rsegs m' 0x347b0 (le8 (Z_to_bv 64 live)) /\
       ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs))
    \/ (cnt <> fail /\ bytes_at rsegs m' 0x24520 (le8 (Z_to_bv 64 fail)) /\
       bytes_at rsegs m' 0x347b0 (le8 (Z_to_bv 64 (live - k))) /\
       bytes_at rsegs m' (S + -8) (le8 ra) /\ bytes_at rsegs m' (S + -16) (le8 s0) /\
       bytes_at rsegs m' (S + -24) (le8 s1) /\ bytes_at rsegs m' (S + -32) (le8 s2) /\
       bytes_at rsegs m' (S + -40) (le8 s3) /\ bytes_at rsegs m' (S + -48) (le8 s4) /\
       ms' = MS (mkR (Z_to_bv 64 0x15694) (Z_to_bv 64 (S + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (p + -16))
                     (Z_to_bv 64 (p + -16)) (Z_to_bv 64 (n + 16)) a2' a3' a4' a5' a6' a7
                     (Z_to_bv 64 0x347a8) (Z_to_bv 64 0x24520) (Z_to_bv 64 k) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x19144) fc None m' (seg_rom rsegs))).

Lemma run1 : forall (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S p n k live cnt fail : Z),
  16 <= p < 2 ^ 63 -> 0 <= n <= 2 ^ 64 - 17 -> 0 <= k < 2 ^ 64 -> 0 <= live < 2 ^ 64 ->
  0 <= cnt < 2 ^ 64 -> 0 <= fail < 2 ^ 64 ->
  0x347c8 <= S + -48 -> S <= 2 ^ 63 -> p + -8 <= S + -48 ->
  (p + -8 <= 0x347b0 \/ 0x347c8 <= p + -16) -> (p + -8 <= 0x24520 \/ 0x24528 <= p + -16) ->
  stk rsegs m (S + -48) S ->
  bytes_at rsegs m 0x347b0 (le8 (Z_to_bv 64 live)) -> wr_at rsegs m 0x347b0 8 ->
  bytes_at rsegs m 0x347c0 (le8 (Z_to_bv 64 cnt)) -> wr_at rsegs m 0x347c0 8 ->
  bytes_at rsegs m 0x24520 (le8 (Z_to_bv 64 fail)) -> wr_at rsegs m 0x24520 8 ->
  bytes_at rsegs m (p + -16) (hd8 k) ->
  evt rsegs (run1_post ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S p n k live cnt fail)
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15564) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S p n k live cnt fail
    Hp Hn Hk Hl Hc Hf HS1 HS2 Hps Hpg1 Hpg2 HK HL HLw HC HCw HF HFw HH.
  destruct (rr_carve8 m (S + -48) S (S + -8) HK ltac:(lia) ltac:(lia)) as (HK1 & j1 & K1).
  destruct (rr_carve8 m (S + -48) (S + -8) (S + -16) HK1 ltac:(lia) ltac:(lia)) as (HK2 & j2 & K2).
  destruct (rr_carve8 m (S + -48) (S + -16) (S + -24) HK2 ltac:(lia) ltac:(lia)) as (HK3 & j3 & K3).
  destruct (rr_carve8 m (S + -48) (S + -24) (S + -32) HK3 ltac:(lia) ltac:(lia)) as (HK4 & j4 & K4).
  destruct (rr_carve8 m (S + -48) (S + -32) (S + -40) HK4 ltac:(lia) ltac:(lia)) as (HK5 & j5 & K5).
  destruct (rr_carve8 m (S + -48) (S + -40) (S + -48) HK5 ltac:(lia) ltac:(lia)) as (HK6 & j6 & K6).
  clear HK HK1 HK2 HK3 HK4 HK5 HK6.
  apply rr_rwc8 in HL; [|exact HLw]. apply rr_rwc8 in HC; [|exact HCw]. apply rr_rwc8 in HF; [|exact HFw].
  clear HLw HCw HFw.
  unfold hd8 in HH.
  assert (HR : ro_cells rsegs m (p + -16)
     [C1 (Z_to_bv 8 (YO0f.le_byte k 8 0)); C1 (Z_to_bv 8 (YO0f.le_byte k 8 1)); C1 (Z_to_bv 8 (YO0f.le_byte k 8 2));
      C1 (Z_to_bv 8 (YO0f.le_byte k 8 3)); C1 (Z_to_bv 8 (YO0f.le_byte k 8 4)); C1 (Z_to_bv 8 (YO0f.le_byte k 8 5));
      C1 (Z_to_bv 8 (YO0f.le_byte k 8 6)); C1 (Z_to_bv 8 (YO0f.le_byte k 8 7))])
    by (split; [cbn; tauto | exact HH]).
  clear HH.
  assert (HM : munch [(S + -48, S); (0x347b0, 0x347b8); (0x347c0, 0x347c8); (0x24520, 0x24528)] m m)
    by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  do 9 step.
  assert (C0 : bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite C0; cbv iota.
  do 9 step.
  if_cases HB; zify_cond HB.
  - step. step. if_cases HB2; zify_cond HB2; [|exfalso; lia].
    do 24 step.
    lazymatch goal with
    | |- context [Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl ?h 32))) ?l)] =>
        replace (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl h 32))) l)) with (Z_to_bv 64 k)
          by (symmetry; f_equal; KindBGlue.kb_lbu8 k)
    end.
    do 5 step. apply evt_done. exists (Z_to_bv 64 0). do 6 eexists.
    split; [exact HM|]. split; [exact HW|]. split; [eapply rr_rwc8_bytes; [exact HC | reflexivity]|].
    right. split; [lia|]. split; [eapply rr_rwc8_bytes; [exact HF | reflexivity]|].
    split; [eapply rr_rwc8_bytes; [exact HL | rewrite !unsigned_lit by lia; reflexivity]|].
    split; [eapply rr_rwc8_bytes; [exact K1 | reflexivity]|].
    split; [eapply rr_rwc8_bytes; [exact K2 | reflexivity]|].
    split; [eapply rr_rwc8_bytes; [exact K3 | reflexivity]|].
    split; [eapply rr_rwc8_bytes; [exact K4 | reflexivity]|].
    split; [eapply rr_rwc8_bytes; [exact K5 | reflexivity]|].
    split; [eapply rr_rwc8_bytes; [exact K6 | reflexivity]|].
    reflexivity.
  - do 12 step. apply evt_done. do 7 eexists.
    split; [exact HM|]. split; [exact HW|]. split; [eapply rr_rwc8_bytes; [exact HC | reflexivity]|].
    left. split; [lia|]. split; [eapply rr_rwc8_bytes; [exact HF | apply bv_eq; vm_compute; reflexivity]|].
    split; [eapply rr_rwc8_bytes; [exact HL | reflexivity]|]. reflexivity.
Qed.

(* run2: from the return of libc realloc (0x15694, a0 = b <> 0) to the SUCCESS return: the head n at b, g_live += n,
   g_peak := max, a0 = b + 16, and the epilogue that restores ra, s0 .. s4. *)
Definition run2_post (gp tp t0 t1 t2 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S n b live peak : Z) (rav s0v s1v s2v s3v s4v : word)
    (ms' : machine_state) : Prop :=
  exists (a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
    munch [(b, b + 8); (0x347b0, 0x347c0)] m m' /\ wmono rsegs m m' /\ rr_pmono m m' /\
    bytes_at rsegs m' b (le8 (Z_to_bv 64 n)) /\
    bytes_at rsegs m' 0x347b0 (le8 (Z_to_bv 64 ((live + n) mod 2 ^ 64))) /\
    bytes_at rsegs m' 0x347b8 (le8 (Z_to_bv 64 (Z.max peak ((live + n) mod 2 ^ 64)))) /\
    ms' = MS (mkR rav (Z_to_bv 64 S) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 (b + 16)) a1' a2' a3' a4' a5' a6' a7
                  s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc None m' (seg_rom rsegs).

Lemma run2 : forall (ra gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S n b live peak : Z) (rav s0v s1v s2v s3v s4v : word),
  0 <= n < 2 ^ 64 -> 0x347c0 <= S + -48 -> S <= 2 ^ 63 -> 0 < b -> b + 8 <= S + -48 ->
  (b + 8 <= 0x347b0 \/ 0x347c0 <= b) -> 0 <= live < 2 ^ 64 -> 0 <= peak < 2 ^ 64 ->
  stk rsegs m b (b + 8) ->
  bytes_at rsegs m (S + -8) (le8 rav) -> wr_at rsegs m (S + -8) 8 ->
  bytes_at rsegs m (S + -16) (le8 s0v) -> wr_at rsegs m (S + -16) 8 ->
  bytes_at rsegs m (S + -24) (le8 s1v) -> wr_at rsegs m (S + -24) 8 ->
  bytes_at rsegs m (S + -32) (le8 s2v) -> wr_at rsegs m (S + -32) 8 ->
  bytes_at rsegs m (S + -40) (le8 s3v) -> wr_at rsegs m (S + -40) 8 ->
  bytes_at rsegs m (S + -48) (le8 s4v) -> wr_at rsegs m (S + -48) 8 ->
  bytes_at rsegs m 0x347b0 (le8 (Z_to_bv 64 live)) -> wr_at rsegs m 0x347b0 8 ->
  bytes_at rsegs m 0x347b8 (le8 (Z_to_bv 64 peak)) -> wr_at rsegs m 0x347b8 8 ->
  evt rsegs (run2_post gp tp t0 t1 t2 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S n b live peak rav s0v s1v s2v s3v s4v)
    (MS (mkR ra (Z_to_bv 64 (S + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) s1 (Z_to_bv 64 b) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x347a8) (Z_to_bv 64 0x24520) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15694) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S n b live peak
    rav s0v s1v s2v s3v s4v Hn HS1 HS2 Hb0 Hb1 Hb2 Hl Hp HH K1 K1w K2 K2w K3 K3w K4 K4w K5 K5w K6 K6w HL HLw HP HPw.
  apply rr_rwc8 in K1; [|exact K1w]. apply rr_rwc8 in K2; [|exact K2w]. apply rr_rwc8 in K3; [|exact K3w].
  apply rr_rwc8 in K4; [|exact K4w]. apply rr_rwc8 in K5; [|exact K5w]. apply rr_rwc8 in K6; [|exact K6w].
  apply rr_rwc8 in HL; [|exact HLw]. apply rr_rwc8 in HP; [|exact HPw]. clear K1w K2w K3w K4w K5w K6w HLw HPw.
  destruct (stk_bytes rsegs m b (b + 8) HH ltac:(lia)) as (hb & Hlen & Hhb).
  destruct hb as [|h0 [|h1 [|h2 [|h3 [|h4 [|h5 [|h6 [|h7 [|? ?]]]]]]]]]; cbn in Hlen; try lia.
  assert (HB : rw_cells rsegs m b [CB 1 [h0]; CB 1 [h1]; CB 1 [h2]; CB 1 [h3]; CB 1 [h4]; CB 1 [h5]; CB 1 [h6]; CB 1 [h7]]).
  { split; [split; [cbn; tauto | exact Hhb] |].
    destruct HH as (_ & _ & HH). split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    exact (proj1 (HH (b + i) ltac:(lia))). }
  clear HH Hhb Hlen.
  assert (HM : munch [(b, b + 8); (0x347b0, 0x347c0)] m m) by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  assert (HPm : rr_pmono m m) by (intros x Hx; exact Hx).
  step.
  assert (C0 : bv_eqb (Z_to_bv 64 b) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite C0; cbv iota.
  do 20 step.
  if_cases HG; zify_cond HG.
  - do 10 step. apply evt_done. do 7 eexists.
    split; [exact HM|]. split; [exact HW|]. split; [exact HPm|].
    split; [eapply rr_head_le8; [exact Hn | exact HB | apply rr_byte_0; lia | apply rr_byte_shr; lia ..]|].
    split; [eapply rr_rwc8_bytes; [exact HL | symmetry; apply Z_to_bv_mod64]|].
    split; [eapply rr_rwc8_bytes; [exact HP | f_equal; lia]|]. reflexivity.
  - do 11 step. apply evt_done. do 7 eexists.
    split; [exact HM|]. split; [exact HW|]. split; [exact HPm|].
    split; [eapply rr_head_le8; [exact Hn | exact HB | apply rr_byte_0; lia | apply rr_byte_shr; lia ..]|].
    split; [eapply rr_rwc8_bytes; [exact HL | symmetry; apply Z_to_bv_mod64]|].
    split; [eapply rr_rwc8_bytes; [exact HP | rewrite Z.max_r by lia; symmetry; apply Z_to_bv_mod64]|]. reflexivity.
Qed.
