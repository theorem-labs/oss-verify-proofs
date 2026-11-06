(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Step.v; 171 of its 200 lines of code are new or changed and 672 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import strlen_c memcpy_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sd_le1 : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. reflexivity. Qed.

Ltac sd_mas :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    lazymatch goal with
    | H : rw_cells segs m A ?cs |- _ =>
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          try lazymatch goal with
          | HM : munch ?W ?m0 m |- _ =>
              apply (munch_write W m0 m (A + Z.of_nat kn) (cbytes c')) in HM;
              [ | lia | simpl_sizes; lia | simpl_sizes; cbn [inside]; lia ]
          end;
          try lazymatch goal with
          | HW : wmono segs ?m0 m |- _ => apply (wmono_write segs m0 m (wa (A + Z.of_nat kn)) (cbytes c')) in HW
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

Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Step.mem_after_store_opt ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => rewrite ?sd_le1; fix_lit_store; sd_mas
  | _ => idtac
  end.

Lemma sd_rwc8 : forall m A v, bytes_at rsegs m A (le8 v) -> wr_at rsegs m A 8 -> rw_cells rsegs m A [C8 v].
Proof.
  intros m A v HB HW. split; [split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB] | exact HW].
Qed.

Lemma sd_carve8 : forall m lo hi a, stk rsegs m lo hi -> lo <= hi - 8 -> a = hi - 8 ->
  stk rsegs m lo a /\ exists j, rw_cells rsegs m a [CB 8 j].
Proof.
  intros m lo hi a H Hl ->. destruct (stk_carve rsegs m lo hi 8 H ltac:(lia)) as (H1 & j & H2).
  split; [exact H1|]. exists j. exact H2.
Qed.

Lemma sd_rwc8_bytes : forall m A v v', rw_cells rsegs m A [C8 v] -> v = v' -> bytes_at rsegs m A (le8 v').
Proof.
  intros m A v v' ((_ & HB) & _) <-. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
Qed.

Definition sd1_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (S s N : Z) (ms' : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    munch [(S + -32, S)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    bytes_at rsegs m' (S + -8) (le8 ra) /\ bytes_at rsegs m' (S + -16) (le8 s0) /\
    bytes_at rsegs m' (S + -24) (le8 s1) /\
    ms' = MS (mkR (Z_to_bv 64 0x14344) (Z_to_bv 64 (S + -32)) gp tp t0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 (N + 1))
                  (Z_to_bv 64 (N + 1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x14064) fc None m' (seg_rom rsegs).

Lemma sd1 : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S s : Z) (cs sl : list byte),
  strlen_contract ->
  0x10000 <= S + -32 -> S <= 2 ^ 63 ->
  stk rsegs m (S + -32) S ->
  bytes_at rsegs m s (cs ++ Z_to_bv 8 0 :: sl) -> ~ In (Z_to_bv 8 0) cs ->
  (- (s + Z.of_nat (length cs) + 1)) mod 8 <= Z.of_nat (length sl) ->
  s + Z.of_nat (length cs) + 1 + Z.of_nat (length sl) <= S + -32 \/ S <= s ->
  mem_inv rsegs m ->
  evt rsegs (sd1_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S s (Z.of_nat (length cs)))
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14320) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S s cs sl
    HSTR HS1 HS2 HK HB HZ HA HD HI.
  unfold strlen_contract, STRLEN in HSTR.
  pose proof (bytes_at_bound rsegs m s _ HB) as HBb. rewrite length_app in HBb. cbn [length] in HBb.
  destruct (sd_carve8 m (S + -32) S (S + -8) HK ltac:(lia) ltac:(lia)) as (HK1 & j1 & K1).
  destruct (sd_carve8 m (S + -32) (S + -8) (S + -16) HK1 ltac:(lia) ltac:(lia)) as (HK2 & j2 & K2).
  destruct (sd_carve8 m (S + -32) (S + -16) (S + -24) HK2 ltac:(lia) ltac:(lia)) as (HK3 & j3 & K3).
  clear HK HK1 HK2 HK3.
  assert (HM : munch [(S + -32, S)] m m) by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  remember (cs ++ Z_to_bv 8 0 :: sl) as bs eqn:EB.
  assert (HL : Z.of_nat (length bs) = Z.of_nat (length cs) + 1 + Z.of_nat (length sl))
    by (subst bs; rewrite length_app; cbn [length]; lia).
  do 6 step.
  subst bs.
  eapply evt_cut.
  { eapply HSTR with (str := cs) (slack := sl);
      [rewrite unsigned_lit by lia; exact HB | exact HZ | rewrite unsigned_lit by lia; exact HA | exact HI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI & _).
  subst ms'.
  rewrite ret_pc_even by first [lia | reflexivity].
  pose proof (rw_cells_transport rsegs [] _ m' _ _ K1 MU WM I) as K1'.
  pose proof (rw_cells_transport rsegs [] _ m' _ _ K2 MU WM I) as K2'.
  pose proof (rw_cells_transport rsegs [] _ m' _ _ K3 MU WM I) as K3'.
  assert (HM' : munch [(S + -32, S)] m m').
  { eapply munch_trans; [exact HM|]. eapply munch_weaken; [|exact MU]. intros x _. exact I. }
  assert (HW' : wmono rsegs m m') by (eapply wmono_trans; [exact HW | exact WM]).
  clear K1 K2 K3 HM HW HI.
  do 3 step.
  apply evt_done. do 15 eexists.
  split; [exact HM'|]. split; [exact HW'|]. split; [exact MI|].
  split; [eapply sd_rwc8_bytes; [exact K1' | reflexivity]|].
  split; [eapply sd_rwc8_bytes; [exact K2' | reflexivity]|].
  split; [eapply sd_rwc8_bytes; [exact K3' | reflexivity]|].
  reflexivity.
Qed.

Lemma sd1_shape : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S s N ms',
  sd1_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S s N ms' ->
  exists R pc m0, ms' = MS R F pc fc None m0 (seg_rom rsegs).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S s N ms'
    (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & _ & _ & _ & _ & _ & _ & E).
  eexists _, _, _. exact E.
Qed.

Lemma sd_roc8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v HB. split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]. Qed.

Ltac sd_fixS :=
  repeat match goal with |- context [Z_to_bv 64 (?x + -32 + 32)] => replace (x + -32 + 32) with x by lia end.

Definition sd2n_post (rav gp tp t0 t1 t2 s0v s1v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (ms' : machine_state) : Prop :=
  ms' = MS (mkR rav (Z_to_bv 64 S) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc None m (seg_rom rsegs).

Lemma sd2n : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0v s1v : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z),
  0x10000 <= S + -32 -> S <= 2 ^ 63 ->
  bytes_at rsegs m (S + -8) (le8 rav) -> bytes_at rsegs m (S + -16) (le8 s0v) -> bytes_at rsegs m (S + -24) (le8 s1v) ->
  evt rsegs (sd2n_post rav gp tp t0 t1 t2 s0v s1v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S)
    (MS (mkR ra (Z_to_bv 64 (S + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14344) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0v s1v F fc m S
    HS1 HS2 K1 K2 K3.
  apply sd_roc8 in K1. apply sd_roc8 in K2. apply sd_roc8 in K3.
  step. try if_true.
  do 5 step.
  apply evt_done. unfold sd2n_post. sd_fixS. reflexivity.
Qed.

Definition sd2c_post (rav gp tp s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (S res n : Z) (src : list byte) (ms' : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    munch [(res, res + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ bytes_at rsegs m' res src /\
    ms' = MS (mkR rav (Z_to_bv 64 S) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc None m' (seg_rom rsegs).

Lemma sd2c_shape : forall rav gp tp s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S res n src ms',
  sd2c_post rav gp tp s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S res n src ms' ->
  exists R pc m0, ms' = MS R F pc fc None m0 (seg_rom rsegs).
Proof.
  intros rav gp tp s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S res n src ms'
    (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & _ & _ & _ & _ & E).
  eexists _, _, _. exact E.
Qed.

Lemma sd2c : forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0v s1v : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S s res n : Z) (src junk : list byte),
  memcpy_contract ->
  0x10000 <= S + -32 -> S <= 2 ^ 63 -> 0 < res -> res + n <= 2 ^ 63 -> 0 <= s -> s + n <= 2 ^ 64 -> 0 < n ->
  Z.of_nat (length src) = n ->
  bytes_at rsegs m (S + -8) (le8 rav) -> bytes_at rsegs m (S + -16) (le8 s0v) -> bytes_at rsegs m (S + -24) (le8 s1v) ->
  bytes_at rsegs m s src -> rw_cells rsegs m res [CB (Z.to_nat n) junk] ->
  s + n <= res \/ res + n <= s ->
  mem_inv rsegs m ->
  evt rsegs (sd2c_post rav gp tp s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S res n src)
    (MS (mkR ra (Z_to_bv 64 (S + -32)) gp tp t0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 n) (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14344) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0v s1v F fc m S s res n
    src junk HMC HS1 HS2 Hr0 Hr1 Hs0 Hs1 Hn0 Hlen K1 K2 K3 HB HD Hdj HI.
  unfold memcpy_contract in HMC.
  apply sd_roc8 in K1. apply sd_roc8 in K2. apply sd_roc8 in K3.
  step.
  assert (C0 : bv_eqb (Z_to_bv 64 res) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite C0; cbv iota.
  do 7 step.
  eapply evt_cut.
  { eapply HMC with (src := src) (junk := junk);
      [ rewrite unsigned_lit by lia; exact HB
      | rewrite unsigned_lit by lia; lia
      | rewrite !unsigned_lit by lia; exact HD
      | rewrite !unsigned_lit by lia; exact Hdj
      | exact HI ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI & RW & _).
  subst ms'. rewrite !unsigned_lit in MU, RW by lia.
  apply evt_done. do 15 eexists.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [destruct RW as ((_ & HB') & _); cbn [cells_bytes cbytes] in HB'; rewrite app_nil_r in HB'; exact HB'|].
  sd_fixS. reflexivity.
Qed.
