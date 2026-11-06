(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog Printf_pieces.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit F_syscalls Stdio_base.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma rw_cells_recast : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma rw_cells_CB0 : forall m A, 0 <= A <= 2^64 -> rw_cells asegs m A [CB 0%nat []].
Proof.
  intros m A HA. split; [split|].
  - cbn. repeat split; exact I.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.

Lemma rw_cells_CB_join : forall m A n1 n2 (b1 b2 : list byte),
  rw_cells asegs m A [CB n1 b1] -> rw_cells asegs m (A + Z.of_nat n1) [CB n2 b2] -> rw_cells asegs m A [CB (n1 + n2)%nat (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 H1 H2.
  pose proof (rw_cells_bound _ _ _ _ H1) as R1. pose proof (rw_cells_bound _ _ _ _ H2) as R2. cbn [cells_size csize Nat.add] in R1, R2.
  destruct H1 as [[W1 B1] X1]. destruct H2 as [[W2 B2] X2]. cbn in W1, W2. destruct W1 as [L1 _]. destruct W2 as [L2 _].
  apply (rw_cells_recast m A [CB n1 b1; CB n2 b2]).
  - apply (proj2 (rw_cells_app asegs m A [CB n1 b1] [CB n2 b2])). cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
    split; [split; [split; [cbn; auto| exact B1]| exact X1] | split; [split; [cbn; auto| exact B2]| exact X2]].
  - cbn. rewrite length_app. repeat split; try lia; exact I.
  - cbn. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma rw_cells_CB_split : forall m A n (n1 : nat) (b : list byte),
  rw_cells asegs m A [CB n b] -> (n1 <= n)%nat ->
  rw_cells asegs m A [CB n1 (firstn n1 b)] /\ rw_cells asegs m (A + Z.of_nat n1) [CB (n - n1)%nat (skipn n1 b)].
Proof.
  intros m A n n1 b H Hn.
  destruct H as [[W B] X]. cbn in W. destruct W as [L _]. pose proof (bytes_at_bound _ _ _ _ B) as R. cbn [cells_bytes cbytes app] in R. rewrite app_nil_r in R.
  assert (H' : rw_cells asegs m A [CB n1 (firstn n1 b); CB (n - n1)%nat (skipn n1 b)]).
  { apply (rw_cells_recast m A [CB n b]).
    - split; [split; [cbn; auto| exact B]| exact X].
    - cbn. rewrite length_firstn, length_skipn. repeat split; try lia; exact I.
    - cbn. rewrite ?app_nil_r, firstn_skipn. reflexivity. }
  apply (proj1 (rw_cells_app asegs m A [CB n1 (firstn n1 b)] [CB (n - n1)%nat (skipn n1 b)])) in H'.
  cbn [cells_size csize Nat.add] in H'. rewrite Nat.add_0_r in H'. exact H'.
Qed.

Lemma stk_rejoin : forall m A cs mid hi,
  rw_cells asegs m A cs -> stk asegs m mid hi -> A + Z.of_nat (cells_size cs) = mid -> mid <= hi -> stk asegs m A hi.
Proof.
  intros m A cs mid hi RC ST E LE. subst mid.
  eapply stk_merge; [eapply stk_of_rw_cells; exact RC| exact ST| pose proof (rw_cells_bound _ _ _ _ RC); lia].
Qed.

Lemma disjoint_from_shrink : forall W a n n', disjoint_from W a n -> 0 <= n' <= n -> disjoint_from W a n'.
Proof.
  induction W as [|[lo hi] W IH]; intros a n n' H Hn; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [lia| apply (IH a n n' H2 Hn)].
Qed.

Lemma length_block_shadow : forall n, 0 <= n -> Z.of_nat (length (block_shadow n)) <= n / 8 + 1.
Proof.
  intros n Hn. unfold block_shadow. rewrite length_app, repeat_length.
  destruct (n mod 8 =? 0); cbn [length]; Z.div_mod_to_equations; lia.
Qed.

Lemma bshadow_transport : forall W m m' A n, 0 <= n ->
  rw_cells asegs m (sh A) (shadow_cells (block_shadow n)) -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W (sh A) (n / 8 + 1) -> rw_cells asegs m' (sh A) (shadow_cells (block_shadow n)).
Proof.
  intros W m m' A n Hn H MU WM D. eapply rw_cells_transport; [exact H | exact MU | exact WM |].
  rewrite cells_size_shadow. eapply disjoint_from_shrink; [exact D|]. pose proof (length_block_shadow n Hn). lia.
Qed.

Lemma implM_of_enode : forall {St A} (n : node) (pl : resp -> option A) (P : A -> machine_state -> Prop) (s : St) ms,
  impl asegs (at_node asegs) (enode n pl) (epost P) ms ->
  implM asegs (msys n pl) s (fun a s' ms' => P a ms' /\ s' = s) ms.
Proof.
  intros St A n pl P s ms H. unfold implM, msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.

Notation RTPA := 0x5e6970%Z (only parsing).
Section ReadI.
  Context {HC : HasCeiling} {St : Type}.
  Hypothesis RDF : read_front_stmt.
  Hypothesis RDB : read_back_stmt.

  Definition READI_DEPTH : Z := 2128 + A0_RT_STACK + 16.

  Definition read_icpt_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : mem) (s : St) : read_ans -> St -> machine_state -> Prop :=
    fun a s' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RTPA) t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q); (B, B + Z.of_nat n); (RTPA - 164, RTPA - 164 + 4)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ asan_env asegs m'
      /\ match a with
         | RdErr e => rw_cells asegs m' B [CB n junk] /\ rw_cells asegs m' (RTPA - 164) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
         | RdData bs => rw_cells asegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                        /\ rw_cells asegs m' (RTPA - 164) [C4 errv] /\ (length bs <= n)%nat
         end
      /\ s' = s.

  #[using="RDF RDB"] Lemma read_icpt : forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : St) (fd B cnt lo : Z) (junk : list byte) (errv : word),
    asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - READI_DEPTH -> q <= 2^47 ->
    rw_cells asegs m B [CB (Z.to_nat cnt) junk] -> rw_cells asegs m (RTPA - 164) [C4 errv] -> mem_inv asegs m ->
    a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 cnt ->
    (3 <= fd < 2^32)%Z -> (0 < cnt <= 2^24)%Z -> (B + cnt <= 0x5e5f80)%Z -> (0x5d5f40 <= B)%Z ->
    shw m B cnt ->
    implM asegs (msys (NRead fd B cnt) (dec_read B cnt)) s
          (read_icpt_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B (Z.to_nat cnt) junk errv lo m s)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RTPA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 A0_read) fc None m (seg_rom asegs)).
  Proof.
    intros until errv. intros ENV ST CLO LO QHI DST ERR MI -> -> -> FD CNT BHI BLO SHB.
    pose proof (@alloc_ceiling_bounds HC) as CEILB. unfold READI_DEPTH, A0_RT_STACK in LO.

    eapply implM_evt.
    { eapply (RDF _ q) with (lo := lo) (fd := fd) (buf := B) (cnt := cnt); rewrite ?unsigned_lit by lia;
        first [exact ENV | exact ST | exact MI | reflexivity | lia]. }
    cbv beta. intros ms1 PO.
    destruct PO as (u0 & u1 & u2 & x13 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & fjunk & -> & MU1 & WM1 & MI1 & ST1 & ENV1 & FR1).
    pose proof (rw_cells_transport asegs _ m m1 _ _ DST MU1 WM1 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as DST1.
    pose proof (rw_cells_transport asegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as ERR1.

    epose proof (read_spec (Z_to_bv 64 290504) (Z_to_bv 64 (q - 2128)) gp (Z_to_bv 64 RTPA) u0 u1 u2 (Z_to_bv 64 q) (Z_to_bv 64 B)
                  (Z_to_bv 64 fd) (Z_to_bv 64 B) (Z_to_bv 64 cnt) x13 x14 x15 x16 x17 (Z_to_bv 64 cnt) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                  F fc m1 fd cnt junk errv lo) as RS.
    rewrite !unsigned_lit in RS by lia.
    eapply implM_post_evt.
    { eapply implM_of_enode. eapply RS; first [exact ST1 | exact DST1 | exact ERR1 | exact MI1 | reflexivity | lia]. }
    clear RS. cbv beta. intros a s' ms' [PO ->].
    destruct PO as (v0 & v1 & v2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & RES).
    rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in RES by lia.
    change (6187376 + -164)%Z with 6187212%Z in MU2, RES.
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ FR1 MU2 WM2 ltac:(cbn [disjoint_from]; simpl_sizes; lia)) as FR2.
    assert (ENV2 : asan_env asegs m2) by (eapply asan_env_frame; [exact ENV1 | exact MU2 | exact WM2 | pose proof CEILB; env_safe_tac]).
    replace (ret_pc (Z_to_bv 64 290504)) with (Z_to_bv 64 290504) by (symmetry; rpc).

    assert (ERES : exists res, read_ret a = Z_to_bv 64 res /\ - 2^63 <= res < 2^63 /\ (0 < res -> res <= cnt)).
    { destruct a as [e|bs]; cbn [read_ret].
      - exists (-1). split; [reflexivity|]. lia.
      - exists (Z.of_nat (length bs)). split; [reflexivity|]. destruct RES as (_ & _ & Hbs). lia. }
    destruct ERES as (res & ERES & RR & RC). rewrite ERES.
    eapply evt_cut.
    { eapply (RDB _ _ _ _ _ _ q) with (lo := lo) (cnt := cnt) (buf := B) (fd := fd); rewrite ?unsigned_lit by lia.
      all: first [ exact FR2 | exact ENV2 | exact ST2 | exact MI2 | lia | unfold A0_RT_STACK; lia | idtac ].
      intros Hr.
      assert (SH2 : shw m2 B cnt).
      { eapply (shw_frame [(lo, q); (B, B + Z.of_nat (Z.to_nat cnt)); (6187212, 6187212 + 4)]); [exact SHB | | app_ivs_tac].
        eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros; lia. }
      destruct SH2 as (AC & RD & _). split; [lia|]. split; [eapply accessible_sub; [exact AC| lia| lia] |]. split; [eapply sh_readable_sub; [exact RD| lia| lia| lia] |].
      unfold icpt_rng, icpt_win. lia. }
    intros ms3 PO. destruct PO as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ENV3).
    rewrite <- ERES.
    apply evt_done. unfold read_icpt_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU3]]];
             unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]|].
    split; [exact MI3|]. split; [exact ST3|]. split; [exact ENV3|].
    split; [| reflexivity].
    destruct a as [e|bs]; cbn [read_ret] in *.
    - destruct RES as (R1 & R2 & R3). split; [| split; [| exact R3]].
      + eapply rw_cells_transport; [exact R1 | exact MU3 | exact WM3 | cbn [disjoint_from]; simpl_sizes; lia].
      + eapply rw_cells_transport; [exact R2 | exact MU3 | exact WM3 | cbn [disjoint_from]; simpl_sizes; lia].
    - destruct RES as (R1 & R2 & R3). split; [| split; [| exact R3]].
      + eapply rw_cells_transport; [exact R1 | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
      + eapply rw_cells_transport; [exact R2 | exact MU3 | exact WM3 | cbn [disjoint_from]; simpl_sizes; lia].
  Qed.
End ReadI.
