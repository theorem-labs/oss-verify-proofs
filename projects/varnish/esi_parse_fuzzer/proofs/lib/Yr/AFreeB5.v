(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMTac AMallocA AMallocI AMalmys AMal9l1 AFreeH.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMal9l1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AFreeB1 AFreeB2 ATransp AFreeB3 AFreeB4 AFreeT.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mrd_wview : forall segs (m : mem) (x : word) b, mrd segs m x = Some b -> ro_addr segs x = false -> wview segs m x <> None.
Proof.
  intros segs m x b R W. unfold mrd in R. unfold wview. destruct (m x) as [b0|] eqn:E; [congruence|].
  unfold seg_rom, memory_read in R. unfold ro_addr in W.
  change (Z.of_N 1) with 1 in R.
  destruct (find_segment segs (bv_unsigned x) 1) as [seg|]; [|discriminate].
  destruct (seg_writable seg); [|discriminate].
  destruct (seg_readable seg); [|discriminate].
  change (N.to_nat 1) with 1%nat in R. cbn [segment_read_bytes] in R.
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned x - Z.of_N (seg_base seg)))); [discriminate| discriminate].
Qed.

Lemma img_wr_at : forall (m : mem) a bs, bytes_at rsegs m a bs -> 0xa8000 <= a -> a + Z.of_nat (length bs) <= 0x60a000 ->
  wr_at rsegs m a (Z.of_nat (length bs)).
Proof.
  (intros m a bs; (first [ intro dR_12; dand3 dR_12 as B0 B1 B | intros (B0 & B1 & B) ]); intros Ha Hb). split; [lia|]. split; [lia|]. intros i Hi.
  specialize (B (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in B by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [| exfalso; apply nth_error_None in E; lia].
  apply (mrd_wview rsegs m _ b B). unfold wa.
  destruct (ro_addr rsegs (Z_to_bv 64 (a + i))) eqn:R; [|reflexivity]. exfalso.
  apply (proj1 (pa_ro_addr_iff _)) in R. rewrite unsigned_lit in R by lia. lia.
Qed.
Lemma img_rw_cells : forall (m : mem) a cs, cells_at rsegs m a cs -> 0xa8000 <= a -> a + Z.of_nat (cells_size cs) <= 0x60a000 ->
  rw_cells rsegs m a cs.
Proof.
  intros m a cs [W B] Ha Hb. split; [exact (conj W B)|]. rewrite <- (cells_bytes_length cs W) in Hb |- *. exact (img_wr_at m a _ B Ha Hb).
Qed.
Lemma img_rw_CB : forall (m : mem) a bs n, bytes_at rsegs m a bs -> length bs = n -> 0xa8000 <= a -> a + Z.of_nat n <= 0x60a000 ->
  rw_cells rsegs m a [CB n bs].
Proof.
  intros m a bs n B L Ha Hb. apply img_rw_cells; [| exact Ha| cbn [cells_size csize]; rewrite Nat.add_0_r; exact Hb].
  split; [cbn; rewrite L; split; [reflexivity| exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
Qed.
Lemma img_rw_C8x4 : forall (m : mem) a v0 v1 v2 v3,
  u64_at rsegs m (a + 0) v0 -> u64_at rsegs m (a + 8) v1 -> u64_at rsegs m (a + 16) v2 -> u64_at rsegs m (a + 24) v3 ->
  0xa8000 <= a -> a + 32 <= 0x60a000 ->
  rw_cells rsegs m a [C8 (wz v0); C8 (wz v1); C8 (wz v2); C8 (wz v3)].
Proof.
  intros m a v0 v1 v2 v3 U0 U1 U2 U3 Ha Hb. apply img_rw_cells; [| exact Ha| cbn; lia].
  split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold u64_at in *. rewrite Z.add_0_r in U0.
  apply bytes_at_app. split; [exact U0|]. rewrite length_le8.
  apply bytes_at_app. split; [exact U1|]. rewrite length_le8. replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) by lia.
  apply bytes_at_app. split; [exact U2|]. rewrite length_le8. replace (a + 16 + Z.of_nat 8) with (a + 24) by lia. exact U3.
Qed.

(* [comment removed for export] *)
Lemma fill_sub : forall (m : mem) a n v i k, fill_at rsegs m a n v -> 0 <= i -> 0 <= k -> i + k <= n ->
  fill_at rsegs m (a + i) k v.
Proof.
  (intros m a n v i k; (first [ intro dR_13; dand3 dR_13 as F0 F1 F | intros (F0 & F1 & F) ]); intros Hi Hk Hn). rewrite repeat_length in F1, F.
  split; [lia|]. split; [rewrite repeat_length; lia|]. intros j Hj. rewrite repeat_length in Hj.
  replace (a + i + Z.of_nat j) with (a + Z.of_nat (Z.to_nat i + j)) by lia.
  rewrite (F (Z.to_nat i + j)%nat) by lia. rewrite !nth_error_repeat by lia. reflexivity.
Qed.
Lemma u64s_repeat0 : forall n, u64s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (8 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat u64s]. rewrite IH.
  replace (8 * S n)%nat with (8 + 8 * n)%nat by lia. rewrite repeat_app. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma set_ia_freeA : forall A p qt qg c D ia b, set_ia (freeA A p qt qg c D ia) b = freeA A p qt qg c D b.
Proof. reflexivity. Qed.
Lemma xferA_freeA : forall A p qt qg c D ia, xferA (freeA A p qt qg c D ia) = freeA A p [] (qg ++ qt) c D ia.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hd_addr (sb : Z) (bs : list batch) : Z := match bs with [] => 0 | b :: _ => batch_addr sb b end.

Fixpoint breprN (m : mem) (sb : Z) (bs : list batch) (nx : Z) : Prop :=
  match bs with
  | [] => True
  | b :: bs' =>
      let a := batch_addr sb b in
      u64_at rsegs m (a + off_qb_next) (match bs' with [] => nx | b' :: _ => batch_addr sb b' end) /\
      u64_at rsegs m (a + off_qb_size) (batch_bytes b) /\
      u64_at rsegs m (a + off_qb_count) (Z.of_nat (length (ba_entries b))) /\
      (forall i e, nth_error (ba_entries b) i = Some e -> u64_at rsegs m (a + off_qb_batch (Z.of_nat i)) (hdr_of sb (qe_chunk e) (qe_n e))) /\
      mapped m a kQuarantineBatchBytes /\
      breprN m sb bs' nx
  end.

Lemma breprN_0 : forall (m : mem) sb bs, batches_repr LPA m sb bs <-> breprN m sb bs 0.
Proof.
  intros m sb bs. induction bs as [|b bs IH]; [cbn; tauto|].
  cbn [batches_repr breprN]. destruct bs as [|b' bs']; tauto.
Qed.

Lemma breprN_cat : forall (m : mem) sb bs1 bs2, breprN m sb bs1 (hd_addr sb bs2) -> batches_repr LPA m sb bs2 -> batches_repr LPA m sb (bs1 ++ bs2).
Proof.
  intros m sb bs1 bs2. induction bs1 as [|b bs1 IH]; intros H1 H2; [exact H2|].
  cbn [app batches_repr]. cbn [breprN] in H1. (first [ dand6 H1 as N S C E M R | destruct H1 as (N & S & C & E & M & R) ]).
  split; [| split; [exact S| split; [exact C| split; [exact E| split; [exact M| exact (IH R H2)]]]]].
  destruct bs1 as [|b1 bs1']; [| exact N]. cbn [app]. destruct bs2 as [|b2 bs2']; exact N.
Qed.

Lemma breprN_relink : forall (mm mm' : mem) sb l bl nx nx',
  breprN mm sb (l ++ [bl]) nx ->
  (forall x, In x l \/ x = bl -> forall i, (i < length (ba_entries x))%nat -> Z.of_nat i < 1021) ->
  (forall x a', In x l -> batch_addr sb x <= a' < batch_addr sb x + kQuarantineBatchBytes -> mm' (Z_to_bv 64 a') = mm (Z_to_bv 64 a')) ->
  (forall a', batch_addr sb bl + 8 <= a' < batch_addr sb bl + kQuarantineBatchBytes -> mm' (Z_to_bv 64 a') = mm (Z_to_bv 64 a')) ->
  u64_at rsegs mm' (batch_addr sb bl + off_qb_next) nx' ->
  mapped mm' (batch_addr sb bl) kQuarantineBatchBytes ->
  breprN mm' sb (l ++ [bl]) nx'.
Proof.
  intros mm mm' sb l. induction l as [|x l IH]; intros bl nx nx' H LEN AG AGL NX MB.
  - cbn [breprN app] in H |- *. (first [ dand6 H as Hn Hs Hc He Hm _ | destruct H as (Hn & Hs & Hc & He & Hm & _) ]).
    unfold off_qb_next, off_qb_size, off_qb_count, off_qb_batch, kQuarantineBatchBytes in *.
    split; [exact NX|]. split; [eapply u64_at_agree; [exact Hs|]; intros i Hi; apply AGL; lia|].
    split; [eapply u64_at_agree; [exact Hc|]; intros i Hi; apply AGL; lia|].
    split; [| split; [exact MB| exact I]].
    intros i e Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as IL. assert (Z.of_nat i < 1021) by (apply (LEN bl); [right; reflexivity| exact IL]).
    eapply u64_at_agree; [exact (He i e Hi)|]. intros j Hj. apply AGL. lia.
  - cbn [breprN app] in H |- *. (first [ dand6 H as Hn Hs Hc He Hm Hr | destruct H as (Hn & Hs & Hc & He & Hm & Hr) ]).
    assert (AGx : forall a', batch_addr sb x <= a' < batch_addr sb x + 8192 -> mm' (Z_to_bv 64 a') = mm (Z_to_bv 64 a'))
      by (intros a' Ha'; apply (AG x); [left; reflexivity| unfold kQuarantineBatchBytes; exact Ha']).
    unfold off_qb_next, off_qb_size, off_qb_count, off_qb_batch in *.
    split; [| split; [| split; [| split; [| split]]]].
    + destruct l as [|y l']; cbn [app] in Hn |- *; eapply u64_at_agree; [exact Hn| | exact Hn|]; intros i Hi; apply AGx; lia.
    + eapply u64_at_agree; [exact Hs|]. intros i Hi. apply AGx. lia.
    + eapply u64_at_agree; [exact Hc|]. intros i Hi. apply AGx. lia.
    + intros i e Hi. eapply u64_at_agree; [exact (He i e Hi)|]. intros j Hj.
      pose proof (nth_error_Some_lt _ _ _ Hi) as IL. assert (Z.of_nat i < 1021) by (apply (LEN x); [left; left; reflexivity| exact IL]).
      apply AGx. lia.
    + eapply mapped_agree_gen; [exact Hm|]. intros i Hi. apply AGx. unfold kQuarantineBatchBytes in Hi. lia.
    + apply (IH bl nx nx' Hr); [| | exact AGL| exact NX| exact MB].
      * intros y Hy. apply LEN. destruct Hy as [Hy| ->]; [left; right; exact Hy| right; reflexivity].
      * intros y a' Hy Ha'. apply (AG y); [right; exact Hy| exact Ha'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Kit.
  Context {Clg : Ceiling}.
  Variables (A : AState) (v : mem).
  Hypothesis AR : WF A /\ @arepr _ DepotRepL LPA AL_pasan [] A v.
  Local Notation qg := (a_qglobal A).
  Local Notation sb := (a_sb A).

  (* [comment removed for export] *)
  Lemma ia_pre_of : ia_pre (a_ia_inited A) v.
  Proof.
    pose proof (ar_ia _ _ _ _ _ (proj2 AR)) as [MAP1 IAx]. pose proof (ar_locks _ _ _ _ _ (proj2 AR)) as LK.
    pose proof (proj1 (ar_consts _ _ _ _ _ (proj2 AR))) as CF.
    change (al_internal_allocator_inst AL_pasan) with IAB in *. change (al_internal_alloc_inited AL_pasan) with 0x144e48 in *.
    unfold ia_pre. destruct (a_ia_inited A).
    - destruct IAx as [U _]. exact (u8_ro _ _ _ U).
    - destruct IAx as [U FL]. unfold ia_pre0.
      unfold locks_repr_ in LK. cbv zeta in LK. (first [ dand6 LK as _ _ _ _ _ LK | destruct LK as (_ & _ & _ & _ & _ & LK) ]).
      change (al_internal_alloc_inited AL_pasan + 1) with 0x144e49 in LK. rewrite lockb_nil in LK.
      pose proof (consts_cell v 0x144e4a [Z_to_bv 8 0; Z_to_bv 8 0] CF eq_refl) as PD.
      split.
      { apply img_rw_cells; [| lia| cbn; lia]. split; [cbn; tauto|]. cbn [cells_bytes cbytes app].
        change (le2 (wz 0)) with [Z_to_bv 8 0; Z_to_bv 8 0].
        apply (bytes_at_app _ v 0x144e48 [Z_to_bv 8 0] [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]). split; [exact U|].
        apply (bytes_at_app _ v _ [Z_to_bv 8 0] [Z_to_bv 8 0; Z_to_bv 8 0]). split; [exact LK| exact PD]. }
      unfold IAB in *.
      split. { apply img_rw_cells; [| lia| cbn; lia]. split; [cbn; tauto|]. cbn [cells_bytes cbytes app].
               pose proof (fill_sub v _ _ _ 0 1 FL ltac:(lia) ltac:(lia) ltac:(lia)) as X. unfold fill_at in X. rewrite Z.add_0_r in X. exact X. }
      split. { apply img_rw_CB; [| apply repeat_length| lia| lia]. exact (fill_sub v _ _ _ 8 262144 FL ltac:(lia) ltac:(lia) ltac:(lia)). }
      split. { split.
               - rewrite u64s_repeat0. pose proof (fill_sub v _ _ _ 0x40040 3456 FL ltac:(lia) ltac:(lia) ltac:(lia)) as X. unfold fill_at in X. exact X.
               - rewrite repeat_length. pose proof (fill_sub v _ _ _ 0x40040 3456 FL ltac:(lia) ltac:(lia) ltac:(lia)) as X. unfold fill_at in X.
                 pose proof (img_wr_at v _ _ X ltac:(lia) ltac:(rewrite repeat_length; lia)) as W. rewrite repeat_length in W. exact W. }
      split. { apply img_rw_CB; [| apply repeat_length| lia| lia]. exact (fill_sub v _ _ _ 0x40dc0 262728 FL ltac:(lia) ltac:(lia) ltac:(lia)). }
      apply img_rw_CB; [| apply repeat_length| lia| lia]. exact (fill_sub v _ _ _ 0x81008 40 FL ltac:(lia) ltac:(lia) ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma q_lockword : rw_cells rsegs v (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)].
  Proof.
    pose proof (ar_locks _ _ _ _ _ (proj2 AR)) as LK. pose proof (proj1 (ar_consts _ _ _ _ _ (proj2 AR))) as CF.
    unfold locks_repr_ in LK. cbv zeta in LK. (first [ dand6 LK as _ _ LKc LKr _ _ | destruct LK as (_ & _ & LKc & LKr & _ & _) ]).
    change (al_instance AL_pasan + off_q_cache_mutex) with 0xb20c8 in LKc. change (al_instance AL_pasan + off_q_recycle_mutex) with 0xb20c9 in LKr.
    rewrite lockb_nil in LKc, LKr.
    pose proof (consts_cell v 0xb20ca [Z_to_bv 8 0; Z_to_bv 8 0] CF eq_refl) as PD.
    change (QINST + 152) with 0xb20c8.
    apply img_rw_cells; [| lia| cbn; lia]. split; [cbn; tauto|]. cbn [cells_bytes cbytes app].
    change (le2 (wz 0)) with [Z_to_bv 8 0; Z_to_bv 8 0].
    apply (bytes_at_app _ v 0xb20c8 [Z_to_bv 8 0] [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]). split; [exact LKc|].
    apply (bytes_at_app _ v _ [Z_to_bv 8 0] [Z_to_bv 8 0; Z_to_bv 8 0]). split; [exact LKr| exact PD].
  Qed.

  (* [comment removed for export] *)
  Lemma q_global_hdr : rw_cells rsegs v (QINST + 160)
    [C8 (wz (Z.of_nat (length qg))); C8 (wz (qc_first A qg)); C8 (wz (qc_last A qg)); C8 (wz (q_bytes qg))].
  Proof.
    (first [ pose proof ((ar_quar _ _ _ _ _ (proj2 AR))) as dR_6; dand3 dR_6 as _ QG _ | pose proof (ar_quar _ _ _ _ _ (proj2 AR)) as (_ & QG & _) ]). (first [ dand5 QG as X1 X2 X3 X4 _ | destruct QG as (X1 & X2 & X3 & X4 & _) ]).
    change (al_instance AL_pasan + off_q_cache_list_size) with (QINST + 160) in X1, X2, X3, X4. change (p_sb (a_pl A)) with sb in X2, X3.
    apply img_rw_C8x4; [exact X1| | | exact X4| unfold QINST; lia| unfold QINST; lia].
    - unfold qc_first. destruct qg; exact X2.
    - unfold qc_last. destruct qg; exact X3.
  Qed.

  (* [comment removed for export] *)
  Lemma q_gl_cell : qg <> [] ->
    rw_cells rsegs v (qc_last A qg) [C8 (wz 0)] /\
    qc_last A qg = batch_addr sb (last qg (BA 0 [])) /\ In (last qg (BA 0 [])) (a_qthread A ++ qg) /\
    kHighMemBeg <= qc_last A qg /\ qc_last A qg + kQuarantineBatchBytes <= alloc_ceiling.
  Proof.
    intros NE. (first [ pose proof ((ar_quar _ _ _ _ _ (proj2 AR))) as dR_8; dand3 dR_8 as _ QG _ | pose proof (ar_quar _ _ _ _ _ (proj2 AR)) as (_ & QG & _) ]). (first [ dand5 QG as _ _ _ _ BR | destruct QG as (_ & _ & _ & _ & BR) ]). change (p_sb (a_pl A)) with sb in BR.
    assert (QL : qc_last A qg = batch_addr sb (last qg (BA 0 []))) by (unfold qc_last; destruct (a_qglobal A); [congruence| reflexivity]).
    assert (INl : In (last qg (BA 0 [])) (a_qthread A ++ qg)).
    { apply in_or_app. right. pattern qg at 2. rewrite <- (removelast_last_app qg (BA 0 []) NE). cbv beta. apply in_or_app. right. left. reflexivity. }
    (first [ pose proof ((batch_range A v AR _ INl)) as dR_10; dand3 dR_10 as R1 R2 _ | pose proof (batch_range A v AR _ INl) as (R1 & R2 & _) ]).
    rewrite QL. split; [| split; [reflexivity| split; [exact INl| split; [exact R1| exact R2]]]].
    pose proof (batches_repr_last _ _ (removelast qg) (last qg (BA 0 [])) ltac:(rewrite (removelast_last_app qg (BA 0 []) NE); exact BR)) as L.
    cbv zeta in L. (first [ dand5 L as Ln _ _ _ Lm | destruct L as (Ln & _ & _ & _ & Lm) ]). unfold off_qb_next in Ln. rewrite Z.add_0_r in Ln.
    apply (ro_rw _ _ _ (u64_ro _ _ _ Ln)). cbn [cells_size csize Nat.add]. intros i Hi. apply Lm. unfold kQuarantineBatchBytes. lia.
  Qed.
End Kit.

(* [comment removed for export] *)
Lemma rw_CB_bytes : forall (m : mem) a n bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof. intros m a n bs [[W B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.
Lemma rw_C8C8_u64 : forall (m : mem) a x y cs, rw_cells rsegs m a (C8 (wz x) :: C8 (wz y) :: cs) -> u64_at rsegs m a x /\ u64_at rsegs m (a + 8) y.
Proof.
  intros m a x y cs [[W B] _]. cbn [cells_bytes cbytes] in B.
  apply bytes_at_app in B as [B1 B]. apply bytes_at_app in B as [B2 _]. rewrite length_le8 in B2.
  split; [exact B1| exact B2].
Qed.

(* [comment removed for export] *)
Lemma ia_post0_facts : forall (v' : mem), ia_post0 v' ->
  ia_repr_ LPA AL_pasan true v' /\ u8_at rsegs v' 0x144e49 0 /\ bytes_at rsegs v' 0x144e4a [Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
  (intros v'; (first [ intro dR_14; dand6 dR_14 as P1 P2 P3 P4 P5 P6 | intros (P1 & P2 & P3 & P4 & P5 & P6) ])). unfold IAB in *.
  destruct P1 as [[_ B1] _]. cbn [cells_bytes cbytes app] in B1. change (le2 (wz 0)) with [Z_to_bv 8 0; Z_to_bv 8 0] in B1.
  apply (bytes_at_app _ v' 0x144e48 [Z_to_bv 8 1] [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) in B1 as [U1 B1].
  apply (bytes_at_app _ v' _ [Z_to_bv 8 0] [Z_to_bv 8 0; Z_to_bv 8 0]) in B1 as [L1 PD]. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in L1, PD.
  split; [| split; [exact L1| exact PD]].
  unfold ia_repr_. change (al_internal_allocator_inst AL_pasan) with 0xb65c0. change (al_internal_alloc_inited AL_pasan) with 0x144e48.
  split.
  - intros i Hi. unfold kDepotNodesL1 in Hi. apply rw_CB_bytes in P3.
    exact (fill_sub v' (0xb65c0 + 8) 262144 0 (8 * i) 8 P3 ltac:(lia) ltac:(lia) ltac:(lia)).
  - split; [exact U1|]. apply rw_C8C8_u64 in P5. exact P5.
Qed.
