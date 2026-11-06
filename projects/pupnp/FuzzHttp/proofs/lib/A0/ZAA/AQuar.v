(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim APrimLem APrimPop APrimQ ASec.
Import ListNotations.
Open Scope Z_scope.

Notation QUAR := 722288%Z.
Notation QUAR_CONST := 722352%Z.
Notation QUAR_MTX := 722440%Z.
Notation QUAR_GQ := 722448%Z.
Notation TQ_OFF := 80%Z.
Notation Q_MAX := 268435456%Z.
Notation Q_MIN := 241591905%Z.
Notation Q_CACHE := 1048576%Z.
Notation Q_BATCH := 1021%Z.
Notation Q_BBYTES := 8192%Z.
Notation K_BCLASS := 24%Z.
Notation AF_MAXFILL := 725288%Z.
Notation CHUNK_MAGIC := 14730877155918386873%Z.

Inductive qkind := QPrim (c v : Z) | QSec (sc : schunk).
Record qchunk := mkQC { qc_kind : qkind; qc_rz : Z; qc_n : Z }.
Record qbatch := mkQB { qb_v : Z; qb_size : Z; qb_chunks : list qchunk }.
Record aquar := mkAQ { q_loc : list qbatch; q_glob : list qbatch }.

Definition qb_count (b : qbatch) : Z := Z.of_nat (length (qb_chunks b)).
Definition qbytes (l : list qbatch) : Z := fold_right (fun b acc => qb_size b + acc) 0 l.

Definition need_batch (l : list qbatch) : bool :=
  match rev l with [] => true | b :: _ => qb_count b =? Q_BATCH end.
Definition q_enq (l : list qbatch) (ch : qchunk) (v : Z) : list qbatch :=
  match rev l with
  | [] => [mkQB v (qc_n ch + Q_BBYTES) [ch]]
  | b :: r => if qb_count b =? Q_BATCH then l ++ [mkQB v (qc_n ch + Q_BBYTES) [ch]]
              else rev r ++ [mkQB (qb_v b) (qb_size b + qc_n ch) (qb_chunks b ++ [ch])]
  end.

Fixpoint q_merge (cur : qbatch) (rest : list qbatch) {struct rest} : list qbatch * list qbatch :=
  match rest with
  | [] => ([cur], [])
  | nx :: rest' =>
      if qb_count cur + qb_count nx <=? Q_BATCH then
        let cur' := mkQB (qb_v cur) (qb_size cur + qb_size nx - Q_BBYTES) (qb_chunks cur ++ qb_chunks nx) in
        let '(l, ex) := q_merge cur' rest' in (l, mkQB (qb_v nx) Q_BBYTES [] :: ex)
      else let '(l, ex) := q_merge nx rest' in (cur :: l, ex)
  end.
Definition q_merge_list (l : list qbatch) : list qbatch * list qbatch :=
  match l with [] => ([], []) | b :: rest => q_merge b rest end.

Fixpoint q_dequeue (l : list qbatch) (bytes min_size : Z) {struct l} : list qbatch * list qbatch :=
  match l with
  | [] => ([], [])
  | b :: l' => if min_size <? bytes
               then let '(taken, rest) := q_dequeue l' (bytes - qb_size b) min_size in (b :: taken, rest)
               else ([], l)
  end.

Definition q_recycle_sel (gl : list qbatch) : list qbatch * list qbatch :=
  let bytes := qbytes gl in
  let ovh := Q_BBYTES * Z.of_nat (length gl) in
  let '(gl1, ex) := if (ovh <? bytes) && (bytes * 100 <? ovh * 200) then q_merge_list gl else (gl, []) in
  let '(taken, rest) := q_dequeue gl1 (qbytes gl1) Q_MIN in
  (rest, ex ++ taken).

Definition q_transfer (Q : aquar) : aquar := mkAQ [] (q_glob Q ++ q_loc Q).
Definition q_drain_sel (Q : aquar) : aquar * list qbatch :=
  let Q1 := q_transfer Q in
  if Q_MAX <? qbytes (q_glob Q1) then let '(rest, todo) := q_recycle_sel (q_glob Q1) in (mkAQ [] rest, todo) else (Q1, []).

Section R.
Context {HC : HasCeiling}.
Variable AL : alayout.
Notation THR := (at_thr (al_thread AL)).
Notation TQ := (at_thr (al_thread AL) + TQ_OFF).

Definition fa_bytes (n : Z) : list byte := repeat (Z_to_bv 8 250) (Z.to_nat n).
Definition fd_bytes (n : Z) : list byte := repeat (Z_to_bv 8 253) (Z.to_nat n).
Definition rup8 (n : Z) : Z := ((n + 7) / 8) * 8.

Definition qc_blk (ch : qchunk) : Z :=
  match qc_kind ch with QPrim c v => region AL c + 16 * v | QSec sc => sc_beg sc + 4096 end.
Definition qc_bsize (ch : qchunk) : Z :=
  match qc_kind ch with QPrim c v => class_size c | QSec sc => sc_msize sc - 4096 end.
Definition qc_hdr (ch : qchunk) : Z := qc_blk ch + qc_rz ch - 16.

Definition qchunk_wf (ch : qchunk) : Prop :=
  16 <= qc_rz ch /\ qc_rz ch mod 16 = 0 /\ 1 <= qc_n ch <= Q_MAX /\ qc_rz ch + rup8 (qc_n ch) <= qc_bsize ch
  /\ match qc_kind ch with QPrim c v => 1 <= c <= 31 /\ 0 <= v /\ (16 * v) mod class_size c = 0 | QSec sc => True end.

Definition qchunk_rep (m : mem) (ch : qchunk) : Prop :=
  let B := qc_blk ch in let M := qc_hdr ch in let n := qc_n ch in let rz := qc_rz ch in
  (exists bits actx, rw_cells asegs m M [CB 4 [Z_to_bv 8 3; bits; Z_to_bv 8 0; Z_to_bv 8 0]; C4 (wz n); C8 actx])
  /\ (16 < rz -> rw_cells asegs m B [C8 (wz CHUNK_MAGIC); C8 (wz M)] /\ exists j, rw_cells asegs m (B + 16) [CB (Z.to_nat (rz - 32)) j])
  /\ (exists j, rw_cells asegs m (M + 16) [CB (Z.to_nat (qc_bsize ch - rz)) j])
  /\ rw_cells asegs m (sh B) [CB (Z.to_nat (rz / 8)) (fa_bytes (rz / 8))]
  /\ rw_cells asegs m (sh (M + 16)) [CB (Z.to_nat (rup8 n / 8)) (fd_bytes (rup8 n / 8))]
  /\ rw_cells asegs m (sh (M + 16 + rup8 n)) [CB (Z.to_nat ((qc_bsize ch - rz - rup8 n) / 8)) (fa_bytes ((qc_bsize ch - rz - rup8 n) / 8))]
  /\ match qc_kind ch with
     | QPrim _ _ => True
     | QSec sc => (exists j, rw_cells asegs m (sc_beg sc + 32) [CB 4064 j]) /\ rw_cells asegs m (sh (sc_beg sc)) [CB 512 (fa_bytes 512)]
     end.

Definition qb_addr (b : qbatch) : Z := region AL K_BCLASS + 16 * qb_v b.
Definition qbatch_rep (m : mem) (b : qbatch) (nx : Z) : Prop :=
  rw_cells asegs m (qb_addr b) [C8 (wz nx); C8 (wz (qb_size b)); C8 (wz (qb_count b))]
  /\ (exists ws, u64arr asegs m (qb_addr b + 24) ws /\ length ws = 1021%nat
                 /\ firstn (length (qb_chunks b)) ws = map (fun ch => wz (qc_hdr ch)) (qb_chunks b))
  /\ rw_cells asegs m (sh (qb_addr b)) [CB 1024 (fa_bytes 1024)].

Definition qfirst (l : list qbatch) : Z := match l with [] => 0 | b :: _ => qb_addr b end.
Definition qlast (l : list qbatch) : Z := match rev l with [] => 0 | b :: _ => qb_addr b end.

Fixpoint qlist_rep (m : mem) (l : list qbatch) (nxt : Z) {struct l} : Prop :=
  match l with
  | [] => True
  | b :: l' => qbatch_rep m b (match l' with [] => nxt | b' :: _ => qb_addr b' end) /\ qlist_rep m l' nxt
  end.

Definition qcache_rep (m : mem) (C : Z) (l : list qbatch) : Prop :=
  rw_cells asegs m C [C8 (wz (Z.of_nat (length l))); C8 (wz (qfirst l)); C8 (wz (qlast l)); C8 (wz (qbytes l))]
  /\ qlist_rep m l 0.

Definition quar_env (m : mem) : Prop :=
  rw_cells asegs m QUAR_CONST [C8 (wz Q_MAX); C8 (wz Q_MIN); C8 (wz Q_CACHE)]
  /\ rw_cells asegs m AF_MAXFILL [C4 (wz 0)].

Definition qbatch_wf (b : qbatch) : Prop :=
  0 <= qb_v b /\ (16 * qb_v b) mod Q_BBYTES = 0 /\ 1 <= qb_count b <= Q_BATCH
  /\ qb_size b = Q_BBYTES + fold_right (fun ch acc => qc_n ch + acc) 0 (qb_chunks b)
  /\ Forall qchunk_wf (qb_chunks b).

Definition quar_wf (Q : aquar) : Prop :=
  Forall qbatch_wf (q_loc Q ++ q_glob Q) /\ qbytes (q_loc Q) <= Q_CACHE /\ qbytes (q_glob Q) <= Q_MAX.

Definition q_all_chunks (Q : aquar) : list qchunk := flat_map qb_chunks (q_loc Q ++ q_glob Q).

Definition RQUAR (Q : aquar) (m : mem) : Prop :=
  quar_wf Q /\ quar_env m
  /\ rw_cells asegs m QUAR_MTX [CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]
  /\ qcache_rep m TQ (q_loc Q) /\ qcache_rep m QUAR_GQ (q_glob Q)
  /\ Forall (qchunk_rep m) (q_all_chunks Q).
End R.

Lemma need_batch_nil : need_batch [] = true. Proof. reflexivity. Qed.
Lemma need_batch_snoc : forall l b, need_batch (l ++ [b]) = (qb_count b =? Q_BATCH).
Proof. intros. unfold need_batch. rewrite rev_app_distr. reflexivity. Qed.
Lemma q_enq_nil : forall ch v, q_enq [] ch v = [mkQB v (qc_n ch + Q_BBYTES) [ch]]. Proof. reflexivity. Qed.
Lemma q_enq_snoc : forall l b ch v,
  q_enq (l ++ [b]) ch v = if qb_count b =? Q_BATCH then (l ++ [b]) ++ [mkQB v (qc_n ch + Q_BBYTES) [ch]]
                          else l ++ [mkQB (qb_v b) (qb_size b + qc_n ch) (qb_chunks b ++ [ch])].
Proof. intros. unfold q_enq. rewrite rev_app_distr. cbn [rev app]. rewrite rev_involutive. reflexivity. Qed.

Lemma qbytes_app : forall l1 l2, qbytes (l1 ++ l2) = qbytes l1 + qbytes l2.
Proof. induction l1 as [|b l IH]; intros l2; unfold qbytes in *; cbn [fold_right app]; [reflexivity|]. rewrite IH. lia. Qed.

Lemma qbytes_nonneg : forall l, Forall (fun b => 0 <= qb_size b) l -> 0 <= qbytes l.
Proof. induction 1 as [|b l Hb Hl IH]; unfold qbytes in *; cbn [fold_right]; lia. Qed.

Section L.
Context {HC : HasCeiling}.
Variable AL : alayout.

#[using="Type"] Lemma qlast_snoc : forall l b, qlast AL (l ++ [b]) = qb_addr AL b.
Proof. intros. unfold qlast. rewrite rev_app_distr. reflexivity. Qed.
#[using="Type"] Lemma qfirst_app : forall l1 l2, l1 <> [] -> qfirst AL (l1 ++ l2) = qfirst AL l1.
Proof. intros [|b l1] l2 NE; [contradiction| reflexivity]. Qed.

#[using="Type"] Lemma qlist_rep_snoc : forall m l b nxt,
  qlist_rep AL m (l ++ [b]) nxt <-> qlist_rep AL m l (qb_addr AL b) /\ qbatch_rep AL m b nxt.
Proof.
  intros m l b nxt. induction l as [|a l IH]; cbn [qlist_rep app].
  - tauto.
  - rewrite IH. destruct l as [|a' l']; cbn [app]; tauto.
Qed.

#[using="Type"] Lemma qlist_rep_app : forall m l1 l2 nxt,
  qlist_rep AL m (l1 ++ l2) nxt <-> qlist_rep AL m l1 (match l2 with [] => nxt | b :: _ => qb_addr AL b end) /\ qlist_rep AL m l2 nxt.
Proof.
  intros m l1 l2 nxt. induction l1 as [|a l IH]; cbn [qlist_rep app].
  - tauto.
  - rewrite IH. destruct l as [|a' l']; cbn [app]; [destruct l2; tauto| tauto].
Qed.

#[using="Type"] Lemma qbatch_rep_frame : forall W m m' b nx,
  qbatch_rep AL m b nx -> munch W m m' -> wmono asegs m m' ->
  0 <= qb_addr AL b -> disjoint_from W (qb_addr AL b) Q_BBYTES -> disjoint_from W (sh (qb_addr AL b)) 1024 -> qbatch_rep AL m' b nx.
Proof.
  intros W m m' b nx (HC3 & (ws & AR & LW & FW) & SHD) MU WM A0 D1 D2. split; [| split].
  - eapply rw_cells_transport; [exact HC3| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D1| cbn; lia| cbn; lia].
  - exists ws. split; [| split; assumption]. eapply u64arr_transport; [exact AR| exact MU| exact WM|].
    eapply disjoint_from_sub; [exact D1| lia| rewrite LW; lia].
  - eapply rw_cells_transport; [exact SHD| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D2| cbn; lia| cbn; lia].
Qed.

#[using="Type"] Lemma qlist_rep_frame : forall W m m' l nxt,
  qlist_rep AL m l nxt -> munch W m m' -> wmono asegs m m' ->
  Forall (fun b => 0 <= qb_addr AL b /\ disjoint_from W (qb_addr AL b) Q_BBYTES /\ disjoint_from W (sh (qb_addr AL b)) 1024) l ->
  qlist_rep AL m' l nxt.
Proof.
  intros W m m' l nxt R MU WM Fd. revert R. induction Fd as [|b l (A0 & D1 & D2) Fd IH]; cbn [qlist_rep]; [tauto|].
  intros [RB RL]. split; [eapply qbatch_rep_frame; eassumption| exact (IH RL)].
Qed.

Definition space_out (iv : Z * Z) : Prop :=
  (snd iv <= al_space AL \/ al_space AL + K_SPACE <= fst iv)
  /\ (snd iv <= sh (al_space AL) \/ sh (al_space AL + K_SPACE) <= fst iv).
Definition in_bchunk (v : Z) (iv : Z * Z) : Prop :=
  (region AL K_BCLASS + 16 * v <= fst iv /\ snd iv <= region AL K_BCLASS + 16 * v + Q_BBYTES)
  \/ (sh (region AL K_BCLASS + 16 * v) <= fst iv /\ snd iv <= sh (region AL K_BCLASS + 16 * v) + 1024).
Definition above_b (bound : Z) (iv : Z * Z) : Prop :=
  region AL K_BCLASS + bound <= fst iv \/ (sh (region AL K_BCLASS + bound) <= fst iv /\ snd iv <= 17594333495296).
Definition qclear (vs : list Z) (bound : Z) (W : list (Z * Z)) : Prop :=
  Forall (fun iv => space_out iv
                    \/ (exists v, ~ In v vs /\ 0 <= v /\ (16 * v) mod Q_BBYTES = 0 /\ 16 * v + Q_BBYTES <= FA_OFF /\ in_bchunk v iv)
                    \/ above_b bound iv) W.

Definition qb_in (bound : Z) (b : qbatch) : Prop := 0 <= qb_v b /\ (16 * qb_v b) mod Q_BBYTES = 0 /\ 16 * qb_v b + Q_BBYTES <= bound.

#[using="Type"] Lemma qclear_disjoint : forall vs bound W b, alayout_ok AL -> bound <= FA_OFF -> bound mod 8 = 0 ->
  qclear vs bound W -> qb_in bound b -> In (qb_v b) vs ->
  0 <= qb_addr AL b /\ disjoint_from W (qb_addr AL b) Q_BBYTES /\ disjoint_from W (sh (qb_addr AL b)) 1024.
Proof.
  intros vs bound W b AO BF B8 QCL (V0 & VA & VB) VIN. assert (VF : 16 * qb_v b + Q_BBYTES <= FA_OFF) by lia.
  layout_facts AO 0%nat RF0. destruct RF0 as (S1 & S2 & SM & _ & S5 & _ & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (RG : region AL K_BCLASS = al_space AL + 24 * K_REGION) by reflexivity.
  unfold qb_addr. set (A := region AL K_BCLASS + 16 * qb_v b) in *.
  pose proof SM as SM'. apply Z.mod_divide in SM'; [| lia]. destruct SM' as [y Hy].
  assert (AR : al_space AL + K_REGION <= A /\ A + Q_BBYTES <= al_space AL + K_SPACE /\ A mod 8 = 0).
  { subst A. rewrite RG. split; [lia|]. split; [lia|].
    apply Z.mod_divide in VA; [| lia]. destruct VA as [z Hz]. rewrite Hz, Hy.
    replace (y * 4096 + 24 * K_REGION + z * Q_BBYTES) with ((y * 512 + 24 * 536870912 + z * 1024) * 8) by lia. apply Z_mod_mult. }
  destruct AR as (A1 & A2 & A8).
  assert (SHA : sh (al_space AL) <= sh A /\ sh A + 1024 <= sh (al_space AL + K_SPACE) /\ sh A + 1024 <= 17594333495296 /\ 2147450880 <= sh A).
  { unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia. }
  split; [lia|].
  induction QCL as [|[lo' hi'] W [SO|[(v & NIN & W0 & WA & WF & IB)|AB]] _ IH]; cbn [disjoint_from]; [tauto| | |].
  - destruct SO as [SO1 SO2]. cbn [fst snd] in *. destruct IH as [I1 I2]. split; (split; [lia| assumption]).
  - destruct IH as [I1 I2]. cbn [fst snd] in *.
    assert (NE : v <> qb_v b) by (intros ->; exact (NIN VIN)).
    pose proof (chunks_apart K_BCLASS v (qb_v b) ltac:(lia) WA VA NE) as AP. change (class_size K_BCLASS) with Q_BBYTES in AP.
    set (A' := region AL K_BCLASS + 16 * v) in *.
    assert (A'8 : A' mod 8 = 0 /\ al_space AL + K_REGION <= A' /\ A' + Q_BBYTES <= al_space AL + K_SPACE).
    { subst A'. rewrite RG. split; [| lia].
      apply Z.mod_divide in WA; [| lia]. destruct WA as [z Hz]. rewrite Hz, Hy.
      replace (y * 4096 + 24 * K_REGION + z * Q_BBYTES) with ((y * 512 + 24 * 536870912 + z * 1024) * 8) by lia. apply Z_mod_mult. }
    destruct A'8 as (A'8 & A'1 & A'2).
    assert (SHA' : 2147450880 <= sh A' /\ sh A' + 1024 <= 17594333495296
                   /\ (A' + Q_BBYTES <= A -> sh A' + 1024 <= sh A) /\ (A + Q_BBYTES <= A' -> sh A + 1024 <= sh A')).
    { unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia. }
    assert (APA : A' + Q_BBYTES <= A \/ A + Q_BBYTES <= A') by (subst A A'; lia).
    unfold in_bchunk in IB. cbn [fst snd] in IB. fold A' in IB.
    destruct IB as [[B1 B2]|[B1 B2]]; (split; (split; [lia| assumption])).
  - destruct IH as [I1 I2]. unfold above_b in AB. cbn [fst snd] in AB.
    set (X := region AL K_BCLASS + bound) in *.
    assert (XF : A + Q_BBYTES <= X /\ sh A + 1024 <= sh X).
    { assert (X8 : X mod 8 = 0).
      { subst X. rewrite RG, Hy. apply Z.mod_divide in B8; [| lia]. destruct B8 as [z Hz]. rewrite Hz.
        replace (y * 4096 + 24 * K_REGION + z * 8) with ((y * 512 + 24 * 536870912 + z) * 8) by lia. apply Z_mod_mult. }
      assert (A + Q_BBYTES <= X) by (subst A X; lia). split; [assumption|].
      unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia. }
    destruct AB as [AB|[AB1 AB2]]; (split; (split; [lia| assumption])).
Qed.

#[using="Type"] Lemma qlist_rep_frame_clear : forall W bound m m' l nxt, alayout_ok AL -> bound <= FA_OFF -> bound mod 8 = 0 ->
  qlist_rep AL m l nxt -> munch W m m' -> wmono asegs m m' -> Forall (qb_in bound) l -> qclear (map qb_v l) bound W -> qlist_rep AL m' l nxt.
Proof.
  intros W bound m m' l nxt AO BF B8 R MU WM FI QCL. eapply qlist_rep_frame; [exact R| exact MU| exact WM|].
  apply Forall_forall. intros b Hb. apply (qclear_disjoint (map qb_v l) bound W b AO BF B8 QCL).
  - exact (proj1 (Forall_forall _ _) FI b Hb).
  - apply in_map. exact Hb.
Qed.

#[using="Type"] Lemma firstn_upd_snocQ {X} : forall (ws : list X) (k : nat) (v : X) (l0 : list X),
  firstn k ws = l0 -> (k < length ws)%nat -> firstn (Datatypes.S k) (upd ws k v) = l0 ++ [v].
Proof.
  intros ws k v l0 Hf Hk. rewrite (upd_firstn_skipn ws k v Hk).
  rewrite firstn_app. rewrite firstn_all2 by (rewrite length_firstn; lia).
  rewrite length_firstn. replace (Datatypes.S k - Nat.min k (length ws))%nat with 1%nat by lia. cbn. rewrite Hf. reflexivity.
Qed.
End L.

