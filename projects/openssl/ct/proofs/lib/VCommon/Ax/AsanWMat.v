(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSMat.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_mem_In (p : word) (l : list word) : page_mem p l = true <-> In p l.
Proof.
  unfold page_mem. rewrite existsb_exists. split.
  - intros [x [Hx E]]. unfold bv_eqb in E. apply Z.eqb_eq in E. assert (p = x) by (apply bv_eq; exact E). subst. exact Hx.
  - intros H. exists p. split; [exact H|]. unfold bv_eqb. apply Z.eqb_refl.
Qed.

Lemma access_pages_acc_spec (n : nat) : forall (base : Z) (pages : list word) (p : word),
  In p (access_pages_acc base n pages) <-> In p pages \/ exists z, base <= z < base + Z.of_nat n /\ p = page_base_of z.
Proof.
  induction n as [|n IH]; intros base pages p; cbn [access_pages_acc].
  - split; [tauto|]. intros [H|[z [Hz _]]]; [exact H | lia].
  - rewrite IH. unfold page_insert. destruct (page_mem (page_base_of base) pages) eqn:E.
    + apply page_mem_In in E. split.
      * intros [H|[z [Hz ->]]]; [left; exact H | right; exists z; split; [lia | reflexivity]].
      * intros [H|[z [Hz ->]]]; [left; exact H|].
        destruct (Z.eq_dec z base) as [->|N]; [left; exact E | right; exists z; split; [lia | reflexivity]].
    + split.
      * intros [[<-|H]|[z [Hz ->]]]; [right; exists base; split; [lia | reflexivity] | left; exact H | right; exists z; split; [lia | reflexivity]].
      * intros [H|[z [Hz ->]]]; [left; right; exact H|].
        destruct (Z.eq_dec z base) as [->|N]; [left; left; reflexivity | right; exists z; split; [lia | reflexivity]].
Qed.

Lemma access_pages_acc_nodup (n : nat) : forall (base : Z) (pages : list word), List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof.
  induction n as [|n IH]; intros base pages H; cbn [access_pages_acc]; [exact H|]. apply IH.
  unfold page_insert. destruct (page_mem (page_base_of base) pages) eqn:E; [exact H|].
  apply List.NoDup_cons; [|exact H]. intros X. apply (proj2 (page_mem_In _ _)) in X. rewrite X in E. discriminate.
Qed.

Definition range_pages (lo : Z) (n : nat) : list word := access_pages_acc lo n [].

Lemma range_pages_incl (a : word) (c : nat) (lo : Z) (n : nat) :
  lo <= bv_unsigned a -> bv_unsigned a + Z.of_nat c <= lo + Z.of_nat n -> incl (access_pages a c) (range_pages lo n).
Proof.
  intros H1 H2 p Hp. unfold access_pages, range_pages in *. apply access_pages_acc_spec in Hp as [[]|[z [Hz ->]]].
  apply access_pages_acc_spec. right. exists z. split; [lia | reflexivity].
Qed.

Lemma range_pages_length (lo : Z) (n : nat) : 0 <= lo -> lo + Z.of_nat n <= 2 ^ 60 ->
  Z.of_nat (length (range_pages lo n)) <= Z.of_nat n / 4096 + 2.
Proof.
  intros Hlo Hhi. destruct n as [|n'].
  { cbn. pose proof (Z.div_pos 0 4096). lia. }
  set (N := Z.of_nat (S n')).
  set (b0 := lo / 4096). set (cnt := (lo + N - 1) / 4096 - b0 + 1).
  assert (Hcnt : 0 <= cnt).
  { unfold cnt, b0. pose proof (Z.div_le_mono lo (lo + N - 1) 4096 ltac:(lia) ltac:(unfold N; lia)). lia. }
  set (E := map (fun j : nat => Z_to_bv 64 ((b0 + Z.of_nat j) * 4096)) (seq 0 (Z.to_nat cnt))).
  assert (Hinc : incl (range_pages lo (S n')) E).
  { intros p Hp. unfold range_pages in Hp. apply access_pages_acc_spec in Hp as [[]|[z [Hz ->]]].
    unfold E. apply in_map_iff. exists (Z.to_nat (z / 4096 - b0)). split.
    - unfold page_base_of, page_size. f_equal. rewrite Z2Nat.id; [ring|].
      unfold b0. pose proof (Z.div_le_mono lo z 4096 ltac:(lia) ltac:(lia)). lia.
    - apply in_seq. unfold cnt, b0. fold N in Hz.
      pose proof (Z.div_le_mono lo z 4096 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_mono z (lo + N - 1) 4096 ltac:(lia) ltac:(lia)). lia. }
  pose proof (List.NoDup_incl_length (access_pages_acc_nodup (S n') lo [] (List.NoDup_nil _)) Hinc) as Hl.
  unfold E in Hl. rewrite length_map, length_seq in Hl.
  assert (cnt <= N / 4096 + 2).
  { unfold cnt, b0. pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
    pose proof (Z.div_mod (lo + N - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (lo + N - 1) 4096 ltac:(lia)).
    pose proof (Z.div_mod N 4096 ltac:(lia)). pose proof (Z.mod_pos_bound N 4096 ltac:(lia)). lia. }
  unfold range_pages in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition matin (m0 m : Model) (L : list word) : Prop :=
  exists Q, m = with_vm_backing (m_vm_lazy m0) (Q ++ m_vm_materialized m0) m0 /\ List.NoDup Q /\ incl Q L /\
            (forall p, In p Q -> ~ In p (m_vm_materialized m0)).

Lemma matin_refl (m0 : Model) (L : list word) : matin m0 m0 L.
Proof.
  exists []. split; [rewrite app_nil_l; symmetry; apply with_vm_backing_id|]. split; [apply List.NoDup_nil|]. split; [intros p []|]. intros p [].
Qed.

Lemma matin_halted (m0 m : Model) (L : list word) : matin m0 m L -> m_halted m = m_halted m0.
Proof. intros [Q [-> _]]. destruct m0 as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma matin_lazy (m0 m : Model) (L : list word) : matin m0 m L -> m_vm_lazy m = m_vm_lazy m0.
Proof. intros [Q [-> _]]. apply with_lazy. Qed.

Lemma matin_maps (m0 m : Model) (L : list word) : matin m0 m L -> m_vmmaps m = m_vmmaps m0.
Proof. intros [Q [-> _]]. apply with_maps. Qed.

Lemma used_with0 (m0 : Model) (P : list word) :
  vm_backing_used (with_vm_backing (m_vm_lazy m0) P m0) = vm_backing_used m0 + (Z.of_nat (length P) - Z.of_nat (length (m_vm_materialized m0))) * page_size.
Proof.
  rewrite vm_used_with. unfold vm_backing_used. lia.
Qed.

Lemma matin_used (m0 m : Model) (L : list word) : matin m0 m L ->
  exists Q, vm_backing_used m = vm_backing_used m0 + Z.of_nat (length Q) * page_size /\ List.NoDup Q /\ incl Q L.
Proof.
  intros [Q [-> [HN [HI _]]]]. exists Q. split; [|split; assumption].
  rewrite used_with0. rewrite length_app. lia.
Qed.

Lemma matin_mat_of (m0 m : Model) (L : list word) : matin m0 m L -> mat_of m0 m (Z.of_nat (length L)).
Proof.
  intros H. pose proof H as [Q [E _]]. split; [exists (Q ++ m_vm_materialized m0); exact E|].
  destruct (matin_used m0 m L H) as [Q' [U [HN HI]]]. pose proof (List.NoDup_incl_length HN HI). unfold page_size in U. lia.
Qed.

Lemma mat_step_in (m0 m : Model) (L : list word) (a : word) (c : nat) :
  matin m0 m L -> incl (access_pages a c) L ->
  vm_backing_used m0 + Z.of_nat (length L) * page_size <= vm_limit (m_vmmaps m0) ->
  exists m', materialize_model_accesses m [(a, c)] = Some m' /\ matin m0 m' L.
Proof.
  intros Hm HL Hb. pose proof Hm as [Q [Em [HN [HI HD]]]].
  unfold materialize_model_accesses, materialize_accesses, newly_materialized_pages. cbn [accesses_pages].
  fold (access_pages a c).
  rewrite Em, with_lazy, with_matd, with_maps.
  set (P0 := m_vm_materialized m0) in *. set (lz := m_vm_lazy m0) in *.
  set (new := List.filter (fun p => page_in_ranges p lz && negb (page_mem p (Q ++ P0))) (access_pages a c)).
  assert (Hnew : List.NoDup (new ++ Q) /\ incl (new ++ Q) L /\ (forall p, In p (new ++ Q) -> ~ In p P0)).
  { assert (Hin : forall p, In p new -> In p (access_pages a c) /\ ~ In p (Q ++ P0)).
    { intros p Hp. unfold new in Hp. apply filter_In in Hp as [X1 X2]. apply andb_prop in X2 as [_ X2].
      apply negb_true_iff in X2. split; [exact X1|]. intros X. apply (proj2 (page_mem_In _ _)) in X. rewrite X in X2. discriminate. }
    split; [|split].
    - apply List.NoDup_app; [| exact HN |].
      + unfold new. apply List.NoDup_filter. apply access_pages_acc_nodup. constructor.
      + intros p X1 X2. destruct (Hin p X1) as [_ X]. apply X. apply in_or_app. left. exact X2.
    - intros p X. apply in_app_or in X as [X|X]; [apply HL; exact (proj1 (Hin p X)) | exact (HI p X)].
    - intros p X. apply in_app_or in X as [X|X]; [intros Y; apply (proj2 (Hin p X)); apply in_or_app; right; exact Y | exact (HD p X)]. }
  destruct Hnew as [HN' [HI' HD']]. pose proof (List.NoDup_incl_length HN' HI') as Hlen. rewrite length_app in Hlen.
  destruct new as [|p0 rest] eqn:Enew.
  - exists (with_vm_backing lz (Q ++ P0) m0). split; [rewrite with_vm_backing_twice; reflexivity|].
    exists Q. split; [reflexivity|]. split; [exact HN|]. split; [exact HI | exact HD].
  - rewrite <- Enew in *.
    assert (Hbud : vm_backing_used (with_vm_backing lz (Q ++ P0) m0) + Z.of_nat (length new) * page_size <= vm_limit (m_vmmaps m0)).
    { unfold lz. rewrite used_with0, length_app. fold P0. unfold page_size in *. lia. }
    rewrite (proj2 (Z.leb_le _ _) Hbud).
    exists (with_vm_backing lz (new ++ Q ++ P0) m0). split; [rewrite with_vm_backing_twice; reflexivity|].
    exists (new ++ Q). split; [rewrite <- app_assoc; reflexivity|]. split; [exact HN'|]. split; [exact HI' | exact HD'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section XSIn.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma xs_ld_in : forall (m0 m : Model) (L : list word) S w sz sg rd rs1 (imm : bv 12) (x a : word) bs' (p' : word) r mm T,
  m_halted m0 = None -> matin m0 m L -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sg rd rs1 imm, 4%Z) ->
  rg S rs1 = x -> (x + sext 64 imm)%bv = a -> ms_mem S = mm ->
  rdn segs mm a (msz_n sz) = Some bs' -> incl (access_pages a (msz_n sz)) L ->
  vm_backing_used m0 + Z.of_nat (length L) * page_size <= vm_limit (m_vmmaps m0) ->
  (ms_pc_val S + Z_to_bv 64 4)%bv = p' -> ms_resv S = r ->
  (forall m', matin m0 m' L -> realizes_cfg segs cfg (mkCfg (setx S rd (load_word sz sg bs') p' r mm) m') T) ->
  realizes_cfg segs cfg (mkCfg S m) T.
Proof.
  intros m0 m L S w sz sg rd rs1 imm x a bs' p' r mm T Hh Hm Hsvc HF HE HD Hx Ha Hmm Hrd HL Hb Hp Hr HK.
  subst x a mm p' r.
  destruct (mat_step_in m0 m L _ (msz_n sz) Hm HL Hb) as [m' [Em Hm']].
  eapply rzc_mat; [rewrite (matin_halted m0 m L Hm); exact Hh | exact Hsvc
                  | eapply wacc_Load; [exact HF | exact HE | exact HD | exact Hrd] | exact Em | ].
  exact (HK m' Hm').
Qed.

Lemma xs_st_in : forall (m0 m : Model) (L : list word) S w sz rs1 rs2 (imm : bv 12) (x y a : word) (p' : word) r mm T,
  m_halted m0 = None -> matin m0 m L -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store sz rs1 rs2 imm, 4%Z) ->
  rg S rs1 = x -> (x + sext 64 imm)%bv = a -> rg S rs2 = y -> ms_mem S = mm ->
  store_ok segs mm a (msz_n sz) = true -> incl (access_pages a (msz_n sz)) L ->
  vm_backing_used m0 + Z.of_nat (length L) * page_size <= vm_limit (m_vmmaps m0) ->
  (ms_pc_val S + Z_to_bv 64 4)%bv = p' -> ms_resv S = r ->
  (forall m', matin m0 m' L -> realizes_cfg segs cfg (mkCfg (setx S 0 w0 p' (inval a r) (write_to_mem mm a (store_bytes sz y))) m') T) ->
  realizes_cfg segs cfg (mkCfg S m) T.
Proof.
  intros m0 m L S w sz rs1 rs2 imm x y a p' r mm T Hh Hm Hsvc HF HE HD Hx Ha Hy Hmm Hok HL Hb Hp Hr HK.
  subst x a y mm p' r.
  destruct (mat_step_in m0 m L _ (msz_n sz) Hm HL Hb) as [m' [Em Hm']].
  eapply rzc_mat; [rewrite (matin_halted m0 m L Hm); exact Hh | exact Hsvc
                  | eapply wacc_Store; [exact HF | exact HE | exact HD | exact Hok] | exact Em | ].
  exact (HK m' Hm').
Qed.

(* [comment removed for export] *)
Lemma rzc_acc_in : forall (m0 m : Model) (L : list word) ms ms' (a : word) (c : nat) T,
  m_halted m0 = None -> matin m0 m L -> ms_svc_pending ms = None ->
  step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' [(a, c)]) ->
  incl (access_pages a c) L ->
  vm_backing_used m0 + Z.of_nat (length L) * page_size <= vm_limit (m_vmmaps m0) ->
  (forall m', matin m0 m' L -> realizes_cfg segs cfg (mkCfg ms' m') T) ->
  realizes_cfg segs cfg (mkCfg ms m) T.
Proof.
  intros m0 m L ms ms' a c T Hh Hm Hsvc Hs HL Hb HK.
  destruct (mat_step_in m0 m L a c Hm HL Hb) as [m' [Em Hm']].
  eapply rzc_mat; [rewrite (matin_halted m0 m L Hm); exact Hh | exact Hsvc | exact Hs | exact Em | ].
  exact (HK m' Hm').
Qed.

End XSIn.
