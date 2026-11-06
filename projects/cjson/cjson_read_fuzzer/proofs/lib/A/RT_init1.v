(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tr0 (h : nat) : list Z := match h with 0%nat => [0x3f0f4; 0x40444] | _ => [0x3f0f4] end.
Definition H0 (h : nat) : Z := match h with 0%nat => 3886627579982177747 | _ => 1641774293848027603 end.
Definition T0 (h : nat) : Z := match h with 0%nat => 3 | _ => 2 end.

Lemma tr0_hash : forall h, trace_hash (tr0 h) = H0 h.
Proof. intros [|h]; vm_compute; reflexivity. Qed.

Definition depot0 (h : nat) (V : nat -> Z) : depot_st :=
  mkDepot [(H0 h, 0, 1)] (fun b => if b =? dbucket (H0 h) then 1 else 0) [4096 * V 453%nat] (T0 h) [4096 * V 454%nat].

(* [comment removed for export] *)
Definition loose0_fixed (V : nat -> Z) : list (Z * Z) :=
  [(4096 * V 471%nat, 4096); (4096 * V 377%nat, FS_TOTAL); (4096 * V 310%nat, 4096); (4096 * V 245%nat, 4096);
   (4096 * V 228%nat, 65536); (4096 * V 227%nat, 4096); (4096 * V 207%nat, 3727360); (4096 * V 78%nat, 65536)].

Definition st_main (h : nat) (V : nat -> Z) (usp : Z) : rtstate :=
  mkRT usp (4096 * V 208%nat) (4096 * (V 208%nat - V 209%nat) + 65536)
       (repeat region0 32) false (repeat [] 32)
       (4096 * V 226%nat) 0 []
       [] [] (depot0 h V) [] [tr0 h]
       (4096 * V 377%nat) (repeat 0 11) []
       (4096 * V 227%nat) (4096 * V 228%nat) (mkTLS (4096 * V 310%nat) 6148688 0 0)
       (loose0_fixed V) false []
       [] [] [] [] [].

(* [comment removed for export] *)
(* [comment removed for export] *)

Record init_pure (h : nat) (V : nat -> Z) (usp : Z) : Prop := mkIP {
  ip_hole : (h = 0 \/ h = 1)%nat;
  ip_usp : 0x7fff80000000 <= usp /\ usp + 192 <= 2^47 /\ usp mod 16 = 0;
  ip_pslack : 0 <= V 209%nat <= 15;
  ip_salign : 0 <= (-4096) * V 209%nat + (4096 * V 208%nat) mod 65536 <= 0;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  ip_ranges : forall r, In r (rt_ranges (st_main h V usp)) -> oclr (fst r) (snd r) /\ fst r < snd r /\ snd r <= alloc_ceiling /\ fst r mod 4096 = 0;   (* [comment removed for export] *)
  ip_pwdj : pwdj (rt_ranges (st_main h V usp));
  (* [comment removed for export] *)
  ip_usp_vars : usp = 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat;
  ip_top : 0 <= 16 * V 6%nat - 4096 * V 344%nat + 3935 <= 4095 }.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section INIT.
Variables (h : nat) (V : nat -> Z) (usp : Z).
Hypothesis IP : init_pure h V usp.
Let st := st_main h V usp.

Lemma rg0 : forall c, rg st c = region0.
Proof.
  intros c. unfold rg. cbn [st_regions st st_main]. unfold nthz. destruct (c <? 0); [reflexivity|].
  generalize (Z.to_nat c) as n. intros n.
  assert (G : forall k n, nth n (repeat region0 k) region0 = region0) by (induction k; intros [|m]; cbn; auto).
  apply G.
Qed.
Lemma cch0 : forall c, cch st c = [].
Proof.
  intros c. unfold cch. cbn [st_cache st st_main]. unfold nthz. destruct (c <? 0); [reflexivity|].
  assert (G : forall k n, nth n (repeat (@nil Z) k) [] = []) by (induction k; intros [|m]; cbn; auto). apply G.
Qed.
Lemma fhint0 : forall k, fhint st k = 0.
Proof.
  intros k. unfold fhint. cbn [st_hints st st_main]. unfold nthz. destruct (k <? 0); [reflexivity|].
  assert (G : forall j n, nth n (repeat 0 j) 0 = 0) by (induction j; intros [|m]; cbn; auto). apply G.
Qed.

Lemma qall0 : qall st = [].      Proof. reflexivity. Qed.
Lemma qelems0 : qelems st = [].  Proof. reflexivity. Qed.
Lemma all_blocks0 : all_blocks st = []. Proof. reflexivity. Qed.
Lemma used0 : forall c, used_cptrs st c = [].
Proof.
  intros c. unfold used_cptrs, avail_cptrs, live_cptrs, quar_cptrs, qpend_cptrs, batch_cptrs, apend_cptrs, lb_prim, q_prim, qp_prim, qbatch_addrs.
  rewrite rg0, cch0, qelems0, qall0. cbn. destruct (c =? 24); reflexivity.
Qed.
Lemma ncarved0 : forall c, ncarved st c = 0.
Proof. intros c. unfold ncarved. rewrite rg0. cbn. reflexivity. Qed.

Lemma in_loose_fs : In (st_fs st, FS_TOTAL) (st_loose0 st).
Proof. cbn. right. left. reflexivity. Qed.
Lemma in_loose_t : In (st_t st, 4096) (st_loose0 st).
Proof. cbn. do 5 right. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma loose_disj : forall b1 k1 b2 k2, In (b1, k1) (st_loose0 st) -> In (b2, k2) (st_loose0 st) ->
  (b1, b1 + k1) = (b2, b2 + k2) \/ b1 + k1 <= b2 \/ b2 + k2 <= b1.
Proof.
  intros b1 k1 b2 k2 H1 H2. pose proof (ip_pwdj _ _ _ IP) as PW.
  unfold rt_ranges in PW. apply pwdj_cons in PW as [_ PW]. apply pwdj_cons in PW as [_ PW].
  assert (I1 : In (b1, b1 + k1) (map (fun e : Z * Z => (fst e, fst e + snd e)) (st_loose0 st) ++ map (fun e : Z * Z => (fst e, fst e + smapsize (snd e))) (st_sec st)
        ++ map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st)) ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st)))).
  { apply in_or_app. left. apply in_map_iff. exists (b1, k1). auto. }
  assert (I2 : In (b2, b2 + k2) (map (fun e : Z * Z => (fst e, fst e + snd e)) (st_loose0 st) ++ map (fun e : Z * Z => (fst e, fst e + smapsize (snd e))) (st_sec st)
        ++ map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st)) ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st)))).
  { apply in_or_app. left. apply in_map_iff. exists (b2, k2). auto. }
  destruct (pwdj_In _ _ _ PW I1 I2) as [E|D]; [left; exact E| right; cbn [fst snd] in D; lia].
Qed.

Lemma loose_range : forall b k, In (b, k) (st_loose0 st) -> oclr b (b + k) /\ b < b + k /\ b + k <= alloc_ceiling /\ b mod 4096 = 0.
Proof.
  intros b k Hb. pose proof (ip_ranges _ _ _ IP (b, b + k)) as R. cbn [fst snd] in R. apply R.
  unfold rt_ranges. do 2 right. apply in_or_app. left. apply in_map_iff. exists (b, k). auto.
Qed.

Theorem st_main_wf : RTWF st.
Proof.
  pose proof (ip_usp _ _ _ IP) as (U1 & U2 & U3). pose proof (ip_pslack _ _ _ IP) as PS. pose proof (ip_salign _ _ _ IP) as SA.
  constructor.
  - (* [comment removed for export] *) constructor; try reflexivity.
    + cbn [st_spacebeg st st_main]. clear - SA. Z.div_mod_to_equations. lia.
    + cbn [st_pbase st st_main]. rewrite Z.mul_comm. apply Z_mod_mult.
    + cbn [st_pbase st_spacebeg st st_main]. unfold KSPACESIZE, PRIM_RES_SIZE. lia.
    + cbn [st_pa st st_main]. rewrite Z.mul_comm. apply Z_mod_mult.
    + cbn [st_t st st_main]. rewrite Z.mul_comm. apply Z_mod_mult.
    + cbn [st_fs st st_main]. rewrite Z.mul_comm. apply Z_mod_mult.
    + exact (ip_ranges _ _ _ IP).
    + exact (ip_pwdj _ _ _ IP).
    + exact in_loose_t.
    + exact in_loose_fs.
    + (* [comment removed for export] *) exists (4096 * V 228%nat), 65536. cbn [st_ctx st st_main]. split; [cbn; do 4 right; left; reflexivity| lia].
    + (* [comment removed for export] *) cbn [st_ctx st_fs st st_main].
      destruct (loose_disj (4096 * V 228%nat) 65536 (4096 * V 377%nat) FS_TOTAL ltac:(cbn; do 4 right; left; reflexivity) ltac:(cbn; right; left; reflexivity)) as [E|D];
        [exfalso; injection E; unfold FS_TOTAL; lia| unfold FS_TOTAL in *; lia].
    + (* [comment removed for export] *) exists (4096 * V 310%nat), 4096. cbn [st_tls st st_main tl_dtls_block]. split; [cbn; do 2 right; left; reflexivity| lia].
    + cbn [st_tls st_fs st st_main tl_dtls_block].
      destruct (loose_disj (4096 * V 310%nat) 4096 (4096 * V 377%nat) FS_TOTAL ltac:(cbn; do 2 right; left; reflexivity) ltac:(cbn; right; left; reflexivity)) as [E|D];
        [exfalso; injection E; unfold FS_TOTAL; lia| unfold FS_TOTAL in *; lia].
    + (* [comment removed for export] *) cbn [st_ctx st_t st st_main].
      destruct (loose_disj (4096 * V 228%nat) 65536 (4096 * V 227%nat) 4096 ltac:(cbn; do 4 right; left; reflexivity) ltac:(cbn; do 5 right; left; reflexivity)) as [E|D];
        [exfalso; injection E; lia| lia].
    + (* [comment removed for export] *) cbn [st_tls st_t st st_main tl_dtls_block].
      destruct (loose_disj (4096 * V 310%nat) 4096 (4096 * V 227%nat) 4096 ltac:(cbn; do 2 right; left; reflexivity) ltac:(cbn; do 5 right; left; reflexivity)) as [E|D];
        [exfalso; injection E | lia].
        (* [comment removed for export] *)
        pose proof (ip_pwdj _ _ _ IP) as PW. unfold rt_ranges in PW. apply pwdj_cons in PW as [_ PW]. apply pwdj_cons in PW as [_ PW].
        cbn [st_loose0 st st_main loose0_fixed map app fst snd] in PW.
        apply pwdj_cons in PW as [_ PW]. apply pwdj_cons in PW as [_ PW]. apply pwdj_cons in PW as [F3 PW].
        rewrite Forall_forall in F3. specialize (F3 (4096 * V 227%nat, 4096 * V 227%nat + 4096) ltac:(cbn; do 2 right; left; reflexivity)). cbn [fst snd] in F3. lia.
    + cbn. lia.
    + cbn [st_sp0 st st_main]. repeat split; lia.
    + cbn [st_nreserved st st_main]. unfold PTRARR_RES_SIZE. repeat split; try lia; try reflexivity.
    + split; [apply rg0| apply cch0].
    + intros _ c. apply cch0.
    + intros k. rewrite fhint0. lia.
    + (* [comment removed for export] *) intros H. exfalso. apply H. reflexivity.
    + intros H. exfalso. apply H. reflexivity.
    + intros H. exfalso. apply H. reflexivity.
    + unfold emb_sz. cbn [st_tls st st_main tl_emb_sz]. pose proof (nexh_bound st eq_refl) as NB. unfold EMB_MSG. lia.
  - (* [comment removed for export] *) intros c Hc. constructor; rewrite ?rg0, ?cch0, ?used0, ?ncarved0.
    + cbn. lia.
    + cbn. reflexivity.
    + cbn. lia.
    + cbn. reflexivity.
    + cbn -[KFREEARRAY_OFF]. unfold KFREEARRAY_OFF. lia.
    + cbn. lia.
    + cbn. reflexivity.
    + cbn -[KFREEARRAY_SIZE]. unfold KFREEARRAY_SIZE. lia.
    + unfold num_freed. rewrite rg0. unfold zlen. cbn. lia.
    + unfold zlen. cbn -[cmaxcount]. unfold cmaxcount, clampz. pose proof (Z.le_max_l 1 (Z.min 8 (1024 / csize c))). lia.
    + intros k Hk. destruct Hk.
    + constructor.
    + cbn. reflexivity.
    + destruct (Z.eq_dec c 0) as [->|NZ]; [cbn; lia|]. pose proof (csize_pos c ltac:(unfold KNUMCLASSES in Hc; lia)). cbn -[csize]. lia.
    + (* [comment removed for export] *) intros H1. left. pose proof (csize_pos c ltac:(unfold KNUMCLASSES in Hc; lia)). cbn -[csize]. lia.
    + cbn. intros E. discriminate.
  - (* [comment removed for export] *) constructor; [intros b Hb; rewrite all_blocks0 in Hb; destruct Hb| rewrite all_blocks0; constructor].
  - (* [comment removed for export] *) constructor; [cbn; constructor| unfold nsec, zlen; cbn; lia| intros e He; destruct He| intros e He; destruct He| cbn; constructor].
  - (* [comment removed for export] *) constructor.
    + intros b Hb. rewrite qall0 in Hb. destruct Hb.
    + intros b Hb. destruct Hb.
    + cbn. unfold QUAR_MAX_CACHE. lia.
    + cbn. unfold QUAR_MAX_SIZE. lia.
    + cbn. unfold QUAR_MAX_SIZE, QUAR_MAX_CACHE, QBATCH_SIZE. lia.
    + cbn. unfold zlen. cbn. lia.
    + intros bd Hbd. destruct Hbd.
    + intros ck Hck. destruct Hck.
  - (* [comment removed for export] *)
    assert (HB : 0 <= dbucket (H0 h) < 2^DEPOT_TAB_LOG) by (unfold dbucket, DEPOT_TAB_LOG; destruct h; cbn -[Z.pow Z.modulo Z.le Z.lt]; Z.div_mod_to_equations; lia).
    assert (HH : 0 <= H0 h < 2^64) by (destruct h; cbn; lia).
    assert (DN1 : forall id, 1 <= id <= 1 -> dnode (depot0 h V) id = (H0 h, 0, 1)).
    { intros id Hid. assert (id = 1) by lia. subst id. reflexivity. }
    constructor; cbn [st_depot st_trs st_trs0 st st_main]; unfold d_U; cbn [d_nodes depot0 length Z.of_nat Pos.of_succ_nat].
    + intros id Hid. rewrite (DN1 id Hid). cbn [dn_link dn_hash dn_store fst snd]. lia.
    + intros b Hb. cbn [d_tab depot0]. destruct (b =? dbucket (H0 h)); lia.
    + intros b Hb. cbn [d_tab depot0]. destruct (Z.eqb_spec b (dbucket (H0 h))); [exfalso; apply Hb; lia| reflexivity].
    + (* [comment removed for export] *) intros b id HR.
      assert (G : id = 1 /\ b = dbucket (H0 h)).
      { induction HR as [id Ht Hnz| id id' HR' IH Hl Hnz].
        - cbn [d_tab depot0] in Ht. destruct (Z.eqb_spec b (dbucket (H0 h))); [split; [lia| assumption]| exfalso; lia].
        - destruct IH as [-> _]. rewrite (DN1 1 ltac:(lia)) in Hl. cbn [dn_link fst snd] in Hl. exfalso. lia. }
      destruct G as [-> ->]. rewrite (DN1 1 ltac:(lia)). cbn [dn_hash fst]. split; [lia| reflexivity].
    + (* [comment removed for export] *) intros id Hid. rewrite (DN1 id Hid). cbn [dn_hash fst]. apply dreach_head; [| lia]. cbn [d_tab depot0]. rewrite Z.eqb_refl. lia.
    + (* [comment removed for export] *) intros tr Htr. cbn [app] in Htr. destruct Htr as [<-|[]]. exists 1. split; [lia|]. rewrite (DN1 1 ltac:(lia)). cbn [dn_hash fst]. symmetry. apply tr0_hash.
    + unfold zlen. cbn. lia.
    + unfold zlen. cbn. lia.
    + unfold DEPOT_KMAX, zlen. cbn. lia.
    + cbn. lia.
    + unfold d_nnb, zlen. cbn. reflexivity.
    + unfold d_nnb, DEPOT_NNB_MAX, zlen. cbn. lia.
    + cbn [d_T depot0]. destruct h; cbn; lia.
    + cbn [d_T depot0]. unfold d_nsb, zlen. cbn -[Z.mul Z.add Z.le]. destruct h; cbn; lia.
    + unfold d_nsb, SSTORE_BLOCK_FRAMES, zlen. cbn [d_T d_sblocks depot0 length Z.of_nat Pos.of_succ_nat]. destruct h; reflexivity.
    + unfold d_nsb, DEPOT_NSB_MAX, zlen. cbn. lia.
    + intros b [<-|[]]. rewrite Z.mul_comm. apply Z_mod_mult.
    + intros b [<-|[]]. rewrite Z.mul_comm. apply Z_mod_mult.
  - (* [comment removed for export] *) constructor; [cbn; constructor| intros F k HF; destruct HF].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PROV_MAIN : Z := Eval vm_compute in
  (zsum (map (fun c => (LUMPU + FAPROV * Nmax c) + LUMPF) classes) + NB + 0 + PTRC + 0 + 0
   + (NODEBLOCK_SIZE * (DEPOT_NNB_MAX - 1) + STOREBLOCK_SIZE * (DEPOT_NSB_MAX - 1)) + 0 + 0 + EMB_CAP).  (* [comment removed for export] *)

Lemma st_main_prov : rt_prov st = PROV_MAIN.
Proof.
  (* [comment removed for export] *)
  unfold rt_prov.
  replace (prov_depot st) with (NODEBLOCK_SIZE * (DEPOT_NNB_MAX - 1) + STOREBLOCK_SIZE * (DEPOT_NSB_MAX - 1)) by reflexivity.
  replace (prov_ptr st) with PTRC by (unfold prov_ptr; cbn [st_nreserved st st_main]; unfold nsec, zlen; cbn -[PTRC]; unfold PTRC; lia).
  replace (prov_slots st) with 0 by reflexivity.
  replace (prov_emb st) with EMB_CAP by reflexivity.
  replace (prov_l24 st) with 0 by reflexivity.
  replace (prov_live st) with 0 by reflexivity.
  replace (prov_quar st) with 0 by reflexivity.
  replace (prov_q st) with 0 by reflexivity.
  replace (prov_nb st) with NB by reflexivity.
  replace (prov_classes st) with (zsum (map (fun c => (LUMPU + FAPROV * Nmax c) + LUMPF) classes)) by (vm_compute; reflexivity).
  vm_compute. reflexivity.
Qed.

Lemma PROV_MAIN_small : PROV_MAIN <= 2^32 - 0xfc0000 - 0x92b45800.
Proof. vm_compute. discriminate. Qed.
End INIT.


End CeilWrap.
