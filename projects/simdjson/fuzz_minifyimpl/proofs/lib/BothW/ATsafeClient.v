(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree Stdio HarnessM Adapter Driver ProgA
  AsanCtrl AsanCtrlProps AsanBudget AsanEmbed AsanInv AsanTotal SizeHist AsanProgDeps AsanOK RSimProg MI_Inv LB_Inv LB_Sum.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import Keeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AProto ATsafeCore ATsafeEv ATsafeAlloc ATsafeOps ATsafeProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation M := Monad.M.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tall_True : forall {R} (t : itree node (exc R)), tall (fun _ => True) t.
Proof. induction t as [[|r]|n k IH]; cbn; auto. Qed.

Lemma keeps_alift : forall {B R} (f : APS -> B) (t : AM R), keeps f (alift t).
Proof.
  intros B R f t s. unfold alift. eapply tall_ebind; [apply tall_True|]. intros r _. cbn. reflexivity.
Qed.

Lemma keeps_cl_malloc : forall n, keeps aps_cl (amalloc_M n).
Proof.
  intros n. unfold amalloc_M. apply keeps_getk. intros s0.
  apply keeps_bind; [apply keeps_alift|]. intros x.
  apply keeps_bind; [apply keeps_upd; intros s; reflexivity|]. intros _. apply keeps_ret.
Qed.

Lemma keeps_cl_free : forall p, keeps aps_cl (afree_M p).
Proof.
  intros p. unfold afree_M. apply keeps_getk. intros s0.
  apply keeps_bind; [apply keeps_alift|]. intros x. apply keeps_upd. intros s; reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CUB (n : Z) : Z := n + n / 4 + n / 8 + 2^21.
Definition FUZZ_COST : Z := 2^27.

Lemma CUB_mono : forall n n', 0 <= n <= n' -> CUB n <= CUB n'.
Proof. intros n n' H. unfold CUB. pose proof (Z.div_le_mono n n' 4 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono n n' 8 ltac:(lia) ltac:(lia)). lia. Qed.
Lemma CUB_nonneg : forall n, 0 <= n -> 0 <= CUB n.
Proof. intros n H. unfold CUB. pose proof (Z.div_pos n 4). pose proof (Z.div_pos n 8). lia. Qed.
Lemma CUB_ge : forall n, 0 <= n -> n <= CUB n.
Proof. intros n H. unfold CUB. pose proof (Z.div_pos n 4). pose proof (Z.div_pos n 8). lia. Qed.
Lemma COSTF_val : COSTF = 9 * (8192 + 128) + 8.      (* [comment removed for export] *)
Proof. reflexivity. Qed.
Lemma COSTM_nonneg : forall n, 0 <= n -> 0 <= COSTM n.
Proof.
  intros n Hn. unfold COSTM, COSTP, COSTS.
  destruct (is_primary n) eqn:P.
  - pose proof (primary_class_facts n Hn P) as (C & _ & S & _). lia.
  - pose proof (Z.div_pos (sec_map_size n) 8). pose proof (Z.div_pos (sec_map_size n) 4).
    assert (NS : 0 <= needed_size n).
    { unfold needed_size, needed0, rounded_size. pose proof (rup_ge (Z.max n 8) 8 ltac:(lia)).
      unfold rz_size. pose proof (proj2 (Z.shiftl_nonneg 16 (rz_log n)) ltac:(lia)). destruct (is_primary n); lia. }
    assert (0 <= sec_map_size n); [| lia]. unfold sec_map_size. pose proof (rup_ge (needed_size n) PG ltac:(unfold PG; lia)). unfold PG in *. lia.
Qed.
Lemma COSTM_le_CUB : forall n, 0 <= n <= 2^40 -> COSTM n <= CUB n.
Proof.
  intros n Hn. unfold COSTM, COSTP, COSTS, CUB.
  destruct (Z.leb_spec n 64512).
  - rewrite is_primary_iff by lia. replace (n <=? 64512) with true by (symmetry; apply Z.leb_le; lia).
    pose proof (size_le_2n n ltac:(lia)). pose proof (Z.div_pos n 4). pose proof (Z.div_pos n 8). lia.
  - rewrite large_not_primary by lia. pose proof (sec_map_size_bounds n ltac:(lia)).
    pose proof (Z.div_le_mono (sec_map_size n) (n + 12296) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (sec_map_size n) (n + 12296) 4 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_mod (n + 12296) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 8 ltac:(lia)).
    pose proof (Z.div_mod (n + 12296) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 4 ltac:(lia)).
    pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
    pose proof (Z.div_mod n 4 ltac:(lia)). pose proof (Z.mod_pos_bound n 4 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Definition PAYMAX : Z := CUB MAX_INPUT.
Lemma PAYMAX_ok : forall n, 0 <= n <= MAX_INPUT -> COSTM n <= PAYMAX.
Proof. intros n H. unfold PAYMAX. etransitivity; [apply COSTM_le_CUB; unfold MAX_INPUT in H; lia| apply CUB_mono; exact H]. Qed.

(* [comment removed for export] *)
Definition CINIT_COST : Z := CUB CLIENT_VEC_BYTES + COSTF.
Definition MINIFY_COST : Z := CUB MAX_INPUT + CUB ERRSTR_BYTES + CUB ERRMSG_LEN + 3 * COSTF.
Lemma call_cost_bound : CINIT_COST + MINIFY_COST <= FUZZ_COST.
Proof. vm_compute. discriminate. Qed.
Lemma CINIT_COST_nonneg : 0 <= CINIT_COST. Proof. vm_compute. discriminate. Qed.
Lemma MINIFY_COST_nonneg : 0 <= MINIFY_COST. Proof. vm_compute. discriminate. Qed.

Section Client.
Variable NMAX : nat.
Variables SB PA : Z.
Variable Abase : alw.
Variable NLK : Z.                                    (* [comment removed for export] *)
Local Notation NMAXZ := (Z.of_nat NMAX).
Hypothesis HLIM : NLK + NMAXZ * 4096 <= LIMIT.
Hypothesis HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
Hypothesis HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
Local Notation TSM := (TSM NMAX (St:=APS)).
Local Notation JJ := (JJ NMAX SB PA Abase NLK).

(* [comment removed for export] *)
Definition clbA (s : APS) : list (AsanCtrl.aptr * Z) :=
  match aps_cl s with Some q => [(q, CLIENT_VEC_BYTES)] | None => [] end.
Definition bank (s : APS) : Z := match aps_cl s with Some _ => COSTF | None => 0 end.

Definition JC (X : list (AsanCtrl.aptr * Z)) (v : Z) : preT (St:=APS) :=
  fun RNG A s mo => 0 <= v /\ JJ (clbA s ++ X) (v + bank s) RNG A s mo.

Lemma length_clbA : forall s, (length (clbA s) <= 1)%nat.
Proof. intros s. unfold clbA. destruct (aps_cl s); cbn; lia. Qed.
Lemma bank_nonneg : forall s, 0 <= bank s.
Proof. intros s. unfold bank. destruct (aps_cl s); [rewrite COSTF_val|]; lia. Qed.

Lemma JC_acct : forall Y v RNG A s mo, JC Y v RNG A s mo -> acct_ok NMAX RNG A mo.
Proof. intros Y v RNG A s mo [_ H]. exact (JJ_acct NMAX SB PA Abase NLK HLIM _ _ _ _ _ _ H). Qed.
Lemma JC_perm : forall Y Y' v RNG A s mo, Permutation Y Y' -> JC Y v RNG A s mo -> JC Y' v RNG A s mo.
Proof. intros Y Y' v RNG A s mo HP [Hv H]. split; [exact Hv|]. eapply (JJ_perm NMAX SB PA Abase NLK); [| exact H]. apply Permutation_app_head. exact HP. Qed.
Lemma JC_credit : forall Y v v' RNG A s mo, 0 <= v' <= v -> JC Y v RNG A s mo -> JC Y v' RNG A s mo.
Proof. intros Y v v' RNG A s mo Hv [_ H]. split; [lia|]. eapply (JJ_credit NMAX SB PA Abase NLK); [| exact H]. pose proof (bank_nonneg s). lia. Qed.
Lemma JC_nonneg : forall Y v RNG A s mo, JC Y v RNG A s mo -> 0 <= v.
Proof. intros Y v RNG A s mo [Hv _]. exact Hv. Qed.
Lemma JC_io : forall n Y v RNG A s mo rsp mo' evs, io_node n -> nstep n mo rsp mo' evs -> JC Y v RNG A s mo -> JC Y v RNG A s mo'.
Proof. intros n Y v RNG A s mo rsp mo' evs Hio Hst [Hv H]. split; [exact Hv|]. exact (JJ_io NMAX SB PA Abase NLK HSB HPA n _ _ _ _ _ _ _ _ _ Hio Hst H). Qed.
Lemma JC_so : forall Y v RNG A s mo w, JC Y v RNG A s mo -> JC Y v RNG A (aset_so w s) mo.
Proof.
  intros Y v RNG A s mo w [Hv H]. split; [exact Hv|]. change (clbA (aset_so w s)) with (clbA s). change (bank (aset_so w s)) with (bank s).
  exact (JJ_so NMAX SB PA Abase NLK _ _ _ _ _ _ w H).
Qed.

(* [comment removed for export] *)
Lemma JC_init : forall X v RNG A s mo, aps_cl s = None -> 0 <= v -> JJ X v RNG A s mo -> JC X v RNG A s mo.
Proof. intros X v RNG A s mo E Hv H. unfold JC, clbA, bank. rewrite E, Z.add_0_r. split; [exact Hv| exact H]. Qed.

Lemma HISTOK_amb3 n (L : list Z) : (length L <= 3)%nat -> HISTOK (n :: L).
Proof. intros HL. apply (HISTOK_amb n [] L); [apply Forall_nil| unfold BCs, zsum; cbn; unfold HB; lia| unfold N4s, N24s, zcount, zlen; cbn; lia| exact HL]. Qed.

(* [comment removed for export] *)
Lemma TSM_keeps_cl : forall {X} (P : preT (St:=APS)) (m : M APS X) (Q : postM (St:=APS) X) (c : option AsanCtrl.aptr),
  TSM P m Q -> keeps aps_cl m ->
  TSM (fun RNG A s mo => P RNG A s mo /\ aps_cl s = c) m (fun x RNG A s mo => Q x RNG A s mo /\ aps_cl s = c).
Proof.
  intros X P m Q c H HK RNG A s mo [Hp Hc]. unfold MQ.
  eapply TS_mono; [eapply (TS_tall NMAX); [apply (H _ _ _ _ Hp)| apply (HK s)]|].
  intros [|[x s']] RNG' A' mo' _ HQ; cbn in HQ |- *; [exact I|]. destruct HQ as [HQ E]. split; [exact HQ| congruence].
Qed.

Lemma clbA_bank_eq : forall s s', aps_cl s' = aps_cl s -> clbA s' = clbA s /\ bank s' = bank s.
Proof. intros s s' E. unfold clbA, bank. rewrite E. split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma UC_malloc_h : forall Y v n, 0 <= n <= REQMAX -> (forall s, HISTOK (n :: map snd (clbA s ++ Y))) ->
  TSM (fun RNG A s mo => JC Y v RNG A s mo /\ COSTM n <= v) (amalloc_M n)
      (fun r RNG A s mo => exists q, r = Some q /\ JC ((q, n) :: Y) (v - COSTM n) RNG A s mo /\ n < 2^63).
Proof.
  intros Y v n Hn HH. intros RNG A s mo [[Hv HJ] Hnv]. pose proof (bank_nonneg s) as HB.
  pose proof (TSM_keeps_cl (fun RNG A s' mo => JJ (clbA s ++ Y) (v + bank s) RNG A s' mo /\ COSTM n <= v + bank s) (amalloc_M n) _ (aps_cl s)
                (U_malloc NMAX SB PA Abase NLK HLIM (clbA s ++ Y) (v + bank s) n Hn (HH s))
                (keeps_cl_malloc n)) as H.
  eapply TS_mono; [apply (H RNG A s mo); split; [split; [exact HJ| lia]| reflexivity]|].
  intros [|[r s']] RNG' A' mo' _ HQ; cbn in HQ |- *; [exact I|].
  destruct HQ as [(q & -> & HJ' & Hlt) E]. exists q. split; [reflexivity|]. split; [| exact Hlt].
  destruct (clbA_bank_eq s s' E) as [EC EB]. unfold JC. rewrite EC, EB. split; [lia|].
  replace (v - COSTM n + bank s) with (v + bank s - COSTM n) by lia.
  eapply (JJ_perm NMAX SB PA Abase NLK); [| exact HJ']. apply Permutation_middle.
Qed.

Lemma UC_malloc : forall Y v n, 0 <= n <= REQMAX -> (length Y <= 2)%nat -> HISTOK (n :: map snd Y) ->
  TSM (fun RNG A s mo => JC Y v RNG A s mo /\ COSTM n <= v) (amalloc_M n)
      (fun r RNG A s mo => exists q, r = Some q /\ JC ((q, n) :: Y) (v - COSTM n) RNG A s mo /\ n < 2^63).
Proof.
  intros Y v n Hn HL _. apply UC_malloc_h; [exact Hn|].
  intros s. apply HISTOK_amb3. rewrite length_map, length_app. pose proof (length_clbA s). lia.
Qed.

Lemma UC_free : forall Y v p n, TSM (fun RNG A s mo => JC ((p, n) :: Y) v RNG A s mo /\ COSTF <= v) (afree_M p) (fun _ => JC Y (v - COSTF)).
Proof.
  intros Y v p n RNG A s mo [[Hv HJ] Hcv]. pose proof (bank_nonneg s) as HB.
  pose proof (TSM_keeps_cl (fun RNG A s' mo => JJ ((p, n) :: clbA s ++ Y) (v + bank s) RNG A s' mo /\ COSTF <= v + bank s) (afree_M p) _ (aps_cl s)
                (U_free NMAX SB PA Abase NLK HLIM (clbA s ++ Y) (v + bank s) p n) (keeps_cl_free p)) as H.
  eapply TS_mono; [apply (H RNG A s mo); split; [| reflexivity]|].
  - split; [| lia]. eapply (JJ_perm NMAX SB PA Abase NLK); [| exact HJ]. apply Permutation_sym, Permutation_middle.
  - intros [|[r s']] RNG' A' mo' _ HQ; cbn in HQ |- *; [exact I|]. destruct HQ as [HJ' E].
    destruct (clbA_bank_eq s s' E) as [EC EB]. unfold JC. rewrite EC, EB. split; [lia|].
    replace (v - COSTF + bank s) with (v + bank s - COSTF) by lia. exact HJ'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation cinitA := (HarnessM.client_init amalloc_M (new_handlerA AAllocAsan) aps_cl aset_cl).

Lemma cinit_some : forall s q, aps_cl s = Some q -> cinitA s = mret tt s.
Proof. intros s q H. unfold HarnessM.client_init, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.
Lemma cinit_none : forall s, aps_cl s = None ->
  cinitA s = (p <- HarnessM.opnew amalloc_M (new_handlerA AAllocAsan) CLIENT_VEC_BYTES ;; mupd (aset_cl (Some p))) s.
Proof. intros s H. unfold HarnessM.client_init, mbind, mget. cbn. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma opnew8_ok : forall Y v, (length Y <= 3)%nat -> COSTM CLIENT_VEC_BYTES <= v ->
  TSM (fun RNG A s mo => JJ Y v RNG A s mo /\ aps_cl s = None)
      (HarnessM.opnew amalloc_M (new_handlerA AAllocAsan) CLIENT_VEC_BYTES)
      (fun p RNG A s mo => JJ ((p, CLIENT_VEC_BYTES) :: Y) (v - COSTM CLIENT_VEC_BYTES) RNG A s mo /\ aps_cl s = None).
Proof.
  intros Y v HL Hv. unfold HarnessM.opnew. change (CLIENT_VEC_BYTES =? 0) with false. cbn iota.
  eapply TSM_bind'.
  - eapply TSM_pre; [apply (TSM_keeps_cl _ _ _ None (U_malloc NMAX SB PA Abase NLK HLIM Y v CLIENT_VEC_BYTES
                               ltac:(unfold CLIENT_VEC_BYTES, REQMAX; lia) ltac:(apply HISTOK_amb3; rewrite length_map; exact HL)) (keeps_cl_malloc _))|].
    intros RNG A s mo [HJ E]. split; [split; [exact HJ| exact Hv]| exact E].
  - intros [q|]; cbv beta.
    + apply TSM_ret. intros RNG A s mo [(q' & Eq & HJ & _) E]. injection Eq as <-.
      split; [exact (JJ_acct NMAX SB PA Abase NLK HLIM _ _ _ _ _ _ HJ)|]. split; [exact HJ| exact E].
    + eapply TSM_pre; [apply TSM_false|]. intros RNG A s mo [(q' & Eq & _) _]. discriminate Eq.
Qed.

(* [comment removed for export] *)
Lemma UC_cinit : forall X v, (length X <= 2)%nat -> CINIT_COST <= v ->
  TSM (JC X v) cinitA (fun _ => JC X (v - CINIT_COST)).
Proof.
  intros X v HL Hv RNG A s mo HJ. pose proof CINIT_COST_nonneg as C0.
  destruct (aps_cl s) as [q|] eqn:E.
  - rewrite (cinit_some s q E). cbn. split; [exact (JC_acct _ _ _ _ _ _ HJ)|]. cbn.
    eapply JC_credit; [| exact HJ]. pose proof (JC_nonneg _ _ _ _ _ _ HJ). lia.
  - rewrite (cinit_none s E). destruct HJ as [Hv0 HJ].
    assert (HJ0 : JJ X v RNG A s mo) by (unfold clbA, bank in HJ; rewrite E, Z.add_0_r in HJ; exact HJ).
    pose proof (COSTM_le_CUB CLIENT_VEC_BYTES ltac:(unfold CLIENT_VEC_BYTES; lia)) as C8. pose proof (COSTM_nonneg CLIENT_VEC_BYTES ltac:(unfold CLIENT_VEC_BYTES; lia)) as C80.
    refine (TSM_bind' NMAX _ _ _ _ _ (opnew8_ok X v ltac:(lia) ltac:(unfold CINIT_COST in Hv; rewrite COSTF_val in Hv; lia)) _ RNG A s mo (conj HJ0 E)).
    intros p. eapply TSM_post; [apply TSM_upd; intros ? ? ? ? [HJ' _]; exact (JJ_acct NMAX SB PA Abase NLK HLIM _ _ _ _ _ _ HJ')|].
    intros [] RNG' A' s'' mo' _ (s' & -> & HJ' & E').
    unfold JC, clbA, bank. destruct s' as [st so rv tp cl]. cbn [aps_cl aset_cl app] in *. subst cl.
    split; [lia|]. unfold CINIT_COST. replace (v - (CUB CLIENT_VEC_BYTES + COSTF) + COSTF) with (v - CUB CLIENT_VEC_BYTES) by lia.
    eapply (JJ_credit NMAX SB PA Abase NLK); [| apply JJ_cl; exact HJ']. unfold CINIT_COST in Hv. rewrite COSTF_val in Hv. lia.
Qed.

(* [comment removed for export] *)
Lemma UC_opnew_h : forall Y v n, 0 < n <= REQMAX -> (forall s, HISTOK (n :: map snd (clbA s ++ Y))) -> CUB n <= v ->
  TSM (JC Y v) (HarnessM.opnew amalloc_M (new_handlerA AAllocAsan) n) (fun p => JC ((p, n) :: Y) (v - CUB n)).
Proof.
  intros Y v n Hn HH Hv. unfold HarnessM.opnew. replace (if n =? 0 then 1 else n) with n by (destruct (Z.eqb_spec n 0); lia).
  pose proof (COSTM_le_CUB n ltac:(unfold REQMAX in Hn; lia)) as HC. pose proof (COSTM_nonneg n ltac:(lia)) as HC0.
  eapply TSM_bind'.
  - eapply TSM_pre; [apply (UC_malloc_h Y v n ltac:(lia) HH)|]. intros RNG A s mo HJ. split; [exact HJ| lia].
  - intros [q|]; cbv beta.
    + apply TSM_ret. intros RNG A s mo (q' & Eq & HJ & _). injection Eq as <-. split; [exact (JC_acct _ _ _ _ _ _ HJ)|].
      eapply JC_credit; [| exact HJ]. pose proof (JC_nonneg _ _ _ _ _ _ HJ). lia.
    + eapply TSM_pre; [apply TSM_false|]. intros RNG A s mo (q' & Eq & _). discriminate Eq.
Qed.

Lemma sizes_clbA : forall s, map snd (clbA s) = [] \/ map snd (clbA s) = [CLIENT_VEC_BYTES].
Proof. intros s. unfold clbA. destruct (aps_cl s); cbn; auto. Qed.
Lemma itemsz_8 : itemsz CLIENT_VEC_BYTES. Proof. right. exists 1. unfold CLIENT_VEC_BYTES. lia. Qed.
Lemma itemsz_56 : itemsz ERRSTR_BYTES. Proof. right. exists 13. unfold ERRSTR_BYTES. lia. Qed.
Lemma HISTOK_client : forall n (c t Zs : list Z), (c = [] \/ c = [CLIENT_VEC_BYTES]) -> (t = [] \/ t = [ERRSTR_BYTES]) -> (length Zs <= 3)%nat ->
  forall M, Permutation M (n :: c ++ t ++ Zs) -> HISTOK M.
Proof.
  intros n c t Zs Hc Ht HL M HP. apply (HISTOK_intro (c ++ t) (n :: Zs)).
  - etransitivity; [exact HP|]. rewrite app_assoc. apply Permutation_middle.
  - apply YWs_app. unfold YWs. split; [destruct Hc as [->| ->]; [apply Forall_nil| apply Forall_cons; [apply itemsz_8| apply Forall_nil]] | destruct Ht as [->| ->]; [apply Forall_nil| apply Forall_cons; [apply itemsz_56| apply Forall_nil]]].
  - destruct Hc as [->| ->]; destruct Ht as [->| ->]; vm_compute; intros; discriminate.
  - destruct Hc as [->| ->]; destruct Ht as [->| ->]; vm_compute; intros; discriminate.
  - cbn [length]. lia.
Qed.
Lemma HISTOK_client_str : forall (c Zs : list Z), (c = [] \/ c = [CLIENT_VEC_BYTES]) -> (length Zs <= 4)%nat ->
  forall M, Permutation M (ERRSTR_BYTES :: c ++ Zs) -> HISTOK M.
Proof.
  intros c Zs Hc HL M HP. apply (HISTOK_intro (ERRSTR_BYTES :: c) Zs); [exact HP| | | | exact HL].
  - unfold YWs. apply Forall_cons; [apply itemsz_56| destruct Hc as [->| ->]; [apply Forall_nil| apply Forall_cons; [apply itemsz_8| apply Forall_nil]]].
  - destruct Hc as [->| ->]; vm_compute; intros; discriminate.
  - destruct Hc as [->| ->]; vm_compute; intros; discriminate.
Qed.

(* [comment removed for export] *)
Definition JCo (b : option AsanCtrl.aptr) (n : Z) (X : list (AsanCtrl.aptr * Z)) (v : Z) : preT (St:=APS) :=
  match b with Some q => JC ((q, n) :: X) v | None => JC X v end.
Definition ocost (b : option AsanCtrl.aptr) : Z := match b with Some _ => COSTF | None => 0 end.
Lemma ocost_bound : forall b, 0 <= ocost b <= COSTF.
Proof. intros [q|]; unfold ocost; rewrite COSTF_val; lia. Qed.
Lemma UC_odelete : forall X v b n, ocost b <= v -> TSM (JCo b n X v) (HarnessM.odelete afree_M b) (fun _ => JC X (v - ocost b)).
Proof.
  intros X v [q|] n Hv; cbn [JCo HarnessM.odelete ocost] in *.
  - eapply TSM_pre; [apply UC_free|]. intros RNG A s mo HJ. split; [exact HJ| exact Hv].
  - apply TSM_ret. intros RNG A s mo HJ. split; [exact (JC_acct _ _ _ _ _ _ HJ)|]. rewrite Z.sub_0_r. exact HJ.
Qed.

Lemma UC_minify : forall X v data, (length X <= 2)%nat -> zlength data <= MAX_INPUT -> MINIFY_COST <= v ->
  TSM (JC X v) (HarnessM.minify_call amalloc_M afree_M (new_handlerA AAllocAsan) data) (fun _ => JC X (v - MINIFY_COST)).
Proof.
  intros X v data HL Hd Hv. unfold HarnessM.minify_call.
  assert (Hn : 0 <= Z.of_nat (length data) <= MAX_INPUT) by (unfold zlength in Hd; lia).
  set (n := Z.of_nat (length data)) in *.
  assert (HLX : (length (map snd X) <= 2)%nat) by (rewrite length_map; exact HL).
  pose proof (CUB_mono n MAX_INPUT Hn) as CN. pose proof (CUB_nonneg n ltac:(lia)) as CN0.
  pose proof (CUB_nonneg ERRSTR_BYTES ltac:(unfold ERRSTR_BYTES; lia)) as C56. pose proof (CUB_nonneg ERRMSG_LEN ltac:(unfold ERRMSG_LEN; lia)) as C54.
  pose proof COSTF_val as CF.
  assert (CRED : forall v', v - MINIFY_COST <= v' -> forall RNG A s mo, JC X v' RNG A s mo -> acct_ok NMAX RNG A mo /\ JC X (v - MINIFY_COST) RNG A s mo).
  { intros v' Hv' RNG A s mo HJ. split; [exact (JC_acct _ _ _ _ _ _ HJ)|]. eapply JC_credit; [| exact HJ]. lia. }
  unfold MINIFY_COST in Hv, CRED.
  eapply TSM_bind' with (Q1 := fun b RNG A s mo => exists w, v - CUB n <= w <= v /\ JCo b n X w RNG A s mo).
  { destruct (Z.eqb_spec n 0) as [E|E].
    - apply TSM_ret. intros RNG A s mo HJ. split; [exact (JC_acct _ _ _ _ _ _ HJ)|]. exists v. split; [lia|]. cbn [JCo]. exact HJ.
    - eapply TSM_bind'; [apply (UC_opnew_h X v n)|].
      + unfold MAX_INPUT, REQMAX in *. lia.
      + intros s. rewrite map_app. eapply (HISTOK_client n (map snd (clbA s)) [] (map snd X)); [apply sizes_clbA| left; reflexivity| lia| reflexivity].
      + lia.
      + intros p. apply TSM_ret. intros RNG A s mo HJ. split; [exact (JC_acct _ _ _ _ _ _ HJ)|]. exists (v - CUB n). split; [lia|]. exact HJ. }
  intros b. apply TSM_exI. intros w. apply TSM_pure'. intros Hw. pose proof (ocost_bound b) as OB.
  destruct (unclosed data).
  2:{ eapply TSM_post; [apply UC_odelete; lia|]. intros [] RNG A s mo _ HJ. apply (CRED (w - ocost b)); [lia| exact HJ]. }
  (* [comment removed for export] *)
  assert (STR : forall Y w1, (length Y <= 3)%nat -> (forall s, HISTOK (ERRSTR_BYTES :: map snd (clbA s ++ Y))) -> CUB ERRSTR_BYTES <= w1 ->
    TSM (JC Y w1) (HarnessM.opnew amalloc_M (new_handlerA AAllocAsan) ERRSTR_BYTES) (fun t => JC ((t, ERRSTR_BYTES) :: Y) (w1 - CUB ERRSTR_BYTES))).
  { intros Y w1 HY HH Hw1. apply UC_opnew_h; [unfold ERRSTR_BYTES, REQMAX; lia| exact HH| exact Hw1]. }
  eapply TSM_bind' with (Q1 := fun t RNG A s mo => JCo b n ((t, ERRSTR_BYTES) :: X) (w - CUB ERRSTR_BYTES) RNG A s mo).
  { destruct b as [q|]; cbn [JCo].
    - eapply TSM_post; [apply (STR ((q, n) :: X) w); [cbn; lia| | lia]|].
      + intros s. rewrite map_app. cbn [map snd]. eapply (HISTOK_client_str (map snd (clbA s)) (n :: map snd X)); [apply sizes_clbA| cbn [length]; lia| reflexivity].
      + intros t RNG A s mo _ HJ. eapply JC_perm; [apply perm_swap| exact HJ].
    - apply (STR X w); [lia| | lia]. intros s. rewrite map_app. eapply (HISTOK_client_str (map snd (clbA s)) (map snd X)); [apply sizes_clbA| lia| reflexivity]. }
  intros t.
  eapply TSM_bind' with (Q1 := fun b' RNG A s mo => exists m w', w - CUB ERRSTR_BYTES - COSTF - CUB ERRMSG_LEN <= w' /\ JCo b' m ((t, ERRSTR_BYTES) :: X) w' RNG A s mo).
  { destruct (Z.leb_spec ERRMSG_LEN n) as [Hle|Hlt].
    - apply TSM_ret. intros RNG A s mo HJ. split; [destruct b; cbn [JCo] in HJ; exact (JC_acct _ _ _ _ _ _ HJ)|].
      exists n, (w - CUB ERRSTR_BYTES). split; [lia| exact HJ].
    - eapply TSM_bind' with (Q1 := fun _ => JC ((t, ERRSTR_BYTES) :: X) (w - CUB ERRSTR_BYTES - ocost b)).
      + destruct b as [q|]; cbn [JCo HarnessM.odelete ocost].
        * eapply TSM_pre; [apply (UC_free ((t, ERRSTR_BYTES) :: X) (w - CUB ERRSTR_BYTES) q n)|].
          intros RNG A s mo HJ. split; [exact HJ| lia].
        * apply TSM_ret. intros RNG A s mo HJ. split; [exact (JC_acct _ _ _ _ _ _ HJ)|]. rewrite Z.sub_0_r. exact HJ.
      + intros []. eapply TSM_bind'; [apply (UC_opnew_h ((t, ERRSTR_BYTES) :: X) (w - CUB ERRSTR_BYTES - ocost b) ERRMSG_LEN)|].
        * unfold ERRMSG_LEN, REQMAX. lia.
        * intros s. rewrite map_app. cbn [map snd]. eapply (HISTOK_client ERRMSG_LEN (map snd (clbA s)) [ERRSTR_BYTES] (map snd X)); [apply sizes_clbA| right; reflexivity| lia| reflexivity].
        * lia.
        * intros p'. apply TSM_ret. intros RNG A s mo HJ. split; [exact (JC_acct _ _ _ _ _ _ HJ)|].
          exists ERRMSG_LEN, (w - CUB ERRSTR_BYTES - ocost b - CUB ERRMSG_LEN). split; [lia| exact HJ]. }
  intros b'. apply TSM_exI. intros m. apply TSM_exI. intros w'. apply TSM_pure'. intros Hw'. pose proof (ocost_bound b') as OB'.
  eapply TSM_bind' with (Q1 := fun _ => JCo b' m X (w' - COSTF)).
  { destruct b' as [q'|]; cbn [JCo].
    - eapply TSM_pre; [apply (UC_free ((q', m) :: X) w' t ERRSTR_BYTES)|]. intros RNG A s mo HJ. split; [eapply JC_perm; [apply perm_swap| exact HJ]|].
      pose proof (JC_nonneg _ _ _ _ _ _ HJ). lia.
    - eapply TSM_pre; [apply (UC_free X w' t ERRSTR_BYTES)|]. intros RNG A s mo HJ. split; [exact HJ|]. pose proof (JC_nonneg _ _ _ _ _ _ HJ). lia. }
  intros []. eapply TSM_post; [apply UC_odelete; lia|].
  intros [] RNG A s mo _ HJ. apply (CRED (w' - COSTF - ocost b')); [lia| exact HJ].
Qed.

(* [comment removed for export] *)
Lemma UC_fuzz : forall X v data, (length X <= 2)%nat -> zlength data <= MAX_INPUT -> FUZZ_COST <= v ->
  TSM (JC X v) (fuzz_oneA AAllocAsan data) (fun _ => JC X (v - FUZZ_COST)).
Proof using HLIM.      (* [comment removed for export] *)
  intros X v data HL Hd Hv. unfold fuzz_oneA, HarnessM.fuzz_one. cbn [amalloc afree a_cl a_set_cl AAllocAsan].
  pose proof call_cost_bound as CB. pose proof CINIT_COST_nonneg as C0. pose proof MINIFY_COST_nonneg as M0.
  eapply TSM_bind'; [apply (UC_cinit X v HL); lia|]. intros [].
  eapply TSM_bind'; [apply (UC_minify X (v - CINIT_COST) data HL Hd); lia|]. intros [].
  apply TSM_ret. intros RNG A s mo HJ. split; [exact (JC_acct _ _ _ _ _ _ HJ)|].
  eapply JC_credit; [| exact HJ]. pose proof (JC_nonneg _ _ _ _ _ _ HJ). lia.
Qed.

Local Notation cexitA := (HarnessM.client_exit afree_M aps_cl aset_cl).

Lemma cexit_none : forall s, aps_cl s = None -> cexitA s = mret tt s.
Proof. intros s H. unfold HarnessM.client_exit, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.
Lemma cexit_some : forall s q, aps_cl s = Some q -> cexitA s = (HarnessM.opdelete afree_M q ;;; mupd (aset_cl None)) s.
Proof. intros s q H. unfold HarnessM.client_exit, mbind, mget. cbn. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma UC_cexit : forall X v, TSM (JC X v) (client_exitA AAllocAsan) (fun _ => JC X v).
Proof using HLIM.      (* [comment removed for export] *)
  intros X v RNG A s mo HJ. change (client_exitA AAllocAsan) with cexitA. destruct (aps_cl s) as [q|] eqn:E.
  - rewrite (cexit_some s q E). destruct HJ as [Hv HJ].
    assert (HJ0 : JJ ((q, CLIENT_VEC_BYTES) :: X) (v + COSTF) RNG A s mo) by (unfold clbA, bank in HJ; rewrite E in HJ; exact HJ).
    pose proof COSTF_val as CF. assert (HC : COSTF <= v + COSTF) by lia.
    refine (TSM_bind' NMAX _ _ _ _ _ (U_free NMAX SB PA Abase NLK HLIM X (v + COSTF) q CLIENT_VEC_BYTES) _ RNG A s mo (conj HJ0 HC)).
    intros []. eapply TSM_post; [apply TSM_upd; intros ? ? ? ? HJ'; exact (JJ_acct NMAX SB PA Abase NLK HLIM _ _ _ _ _ _ HJ')|].
    intros [] RNG' A' s'' mo' _ (s' & -> & HJ').
    unfold JC, clbA, bank. destruct s' as [st so rv tp cl]. cbn [aps_cl aset_cl app] in *.
    split; [exact Hv|]. replace (v + 0) with (v + COSTF - COSTF) by lia. apply JJ_cl. exact HJ'.
  - rewrite (cexit_none s E). cbn. split; [exact (JC_acct _ _ _ _ _ _ HJ)|]. exact HJ.
Qed.

End Client.
End CANSEC1.
