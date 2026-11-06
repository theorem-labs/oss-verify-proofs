(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree Stdio HarnessP Adapter Driver ProgA
  AsanCtrl AsanCtrlProps AsanEmbed AsanInv AsanTotal SizeHist AsanProgDeps AsanOK RSimProg MI_Inv LB_Inv LB_Sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Keeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import AProto ATsafeCore ATsafeEv ATsafeAlloc ATsafeOps ATsafeProg.
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
Section Client.
Variable NMAX : nat.
Variables SB PA : Z.
Variable Abase : alw.
Local Notation NMAXZ := (Z.of_nat NMAX).
Hypothesis HLIM : NLK0 + NMAXZ * 4096 <= LIMIT.
Hypothesis ABASE_SH : forall z',
  (shad SB <= z' < shad (SB + K_SPACE_SIZE) \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> Abase (page_base_of z').
Hypothesis HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
Hypothesis HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
Local Notation TSM := (TSM NMAX (St:=APS)).
Local Notation JJ := (JJ NMAX SB PA Abase).

(* [comment removed for export] *)
Definition CLIENT_VEC_BYTES : Z := 8.
(* [comment removed for export] *)
Definition clbA (s : APS) : list (AsanCtrl.aptr * Z) :=
  match aps_cl s with Some q => [(q, CLIENT_VEC_BYTES)] | None => [] end.

Definition JC (X : list (AsanCtrl.aptr * Z)) (v : Z) : preT (St:=APS) :=
  fun RNG A s mo => JJ (clbA s ++ X) v RNG A s mo.

Lemma length_clbA : forall s, (length (clbA s) <= 1)%nat.
Proof. intros s. unfold clbA. destruct (aps_cl s); cbn; lia. Qed.

Lemma JC_acct : forall Y v RNG A s mo, JC Y v RNG A s mo -> acct_ok NMAX RNG A mo.
Proof. intros Y v RNG A s mo H. exact (JJ_acct NMAX SB PA Abase HLIM _ _ _ _ _ _ H). Qed.
Lemma JC_perm : forall Y Y' v RNG A s mo, Permutation Y Y' -> JC Y v RNG A s mo -> JC Y' v RNG A s mo.
Proof. intros Y Y' v RNG A s mo HP H. eapply (JJ_perm NMAX SB PA Abase); [| exact H]. apply Permutation_app_head. exact HP. Qed.
Lemma JC_credit : forall Y v v' RNG A s mo, 0 <= v' <= v -> JC Y v RNG A s mo -> JC Y v' RNG A s mo.
Proof. intros Y v v' RNG A s mo Hv H. exact (JJ_credit NMAX SB PA Abase _ _ _ _ _ _ _ Hv H). Qed.
Lemma JC_nonneg : forall Y v RNG A s mo, JC Y v RNG A s mo -> 0 <= v.
Proof. intros Y v RNG A s mo (_ & _ & _ & _ & _ & Hv & _). exact Hv. Qed.
Lemma JC_io : forall n Y v RNG A s mo rsp mo' evs, io_node n -> nstep n mo rsp mo' evs -> JC Y v RNG A s mo -> JC Y v RNG A s mo'.
Proof. intros n Y v RNG A s mo rsp mo' evs Hio Hst H. exact (JJ_io NMAX SB PA Abase HSB HPA n _ _ _ _ _ _ _ _ _ Hio Hst H). Qed.
Lemma JC_so : forall Y v RNG A s mo w, JC Y v RNG A s mo -> JC Y v RNG A (aset_so w s) mo.
Proof. intros Y v RNG A s mo w H. unfold JC. change (clbA (aset_so w s)) with (clbA s). exact (JJ_so NMAX SB PA Abase _ _ _ _ _ _ w H). Qed.

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

(* [comment removed for export] *)
Lemma UC_malloc : forall Y v n, 0 <= n <= REQMAX -> (length Y <= 2)%nat -> HISTOK (n :: map snd Y) ->
  TSM (fun RNG A s mo => JC Y v RNG A s mo /\ n <= v) (amalloc_M n)
      (fun r RNG A s mo => exists q, r = Some q /\ JC ((q, n) :: Y) (v - n) RNG A s mo /\ n < 2^63).
Proof.
  intros Y v n Hn HL _. intros RNG A s mo [HJ Hnv].
  pose proof (TSM_keeps_cl (fun RNG A s' mo => JJ (clbA s ++ Y) v RNG A s' mo /\ n <= v) (amalloc_M n) _ (aps_cl s)
                (U_malloc NMAX SB PA Abase HLIM ABASE_SH (clbA s ++ Y) v n Hn
                   ltac:(apply HISTOK_amb3; rewrite length_map, length_app; pose proof (length_clbA s); lia))
                (keeps_cl_malloc n)) as H.
  eapply TS_mono; [apply (H RNG A s mo); split; [split; [exact HJ| exact Hnv]| reflexivity]|].
  intros [|[r s']] RNG' A' mo' _ HQ; cbn in HQ |- *; [exact I|].
  destruct HQ as [(q & -> & HJ' & Hlt) E]. exists q. split; [reflexivity|]. split; [| exact Hlt].
  unfold JC. assert (EC : clbA s' = clbA s) by (unfold clbA; rewrite E; reflexivity). rewrite EC.
  eapply (JJ_perm NMAX SB PA Abase); [| exact HJ']. apply Permutation_middle.
Qed.

Lemma UC_free : forall Y v p n, TSM (JC ((p, n) :: Y) v) (afree_M p) (fun _ => JC Y v).
Proof.
  intros Y v p n RNG A s mo HJ.
  pose proof (TSM_keeps_cl (JJ ((p, n) :: clbA s ++ Y) v) (afree_M p) _ (aps_cl s)
                (U_free NMAX SB PA Abase HLIM ABASE_SH (clbA s ++ Y) v p n) (keeps_cl_free p)) as H.
  eapply TS_mono; [apply (H RNG A s mo); split; [| reflexivity]|].
  - eapply (JJ_perm NMAX SB PA Abase); [| exact HJ]. apply Permutation_sym, Permutation_middle.
  - intros [|[r s']] RNG' A' mo' _ HQ; cbn in HQ |- *; [exact I|]. destruct HQ as [HJ' E].
    unfold JC. assert (EC : clbA s' = clbA s) by (unfold clbA; rewrite E; reflexivity). rewrite EC. exact HJ'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma UC_malloc_h : forall Y v n, 0 <= n <= REQMAX -> (forall s, HISTOK (n :: map snd (clbA s ++ Y))) ->
  TSM (fun RNG A s mo => JC Y v RNG A s mo /\ n <= v) (amalloc_M n)
      (fun r RNG A s mo => exists q, r = Some q /\ JC ((q, n) :: Y) (v - n) RNG A s mo /\ n < 2^63).
Proof.
  intros Y v n Hn HH. intros RNG A s mo [HJ Hnv].
  pose proof (TSM_keeps_cl (fun RNG A s' mo => JJ (clbA s ++ Y) v RNG A s' mo /\ n <= v) (amalloc_M n) _ (aps_cl s)
                (U_malloc NMAX SB PA Abase HLIM ABASE_SH (clbA s ++ Y) v n Hn (HH s))
                (keeps_cl_malloc n)) as H.
  eapply TS_mono; [apply (H RNG A s mo); split; [split; [exact HJ| exact Hnv]| reflexivity]|].
  intros [|[r s']] RNG' A' mo' _ HQ; cbn in HQ |- *; [exact I|].
  destruct HQ as [(q & -> & HJ' & Hlt) E]. exists q. split; [reflexivity|]. split; [| exact Hlt].
  unfold JC. assert (EC : clbA s' = clbA s) by (unfold clbA; rewrite E; reflexivity). rewrite EC.
  eapply (JJ_perm NMAX SB PA Abase); [| exact HJ']. apply Permutation_middle.
Qed.

Lemma UC_opnew_h : forall Y v n, 0 < n <= REQMAX -> (forall s, HISTOK (n :: map snd (clbA s ++ Y))) -> n <= v ->
  TSM (JC Y v) (HarnessP.opnew amalloc_M (new_handlerA AAllocAsan) n) (fun p => JC ((p, n) :: Y) (v - n)).
Proof.
  intros Y v n Hn HH Hv. unfold HarnessP.opnew. replace (if n =? 0 then 1 else n) with n by (destruct (Z.eqb_spec n 0); lia).
  eapply TSM_bind'.
  - eapply TSM_pre; [apply (UC_malloc_h Y v n ltac:(lia) HH)|]. intros RNG A s mo HJ. split; [exact HJ| exact Hv].
  - intros [q|]; cbv beta.
    + apply TSM_ret. intros RNG A s mo (q' & Eq & HJ & _). injection Eq as <-. split; [exact (JC_acct _ _ _ _ _ _ HJ)| exact HJ].
    + eapply TSM_pre; [apply TSM_false|]. intros RNG A s mo (q' & Eq & _). discriminate Eq.
Qed.

(* [comment removed for export] *)
Lemma HISTOK_parserA : forall (X C : list (AsanCtrl.aptr * Z)) n s, (length X <= 2)%nat -> (length C <= 8)%nat -> 0 <= n ->
  Forall (fun b => 0 <= snd b) C -> n + zsum (map snd C) <= 2^31 - CLIENT_VEC_BYTES ->
  HISTOK (n :: map snd (clbA s ++ (C ++ X))).
Proof.
  intros X C n s HX HC Hn HF HS. right.
  exists (map snd X), (n :: map snd (clbA s) ++ map snd C). split; [| split; [| split; [| split]]].
  - rewrite !map_app. rewrite app_assoc, app_comm_cons. apply Permutation_app_comm.
  - rewrite length_map. exact HX.
  - cbn [length]. rewrite length_app, !length_map. pose proof (length_clbA s). lia.
  - constructor; [exact Hn|]. apply Forall_app. split.
    + unfold clbA. destruct (aps_cl s); cbn [map snd]; [constructor; [unfold CLIENT_VEC_BYTES; lia| constructor]| constructor].
    + apply Forall_map. exact HF.
  - rewrite zsum_cons, zsum_app. unfold clbA. destruct (aps_cl s); cbn [map snd]; rewrite ?zsum_cons, ?zsum_nil;
      unfold CLIENT_VEC_BYTES in *; lia.
Qed.

Lemma UC_opnew_step : forall X C w n, (length X <= 2)%nat -> (length C <= 7)%nat -> Forall (fun b => 0 <= snd b) C ->
  0 < n <= REQMAX -> n + zsum (map snd C) <= 2^31 - CLIENT_VEC_BYTES -> n <= w ->
  TSM (JC (C ++ X) w) (HarnessP.opnew amalloc_M (new_handlerA AAllocAsan) n) (fun p => JC ((p, n) :: C ++ X) (w - n)).
Proof. intros X C w n HX HC HF Hn HS Hw. apply UC_opnew_h; [exact Hn| | exact Hw]. intros s. apply HISTOK_parserA; auto; lia. Qed.

Lemma UC_free_mid : forall l1 X' w p n, TSM (JC (l1 ++ (p, n) :: X') w) (HarnessP.opdelete afree_M p) (fun _ => JC (l1 ++ X') w).
Proof.
  intros l1 X' w p n. unfold HarnessP.opdelete. eapply TSM_pre; [apply (UC_free (l1 ++ X') w p n)|].
  intros RNG A s mo HJ. eapply JC_perm; [| exact HJ]. apply Permutation_sym, Permutation_middle.
Qed.

(* [comment removed for export] *)
Definition PTOTAL (len : Z) : Z :=
  SB_BYTES len + TAPE_BYTES len + IMPL_BYTES + SIDX_BYTES len + OC_BYTES + ISARR_BYTES + COPY_BYTES len + (len + 64).

Lemma parser_sizesA : forall len, 0 <= len <= MAX_INPUT ->
  0 < SB_BYTES len /\ 0 < TAPE_BYTES len /\ 0 < SIDX_BYTES len /\ 0 < COPY_BYTES len
  /\ PTOTAL len <= 2^31 - CLIENT_VEC_BYTES
  /\ TAPE_BYTES len <= REQMAX /\ SB_BYTES len <= REQMAX /\ SIDX_BYTES len <= REQMAX /\ COPY_BYTES len <= REQMAX
  /\ IMPL_BYTES = 96 /\ OC_BYTES = 8192 /\ ISARR_BYTES = 1024.
Proof.
  intros len H. pose proof (sizes_pos len ltac:(lia)) as P. pose proof (sizes_upper len ltac:(lia)) as U.
  assert (C1 : HarnessP.CAP len <= 2^26) by (unfold HarnessP.CAP, MAX_INPUT in *; lia).
  assert (C2 : HarnessP.CAP len / 3 <= HarnessP.CAP len) by (apply Z.div_le_upper_bound; unfold HarnessP.CAP; lia).
  assert (C3 : 0 <= HarnessP.CAP len / 3) by (apply Z.div_pos; unfold HarnessP.CAP; lia).
  unfold PTOTAL, REQMAX, CLIENT_VEC_BYTES, MAX_INPUT in *. lia.
Qed.

Local Ltac sz_nonneg := repeat (apply Forall_cons; [cbn [snd]; lia|]); apply Forall_nil.
Local Ltac sz_sum := cbn [map snd fst]; rewrite ?zsum_cons, ?zsum_nil; lia.
Local Ltac side := first [ assumption | (cbn [length]; lia) | sz_nonneg | sz_sum | lia | (unfold REQMAX, MAX_INPUT in *; lia) ].
Local Ltac ret_acct := apply TSM_ret; intros ? ? ? ? HJ; split; [exact (JC_acct _ _ _ _ _ _ HJ)|].

(* [comment removed for export] *)
Definition pbJ (len : Z) (X : list (AsanCtrl.aptr * Z)) (w : Z)
    (b : AsanCtrl.aptr * AsanCtrl.aptr * (AsanCtrl.aptr * AsanCtrl.aptr * AsanCtrl.aptr * AsanCtrl.aptr) * option AsanCtrl.aptr) : preT (St:=APS) :=
  let '(sb, tp, (im, si, oc, ia), lb) := b in
  let C := [(ia, ISARR_BYTES); (oc, OC_BYTES); (si, SIDX_BYTES len); (im, IMPL_BYTES); (tp, TAPE_BYTES len); (sb, SB_BYTES len)] in
  match lb with Some l => JC ((l, COPY_BYTES len) :: C ++ X) w | None => JC (C ++ X) w end.

Lemma UC_parse : forall X v data, (length X <= 2)%nat -> zlength data <= MAX_INPUT -> PTOTAL (zlength data) <= v ->
  TSM (JC X v) (HarnessP.parse_into_doc amalloc_M afree_M (new_handlerA AAllocAsan) data)
      (fun b RNG A s mo => exists w, v - PTOTAL (zlength data) <= w /\ pbJ (zlength data) X w b RNG A s mo).
Proof.
  intros X v data HX Hd Hv.
  unfold HarnessP.parse_into_doc, HarnessP.doc_allocate, HarnessP.impl_create, HarnessP.impl_set_capacity,
    HarnessP.impl_set_max_depth, HarnessP.padded_alloc, HarnessP.parse_impl, HarnessP.root_copy.
  cbv zeta. assert (H0 : 0 <= zlength data) by (unfold zlength; lia).
  set (len := zlength data) in *.
  destruct (parser_sizesA len ltac:(lia)) as (P1 & P2 & P3 & P4 & S & R1 & R2 & R3 & R4 & E1 & E2 & E3).
  unfold PTOTAL in S, Hv |- *.
  eapply TSM_bind' with (Q1 := fun d => JC ((snd d, TAPE_BYTES len) :: (fst d, SB_BYTES len) :: X) (v - SB_BYTES len - TAPE_BYTES len)).
  { eapply TSM_bind'; [apply (UC_opnew_step X [] v (SB_BYTES len)); side|]. intros sb.
    eapply TSM_bind'; [apply (UC_opnew_step X [(sb, SB_BYTES len)] (v - SB_BYTES len) (TAPE_BYTES len)); side|]. intros tp.
    ret_acct. exact HJ. }
  intros [sb tp]. cbn [fst snd].
  eapply TSM_bind' with (Q1 := fun i => let '(im, si, oc, ia) := i in
    JC ([(ia, ISARR_BYTES); (oc, OC_BYTES); (si, SIDX_BYTES len); (im, IMPL_BYTES); (tp, TAPE_BYTES len); (sb, SB_BYTES len)] ++ X)
       (v - SB_BYTES len - TAPE_BYTES len - IMPL_BYTES - SIDX_BYTES len - OC_BYTES - ISARR_BYTES)).
  { eapply TSM_bind'; [apply (UC_opnew_step X [(tp, TAPE_BYTES len); (sb, SB_BYTES len)] (v - SB_BYTES len - TAPE_BYTES len) IMPL_BYTES); side|].
    intros im.
    eapply TSM_bind'; [apply (UC_opnew_step X [(im, IMPL_BYTES); (tp, TAPE_BYTES len); (sb, SB_BYTES len)]
                                 (v - SB_BYTES len - TAPE_BYTES len - IMPL_BYTES) (SIDX_BYTES len)); side|]. intros si.
    eapply TSM_bind' with (Q1 := fun o => JC ([(snd o, ISARR_BYTES); (fst o, OC_BYTES); (si, SIDX_BYTES len); (im, IMPL_BYTES);
                                               (tp, TAPE_BYTES len); (sb, SB_BYTES len)] ++ X)
                                            (v - SB_BYTES len - TAPE_BYTES len - IMPL_BYTES - SIDX_BYTES len - OC_BYTES - ISARR_BYTES)).
    { eapply TSM_bind'; [apply (UC_opnew_step X [(si, SIDX_BYTES len); (im, IMPL_BYTES); (tp, TAPE_BYTES len); (sb, SB_BYTES len)]
                                   (v - SB_BYTES len - TAPE_BYTES len - IMPL_BYTES - SIDX_BYTES len) OC_BYTES); side|]. intros oc.
      eapply TSM_bind'; [apply (UC_opnew_step X [(oc, OC_BYTES); (si, SIDX_BYTES len); (im, IMPL_BYTES); (tp, TAPE_BYTES len); (sb, SB_BYTES len)]
                                   (v - SB_BYTES len - TAPE_BYTES len - IMPL_BYTES - SIDX_BYTES len - OC_BYTES) ISARR_BYTES); side|]. intros ia.
      ret_acct. exact HJ. }
    intros [oc ia]. ret_acct. exact HJ. }
  intros [[[im si] oc] ia]. cbv beta iota.
  set (C6 := [(ia, ISARR_BYTES); (oc, OC_BYTES); (si, SIDX_BYTES len); (im, IMPL_BYTES); (tp, TAPE_BYTES len); (sb, SB_BYTES len)]).
  set (w6 := v - SB_BYTES len - TAPE_BYTES len - IMPL_BYTES - SIDX_BYTES len - OC_BYTES - ISARR_BYTES).
  destruct (HarnessP.copy_made len) eqn:CM; cbv beta iota.
  - assert (HC : COPY_BYTES len <= 2^20) by (unfold HarnessP.copy_made, HarnessP.COPY_LIMIT in CM; apply Z.leb_le in CM; exact CM).
    eapply TSM_bind' with (Q1 := fun l => match l with Some a => JC ((a, COPY_BYTES len) :: C6 ++ X) (w6 - COPY_BYTES len)
                                                   | None => fun _ _ _ _ => False end).
    { eapply TSM_bind'; [apply (UC_opnew_step X C6 w6 (COPY_BYTES len)); unfold C6, w6; side|]. intros cp. ret_acct. exact HJ. }
    intros [cp|]; cbv beta iota; [| apply TSM_false].
    eapply TSM_bind' with (Q1 := fun _ RNG A s mo => exists w, w6 - COPY_BYTES len - (len + 64) <= w /\ JC ((cp, COPY_BYTES len) :: C6 ++ X) w RNG A s mo).
    { destruct (SjStage1.root_number_alloc data) as [nr|] eqn:RN; cbv beta iota.
      - pose proof (SjStage1.root_number_alloc_bound data nr RN) as RB.
        assert (RB' : 64 < nr <= len + 64) by (unfold len, zlength; lia).
        eapply TSM_bind'; [apply (UC_opnew_step X ((cp, COPY_BYTES len) :: C6) (w6 - COPY_BYTES len) nr); unfold C6, w6; side|]. intros c.
        eapply TSM_post; [apply (UC_free_mid [] ((cp, COPY_BYTES len) :: C6 ++ X) (w6 - COPY_BYTES len - nr) c nr)|].
        intros [] RNG A s mo _ HJ. exists (w6 - COPY_BYTES len - nr). split; [lia| exact HJ].
      - ret_acct. exists (w6 - COPY_BYTES len). split; [lia| exact HJ]. }
    intros []. apply TSM_exI. intros w. apply TSM_pure'. intros Hw.
    ret_acct. exists w. split; [unfold w6 in Hw; lia| exact HJ].
  - eapply TSM_bind' with (Q1 := fun l => match l with None => JC (C6 ++ X) w6 | Some _ => fun _ _ _ _ => False end).
    { ret_acct. exact HJ. }
    intros [cp|]; cbv beta iota; [apply TSM_false|].
    eapply TSM_bind' with (Q1 := fun _ => JC (C6 ++ X) w6); [ret_acct; exact HJ|].
    intros []. ret_acct. exists w6. split; [unfold w6; lia| exact HJ].
Qed.

Lemma UC_dtor : forall X len w b, TSM (pbJ len X w b) (HarnessP.parser_dtor afree_M b) (fun _ => JC X w).
Proof.
  intros X len w [[[sb tp] [[[im si] oc] ia]] lb].
  unfold HarnessP.parser_dtor, HarnessP.doc_dtor, HarnessP.impl_dtor, pbJ. cbv beta iota zeta.
  eapply TSM_seq with (P1 := JC ([(ia, ISARR_BYTES); (oc, OC_BYTES); (si, SIDX_BYTES len); (im, IMPL_BYTES);
                                 (tp, TAPE_BYTES len); (sb, SB_BYTES len)] ++ X) w).
  { destruct lb as [l|]; cbn [HarnessP.odelete].
    - apply (UC_free_mid [] _ w l (COPY_BYTES len)).
    - ret_acct. exact HJ. }
  intros [].
  eapply TSM_seq with (P1 := JC ([(ia, ISARR_BYTES); (oc, OC_BYTES); (si, SIDX_BYTES len); (im, IMPL_BYTES)] ++ X) w).
  { eapply TSM_seq; [apply (UC_free_mid [(ia, ISARR_BYTES); (oc, OC_BYTES); (si, SIDX_BYTES len); (im, IMPL_BYTES); (tp, TAPE_BYTES len)]
                                        X w sb (SB_BYTES len))|]. intros [].
    apply (UC_free_mid [(ia, ISARR_BYTES); (oc, OC_BYTES); (si, SIDX_BYTES len); (im, IMPL_BYTES)] X w tp (TAPE_BYTES len)). }
  intros [].
  eapply TSM_seq; [apply (UC_free_mid [] _ w ia ISARR_BYTES)|]. intros [].
  eapply TSM_seq; [apply (UC_free_mid [] _ w oc OC_BYTES)|]. intros [].
  eapply TSM_seq; [apply (UC_free_mid [] _ w si (SIDX_BYTES len))|]. intros [].
  apply (UC_free_mid [] X w im IMPL_BYTES).
Qed.

(* [comment removed for export] *)
Lemma UC_fuzz : forall X v data, (length X <= 2)%nat -> zlength data <= MAX_INPUT -> FUZZ_COST <= v ->
  TSM (JC X v) (fuzz_oneA AAllocAsan data) (fun _ => JC X (v - FUZZ_COST)).
Proof using HLIM ABASE_SH.      (* [comment removed for export] *)
  intros X v data HL Hd Hv. unfold fuzz_oneA, HarnessP.fuzz_one. cbn [amalloc afree AAllocAsan].
  assert (H0 : 0 <= zlength data) by (unfold zlength; lia).
  destruct (parser_sizesA (zlength data) ltac:(lia)) as (_ & _ & _ & _ & S & _).
  eapply TSM_bind'; [apply (UC_parse X v data HL Hd); unfold FUZZ_COST, CLIENT_VEC_BYTES in *; lia|]. intros b.
  apply TSM_exI. intros w. apply TSM_pure'. intros Hw.
  eapply TSM_seq; [apply (UC_dtor X (zlength data) w b)|]. intros [].
  ret_acct. eapply JC_credit; [| exact HJ]. pose proof (JC_nonneg _ _ _ _ _ _ HJ). unfold FUZZ_COST, CLIENT_VEC_BYTES in *. lia.
Qed.

(* [comment removed for export] *)
Lemma UC_cexit : forall X v, TSM (JC X v) (client_exitA AAllocAsan) (fun _ => JC X v).
Proof using HLIM ABASE_SH.      (* [comment removed for export] *)
  intros X v. unfold client_exitA, HarnessP.client_exit. ret_acct. exact HJ.
Qed.

End Client.
End CANSEC1.
