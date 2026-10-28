(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ARep ALayout.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition is_sec (ch : achunk) : bool := match ch with CSec _ _ _ => true | CPrim _ _ => false end.
Definition sec_chunks_of (st : astate) : list achunk := List.filter is_sec (achunks st).
Definition sec_mb (ch : achunk) : Z := match ch with CSec mb _ _ => mb | CPrim _ _ => 0 end.
Definition sec_ms (ch : achunk) : Z := match ch with CSec _ ms _ => ms | CPrim _ _ => 0 end.
Definition sec_n (ch : achunk) : Z := match ch with CSec _ _ n => n | CPrim _ n => n end.
Definition SEC_UOFF : Z := 6144.                 (* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_clear (L : alayout) (mb ms : Z) : Prop :=
     (mb + ms <= al_t L \/ al_t L + 4096 <= mb) /\ (mb + ms <= al_ctx L \/ al_ctx L + 65536 <= mb)
  /\ (mb + ms <= al_res L \/ al_res L + 137439023104 <= mb)                 (* [comment removed for export] *)
  /\ (mb + ms <= al_ptr_array L \/ al_ptr_array L + 8388608 <= mb)
  /\ (mb + ms <= al_nodes L \/ al_nodes L + 1048576 <= mb) /\ (mb + ms <= al_store L \/ al_store L + 8388608 <= mb)
  /\ (mb + ms <= al_fake L \/ al_fake L + 11571200 <= mb) /\ (mb + ms <= al_dtls L \/ al_dtls L + 4096 <= mb).
(* [comment removed for export] *)
Definition sec_wf1 (L : alayout) (ch : achunk) : Prop :=
  match ch with
  | CSec mb ms n => mb mod 4096 = 0 /\ ablk mb (mb + ms) /\ mb + ms <= ATOP /\ ms = sec_map_size n     (* [comment removed for export] *)
                   /\ 64512 < n <= AREQMAX /\ is_primary n = false /\ sec_clear L mb ms
  | CPrim _ _ => False
  end.
(* [comment removed for export] *)
Definition RSEC (cs : list achunk) (RNG : footprint) : Prop :=
  Forall (fun ch => rng RNG (sec_mb ch) (sec_ms ch) /\ rng RNG (shad (sec_mb ch)) (sec_ms ch / 8)) cs.

Lemma RSEC_mono : forall cs RNG RNG', fp_le RNG RNG' -> RSEC cs RNG -> RSEC cs RNG'.
Proof.
  intros cs RNG RNG' LE H. unfold RSEC in *. eapply Forall_impl; [| exact H]. cbn. intros ch [A B].
  split; (eapply rng_fp_le; [exact LE | assumption]).
Qed.
Lemma RSEC_perm : forall cs cs' RNG, Permutation cs cs' -> RSEC cs RNG -> RSEC cs' RNG.
Proof. intros cs cs' RNG P H. unfold RSEC in *. rewrite Forall_forall in H |- *. intros x Hx. apply H. eapply Permutation_in; [apply Permutation_sym; exact P | exact Hx]. Qed.
Lemma RSEC_nil : forall RNG, RSEC [] RNG.
Proof. intros. constructor. Qed.

(* [comment removed for export] *)
Lemma sec_chunks_of_eq : forall st st',
  a_live st' = a_live st -> a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st -> sec_chunks_of st' = sec_chunks_of st.
Proof. intros st st' E1 E2 E3. unfold sec_chunks_of, achunks. rewrite E1, E2, E3. reflexivity. Qed.

Lemma filter_is_sec_app : forall l1 l2, List.filter is_sec (l1 ++ l2) = List.filter is_sec l1 ++ List.filter is_sec l2.
Proof. intros. apply List.filter_app. Qed.

(* [comment removed for export] *)
Lemma sec_chunks_of_insert_prim : forall st st' p c n,
  (a_live st) !! p = None ->
  a_live st' = <[p := CPrim c n]> (a_live st) -> a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  Permutation (sec_chunks_of st') (sec_chunks_of st).
Proof.
  intros st st' p c n NONE E1 E2 E3. unfold sec_chunks_of, achunks. rewrite E1, E2, E3, !filter_is_sec_app.
  apply Permutation_app_tail.
  pose proof (map_to_list_insert (a_live st) p (CPrim c n) NONE) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P.
  assert (FP : forall (l l' : list achunk), Permutation l l' -> Permutation (List.filter is_sec l) (List.filter is_sec l')).
  { intros l l' HP. induction HP; cbn; [constructor| | |].
    - destruct (is_sec x); [apply perm_skip|]; assumption.
    - destruct (is_sec x), (is_sec y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
    - eapply Permutation_trans; eassumption. }
  eapply Permutation_trans; [apply FP; exact P|]. cbn. apply Permutation_refl.
Qed.

(* [comment removed for export] *)
Lemma sec_chunks_of_delete_prim : forall st st' p c n,
  (a_live st) !! p = Some (CPrim c n) ->
  a_live st' = delete p (a_live st) ->
  Permutation (List.filter is_sec (flat_map b_chunks (a_qloc st' ++ a_qglob st')))
              (List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))) ->
  Permutation (sec_chunks_of st') (sec_chunks_of st).
Proof.
  intros st st' p c n SOME E1 PQ. unfold sec_chunks_of, achunks. rewrite E1, !filter_is_sec_app.
  apply Permutation_app; [| exact PQ].
  pose proof (map_to_list_delete (a_live st) p (CPrim c n) SOME) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P.
  assert (FP : forall (l l' : list achunk), Permutation l l' -> Permutation (List.filter is_sec l) (List.filter is_sec l')).
  { intros l l' HP. induction HP; cbn; [constructor| | |].
    - destruct (is_sec x); [apply perm_skip|]; assumption.
    - destruct (is_sec x), (is_sec y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
    - eapply Permutation_trans; eassumption. }
  apply FP in P. cbn in P. exact P.
Qed.

(* [comment removed for export] *)
Definition arng (L : alayout) (RNG : footprint) (st : astate) : Prop :=
     rng RNG 0x10000 0x615000                                   (* [comment removed for export] *)
  /\ rng RNG (al_t L) 4096 /\ rng RNG (al_ctx L) 65536
  /\ rng RNG (al_nodes L) 1048576 /\ rng RNG (al_store L) 8388608
  /\ rng RNG (al_space_beg L + K_SPACE_SIZE) K_SPACE_EXTRA             (* [comment removed for export] *)
  /\ rng RNG (al_fake L) 11571200 /\ rng RNG (shad (al_fake L)) (shlen 11571200) /\ rng RNG (al_dtls L) 4096   (* [comment removed for export] *)
  /\ (forall c, 1 <= c < K_NUM_CLASSES ->
        let r := get_cls st c in
           rng RNG (aregion L c) (c_mapped_user r)
        /\ rng RNG (shad (aregion L c)) (shlen (c_mapped_user r))
        /\ rng RNG (afreearr L c) (c_mapped_free_array r)
        /\ rng RNG (shad (afreearr L c)) (shlen (c_mapped_free_array r)))
  (* [comment removed for export] *)
  /\ rng RNG (al_ptr_array L) (8 * a_nres st)
  /\ RSEC (sec_chunks_of st) RNG
  /\ rng RNG (shad (al_space_beg L)) (shlen K_SPACE_SIZE).

Lemma arng_mono : forall L RNG RNG' st, fp_le RNG RNG' -> arng L RNG st -> arng L RNG' st.
Proof.
  intros L RNG RNG' st LE (A1 & A2 & A3 & A4 & A5 & A6 & A6a & A6b & A6c & A7 & A8 & A9 & A10).
  assert (M : forall lo n, rng RNG lo n -> rng RNG' lo n).
  { intros lo n (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|]. intros b j Hb Hj. apply LE. apply R3; assumption. }
  split; [apply M; exact A1|]. split; [apply M; exact A2|]. split; [apply M; exact A3|]. split; [apply M; exact A4|].
  split; [apply M; exact A5|]. split; [apply M; exact A6|]. split; [apply M; exact A6a|]. split; [apply M; exact A6b|]. split; [apply M; exact A6c|].
  split. { intros c Hc. destruct (A7 c Hc) as (B1 & B2 & B3 & B4). split; [apply M; exact B1|]. split; [apply M; exact B2|]. split; [apply M; exact B3| apply M; exact B4]. }
  split; [apply M; exact A8|]. split; [eapply RSEC_mono; [exact LE| exact A9]| apply M; exact A10].
Qed.

(* [comment removed for export] *)
Lemma arng_st : forall L RNG st st',
  (forall c, 1 <= c < K_NUM_CLASSES -> get_cls st' c = get_cls st c) -> a_nres st' = a_nres st ->
  Permutation (sec_chunks_of st') (sec_chunks_of st) ->
  arng L RNG st -> arng L RNG st'.
Proof.
  intros L RNG st st' EC EN P (A1 & A2 & A3 & A4 & A5 & A6 & A6a & A6b & A6c & A7 & A8 & A9 & A10).
  repeat (split; [assumption|]). split.
  { intros c Hc. rewrite (EC c Hc). exact (A7 c Hc). }
  rewrite EN. split; [exact A8|]. split; [eapply RSEC_perm; [apply Permutation_sym; exact P| exact A9]| exact A10].
Qed.

(* [comment removed for export] *)
Definition ablocks (L : alayout) (st : astate) (X : aconc) (LB : list ablock) : Prop :=
     (forall p A n, In (HB p A n) LB ->
           (exists b, In b (x_busy X) /\ xb_st b = BLive p /\ xb_user L b = A /\ xb_n b = n)
        \/ (exists mb ms, (a_live st) !! p = Some (CSec mb ms n) /\ A = mb + SEC_UOFF /\ sec_wf1 L (CSec mb ms n)))
  /\ (forall cls A n, In (mkABlock (ABFake cls) A n) LB -> al_fake L <= A /\ 0 <= n /\ A + n <= al_fake L + 11571200)
  /\ List.NoDup (hb_ids LB)
  /\ List.NoDup LB.

(* [comment removed for export] *)
Lemma ablocks_mono : forall L st st' X X' LB,
  ablocks L st X LB ->
  (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')) ->
  (forall p mb ms n, (a_live st) !! p = Some (CSec mb ms n) -> (a_live st') !! p = Some (CSec mb ms n)) ->
  ablocks L st' X' LB.
Proof.
  intros L st st' X X' LB (B1 & B2 & B3 & B4) HX HL. split; [| split; [exact B2| split; [exact B3| exact B4]]].
  intros p A n Hin. destruct (B1 p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  - left. exists b. split; [exact (HX b p Hb Sb)|]. split; [exact Sb|]. split; [exact Ub| exact Nb].
  - right. exists mb, ms. split; [exact (HL _ _ _ _ Lp)| split; [exact EA| exact G]].
Qed.
Lemma ablocks_same : forall L st st' X X' LB,
  ablocks L st X LB -> x_busy X' = x_busy X -> a_live st' = a_live st -> ablocks L st' X' LB.
Proof. intros L st st' X X' LB B EX EL. eapply ablocks_mono; [exact B| intros b p Hb _; rewrite EX; exact Hb| intros; rewrite EL; assumption]. Qed.
Lemma ablocks_sub : forall L st X LB LB',
  ablocks L st X LB -> (forall b, In b LB' -> In b LB) -> List.NoDup (hb_ids LB') -> List.NoDup LB' -> ablocks L st X LB'.
Proof.
  intros L st X LB LB' (B1 & B2 & B3 & B4) SUB ND1 ND2. split; [| split; [| split; [exact ND1| exact ND2]]].
  - intros p A n Hin. exact (B1 p A n (SUB _ Hin)).
  - intros cls A n Hin. exact (B2 cls A n (SUB _ Hin)).
Qed.

Definition AHEAP_P (H : aholes) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (m : amem) : Prop :=
  alayout_ok L /\ arng L RNG st /\ (exists X, AREP H L st X m /\ ablocks L st X LB) /\ ah_fake H L LB m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition quar_untouched (L : alayout) (X : aconc) (W : list (Z * Z)) : Prop :=
  Forall (fun iv =>
       (snd iv <= al_t L + 80 \/ al_t L + 208 <= fst iv)
    /\ (snd iv <= AINSTANCE + 728 \/ AINSTANCE + 984 <= fst iv)
    /\ (snd iv <= 0xd0f00 \/ 0xd0f00 + 0x81030 <= fst iv)
    /\ (snd iv <= 0x15f788 \/ 0x15f788 + 4 <= fst iv)
    /\ (forall b, In b (x_busy X) -> match xb_st b with BLive _ => True | _ =>
          snd iv <= xb_alloc L b \/ xb_alloc L b + size_of_class (xb_class b) <= fst iv end)) W.
(* [comment removed for export] *)
Definition quar_same (st st' : astate) (X X' : aconc) : Prop :=
     a_qloc st' = a_qloc st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob st' = a_qglob st /\ a_qglob_bytes st' = a_qglob_bytes st
  /\ a_space_beg st' = a_space_beg st
  /\ (forall b, In b (x_busy X) -> match xb_st b with BLive _ => True | _ => In b (x_busy X') end)
  /\ (forall b, In b (x_busy X') -> match xb_st b with BLive _ => True | _ => In b (x_busy X) end).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition aknown (L : alayout) (a : Z) : Prop :=
     ((0 <= a < AIMG_HI /\ ~ (AINSTANCE + 72 <= a < AINSTANCE + 728)) \/ (KLS <= a < shad AIMG_HI) \/ (shad KLS <= a < 0x2008fff7000))
  \/ (shad (al_space_beg L) + 536870912 <= a < shad (al_space_beg L) + 17179869696 (* [comment removed for export] *))
  \/ (shad (al_fake L) <= a < shad (al_fake L) + 1446400)
  \/ (shad ATOP <= a < 0x10007fff8000)
  \/ ATOP <= a
  \/ (al_t L <= a < al_t L + 4096) \/ (al_ctx L <= a < al_ctx L + 65536)
  \/ (al_res L <= a < al_res L + 137439023104 (* [comment removed for export] *))
  \/ (al_nodes L <= a < al_nodes L + 1048576) \/ (al_store L <= a < al_store L + 8388608)
  \/ (al_fake L <= a < al_fake L + 11571200) \/ (al_dtls L <= a < al_dtls L + 4096).
Definition sec_untouched (L : alayout) (W : list (Z * Z)) : Prop :=
  Forall (fun iv => forall a, fst iv <= a < snd iv -> aknown L a) W.
Definition sec_same (st st' : astate) : Prop :=
     a_nsec st' = a_nsec st /\ a_nres st' = a_nres st /\ a_ptr_array st' = a_ptr_array st
  /\ (forall p mb ms n, (a_live st') !! p = Some (CSec mb ms n) <-> (a_live st) !! p = Some (CSec mb ms n))
  /\ Permutation (sec_chunks_of st') (sec_chunks_of st).                  (* [comment removed for export] *)
Lemma sec_same_refl : forall st, sec_same st st.
Proof. intros st. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; tauto| apply Permutation_refl]. Qed.

(* [comment removed for export] *)
Definition fake_untouched (L : alayout) (W : list (Z * Z)) : Prop :=
  Forall (fun iv => (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
                 /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
                 /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
                 /\ (snd iv <= 0xc90f0 \/ 0xc90f0 + 8 <= fst iv)
                 /\ (snd iv <= 0x602ca8 \/ 0x602ca8 + 16 <= fst iv)
                 /\ (snd iv <= 0x602cb8 \/ 0x602cb8 + 8 <= fst iv)
                 /\ (snd iv <= 0x602cd8 \/ 0x602cd8 + 8 <= fst iv)
                 /\ (snd iv <= 0x1618b1 \/ 0x1618b1 + 1 <= fst iv)
                 /\ (snd iv <= 0x15f798 \/ 0x15f798 + 4 <= fst iv)) W.

Record ahole_laws (H : aholes) : Prop := mkAHL {
  hq_frame : forall L st st' X X' m m' W,
      ah_quar H L st X m -> munch W m m' -> wmono bsegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
      ah_quar H L st' X' m';
  hs_frame : forall L st st' X X' m m' W,
      ah_sec H L st X m -> munch W m m' -> wmono bsegs m m' -> sec_untouched L W -> sec_same st st' ->
      ah_sec H L st' X' m';
  hd_frame : forall L m m' W,
      ah_depot H L m -> munch W m m' -> wmono bsegs m m' ->
      Forall (fun iv => forall a, fst iv <= a < snd iv ->
                           ~ (0x1a1bc8 <= a < 0x5f1c10) /\ ~ (al_nodes L <= a < al_nodes L + 1048576)
                           /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
      ah_depot H L m';                                  (* [comment removed for export] *)
  hf_frame : forall L LB m m' W,
      ah_fake H L LB m -> munch W m m' -> wmono bsegs m m' -> fake_untouched L W -> ah_fake H L LB m';
  hf_blocks : forall L LB LB' m,
      ah_fake H L LB m -> (forall c F n, In (mkABlock (ABFake c) F n) LB' <-> In (mkABlock (ABFake c) F n) LB) ->
      ah_fake H L LB' m
}.
End CANSEC1.
(* [comment removed for export] *)
