(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs Lept_iface Lept_env LeptC_kit LeptL_kit Lept_objkit Gm_iface Fh_iface Fh_sel_iface LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma rw_cells_C8s_u64arr : forall (mm : mem) A (ws : list word), rw_cells asegs mm A (map C8 ws) -> u64arr asegs mm A ws.
Proof.
  intros mm A ws [[_ HB] HW]. split.
  - replace (u64s ws) with (cells_bytes (map C8 ws)); [exact HB|]. clear. induction ws as [|w ws IH]; [reflexivity|].
    cbn [map cells_bytes cbytes u64s]. rewrite IH. reflexivity.
  - replace (8 * Z.of_nat (length ws)) with (Z.of_nat (cells_size (map C8 ws))); [exact HW|]. clear. induction ws as [|w ws IH]; [reflexivity|].
    cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IH. lia.
Qed.

Lemma C8s_cells : forall ws : list word, cells_wf (map C8 ws) /\ cells_bytes (map C8 ws) = u64s ws /\ Z.of_nat (cells_size (map C8 ws)) = 8 * Z.of_nat (length ws).
Proof.
  induction ws as [|w ws (IH1 & IH2 & IH3)]; [repeat split|]. cbn [map cells_wf cell_wf cells_bytes cbytes u64s cells_size csize length].
  split; [split; [exact I| exact IH1]|]. split; [rewrite IH2; reflexivity|]. rewrite Nat2Z.inj_add, IH3. lia.
Qed.
Lemma u64arr_rw_cells_C8s : forall (mm : mem) A (ws : list word), u64arr asegs mm A ws -> rw_cells asegs mm A (map C8 ws).
Proof.
  intros mm A ws [HB HW]. destruct (C8s_cells ws) as (W1 & W2 & W3). split; [split; [exact W1| rewrite W2; exact HB]| rewrite W3; exact HW].
Qed.

(* [comment removed for export] *)
Lemma u64s_exists : forall (k : nat) (bs : list byte), length bs = (8 * k)%nat -> exists ws : list word, u64s ws = bs /\ length ws = k.
Proof.
  induction k as [|k IH]; intros bs L.
  - destruct bs; [exists []; split; reflexivity| discriminate].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 rest]]]]]]]]; cbn [length] in L; try lia.
    destruct (IH rest ltac:(lia)) as (ws & E & Lw).
    exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7]) :: ws). split; [| cbn [length]; lia].
    cbn [u64s]. rewrite E. change (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) with ([b0; b1; b2; b3; b4; b5; b6; b7] ++ rest). f_equal.
    change (Mem.le8 ?v) with (le8 v).
    unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite (Z_to_le_bytes_mod 8 _ 64) by lia. exact (le_bytes_roundtrip [b0; b1; b2; b3; b4; b5; b6; b7]).
Qed.
Lemma u8arr_u64arr : forall (m : mem) A bs (k : Z), u8arr asegs m A bs -> Z.of_nat (length bs) = 8 * k ->
  exists ws : list word, u64arr asegs m A ws /\ Z.of_nat (length ws) = k.
Proof.
  intros m A bs k [Hb Hw] L. destruct (u64s_exists (Z.to_nat k) bs ltac:(lia)) as (ws & E & Lw).
  exists ws. split; [| lia]. split; [rewrite E; exact Hb|]. replace (8 * Z.of_nat (length ws)) with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma u64arr_agree : forall (P : Z -> Prop) (m m' : mem) A (ws : list word), u64arr asegs m A ws -> agree_on P m m' ->
  (forall x, A <= x < A + 8 * Z.of_nat (length ws) -> P x) -> u64arr asegs m' A ws.
Proof.
  intros P m m' A ws [HB HW] AG HP. split.
  - apply (bytes_at_agree asegs m m' A _ HB). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx. apply HP. rewrite u64s_length in Hx. lia.
  - apply (wr_at_agree_nw asegs m m' A _ HW). eapply agree_sub; [exact AG|]. exact HP.
Qed.

(* [comment removed for export] *)
Lemma firstn_upd_snoc : forall (X : Type) (l : list X) (n : nat) (v : X), (n < length l)%nat -> firstn (S n) (upd l n v) = firstn n l ++ [v].
Proof.
  induction l as [|h t IH]; intros n v Hn; [cbn in Hn; lia|]. destruct n as [|n]; [reflexivity|]. cbn [upd].
  change (firstn (S (S n)) (h :: upd t n v)) with (h :: firstn (S n) (upd t n v)). rewrite IH by (cbn in Hn; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Ltac arr_sd A idx E :=
  lazymatch goal with
  | UA : u64arr asegs ?mm A ?ws, UAL : Z.of_nat (length ?ws) = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws idx (wa E) UA ltac:(lia) ltac:(f_equal; lia)) as SOK;
    zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm (Z_to_bv 64 ?E') (le8 ?v)) _) =>
      let N := fresh "UA" in
      assert (N : u64arr asegs (write_to_mem mm (wa E') (le8 v)) A (upd ws (Z.to_nat idx) v))
        by (replace E' with (A + 8 * idx) by lia; apply (u64arr_write asegs mm A ws idx v UA); lia);
      clear UA; store_done; rename N into UA
    end
  end.

(* [comment removed for export] *)
Ltac shbr8_zero :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?SLOW else Z_to_bv 64 ?FAST) ?fc ?rv ?m ?ro) =>
      let b := shbyte_of c in
      lazymatch goal with
      | K : shk m b ?X |- _ =>
          let OK := fresh "SHOK" in
          first [ match goal with ACC : acc asegs m ?a ?n |- _ =>
                    assert (OK : sh_ok b (X + 8 - 1)) by (apply (shk_ok m a n X 8 b ACC K); lia) end
                | fail 1 "shbr8_zero: cannot prove the 8-byte access addressable:" X ];
          apply sh_ok_8 in OK; [ | lia ];
          rewrite ?(sxb_small b) by lia;
          rewrite ?OK; brF; clear K OK
      end
  end.

(* [comment removed for export] *)
Section SelKitRT.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma new_chunks_apart : forall Σ' (m : mem) newl live0 frs usp,
  ART RT Σ' m -> rt_live RT Σ' = newl ++ live0 -> rt_frames RT Σ' = frs -> rt_sp0 RT Σ' - STACK_WIN <= usp ->
  forall p n a, In (p, n) newl -> aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ' m newl live0 frs usp HA LV FRS SPL p n a HIn Ha.
  assert (INL : In (p, n) (rt_live RT Σ')) by (rewrite LV; apply in_or_app; left; exact HIn).
  pose proof (af_live_range RT AF Σ' m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp).
    destruct (in_split _ _ HIn) as (l1 & l2 & E).
    assert (LV' : rt_live RT Σ' = l1 ++ (p, n) :: (l2 ++ live0)) by (rewrite LV, E, <- app_assoc; reflexivity).
    assert (Hin' : In (p', n') (l1 ++ (l2 ++ live0))) by (apply in_or_app; right; apply in_or_app; right; exact Hin).
    pose proof (af_live_disj RT AF Σ' m p n p' n' l1 (l2 ++ live0) HA LV' Hin') as D. lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF Σ' m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF Σ' m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.

(* [comment removed for export] *)
Lemma new_chunks_disj : forall Σ' (m : mem) l1 p n l2, ART RT Σ' m -> rt_live RT Σ' = l1 ++ (p, n) :: l2 ->
  forall q k, In (q, k) (l1 ++ l2) -> p + n <= q \/ q + k <= p.
Proof using AF. intros Σ' m l1 p n l2 HA LV q k Hin. exact (af_live_disj RT AF Σ' m p n q k l1 l2 HA LV Hin). Qed.
(* [comment removed for export] *)
Lemma live_addr_disj : forall Σ' (m : mem) p n q k, ART RT Σ' m -> In (p, n) (rt_live RT Σ') -> In (q, k) (rt_live RT Σ') -> p <> q ->
  p + n <= q \/ q + k <= p.
Proof using AF.
  intros Σ' m p n q k HA Hp Hq NE. destruct (in_split _ _ Hp) as (l1 & l2 & E).
  apply (af_live_disj RT AF Σ' m p n q k l1 l2 HA E). rewrite E in Hq. apply in_app_or in Hq. apply in_or_app.
  destruct Hq as [Hq|[Hq|Hq]]; [left; exact Hq| injection Hq as E1 _; congruence| right; exact Hq].
Qed.

(* [comment removed for export] *)
Lemma live_nodup_seg : forall Σ' (m : mem) seg pre post, ART RT Σ' m -> rt_live RT Σ' = pre ++ seg ++ post ->
  (forall p n, In (p, n) seg -> 0 < n) -> List.NoDup (map fst seg).
Proof using AF.
  intros Σ' m seg. induction seg as [|[p n] t IH]; intros pre post HA LV POS; [constructor|].
  cbn [map fst]. constructor.
  - intros Hin. apply in_map_iff in Hin as ([p' n'] & E & Hin). cbn [fst] in E. subst p'.
    pose proof (af_live_disj RT AF Σ' m p n p n' pre (t ++ post) HA LV ltac:(apply in_or_app; right; apply in_or_app; left; exact Hin)) as D.
    pose proof (POS p n ltac:(left; reflexivity)). pose proof (POS p n' ltac:(right; exact Hin)). lia.
  - apply (IH (pre ++ [(p, n)]) post HA); [rewrite LV, <- app_assoc; reflexivity| intros q k Hq; apply (POS q k); right; exact Hq].
Qed.
(* [comment removed for export] *)
Lemma live_segs_disj : forall Σ' (m : mem) P A B C, ART RT Σ' m -> rt_live RT Σ' = P ++ A ++ B ++ C ->
  forall p n q k, In (p, n) A -> In (q, k) B -> p + n <= q \/ q + k <= p.
Proof using AF.
  intros Σ' m P A B C HA LV p n q k Hp Hq. destruct (in_split _ _ Hp) as (a1 & a2 & E).
  apply (af_live_disj RT AF Σ' m p n q k (P ++ a1) (a2 ++ B ++ C) HA).
  - rewrite LV, E, <- !app_assoc. reflexivity.
  - apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hq.
Qed.
(* [comment removed for export] *)
Lemma live_nodup_all : forall Σ' (m : mem), ART RT Σ' m -> (forall p n, In (p, n) (rt_live RT Σ') -> 0 < n) -> List.NoDup (map fst (rt_live RT Σ')).
Proof using AF.
  intros Σ' m HA POS. apply (live_nodup_seg Σ' m (rt_live RT Σ') [] [] HA); [rewrite app_nil_r; reflexivity| exact POS].
Qed.
End SelKitRT.

(* [comment removed for export] *)
Lemma tl_sel_live : forall sel v,
  tl (sel_live sel v) = rev (map (fun r => (r, 4 * s_sx v)) (s_rows v)) ++ [(s_data v, 8 * s_sy v); (sel, 32)].
Proof. reflexivity. Qed.
Lemma row_in_sel_live : forall sel v r, In r (s_rows v) -> In (r, 4 * s_sx v) (tl (sel_live sel v)).
Proof. intros sel v r Hr. rewrite tl_sel_live. apply in_or_app. left. apply -> in_rev. apply (in_map (fun r => (r, 4 * s_sx v))). exact Hr. Qed.
Lemma data_in_sel_live : forall sel v, In (s_data v, 8 * s_sy v) (tl (sel_live sel v)).
Proof. intros sel v. rewrite tl_sel_live. apply in_or_app. right. left. reflexivity. Qed.
Lemma sel_in_sel_live : forall sel v, In (sel, 32) (tl (sel_live sel v)).
Proof. intros sel v. rewrite tl_sel_live. apply in_or_app. right. right. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sel_body_pos : forall (live : list (Z * Z)) (m : mem) sel v, sel_body live m sel v -> forall p n, In (p, n) (tl (sel_live sel v)) -> 0 < n.
Proof.
  intros live m sel v (_ & (_ & _ & _ & PS) & _ & _ & _ & _ & (_ & _ & _ & PD) & ROWS & _) p n Hin.
  rewrite tl_sel_live in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[E|[E|[]]]]; try (injection E as _ <-; assumption).
  apply in_rev in Hin. apply in_map_iff in Hin as (r & E & Hr). injection E as _ <-.
  exact (proj2 (proj2 (proj2 (proj1 (Forall_forall _ _) ROWS r Hr)))).
Qed.
Lemma sel_obj_pos : forall (live : list (Z * Z)) (m : mem) sel v nm, sel_obj live m sel v nm -> forall p n, In (p, n) (sel_live sel v) -> 0 < n.
Proof.
  intros live m sel v nm (SB & _ & _ & _) p n [E|Hin]; [injection E as _ <-; lia| exact (sel_body_pos live m sel v SB p n Hin)].
Qed.

(* [comment removed for export] *)
Lemma cells_size_C8map : forall (X : Type) (f : X -> word) (l : list X), Z.of_nat (cells_size (map (fun e => C8 (f e)) l)) = 8 * Z.of_nat (length l).
Proof. intros X f l. induction l as [|e l IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IH. lia. Qed.
Lemma cells_size_C8rep : forall (z : word) (k : nat), Z.of_nat (cells_size (repeat (C8 z) k)) = 8 * Z.of_nat k.
Proof. intros z k. induction k as [|k IH]; [reflexivity|]. cbn [repeat cells_size csize]. rewrite Nat2Z.inj_add, IH. lia. Qed.

Lemma chunk_mono : forall (live live' : list (Z * Z)) p n, chunk live p n -> (forall e, In e live -> In e live') -> chunk live' p n.
Proof. intros live live' p n (H1 & H2) SUB. split; [apply SUB; exact H1| exact H2]. Qed.

Lemma sel_body_agree : forall (live live' : list (Z * Z)) (m m' : mem) sel v, sel_body live m sel v -> (forall e, In e live -> In e live') ->
  agree_on (in_live (tl (sel_live sel v))) m m' -> sel_body live' m' sel v.
Proof.
  intros live live' m m' sel v (SC & CS & HSY & HSX & HLEN & DC & CD & ROWS & ND) SUB AG.
  split; [| split; [exact (chunk_mono _ _ _ _ CS SUB)| split; [exact HSY| split; [exact HSX| split; [exact HLEN| split; [| split; [exact (chunk_mono _ _ _ _ CD SUB)| split; [| exact ND]]]]]]]].
  - apply (rw_cells_agree_nw asegs m m' sel _ SC). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
    exists sel, 32. split; [apply sel_in_sel_live| exact Hx].
  - apply (rw_cells_agree_nw asegs m m' (s_data v) _ DC). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
    rewrite (cells_size_C8map Z (Z_to_bv 64) (s_rows v)) in Hx. exists (s_data v), (8 * s_sy v). split; [apply data_in_sel_live| lia].
  - eapply Forall_impl; [| exact ROWS]. intros r Hr. exact (chunk_mono _ _ _ _ Hr SUB).
Qed.

Lemma in_live_tl_sel_live : forall sel v x, in_live (tl (sel_live sel v)) x -> in_live (sel_live sel v) x.
Proof. intros sel v x (p & n & Hin & Hx). exists p, n. split; [right; exact Hin| exact Hx]. Qed.

Lemma sel_obj_agree : forall (live live' : list (Z * Z)) (m m' : mem) sel v nm, sel_obj live m sel v nm -> (forall e, In e live -> In e live') ->
  agree_on (in_live (sel_live sel v)) m m' -> sel_obj live' m' sel v nm.
Proof.
  intros live live' m m' sel v nm (SB & NB & CN & NL) SUB AG.
  split; [| split; [| split; [exact (chunk_mono _ _ _ _ CN SUB)| exact NL]]].
  - apply (sel_body_agree live live' m m' sel v SB SUB). eapply agree_sub; [exact AG|]. exact (in_live_tl_sel_live sel v).
  - apply (bytes_at_agree asegs m m' (s_name v) nm NB). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
    exists (s_name v), 8. split; [left; reflexivity| rewrite NL in Hx; lia].
Qed.

Lemma sel_live_in_sela_live : forall sela arr sels e x, In e sels -> in_live (sel_live (fst (fst e)) (snd (fst e))) x -> in_live (sela_live sela arr sels) x.
Proof.
  intros sela arr sels e x He (p & n & Hin & Hx). exists p, n. split; [| exact Hx]. unfold sela_live. apply in_or_app. left.
  apply in_flat_map. exists e. split; [apply -> in_rev; exact He| exact Hin].
Qed.

Lemma sela_obj_agree : forall (live live' : list (Z * Z)) (m m' : mem) sela arr sels, sela_obj live m sela arr sels -> (forall e, In e live -> In e live') ->
  agree_on (in_live (sela_live sela arr sels)) m m' -> sela_obj live' m' sela arr sels.
Proof.
  intros live live' m m' sela arr sels (SAC & CS & CA & L50 & ARRC & SELS) SUB AG.
  split; [| split; [exact (chunk_mono _ _ _ _ CS SUB)| split; [exact (chunk_mono _ _ _ _ CA SUB)| split; [exact L50| split]]]].
  - apply (rw_cells_agree_nw asegs m m' sela _ SAC). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
    exists sela, 16. split; [unfold sela_live; apply in_or_app; right; right; left; reflexivity| exact Hx].
  - apply (rw_cells_agree_nw asegs m m' arr _ ARRC). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
    rewrite cells_size_app, Nat2Z.inj_add, (cells_size_C8map _ (fun e => Z_to_bv 64 (fst (fst e))) sels), cells_size_C8rep in Hx.
    exists arr, 400. split; [unfold sela_live; apply in_or_app; right; left; reflexivity| lia].
  - apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) SELS e He) as SO.
    apply (sel_obj_agree live live' m m' _ _ _ SO SUB). eapply agree_sub; [exact AG|]. intros x. exact (sel_live_in_sela_live sela arr sels e x He).
Qed.

(* [comment removed for export] *)
Lemma sela_live_snoc : forall sela arr sels sel v nm,
  sela_live sela arr (sels ++ [(sel, v, nm)]) = sel_live sel v ++ sela_live sela arr sels.
Proof. intros. unfold sela_live. rewrite rev_app_distr. cbn [rev app flat_map fst snd]. rewrite <- app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Lemma upd_app_len : forall (X : Type) (l1 l2 : list X) (v : X), l2 <> [] -> upd (l1 ++ l2) (length l1) v = l1 ++ v :: tl l2.
Proof.
  intros X l1. induction l1 as [|h t IH]; intros l2 v NE; [destruct l2; [contradiction| reflexivity]|].
  cbn [app length upd]. rewrite IH by exact NE. reflexivity.
Qed.

(* [comment removed for export] *)
Definition memz (p : Z) (ps : list Z) : bool := existsb (Z.eqb p) ps.
Lemma memz_In : forall p ps, memz p ps = true <-> In p ps.
Proof.
  intros p ps. unfold memz. rewrite existsb_exists. split.
  - intros (x & Hx & E). apply Z.eqb_eq in E. subst x. exact Hx.
  - intros H. exists p. split; [exact H| apply Z.eqb_refl].
Qed.

(* [comment removed for export] *)
Lemma live_remove_head : forall p n (l : list (Z * Z)), live_remove p ((p, n) :: l) = live_remove p l.
Proof.
  intros p n l. unfold live_remove. apply stdpp.list_basics.list.filter_cons_False. cbn [fst]. rewrite Z.eqb_refl. cbn. tauto.
Qed.
Lemma live_remove_other : forall p q n (l : list (Z * Z)), q <> p -> live_remove p ((q, n) :: l) = (q, n) :: live_remove p l.
Proof.
  intros p q n l NE. unfold live_remove. apply stdpp.list_basics.list.filter_cons_True. cbn [fst].
  replace (q =? p) with false by (symmetry; apply Z.eqb_neq; exact NE). exact I.
Qed.
Lemma live_remove_List : forall p (l : list (Z * Z)), live_remove p l = List.filter (fun e => negb (fst e =? p)) l.
Proof.
  intros p l. induction l as [|[q n] l IH]; [reflexivity|]. cbn [List.filter fst].
  destruct (Z.eqb_spec q p) as [->|NE]; cbn [negb]; [rewrite live_remove_head; exact IH| rewrite live_remove_other by exact NE; f_equal; exact IH].
Qed.
Lemma live_remove_all_filter : forall ps l, live_remove_all ps l = List.filter (fun e => negb (memz (fst e) ps)) l.
Proof.
  induction ps as [|p ps IH]; intros l; unfold live_remove_all; cbn [fold_left].
  - induction l as [|e l IHl]; [reflexivity|]. cbn [List.filter memz existsb negb]. f_equal. exact IHl.
  - change (fold_left (fun l0 p0 => live_remove p0 l0) ps (live_remove p l)) with (live_remove_all ps (live_remove p l)).
    rewrite IH, live_remove_List. induction l as [|e l IHl]; [reflexivity|].
    cbn [List.filter memz existsb]. destruct (Z.eqb_spec (fst e) p) as [E|NE]; cbn [negb orb].
    + exact IHl.
    + cbn [List.filter]. fold (memz (fst e) ps). destruct (memz (fst e) ps); cbn [negb]; [exact IHl| f_equal; exact IHl].
Qed.

Lemma filter_all_false : forall (A : Type) (f : A -> bool) l, (forall e, In e l -> f e = false) -> List.filter f l = [].
Proof. intros A f l. induction l as [|e l IH]; intros H; [reflexivity|]. cbn. rewrite (H e (or_introl eq_refl)). apply IH. intros x Hx. apply H. right. exact Hx. Qed.
Lemma filter_all_true : forall (A : Type) (f : A -> bool) l, (forall e, In e l -> f e = true) -> List.filter f l = l.
Proof. intros A f l. induction l as [|e l IH]; intros H; [reflexivity|]. cbn. rewrite (H e (or_introl eq_refl)). f_equal. apply IH. intros x Hx. apply H. right. exact Hx. Qed.

Lemma nodup_app_disj : forall (A : Type) (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros A l1 l2 x. induction l1 as [|y l1 IH]; intros ND H1 H2; [destruct H1|].
  cbn in ND. inversion ND as [|z zs NI ND']; subst. destruct H1 as [->|H1]; [apply NI, in_or_app; right; exact H2| exact (IH ND' H1 H2)].
Qed.

(* [comment removed for export] *)
Lemma live_remove_all_mid : forall ps (l1 mid l2 : list (Z * Z)),
  List.NoDup (map fst (l1 ++ mid ++ l2)) -> (forall p, In p ps <-> In p (map fst mid)) ->
  live_remove_all ps (l1 ++ mid ++ l2) = l1 ++ l2.
Proof.
  intros ps l1 mid l2 ND EQ. rewrite live_remove_all_filter, !List.filter_app.
  rewrite !map_app in ND.
  assert (OUT : forall e, In e l1 \/ In e l2 -> memz (fst e) ps = false).
  { intros e He. destruct (memz (fst e) ps) eqn:M; [| reflexivity]. exfalso.
    apply memz_In in M. apply EQ in M.
    destruct He as [He|He].
    - apply (nodup_app_disj _ _ _ (fst e) ND); [apply in_map; exact He| apply in_or_app; left; exact M].
    - apply List.NoDup_app_remove_l in ND. apply (nodup_app_disj _ _ _ (fst e) ND); [exact M| apply in_map; exact He]. }
  rewrite (filter_all_true _ _ l1) by (intros e He; rewrite (OUT e (or_introl He)); reflexivity).
  rewrite (filter_all_true _ _ l2) by (intros e He; rewrite (OUT e (or_intror He)); reflexivity).
  rewrite (filter_all_false _ _ mid); [reflexivity|].
  intros e He. assert (M : memz (fst e) ps = true) by (apply memz_In, EQ, in_map; exact He). rewrite M. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sel_frees_live : forall sel v p, In p (sel_frees sel v) <-> In p (map fst (sel_live sel v)).
Proof.
  intros sel v p. unfold sel_frees, sel_live. cbn [map fst]. rewrite map_app, map_rev, map_map. cbn [map fst].
  replace (map (fun x : Z => x) (s_rows v)) with (s_rows v) by (symmetry; apply map_id).
  rewrite in_app_iff. cbn [In]. rewrite in_app_iff, <- in_rev. cbn [In].
  intuition.
Qed.
Lemma sela_frees_live : forall sela arr sels p, In p (sela_frees sela arr sels) <-> In p (map fst (sela_live sela arr sels)).
Proof.
  intros sela arr sels p. unfold sela_frees, sela_live. rewrite map_app, !in_app_iff. cbn [map fst In].
  assert (E : In p (flat_map (fun e => sel_frees (fst (fst e)) (snd (fst e))) sels)
              <-> In p (map fst (flat_map (fun e => sel_live (fst (fst e)) (snd (fst e))) (rev sels)))).
  { rewrite in_flat_map, in_map_iff. split.
    - intros (e & He & Hp). apply sel_frees_live in Hp. apply in_map_iff in Hp. destruct Hp as (c & Ec & Hc).
      exists c. split; [exact Ec|]. apply in_flat_map. exists e. split; [apply -> in_rev; exact He| exact Hc].
    - intros (c & Ec & Hc). apply in_flat_map in Hc. destruct Hc as (e & He & Hc). exists e. split; [apply in_rev; exact He|].
      apply sel_frees_live. apply in_map_iff. exists c. split; assumption. }
  tauto.
Qed.

(* [comment removed for export] *)
Theorem sela_destroy_live : forall sela arr sels (l1 l2 : list (Z * Z)),
  List.NoDup (map fst (l1 ++ sela_live sela arr sels ++ l2)) ->
  live_remove_all (sela_frees sela arr sels) (l1 ++ sela_live sela arr sels ++ l2) = l1 ++ l2.
Proof. intros sela arr sels l1 l2 ND. apply live_remove_all_mid; [exact ND| intros p; apply sela_frees_live]. Qed.

(* [comment removed for export] *)
Lemma live_remove_all_In : forall ps (l : list (Z * Z)) x, In x (live_remove_all ps l) <-> In x l /\ ~ In (fst x) ps.
Proof.
  intros ps l x. rewrite live_remove_all_filter, filter_In. split; intros [H1 H2]; (split; [exact H1|]).
  - intros HI. apply memz_In in HI. rewrite HI in H2. discriminate.
  - destruct (memz (fst x) ps) eqn:M; [apply memz_In in M; contradiction| reflexivity].
Qed.
Lemma live_remove_all_app : forall a b (l : list (Z * Z)), live_remove_all (a ++ b) l = live_remove_all b (live_remove_all a l).
Proof. intros a b l. unfold live_remove_all. apply fold_left_app. Qed.
Lemma live_remove_all_snoc : forall ps p (l : list (Z * Z)), live_remove_all (ps ++ [p]) l = live_remove p (live_remove_all ps l).
Proof. intros ps p l. rewrite live_remove_all_app. reflexivity. Qed.

Lemma firstn_S_nth : forall (l : list Z) (i : nat) d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  induction l as [|h t IH]; intros i d Hi; [cbn in Hi; lia|]. destruct i as [|i]; [reflexivity|].
  cbn [firstn nth app]. f_equal. apply IH. cbn in Hi. lia.
Qed.
Lemma nodup_nth_notin_firstn : forall (l : list Z) (i : nat) d, List.NoDup l -> (i < length l)%nat -> ~ In (nth i l d) (firstn i l).
Proof.
  induction l as [|h t IH]; intros i d ND Hi; [cbn in Hi; lia|]. inversion ND as [|x xs NI ND']; subst.
  destruct i as [|i]; [intros []|]. cbn [firstn nth]. intros [E|Hin].
  - apply NI. rewrite E. apply nth_In. cbn in Hi. lia.
  - exact (IH i d ND' ltac:(cbn in Hi; lia) Hin).
Qed.

Lemma sel_live_nodup_facts : forall sel v, List.NoDup (map fst (sel_live sel v)) ->
  List.NoDup (s_rows v) /\ ~ In (s_data v) (s_rows v) /\ ~ In sel (s_rows v) /\ ~ In (s_name v) (s_rows v)
  /\ s_data v <> sel /\ s_name v <> s_data v /\ s_name v <> sel.
Proof.
  intros sel v ND. unfold sel_live in ND. cbn [map fst] in ND. rewrite map_app, map_rev, map_map in ND. cbn [map fst] in ND.
  change (map (fun x : Z => fst (x, 4 * s_sx v)) (s_rows v)) with (map (fun x : Z => x) (s_rows v)) in ND. rewrite map_id in ND.
  apply NoDup_cons_iff in ND as (NN & ND).
  assert (NR : List.NoDup (rev (s_rows v))) by (exact (NoDup_app_remove_r _ _ ND)).
  assert (ND2 : List.NoDup [s_data v; sel]) by (exact (NoDup_app_remove_l _ _ ND)).
  split; [rewrite <- (rev_involutive (s_rows v)); apply NoDup_rev; exact NR|].
  split; [intros H; apply (nodup_app_disj _ _ _ (s_data v) ND); [apply -> in_rev; exact H| left; reflexivity]|].
  split; [intros H; apply (nodup_app_disj _ _ _ sel ND); [apply -> in_rev; exact H| right; left; reflexivity]|].
  split; [intros H; apply NN; apply in_or_app; left; apply -> in_rev; exact H|].
  split; [intros E; apply NoDup_cons_iff in ND2 as (N1 & _); apply N1; left; symmetry; exact E|].
  split; [intros E; apply NN; apply in_or_app; right; left; symmetry; exact E|].
  intros E; apply NN; apply in_or_app; right; right; left; symmetry; exact E.
Qed.
Lemma in_firstn : forall (X : Type) (l : list X) (n : nat) (x : X), In x (firstn n l) -> In x l.
Proof. intros X l n x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

(* [comment removed for export] *)
Lemma sel_body_agree2 : forall (live live' : list (Z * Z)) (m m' : mem) sel v, sel_body live m sel v ->
  (forall e, In e (tl (sel_live sel v)) -> In e live') -> agree_on (in_live (tl (sel_live sel v))) m m' -> sel_body live' m' sel v.
Proof.
  intros live live' m m' sel v (SC & (_ & CS) & HSY & HSX & HLEN & DC & (_ & CD) & ROWS & ND) SUB AG.
  split; [| split; [split; [apply SUB, sel_in_sel_live| exact CS]| split; [exact HSY| split; [exact HSX| split; [exact HLEN| split; [| split; [split; [apply SUB, data_in_sel_live| exact CD]| split; [| exact ND]]]]]]]].
  - apply (rw_cells_agree_nw asegs m m' sel _ SC). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
    exists sel, 32. split; [apply sel_in_sel_live| exact Hx].
  - apply (rw_cells_agree_nw asegs m m' (s_data v) _ DC). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
    rewrite (cells_size_C8map Z (Z_to_bv 64) (s_rows v)) in Hx. exists (s_data v), (8 * s_sy v). split; [apply data_in_sel_live| lia].
  - apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) ROWS r Hr) as (_ & CR). split; [apply SUB, row_in_sel_live; exact Hr| exact CR].
Qed.
Lemma sel_obj_agree2 : forall (live live' : list (Z * Z)) (m m' : mem) sel v nm, sel_obj live m sel v nm ->
  (forall e, In e (sel_live sel v) -> In e live') -> agree_on (in_live (sel_live sel v)) m m' -> sel_obj live' m' sel v nm.
Proof.
  intros live live' m m' sel v nm (SB & NB & (_ & CN) & NL) SUB AG.
  split; [| split; [| split; [split; [apply SUB; left; reflexivity| exact CN]| exact NL]]].
  - apply (sel_body_agree2 live live' m m' sel v SB); [intros e He; apply SUB; right; exact He|].
    eapply agree_sub; [exact AG|]. exact (in_live_tl_sel_live sel v).
  - apply (bytes_at_agree asegs m m' (s_name v) nm NB). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
    exists (s_name v), 8. split; [left; reflexivity| rewrite NL in Hx; lia].
Qed.

Lemma nodup_fst_filter : forall (f : Z * Z -> bool) (l : list (Z * Z)), List.NoDup (map fst l) -> List.NoDup (map fst (List.filter f l)).
Proof.
  intros f l. induction l as [|e l IH]; intros ND; [constructor|]. cbn [map] in ND. inversion ND as [|x xs NI ND']; subst.
  cbn [List.filter]. destruct (f e); [| exact (IH ND')]. cbn [map]. constructor; [| exact (IH ND')].
  intros Hin. apply NI. apply in_map_iff in Hin as (y & E & Hy). apply filter_In in Hy. apply in_map_iff. exists y. split; [exact E| exact (proj1 Hy)].
Qed.
Lemma live_remove_all_nodup : forall ps (l : list (Z * Z)), List.NoDup (map fst l) -> List.NoDup (map fst (live_remove_all ps l)).
Proof. intros ps l ND. rewrite live_remove_all_filter. apply nodup_fst_filter. exact ND. Qed.

(* [comment removed for export] *)
Lemma C8s_slot : forall (mm : mem) A (ws : list word) (j : nat) (w : word),
  rw_cells asegs mm A (map C8 ws) -> nth_error ws j = Some w -> rw_cells asegs mm (A + 8 * Z.of_nat j) [C8 w].
Proof.
  intros mm A ws j w H NTH. destruct (nth_error_split ws j w NTH) as (pre & post & E & L). subst ws.
  rewrite map_app in H. apply rw_cells_app in H. destruct H as (_ & H). cbn [map] in H. apply rw_cells_head in H.
  destruct (C8s_cells pre) as (_ & _ & SZ). rewrite SZ, L in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma accok_keep_fp : forall live frames (m m' : mem) live' frames' sp W a n, accok live frames m a n ->
  agree_on (fun x => aclient live' frames' sp x /\ outside W x) m m' -> 0 <= n ->
  (forall e, In e frames -> In e frames') ->
  (forall x, shad a <= x < shad a + (n + 7) / 8 -> outside W x) -> accok live frames m' a n.
Proof.
  intros live frames m m' live' frames' sp W a n [H|(f & k & Hin & H1 & H2 & H8 & H0 & HT & Hb)] AG Hn HF HO; [left; exact H| right].
  exists f, k. repeat (split; [first [assumption | lia]|]).
  apply (bytes_at_agree asegs m m' _ _ Hb). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
  rewrite (ushadow_length n Hn) in Hx. split; [| exact (HO x Hx)].
  right; right; right; right. exists f, k. split; [exact (HF _ Hin)|]. unfold shad in *. Z.div_mod_to_equations. lia.
Qed.
Lemma nodup_fst_inj : forall (l : list (Z * Z)) p n1 n2, List.NoDup (map fst l) -> In (p, n1) l -> In (p, n2) l -> n1 = n2.
Proof.
  induction l as [|[q k] l IH]; intros p n1 n2 ND H1 H2; [destruct H1|]. cbn [map fst] in ND. inversion ND as [|x xs NI ND']; subst.
  destruct H1 as [E1|H1], H2 as [E2|H2].
  - congruence.
  - injection E1 as -> ->. exfalso. apply NI. apply in_map_iff. exists (p, n2). split; [reflexivity| exact H2].
  - injection E2 as -> ->. exfalso. apply NI. apply in_map_iff. exists (p, n1). split; [reflexivity| exact H1].
  - exact (IH p n1 n2 ND' H1 H2).
Qed.

Section SelKitRT2.
Variable RT : rt_sig.
Hypothesis AF2 : art_facts RT.

(* [comment removed for export] *)
Lemma freed_chunk_apart : forall Σ' (m : mem) ps frs usp q k a,
  ART RT Σ' m -> rt_frames RT Σ' = frs -> rt_sp0 RT Σ' - STACK_WIN <= usp ->
  In (q, k) (rt_live RT Σ') -> In q ps -> aclient (live_remove_all ps (rt_live RT Σ')) frs usp a -> a < q \/ q + k <= a.
Proof using AF2.
  intros Σ' m ps frs usp q k a HA FRS SPL Hq Hps Ha.
  pose proof (af_live_range RT AF2 Σ' m q k HA Hq) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp). apply live_remove_all_In in Hin. destruct Hin as (Hin & Hnf). cbn [fst] in Hnf.
    assert (NE : q <> p') by (intros E; apply Hnf; rewrite <- E; exact Hps).
    pose proof (live_addr_disj RT AF2 Σ' m q k p' n' HA Hq Hin NE) as D. lia.
  - destruct H as (f & kk & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF2 Σ' m f kk HA Hin) as (_ & _ & _ & FLV). specialize (FLV q k Hq). lia.
  - destruct H as (f & kk & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF2 Σ' m f kk HA Hin) as (SA1 & _). specialize (SA1 q k Hq). lia.
Qed.
End SelKitRT2.

(* [comment removed for export] *)
Lemma sel_live_in : forall (live : list (Z * Z)) (m : mem) sel v nm, sel_obj live m sel v nm -> forall e, In e (sel_live sel v) -> In e live.
Proof.
  intros live m sel v nm ((_ & (IS & _) & _ & _ & _ & _ & (ID & _) & ROWS & _) & _ & (IN & _) & _) e [E|He]; [subst e; exact IN|].
  apply in_app_or in He. destruct He as [He|[E|[E|[]]]]; [| subst e; exact ID| subst e; exact IS].
  apply in_rev in He. apply in_map_iff in He as (r & E & Hr). subst e. exact (proj1 (proj1 (Forall_forall _ _) ROWS r Hr)).
Qed.
Lemma sela_live_in : forall (live : list (Z * Z)) (m : mem) sela arr sels, sela_obj live m sela arr sels ->
  forall e, In e (sela_live sela arr sels) -> In e live.
Proof.
  intros live m sela arr sels (_ & (IS & _) & (IA & _) & _ & _ & SELS) e He. unfold sela_live in He. apply in_app_or in He.
  destruct He as [He|[E|[E|[]]]]; [| subst e; exact IA| subst e; exact IS].
  apply in_flat_map in He as (x & Hx & He). apply in_rev in Hx. exact (sel_live_in live m _ _ _ (proj1 (Forall_forall _ _) SELS x Hx) e He).
Qed.
Lemma sela_obj_pos : forall (live : list (Z * Z)) (m : mem) sela arr sels, sela_obj live m sela arr sels ->
  forall p n, In (p, n) (sela_live sela arr sels) -> 0 < n.
Proof.
  intros live m sela arr sels (_ & _ & _ & _ & _ & SELS) p n He. unfold sela_live in He. apply in_app_or in He.
  destruct He as [He|[E|[E|[]]]]; try (injection E as _ <-; lia).
  apply in_flat_map in He as (x & Hx & He). apply in_rev in Hx. exact (sel_obj_pos live m _ _ _ (proj1 (Forall_forall _ _) SELS x Hx) p n He).
Qed.
Lemma sela_obj_agree2 : forall (live live' : list (Z * Z)) (m m' : mem) sela arr sels, sela_obj live m sela arr sels ->
  (forall e, In e (sela_live sela arr sels) -> In e live') -> agree_on (in_live (sela_live sela arr sels)) m m' -> sela_obj live' m' sela arr sels.
Proof.
  intros live live' m m' sela arr sels (SAC & (_ & CS) & (_ & CA) & L50 & ARRC & SELS) SUB AG.
  split; [| split; [split; [apply SUB; unfold sela_live; apply in_or_app; right; right; left; reflexivity| exact CS]
                  | split; [split; [apply SUB; unfold sela_live; apply in_or_app; right; left; reflexivity| exact CA]| split; [exact L50| split]]]].
  - apply (rw_cells_agree_nw asegs m m' sela _ SAC). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
    exists sela, 16. split; [unfold sela_live; apply in_or_app; right; right; left; reflexivity| exact Hx].
  - apply (rw_cells_agree_nw asegs m m' arr _ ARRC). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
    rewrite cells_size_app, Nat2Z.inj_add, (cells_size_C8map _ (fun e => Z_to_bv 64 (fst (fst e))) sels), cells_size_C8rep in Hx.
    exists arr, 400. split; [unfold sela_live; apply in_or_app; right; left; reflexivity| lia].
  - apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) SELS e He) as SO.
    apply (sel_obj_agree2 live live' m m' _ _ _ SO).
    + intros c Hc. apply SUB. unfold sela_live. apply in_or_app. left. apply in_flat_map. exists e. split; [apply -> in_rev; exact He| exact Hc].
    + eapply agree_sub; [exact AG|]. intros x. exact (sel_live_in_sela_live sela arr sels e x He).
Qed.
(* [comment removed for export] *)
Lemma sela_obj_keep2 : forall (live live' : list (Z * Z)) (m m' : mem) sela arr sels, sela_obj live m sela arr sels ->
  (forall e, In e (sela_live sela arr sels) -> In e live') -> Lept_objkit.keeps_live live' m m' -> sela_obj live' m' sela arr sels.
Proof.
  intros live live' m m' sela arr sels SO SUB KL. apply (sela_obj_agree2 live live' m m' sela arr sels SO SUB).
  intros a (p & n & Hin & Ha). exact (KL p n (SUB _ Hin) a Ha).
Qed.
