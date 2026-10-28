(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_quar_defs R_qrec_defs R_qput R_qdrain R_qrec_deq R_qrec_deq2 R_qmerge R_deallocate.
From Stdlib Require Import Permutation.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma qcache_rep_frame : forall W (m m' : mem) Q bs, qcache_rep m Q bs -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W Q 32 -> Forall (fun e => disjoint_from W (fst e) 8192) bs -> qcache_rep m' Q bs.
Proof.
  intros W m m' Q bs QR MU WM HQ HB. apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & QC).
  apply (proj2 (qcache_rep_iff _ _ _)). split.
  - apply (rw_cells_transport asegs W m m' _ _ QH MU WM). exact HQ.
  - apply (proj2 (qchain_to_0 _ _)). apply (qchain_to_frame _ m m' _ _ (proj1 (qchain_to_0 _ _) QC) MU WM HB).
Qed.

Definition qdorec_entry : Z := 0x5d840.

Definition qrec_A_post (ra gp tp s5 s6 s7 s8 s9 s10 s11 CACHE STACK : word) (F : bvmap 5 word) (fc : bv 32) (TMP : Z)
    (W : list (Z * Z)) (Xd r : list batch) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' s0' s1' s2' s3' s4' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x5d648) (Z_to_bv 64 TMP) gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 QUAR) (Z_to_bv 64 TMP) CACHE STACK
                  a4' a5' a6' a7' s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 qdorec_entry) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ qcache_rep m' QG r /\ qcache_rep m' TMP Xd /\ q_lock m' 0 0.

Section REC.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 CACHE STACK : word) (F : bvmap 5 word) (fc : bv 32).
Variables (MIN SB TMP : Z).
Hypothesis HMIN : (0 <= MIN < 2^63)%Z.
Hypothesis HSB : (0 < SB)%Z.
Hypothesis HTMP : (r24 SB + 2^32 <= TMP /\ TMP + 32 <= 2^47)%Z.

Lemma qrec_tail : forall (m : mem) (ra0 t0 t1 t2 a1 a4 a5 a6 a7 : word) (Xd r : list batch),
  rw_cells asegs m q_lockw [C4 (Z_to_bv 64 257)] -> qcache_rep m QG r -> qcache_rep m TMP Xd ->
  qwf SB (Xd ++ r) -> mem_inv asegs m ->
  evt asegs (qrec_A_post ra gp tp s5 s6 s7 s8 s9 s10 s11 CACHE STACK F fc TMP [(q_lockw, q_lockw + 4)]%Z Xd r m)
    (MS (mkR ra0 (Z_to_bv 64 TMP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) a1 CACHE STACK a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5d630) fc None m (seg_rom asegs)).
Proof.
  intros until r. intros LK QR TR WF MI.
  pose proof (qwf_region _ _ WF) as RG. apply box in RG. apply box in QR. apply box in TR.
  unfold r24 in *.
  change (Z_to_bv 64 257) with (Z_to_bv 64 (1 + 256 * 1)) in LK. apply (c4_to_hdr3 _ _ 1 1 []) in LK; [| lia| lia].
  pose proof (munch_refl [(1509704, 1509704 + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zhide.
  zstep. zstep; fix_lit_store. zstep. zstep; fix_lit_store.
  do 2 zstep.
  apply evt_done. unfold qrec_A_post, qdorec_entry, q_lock. do 17 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  pose proof (unbox _ RG) as RG'. apply Forall_app in RG'. destruct RG' as (RG1 & RG2).
  split; [| split; [| eassumption]].
  - lazymatch goal with |- qcache_rep ?mm _ _ => apply (qcache_rep_frame _ m mm _ _ (unbox _ QR) MU WM) end.
    + cbn [disjoint_from]. lia.
    + apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) RG2 e He) as (E1 & E2). cbn [disjoint_from]. lia.
  - lazymatch goal with |- qcache_rep ?mm _ _ => apply (qcache_rep_frame _ m mm _ _ (unbox _ TR) MU WM) end.
    + cbn [disjoint_from]. lia.
    + apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) RG1 e He) as (E1 & E2). cbn [disjoint_from]. lia.
Qed.

Lemma qrec_deq_k : forall (m : mem) (ra0 t0 t1 t2 a4 a5 a7 : word) (K X : list batch),
  qcache_rep m QG K -> qcache_rep m TMP X -> rw_cells asegs m q_lockw [C4 (Z_to_bv 64 257)] ->
  qwf SB (X ++ K) -> (qbytes (X ++ K) < 2^56)%Z ->
  mem_inv asegs m ->
  evt asegs (qrec_A_post ra gp tp s5 s6 s7 s8 s9 s10 s11 CACHE STACK F fc TMP
               ([(QG, QG + 32); (TMP, TMP + 32); (q_lockw, q_lockw + 4)] ++ bivs (X ++ K))%Z
               (X ++ fst (deq K (qbytes K) MIN)) (snd (deq K (qbytes K) MIN)) m)
    (MS (mkR ra0 (Z_to_bv 64 TMP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 MIN) CACHE STACK a4 a5
             (Z_to_bv 64 (Z.of_nat (length K))) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5d594) fc None m (seg_rom asegs)).
Proof.
  intros until X. intros QR TR LK WF HBY MI.
  pose proof (qbytes_ge _ _ (qwf_suffix _ _ _ WF)) as QGE. pose proof (qbytes_nonneg _ _ (qwf_prefix _ _ _ WF)) as QXN.
  rewrite qbytes_app in HBY.
  pose proof QR as QR0. pose proof TR as TR0. apply box in QR0. apply box in TR0.
  apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & QC). apply box in QC.
  apply (proj1 (qcache_rep_iff _ _ _)) in TR. destruct TR as (TH & TC). apply box in TC.
  unfold r24 in *.
  pose proof (munch_refl [] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  zhide.
  do 3 zstep. zstep.
  destruct (Z.leb_spec (qbytes K) MIN) as [HX|HX].
  -
    ifT.
    assert (ED : deq K (qbytes K) MIN = ([], K)) by (destruct K as [|B rest]; [reflexivity| cbn [deq]; destruct (Z.leb_spec (qbytes (B :: rest)) MIN); [reflexivity| lia]]).
    rewrite ED. cbn [fst snd]. rewrite app_nil_r.
    clear QH TH QC TC. apply (unbox _) in QR0. apply (unbox _) in TR0.
    eapply evt_mono; [eapply qrec_tail; try eassumption; rewrite app_nil_r; exact WF|].
    intros ms' (t0' & t1' & t2' & s0' & s1' & s2' & s3' & s4' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU' & P).
    exists t0', t1', t2', s0', s1', s2', s3', s4', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|].
    split; [| exact P]. eapply munch_weaken; [| exact MU']. intros x Hx. apply outside_app in Hx. destruct Hx as (Hx & _).
    cbn [outside] in *. tauto.
  -
    ifF.
    destruct K as [|B rest]; [cbn in HX; lia|].
    zstep. zstep.
    replace (qfirst (B :: rest)) with (fst B) by (destruct B; reflexivity).
    eapply evt_cut.
    { eapply (deq_loop ra0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 CACHE STACK F fc MIN SB TMP HMIN HSB HTMP
                rest B X m); try eassumption.
      - rewrite qbytes_app. lia.
      - exact (proj1 (qchain_to_0 _ _) (unbox _ QC)).
      - exact (proj1 (qchain_to_0 _ _) (unbox _ TC)).
      - intros _. reflexivity. }
    intros ms1 (t0' & t1' & t2' & a4' & a5' & a6' & a7' & m1 & E1 & MU1 & WM1 & MI1 & QG1 & TQ1). subst ms1.
    pose proof (deq_app (B :: rest) (qbytes (B :: rest)) MIN) as EDQ.
    pose proof (qwf_region _ _ WF) as RG. apply box in RG.
    assert (LK1 : rw_cells asegs m1 q_lockw [C4 (Z_to_bv 64 257)]).
    { apply (rw_cells_transport asegs _ m m1 _ _ LK MU1 WM1). change (Z.of_nat (cells_size [C4 (Z_to_bv 64 257)])) with 4%Z.
      apply disjoint_from_app.
      - cbn [disjoint_from]. lia.
      - apply disjoint_bivs. apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e He) as (E1 & E2).
        unfold r24 in *. lia. }
    eapply evt_mono; [eapply qrec_tail; [exact LK1 | exact QG1 | exact TQ1 | rewrite <- app_assoc, EDQ; exact WF | exact MI1]|].
    intros ms' (t0'' & t1'' & t2'' & s0' & s1' & s2' & s3' & s4' & a4'' & a5'' & a6'' & a7'' & t3' & t4' & t5' & t6' & m' & E & MU' & WM' & MI' & P).
    exists t0'', t1'', t2'', s0', s1', s2', s3', s4', a4'', a5'', a6'', a7'', t3', t4', t5', t6', m'. split; [exact E|].
    split; [| split; [eapply wmono_trans; eassumption| split; [exact MI'| exact P]]].
    eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU']].
    + intros x Hx. apply outside_app in Hx. destruct Hx as (H1 & H2). apply outside_app. split; [cbn [outside] in *; tauto | exact H2].
    + intros x Hx. apply outside_app in Hx. destruct Hx as (H1 & H2). cbn [outside] in *. tauto.
Qed.

End REC.

Lemma merge_walk_perm : forall rest cur,
  Permutation (map fst (fst (merge_walk cur rest)) ++ map fst (snd (merge_walk cur rest))) (fst cur :: map fst rest).
Proof.
  induction rest as [|nxt rest IH]; intros cur; cbn [merge_walk]; [cbn; apply Permutation_refl|].
  destruct (_ <=? _); cbn [fst snd map app].
  - pose proof (IH (fst cur, snd cur ++ snd nxt)) as P. cbn [fst] in P.
    eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
    eapply Permutation_trans; [apply perm_skip, P| apply perm_swap].
  - apply perm_skip. apply IH.
Qed.

Lemma merge_all_perm : forall gl, Permutation (map fst (snd (merge_all gl) ++ fst (merge_all gl))) (map fst gl).
Proof.
  intros [|cur rest]; [apply Permutation_refl|]. cbn [merge_all]. rewrite map_app.
  eapply Permutation_trans; [apply Permutation_app_comm| apply merge_walk_perm].
Qed.

Definition qent_ok (SB : Z) (e : batch) : Prop :=
  (fst e mod 8192 = 0 /\ r24 SB <= fst e /\ fst e + 8192 <= r24 SB + 2 ^ 32 /\ (length (snd e) <= 1021)%nat
   /\ Forall (fun x => 0 <= snd x) (snd e))%Z.

Lemma merge_walk_ok : forall SB rest cur, qent_ok SB cur -> Forall (qent_ok SB) rest ->
  Forall (qent_ok SB) (fst (merge_walk cur rest)) /\ Forall (qent_ok SB) (snd (merge_walk cur rest)).
Proof.
  intros SB. induction rest as [|nxt rest IH]; intros cur Hc Hr; cbn [merge_walk].
  - cbn [fst snd]. split; [constructor; [exact Hc| constructor]| constructor].
  - inversion Hr as [|? ? Hn Hr']; subst.
    destruct (Z.leb_spec (Z.of_nat (length (snd cur) + length (snd nxt))) 1021) as [HL|HL]; cbn [fst snd].
    + destruct (IH (fst cur, snd cur ++ snd nxt)) as (A & B); [| exact Hr' |].
      * destruct Hc as (C1 & C2 & C3 & C4 & C5). destruct Hn as (N1 & N2 & N3 & N4 & N5). unfold qent_ok. cbn [fst snd].
        rewrite app_length. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [lia|].
        apply Forall_app. split; assumption.
      * split; [exact A| constructor; [| exact B]].
        destruct Hn as (N1 & N2 & N3 & N4 & N5). unfold qent_ok. cbn [fst snd length].
        split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [lia| constructor].
    + destruct (IH nxt Hn Hr') as (A & B). split; [constructor; assumption| exact B].
Qed.

Lemma qwf_merge : forall SB gl, qwf SB gl -> qwf SB (snd (merge_all gl) ++ fst (merge_all gl)).
Proof.
  intros SB gl (ND & HF). split.
  - apply (Permutation_NoDup (Permutation_sym (merge_all_perm gl))). exact ND.
  - destruct gl as [|cur rest]; [constructor|]. cbn [merge_all]. inversion HF as [|? ? H1 H2]; subst.
    destruct (merge_walk_ok SB rest cur H1 H2) as (A & B). apply Forall_app. split; assumption.
Qed.

Lemma bivs_merge_sub : forall gl, sub_fp (bivs (snd (merge_all gl) ++ fst (merge_all gl))) (bivs gl).
Proof.
  intros gl x Hx. apply outside_bivs. apply outside_bivs in Hx. apply Forall_forall. intros e He.
  assert (Hm : In (fst e) (map fst gl)) by (apply (Permutation_in _ (merge_all_perm gl)); apply in_map; exact He).
  apply in_map_iff in Hm. destruct Hm as (e' & E' & He'). pose proof (proj1 (Forall_forall _ _) Hx e' He') as Hn.
  cbv beta in Hn. rewrite E' in Hn. exact Hn.
Qed.

Definition rec_x (gl : list batch) (MIN : Z) : list batch :=
  snd (rec_merge gl) ++ fst (deq (fst (rec_merge gl)) (qbytes (fst (rec_merge gl))) MIN).
Definition rec_r (gl : list batch) (MIN : Z) : list batch := snd (deq (fst (rec_merge gl)) (qbytes (fst (rec_merge gl))) MIN).

Definition qrec_frame (m : mem) (A : Z) (ra s0 s1 s2 s3 s4 : word) : Prop :=
  rw_cells asegs m (A + 32) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition qrec_E_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 CACHE STACK : word) (F : bvmap 5 word) (fc : bv 32)
    (W : list (Z * Z)) (Xd r : list batch) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' s0' s1' s2' s3' s4' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x5d648) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 QUAR)
                  (Z_to_bv 64 (bv_unsigned sp + -80)) CACHE STACK a4' a5' a6' a7' s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 qdorec_entry) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ qcache_rep m' QG r /\ qcache_rep m' (bv_unsigned sp + -80) Xd /\ q_lock m' 0 0
    /\ qrec_frame m' (bv_unsigned sp + -80) ra s0 s1 s2 s3 s4 /\ stk asegs m' lo (bv_unsigned sp + -80).

Lemma qrec_k : forall sp gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 CACHE STACK (F : bvmap 5 word) fc (MIN SB lo : Z) (m : mem)
    (ra0 t0 t1 t2 s0 s1 s2 s3 s4 a4 a5 a7 rr s0r s1r s2r s3r s4r : word) (K X : list batch),
  (0 <= MIN < 2^63)%Z -> (0 < SB)%Z -> (r24 SB + 2^32 <= lo)%Z -> (lo <= bv_unsigned sp - 96)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  qcache_rep m QG K -> qcache_rep m (bv_unsigned sp + -80) X -> rw_cells asegs m q_lockw [C4 (Z_to_bv 64 257)] ->
  qwf SB (X ++ K) -> (qbytes (X ++ K) < 2^56)%Z ->
  qrec_frame m (bv_unsigned sp + -80) rr s0r s1r s2r s3r s4r -> stk asegs m lo (bv_unsigned sp + -80) ->
  mem_inv asegs m ->
  evt asegs (qrec_E_post rr sp gp tp s0r s1r s2r s3r s4r s5 s6 s7 s8 s9 s10 s11 CACHE STACK F fc
               ([(QG, QG + 32); (bv_unsigned sp + -80, bv_unsigned sp + -80 + 32); (q_lockw, q_lockw + 4)] ++ bivs (X ++ K))%Z
               (X ++ fst (deq K (qbytes K) MIN)) (snd (deq K (qbytes K) MIN)) lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 MIN) CACHE STACK a4 a5
             (Z_to_bv 64 (Z.of_nat (length K))) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5d594) fc None m (seg_rom asegs)).
Proof.
  intros until X. intros HMIN HSB HRl HLO HSP QR TR LK WF HBY FR ST MI.
  pose proof (qwf_region _ _ WF) as RG. apply box in RG. apply box in FR. apply box in ST.
  eapply evt_mono; [eapply (qrec_deq_k rr gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 CACHE STACK F fc MIN SB
                              (bv_unsigned sp + -80) HMIN HSB ltac:(unfold r24 in *; lia) m ra0 t0 t1 t2 a4 a5 a7 K X);
                    eassumption|].
  intros ms' (t0' & t1' & t2' & s0' & s1' & s2' & s3' & s4' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU' & WM' & MI'
              & QG' & TQ' & LK').
  exists t0', t1', t2', s0', s1', s2', s3', s4', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|].
  split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact QG'|]. split; [exact TQ'|]. split; [exact LK'|].
  assert (DJ : forall a n, (lo <= a)%Z -> (a + n <= bv_unsigned sp)%Z -> (bv_unsigned sp + -80 + 32 <= a \/ a + n <= bv_unsigned sp + -80)%Z ->
            disjoint_from ([(QG, QG + 32); (bv_unsigned sp + -80, bv_unsigned sp + -80 + 32); (q_lockw, q_lockw + 4)] ++ bivs (X ++ K))%Z a n).
  { intros a n H1 H2 H3. apply disjoint_from_app; [cbn [disjoint_from]; unfold r24 in *; lia|].
    apply disjoint_bivs. apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e He) as (E1 & E2).
    unfold r24 in *. lia. }
  split.
  - unfold qrec_frame in *. apply (rw_cells_transport asegs _ m m' _ _ (unbox _ FR) MU' WM'). apply DJ; cbn [cells_size csize Nat.add Z.of_nat]; lia.
  - apply (stk_transport_disjoint asegs _ m m' _ _ (unbox _ ST) MU' WM'). apply DJ; lia.
Qed.

Lemma qrec_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (CACHE STACK : word) (MIN SB lo : Z) (gl : list batch),
  merge_stmt ->
  qcache_rep m QG gl -> qwf SB gl -> (qbytes gl < 2^56)%Z -> (0 <= MIN < 2^63)%Z -> (0 < SB)%Z -> q_lock m 0 1 ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 96)%Z -> (r24 SB + 2^32 <= lo)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (qrec_E_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 CACHE STACK F fc
               ([(q_lockw, q_lockw + 4); (QG, QG + 32); (bv_unsigned sp - 96, bv_unsigned sp)] ++ bivs gl)%Z
               (rec_x gl MIN) (rec_r gl MIN) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 MIN) CACHE STACK a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qrecycle_entry) fc None m (seg_rom asegs)).
Proof.
  intros until gl. intros MERGE QR WF HBY HMIN HSB LK ST HLO HRl HSP MI.
  pose proof (qbytes_ge _ _ WF) as QGE.
  pose proof (qwf_region _ _ WF) as RG. apply box in RG.
  pose proof QR as QR0. apply box in QR0.
  apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & QC). apply box in QC.
  unfold q_lock, qrecycle_entry, r24 in *.
  pose proof (Nat2Z.is_nonneg (length gl)) as HNG.
  remember (Z.of_nat (length gl)) as NG eqn:ENG.
  remember (qbytes gl) as BG eqn:EBG.
  remember (qfirst gl) as FG eqn:EFG. remember (qlast gl) as LG eqn:ELG.
  move LK at bottom. move QH at bottom.
  pose proof (munch_refl [(1509704, 1509704 + 4); (bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST. carve_frame 32%nat ST.
  zhide.
  do 7 zstep.
  zstep; fix_lit_store. zstep; fix_lit_store. zstep; fix_lit_store. zstep; fix_lit_store.
  do 4 zstep.
  apply (hdr3_to_c4 _ _ 0 1 []) in LK; [| lia| lia]. change (0 + 256 * 1)%Z with 256%Z in LK.
  assert (AMO : amo_aligned AW (Z_to_bv 64 1509704) = true) by (vm_compute; reflexivity).
  amo_step AMO. rewrite (sx32_small_A 256) by lia.
  do 4 zstep. fold_reg 6%Z.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. zstep.
  replace (NG ≪ 13)%Z with (8192 * NG)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. ifF.
  zstep.
  sp_facts.
  assert (QRm : forall mm, munch [(1509704, 1509704 + 4); (bv_unsigned sp - 80, bv_unsigned sp)]%Z m mm -> wmono asegs m mm ->
            qcache_rep mm QG gl).
  { intros mm MUm WMm. apply (qcache_rep_frame _ m mm _ _ (unbox _ QR0) MUm WMm).
    - cbn [disjoint_from]. lia.
    - apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e He) as (E1 & E2).
      cbn [disjoint_from]. lia. }
  assert (TR0 : forall mm, rw_cells asegs mm (bv_unsigned sp + -80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
            qcache_rep mm (bv_unsigned sp + -80) []).
  { intros mm H. apply (proj2 (qcache_rep_iff _ _ _)). split; [exact H| exact I]. }
  destruct (Z.leb_spec BG (8192 * NG)) as [HC1|HC1].
  -
    ifT.
    assert (MC : merge_cond gl = false).
    { unfold merge_cond. rewrite <- ENG, <- EBG. apply andb_false_iff. left. apply Z.ltb_ge. lia. }
    rewrite ENG.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_mono; [eapply (qrec_k sp gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 CACHE STACK F fc MIN SB lo mm
                                  ra _ _ _ s0 s1 s2 s3 s4 _ _ _ ra s0 s1 s2 s3 s4 gl []); try eassumption|] end.
    + apply QRm; eassumption.
    + apply TR0; eassumption.
    + change ([] ++ gl) with gl. lia.
    + unfold qrec_frame. qexact_addr.
    + intros ms' (t0' & t1' & t2' & s0' & s1' & s2' & s3' & s4' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU' & WM'
                  & MI' & QG' & TQ' & LK' & FR' & ST').
      exists t0', t1', t2', s0', s1', s2', s3', s4', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|].
      unfold rec_x, rec_r, rec_merge. rewrite MC. cbn [fst snd app].
      split; [| split; [eapply wmono_trans; eassumption| split; [exact MI'| split; [exact QG'| split; [exact TQ'| split; [exact LK'|
              split; [exact FR'| exact ST']]]]]]].
      eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU']].
      * intros x Hx. cbn [outside] in *. lia.
      * intros x Hx. cbn [outside] in Hx. destruct Hx as (H1 & H2 & H3 & H4). apply outside_app. split; [cbn [outside]; lia| exact H4].
  - ifF.
    do 5 zstep.
    destruct (Z.leb_spec (NG * 1638400) (BG * 100)) as [HC2|HC2].
    +
      ifT.
      assert (MC : merge_cond gl = false).
      { unfold merge_cond. rewrite <- ENG, <- EBG. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
      rewrite ENG.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_mono; [eapply (qrec_k sp gp tp s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 CACHE STACK F fc MIN SB lo mm
                                    ra _ _ _ s0 s1 s2 s3 s4 _ _ _ ra s0 s1 s2 s3 s4 gl []); try eassumption|] end.
      * apply QRm; eassumption.
      * apply TR0; eassumption.
      * change ([] ++ gl) with gl. lia.
      * unfold qrec_frame. qexact_addr.
      * intros ms' (t0' & t1' & t2' & s0' & s1' & s2' & s3' & s4' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU' & WM'
                    & MI' & QG' & TQ' & LK' & FR' & ST').
        exists t0', t1', t2', s0', s1', s2', s3', s4', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|].
        unfold rec_x, rec_r, rec_merge. rewrite MC. cbn [fst snd app].
        split; [| split; [eapply wmono_trans; eassumption| split; [exact MI'| split; [exact QG'| split; [exact TQ'| split; [exact LK'|
                split; [exact FR'| exact ST']]]]]]].
        eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU']].
        -- intros x Hx. cbn [outside] in *. lia.
        -- intros x Hx. cbn [outside] in Hx. destruct Hx as (H1 & H2 & H3 & H4). apply outside_app. split; [cbn [outside]; lia| exact H4].
    +
      ifF.
      assert (MC : merge_cond gl = true).
      { unfold merge_cond. rewrite <- ENG, <- EBG. apply andb_true_iff. split; apply Z.ltb_lt; lia. }
      do 8 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (QRm mm MU WM) as QRc; pose proof (TR0 mm ltac:(eassumption)) as TRc end.
      clear QRm TR0. apply box in FR. apply box in LK. apply box in MU. apply box in WM.
      eapply evt_cut.
      { eapply (MERGE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1509712%Z (bv_unsigned sp + -80)%Z SB lo gl).
        all: rewrite ?Esp; first [eassumption| unfold r24 in *; lia]. }
      intros ms1 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & E1 & MU1 & WM1 & MI1
                  & QG1 & TQ1 & ST1).
      subst ms1.
      replace (ret_pc (Z_to_bv 64 382336)) with (Z_to_bv 64 382336) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite Esp in MU1, ST1.
      pose proof QG1 as QG1b. apply box in QG1b.
      apply (proj1 (qcache_rep_iff _ _ _)) in QG1. destruct QG1 as (QH1 & QC1). apply box in QC1.
      assert (FR1 : rw_cells asegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { apply (rw_cells_transport asegs _ _ m1 _ _ (unbox _ FR) MU1 WM1). cbn [disjoint_from cells_size csize Nat.add Z.of_nat].
        refine (conj _ (conj _ (conj _ _))); [lia| lia| lia|].
        apply disjoint_bivs. apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e He) as (E1 & E2).
        unfold r24 in *. lia. }
      assert (LK1 : rw_cells asegs m1 1509704 [C4 (Z_to_bv 64 257)]).
      { apply (rw_cells_transport asegs _ _ m1 _ _ (unbox _ LK) MU1 WM1). cbn [disjoint_from cells_size csize Nat.add Z.of_nat].
        refine (conj _ (conj _ (conj _ _))); [lia| lia| lia|].
        apply disjoint_bivs. apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e He) as (E1 & E2).
        unfold r24 in *. lia. }
      clear FR LK. move LK1 at bottom. move QH1 at bottom. move FR1 at bottom.
      do 5 zstep.
      pose proof (qwf_merge _ _ WF) as WFm. pose proof (merge_all_bytes gl) as MB.
      eapply evt_mono; [eapply (qrec_k sp gp tp s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' CACHE STACK F fc MIN SB lo m1
                                  (Z_to_bv 64 382336) _ _ _ (Z_to_bv 64 1509712) (Z_to_bv 64 MIN) (Z_to_bv 64 1509552) STACK CACHE _ _ _
                                  ra s0 s1 s2 s3 s4 (fst (merge_all gl)) (snd (merge_all gl))); try eassumption|].
      * rewrite qbytes_app. lia.
      * unfold qrec_frame. qexact_addr.
      * intros ms' (t0'' & t1'' & t2'' & s0' & s1' & s2' & s3' & s4' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m' & E & MU'
                    & WM' & MI' & QG' & TQ' & LK' & FR' & ST').
        exists t0'', t1'', t2'', s0', s1', s2', s3', s4', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m'. split; [exact E|].
        unfold rec_x, rec_r, rec_merge. rewrite MC.
        split; [| split; [eapply wmono_trans; [eapply wmono_trans; [exact (unbox _ WM)| exact WM1]| exact WM']|
                split; [exact MI'| split; [exact QG'| split; [exact TQ'| split; [exact LK'| split; [exact FR'| exact ST']]]]]]].
        eapply munch_trans; [eapply munch_trans; [eapply munch_weaken; [| exact (unbox _ MU)]| eapply munch_weaken; [| exact MU1]]|
                             eapply munch_weaken; [| exact MU']].
        -- intros x Hx. cbn [outside app] in *. lia.
        -- intros x Hx. cbn [outside app] in Hx. destruct Hx as (H1 & H2 & H3 & H4). cbn [outside].
           refine (conj _ (conj _ (conj _ _))); [lia| lia| lia| exact H4].
        -- intros x Hx. cbn [outside app] in Hx. destruct Hx as (H1 & H2 & H3 & H4). apply outside_app.
           split; [cbn [outside]; lia| apply (bivs_merge_sub gl); exact H4].
Qed.

Definition qrec_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma qrec_ret_spec : forall ra sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra0 s0 s1 s2 s3 s4 w0 w1 w2 w3 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  rw_cells asegs m (bv_unsigned sp + -80) [C8 w0; C8 w1; C8 w2; C8 w3] ->
  qrec_frame m (bv_unsigned sp + -80) ra s0 s1 s2 s3 s4 ->
  stk asegs m lo (bv_unsigned sp + -80) -> (lo <= bv_unsigned sp + -80)%Z -> (0x6ca000 <= lo)%Z ->
  mem_inv asegs m ->
  evt asegs (qrec_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5d648) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros TH FR ST HLO HIMG MI. unfold qrec_frame in FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  assert (FRa : rw_cells asegs m (bv_unsigned sp + -80) ([C8 w0; C8 w1; C8 w2; C8 w3] ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply (proj2 (rwc_app _ _ _ _ _)). split; [exact TH|].
    change (Z.of_nat (cells_size [C8 w0; C8 w1; C8 w2; C8 w3])) with 32%Z. exact FR. }
  cbn [app] in FRa. clear TH FR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  zhide.
  do 7 zstep.
  release_frame FRa ST (bv_unsigned sp).
  zstep.
  finish.
Qed.
