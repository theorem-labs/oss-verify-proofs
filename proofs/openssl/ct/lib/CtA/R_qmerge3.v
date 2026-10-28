(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk Image. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_quar_defs R_qrec_defs R_qput R_qdrain R_qrec_deq R_qmerge R_qmerge2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Lemma qchain_split3 : forall (m : mem) K b e rest,
  qchain_to m (K ++ (b, e) :: rest) 0 <-> qchain_to m K b /\ qbatch m b (qfirst rest) e /\ qchain_to m rest 0.
Proof.
  intros m K b e rest. rewrite (qchain_to_app m K ((b, e) :: rest) 0) by discriminate. cbn [qfirst qchain_to].
  destruct rest as [|[b1 e1] rest]; cbn [qfirst]; tauto.
Qed.

Lemma qchain_split4 : forall (m : mem) K b e b' e' rest,
  qchain_to m (K ++ (b, e) :: (b', e') :: rest) 0 <->
  qchain_to m K b /\ qbatch m b b' e /\ qbatch m b' (qfirst rest) e' /\ qchain_to m rest 0.
Proof.
  intros m K b e b' e' rest. rewrite qchain_split3. cbn [qfirst qchain_to].
  destruct rest as [|[b1 e1] rest]; cbn [qfirst]; tauto.
Qed.

Lemma qfirst_app_cons : forall (K : list batch) b e1 e2 r1 r2, qfirst (K ++ (b, e1) :: r1) = qfirst (K ++ (b, e2) :: r2).
Proof. intros [|[b0 e0] K] b e1 e2 r1 r2; reflexivity. Qed.

Lemma qlast_cons_ne' : forall (x : batch) rest, rest <> [] -> qlast (x :: rest) = qlast rest.
Proof. intros x rest H. unfold qlast. destruct rest as [|y rest]; [congruence| reflexivity]. Qed.

Lemma qlast_in : forall (l : list batch), l <> [] -> In (qlast l) (map fst l).
Proof.
  intros l H. unfold qlast. induction l as [|x l IH]; [congruence|].
  destruct l as [|y l]; [left; reflexivity|]. right. apply IH. discriminate.
Qed.

(* [comment removed for export] *)
Lemma merge_qlast : forall SB K b e b' e' e2 rest X, qwf SB ((K ++ (b, e) :: (b', e') :: rest) ++ X) ->
  (if qlast (K ++ (b, e) :: (b', e') :: rest) =? b' then b else qlast (K ++ (b, e) :: (b', e') :: rest))%Z = qlast (K ++ (b, e2) :: rest).
Proof.
  intros SB K b e b' e' e2 rest X WF.
  rewrite (qlast_app_ne K ((b, e) :: (b', e') :: rest)) by discriminate.
  rewrite (qlast_app_ne K ((b, e2) :: rest)) by discriminate.
  destruct rest as [|r0 rest'].
  - cbn [qlast map last]. rewrite Z.eqb_refl. reflexivity.
  - rewrite (qlast_cons_ne' (b, e) ((b', e') :: r0 :: rest')) by discriminate.
    rewrite (qlast_cons_ne' (b', e') (r0 :: rest')) by discriminate.
    rewrite (qlast_cons_ne' (b, e2) (r0 :: rest')) by discriminate.
    destruct (Z.eqb_spec (qlast (r0 :: rest')) b') as [Eq|Eq]; [| reflexivity].
    exfalso. destruct WF as (ND & _). rewrite !map_app in ND. apply NoDup_app_remove_r in ND.
    apply NoDup_app_remove_l in ND. cbn [map] in ND. inversion ND as [|? ? _ ND']; subst.
    inversion ND' as [|? ? NI _]; subst. apply NI. try rewrite <- Eq. apply qlast_in. discriminate.
Qed.

(* [comment removed for export] *)
Lemma merge_fit_perm : forall (K rest X : list batch) (b b' : Z) (e e2 e' : list (Z * Z)),
  Permutation (map fst ((K ++ (b, e2) :: rest) ++ X ++ [(b', [])])) (map fst ((K ++ (b, e) :: (b', e') :: rest) ++ X)).
Proof.
  intros. rewrite !map_app. cbn [map fst]. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
  apply perm_skip. rewrite app_assoc. apply Permutation_sym. apply Permutation_cons_app. rewrite app_nil_r. apply Permutation_refl.
Qed.

Lemma merge_fit_wf : forall SB (K rest X : list batch) (b b' : Z) (e e' : list (Z * Z)), qwf SB ((K ++ (b, e) :: (b', e') :: rest) ++ X) ->
  (length (e ++ e') <= 1021)%nat -> qwf SB ((K ++ (b, e ++ e') :: rest) ++ X ++ [(b', [])]).
Proof.
  intros SB K b e b' e' rest X (ND & HF) Hl. split.
  - eapply Permutation_NoDup; [apply Permutation_sym, merge_fit_perm| exact ND].
  - rewrite <- !app_assoc in *. apply Forall_app in HF. destruct HF as (HK & HF). inversion HF as [|? ? Hb HF1]; subst.
    inversion HF1 as [|? ? Hb' HF2]; subst. apply Forall_app in HF2. destruct HF2 as (HR & HX).
    apply Forall_app. split; [exact HK|]. constructor.
    + destruct Hb as (A1 & A2 & A3 & A4 & A5). destruct Hb' as (_ & _ & _ & _ & B5). cbn [fst snd] in *.
      split; [exact A1| split; [exact A2| split; [exact A3| split; [exact Hl| apply Forall_app; split; assumption]]]].
    + cbn [app]. apply Forall_app. split; [exact HR|]. apply Forall_app. split; [exact HX|]. constructor; [| constructor].
      destruct Hb' as (B1 & B2 & B3 & _ & _). cbn [fst snd] in *. split; [exact B1| split; [exact B2| split; [exact B3| split; [cbn; lia| constructor]]]].
Qed.

Ltac qtrans H MU WM :=
  let H' := fresh H in
  pose proof (rw_cells_transport ctasegs _ _ _ _ _ H MU WM ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as H';
  clear H; rename H' into H.

(* [comment removed for export] *)
Lemma qcache_rep_frame' : forall W (m m' : mem) Q bs, qcache_rep m Q bs -> munch W m m' -> wmono ctasegs m m' ->
  disjoint_from W Q 32 -> Forall (fun e => disjoint_from W (fst e) 8192) bs -> qcache_rep m' Q bs.
Proof.
  intros W m m' Q bs QR MU WM HQ HB. apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & QC).
  apply (proj2 (qcache_rep_iff _ _ _)). split.
  - apply (rw_cells_transport ctasegs W m m' _ _ QH MU WM). exact HQ.
  - apply (proj2 (qchain_to_0 _ _)). apply (qchain_to_frame _ m m' _ _ (proj1 (qchain_to_0 _ _) QC) MU WM HB).
Qed.

Section MLOOP.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (FROM TO SB lo : Z) (gl : list batch) (m0 : mem).
Hypothesis HSB : (0 < SB)%Z.
Hypothesis HF0 : (0 < FROM)%Z.
Hypothesis HFS : (FROM + 32 <= r24 SB \/ r24 SB + 2^32 <= FROM)%Z.
Hypothesis HTS : (TO + 32 <= r24 SB \/ r24 SB + 2^32 <= TO)%Z.
Hypothesis HFT : (FROM + 32 <= TO \/ TO + 32 <= FROM)%Z.
Hypothesis HTSP : (bv_unsigned sp <= TO \/ TO + 32 <= lo)%Z.
Hypothesis HLO : (lo <= bv_unsigned sp - 16)%Z.
Hypothesis HRl : (r24 SB + 2^32 <= lo)%Z.
Hypothesis HFl : (FROM + 32 <= lo)%Z.
Hypothesis HSP : (bv_unsigned sp <= 2^47)%Z.
Hypothesis HBY : (qbytes gl < 2^56)%Z.
Hypothesis HWG : qwf SB gl.

Definition mW : list (Z * Z) := ((FROM, FROM + 32) :: (TO, TO + 32) :: (bv_unsigned sp - 16, bv_unsigned sp) :: bivs gl)%Z.

(* [comment removed for export] *)
Lemma merge_exit : forall (L X : list batch) (m : mem) (j0 : list byte) (t0 t1 t2 t3 t4 t5 t6 a1 a3 a4 a5 a6 a7 : word),
  merge_mem m FROM TO (qbytes gl) L X -> merge_all gl = (L, X) -> Forall (fun e => snd e = []) X -> qwf SB (L ++ X) ->
  rw_cells ctasegs m (bv_unsigned sp + -16) [CB 8 j0] -> rw_cells ctasegs m (bv_unsigned sp + -8) [C8 ra] ->
  stk ctasegs m lo (bv_unsigned sp + -16) ->
  munch mW m0 m -> wmono ctasegs m0 m -> mem_inv ctasegs m ->
  evt ctasegs (merge_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FROM TO gl lo m0)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FROM) a1 (Z_to_bv 64 (8192 * Z.of_nat (length X)))
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19df94) fc None m (seg_rom ctasegs)).
Proof.
  intros until a7. intros (FH & FC & TH & TC) EM HX WF FR0 FR ST MU WM MI.
  pose proof (merge_all_bytes gl) as MB. rewrite EM in MB. cbn [fst snd] in MB. rewrite (qbytes_empty_ents X HX) in MB.
  pose proof (qwf_region _ _ WF) as RG. apply box in RG. apply box in FC. apply box in TC. apply box in TH.
  pose proof (qbytes_nonneg _ _ (qwf_prefix _ _ _ WF)) as QLN.
  apply box in MU. pose proof (munch_refl [(FROM, FROM + 32); (bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MUe.
  pose proof (wmono_refl ctasegs m) as WMe.
  unfold r24 in *.
  do 5 zstep.
  release_frame FR0 ST (bv_unsigned sp + -8)%Z. release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evt_done. unfold merge_post. rewrite EM. cbn [fst snd].
  do 16 eexists. split; [reflexivity|].
  lazymatch goal with |- munch _ _ ?mm /\ _ =>
    assert (DJ : forall a n, (0 <= n)%Z -> (a + n <= FROM \/ FROM + 32 <= a)%Z -> (a + n <= bv_unsigned sp - 16 \/ bv_unsigned sp <= a)%Z ->
              disjoint_from [(FROM, FROM + 32); (bv_unsigned sp - 16, bv_unsigned sp)]%Z a n) by (intros; cbn [disjoint_from]; lia) end.
  split; [eapply munch_trans; [exact (unbox _ MU)| eapply munch_weaken; [| eassumption]]|].
  { intros x Hx. unfold mW in Hx. cbn [outside] in Hx |- *. clear - Hx. tauto. }
  split; [eassumption|]. split; [eassumption|].
  split; [| split; [| eassumption]].
  - apply (proj2 (qcache_rep_iff _ _ _)). split.
    + replace (qbytes gl + - (8192 * Z.of_nat (length X)))%Z with (qbytes L) in * by lia. eassumption.
    + apply (proj2 (qchain_to_0 _ _)). apply (qchain_to_frame _ m _ _ _ (unbox _ FC) MUe WMe).
      apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e ltac:(apply in_or_app; left; exact He)) as (E1 & E2).
      apply DJ; lia.
  - apply (proj2 (qcache_rep_iff _ _ _)). split.
    + rewrite (qbytes_empty_ents X HX). apply (rw_cells_transport ctasegs _ m _ _ _ (unbox _ TH) MUe WMe).
      apply DJ; cbn [cells_size csize Nat.add Z.of_nat]; lia.
    + apply (proj2 (qchain_to_0 _ _)). apply (qchain_to_frame _ m _ _ _ (unbox _ TC) MUe WMe).
      apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e ltac:(apply in_or_app; right; exact He)) as (E1 & E2).
      apply DJ; lia.
Qed.

(* [comment removed for export] *)
Lemma merge_fit : forall (K rest X : list batch) (b b' : Z) (e e' : list (Z * Z)) (m : mem) (P : machine_state -> Prop)
    (t1 t2 t3 t4 t5 t6 a3 : word),
  (Z.of_nat (length e + length e') <= 1021)%Z -> (bsum e + bsum e' < 2^56)%Z ->
  (Z.of_nat (length (K ++ (b, e) :: (b', e') :: rest)) < 2^50)%Z -> (Z.of_nat (length X) < 2^50)%Z ->
  merge_mem m FROM TO (qbytes gl) (K ++ (b, e) :: (b', e') :: rest) X ->
  qwf SB ((K ++ (b, e) :: (b', e') :: rest) ++ X) -> Forall (fun x => snd x = []) X ->
  mem_inv ctasegs m ->
  (forall (m' : mem) (t1' t2' t3' t4' t5' a3' : word),
     munch [(FROM, FROM + 32); (TO, TO + 32); (b, b + 8192); (b', b' + 24); ((if Z.of_nat (length X) =? 0 then b' else qlast X), (if Z.of_nat (length X) =? 0 then b' else qlast X) + 8)]%Z m m' -> wmono ctasegs m m' ->
     mem_inv ctasegs m' ->
     merge_mem m' FROM TO (qbytes gl) (K ++ (b, e ++ e') :: rest) (X ++ [(b', [])]) ->
     evt ctasegs P (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 (qfirst rest)) t1' t2' s0 s1 (Z_to_bv 64 FROM)
                          (Z_to_bv 64 TO) (Z_to_bv 64 (8192 * Z.of_nat (length (X ++ [(b', [])])))) a3' (Z_to_bv 64 b)
                          (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
                     F (Z_to_bv 64 0x19df90) fc None m' (seg_rom ctasegs))) ->
  evt ctasegs P (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 b') t1 t2 s0 s1 (Z_to_bv 64 FROM) (Z_to_bv 64 TO)
                       (Z_to_bv 64 (8192 * Z.of_nat (length X))) a3 (Z_to_bv 64 b) (Z_to_bv 64 1021) (Z_to_bv 64 (-8192))
                       (Z_to_bv 64 8192) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x19deb0) fc None m (seg_rom ctasegs)).
Proof.
  intros until a3. intros Hfit HBS HLb HXb (FH & CL & TH & CX) WF HX MI KC.
  apply (proj1 (qchain_split4 _ _ _ _ _ _ _)) in CL. destruct CL as (CK & QB & QB' & CR).
  apply (proj1 (qbatch_iff _ _ _ _)) in QB. destruct QB as (BH & (wc & BA & BL & BP) & Ble).
  apply (proj1 (qbatch_iff _ _ _ _)) in QB'. destruct QB' as (BH' & (wn & BA' & BL' & BP') & Ble').
  pose proof (qwf_region _ _ WF) as RG.
  pose proof (proj1 (Forall_forall _ _) RG (b, e) ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as (Hb1 & Hb2).
  pose proof (proj1 (Forall_forall _ _) RG (b', e') ltac:(apply in_or_app; left; apply in_or_app; right; right; left; reflexivity))
    as (Hb1' & Hb2').
  cbn [fst] in Hb1, Hb2, Hb1', Hb2'. apply box in RG. unfold r24 in *.
  assert (WFa : qwf SB (K ++ ((b, e) :: (b', e') :: rest ++ X))) by (rewrite <- app_assoc in WF; exact WF).
  assert (WFb : qwf SB ((K ++ [(b, e); (b', e')]) ++ (rest ++ X)))
    by (replace ((K ++ [(b, e); (b', e')]) ++ rest ++ X) with ((K ++ (b, e) :: (b', e') :: rest) ++ X) by (rewrite <- !app_assoc; reflexivity);
        exact WF).
  assert (WFc : qwf SB ((K ++ [(b, e)]) ++ ((b', e') :: rest ++ X)))
    by (replace ((K ++ [(b, e)]) ++ (b', e') :: rest ++ X) with ((K ++ (b, e) :: (b', e') :: rest) ++ X) by (rewrite <- !app_assoc; reflexivity);
        exact WF).
  pose proof (qwf_app_disj _ _ _ (b, e) (b', e') WFc ltac:(apply in_or_app; right; left; reflexivity) ltac:(left; reflexivity)) as Hbb.
  cbn [fst] in Hbb.
  pose proof (proj2 WF) as HF. apply Forall_app in HF. destruct HF as (HFL & HFX).
  pose proof (proj1 (Forall_forall _ _) HFL (b, e) ltac:(apply in_or_app; right; left; reflexivity)) as (_ & _ & _ & _ & Hbp).
  pose proof (proj1 (Forall_forall _ _) HFL (b', e') ltac:(apply in_or_app; right; right; left; reflexivity)) as (_ & _ & _ & _ & Hbp').
  cbn [snd] in Hbp, Hbp'. pose proof (bsum_nonneg _ Hbp) as Hs1. pose proof (bsum_nonneg _ Hbp') as Hs2.
  assert (XL : (Z.of_nat (length X) <> 0 -> rw_cells ctasegs m (qlast X) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 8192); C8 (Z_to_bv 64 0)])%Z).
  { intros Hne. destruct (snoc_cases X) as [->| (pre & [bl el] & ->)]; [cbn in Hne; lia|].
    rewrite qlast_snoc. apply (proj1 (qchain_to_snoc _ _ _ _ _)) in CX. destruct CX as (_ & QBL).
    apply (proj1 (qbatch_iff _ _ _ _)) in QBL. destruct QBL as (BLH & _ & _).
    pose proof (proj1 (Forall_forall _ _) HX (bl, el) ltac:(apply in_or_app; right; left; reflexivity)) as Hel. cbn [snd] in Hel.
    subst el. exact BLH. }
  assert (HXS : (Z.of_nat (length X) <> 0 -> (0 < qlast X /\ qlast X + 8192 <= 2^47) /\ (qlast X + 8192 <= b \/ b + 8192 <= qlast X)
                 /\ (qlast X + 8192 <= b' \/ b' + 8192 <= qlast X) /\ (FROM + 32 <= qlast X \/ qlast X + 8192 <= FROM)
                 /\ (TO + 32 <= qlast X \/ qlast X + 8192 <= TO))%Z).
  { intros Hne. assert (XNE : X <> []) by (intros ->; cbn in Hne; lia).
    pose proof (qlast_in X XNE) as HIN. apply in_map_iff in HIN. destruct HIN as (x & Ex & Hx). rewrite <- Ex.
    pose proof (proj1 (Forall_forall _ _) (unbox _ RG) x ltac:(apply in_or_app; right; exact Hx)) as (E1 & E2). unfold r24 in E1, E2.
    pose proof (qwf_app_disj _ _ _ (b, e) x WF ltac:(apply in_or_app; right; left; reflexivity) Hx) as S1.
    pose proof (qwf_app_disj _ _ _ (b', e') x WF ltac:(apply in_or_app; right; right; left; reflexivity) Hx) as S2.
    cbn [fst] in S1, S2. lia. }
  apply box in CK. apply box in CR. apply box in CX.
  eapply merge_fb1; [exact Hfit| exact Hbb| lia| lia| lia| exact BH| exact BH'| exact BA| exact BL| exact BP| exact BA'| exact BL'
                   | exact BP'| exact MI|].
  intros m1 wc' q2 q3 q4 q5 MU1 WM1 MI1 BA1 BL1 BP1.
  qtrans FH MU1 WM1. qtrans BH MU1 WM1. qtrans BH' MU1 WM1. qtrans TH MU1 WM1.
  assert (HL2 : (2 <= Z.of_nat (length (K ++ (b, e) :: (b', e') :: rest)))%Z) by (rewrite app_length; cbn [length]; lia).
  eapply merge_fb2 with (n0 := Z.of_nat (length (K ++ (b, e) :: (b', e') :: rest))); [exact Hbb| lia| lia| exact Hs1| exact Hs2| exact HBS| exact Hfit| lia| exact HF0| lia| lia| exact FH| exact BH
                   | exact BH'| exact MI1|].
  intros m2 q2' MU2 WM2 MI2 FH2 BH2 BH'2.
  qtrans TH MU2 WM2.
  assert (XL2 : (Z.of_nat (length X) <> 0 -> rw_cells ctasegs m2 (qlast X) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 8192); C8 (Z_to_bv 64 0)])%Z).
  { intros Hne. pose proof (HXS Hne) as (X1 & X2 & X3 & X4 & X5).
    apply (rw_cells_transport ctasegs _ _ _ _ _ (rw_cells_transport ctasegs _ _ _ _ _ (XL Hne) MU1 WM1
             ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) MU2 WM2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia. }
  pose proof (rw_cells_bound ctasegs _ _ _ TH) as HTB. cbn [cells_size csize Nat.add Z.of_nat] in HTB.
  eapply merge_fb3 with (xn := Z.of_nat (length X)) (xl := qlast X) (l0 := qlast (K ++ (b, e) :: (b', e') :: rest))
                         (nb' := qfirst rest) (n0 := Z.of_nat (length (K ++ (b, e) :: (b', e') :: rest))); [exact HF0| exact HFT| exact Hbb| lia| lia| lia| lia| lia| lia| lia| lia| | | lia| exact HXS| exact FH2| exact TH
                   | exact BH2| exact BH'2| exact XL2| exact MI2|].
  - pose proof (qlast_in (K ++ (b, e) :: (b', e') :: rest) ltac:(intros H0; apply app_eq_nil in H0; destruct H0 as (_ & H0); discriminate))
      as HIN.
    apply in_map_iff in HIN. destruct HIN as (x & Ex & Hx). rewrite <- Ex.
    pose proof (proj1 (Forall_forall _ _) (unbox _ RG) x ltac:(apply in_or_app; left; exact Hx)) as (E1 & E2). unfold r24 in E1, E2. lia.
  - destruct rest as [|[b'' e''] rest']; [cbn [qfirst]; lia|]. cbn [qfirst].
    pose proof (proj1 (Forall_forall _ _) (unbox _ RG) (b'', e'')
                  ltac:(apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity)) as (E1 & E2).
    unfold r24 in E1, E2. cbn [fst] in E1, E2. lia.
  - intros m3 q1 q2'' MU3 WM3 MI3 FH3 TH3 BH3 BH'3 XL3.
    eapply merge_fb4 with (ax := (8192 * Z.of_nat (length X))%Z); [lia| lia| lia| exact TH3| exact BH3| exact MI3|].
    intros m4 MU4 WM4 MI4 TH4 BH4.
    replace (8192 * Z.of_nat (length X) + 8192)%Z with (8192 * Z.of_nat (length (X ++ [(b', [])])))%Z by (rewrite app_length; cbn [length]; lia).
    assert (MUt : munch [(FROM, FROM + 32); (TO, TO + 32); (b, b + 8192); (b', b' + 24); ((if Z.of_nat (length X) =? 0 then b' else qlast X), (if Z.of_nat (length X) =? 0 then b' else qlast X) + 8)]%Z m m4).
    { eapply munch_trans; [eapply munch_trans; [eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]
                                               | eapply munch_weaken; [| exact MU3]]| eapply munch_weaken; [| exact MU4]];
        intros x Hx; clear - Hx; cbn [outside] in *; lia. }
    assert (WMt : wmono ctasegs m m4) by (eapply wmono_trans; [eapply wmono_trans; [eapply wmono_trans; [exact WM1| exact WM2]| exact WM3]| exact WM4]).
    assert (MUt1 : munch [(b, b + 24); (b', b' + 24); (FROM, FROM + 32); (TO, TO + 32); ((if Z.of_nat (length X) =? 0 then b' else qlast X), (if Z.of_nat (length X) =? 0 then b' else qlast X) + 8)]%Z m1 m4).
    { eapply munch_trans; [eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]
                          | eapply munch_weaken; [| exact MU4]]; intros x Hx; clear - Hx; cbn [outside] in *; lia. }
    assert (WMt1 : wmono ctasegs m1 m4) by (eapply wmono_trans; [eapply wmono_trans; [exact WM2| exact WM3]| exact WM4]).
    qtrans FH3 MU4 WM4. qtrans BH'3 MU4 WM4.
    assert (XL4 : (Z.of_nat (length X) <> 0 -> rw_cells ctasegs m4 (qlast X) [C8 (Z_to_bv 64 b'); C8 (Z_to_bv 64 8192); C8 (Z_to_bv 64 0)])%Z).
    { intros Hne. pose proof (HXS Hne) as (X1 & X2 & X3 & X4 & X5).
      apply (rw_cells_transport ctasegs _ _ _ _ _ (XL3 Hne) MU4 WM4). cbn [disjoint_from cells_size csize Nat.add Z.of_nat].
      clear - X1 X5. lia. }
    clear XL3 MU1 MU2 MU3 MU4 WM1 WM2 WM3 WM4.
    (* [comment removed for export] *)
    assert (DJW : forall x, In x (K ++ rest) \/ (In x X /\ fst x <> qlast X) ->
              disjoint_from [(FROM, FROM + 32); (TO, TO + 32); (b, b + 8192); (b', b' + 24); ((if Z.of_nat (length X) =? 0 then b' else qlast X), (if Z.of_nat (length X) =? 0 then b' else qlast X) + 8)]%Z (fst x) 8192).
    { intros x Hx.
      assert (HxIn : In x ((K ++ (b, e) :: (b', e') :: rest) ++ X)).
      { destruct Hx as [Hx|(Hx & _)]; [apply in_app_or in Hx; destruct Hx as [Hx|Hx]|].
        - apply in_or_app; left; apply in_or_app; left; exact Hx.
        - apply in_or_app; left; apply in_or_app; right; right; right; exact Hx.
        - apply in_or_app; right; exact Hx. }
      pose proof (proj1 (Forall_forall _ _) (unbox _ RG) x HxIn) as (E1 & E2). unfold r24 in E1, E2.
      assert (SB1 : (fst x + 8192 <= b \/ b + 8192 <= fst x)%Z /\ (fst x + 8192 <= b' \/ b' + 8192 <= fst x)%Z).
      { destruct Hx as [Hx|(Hx & _)]; [apply in_app_or in Hx; destruct Hx as [Hx|Hx]|].
        - pose proof (qwf_app_disj _ _ _ x (b, e) WFa Hx ltac:(left; reflexivity)) as S1.
          pose proof (qwf_app_disj _ _ _ x (b', e') WFa Hx ltac:(right; left; reflexivity)) as S2. cbn [fst] in S1, S2. clear - S1 S2. lia.
        - pose proof (qwf_app_disj _ _ _ (b, e) x WFb ltac:(apply in_or_app; right; left; reflexivity) ltac:(apply in_or_app; left; exact Hx))
            as S1.
          pose proof (qwf_app_disj _ _ _ (b', e') x WFb ltac:(apply in_or_app; right; right; left; reflexivity)
                        ltac:(apply in_or_app; left; exact Hx)) as S2. cbn [fst] in S1, S2. clear - S1 S2. lia.
        - pose proof (qwf_app_disj _ _ _ (b, e) x WF ltac:(apply in_or_app; right; left; reflexivity) Hx) as S1.
          pose proof (qwf_app_disj _ _ _ (b', e') x WF ltac:(apply in_or_app; right; right; left; reflexivity) Hx) as S2.
          cbn [fst] in S1, S2. clear - S1 S2. lia. }
      assert (SX : (fst x + 8192 <= (if Z.of_nat (length X) =? 0 then b' else qlast X) \/ (if Z.of_nat (length X) =? 0 then b' else qlast X) + 8 <= fst x)%Z).
      { destruct X as [|x0 X0] eqn:EX; [change (Z.of_nat (length (@nil batch)) =? 0)%Z with true; cbv iota; clear - SB1; lia|].
        rewrite (proj2 (Z.eqb_neq (Z.of_nat (length (x0 :: X0))) 0)) by (cbn [length]; lia).
        pose proof (qlast_in (x0 :: X0) ltac:(discriminate)) as HIN. apply in_map_iff in HIN. destruct HIN as (z & Ez & Hz). rewrite <- Ez.
        destruct Hx as [Hx|(Hx & Hne)].
        - assert (HxL : In x (K ++ (b, e) :: (b', e') :: rest)).
          { apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply in_or_app; left; exact Hx| apply in_or_app; right; right; right; exact Hx]. }
          pose proof (qwf_app_disj _ _ _ x z WF HxL Hz) as S. clear - S. lia.
        - pose proof (proj1 (Forall_forall _ _) (proj2 WF) x HxIn) as (A1 & _).
          pose proof (proj1 (Forall_forall _ _) (proj2 WF) z ltac:(apply in_or_app; right; exact Hz)) as (A2 & _).
          rewrite <- Ez in Hne. pose proof (align_disj _ _ A1 A2 Hne) as S. clear - S. lia. }
      cbn [disjoint_from]. unfold r24 in *. clear - E1 E2 SB1 SX HFS HTS HSB. lia. }
    eapply KC; [exact MUt| exact WMt| exact MI4|].
    unfold merge_mem. split; [| split; [| split]].
    + (* [comment removed for export] *)
      rewrite (qfirst_app_cons K b (e ++ e') e rest ((b', e') :: rest)). rewrite <- (merge_qlast SB K b e b' e' (e ++ e') rest X WF).
      replace (Z.of_nat (length (K ++ (b, e ++ e') :: rest))) with (Z.of_nat (length (K ++ (b, e) :: (b', e') :: rest)) - 1)%Z
        by (rewrite !app_length; cbn [length]; lia).
      exact FH3.
    + (* [comment removed for export] *)
      apply (proj2 (qchain_split3 _ _ _ _ _)). split; [| split].
      * apply (qchain_to_frame _ m m4 _ _ (unbox _ CK) MUt WMt). apply Forall_forall. intros x Hx. apply DJW. left. apply in_or_app. left. exact Hx.
      * apply (proj2 (qbatch_iff _ _ _ _)). split; [exact BH4| split; [exists wc'; split; [| split; [exact BL1| exact BP1]]|]].
        -- apply (u64arr_transport ctasegs _ m1 m4 _ _ BA1 MUt1 WMt1). rewrite BL1.
           destruct (Z.eq_dec (Z.of_nat (length X)) 0) as [H0|H0].
           ++ rewrite (proj2 (Z.eqb_eq _ _) H0). cbv iota. cbn [disjoint_from]. clear - Hbb HFS HTS Hb1 Hb2 HSB. lia.
           ++ rewrite (proj2 (Z.eqb_neq _ _) H0). cbv iota.
              pose proof (HXS H0) as (X1 & X2 & X3 & X4 & X5). cbn [disjoint_from]. clear - Hbb HFS HTS Hb1 Hb2 HSB X1 X2 X3 X4 X5. lia.
        -- rewrite app_length. lia.
      * apply (qchain_to_frame _ m m4 _ _ (unbox _ CR) MUt WMt). apply Forall_forall. intros x Hx. apply DJW. left. apply in_or_app. right. exact Hx.
    + (* [comment removed for export] *)
      rewrite app_length, qlast_snoc. cbn [length].
      replace (Z.of_nat (length X + 1)) with (Z.of_nat (length X) + 1)%Z by lia.
      replace (8192 * (Z.of_nat (length X) + 1))%Z with (8192 * Z.of_nat (length X) + 8192)%Z by lia.
      destruct X as [|x0 X0]; [exact TH4|].
      rewrite (qfirst_app_ne (x0 :: X0) [(b', [])]) by discriminate.
      rewrite (proj2 (Z.eqb_neq (Z.of_nat (length (x0 :: X0))) 0)) in TH4 by (cbn [length]; lia). exact TH4.
    + (* [comment removed for export] *)
      apply (proj2 (qchain_to_snoc _ _ _ _ _)). split.
      * destruct (snoc_cases X) as [EX| (pre & [bl el] & EX)]; [subst X; exact I|].
        pose proof (proj1 (Forall_forall _ _) HX (bl, el) ltac:(rewrite EX; apply in_or_app; right; left; reflexivity)) as Hel.
        cbn [snd] in Hel. subst el.
        pose proof (unbox _ CX) as CX0. rewrite EX in CX0. pose proof (proj1 (qchain_to_snoc _ _ _ _ _) CX0) as (CP & QBL). clear CX0.
        apply (proj1 (qbatch_iff _ _ _ _)) in QBL. destruct QBL as (_ & (wsl & BLA & BLL & BLP) & _).
        assert (HnX : (Z.of_nat (length X) <> 0)%Z) by (rewrite EX, app_length; cbn [length]; clear; lia).
        pose proof (XL4 HnX) as XLm. pose proof (HXS HnX) as (X1 & X2 & X3 & X4 & X5). rewrite EX, qlast_snoc in XLm, X1, X2, X3, X4, X5.
        rewrite EX. apply (proj2 (qchain_to_snoc _ _ _ _ _)). split.
        -- apply (qchain_to_frame _ m m4 _ _ CP MUt WMt). apply Forall_forall. intros x Hx. apply DJW. right. split.
           ++ rewrite EX. apply in_or_app. left. exact Hx.
           ++ rewrite EX, qlast_snoc. intros Hxb.
              pose proof (qwf_snoc_disj _ _ _ _ (qwf_suffix _ _ _ (eq_ind X (fun l => qwf SB (_ ++ l)) WF _ EX))) as DJP.
              pose proof (proj1 (Forall_forall _ _) DJP x Hx) as S. cbv beta in S. clear - S Hxb. lia.
        -- apply (proj2 (qbatch_iff _ _ _ _)). split; [exact XLm| split; [exists wsl; split; [| split; [exact BLL| exact BLP]]| cbn; lia]].
           apply (u64arr_transport ctasegs _ m m4 _ _ BLA MUt WMt). rewrite BLL. rewrite (proj2 (Z.eqb_neq _ _) HnX). cbv iota.
           rewrite EX, qlast_snoc. cbn [disjoint_from]. clear - X1 X2 X3 X4 X5. lia.
      * apply (proj2 (qbatch_iff _ _ _ _)). split; [exact BH'3| split; [exists wn; split; [| split; [exact BL'| reflexivity]]| cbn; lia]].
        apply (u64arr_transport ctasegs _ m m4 _ _ BA' MUt WMt). rewrite BL'.
        destruct (Z.eq_dec (Z.of_nat (length X)) 0) as [H0|H0].
        -- rewrite (proj2 (Z.eqb_eq _ _) H0). cbv iota. cbn [disjoint_from]. clear - Hbb HFS HTS Hb1' Hb2' HSB. lia.
        -- rewrite (proj2 (Z.eqb_neq _ _) H0). cbv iota.
           pose proof (HXS H0) as (X1 & X2 & X3 & X4 & X5). cbn [disjoint_from]. clear - Hbb HFS HTS Hb1' Hb2' HSB X1 X2 X3 X4 X5. lia.
Qed.

Lemma qbytes_cons' : forall b e l, qbytes ((b, e) :: l) = (8192 + bsum e + qbytes l)%Z.
Proof. reflexivity. Qed.

Lemma merge_bytes_inv : forall K X cur rest, merge_all gl = (K ++ fst (merge_walk cur rest), X ++ snd (merge_walk cur rest)) ->
  (qbytes K + qbytes X + qbytes (cur :: rest) = qbytes gl)%Z.
Proof.
  intros K X cur rest H. pose proof (merge_all_bytes gl) as MB. rewrite H in MB. cbn [fst snd] in MB. rewrite !qbytes_app in MB.
  pose proof (merge_walk_bytes rest cur). lia.
Qed.

Lemma in_gl_outside : forall x a, In a (map fst gl) -> outside (bivs gl) x -> ~ (a <= x < a + 8192)%Z.
Proof.
  intros x a Ha Hx. apply outside_bivs in Hx. apply in_map_iff in Ha. destruct Ha as (e0 & E0 & He0).
  pose proof (proj1 (Forall_forall _ _) Hx e0 He0) as H. cbv beta in H. rewrite E0 in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma fit_sub : forall (K rest X : list batch) (b b' : Z) (e e' : list (Z * Z)),
  Permutation (map fst ((K ++ (b, e) :: (b', e') :: rest) ++ X)) (map fst gl) ->
  sub_fp [(FROM, FROM + 32); (TO, TO + 32); (b, b + 8192); (b', b' + 24);
          (if Z.of_nat (length X) =? 0 then b' else qlast X, (if Z.of_nat (length X) =? 0 then b' else qlast X) + 8)]%Z mW.
Proof.
  intros K rest X b b' e e' PM x Hx. unfold mW in Hx. cbn [outside] in Hx. destruct Hx as (H1 & H2 & H3 & H4). cbn [outside].
  assert (Ib : In b (map fst gl)).
  { apply (Permutation_in _ PM). rewrite !map_app. apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  assert (Ib' : In b' (map fst gl)).
  { apply (Permutation_in _ PM). rewrite !map_app. apply in_or_app. left. apply in_or_app. right. right. left. reflexivity. }
  pose proof (in_gl_outside x b Ib H4) as O1. pose proof (in_gl_outside x b' Ib' H4) as O2.
  assert (O3 : ~ ((if Z.of_nat (length X) =? 0 then b' else qlast X) <= x < (if Z.of_nat (length X) =? 0 then b' else qlast X) + 8)%Z).
  { destruct (Z.eqb_spec (Z.of_nat (length X)) 0) as [E0|E0]; [lia|].
    assert (XNE : X <> []) by (intros ->; cbn in E0; lia).
    assert (Ix : In (qlast X) (map fst gl)).
    { apply (Permutation_in _ PM). rewrite map_app. apply in_or_app. right. apply qlast_in. exact XNE. }
    pose proof (in_gl_outside x _ Ix H4). lia. }
  repeat split; try lia; exact O3.
Qed.

Lemma xc_region : forall (K rest X : list batch) (b b' : Z) (e e' : list (Z * Z)), qwf SB ((K ++ (b, e) :: (b', e') :: rest) ++ X) ->
  (r24 SB <= (if Z.of_nat (length X) =? 0 then b' else qlast X) /\ (if Z.of_nat (length X) =? 0 then b' else qlast X) + 8192 <= r24 SB + 2^32)%Z.
Proof.
  intros K rest X b b' e e' WF. pose proof (qwf_region _ _ WF) as RG.
  destruct (Z.eqb_spec (Z.of_nat (length X)) 0) as [E0|E0].
  - exact (proj1 (Forall_forall _ _) RG (b', e') ltac:(apply in_or_app; left; apply in_or_app; right; right; left; reflexivity)).
  - assert (XNE : X <> []) by (intros ->; cbn in E0; lia).
    pose proof (qlast_in X XNE) as HIN. apply in_map_iff in HIN. destruct HIN as (x & Ex & Hx). rewrite <- Ex.
    exact (proj1 (Forall_forall _ _) RG x ltac:(apply in_or_app; right; exact Hx)).
Qed.

(* [comment removed for export] *)
Lemma merge_loop : forall (rest K : list batch) (b : Z) (e : list (Z * Z)) (b' : Z) (e' : list (Z * Z)) (X : list batch)
    (m : mem) (j0 : list byte) (t1 t2 t3 t4 t5 t6 a3 : word),
  merge_mem m FROM TO (qbytes gl) (K ++ (b, e) :: (b', e') :: rest) X ->
  qwf SB ((K ++ (b, e) :: (b', e') :: rest) ++ X) -> Forall (fun x => snd x = []) X ->
  Permutation (map fst ((K ++ (b, e) :: (b', e') :: rest) ++ X)) (map fst gl) ->
  merge_all gl = (K ++ fst (merge_walk (b, e) ((b', e') :: rest)), X ++ snd (merge_walk (b, e) ((b', e') :: rest))) ->
  rw_cells ctasegs m (bv_unsigned sp + -16) [CB 8 j0] -> rw_cells ctasegs m (bv_unsigned sp + -8) [C8 ra] ->
  stk ctasegs m lo (bv_unsigned sp + -16) ->
  munch mW m0 m -> wmono ctasegs m0 m -> mem_inv ctasegs m ->
  evt ctasegs (merge_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FROM TO gl lo m0)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 b') t1 t2 s0 s1 (Z_to_bv 64 FROM) (Z_to_bv 64 TO)
             (Z_to_bv 64 (8192 * Z.of_nat (length X))) a3 (Z_to_bv 64 b) (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19deb0) fc None m (seg_rom ctasegs)).
Proof.
  induction rest as [|[b'' e''] rest IH]; intros K b e b' e' X m j0 t1 t2 t3 t4 t5 t6 a3 MM WF HX PM EQ FR0 FR ST MU WM MI.
  all: pose proof (merge_bytes_inv _ _ _ _ EQ) as HQB.
  all: pose proof (Permutation_length PM) as PL; rewrite !map_length, !app_length in PL.
  all: pose proof (qbytes_ge _ _ HWG) as QG; pose proof (qwf_prefix _ _ _ WF) as WFL; pose proof (qwf_suffix _ K _ WFL) as WFR;
       pose proof (qbytes_nonneg _ _ (qwf_prefix _ _ _ WFL)) as QK; pose proof (qbytes_nonneg _ _ WFR) as QR.
  all: pose proof (qbytes_nonneg _ _ (qwf_suffix _ _ _ WF)) as QX.
  all: pose proof (proj2 WF) as HF; apply Forall_app in HF; destruct HF as (HFL & _); apply Forall_app in HFL; destruct HFL as (_ & HFL).
  all: inversion HFL as [|? ? (Hb8 & Hb1 & Hb2 & Hble & Hbp) HFL1]; subst; inversion HFL1 as [|? ? (Hb8' & Hb1' & Hb2' & Hble' & Hbp') HFL2]; subst.
  all: cbn [fst snd] in *. all: pose proof (bsum_nonneg _ Hbp) as Hs1; pose proof (bsum_nonneg _ Hbp') as Hs2.
  all: rewrite (qbytes_cons' b e), (qbytes_cons' b' e') in HQB, QR.
  all: pose proof (qbytes_nonneg _ _ (qwf_suffix SB [(b, e); (b', e')] _ WFR)) as QRest.
  all: unfold r24 in *.
  all: destruct (Z.leb_spec (Z.of_nat (length e + length e')) 1021) as [Hfit|Hnf].
  - (* [comment removed for export] *)
    eapply (merge_fit K [] X b b' e e' m _ t1 t2 t3 t4 t5 t6 a3); [exact Hfit| lia| rewrite app_length; cbn [length] in *; lia| lia
                                                                 | exact MM| exact WF| exact HX| exact MI|].
    intros m' q1 q2 q3 q4 q5 q6 MUf WMf MIf MMf.
    change (qfirst (@nil batch)) with 0%Z.
    zstep. ifF.
    pose proof (xc_region K [] X b b' e e' WF) as HXC. unfold r24 in HXC.
    cbn [merge_walk] in EQ. rewrite (proj2 (Z.leb_le _ _) Hfit) in EQ. cbn [fst snd] in EQ.
    eapply (merge_exit (K ++ [(b, e ++ e')]) (X ++ [(b', [])]) m' j0); [exact MMf| exact EQ| | | | | | | | exact MIf].
    + apply Forall_app. split; [exact HX| constructor; [reflexivity| constructor]].
    + apply (merge_fit_wf SB K [] X b b' e e' WF). rewrite app_length. lia.
    + apply (rw_cells_transport ctasegs _ m m' _ _ FR0 MUf WMf). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. clear - HXC HFl HTSP HLO Hb2 Hb2' HRl. lia.
    + apply (rw_cells_transport ctasegs _ m m' _ _ FR MUf WMf). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. clear - HXC HFl HTSP HLO Hb2 Hb2' HRl. lia.
    + apply (stk_transport_disjoint ctasegs _ m m' _ _ ST MUf WMf). cbn [disjoint_from]. clear - HXC HFl HTSP HLO Hb2 Hb2' HRl. lia.
    + eapply munch_trans; [exact MU| eapply munch_weaken; [apply (fit_sub K [] X b b' e e' PM)| exact MUf]].
    + eapply wmono_trans; [exact WM| exact WMf].
  - (* [comment removed for export] *)
    pose proof MM as MM0. destruct MM0 as (FH & CL & TH & CX).
    apply (proj1 (qchain_split4 _ _ _ _ _ _ _)) in CL. destruct CL as (_ & QB & QB' & _).
    apply (proj1 (qbatch_iff _ _ _ _)) in QB. destruct QB as (BH & _ & _).
    apply (proj1 (qbatch_iff _ _ _ _)) in QB'. destruct QB' as (BH' & _ & _).
    change (qfirst (@nil batch)) with 0%Z in BH'.
    do 3 zstep. zstep. ifT.
    do 2 zstep. zstep. ifT.
    cbn [merge_walk] in EQ. rewrite (proj2 (Z.leb_gt _ _) Hnf) in EQ. cbn [fst snd merge_walk] in EQ. rewrite app_nil_r in EQ.
    eapply (merge_exit (K ++ [(b, e); (b', e')]) X m j0); [exact MM| exact EQ| exact HX| exact WF| exact FR0| exact FR| exact ST| exact MU
                                                           | exact WM| exact MI].
  - (* [comment removed for export] *)
    eapply (merge_fit K ((b'', e'') :: rest) X b b' e e' m _ t1 t2 t3 t4 t5 t6 a3);
      [exact Hfit| lia| rewrite app_length; cbn [length] in *; lia| lia| exact MM| exact WF| exact HX| exact MI|].
    intros m' q1 q2 q3 q4 q5 q6 MUf WMf MIf MMf.
    change (qfirst ((b'', e'') :: rest)) with b''.
    inversion HFL2 as [|? ? (_ & Hb1'' & Hb2'' & _) _]; subst. cbn [fst] in Hb1'', Hb2''.
    zstep. ifT.
    pose proof (xc_region K ((b'', e'') :: rest) X b b' e e' WF) as HXC. unfold r24 in HXC.
    cbn [merge_walk] in EQ. rewrite (proj2 (Z.leb_le _ _) Hfit) in EQ. cbn [fst snd] in EQ.
    replace (X ++ (b', []) :: snd (merge_walk (b, e ++ e') ((b'', e'') :: rest)))
      with ((X ++ [(b', [])]) ++ snd (merge_walk (b, e ++ e') ((b'', e'') :: rest))) in EQ by (rewrite <- app_assoc; reflexivity).
    eapply (IH K b (e ++ e') b'' e'' (X ++ [(b', [])]) m' j0); [exact MMf| | | | exact EQ| | | | | | exact MIf].
    + apply (merge_fit_wf SB K ((b'', e'') :: rest) X b b' e e' WF). rewrite app_length. lia.
    + apply Forall_app. split; [exact HX| constructor; [reflexivity| constructor]].
    + eapply Permutation_trans; [apply merge_fit_perm| exact PM].
    + apply (rw_cells_transport ctasegs _ m m' _ _ FR0 MUf WMf). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. clear - HXC HFl HTSP HLO Hb2 Hb2' HRl. lia.
    + apply (rw_cells_transport ctasegs _ m m' _ _ FR MUf WMf). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. clear - HXC HFl HTSP HLO Hb2 Hb2' HRl. lia.
    + apply (stk_transport_disjoint ctasegs _ m m' _ _ ST MUf WMf). cbn [disjoint_from]. clear - HXC HFl HTSP HLO Hb2 Hb2' HRl. lia.
    + eapply munch_trans; [exact MU| eapply munch_weaken; [apply (fit_sub K ((b'', e'') :: rest) X b b' e e' PM)| exact MUf]].
    + eapply wmono_trans; [exact WM| exact WMf].
  - (* [comment removed for export] *)
    pose proof MM as MM0. destruct MM0 as (FH & CL & TH & CX).
    apply (proj1 (qchain_split4 _ _ _ _ _ _ _)) in CL. destruct CL as (_ & QB & QB' & _).
    apply (proj1 (qbatch_iff _ _ _ _)) in QB. destruct QB as (BH & _ & _).
    apply (proj1 (qbatch_iff _ _ _ _)) in QB'. destruct QB' as (BH' & _ & _).
    change (qfirst ((b'', e'') :: rest)) with b'' in BH'.
    inversion HFL2 as [|? ? (_ & Hb1'' & Hb2'' & _) _]; subst. cbn [fst] in Hb1'', Hb2''.
    do 3 zstep. zstep. ifT.
    do 2 zstep. zstep. ifF.
    cbn [merge_walk] in EQ. rewrite (proj2 (Z.leb_gt _ _) Hnf) in EQ. cbn [fst snd] in EQ.
    replace (K ++ (b, e) :: fst (merge_walk (b', e') ((b'', e'') :: rest)))
      with ((K ++ [(b, e)]) ++ fst (merge_walk (b', e') ((b'', e'') :: rest))) in EQ by (rewrite <- app_assoc; reflexivity).
    eapply (IH (K ++ [(b, e)]) b' e' b'' e'' X m j0); [| | exact HX| | exact EQ| exact FR0| exact FR| exact ST| exact MU| exact WM| exact MI].
    + rewrite <- (app_assoc K [(b, e)] ((b', e') :: (b'', e'') :: rest)). exact MM.
    + rewrite <- (app_assoc K [(b, e)] ((b', e') :: (b'', e'') :: rest)). exact WF.
    + rewrite <- (app_assoc K [(b, e)] ((b', e') :: (b'', e'') :: rest)). exact PM.
Qed.

End MLOOP.

(* [comment removed for export] *)
Lemma merge_spec : merge_stmt.
Proof.
  unfold merge_stmt. intros until gl. intros QR TR WF HBY HSB HF0 HFS HTS HFT HTSP ST HLO HRl HFl HSP MI.
  pose proof QR as QR0. apply (proj1 (qcache_rep_iff _ _ _)) in QR0. destruct QR0 as (QH & QC).
  pose proof TR as TR0. apply (proj1 (qcache_rep_iff _ _ _)) in TR0. destruct TR0 as (TH & _).
  cbn [length Z.of_nat qfirst qlast qbytes map last fold_right] in TH.
  pose proof (qwf_region _ _ WF) as RG. apply box in RG.
  unfold qmerge_entry, r24 in *.
  pose proof (munch_refl [(FROM, FROM + 32); (bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  carve_frame 8%nat ST. carve_frame 8%nat ST.
  do 2 zstep.
  destruct gl as [|[b0 e0] rest0].
  - (* [comment removed for export] *)
    change (qfirst (@nil batch)) with 0%Z in QH. clear RG.
    zstep. zstep. ifT.
    do 5 zstep.
    release_frame FR0 ST (bv_unsigned sp + -8)%Z. release_frame FR ST (bv_unsigned sp).
    zstep.
    apply evt_done. unfold merge_post. cbn [merge_all fst snd bivs map].
    do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| eassumption]; intros x Hx; clear - Hx; cbn [outside] in *; tauto|].
    split; [eassumption|]. split; [eassumption|]. split; [| split; [| eassumption]].
    + apply (proj2 (qcache_rep_iff _ _ _)). split; [| exact I]. cbn [length Z.of_nat qfirst qlast qbytes map last fold_right].
      replace (0 + - 0)%Z with 0%Z in * by reflexivity. eassumption.
    + apply (qcache_rep_frame' _ m _ _ _ TR ltac:(eassumption) ltac:(eassumption)); [cbn [disjoint_from]; clear - HFT HTSP HLO; lia| constructor].
  - pose proof (proj1 (qchain_to_0 _ _) QC) as QC1.
    apply (proj1 (qchain_split3 _ [] b0 e0 rest0)) in QC1. destruct QC1 as (_ & QB0 & _).
    apply (proj1 (qbatch_iff _ _ _ _)) in QB0. destruct QB0 as (BH0 & _ & _).
    change (qfirst ((b0, e0) :: rest0)) with b0 in QH.
    pose proof (proj1 (Forall_forall _ _) (unbox _ RG) (b0, e0) ltac:(left; reflexivity)) as (Hb01 & Hb02). cbn [fst] in Hb01, Hb02.
    unfold r24 in Hb01, Hb02.
    qtrans BH0 MU WM.
    zstep. zstep. ifF.
    zstep. zstep.
    destruct rest0 as [|[b1 e1] rest1].
    + (* [comment removed for export] *)
      change (qfirst (@nil batch)) with 0%Z in *. ifT.
      do 5 zstep.
      release_frame FR0 ST (bv_unsigned sp + -8)%Z. release_frame FR ST (bv_unsigned sp).
      zstep.
      apply evt_done. unfold merge_post. cbn [merge_all merge_walk fst snd].
      do 16 eexists. split; [reflexivity|].
      split; [eapply munch_weaken; [| eassumption]; intros x Hx; clear - Hx; cbn [outside] in *; tauto|].
      split; [eassumption|]. split; [eassumption|]. split; [| split; [| eassumption]].
      * apply (proj2 (qcache_rep_iff _ _ _)). split.
        -- replace (qbytes [(b0, e0)] + - 0)%Z with (qbytes [(b0, e0)]) in QH by lia. exact QH.
        -- apply (proj2 (qchain_to_0 _ _)). apply (qchain_to_frame _ m _ _ _ (proj1 (qchain_to_0 _ _) QC) ltac:(eassumption) ltac:(eassumption)).
           constructor; [| constructor]. cbn [disjoint_from fst]. clear - Hb01 Hb02 HFS HRl HLO. lia.
      * apply (qcache_rep_frame' _ m _ _ _ TR ltac:(eassumption) ltac:(eassumption)); [cbn [disjoint_from]; clear - HFT HTSP HLO; lia| constructor].
    + change (qfirst ((b1, e1) :: rest1)) with b1 in *.
      pose proof (proj1 (Forall_forall _ _) (unbox _ RG) (b1, e1) ltac:(right; left; reflexivity)) as (Hb11 & Hb12). cbn [fst] in Hb11, Hb12.
      unfold r24 in Hb11, Hb12.
      ifF.
      do 5 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (merge_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FROM TO SB lo ((b0, e0) :: (b1, e1) :: rest1) m)
          with (K := []) (X := []) (m := mm) (e := e0) (e' := e1) (rest := rest1) end.
      all: try eassumption; try lia.
      * unfold merge_mem. cbn [app]. split; [exact QH| split; [| split; [exact TH| exact I]]].
        apply (qchain_to_frame _ m _ _ _ (proj1 (qchain_to_0 _ _) QC) ltac:(eassumption) ltac:(eassumption)).
        apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) (unbox _ RG) x Hx) as (E1 & E2). unfold r24 in E1, E2.
        cbn [disjoint_from]. clear - E1 E2 HFS HRl HLO. lia.
      * rewrite app_nil_r. exact WF.
      * constructor.
      * rewrite app_nil_r. apply Permutation_refl.
      * cbn [merge_all app]. destruct (merge_walk (b0, e0) ((b1, e1) :: rest1)). reflexivity.
      * eapply munch_weaken; [| eassumption]. intros x Hx. clear - Hx. unfold mW in Hx. cbn [outside] in *. tauto.
Qed.

