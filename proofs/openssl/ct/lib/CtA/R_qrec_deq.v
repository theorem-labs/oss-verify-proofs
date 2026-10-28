(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk Image. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_quar_defs R_qrec_defs R_qput R_qdrain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call ctasegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma snoc_cases : forall {X} (l : list X), l = [] \/ exists l' x, l = l' ++ [x].
Proof.
  intros X l. induction l as [|y l IH]; [left; reflexivity| right].
  destruct IH as [->|(l' & x & ->)]; [exists [], y; reflexivity| exists (y :: l'), x; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma sub_fp_batch : forall (W0 : list (Z * Z)) L b e k, In (b, e) L -> (0 <= k <= 8192)%Z ->
  forall x, outside (W0 ++ bivs L) x -> ~ (b <= x < b + k)%Z.
Proof.
  intros W0 L b e k Hin Hk x H Hx. apply outside_app in H. destruct H as (_ & H).
  apply (inside_bivs L (b, e) x Hin); [cbn; lia| exact H].
Qed.

Lemma in_batch_outside : forall L b e k x, In (b, e) L -> (0 <= k <= 8192)%Z -> outside (bivs L) x -> ~ (b <= x < b + k)%Z.
Proof. intros L b e k x Hin Hk H Hx. apply (inside_bivs L (b, e) x Hin); [cbn; lia| exact H]. Qed.

Section DEQ.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 CACHE STACK : word) (F : bvmap 5 word) (fc : bv 32).
Variables (MIN SB TMP : Z).
Hypothesis HMIN : (0 <= MIN < 2^63)%Z.
Hypothesis HSB : (0 < SB)%Z.
Hypothesis HTMP : (r24 SB + 2^32 <= TMP /\ TMP + 32 <= 2^47)%Z.

(* [comment removed for export] *)
Definition deq_post (W : list (Z * Z)) (XD d r : list batch) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 TMP) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 MIN) CACHE STACK a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19ddec) fc None m' (seg_rom ctasegs)
    /\ munch W m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ qcache_rep m' QG r /\ qcache_rep m' TMP (XD ++ d).

Lemma deq_last : forall (B : batch) (XD : list batch) (m : mem) (t1 t2 a5 a7 w0 w2 : word),
  (MIN < qbytes [B])%Z -> qwf SB (XD ++ [B]) -> (qbytes (XD ++ [B]) < 2^56)%Z ->
  rw_cells ctasegs m QG [C8 (Z_to_bv 64 (Z.of_nat (length [B]))); C8 (Z_to_bv 64 (fst B)); C8 (Z_to_bv 64 (qlast [B]));
                       C8 (Z_to_bv 64 (qbytes [B]))] ->
  qchain_to m [B] 0 ->
  rw_cells ctasegs m TMP [C8 w0; C8 (Z_to_bv 64 (qfirst XD)); C8 w2; C8 (Z_to_bv 64 (qbytes XD))] ->
  qchain_to m XD 0 -> (XD <> [] -> a5 = Z_to_bv 64 (qlast XD)) ->
  mem_inv ctasegs m ->
  evt ctasegs (deq_post ([(QG, QG + 32); (TMP, TMP + 32)] ++ bivs (XD ++ [B]))%Z
               XD (fst (deq [B] (qbytes [B]) MIN)) (snd (deq [B] (qbytes [B]) MIN)) m)
    (MS (mkR ra (Z_to_bv 64 TMP) gp tp (Z_to_bv 64 (fst B)) t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 MIN) CACHE STACK
             (Z_to_bv 64 (Z.of_nat (length XD))) a5 (Z_to_bv 64 (Z.of_nat (length [B]))) a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19dd90) fc None m (seg_rom ctasegs)).
Proof.
  intros [b eb] XD m t1 t2 a5 a7 w0 w2 HB WF HBY QGH QC TH TC Ha5 MI.
  cbn [qchain_to] in QC. destruct QC as (QB & _).
  apply (proj1 (qbatch_iff _ _ _ _)) in QB. destruct QB as (BH & BA & Ble). apply box in BA.
  pose proof (qwf_region _ _ WF) as RG. apply box in RG.
  assert (ED : deq [(b, eb)] (qbytes [(b, eb)]) MIN = ([(b, eb)], [])).
  { cbn [deq]. destruct (Z.leb_spec (qbytes [(b, eb)]) MIN); [lia| reflexivity]. }
  rewrite ED. cbn [fst snd].
  cbn [length Z.of_nat qlast map last fst snd qbytes fold_right] in QGH, HB.
  unfold r24 in *.
  pose proof (qwf_last _ _ _ _ WF) as (Hb8 & Hb1 & Hb2 & _ & Hebs). unfold r24 in Hb1, Hb2.
  pose proof (bsum_nonneg _ Hebs) as BSN.
  rewrite qbytes_app in HBY. pose proof (qbytes_nonneg SB XD (qwf_prefix _ _ _ WF)) as QXN.
  cbn [qbytes fold_right fst snd] in HBY.
  destruct (snoc_cases XD) as [->|(XD' & [xl el] & ->)].
  + (* [comment removed for export] *)
    cbn [length Z.of_nat qfirst qbytes fold_right] in TH |- *.
    pose proof (munch_refl [(6745424, 6745424 + 32); (TMP, TMP + 32); (b, b + 8)]%Z m) as MU.
    pose proof (wmono_refl ctasegs m) as WM.
    zhide.
    zstep. ifF.
    zstep. zstep; fix_lit_store. zstep. ifF. zstep; fix_lit_store.
    do 7 zstep. zstep; fix_lit_store.
    zstep. ifF.
    zstep. zstep. zstep.
    do 4 zstep. do 5 zstep. ifT.
    zstep. zstep.
    cbn [app].
    apply evt_done. unfold deq_post. do 8 eexists. split; [reflexivity|].
    split.
    { eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in Hx. destruct Hx as (H1 & H2 & H3).
      pose proof (in_batch_outside [(b, eb)] b eb 8 x (or_introl eq_refl) ltac:(lia) H3) as H4.
      cbn [outside]. tauto. }
    split; [eassumption|]. split; [eassumption|]. split.
    * apply (proj2 (qcache_rep_iff _ _ _)). cbn [length Z.of_nat qfirst qlast map last qbytes fold_right qchain].
      split; [| exact I].
      lazymatch goal with H : rw_cells ctasegs ?mm 6745424 _ |- _ =>
        replace (Z.of_nat 1 + -1)%Z with 0%Z in H by lia;
        replace (8192 + bsum eb + - (8192 + bsum eb))%Z with 0%Z in H by lia; exact H end.
    * apply (proj2 (qcache_rep_iff _ _ _)). cbn [length Z.of_nat qfirst qlast map last qbytes fold_right qchain fst snd].
      split.
      -- lazymatch goal with H : rw_cells ctasegs ?mm TMP _ |- _ =>
           replace (Z.of_nat 0 + 1)%Z with 1%Z in H by lia;
           replace (0 + (8192 + bsum eb))%Z with (8192 + bsum eb + 0)%Z in H by lia; exact H end.
      -- split; [| exact I]. apply (proj2 (qbatch_iff _ _ _ _)). split; [eassumption| split; [| exact Ble]].
         destruct (unbox _ BA) as (bws & BA0 & BL0 & BP0). exists bws. split; [| split; [exact BL0| exact BP0]].
         lazymatch goal with |- u64arr ctasegs ?mm _ _ => apply (u64arr_transport ctasegs _ m mm _ _ BA0 MU WM) end.
         rewrite BL0. cbn [disjoint_from]. lia.
  + (* [comment removed for export] *)
    apply (proj1 (qchain_to_snoc _ _ _ _ _)) in TC. destruct TC as (XP & XB). apply box in XP.
    apply (proj1 (qbatch_iff _ _ _ _)) in XB. destruct XB as (XH & XA & Xle). apply box in XA.
    rewrite (Ha5 (snoc_ne _ _)), qlast_snoc.
    pose proof (qwf_snoc_disj _ _ _ _ WF) as DJ. apply Forall_app in DJ. destruct DJ as (DJ' & DJx).
    inversion DJx as [|y l HXB _]; subst. cbn [fst] in HXB. apply box in DJ'.
    pose proof (qwf_prefix _ _ _ WF) as WF0. pose proof (qwf_last _ _ _ _ WF0) as (Hx8 & Hx1 & Hx2 & _ & _). unfold r24 in Hx1, Hx2.
    pose proof (qwf_snoc_disj _ _ _ _ WF0) as DJX. apply box in DJX.
    rewrite qbytes_snoc in QXN, HBY. pose proof (bsum_nonneg el) as BSNX.
    remember (Z.of_nat (length (XD' ++ [(xl, el)]))) as NX eqn:ENX.
    assert (RNX : (1 <= NX < 2^50)%Z).
    { pose proof (qbytes_ge _ _ WF0) as QGE. rewrite <- ENX, qbytes_snoc in QGE.
      assert (1 <= NX)%Z by (subst NX; rewrite app_length; cbn [length]; lia). clear - QGE HBY BSN H. lia. }
    remember (qfirst (XD' ++ [(xl, el)])) as FX eqn:EFX. remember (qbytes XD') as BXP eqn:EBXP.
    cbn [qbytes fold_right] in TH. rewrite qbytes_snoc, <- EBXP in TH.
    pose proof (munch_refl [(6745424, 6745424 + 32); (TMP, TMP + 32); (b, b + 8); (xl, xl + 8)]%Z m) as MU.
    pose proof (wmono_refl ctasegs m) as WM.
    zstep. ifF.
    zstep. zstep; fix_lit_store. zstep. ifF. zstep; fix_lit_store.
    do 7 zstep. zstep; fix_lit_store.
    zstep. ifT.
    zstep.
    do 4 zstep. do 5 zstep. ifT.
    zstep. zstep.
    apply evt_done. unfold deq_post. do 8 eexists. split; [reflexivity|].
    split.
    { eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in Hx. destruct Hx as (H1 & H2 & H3).
      pose proof (in_batch_outside ((XD' ++ [(xl, el)]) ++ [(b, eb)]) b eb 8 x
                    ltac:(apply in_or_app; right; left; reflexivity) ltac:(lia) H3) as H4.
      pose proof (in_batch_outside ((XD' ++ [(xl, el)]) ++ [(b, eb)]) xl el 8 x
                    ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity) ltac:(lia) H3) as H5.
      cbn [outside]. tauto. }
    split; [eassumption|]. split; [eassumption|]. split.
    * apply (proj2 (qcache_rep_iff _ _ _)). cbn [length Z.of_nat qfirst qlast map last qbytes fold_right qchain].
      split; [| exact I].
      lazymatch goal with H : rw_cells ctasegs ?mm 6745424 _ |- _ =>
        replace (Z.of_nat 1 + -1)%Z with 0%Z in H by lia;
        replace (8192 + bsum eb + - (8192 + bsum eb))%Z with 0%Z in H by lia; exact H end.
    * apply (proj2 (qcache_rep_iff _ _ _)).
      rewrite app_length, Nat2Z.inj_add, <- ENX. rewrite (qfirst_app_ne _ _ (snoc_ne _ _)), <- EFX, qlast_snoc.
      rewrite qbytes_snoc, qbytes_snoc, <- EBXP. cbn [length Z.of_nat]. split.
      -- lazymatch goal with H : rw_cells ctasegs ?mm TMP _ |- _ =>
           replace (BXP + 8192 + bsum el + (8192 + bsum eb))%Z with (BXP + 8192 + bsum el + 8192 + bsum eb)%Z in H by lia;
           exact H end.
      -- apply (proj2 (qchain_to_0 _ _)). apply (proj2 (qchain_to_snoc _ _ _ _ _)). split.
         ++ apply (proj2 (qchain_to_snoc _ _ _ _ _)). split.
            ** lazymatch goal with |- qchain_to ?mm _ _ => apply (qchain_to_frame _ m mm _ _ (unbox _ XP) MU WM) end.
               pose proof (qwf_region _ _ (qwf_prefix _ _ _ WF0)) as RG'.
               apply Forall_forall. intros e He.
               pose proof (proj1 (Forall_forall _ _) RG' e He) as (E1 & E2).
               pose proof (proj1 (Forall_forall _ _) (unbox _ DJ') e He) as E3.
               pose proof (proj1 (Forall_forall _ _) (unbox _ DJX) e He) as E4.
               unfold r24 in E1, E2. cbv beta in E3, E4. cbn [disjoint_from]. repeat split; lia.
            ** apply (proj2 (qbatch_iff _ _ _ _)). split; [eassumption| split; [| exact Xle]].
               destruct (unbox _ XA) as (bws & BA0 & BL0 & BP0). exists bws. split; [| split; [exact BL0| exact BP0]].
               lazymatch goal with |- u64arr ctasegs ?mm _ _ => apply (u64arr_transport ctasegs _ m mm _ _ BA0 MU WM) end.
               rewrite BL0. cbn [disjoint_from]. lia.
         ++ apply (proj2 (qbatch_iff _ _ _ _)). split; [eassumption| split; [| exact Ble]].
            destruct (unbox _ BA) as (bws & BA0 & BL0 & BP0). exists bws. split; [| split; [exact BL0| exact BP0]].
            lazymatch goal with |- u64arr ctasegs ?mm _ _ => apply (u64arr_transport ctasegs _ m mm _ _ BA0 MU WM) end.
            rewrite BL0. cbn [disjoint_from]. lia.
Qed.

End DEQ.
