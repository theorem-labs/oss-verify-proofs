(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_quar_defs R_qrec_defs R_qput R_qdrain R_qrec_deq.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section DEQ2.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 CACHE STACK : word) (F : bvmap 5 word) (fc : bv 32).
Variables (MIN SB TMP : Z).
Hypothesis HMIN : (0 <= MIN < 2^63)%Z.
Hypothesis HSB : (0 < SB)%Z.
Hypothesis HTMP : (r24 SB + 2^32 <= TMP /\ TMP + 32 <= 2^47)%Z.

Definition iter_post (XD : list batch) (B : batch) (rest : list batch) (W : list (Z * Z)) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (w0' w2' : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 TMP) gp tp (Z_to_bv 64 (qfirst rest)) (Z_to_bv 64 (fst B)) (Z_to_bv 64 (qbytes rest)) s0 s1
                  (Z_to_bv 64 QUAR) (Z_to_bv 64 MIN) CACHE STACK (Z_to_bv 64 (Z.of_nat (length XD) + 1)) (Z_to_bv 64 (fst B))
                  (Z_to_bv 64 (Z.of_nat (length rest))) (Z_to_bv 64 (qfirst rest)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x5b588) fc None m' (seg_rom bsegs)
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' QG [C8 (Z_to_bv 64 (Z.of_nat (length rest))); C8 (Z_to_bv 64 (qfirst rest)); C8 (Z_to_bv 64 (qlast rest));
                            C8 (Z_to_bv 64 (qbytes rest))]
    /\ qchain_to m' rest 0
    /\ rw_cells bsegs m' TMP [C8 w0'; C8 (Z_to_bv 64 (qfirst (XD ++ [B]))); C8 w2'; C8 (Z_to_bv 64 (qbytes (XD ++ [B])))]
    /\ qchain_to m' (XD ++ [B]) 0.

Lemma deq_iter : forall (rest : list batch) (B : batch) (XD : list batch) (m : mem) (t1 t2 a5 a7 w0 w2 : word),
  rest <> [] ->
  (MIN < qbytes (B :: rest))%Z -> qwf SB (XD ++ B :: rest) -> (qbytes (XD ++ B :: rest) < 2^56)%Z ->
  rw_cells bsegs m QG [C8 (Z_to_bv 64 (Z.of_nat (length (B :: rest)))); C8 (Z_to_bv 64 (fst B)); C8 (Z_to_bv 64 (qlast (B :: rest)));
                       C8 (Z_to_bv 64 (qbytes (B :: rest)))] ->
  qchain_to m (B :: rest) 0 ->
  rw_cells bsegs m TMP [C8 w0; C8 (Z_to_bv 64 (qfirst XD)); C8 w2; C8 (Z_to_bv 64 (qbytes XD))] ->
  qchain_to m XD 0 -> (XD <> [] -> a5 = Z_to_bv 64 (qlast XD)) ->
  mem_inv bsegs m ->
  evt bsegs (iter_post XD B rest ([(QG, QG + 32); (TMP, TMP + 32)] ++ bivs (XD ++ B :: rest))%Z m)
    (MS (mkR ra (Z_to_bv 64 TMP) gp tp (Z_to_bv 64 (fst B)) t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 MIN) CACHE STACK
             (Z_to_bv 64 (Z.of_nat (length XD))) a5 (Z_to_bv 64 (Z.of_nat (length (B :: rest)))) a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5b58c) fc None m (seg_rom bsegs)).
Proof.
  intros rest [b eb] XD m t1 t2 a5 a7 w0 w2 Hne HB WF HBY QGH QC TH TC Ha5 MI.
  destruct rest as [|[b' eb'] rest']; [congruence|]. clear Hne. cbn [fst snd] in *.
  assert (QCc : qbatch m b b' eb /\ qchain_to m ((b', eb') :: rest') 0) by exact QC. clear QC.
  destruct QCc as (QB & QR). apply box in QR.
  apply (proj1 (qbatch_iff _ _ _ _)) in QB. destruct QB as (BH & BA & Ble). apply box in BA.
  pose proof (qwf_region _ _ WF) as RG. apply box in RG.
  pose proof (proj1 (Forall_forall _ _) (proj2 WF) (b, eb) ltac:(apply in_or_app; right; left; reflexivity))
    as (Hb8 & Hb1 & Hb2 & _ & Hebs).
  cbn [fst snd] in Hb8, Hb1, Hb2, Hebs. unfold r24 in *.
  pose proof (bsum_nonneg _ Hebs) as BSN.
  pose proof (qbytes_ge _ _ (qwf_suffix _ _ _ WF)) as QGE. pose proof (qbytes_nonneg _ _ (qwf_prefix _ _ _ WF)) as QXN.
  rewrite qbytes_app in HBY.
  remember ((b', eb') :: rest') as rest eqn:Erest.
  assert (RST : (8192 <= qbytes rest)%Z).
  { pose proof (qbytes_ge _ _ (qwf_suffix SB [(b, eb)] rest (qwf_suffix SB XD _ WF))) as Q2. subst rest. cbn [length] in Q2. lia. }
  cbn [length] in QGH |- *. rewrite Nat2Z.inj_succ in QGH |- *.
  assert (EQL : qlast ((b, eb) :: rest) = qlast rest) by (subst rest; reflexivity). rewrite EQL in QGH.
  assert (EQB : qbytes ((b, eb) :: rest) = (8192 + bsum eb + qbytes rest)%Z) by reflexivity. rewrite EQB in QGH, HB, HBY.
  assert (EQF : b' = qfirst rest) by (subst rest; reflexivity). rewrite EQF in BH.
  assert (RNR : (0 <= Z.of_nat (length rest) < 2^50)%Z).
  { cbn [length] in QGE. rewrite Nat2Z.inj_succ in QGE. rewrite EQB in QGE. clear - QGE HBY BSN QXN RST. lia. }
  remember (Z.of_nat (length rest)) as NR eqn:ENR. remember (qfirst rest) as FR eqn:EFR.
  remember (qlast rest) as LR eqn:ELR. remember (qbytes rest) as BR eqn:EBR.
  assert (RFR : (0 < FR < 2^47)%Z).
  { subst FR rest. pose proof (proj1 (Forall_forall _ _) (unbox _ RG) (b', eb') ltac:(apply in_or_app; right; right; left; reflexivity))
      as (E1 & E2). cbn [qfirst fst] in *. unfold r24 in E1, E2. lia. }
  destruct (snoc_cases XD) as [->|(XD' & [xl el] & ->)].
  +
    cbn [length Z.of_nat qfirst qbytes fold_right] in TH |- *.
    pose proof (munch_refl [(1525968, 1525968 + 32); (TMP, TMP + 32); (b, b + 8)]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    zhide.
    zstep. ifF.
    zstep. zstep. zstep. ifT.
    do 7 zstep. zstep; fix_lit_store.
    zstep. ifF.
    zstep. zstep. zstep.
    do 4 zstep. do 4 zstep.
    replace (Z.succ NR + -1)%Z with NR in * by lia. replace (8192 + bsum eb + BR + - (8192 + bsum eb))%Z with BR in * by lia.
    apply evt_done. unfold iter_post. rewrite <- EFR, <- EBR, <- ENR, <- ELR. cbn [fst].
    do 3 eexists. split; [reflexivity|].
    split.
    { eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in Hx. destruct Hx as (H1 & H2 & H3).
      pose proof (in_batch_outside ([] ++ (b, eb) :: rest) b eb 8 x (or_introl eq_refl) ltac:(lia) H3) as H4.
      cbn [outside]. tauto. }
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split.
    { lazymatch goal with |- qchain_to ?mm _ _ => apply (qchain_to_frame _ m mm _ _ (unbox _ QR) MU WM) end.
      apply Forall_forall. intros e He.
      pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e ltac:(apply in_or_app; right; right; exact He)) as (E1 & E2).
      pose proof (qwf_app_disj SB [(b, eb)] rest (b, eb) e (qwf_suffix SB [] _ WF) (or_introl eq_refl) He) as E3.
      unfold r24 in E1, E2. cbn [fst] in E3. cbn [disjoint_from]. repeat split; lia. }
    split.
    { cbn [app qfirst qbytes fold_right snd]. replace (8192 + bsum eb + 0)%Z with (0 + (8192 + bsum eb))%Z by lia. eassumption. }
    cbn [app qchain_to]. split; [| exact I].
    apply (proj2 (qbatch_iff _ _ _ _)). split; [eassumption| split; [| exact Ble]].
    destruct (unbox _ BA) as (bws & BA0 & BL0 & BP0). exists bws. split; [| split; [exact BL0| exact BP0]].
    lazymatch goal with |- u64arr bsegs ?mm _ _ => apply (u64arr_transport bsegs _ m mm _ _ BA0 MU WM) end.
    rewrite BL0. cbn [disjoint_from]. lia.
  +
    apply (proj1 (qchain_to_snoc _ _ _ _ _)) in TC. destruct TC as (XP & XB). apply box in XP.
    apply (proj1 (qbatch_iff _ _ _ _)) in XB. destruct XB as (XH & XA & Xle). apply box in XA.
    rewrite (Ha5 (snoc_ne _ _)), qlast_snoc.
    assert (WFs : qwf SB ((XD' ++ [(xl, el)]) ++ [(b, eb)])).
    { apply (qwf_prefix SB _ rest). rewrite <- app_assoc. exact WF. }
    pose proof (qwf_snoc_disj _ _ _ _ WFs) as DJ. apply Forall_app in DJ. destruct DJ as (DJ' & DJx).
    inversion DJx as [|y l HXB _]; subst y l. cbn [fst] in HXB. apply box in DJ'.
    pose proof (qwf_prefix _ _ _ WFs) as WF0. pose proof (qwf_last _ _ _ _ WF0) as (Hx8 & Hx1 & Hx2 & _ & _). unfold r24 in Hx1, Hx2.
    pose proof (qwf_snoc_disj _ _ _ _ WF0) as DJX. apply box in DJX.
    rewrite qbytes_snoc in QXN, HBY.
    remember (Z.of_nat (length (XD' ++ [(xl, el)]))) as NX eqn:ENX.
    assert (RNX : (1 <= NX < 2^50)%Z).
    { pose proof (qbytes_ge _ _ WF0) as QGE0. rewrite <- ENX, qbytes_snoc in QGE0.
      assert (1 <= NX)%Z by (subst NX; rewrite app_length; cbn [length]; lia). clear - QGE0 HBY BSN H RST. lia. }
    remember (qfirst (XD' ++ [(xl, el)])) as FX eqn:EFX. remember (qbytes XD') as BXP eqn:EBXP.
    cbn [qbytes fold_right] in TH. rewrite qbytes_snoc, <- EBXP in TH.
    pose proof (munch_refl [(1525968, 1525968 + 32); (TMP, TMP + 32); (b, b + 8); (xl, xl + 8)]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    zstep. ifF.
    zstep. zstep. zstep. ifT.
    do 7 zstep. zstep; fix_lit_store.
    zstep. ifT.
    zstep.
    do 4 zstep. do 4 zstep.
    replace (Z.succ NR + -1)%Z with NR in * by lia. replace (8192 + bsum eb + BR + - (8192 + bsum eb))%Z with BR in * by lia.
    apply evt_done. unfold iter_post. rewrite <- EFR, <- EBR, <- ENR, <- ELR. cbn [fst]. rewrite <- ENX.
    do 3 eexists. split; [reflexivity|].
    split.
    { eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in Hx. destruct Hx as (H1 & H2 & H3).
      pose proof (in_batch_outside ((XD' ++ [(xl, el)]) ++ (b, eb) :: rest) b eb 8 x
                    ltac:(apply in_or_app; right; left; reflexivity) ltac:(lia) H3) as H4.
      pose proof (in_batch_outside ((XD' ++ [(xl, el)]) ++ (b, eb) :: rest) xl el 8 x
                    ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity) ltac:(lia) H3) as H5.
      cbn [outside]. tauto. }
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split.
    { lazymatch goal with |- qchain_to ?mm _ _ => apply (qchain_to_frame _ m mm _ _ (unbox _ QR) MU WM) end.
      apply Forall_forall. intros e He.
      pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e ltac:(apply in_or_app; right; right; exact He)) as (E1 & E2).
      pose proof (qwf_app_disj SB ((XD' ++ [(xl, el)]) ++ [(b, eb)]) rest (b, eb) e
                    ltac:(rewrite <- app_assoc; exact WF) ltac:(apply in_or_app; right; left; reflexivity) He) as E3.
      pose proof (qwf_app_disj SB ((XD' ++ [(xl, el)]) ++ [(b, eb)]) rest (xl, el) e
                    ltac:(rewrite <- app_assoc; exact WF) ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity) He)
        as E4.
      unfold r24 in E1, E2. cbn [fst] in E3, E4. cbn [disjoint_from]. repeat split; lia. }
    split.
    { rewrite (qfirst_app_ne _ _ (snoc_ne _ _)), <- EFX, !qbytes_snoc, <- EBXP.
      lazymatch goal with H : rw_cells bsegs ?mm TMP _ |- _ =>
        replace (BXP + 8192 + bsum el + (8192 + bsum eb))%Z with (BXP + 8192 + bsum el + 8192 + bsum eb)%Z in H by lia;
        exact H end. }
    apply (proj2 (qchain_to_snoc _ _ _ _ _)). split.
    * apply (proj2 (qchain_to_snoc _ _ _ _ _)). split.
      -- lazymatch goal with |- qchain_to ?mm _ _ => apply (qchain_to_frame _ m mm _ _ (unbox _ XP) MU WM) end.
         pose proof (qwf_region _ _ (qwf_prefix _ _ _ WF0)) as RG'.
         apply Forall_forall. intros e He.
         pose proof (proj1 (Forall_forall _ _) RG' e He) as (E1 & E2).
         pose proof (proj1 (Forall_forall _ _) (unbox _ DJ') e He) as E3.
         pose proof (proj1 (Forall_forall _ _) (unbox _ DJX) e He) as E4.
         unfold r24 in E1, E2. cbv beta in E3, E4. cbn [disjoint_from]. repeat split; lia.
      -- apply (proj2 (qbatch_iff _ _ _ _)). split; [eassumption| split; [| exact Xle]].
         destruct (unbox _ XA) as (bws & BA0 & BL0 & BP0). exists bws. split; [| split; [exact BL0| exact BP0]].
         lazymatch goal with |- u64arr bsegs ?mm _ _ => apply (u64arr_transport bsegs _ m mm _ _ BA0 MU WM) end.
         rewrite BL0. cbn [disjoint_from]. lia.
    * apply (proj2 (qbatch_iff _ _ _ _)). split; [eassumption| split; [| exact Ble]].
      destruct (unbox _ BA) as (bws & BA0 & BL0 & BP0). exists bws. split; [| split; [exact BL0| exact BP0]].
      lazymatch goal with |- u64arr bsegs ?mm _ _ => apply (u64arr_transport bsegs _ m mm _ _ BA0 MU WM) end.
      rewrite BL0. cbn [disjoint_from]. lia.
Qed.

Lemma deq_loop : forall (rest : list batch) (B : batch) (XD : list batch) (m : mem) (t1 t2 a5 a7 w0 w2 : word),
  (MIN < qbytes (B :: rest))%Z -> qwf SB (XD ++ B :: rest) -> (qbytes (XD ++ B :: rest) < 2^56)%Z ->
  rw_cells bsegs m QG [C8 (Z_to_bv 64 (Z.of_nat (length (B :: rest)))); C8 (Z_to_bv 64 (fst B)); C8 (Z_to_bv 64 (qlast (B :: rest)));
                       C8 (Z_to_bv 64 (qbytes (B :: rest)))] ->
  qchain_to m (B :: rest) 0 ->
  rw_cells bsegs m TMP [C8 w0; C8 (Z_to_bv 64 (qfirst XD)); C8 w2; C8 (Z_to_bv 64 (qbytes XD))] ->
  qchain_to m XD 0 -> (XD <> [] -> a5 = Z_to_bv 64 (qlast XD)) ->
  mem_inv bsegs m ->
  evt bsegs (deq_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 CACHE STACK F fc MIN TMP
               ([(QG, QG + 32); (TMP, TMP + 32)] ++ bivs (XD ++ B :: rest))%Z
               XD (fst (deq (B :: rest) (qbytes (B :: rest)) MIN)) (snd (deq (B :: rest) (qbytes (B :: rest)) MIN)) m)
    (MS (mkR ra (Z_to_bv 64 TMP) gp tp (Z_to_bv 64 (fst B)) t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 MIN) CACHE STACK
             (Z_to_bv 64 (Z.of_nat (length XD))) a5 (Z_to_bv 64 (Z.of_nat (length (B :: rest)))) a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5b58c) fc None m (seg_rom bsegs)).
Proof.
  induction rest as [|B' rest IH]; intros B XD m t1 t2 a5 a7 w0 w2 HB WF HBY QGH QC TH TC Ha5 MI.
  - eapply deq_last; eassumption.
  - eapply evt_cut; [eapply (deq_iter (B' :: rest) B XD m); try eassumption; discriminate|].
    intros ms1 (w0' & w2' & m1 & E1 & MU1 & WM1 & MI1 & QGH1 & QC1 & TH1 & TC1). subst ms1.
    assert (ED : deq (B :: B' :: rest) (qbytes (B :: B' :: rest)) MIN
                 = (B :: fst (deq (B' :: rest) (qbytes (B' :: rest)) MIN), snd (deq (B' :: rest) (qbytes (B' :: rest)) MIN))).
    { cbn [deq]. destruct (Z.leb_spec (qbytes (B :: B' :: rest)) MIN); [lia|].
      replace (qbytes (B :: B' :: rest) - (8192 + bsum (snd B)))%Z with (qbytes (B' :: rest)) by (unfold qbytes; cbn; lia).
      reflexivity. }
    rewrite ED. cbn [fst snd].
    pose proof (qbytes_ge _ _ (qwf_suffix SB (XD ++ [B]) (B' :: rest) ltac:(rewrite <- app_assoc; exact WF))) as QGE.
    assert (RQB : (0 <= qbytes (B' :: rest) < 2^56)%Z).
    { rewrite qbytes_app in HBY. pose proof (qbytes_nonneg _ _ (qwf_prefix _ _ _ WF)) as Q1.
      pose proof (proj1 (Forall_forall _ _) (proj2 WF) B ltac:(apply in_or_app; right; left; reflexivity)) as (_ & _ & _ & _ & HeB).
      pose proof (bsum_nonneg _ HeB) as Q2.
      replace (qbytes (B :: B' :: rest)) with (8192 + bsum (snd B) + qbytes (B' :: rest))%Z in HBY by (unfold qbytes; cbn; lia).
      clear - QGE HBY Q1 Q2. lia. }
    pose proof (munch_refl [(TMP, TMP + 32)]%Z m1) as MU0. pose proof (wmono_refl bsegs m1) as WM0.
    apply box in QC1. apply box in TC1. apply box in MU1.
    assert (HQT : (1525968 + 32 <= TMP)%Z) by (unfold r24 in HTMP; lia).
    zhide.
    zstep.
    destruct (Z.leb_spec (qbytes (B' :: rest)) MIN) as [HX|HX].
    +
      ifT.
      zstep. zstep.
      assert (ED2 : deq (B' :: rest) (qbytes (B' :: rest)) MIN = ([], B' :: rest)).
      { cbn [deq]. destruct (Z.leb_spec (qbytes (B' :: rest)) MIN); [reflexivity| lia]. }
      rewrite ED2. cbn [fst snd].
      destruct B as [b eb].
      apply evt_done. unfold deq_post. do 8 eexists. split; [reflexivity|].
      split; [eapply munch_trans; [exact (unbox _ MU1)| eapply munch_weaken; [| exact MU0]]; intros x Hx;
              apply outside_app in Hx; destruct Hx as (Hx & _); cbn [outside] in *; tauto|].
      split; [eassumption|]. split; [eassumption|]. split.
      * apply (proj2 (qcache_rep_iff _ _ _)). split.
        -- lazymatch goal with H : rw_cells bsegs ?mm 1525968 _ |- _ => exact H end.
        -- apply (proj2 (qchain_to_0 _ _)).
           lazymatch goal with |- qchain_to ?mm _ _ => apply (qchain_to_frame _ m1 mm _ _ (unbox _ QC1) MU0 WM0) end.
           pose proof (qwf_region _ _ (qwf_suffix SB (XD ++ [(b, eb)]) (B' :: rest) ltac:(rewrite <- app_assoc; exact WF))) as RG.
           apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) RG e He) as (E1 & E2).
           unfold r24 in *. cbn [disjoint_from]. repeat split; lia.
      * apply (proj2 (qcache_rep_iff _ _ _)). rewrite app_length, Nat2Z.inj_add, qlast_snoc. cbn [length Z.of_nat]. split.
        -- lazymatch goal with H : rw_cells bsegs ?mm TMP _ |- _ => exact H end.
        -- apply (proj2 (qchain_to_0 _ _)).
           lazymatch goal with |- qchain_to ?mm _ _ => apply (qchain_to_frame _ m1 mm _ _ (unbox _ TC1) MU0 WM0) end.
           pose proof (qwf_region _ _ (qwf_prefix SB (XD ++ [(b, eb)]) (B' :: rest) ltac:(rewrite <- app_assoc; exact WF))) as RG.
           apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) RG e He) as (E1 & E2).
           unfold r24 in *. cbn [disjoint_from]. repeat split; lia.
    +
      ifF.
      apply (unbox _) in QC1. apply (unbox _) in TC1. apply (unbox _) in MU1. clear MU0 WM0.
      replace (Z.of_nat (length XD) + 1)%Z with (Z.of_nat (length (XD ++ [B]))) by (rewrite app_length; cbn [length]; lia).
      replace (qfirst (B' :: rest)) with (fst B') by (destruct B'; reflexivity).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_mono; [eapply (IH B' (XD ++ [B]) mm); try eassumption|] end.
      * rewrite <- app_assoc. exact WF.
      * rewrite <- app_assoc. exact HBY.
      * intros _. destruct B as [b eb]. rewrite qlast_snoc. reflexivity.
      * intros ms' P. unfold deq_post in *.
        destruct P as (t0' & t1' & t2' & a4' & a5' & a6' & a7' & m' & E & MU' & WM' & MI' & QG' & TQ').
        exists t0', t1', t2', a4', a5', a6', a7', m'. split; [exact E|].
        rewrite <- app_assoc in MU', TQ'. cbn [app] in MU', TQ'.
        split; [eapply munch_trans; [exact MU1| exact MU']|].
        split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact QG'| exact TQ'].
Qed.

End DEQ2.
