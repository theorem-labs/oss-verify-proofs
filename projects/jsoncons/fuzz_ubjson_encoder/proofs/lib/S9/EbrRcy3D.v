(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EbtLeaf EbtAllocG EbtPoison ArtRuns ArtRunsMem EbtFp EbtRefill1 EbtCellEx EbtCls.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import EbtRecycle3 EbtRecycle3R EbtRecycle3D EbrRcy3R.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r3ef18_4052c Eb0_code_r731ac_733ac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Ltac inl4 := cbn [In]; repeat (first [left; reflexivity | right]).

Definition art_lcdrain_fp (sp t spb ris qs c nf h mfa : Z) : list (Z * Z) :=
  [ (sp - 640, 640); (t + 208 + 80 * c, 4); (ris + 128 * c, 8); (ris + 128 * c + 16, 16); (ris + 128 * c + 80, 8); (spb + c * 2 ^ 32 + 3758096384 + 4 * nf, 4 * h);
    (spb + c * 2 ^ 32 + 3758096384 + mfa, 536870912 - mfa); (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864); (t + 2872, 16) ].

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_lcdrain_aruns :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) ws regs (M rom : word -> option byte) (raw : word)
         (sp HI t ctx tp key tsd spb ris qs qris c cnt h nf mfa kf nfr m1 m2 : Z),
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 (t + 208) -> getr regs 11 = Z_to_bv 64 (t + 208 + 80 * c) ->
    getr regs 12 = Z_to_bv 64 1321624 -> getr regs 13 = Z_to_bv 64 c ->
    art_geo HI t ctx tp tsd spb ris qs -> HI <= sp - 640 -> sp < 2 ^ 47 -> 1 <= c <= 30 -> ris = 128 * qris ->
    h = Z.of_nat (length ws) -> 1 <= h -> h <= cnt -> cnt <= 16 ->
    0 <= nf -> 4 * nf <= mfa -> mfa = 262144 * kf -> art_mfa_grow mfa (nf + h) <= 2 ^ 29 -> 0 <= nfr < 2 ^ 64 ->
    wrA M (sp - 640) 640 -> wrA M t 4096 -> wrA M (ris + 128 * c) 128 -> wrA M (spb + c * 2 ^ 32 + 3758096384) mfa ->
    wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048) 67108864 ->
    art_prim_consts spb ris M -> art_layout M -> art_tsd M tp key tsd ctx t ->
    cellA M (t + 208 + 80 * c) 4 cnt -> cellA M (t + 208 + 80 * c + 4) 4 (2 * h) ->
    cellA M (ris + 128 * c) 8 0 -> cellA M (ris + 128 * c + 16) 8 nf -> cellA M (ris + 128 * c + 24) 8 mfa -> cellA M (ris + 128 * c + 80) 8 nfr ->
    cellA M (t + 2872) 8 m1 -> cellA M (t + 2880) 8 m2 ->
    (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA M (t + 208 + 80 * c + 16 + 4 * (cnt - h) + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
    art_evok_list EVOK log (art_rta_events spb c nf h mfa) ->
    (forall regs' (M' : word -> option byte),
        getr regs' 2 = Z_to_bv 64 sp ->
        (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
        mem_grows M M' -> art_agree (art_lcdrain_fp sp t spb ris qs c nf h mfa) M M' ->
        cellA M' (t + 208 + 80 * c) 4 (cnt - h) ->
        cellA M' (ris + 128 * c) 8 0 -> cellA M' (ris + 128 * c + 16) 8 (nf + h) -> cellA M' (ris + 128 * c + 24) 8 (art_mfa_grow mfa (nf + h)) ->
        cellA M' (ris + 128 * c + 80) 8 (nfr + h) ->
        (forall j, (j < length ws)%nat -> cellA M' (spb + c * 2 ^ 32 + 3758096384 + 4 * (nf + Z.of_nat j)) 4 (nth j ws 0)) ->
        wrA M' (spb + c * 2 ^ 32 + 3758096384) (art_mfa_grow mfa (nf + h)) ->
        (exists m1' m2', cellA M' (t + 2872) 8 m1' /\ cellA M' (t + 2880) 8 m2') ->
        Q (log ++ art_rta_events spb c nf h mfa) (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x5609c : word) M rom).
Proof.
  intros Q log ws regs M rom raw sp HI t ctx tp key tsd spb ris qs qris c cnt h nf mfa kf nfr m1 m2
         H1 Hret H2 H4 H10 H11 H12 H13 GEO HHI Hsp' Hc Eq Eh Hh Hhc Hcnt Hnf Hnf4 Emfa Room Hnfr W Wt Wr Wfa Wsh PC L T Ccnt Cmc Cmx Cnf Cmfa Cnfr Cm1 Cm2 Cws EV K.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x69c000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  clear G9 G10 G15 G16. unfold apart in G11, At_i, At_s.
  assert (Hmfa0 : 0 <= mfa) by lia.
  destruct (art_mfa_grow_facts mfa (nf + h) kf Emfa Hmfa0 ltac:(lia)) as (Hg1 & Hg2 & _).
  set (mfa' := art_mfa_grow mfa (nf + h)) in *.
  set (ca := t + 208) in *.
  assert (Eca : ca = t + 208) by reflexivity. clearbody ca.
  pose proof (art_lcdrain_a_fn regs M rom raw sp ca 1321624 c cnt h H1 H2 H10 H11 H12 H13 ltac:(lia) ltac:(lia) ltac:(eapply wr_sub; [exact W|lia|lia]) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                Hh Hhc Hcnt ltac:(eapply wr_sub; [exact Wt|lia|lia]) Ccnt Cmc) as RUN1.
  unfold art_lcdrain_a_mem in RUN1.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?X1 _) =>
    assert (F1 : mem_grows M X1 /\ art_agree [(sp - 64, 64); (ca + 80 * c, 4)] M X1) by (split; [zgrows|eapply art_agree_sub; [zagree|]; zsub]);
    assert (C1 : cellA X1 (sp - 8) 8 (U raw) /\ cellA X1 (sp - 32) 8 0 /\ cellA X1 (sp - 24) 8 0 /\ cellA X1 (ca + 80 * c) 4 (cnt - h))
      by (repeat split; zcell);
    set (Ra := R1) in *; set (Xa := X1) in *
  end.
  destruct F1 as (G1x & AG1).
  destruct C1 as (E8 & E32 & E24 & Ccnt1).
  clearbody Xa.
  assert (T1 : forall a (k : nat) v, art_gap [(sp - 64, 64); (ca + 80 * c, 4)] a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA Xa a k v).
  { intros a k v G Ha Hk C. exact (art_cell_tr _ M Xa a k v AG1 G Ha Hk C). }
  assert (GI1 : forall a k, a + k <= HI -> apart a k (ca + 80 * c) 4 -> art_gap [(sp - 64, 64); (ca + 80 * c, 4)] a k).
  { intros a k Hk A. cbn [art_gap fst snd]. unfold apart in A |- *. repeat split; try exact I; lia. }
  assert (PCa : art_prim_consts spb ris Xa).
  { destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    unfold art_prim_consts. repeat split; (apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|assumption]). }
  assert (La : art_layout Xa). { eapply art_layout_fp; [exact AG1| |exact L]. intros z Hz. cbn. repeat split; lia. }
  assert (Ta : art_tsd Xa tp key tsd ctx t).
  { eapply art_tsd_fp; [exact AG1| | |exact G19|exact G20|exact G21|exact G22|exact T].
    - intros z Hz. cbn. repeat split; lia.
    - intros z Hz. pose proof G17 as X1. pose proof G18 as X2. unfold apart in X1, X2. cbn. repeat split; lia. }
  assert (Cws1 : forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA Xa (ca + 80 * c + 16 + 4 * (cnt - h) + 4 * Z.of_nat j) 4 (nth j ws 0)).
  { intros j Hj. destruct (Cws j Hj) as [Rj Cj]. split; [exact Rj|]. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'.
    apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|exact Cj]. }
  apply (ar_steps ASEGS EVOK GR Q log _ _ RUN1).
  apply (aruns_bind ASEGS EVOK GR (fun lg s1 => aruns ASEGS EVOK GR Q lg s1) Q); [|intros lg s1 X; exact X].
  apply (art_rta_aruns EVOK GR (fun lg s1 => aruns ASEGS EVOK GR Q lg s1) log ws Ra Xa rom (0x56100 : bv 64)%bv (sp - 64) HI t ctx tp key tsd spb ris qs qris (sp - 56) (ca + 2560) c
           (ca + 80 * c + 16 + 4 * (cnt - h)) h nf mfa kf nfr m1 m2);
    [unfold Ra; gres; bveq|unfold ret_ok; bveq|unfold Ra; gres; reflexivity|unfold Ra; gres; exact H4|unfold Ra; gres; reflexivity|unfold Ra; gres; reflexivity
    |unfold Ra; gres; reflexivity|unfold Ra; gres; exact H13|unfold Ra; gres; reflexivity|unfold Ra; gres; reflexivity
    |exact GEO|lia|lia|exact Hc|exact Eq|exact Eh|lia|lia|lia|exact Hnf|exact Hnf4|exact Emfa|exact Room|exact Hnfr|lia|lia
    |eapply wr_grows; [exact G1x|]; eapply wr_sub; [exact W|lia|lia]|eapply wr_grows; [exact G1x|exact Wr]|eapply wr_grows; [exact G1x|exact Wfa]|eapply wr_grows; [exact G1x|exact Wt]
    |eapply wr_grows; [exact G1x|exact Wsh]|exact PCa|exact La|exact Ta
    |apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|exact Cmx]
    |apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|exact Cnf]|apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|exact Cmfa]
    |apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|exact Cnfr]
    |apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|exact Cm1]|apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|exact Cm2]
    |exact Cws1|exact EV|].
  intros r2 M2 B2 BK G2x AG2 Cmx2 Cnf2 Cmfa2 Cnfr2 Cfa2 Wfa2 (m1' & m2' & Cm1' & Cm2').
  set (W2 := art_rta_fp (sp - 64) t spb ris qs c nf h mfa) in *.
  assert (GF : forall a k, sp - 64 <= a -> a + k <= sp -> art_gap W2 a k).
  { intros a k Ha Hk. unfold W2, art_rta_fp. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (GC : art_gap W2 (ca + 80 * c) 4).
  { unfold W2, art_rta_fp. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (F8 : cellA M2 (sp - 8) 8 (U raw)) by (apply (art_cell_tr W2 Xa M2 _ _ _ AG2); [apply GF; cbn; lia|lia|cbn; lia|exact E8]).
  assert (F32 : cellA M2 (sp - 32) 8 0) by (apply (art_cell_tr W2 Xa M2 _ _ _ AG2); [apply GF; cbn; lia|lia|cbn; lia|exact E32]).
  assert (F24 : cellA M2 (sp - 24) 8 0) by (apply (art_cell_tr W2 Xa M2 _ _ _ AG2); [apply GF; cbn; lia|lia|cbn; lia|exact E24]).
  assert (Ccnt2 : cellA M2 (ca + 80 * c) 4 (cnt - h)) by (apply (art_cell_tr W2 Xa M2 _ _ _ AG2); [exact GC|lia|cbn; lia|exact Ccnt1]).
  assert (W2a : wrA M2 (sp - 64 - 48) 48) by (eapply wr_grows; [exact G2x|]; eapply wr_grows; [exact G1x|]; eapply wr_sub; [exact W|lia|lia]).
  eassert (RUN3 : msteps ASEGS (mkst r2 (0x56100 : bv 64)%bv M2 rom) _).
  { zld F_560b0 D_560b0 (sp - 32) F32.
    zld F_560b4 D_560b4 (sp - 24) F24.
    zstep F_560b8 D_560b8.
    stepn F_560bc D_560bc.
    zcall (art_unmap_null_fn _ _ _ (0x56110 : word) (sp - 64)).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (F8' : cellA X (sp - 8) 8 (U raw)) by (unfold art_f32; zcell) end.
    zld F_560c0 D_560c0 (sp - 8) F8'. rewrite Z_to_bv_bv_unsigned.
    zstep F_560c4 D_560c4.
    stepret F_560c8 D_560c8 raw ltac:(reflexivity).
    apply mst_refl. }
  match type of RUN3 with msteps _ _ (mkst ?R3 _ ?X3 _) =>
    assert (F3 : mem_grows M2 X3 /\ art_agree [(sp - 96, 32)] M2 X3) by (unfold art_f32; split; [zgrows|eapply art_agree_sub; [zagree|]; zsub]);
    set (M3 := X3) in *
  end.
  destruct F3 as (G3 & AG3). clearbody M3.
  assert (T3 : forall a (k : nat) v, apart a (Z.of_nat k) (sp - 96) 32 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M2 a k v -> cellA M3 a k v).
  { intros a k v A Ha Hk C. apply (art_cell_tr _ M2 M3 a k v AG3); [cbn [art_gap fst snd]; split; [exact A|exact I]|exact Ha|exact Hk|exact C]. }
  eapply ar_steps; [exact RUN3|]. apply ar_done.
  apply K.
  - gres; f_equal; lia.
  - intros x Hx. cbn [In] in Hx.
    repeat (destruct Hx as [<-|Hx]; [gres; rewrite ?BK by inl4; unfold Ra; gres; reflexivity|]). destruct Hx.
  - eapply mem_grows_trans; [exact G1x|]. eapply mem_grows_trans; [exact G2x|]. exact G3.
  - eapply art_agree_sub; [eapply art_agree_trans; [exact AG1|]; eapply art_agree_trans; [exact AG2|]; exact AG3|].
    unfold W2, art_rta_fp, art_lcdrain_fp. rewrite <- Eca. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; lia.
  - apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact Ccnt2].
  - apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact Cmx2].
  - apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact Cnf2].
  - apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact Cmfa2].
  - apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact Cnfr2].
  - intros j Hj. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact (Cfa2 j Hj)].
  - eapply wr_grows; [exact G3|exact Wfa2].
  - exists m1', m2'. split; (apply T3; [unfold apart; cbn; lia|lia|cbn; lia|assumption]).
Qed.

End Spec.
