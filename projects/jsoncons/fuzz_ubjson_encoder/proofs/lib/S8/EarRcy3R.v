(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EatLeaf EatAllocG EatPoison ArtRuns ArtRunsMem EatFp EatMmapFixed EatRefill1 EatPopulate1 EatPopulate2 EatCellEx EatCls EatClsPop2 EatClsPop3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import EatRecycle3 EatRecycle3R EarRcy2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r3ef18_4052c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_mfa_grow (mfa tot : Z) : Z := if 4 * tot <=? mfa then mfa else (4 * tot + 262143) / 262144 * 262144.
Lemma art_cls_mfa'_grow : forall cl tot, art_cls_mfa' cl tot = art_mfa_grow (cl_mfa cl) tot.
Proof. reflexivity. Qed.
Definition art_rta_events (spb c nf n mfa : Z) : list aev :=
  if 4 * (nf + n) <=? mfa then [] else [AMmapFixed (spb + c * 2 ^ 32 + 3758096384 + mfa) (art_mfa_grow mfa (nf + n) - mfa)].

Definition art_rta_fp (sp t spb ris qs c nf n mfa : Z) : list (Z * Z) :=
  [ (sp - 576, 576); (ris + 128 * c, 8); (ris + 128 * c + 16, 16); (ris + 128 * c + 80, 8); (spb + c * 2 ^ 32 + 3758096384 + 4 * nf, 4 * n);
    (spb + c * 2 ^ 32 + 3758096384 + mfa, 536870912 - mfa); (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864); (t + 2872, 16) ].

Lemma art_mfa_grow_warm : forall mfa tot, 4 * tot <= mfa -> art_mfa_grow mfa tot = mfa.
Proof. intros mfa tot H. unfold art_mfa_grow. destruct (4 * tot <=? mfa) eqn:E; [reflexivity|]. apply Z.leb_gt in E. lia. Qed.
Lemma art_mfa_grow_cold : forall mfa tot, mfa < 4 * tot -> 0 <= mfa ->
  exists q rr, 4 * tot + 262143 = 262144 * q + rr /\ 0 <= rr < 262144 /\ art_mfa_grow mfa tot = 262144 * q /\ 4 * tot <= 262144 * q.
Proof.
  intros mfa tot H H0. unfold art_mfa_grow. destruct (4 * tot <=? mfa) eqn:E; [apply Z.leb_le in E; lia|].
  exists ((4 * tot + 262143) / 262144), ((4 * tot + 262143) mod 262144).
  pose proof (Z.div_mod (4 * tot + 262143) 262144 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (4 * tot + 262143) 262144 ltac:(lia)) as R.
  set (q := (4 * tot + 262143) / 262144) in *. set (rr := (4 * tot + 262143) mod 262144) in *. clearbody q rr.
  repeat split; lia.
Qed.
Lemma art_mfa_grow_facts : forall mfa tot k, mfa = 262144 * k -> 0 <= mfa -> 0 <= tot ->
  mfa <= art_mfa_grow mfa tot /\ 4 * tot <= art_mfa_grow mfa tot /\ (exists k', art_mfa_grow mfa tot = 262144 * k').
Proof.
  intros mfa tot k E H0 Ht. destruct (Z_le_gt_dec (4 * tot) mfa) as [Hw|Hc].
  - rewrite art_mfa_grow_warm by exact Hw. repeat split; [lia|lia|exists k; exact E].
  - destruct (art_mfa_grow_cold mfa tot ltac:(lia) H0) as (q & rr & Eq & Hrr & Eg & Hq). rewrite Eg. repeat split; [lia|lia|exists q; reflexivity].
Qed.

Ltac inl3 := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac gkeep3 K rnew i V := let E := fresh "E" in assert (E : getr rnew i = V) by (rewrite K by reg_neq_tac; gres; rwH; reflexivity).

Lemma art_mfa_grow_le : forall mfa tot k, mfa = 262144 * k -> 0 <= mfa <= 2 ^ 29 -> 0 <= tot -> 4 * tot <= 2 ^ 29 -> art_mfa_grow mfa tot <= 2 ^ 29.
Proof.
  intros mfa tot k E H0 Ht H. destruct (Z_le_gt_dec (4 * tot) mfa) as [Hw|Hc].
  - rewrite art_mfa_grow_warm by exact Hw. lia.
  - destruct (art_mfa_grow_cold mfa tot ltac:(lia) ltac:(lia)) as (q & rr & Eq & Hrr & Eg & Hq). rewrite Eg.
    assert (q <= 2048) by lia. lia.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_rta_mida_fn : forall regs (M rom : word -> option byte) (sp r n nf ia : Z),
  getr regs 2 = Z_to_bv 64 (sp - 128) -> getr regs 8 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 ia -> getr regs 21 = Z_to_bv 64 n ->
  0 <= r -> r + 128 < 2 ^ 64 -> cellA M (r + 16) 8 nf ->
  exists regs',
    msteps ASEGS (mkst regs (0x55b64 : word) M rom) (mkst regs' (0x55d40 : word) M rom)
    /\ getr regs' 1 = (0x55b7c : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 ia /\ getr regs' 11 = Z_to_bv 64 r /\ getr regs' 13 = Z_to_bv 64 (nf + n)
    /\ getr regs' 9 = Z_to_bv 64 nf /\ getr regs' 23 = Z_to_bv 64 (nf + n)
    /\ (forall x : reg, In x [2; 3; 4; 8; 12; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x).
Proof.
  intros regs M rom sp r n nf ia H2 H8 H20 H21 Hr Hr' Cnf.
  eexists. split.
  { zld F_55b14 D_55b14 (r + 16) Cnf.
    zstep F_55b18 D_55b18. zstep F_55b1c D_55b1c. zstep F_55b20 D_55b20. zstep F_55b24 D_55b24.
    stepn F_55b28 D_55b28.
    apply mst_refl. }
  split; [gres; bveq|]. split; [gres; rwH; reflexivity|]. split; [gres; rwH; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
Qed.

#[using="Type"] Lemma art_rta_midb_run : forall ws regs (M rom : word -> option byte) (sp HI ia mp c chp n r rb nf nfr : Z),
  getr regs 2 = Z_to_bv 64 (sp - 128) -> getr regs 8 = Z_to_bv 64 r -> getr regs 9 = Z_to_bv 64 nf -> getr regs 10 = Z_to_bv 64 1 ->
  getr regs 18 = Z_to_bv 64 c -> getr regs 19 = Z_to_bv 64 mp ->
  getr regs 20 = Z_to_bv 64 ia -> getr regs 21 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 chp -> getr regs 23 = Z_to_bv 64 (nf + n) -> getr regs 25 = Z_to_bv 64 (rb + 3758096384) ->
  0x698000 <= HI -> HI <= sp - 176 -> sp < 2 ^ 64 -> 0x698000 <= r -> r + 128 <= HI -> 0x698000 <= rb -> rb + 2 ^ 32 <= HI -> HI < 2 ^ 47 ->
  n = Z.of_nat (length ws) -> 1 <= n <= 16 -> 4096 <= chp -> chp + 4 * n <= HI -> 0 <= nf -> 4 * (nf + n) <= 2 ^ 29 -> 0 <= nfr < 2 ^ 64 ->
  0 <= ia < 2 ^ 64 -> 0 <= mp < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  apart (rb + 3758096384 + 4 * nf) (4 * n) chp (4 * n) -> apart chp (4 * n) r 128 -> apart r 128 (rb + 3758096384) (2 ^ 29) ->
  wrA M r 128 -> wrA M (rb + 3758096384 + 4 * nf) (4 * n) ->
  cellA M (r + 80) 8 nfr ->
  (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA M (chp + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x55b7c : word) M rom) (mkst regs' (0x55ec0 : word) M' rom)
    /\ getr regs' 1 = (0x55bcc : bv 64)%bv /\ getr regs' 2 = Z_to_bv 64 (sp - 128) /\ getr regs' 10 = Z_to_bv 64 ia /\ getr regs' 11 = Z_to_bv 64 mp
    /\ getr regs' 12 = Z_to_bv 64 c /\ getr regs' 13 = Z_to_bv 64 0
    /\ (forall x : reg, In x [3; 4; 8; 24]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M' /\ art_agree [(rb + 3758096384 + 4 * nf, 4 * n); (r + 16, 8); (r + 80, 8)] M M'
    /\ cellA M' (r + 16) 8 (nf + n) /\ cellA M' (r + 80) 8 (nfr + n)
    /\ (forall j, (j < length ws)%nat -> cellA M' (rb + 3758096384 + 4 * (nf + Z.of_nat j)) 4 (nth j ws 0)).
Proof.
  intros ws regs M rom sp HI ia mp c chp n r rb nf nfr H2 H8 H9 H10 H18 H19 H20 H21 H22 H23 H25 HHI Hsp Hsp' Hr Hr' Hrb Hrb' HHI' En Hn Hchp Hchp' Hnf Hmfa' Hnfr Hia Hmp Hc
    A1 A2 A3 Wr Wfa Cnfr Cws.
  unfold apart in A1, A2, A3.
  eassert (RUN1 : msteps ASEGS (mkst regs (0x55b7c : word) M rom) _).
  { zbft F_55b2c D_55b2c.
    zbft F_55b30 D_55b30.
    zstep F_55b34 D_55b34. zstep F_55b38 D_55b38. zstep F_55b3c D_55b3c. zstep F_55b40 D_55b40.
    apply mst_refl. }
  assert (Hlen : (1 <= length ws)%nat) by lia.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?X1 _) =>
    assert (Wfa1 : wrA X1 (rb + 3758096384 + 4 * nf) (4 * Z.of_nat (length ws))) by (eapply wr_sub; [exact Wfa|lia|lia]);
    destruct (art_rta_copy ws R1 X1 rom (rb + 3758096384 + 4 * nf) chp (chp + 4 * n) ltac:(gres; f_equal; lia) ltac:(gres; rwH; reflexivity) ltac:(gres; f_equal; lia)
                ltac:(lia) Hlen ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; lia) Wfa1 Cws) as (r2 & RUN2 & K2);
    gkeep3 K2 r2 (2%bv : reg) (Z_to_bv 64 (sp - 128)); gkeep3 K2 r2 (8%bv : reg) (Z_to_bv 64 r); gkeep3 K2 r2 (18%bv : reg) (Z_to_bv 64 c);
    gkeep3 K2 r2 (19%bv : reg) (Z_to_bv 64 mp); gkeep3 K2 r2 (20%bv : reg) (Z_to_bv 64 ia); gkeep3 K2 r2 (21%bv : reg) (Z_to_bv 64 n); gkeep3 K2 r2 (23%bv : reg) (Z_to_bv 64 (nf + n));
    set (X2 := art_w4s X1 (rb + 3758096384 + 4 * nf) ws) in *;
    assert (Cnfr2 : cellA X2 (r + 80) 8 nfr) by (apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|exact Cnfr]);
    assert (Wr2 : wrA X2 r 128) by (eapply wr_grows; [apply art_w4s_grows|exact Wr]);
    assert (G2 : mem_grows X1 X2) by (apply art_w4s_grows);
    assert (AG2 : art_agree [(rb + 3758096384 + 4 * nf, 4 * n)] X1 X2) by (intros x Hx; cbn [art_out fst snd] in Hx; apply art_w4s_outside; [lia|lia|rewrite <- En; tauto]);
    assert (CW2 : forall j, (j < length ws)%nat -> cellA X2 (rb + 3758096384 + 4 * nf + 4 * Z.of_nat j) 4 (nth j ws 0))
      by (intros j Hj; apply cell_w4s_nth; [lia|lia|exact Hj|intros k Hk; destruct (Cws k Hk) as [Rk _]; lia])
  end.
  clearbody X2.
  match type of RUN2 with msteps _ _ ?S2 => eassert (RUN3 : msteps ASEGS S2 _) end.
  { zld F_55b58 D_55b58 (r + 80) Cnfr2.
    zsd F_55b5c D_55b5c (r + 16) (nf + n) ltac:(zwok').
    zstep F_55b60 D_55b60.
    zsd F_55b64 D_55b64 (r + 80) (nfr + n) ltac:(zwok').
    zstep F_55b68 D_55b68. zstep F_55b6c D_55b6c. zstep F_55b70 D_55b70. zstep F_55b74 D_55b74.
    stepn F_55b78 D_55b78.
    apply mst_refl. }
  eexists. eexists. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3|].
  split; [gres; bveq|]. split; [gres; rwH; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split. { intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rewrite K2 by reg_neq_tac; gres; first [reflexivity | rwH; reflexivity]|]). destruct Hx. }
  split. { eapply mem_grows_trans; [exact G2|]. zgrows. }
  split. { eapply art_agree_sub; [eapply art_agree_trans; [exact AG2|]; zagree|]. zsub. }
  split; [zcell|]. split; [zcell|].
  intros j Hj. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. replace (rb + 3758096384 + 4 * (nf + Z.of_nat j)) with (rb + 3758096384 + 4 * nf + 4 * Z.of_nat j) by lia.
  apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. exact (CW2 j Hj).
Qed.

End FPX.

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

Definition art_rta_mid_fp (sp t spb ris qs c nf n mfa : Z) : list (Z * Z) :=
  [ (sp - 576, 448); (spb + c * 2 ^ 32 + 3758096384 + 4 * nf, 4 * n); (ris + 128 * c + 16, 16); (ris + 128 * c + 80, 8);
    (spb + c * 2 ^ 32 + 3758096384 + mfa, 536870912 - mfa); (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864); (t + 2872, 16) ].

#[using="Type"] Lemma art_rta_mid_aruns :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) ws regs (M rom : word -> option byte)
         (sp HI t ctx tp key tsd spb ris qs mp c chp n nf mfa kf nfr m1 m2 : Z),
    getr regs 2 = Z_to_bv 64 (sp - 128) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 (ris + 128 * c) -> getr regs 12 = Z_to_bv 64 (spb + c * 2 ^ 32) ->
    getr regs 18 = Z_to_bv 64 c -> getr regs 19 = Z_to_bv 64 mp -> getr regs 20 = Z_to_bv 64 1303448 -> getr regs 21 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 chp ->
    getr regs 25 = Z_to_bv 64 (spb + c * 2 ^ 32 + 3758096384) ->
    art_geo HI t ctx tp tsd spb ris qs -> HI <= sp - 576 -> sp < 2 ^ 47 -> 1 <= c <= 30 ->
    n = Z.of_nat (length ws) -> 1 <= n <= 16 -> t + 208 <= chp -> chp + 4 * n <= t + 2800 ->
    0 <= nf -> 4 * nf <= mfa -> mfa = 262144 * kf -> art_mfa_grow mfa (nf + n) <= 2 ^ 29 -> 0 <= nfr < 2 ^ 64 -> 0 <= mp < 2 ^ 64 ->
    wrA M (sp - 576) 448 -> wrA M (ris + 128 * c) 128 -> wrA M (spb + c * 2 ^ 32 + 3758096384) mfa -> wrA M t 4096 ->
    wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048) 67108864 ->
    art_prim_consts spb ris M -> art_layout M -> art_tsd M tp key tsd ctx t ->
    cellA M (ris + 128 * c + 16) 8 nf -> cellA M (ris + 128 * c + 24) 8 mfa -> cellA M (ris + 128 * c + 80) 8 nfr ->
    cellA M (t + 2872) 8 m1 -> cellA M (t + 2880) 8 m2 ->
    (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA M (chp + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
    art_evok_list EVOK log (art_rta_events spb c nf n mfa) ->
    (forall regs' (M' : word -> option byte),
        getr regs' 1 = (0x55bcc : bv 64)%bv -> getr regs' 2 = Z_to_bv 64 (sp - 128) -> getr regs' 10 = Z_to_bv 64 1303448 -> getr regs' 11 = Z_to_bv 64 mp ->
        getr regs' 12 = Z_to_bv 64 c -> getr regs' 13 = Z_to_bv 64 0 ->
        (forall x : reg, In x [3; 4; 8; 24]%bv -> getr regs' x = getr regs x) ->
        mem_grows M M' -> art_agree (art_rta_mid_fp sp t spb ris qs c nf n mfa) M M' ->
        cellA M' (ris + 128 * c + 16) 8 (nf + n) -> cellA M' (ris + 128 * c + 24) 8 (art_mfa_grow mfa (nf + n)) -> cellA M' (ris + 128 * c + 80) 8 (nfr + n) ->
        (forall j, (j < length ws)%nat -> cellA M' (spb + c * 2 ^ 32 + 3758096384 + 4 * (nf + Z.of_nat j)) 4 (nth j ws 0)) ->
        wrA M' (spb + c * 2 ^ 32 + 3758096384) (art_mfa_grow mfa (nf + n)) ->
        (exists m1' m2', cellA M' (t + 2872) 8 m1' /\ cellA M' (t + 2880) 8 m2') ->
        Q (log ++ art_rta_events spb c nf n mfa) (mkst regs' (0x55ec0 : word) M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x55b64 : word) M rom).
Proof.
  intros Q log ws regs M rom sp HI t ctx tp key tsd spb ris qs mp c chp n nf mfa kf nfr m1 m2
         H2 H4 H8 H12 H18 H19 H20 H21 H22 H25 GEO HHI Hsp' Hc En Hn Hchp Hchp' Hnf Hnf4 Emfa Room Hnfr Hmp W Wr Wfa Wt Wsh PC L T Cnf Cmfa Cnfr Cm1 Cm2 Cws EV K.
  destruct GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x698000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  assert (Ac_i : apart ctx 4096 0x10000 (0x698000 - 0x10000)) by (unfold apart; clear - G15; lia).
  assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G16; lia).
  clear G9 G10 G15 G16.
  destruct PC as (Cspb & Cris & Crel & Cpm & Cmask & Cpg1 & Cpg2 & Cdec & Clim).
  assert (Ccf : cellA M 0x1391a8 8 0x1d3528) by (destruct L as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  set (r := ris + 128 * c) in *. set (rb := spb + c * 2 ^ 32) in *. set (fa := rb + 3758096384) in *.
  assert (Er : r = ris + 128 * c) by reflexivity. assert (Erb : rb = spb + c * 2 ^ 32) by reflexivity. assert (Efa : fa = rb + 3758096384) by reflexivity.
  clearbody r rb fa.
  assert (Hmfa0 : 0 <= mfa) by lia.
  unfold art_rta_events in EV, K.
  destruct (4 * (nf + n) <=? mfa) eqn:Eleb.
  -
    apply Z.leb_le in Eleb.
    assert (Eg : art_mfa_grow mfa (nf + n) = mfa) by (apply art_mfa_grow_warm; exact Eleb).
    rewrite Eg in Room, K.
    destruct (art_rta_mid_run ws regs M rom sp HI 1303448 mp c chp n r rb nf mfa nfr H2 H8 ltac:(rewrite H12; reflexivity) H18 H19 H20 H21 H22 ltac:(rewrite H25, Efa; reflexivity)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) En Hn ltac:(lia) ltac:(lia) Hnf Eleb Room Hnfr ltac:(lia) Hmp ltac:(lia)
                ltac:(pose proof G11 as X; unfold apart in X |- *; lia) ltac:(pose proof G11 as X; unfold apart in X |- *; lia) ltac:(unfold apart; lia)
                ltac:(eapply wr_sub; [exact W|lia|lia]) Wr ltac:(rewrite Efa in Wfa; exact Wfa) Cnf Cmfa Cnfr Cws)
      as (r2 & M2 & RUN & B1 & B2 & B10 & B11 & B12 & B13 & BK & GM & AG & Dnf & Dnfr & Dfa).
    eapply ar_steps; [exact RUN|]. rewrite <- (app_nil_r log).
    apply ar_done. apply K; try assumption.
    + eapply art_agree_sub; [exact AG|]. unfold art_rta_mid_fp. rewrite <- Erb, <- Er. clear - Efa Hmfa0 Room Hnf Hn. zsub.
    + assert (AGx : art_agree [(sp - 176, 48); (rb + 3758096384 + 4 * nf, 4 * n); (r + 16, 8); (r + 80, 8)] M M2) by exact AG.
      clear AG. ztr.
    + intros j Hj. rewrite Efa. exact (Dfa j Hj).
    + eapply wr_grows; [exact GM|exact Wfa].
    + exists m1, m2. assert (AGx : art_agree [(sp - 176, 48); (rb + 3758096384 + 4 * nf, 4 * n); (r + 16, 8); (r + 80, 8)] M M2) by exact AG.
      clear AG. pose proof At_s as X. unfold apart in X. split; ztr.
  -
    apply Z.leb_gt in Eleb.
    destruct (art_mfa_grow_cold mfa (nf + n) Eleb Hmfa0) as (q & rr & Eq & Hrr & Eg & Hq4).
    rewrite Eg in Room, K, EV. clear Eg.
    cbn [art_evok_list] in EV. destruct EV as [EV _].
    assert (Hkf : 0 <= kf) by lia. assert (Hq1 : kf + 1 <= q) by lia.
    set (addr2 := spb + c * 2 ^ 32 + 3758096384 + mfa) in *. set (len2 := 262144 * q - mfa) in *. set (shb2 := 2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048 + 32768 * kf).
    assert (Haddr2 : addr2 = spb + c * 2 ^ 32 + 3758096384 + mfa) by reflexivity.
    assert (Hlen2 : len2 = 262144 * q - mfa) by reflexivity.
    assert (Hshb2 : shb2 = 2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048 + 32768 * kf) by reflexivity.
    clearbody addr2 len2 shb2.
    set (S := sp - 64). assert (ES : S = sp - 64) by reflexivity. clearbody S.
    assert (At_r : apart t 4096 r 128) by (pose proof G11 as X; unfold apart in X |- *; clear - X Er Eris Hc; lia).

    destruct (art_rta_mida_fn regs M rom sp r n nf 1303448 H2 H8 H20 H21 ltac:(lia) ltac:(lia) Cnf) as (ra & RUNa & A1 & A10 & A11 & A13 & A9 & A23 & AK).
    eapply ar_steps; [exact RUNa|].

    destruct (art_rta_Cm1 ra M rom S r c spb qs (nf + n) mfa kf q rr addr2 Haddr2 A1 ltac:(rewrite AK by inl; rewrite H2; f_equal; lia) A10 A11
                ltac:(rewrite AK by inl; rewrite H12, Erb; reflexivity) A13
                ltac:(lia) ltac:(lia) Hc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Espb ltac:(lia) ltac:(lia) Emfa Eq Hrr ltac:(lia)
                ltac:(eapply wr_sub; [exact W|lia|lia]) Cmfa Cpm Cpg1 Cpg2 Ccf Cdec)
      as (r1 & M1 & RUN1 & ARGS & C1_1 & C1_2 & C1_8 & K1 & G1m & A1m & E1c & E8c & E9c & E18c & E19c & F1c & F8c & F9c & F18c & D1c & D8c & D9c & D18c & D19c & D20c).
    rewrite <- Hlen2 in ARGS, C1_8, F18c, D8c, D18c.
    eapply ar_steps; [exact RUN1|].
    eapply (ar_mmap_fixed ASEGS EVOK GR Q log r1 (0x8c604 : word) (0x8c608 : word) M1 rom addr2 len2 art_at_ecall_mmap ltac:(apply bv_eq; reflexivity) ARGS EV).
    set (MZ := art_zfill M1 addr2 len2). set (rZ := regupd r1 10 (Z_to_bv 64 addr2)).
    assert (AZ : art_agree [(addr2, len2)] M1 MZ) by apply art_agree_zfill.
    assert (GZ : mem_grows M1 MZ) by apply art_zfill_grows.
    assert (AMZ : art_agree [(S - 512, 448); (addr2, len2)] M MZ) by exact (art_agree_trans [(S - 512, 448)] [(addr2, len2)] M M1 MZ A1m AZ).
    assert (GMZ : mem_grows M MZ) by (eapply mem_grows_trans; [exact G1m|exact GZ]).
    assert (WfaZ : wrA MZ fa (262144 * q)).
    { replace (262144 * q) with (mfa + len2) by lia. apply wr_join; [lia|lia|lia|lia|eapply wr_grows; [exact GMZ|exact Wfa]|]. replace (fa + mfa) with addr2 by lia. unfold MZ. apply wr_zfill; lia. }
    clear GZ. clearbody MZ.
    assert (LZ : art_layout MZ).
    { eapply art_layout_fp; [exact AMZ| |exact L]. intros z Hz. cbn. clear - Hz HHI ES G1 G4 Eris G6 Hc Haddr2 Espb Hmfa0. repeat split; lia. }
    assert (TZ : art_tsd MZ tp key tsd ctx t).
    { eapply art_tsd_fp; [exact AMZ| | |exact G19|exact G20|exact G21|exact G22|exact T].
      - intros z Hz. pose proof At_i as X. unfold apart in X. cbn. clear - Hz X HHI ES G1 G4 Eris G6 Hc Haddr2 Espb Hmfa0. repeat split; lia.
      - intros z Hz. pose proof G17 as X1. pose proof G18 as X2. pose proof Ac_s as X3. unfold apart in X1, X2, X3. cbn.
        clear - Hz X1 X2 X3 HHI ES G1 G2 G4 Eris G6 G13 G14 Hc Haddr2 Espb Hmfa0 Room Hlen2. repeat split; lia. }
    pose proof (art_cell_norm _ _ _ _ Cm1) as Cm1n. pose proof (art_cell_norm _ _ _ _ Cm2) as Cm2n.
    pose proof (art_mod64_range m1) as Hm1n. pose proof (art_mod64_range m2) as Hm2n.
    set (m1n := m1 mod 2 ^ 64) in *. set (m2n := m2 mod 2 ^ 64) in *. clearbody m1n m2n.
    assert (Ash_t : apart shb2 (32768 * (q - kf)) t 4096) by (pose proof At_s as X; unfold apart in X |- *; clear - X Hshb2 Espb G4 Eris G6 G1 G2 HHI Hc Hkf Hq1 Room; lia).
    assert (Ash_c : apart shb2 (32768 * (q - kf)) ctx 4096) by (pose proof Ac_s as X; unfold apart in X |- *; clear - X Hshb2 Espb G4 Eris G6 G1 G2 HHI Hc Hkf Hq1 Room; lia).
    assert (Ash_r : apart shb2 (32768 * (q - kf)) r 128) by (unfold apart; clear - Er Hshb2 Espb G4 Eris G6 G1 G2 HHI Hc Hkf Hq1 Room; lia).
    assert (WshZ : wrA MZ shb2 (32768 * (q - kf))). { eapply wr_grows; [exact GMZ|]. eapply wr_sub; [exact Wsh|lia|lia]. }

    destruct (art_rta_Cm2 rZ MZ rom S tp key tsd ctx t r c spb qs mfa kf q m1n m2n addr2 len2 shb2 (getr ra 8) (getr ra 9) (getr ra 18) (getr ra 19) (getr ra 20)
                Haddr2 Hlen2 Hshb2
                ltac:(unfold rZ; gres; exact C1_1) ltac:(unfold rZ; gres; exact C1_2) ltac:(unfold rZ; gres; rewrite K1 by inl; rewrite AK by inl; exact H4)
                ltac:(unfold rZ; gres; exact C1_8) ltac:(unfold rZ; gres; reflexivity)
                ltac:(lia) ltac:(lia) Hc Espb Emfa Hkf Hq1 ltac:(lia) ltac:(unfold kHighMemBeg; lia) ltac:(lia) Hm1n Hm2n
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) At_r G19 G20 G21 G22 ltac:(lia) ltac:(lia) Ash_t Ash_r Ash_c ltac:(lia)
                ltac:(eapply wr_grows; [exact GMZ|]; eapply wr_sub; [exact W|lia|lia]) WshZ
                ltac:(eapply wr_grows; [exact GMZ|]; eapply wr_sub; [exact Wt|lia|lia]) ltac:(eapply wr_grows; [exact GMZ|exact Wr]) LZ TZ
                ltac:(clear A1m; ztr) ltac:(clear A1m; ztr) ltac:(clear A1m; ztr) ltac:(clear A1m; ztr) ltac:(clear A1m; ztr)
                ltac:(clear A1m; ztr) ltac:(clear A1m; ztr) ltac:(clear A1m; ztr) ltac:(clear A1m; ztr)
                ltac:(clear A1m; ztr) ltac:(clear A1m; ztr) ltac:(clear A1m; ztr) ltac:(clear A1m; ztr) ltac:(clear A1m; ztr) ltac:(clear A1m; ztr)
                ltac:(clear A1m; ztr) ltac:(clear A1m; ztr)
                ltac:(clear A1m; pose proof At_s as X; unfold apart in X; ztr) ltac:(clear A1m; pose proof At_s as X; unfold apart in X; ztr))
      as (rC & MC & RUNC & C10 & C2 & C8 & C9 & C18 & C19 & C20 & KC & GC & AC & Tm1 & Tm2 & Tmfa).
    eapply ar_steps; [exact RUNC|].
    assert (GMC : mem_grows M MC) by (eapply mem_grows_trans; [exact GMZ|exact GC]).
    assert (AMC : art_agree [(S - 512, 448); (addr2, len2); (shb2, 32768 * (q - kf)); (t + 2872, 16); (r + 24, 8)] M MC).
    { eapply art_agree_sub; [eapply art_agree_trans; [exact AMZ|exact AC]|]. clear - ES. zsub. }
    assert (KCR : forall x : reg, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rC x = getr ra x).
    { intros x Hx. cbn [In] in Hx.
      destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; (rewrite KC by inl; unfold rZ; gres; apply K1; inl). }
    clear AMZ AC A1m AZ.

    assert (Cws' : forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA MC (chp + 4 * Z.of_nat j) 4 (nth j ws 0)).
    { intros j Hj. destruct (Cws j Hj) as [Rj Cj]. split; [exact Rj|]. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. pose proof At_s as X. pose proof G11 as X'. unfold apart in X, X'. ztr. }
    destruct (art_rta_midb_run ws rC MC rom sp HI 1303448 mp c chp n r rb nf nfr
                ltac:(rewrite C2; f_equal; lia) ltac:(rewrite C8, AK by inl; exact H8) ltac:(rewrite C9; exact A9) C10
                ltac:(rewrite C18, AK by inl; exact H18) ltac:(rewrite C19, AK by inl; exact H19) ltac:(rewrite C20, AK by inl; exact H20)
                ltac:(rewrite KCR, AK by inl; exact H21) ltac:(rewrite KCR, AK by inl; exact H22) ltac:(rewrite KCR by inl; exact A23)
                ltac:(rewrite KCR, AK by inl; rewrite H25, Efa; reflexivity)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) En Hn ltac:(lia) ltac:(lia) Hnf ltac:(lia) Hnfr ltac:(lia) Hmp ltac:(lia)
                ltac:(pose proof G11 as X; unfold apart in X |- *; lia) ltac:(pose proof G11 as X; unfold apart in X |- *; lia) ltac:(unfold apart; lia)
                ltac:(eapply wr_grows; [exact GMC|exact Wr]) ltac:(rewrite <- Efa; eapply wr_sub; [eapply wr_grows; [exact GC|exact WfaZ]|lia|lia])
                ltac:(pose proof At_s as X; unfold apart in X; ztr) Cws')
      as (r2 & M2 & RUN & B1 & B2 & B10 & B11 & B12 & B13 & BK & GM & AG & Dnf & Dnfr & Dfa).
    eapply ar_steps; [exact RUN|]. apply ar_done.
    apply K; try assumption.
    + intros x Hx. rewrite BK by exact Hx. cbn [In] in Hx.
      destruct Hx as [<-|[<-|[<-|[<-|[]]]]]; [rewrite KCR, AK by inl; reflexivity|rewrite KCR, AK by inl; reflexivity|rewrite C8, AK by inl; reflexivity|rewrite KCR, AK by inl; reflexivity].
    + eapply mem_grows_trans; [exact GMC|exact GM].
    + eapply art_agree_sub; [eapply art_agree_trans; [exact AMC|exact AG]|]. unfold art_rta_mid_fp. rewrite <- Erb, <- Er. rewrite <- Efa.
      clear - ES Efa Haddr2 Erb Hlen2 Hshb2 Hmfa0 Room Hnf Hn Hkf Hq1 Hq4 Emfa. zsub.
    + replace (r + 24) with (r + 16 + 8) in Tmfa by lia. clear AMC. pose proof Tmfa as X. replace (r + 16 + 8) with (r + 24) in X by lia. ztr.
    + intros j Hj. rewrite Efa. exact (Dfa j Hj).
    + eapply wr_grows; [exact GM|]. eapply wr_grows; [exact GC|exact WfaZ].
    + exists (m1n + 1), (m2n + len2). clear AMC. pose proof At_s as X. unfold apart in X. split; ztr.
Qed.

#[using="Type"] Lemma art_rta_aruns :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) ws regs (M rom : word -> option byte) (raw : word)
         (sp HI t ctx tp key tsd spb ris qs qris mp st c chp n nf mfa kf nfr m1 m2 : Z),
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 1303448 -> getr regs 11 = Z_to_bv 64 mp ->
    getr regs 12 = Z_to_bv 64 st -> getr regs 13 = Z_to_bv 64 c -> getr regs 14 = Z_to_bv 64 chp -> getr regs 15 = Z_to_bv 64 n ->
    art_geo HI t ctx tp tsd spb ris qs -> HI <= sp - 576 -> sp < 2 ^ 47 -> 1 <= c <= 30 -> ris = 128 * qris ->
    n = Z.of_nat (length ws) -> 1 <= n <= 16 -> t + 208 <= chp -> chp + 4 * n <= t + 2800 ->
    0 <= nf -> 4 * nf <= mfa -> mfa = 262144 * kf -> art_mfa_grow mfa (nf + n) <= 2 ^ 29 -> 0 <= nfr < 2 ^ 64 -> 0 <= mp < 2 ^ 64 -> 0 <= st < 2 ^ 64 ->
    wrA M (sp - 576) 576 -> wrA M (ris + 128 * c) 128 -> wrA M (spb + c * 2 ^ 32 + 3758096384) mfa -> wrA M t 4096 ->
    wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048) 67108864 ->
    art_prim_consts spb ris M -> art_layout M -> art_tsd M tp key tsd ctx t ->
    cellA M (ris + 128 * c) 8 0 -> cellA M (ris + 128 * c + 16) 8 nf -> cellA M (ris + 128 * c + 24) 8 mfa -> cellA M (ris + 128 * c + 80) 8 nfr ->
    cellA M (t + 2872) 8 m1 -> cellA M (t + 2880) 8 m2 ->
    (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA M (chp + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
    art_evok_list EVOK log (art_rta_events spb c nf n mfa) ->
    (forall regs' (M' : word -> option byte),
        getr regs' 2 = Z_to_bv 64 sp ->
        (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
        mem_grows M M' -> art_agree (art_rta_fp sp t spb ris qs c nf n mfa) M M' ->
        cellA M' (ris + 128 * c) 8 0 -> cellA M' (ris + 128 * c + 16) 8 (nf + n) -> cellA M' (ris + 128 * c + 24) 8 (art_mfa_grow mfa (nf + n)) ->
        cellA M' (ris + 128 * c + 80) 8 (nfr + n) ->
        (forall j, (j < length ws)%nat -> cellA M' (spb + c * 2 ^ 32 + 3758096384 + 4 * (nf + Z.of_nat j)) 4 (nth j ws 0)) ->
        wrA M' (spb + c * 2 ^ 32 + 3758096384) (art_mfa_grow mfa (nf + n)) ->
        (exists m1' m2', cellA M' (t + 2872) 8 m1' /\ cellA M' (t + 2880) 8 m2') ->
        Q (log ++ art_rta_events spb c nf n mfa) (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x55a18 : word) M rom).
Proof.
  intros Q log ws regs M rom raw sp HI t ctx tp key tsd spb ris qs qris mp st c chp n nf mfa kf nfr m1 m2
         H1 Hret H2 H4 H10 H11 H12 H13 H14 H15 GEO HHI Hsp' Hc Eq En Hn Hchp Hchp' Hnf Hnf4 Emfa Room Hnfr Hmp Hst W Wr Wfa Wt Wsh PC L T Cmx Cnf Cmfa Cnfr Cm1 Cm2 Cws EV K.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x698000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  clear G9 G10 G15 G16. unfold apart in G11, At_i, At_s.
  pose proof PC as (Cspb & Cris & Crel & Cpm & Crd & Cpc & Cpg & Cdec & Clim).
  assert (Hmfa0 : 0 <= mfa) by lia.
  destruct (art_mfa_grow_facts mfa (nf + n) kf Emfa Hmfa0 ltac:(lia)) as (Hg1 & Hg2 & _).
  set (mfa' := art_mfa_grow mfa (nf + n)) in *.
  set (r := ris + 128 * c) in *. set (rb := spb + c * 2 ^ 32) in *.
  assert (Hr : 0x698000 <= r /\ r + 128 <= HI) by (unfold r; lia). destruct Hr as (Hr & Hr').
  assert (Hrb : 0x698000 <= rb /\ rb + 2 ^ 32 <= ris) by (unfold rb; lia). destruct Hrb as (Hrb & Hrb').

  pose proof (art_rta_lock_fn regs M rom raw sp 1303448 mp st c chp n spb ris qris H1 H2 H10 H11 H12 H13 H14 H15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Eq
                ltac:(unfold apart; fold r; lia) Hmp Hst ltac:(lia) ltac:(lia) ltac:(eapply wr_sub; [exact W|lia|lia]) Wr Cspb Cris Cmx) as RUN1.
  fold r in RUN1. unfold art_gfa_frame in RUN1.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?X1 _) =>
    assert (F1 : mem_grows M X1 /\ art_agree [(sp - 208, 208); (r, 8)] M X1) by (split; [zgrows|eapply art_agree_sub; [zagree|]; zsub]);
    assert (C1 : cellA X1 r 8 (2 ^ 60)
                 /\ cellA X1 (sp - 8) 8 (U raw) /\ cellA X1 (sp - 16) 8 (U (getr regs 8)) /\ cellA X1 (sp - 24) 8 (U (getr regs 9)) /\ cellA X1 (sp - 32) 8 (U (getr regs 18))
                 /\ cellA X1 (sp - 40) 8 (U (getr regs 19)) /\ cellA X1 (sp - 48) 8 (U (getr regs 20)) /\ cellA X1 (sp - 56) 8 (U (getr regs 21)) /\ cellA X1 (sp - 64) 8 (U (getr regs 22))
                 /\ cellA X1 (sp - 72) 8 (U (getr regs 23)) /\ cellA X1 (sp - 80) 8 (U (getr regs 24)) /\ cellA X1 (sp - 88) 8 (U (getr regs 25)) /\ cellA X1 (sp - 96) 8 (U (getr regs 26))
                 /\ cellA X1 (sp - 104) 8 (U (getr regs 27))) by (repeat split; zcell);
    set (Ra := R1) in *; set (Xa := X1) in *
  end.
  destruct F1 as (G1x & AG1).
  destruct C1 as (Cst1 & E8 & E16 & E24 & E32 & E40 & E48 & E56 & E64 & E72 & E80 & E88 & E96 & E104).
  clearbody Xa.
  assert (T1 : forall a (k : nat) v, art_gap [(sp - 208, 208); (r, 8)] a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA Xa a k v).
  { intros a k v G Ha Hk C. exact (art_cell_tr _ M Xa a k v AG1 G Ha Hk C). }
  assert (GI1 : forall a k, a + k <= HI -> apart a k r 8 -> art_gap [(sp - 208, 208); (r, 8)] a k).
  { intros a k Hk A. cbn [art_gap fst snd]. unfold apart in A |- *. repeat split; try exact I; lia. }
  assert (PCa : art_prim_consts spb ris Xa).
  { unfold art_prim_consts. repeat split; (apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|assumption]). }
  assert (La : art_layout Xa). { eapply art_layout_fp; [exact AG1| |exact L]. intros z Hz. cbn. repeat split; lia. }
  assert (Ta : art_tsd Xa tp key tsd ctx t).
  { eapply art_tsd_fp; [exact AG1| | |exact G19|exact G20|exact G21|exact G22|exact T].
    - intros z Hz. cbn. repeat split; lia.
    - intros z Hz. pose proof G17 as X1. pose proof G18 as X2. unfold apart in X1, X2. cbn. repeat split; lia. }
  assert (Cws1 : forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA Xa (chp + 4 * Z.of_nat j) 4 (nth j ws 0)).
  { intros j Hj. destruct (Cws j Hj) as [Rj Cj]. split; [exact Rj|]. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'.
    apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|exact Cj]. }

  apply (ar_steps ASEGS EVOK GR Q log _ _ RUN1).
  apply (aruns_bind ASEGS EVOK GR (fun lg s1 => aruns ASEGS EVOK GR Q lg s1) Q); [|intros lg s1 X; exact X].
  apply (art_rta_mid_aruns (fun lg s1 => aruns ASEGS EVOK GR Q lg s1) log ws Ra Xa rom sp HI t ctx tp key tsd spb ris qs mp c chp n nf mfa kf nfr m1 m2);
    [unfold Ra; gres; reflexivity|unfold Ra; gres; exact H4|unfold Ra; gres; reflexivity|unfold Ra; gres; reflexivity|unfold Ra; gres; reflexivity|unfold Ra; gres; reflexivity
    |unfold Ra; gres; reflexivity|unfold Ra; gres; reflexivity|unfold Ra; gres; reflexivity|unfold Ra; gres; reflexivity
    |exact GEO|exact HHI|exact Hsp'|exact Hc|exact En|exact Hn|exact Hchp|exact Hchp'|exact Hnf|exact Hnf4|exact Emfa|exact Room|exact Hnfr|exact Hmp
    |eapply wr_grows; [exact G1x|]; eapply wr_sub; [exact W|lia|lia]|eapply wr_grows; [exact G1x|exact Wr]|eapply wr_grows; [exact G1x|exact Wfa]|eapply wr_grows; [exact G1x|exact Wt]
    |eapply wr_grows; [exact G1x|exact Wsh]|exact PCa|exact La|exact Ta
    |apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|exact Cnf]|apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|exact Cmfa]
    |apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|exact Cnfr]
    |apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|exact Cm1]|apply T1; [apply GI1; [cbn; lia|unfold apart; cbn; lia]|lia|cbn; lia|exact Cm2]
    |exact Cws1|exact EV|].
  intros r2 M2 B1 B2 B10 B11 B12 B13 BK G2x AG2 Cnf2 Cmfa2 Cnfr2 Cfa2 Wfa2 (m1' & m2' & Cm1' & Cm2').

  set (W2 := art_rta_mid_fp sp t spb ris qs c nf n mfa) in *.
  assert (T2 : forall a (k : nat) v, art_gap W2 a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA Xa a k v -> cellA M2 a k v).
  { intros a k v G Ha Hk C. exact (art_cell_tr W2 Xa M2 a k v AG2 G Ha Hk C). }
  assert (GI : forall a k, 0x10000 <= a -> a + k <= 0x698000 -> art_gap W2 a k).
  { intros a k Ha Hk. unfold W2, art_rta_mid_fp. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  destruct PCa as (_ & Cris1 & Crel1 & _ & Crd1 & Cpc1 & Cpg1 & _ & _).
  assert (Cris2 : cellA M2 (1303448 + 48) 8 ris) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Cris1]).
  assert (Crel2 : cellA M2 (1303448 + 40) 4 0xffffffff) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Crel1]).
  assert (Cpc2 : cellA M2 0x139198 8 0x1d14a0) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Cpc1]).
  assert (Cpg2 : cellA M2 0x1d14a0 8 4096) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Cpg1]).
  assert (W1a : wrA Xa (sp - 208) 208) by (eapply wr_grows; [exact G1x|]; eapply wr_sub; [exact W|lia|lia]).
  assert (W1r : wrA Xa r 128) by (eapply wr_grows; [exact G1x|exact Wr]).
  destruct (art_mrtos_ret r2 M2 rom (0x55bcc : bv 64)%bv (sp - 128) 1303448 c ris (nf + n) ((nfr + n) mod 2 ^ 64) B1 ltac:(unfold ret_ok; bveq) B2 B10 B12 B13 ltac:(lia) ltac:(lia)
              ltac:(eapply wr_grows; [exact G2x|]; eapply wr_sub; [exact W1a|lia|lia]) Hc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; fold r; lia) ltac:(lia)
              ltac:(apply Z.mod_pos_bound; lia) ltac:(eapply wr_grows; [exact G2x|exact W1r]) Cris2 Cpc2 Cpg2 Crel2 Cnf2 ltac:(apply art_cell_norm; exact Cnfr2))
    as (r3 & RUN3 & D2 & DK).
  destruct (art_f80_facts M2 (sp - 128) (0x55bcc : bv 64)%bv r2 ltac:(lia) ltac:(lia)) as (G3 & AG3).
  set (M3 := art_f80 M2 (sp - 128) (0x55bcc : bv 64)%bv r2) in *. clearbody M3.
  replace (sp - 128 - 80) with (sp - 208) in AG3 by lia.

  assert (T3 : forall a (k : nat) v, art_gap W2 a (Z.of_nat k) -> apart a (Z.of_nat k) (sp - 208) 80 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA Xa a k v -> cellA M3 a k v).
  { intros a k v G A Ha Hk C. apply (art_cell_tr _ M2 M3 a k v AG3); [cbn [art_gap fst snd]; split; [exact A|exact I]|exact Ha|exact Hk|]. exact (T2 a k v G Ha Hk C). }
  assert (GF : forall a k, sp - 128 <= a -> a + k <= sp -> art_gap W2 a k /\ apart a k (sp - 208) 80).
  { intros a k Ha Hk. unfold W2, art_rta_mid_fp. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (GRx : art_gap W2 r 8 /\ apart r 8 (sp - 208) 80) by (unfold W2, art_rta_mid_fp; cbn [art_gap fst snd]; unfold apart, r; repeat split; try exact I; lia).
  pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R8. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R9. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as R18.
  pose proof (bv_unsigned_in_range 64 (getr regs 19)) as R19. pose proof (bv_unsigned_in_range 64 (getr regs 20)) as R20. pose proof (bv_unsigned_in_range 64 (getr regs 21)) as R21.
  pose proof (bv_unsigned_in_range 64 (getr regs 22)) as R22. pose proof (bv_unsigned_in_range 64 (getr regs 23)) as R23. pose proof (bv_unsigned_in_range 64 (getr regs 24)) as R24.
  pose proof (bv_unsigned_in_range 64 (getr regs 25)) as R25. pose proof (bv_unsigned_in_range 64 (getr regs 26)) as R26. pose proof (bv_unsigned_in_range 64 (getr regs 27)) as R27.
  change (bv_modulus 64) with (2 ^ 64) in *.
  pose proof (art_rta_tail_fn r3 M3 rom raw sp r ris qris c _ _ _ _ _ _ _ _ _ _ _ _ D2
                ltac:(rewrite DK by inl3; rewrite BK by inl3; unfold Ra; gres; reflexivity) ltac:(rewrite DK by inl3; rewrite BK by inl3; unfold Ra; gres; reflexivity)
                ltac:(lia) ltac:(lia) eq_refl Eq ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; lia) Hret R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27
                ltac:(apply (wr_wok _ _ r 128); [eapply wr_grows; [exact G3|]; eapply wr_grows; [exact G2x|exact W1r]|lia|cbn; lia])
                ltac:(apply T3; [apply GRx|apply GRx|lia|cbn; lia|exact Cst1]) ltac:(apply T3; [apply GI; cbn; lia|unfold apart; cbn; lia|lia|cbn; lia|exact Crd1])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E8]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E16])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E24]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E32])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E40]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E48])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E56]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E64])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E72]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E80])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E88]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E96])
                ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E104])) as RUN4.
  assert (T4 : forall a (k : nat) v, apart a (Z.of_nat k) (sp - 208) 80 -> apart a (Z.of_nat k) r 8 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M2 a k v -> cellA (Wn 8 M3 r 0) a k v).
  { intros a k v A1 A2 Ha Hk C. apply cell_Wn_other; [lia|cbn; lia|exact Ha|exact Hk|apply apart_sym; exact A2|].
    apply (art_cell_tr _ M2 M3 a k v AG3); [cbn [art_gap fst snd]; split; [exact A1|exact I]|exact Ha|exact Hk|exact C]. }
  eapply ar_steps; [eapply msteps_trans; [exact RUN3|exact RUN4]|]. apply ar_done.
  apply K.
  - gres; reflexivity.
  - intros x Hx. cbn [In] in Hx.
    destruct Hx as [<-|Hx]; [gres; rewrite DK by inl3; rewrite BK by inl3; unfold Ra; gres; reflexivity|].
    destruct Hx as [<-|Hx]; [gres; rewrite DK by inl3; rewrite BK by inl3; unfold Ra; gres; reflexivity|].
    repeat (destruct Hx as [<-|Hx]; [gres; apply Z_to_bv_bv_unsigned|]). destruct Hx.
  - eapply mem_grows_trans; [exact G1x|]. eapply mem_grows_trans; [exact G2x|]. eapply mem_grows_trans; [exact G3|]. apply Wn_grows.
  - eapply art_agree_sub; [eapply art_agree_trans; [exact AG1|]; eapply art_agree_trans; [exact AG2|]; eapply art_agree_trans; [exact AG3|]; apply art_agree_Wn; [lia|cbn; lia]|].
    unfold W2, art_rta_mid_fp, art_rta_fp. fold r rb. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; lia.
  - apply cell_Wn_hit; [lia|cbn; lia].
  - apply T4; [unfold apart; cbn; lia|unfold apart; cbn; lia|lia|cbn; lia|exact Cnf2].
  - apply T4; [unfold apart; cbn; lia|unfold apart; cbn; lia|lia|cbn; lia|exact Cmfa2].
  - apply T4; [unfold apart; cbn; lia|unfold apart; cbn; lia|lia|cbn; lia|exact Cnfr2].
  - intros j Hj. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. apply T4; [unfold apart, rb; cbn; lia|unfold apart, r, rb; cbn; lia|unfold rb; lia|unfold rb; cbn; lia|exact (Cfa2 j Hj)].
  - eapply wr_grows; [apply Wn_grows|]. eapply wr_grows; [exact G3|exact Wfa2].
  - exists m1', m2'. split; (apply T4; [unfold apart; cbn; lia|unfold apart, r; cbn; lia|lia|cbn; lia|assumption]).
Qed.

End Spec.
