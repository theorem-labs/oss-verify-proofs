(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatInitCache_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatRefill1_b BatPopulate1_b BatPopulate4_b
     BatCls_b BatFp_b BatClsPop3_b BatClsRep_b BatClsGfa1_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_cls_pre_take (c : Z) (cl : art_cls) : art_cls := if art_cls_needs_populate c cl then art_cls_populate c cl else cl.
Lemma art_cls_refill_eq : forall c cl, art_cls_refill c cl = art_cls_take (art_refill_n c) (art_cls_pre_take c cl).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition art_gfa_fp (sp t spb ris qs c km : Z) : list (Z * Z) :=
  (sp - 128, 128) :: (t + 208 + 80 * c + 16, 64) :: art_pop_fp (sp - 128) t spb ris qs c km.

Lemma art_prim_consts_fp : forall W M M' spb ris, art_agree W M M' -> (forall z, 0x10000 <= z < 0x696000 -> art_out W z) ->
  art_prim_consts spb ris M -> art_prim_consts spb ris M'.
Proof.
  intros W M M' spb ris A O (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  assert (TI : forall a (n : nat) v, 0x10000 <= a -> a + Z.of_nat n <= 0x696000 -> cellA M a n v -> cellA M' a n v).
  { intros a n v Ha Hn C. apply (art_cell_agree _ M M'); [|lia|lia|exact C]. intros x Hx. apply A. apply O. lia. }
  unfold art_prim_consts. repeat split; apply TI; first [assumption | cbn; lia].
Qed.

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_gfa_tail :
  forall (Q : list aev -> machine_state -> Prop) (logE : list aev) regs rE (M M1 ME rom : word -> option byte) (raw : word)
         (sp HI t spb ris qs c km : Z) (n : nat) (cl1 : art_cls),
    let fa := spb + c * 2 ^ 32 + 3758096384 in
    let r := ris + 128 * c in
    let chp := t + 208 + 80 * c + 16 in
    let k := (length (cl_free cl1) - n)%nat in
    ret_ok raw -> 1 <= c <= 30 -> HI <= sp - 640 -> sp < 2 ^ 47 ->
    spb = 65536 * qs -> 0x10007fff8000 <= spb -> ris = spb + 2 ^ 37 -> ris + 4096 <= HI -> 4096 <= t -> t + 4096 <= HI ->
    apart t 4096 spb (2 ^ 37 + 4096) -> apart t 4096 0x10000 (0x696000 - 0x10000) ->
    (1 <= n <= 8)%nat -> (n <= length (cl_free cl1))%nat -> 4 * Z.of_nat (length (cl_free cl1)) <= 2 ^ 29 ->
    Forall (art_cptr_ok (AsanTab.class_size c) (cl_au cl1)) (cl_free cl1) -> cl_au cl1 <= 3758096384 ->
    art_region_rep spb ris c (2 ^ 60) cl1 M1 -> cellA M1 0x10420 8 0xafffff00000fffff -> wrA M1 t 4096 ->
    mem_grows M M1 -> art_agree (art_gfa_fp sp t spb ris qs c km) M M1 ->
    mem_grows M1 ME -> art_agree [(r + 16, 8)] M1 ME -> cellA ME (r + 16) 8 (Z.of_nat k) ->
    art_gfa_fcells ME sp raw (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                   (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ->
    getr rE 2 = Z_to_bv 64 (sp - 128) -> getr rE 8 = Z_to_bv 64 r -> getr rE 11 = Z_to_bv 64 (chp + 4 * Z.of_nat n) -> getr rE 13 = Z_to_bv 64 chp ->
    getr rE 14 = Z_to_bv 64 (Z.of_nat n) -> getr rE 19 = Z_to_bv 64 (2 ^ 61) -> getr rE 20 = Z_to_bv 64 (fa + 4 * Z.of_nat k) ->
    getr rE 3 = getr regs 3 -> getr rE 4 = getr regs 4 ->
    (forall regs' (M' : word -> option byte),
        getr regs' 10 = Z_to_bv 64 1 -> getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
        (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
        mem_grows M M' -> art_agree (art_gfa_fp sp t spb ris qs c km) M M' ->
        mem_grows M1 M' -> art_agree [(r + 16, 8); (chp, 64); (r + 72, 8); (r, 8)] M1 M' ->
        art_region_rep spb ris c 0 (art_cls_take n cl1) M' ->
        (forall j, (j < n)%nat -> cellA M' (chp + 4 * Z.of_nat j) 4 (nth j (cl_cache (art_cls_take n cl1)) 0)) ->
        Q logE (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q logE (mkst rE (0x57700 : word) ME rom).
Proof.
  intros Q logE regs rE M M1 ME rom raw sp HI t spb ris qs c km n cl1 fa r chp k
         Hret Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ati Hn Hnl Hnf Hcp Hau RR1 Crd Wt GM1 AM1 G1E A1E Cnf F E2 E8 E11 E13 E14 E19 E20 E3 E4 K.
  assert (Hr : r = ris + 128 * c) by reflexivity. assert (Hfa : fa = spb + c * 2 ^ 32 + 3758096384) by reflexivity. assert (Hchp : chp = t + 208 + 80 * c + 16) by reflexivity.
  assert (Hk : Z.of_nat k = Z.of_nat (length (cl_free cl1)) - Z.of_nat n) by (unfold k; lia).
  pose proof RR1 as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
  fold r in Rmx, Rnf, Rmfa, Rau, Ram, Rmu, Rmm, Rna, Rnfr, Wr. fold fa in Rfa.
  set (ws := skipn k (cl_free cl1)).
  assert (Lws : length ws = n) by (unfold ws; rewrite length_skipn; unfold k; lia).
  assert (Nws : forall j, (j < n)%nat -> nth j ws 0 = nth (k + j) (cl_free cl1) 0). { intros j Hj. unfold ws. apply nth_skipn. }
  pose proof (art_class_size_facts c Hc) as (Hsz & _).
  unfold apart in Atk, Ati.
  pose proof (art_cell_norm _ _ _ _ Rna) as Rnan. pose proof (art_mod64_range (cl_na cl1)) as Hnan.
  destruct (art_clsgfa_finish ws rE ME rom raw sp r ris (512 * qs + 2 ^ 30) c chp (fa + 4 * Z.of_nat k) (cl_na cl1 mod 2 ^ 64)
              (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
              E2 E8 ltac:(rewrite Lws; exact E11) E13 ltac:(rewrite Lws; exact E14) E19 E20 Hret ltac:(rewrite Lws; exact Hn)
              ltac:(lia) Hsp' Hr ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(rewrite Lws; unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia) Hnan
              ltac:(rewrite Lws; eapply wr_grows; [exact G1E|]; eapply wr_sub; [exact Wt|lia|lia]) ltac:(eapply wr_grows; [exact G1E|exact Wr])
              ltac:(intros j Hj; rewrite Lws in Hj; rewrite (Nws j Hj); split;
                    [ assert (X : art_cptr_ok (AsanTab.class_size c) (cl_au cl1) (nth (k + j) (cl_free cl1) 0)) by (apply (proj1 (Forall_forall _ _) Hcp); apply nth_In; lia);
                      pose proof (art_cptr_lt (AsanTab.class_size c) (cl_au cl1) _ ltac:(lia) Hau X); lia
                    | replace (fa + 4 * Z.of_nat k + 4 * Z.of_nat j) with (fa + 4 * Z.of_nat (k + j)) by lia;
                      apply (art_cell_tr _ M1 ME _ _ _ A1E); [zgap|lia|cbn; lia|apply Rfa; lia] ])
              ltac:(ztr) ltac:(ztr) ltac:(ztr) F)
    as (rF & MF & RUNF & F10 & F2 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F3 & F4 & GF & AF & Cch & Cna' & Cmx').
  rewrite Lws in AF.
  eapply ar_steps; [exact RUNF|]. apply ar_done.
  assert (A1F : art_agree [(r + 16, 8); (chp, 64); (r + 72, 8); (r, 8)] M1 MF).
  { eapply art_agree_sub; [eapply art_agree_trans; [exact A1E|exact AF]|]. zsub. }
  assert (G1F : mem_grows M1 MF) by (eapply mem_grows_trans; eassumption).
  assert (Lfn : length (firstn k (cl_free cl1)) = k) by (rewrite length_firstn; unfold k; lia).
  apply (K rF MF F10 F2 F1).
  - intros x Hx. cbn [In] in Hx.
    destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
      first [ rewrite F3; exact E3 | rewrite F4; exact E4 | assumption ].
  - eapply mem_grows_trans; [exact GM1|exact G1F].
  - eapply art_agree_sub; [eapply art_agree_trans; [exact AM1|exact A1F]|]. unfold art_gfa_fp, art_pop_fp. fold r chp. clear - Hr Hchp. zsub.
  - exact G1F.
  - exact A1F.
  - apply (art_region_rep_upd spb ris c (2 ^ 60) 0 cl1 (art_cls_take n cl1) M1 MF [(r + 16, 8); (chp, 64); (r + 72, 8); (r, 8)]);
      try reflexivity; fold r fa; cbn [art_cls_take cl_free cl_na]; fold k; rewrite ?Lfn.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact Hnf.
    + lia.
    + intros j Hj. rewrite nth_firstn. replace (j <? k)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). reflexivity.
    + exact RR1.
    + exact G1F.
    + exact A1F.
    + zgap.
    + zgap.
    + zgap.
    + exact Cmx'.
    + ztr.
    + apply art_cell_mod_add. rewrite Lws in Cna'. exact Cna'.
  - intros j Hj. cbn [art_cls_take cl_cache]. fold k ws. apply Cch. rewrite Lws. exact Hj.
Qed.

#[using="Type"] Lemma art_gfa_aruns :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
         (sp HI t ctx tp key tsd spb ris qs c km m1 m2 sv : Z) (cl : art_cls),
    let n := art_refill_n c in
    let chp := t + 208 + 80 * c + 16 in
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp ->
    getr regs 10 = Z_to_bv 64 1295832 -> getr regs 11 = Z_to_bv 64 (t + 2768) -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 chp ->
    getr regs 14 = Z_to_bv 64 (Z.of_nat n) ->
    1 <= c <= 30 -> HI <= sp - 640 -> sp < 2 ^ 47 -> art_geo HI t ctx tp tsd spb ris qs ->
    wrA M (sp - 640) 640 -> wrA M t 4096 ->
    art_prim_consts spb ris M -> art_layout M -> art_tsd M tp key tsd ctx t ->
    art_region_rep spb ris c 0 cl M -> art_cls_ok c cl -> cl_mu cl = 262144 * km ->
    cellA M (t + 2872) 8 m1 -> cellA M (t + 2880) 8 m2 -> cellA M (t + 2792) 8 sv ->
    (art_cls_needs_populate c cl = true ->
       cl_mu cl + 262144 <= 3758096384
       /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912
       /\ wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km) 32768
       /\ wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048) 67108864) ->
    art_evok_list EVOK log (art_refill_events spb c cl) ->
    (forall regs' (M' : word -> option byte),
        getr regs' 10 = Z_to_bv 64 1 -> getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
        (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
        mem_grows M M' -> art_agree (art_gfa_fp sp t spb ris qs c km) M M' ->
        art_region_rep spb ris c 0 (art_cls_refill c cl) M' ->
        (forall j, (j < n)%nat -> cellA M' (chp + 4 * Z.of_nat j) 4 (nth j (cl_cache (art_cls_refill c cl)) 0)) ->
        (art_cls_needs_populate c cl = true -> forall j, 0 <= j < 32768 -> cellA M' (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + j) 1 250) ->
        (exists m1' m2' sv', cellA M' (t + 2872) 8 m1' /\ cellA M' (t + 2880) 8 m2' /\ cellA M' (t + 2792) 8 sv') ->
        Q (log ++ art_refill_events spb c cl) (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x5758c : word) M rom).
Proof.
  intros Q log regs M rom raw sp HI t ctx tp key tsd spb ris qs c km m1 m2 sv cl n chp
         H1 Hret H2 H4 H10 H11 H12 H13 H14 Hc HHI Hsp' GEO W Wt PC L T RR OK Emu Cm1 Cm2 Csv Room EV K.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  assert (Ac_i : apart ctx 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G15; lia).
  clear G9 G10 G15 G16.
  pose proof PC as (Pspb & Pris & _ & _ & Pmask & _).
  pose proof RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
  pose proof OK as (_ & (Hau0 & Haumu) & Hrem0 & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _).
  destruct (art_refill_need c Hc) as (Hneed & Hn). fold n in Hneed, Hn.
  set (r := ris + 128 * c) in *. set (fa := spb + c * 2 ^ 32 + 3758096384) in *. set (nf := Z.of_nat (length (cl_free cl))) in *.
  assert (Er : r = ris + 128 * c) by reflexivity. assert (Efa : fa = spb + c * 2 ^ 32 + 3758096384) by reflexivity. assert (Echp : chp = t + 208 + 80 * c + 16) by reflexivity.
  (* [comment removed for export] *)
  destruct (art_clsgfa_lock regs M rom raw sp (t + 2768) c chp (Z.of_nat n) spb ris (512 * qs + 2 ^ 30) H1 H2 H10 H11 H12 H13 H14
              ltac:(lia) Hsp' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(eapply wr_sub; [exact W|lia|lia]) Wr Pspb Pris Rmx)
    as (rL & ML & RUNL & L2 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L19 & L20 & L3 & L4 & GL & AL & FL & CmxL).
  fold r in L8, L10, AL, CmxL. fold fa in L20.
  eapply ar_steps; [exact RUNL|].
  assert (RRL : art_region_rep spb ris c (2 ^ 60) cl ML).
  { apply (art_region_rep_upd spb ris c 0 (2 ^ 60) cl cl M ML [(sp - 128, 128); (r, 8)]); try reflexivity; fold r fa nf;
      first [ lia | exact RR | exact GL | exact AL | exact CmxL | (intros; reflexivity) | idtac ].
    - clear - Er HHI G6 Eris Hc. zgap.
    - clear - Er HHI G6 Eris Hc. zgap.
    - clear - Er Efa HHI G6 Eris Hc G4 Espb Hnf4 Hmfa1. zgap.
    - ztr.
    - ztr. }
  assert (Hfor' : Forall (art_cptr_ok (AsanTab.class_size c) (cl_au cl)) (cl_free cl)) by (apply Forall_app in Hfor; exact (proj2 Hfor)).
  assert (CrdL : cellA ML 0x10420 8 0xafffff00000fffff) by ztr.
  assert (WtL : wrA ML t 4096) by (eapply wr_grows; [exact GL|exact Wt]).
  assert (AML : art_agree (art_gfa_fp sp t spb ris qs c km) M ML).
  { eapply art_agree_sub; [exact AL|]. unfold art_gfa_fp, art_pop_fp. fold r. clear - Er. zsub. }
  assert (Hnf : 0 <= nf) by (unfold nf; lia).
  assert (Hkm : 0 <= km) by lia.
  destruct (art_cls_needs_populate c cl) eqn:NP.
  - (* [comment removed for export] *)
    assert (Hlt : (length (cl_free cl) < n)%nat) by (unfold art_cls_needs_populate in NP; apply Nat.ltb_lt in NP; exact NP).
    destruct (Room eq_refl) as (Room1 & Room2 & Wsh1 & Wsh2).
    assert (Eev : art_refill_events spb c cl = art_pop_events spb c cl) by (unfold art_refill_events, art_pop_events; rewrite NP; reflexivity).
    rewrite Eev in EV, K.
    pose proof (art_cls_ok_populate c cl Hc OK Room1 Room2) as OK1.
    pose proof (art_gfa_popa_fn rL ML rom 1295832 r chp (Z.of_nat n) nf (r + 8) L8 L9 L10 L13 L14 ltac:(lia) ltac:(lia) ltac:(unfold nf; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ztr)) as RUNP.
    match type of RUNP with msteps _ _ (mkst ?R _ _ _) => set (rP := R) in RUNP end.
    eapply ar_steps; [exact RUNP|].
    pose proof G17 as X17. unfold apart in X17.
    assert (PCL : art_prim_consts spb ris ML). { eapply art_prim_consts_fp; [exact AL| |exact PC]. intros z Hz. cbn. clear - Hz Er HHI G1 G6 Eris Hc G4. repeat split; lia. }
    assert (LL : art_layout ML). { eapply art_layout_fp; [exact AL| |exact L]. intros z Hz. cbn. clear - Hz Er HHI G1 G6 Eris Hc G4. repeat split; lia. }
    assert (TL : art_tsd ML tp key tsd ctx t).
    { eapply art_tsd_fp; [exact AL| | |exact G19|exact G20|exact G21|exact G22|exact T].
      - intros z Hz. cbn. clear - Hz Er HHI G1 G6 Eris Hc G4. repeat split; lia.
      - intros z Hz. cbn. clear - Hz X17 Er HHI G1 G6 G13 G14 Eris Hc G4. repeat split; lia. }
    pose proof G11 as X11. unfold apart in X11.
    set (Q1 := fun (lg : list aev) (st : machine_state) => exists rQ MQ,
                 st = mkst rQ (0x57848 : word) MQ rom /\ lg = log ++ art_pop_events spb c cl
                 /\ getr rQ 10 = Z_to_bv 64 1 /\ getr rQ 2 = Z_to_bv 64 (sp - 128)
                 /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rQ x = getr rP x)
                 /\ mem_grows ML MQ /\ art_agree (art_pop_fp (sp - 128) t spb ris qs c km) ML MQ
                 /\ art_region_rep spb ris c (2 ^ 60) (art_cls_populate c cl) MQ
                 /\ (forall j, 0 <= j < 32768 -> cellA MQ (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + j) 1 250)
                 /\ (exists m1' m2' sv', cellA MQ (t + 2872) 8 m1' /\ cellA MQ (t + 2880) 8 m2' /\ cellA MQ (t + 2792) 8 sv')).
    apply (aruns_bind ASEGS EVOK GR Q1 Q).
    + apply (art_populate_aruns EVOK GR Q1 log rP ML rom (0x57848 : bv 64)%bv (sp - 128) HI t ctx tp key tsd spb ris qs c km (Z.of_nat n - nf) (2 ^ 60) m1 m2 sv cl
               ltac:(unfold rP; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold rP; gres; exact L2) ltac:(unfold rP; gres; rewrite L4; exact H4)
               ltac:(unfold rP; gres; reflexivity) ltac:(unfold rP; gres; exact L11) ltac:(unfold rP; gres; exact L12) ltac:(unfold rP; gres; reflexivity)
               ltac:(unfold rP; gres; reflexivity)
               Hc ltac:(lia) ltac:(lia) GEO ltac:(unfold nf; lia) ltac:(assert (AsanTab.class_size c * (Z.of_nat n - nf) <= AsanTab.class_size c * Z.of_nat n) by (apply Z.mul_le_mono_nonneg_l; [pose proof (art_class_size_facts c Hc); lia|lia]); lia)
               ltac:(eapply wr_grows; [exact GL|]; eapply wr_sub; [exact W|lia|lia]) WtL PCL LL TL RRL OK Emu
               ltac:(ztr_c ltac:(clear - X11 Er HHI Hsp' G2 G6 G7 G8 Eris Hc G4 Espb)) ltac:(ztr_c ltac:(clear - X11 Er HHI Hsp' G2 G6 G7 G8 Eris Hc G4 Espb))
               ltac:(ztr_c ltac:(clear - X11 Er HHI Hsp' G2 G6 G7 G8 Eris Hc G4 Espb))
               Room1 Room2 ltac:(eapply wr_grows; [exact GL|exact Wsh1]) ltac:(eapply wr_grows; [exact GL|exact Wsh2]) EV).
      intros rQ MQ Q10 Q2 Q1' QK QG QA QRR QSH QST. exists rQ, MQ. repeat (split; [first [reflexivity | assumption]|]). assumption.
    + intros lg st (rQ & MQ & -> & -> & Q10 & Q2 & QK & QG & QA & QRR & QSH & QST).
      pose proof QRR as (Qmx & Qnf & _ & _ & _ & _ & _ & _ & _ & _ & Wr' & _ & _). fold r in Qmx, Qnf, Wr'.
      unfold art_pop_fp in QA. fold r in QA.
      pose proof OK1 as (_ & (Hau1 & Haumu1) & _ & _ & _ & Hmu31 & _ & (_ & Hmfa11) & Hnf41 & Hfor1 & _).
      set (cl1 := art_cls_populate c cl) in *. set (nf2 := Z.of_nat (length (cl_free cl1))) in *.
      assert (Hnew : Z.of_nat n - nf <= art_cls_new c cl).
      { unfold art_cls_new. apply Z.div_le_lower_bound; [pose proof (art_class_size_facts c Hc); lia|].
        assert (AsanTab.class_size c * (Z.of_nat n - nf) <= AsanTab.class_size c * Z.of_nat n) by (apply Z.mul_le_mono_nonneg_l; [pose proof (art_class_size_facts c Hc); lia|lia]). lia. }
      assert (Enf2 : nf2 = nf + art_cls_new c cl).
      { unfold nf2, cl1, art_cls_populate. cbn [cl_free]. rewrite length_app, art_carved_length, Nat2Z.inj_add, Z2Nat.id by lia. reflexivity. }
      assert (Hnn : (n <= length (cl_free cl1))%nat) by (fold nf2 in Enf2; lia).
      pose proof (art_gfa_popb_fn rQ MQ rom r fa chp (Z.of_nat n) nf2 (r + 8) Q10
                    ltac:(rewrite QK by inl; unfold rP; gres; exact L8) ltac:(rewrite QK by inl; unfold rP; gres; reflexivity)
                    ltac:(rewrite QK by inl; unfold rP; gres; exact L20) ltac:(rewrite QK by inl; unfold rP; gres; reflexivity) ltac:(rewrite QK by inl; unfold rP; gres; reflexivity)
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Wr' Qnf) as RUNB.
      match type of RUNB with msteps _ _ (mkst ?R _ ?X _) => set (rB := R) in RUNB; set (MB := X) in RUNB end.
      eapply ar_steps; [exact RUNB|].
      assert (A1E : art_agree [(r + 16, 8)] MQ MB). { unfold MB. eapply art_agree_sub; [zagree|]. zsub. }
      pose proof At_i as Xi. unfold apart in Xi.
      apply (art_gfa_tail Q (log ++ art_pop_events spb c cl) regs rB M MQ MB rom raw sp HI t spb ris qs c km n cl1 Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 At_i Hn Hnn
               ltac:(fold nf2; lia) ltac:(apply Forall_app in Hfor1; exact (proj2 Hfor1)) ltac:(lia) QRR
               ltac:(ztr_c ltac:(clear - Xi Er HHI Hsp' G1 G2 G6 G7 G8 Eris Hc G4 Espb Emu Hmu3 Hkm)) ltac:(eapply wr_grows; [exact QG|exact WtL])
               ltac:(eapply mem_grows_trans; [exact GL|exact QG])
               ltac:(eapply art_agree_sub; [eapply art_agree_trans; [exact AL|exact QA]|]; unfold art_gfa_fp, art_pop_fp; fold r; clear - Er; zsub)
               ltac:(unfold MB; apply Wn_grows) A1E).
      * fold r. unfold MB. replace (Z.of_nat (length (cl_free cl1) - n)) with (nf2 - Z.of_nat n) by (unfold nf2; lia). apply cell_Wn_hit; [lia|cbn; lia].
      * pose proof (art_agree_trans _ _ ML MQ MB QA A1E) as AQB.
        eapply (art_gfa_fcells_tr _ ML MB); [exact AQB| |lia|lia|exact FL].
        clear - Er HHI Hsp' G1 G2 G6 G7 G8 Eris Hc G4 Espb Emu Hmu3 Hkm. zgap.
      * unfold rB; gres. exact Q2.
      * unfold rB; gres. rewrite QK by inl. unfold rP; gres. exact L8.
      * unfold rB; gres. fold chp. f_equal. lia.
      * unfold rB; gres. reflexivity.
      * unfold rB; gres. reflexivity.
      * unfold rB; gres. rewrite QK by inl. unfold rP; gres. exact L19.
      * unfold rB; gres. fold fa. f_equal. unfold nf2. lia.
      * unfold rB; gres. rewrite QK by inl. unfold rP; gres. exact L3.
      * unfold rB; gres. rewrite QK by inl. unfold rP; gres. exact L4.
      * intros regs' M' P10 P2 P1 PK PG PA PG1 PA1 PR PC'. apply (K regs' M' P10 P2 P1 PK PG PA).
        -- unfold art_cls_refill. rewrite NP. exact PR.
        -- unfold art_cls_refill. rewrite NP. exact PC'.
        -- intros _ j Hj. pose proof (QSH j Hj) as C. fold r chp in PA1. pose proof At_s as Xs. unfold apart in Xs.
           ztr_c ltac:(clear - Hj Xs Er Echp HHI Hsp' G1 G2 G6 G7 G8 Eris Hc G4 Espb Emu Hmu3 Hkm).
        -- destruct QST as (m1' & m2' & sv' & S1 & S2 & S3). exists m1', m2', sv'. fold r chp in PA1.
           repeat split; ztr_c ltac:(clear - X11 Er Echp HHI Hsp' G2 G6 G7 G8 Eris Hc G4 Espb).
  - (* [comment removed for export] *)
    assert (Hnn : (n <= length (cl_free cl))%nat) by (unfold art_cls_needs_populate in NP; apply Nat.ltb_ge in NP; exact NP).
    unfold art_refill_events in K. rewrite NP in K. rewrite app_nil_r in K.
    pose proof (art_gfa_mid_fn rL ML rom r fa chp (Z.of_nat n) nf L8 L20 L13 L14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold nf; lia) ltac:(lia)
                  ltac:(eapply wr_grows; [exact GL|exact Wr]) ltac:(ztr)) as RUNM.
    match type of RUNM with msteps _ _ (mkst ?R _ ?X _) => set (rM := R) in RUNM; set (MM := X) in RUNM end.
    eapply ar_steps; [exact RUNM|].
    assert (A1E : art_agree [(r + 16, 8)] ML MM). { unfold MM. eapply art_agree_sub; [zagree|]. zsub. }
    apply (art_gfa_tail Q log regs rM M ML MM rom raw sp HI t spb ris qs c km n cl Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 At_i Hn Hnn ltac:(fold nf; lia) Hfor' ltac:(lia)
             RRL CrdL WtL GL AML ltac:(unfold MM; apply Wn_grows) A1E).
    + fold r. unfold MM. replace (Z.of_nat (length (cl_free cl) - n)) with (nf - Z.of_nat n) by (unfold nf; lia). apply cell_Wn_hit; [lia|cbn; lia].
    + eapply (art_gfa_fcells_tr [(r + 16, 8)] ML MM); [exact A1E| |lia|lia|exact FL]. clear - Er HHI G6 Eris Hc. zgap.
    + unfold rM; gres. exact L2.
    + unfold rM; gres. exact L8.
    + unfold rM; gres. fold chp. f_equal. lia.
    + unfold rM; gres. exact L13.
    + unfold rM; gres. exact L14.
    + unfold rM; gres. exact L19.
    + unfold rM; gres. fold fa. f_equal. unfold nf. lia.
    + unfold rM; gres. exact L3.
    + unfold rM; gres. exact L4.
    + intros regs' M' P10 P2 P1 PK PG PA PG1 PA1 PR PC'. apply (K regs' M' P10 P2 P1 PK PG PA).
      * unfold art_cls_refill. rewrite NP. exact PR.
      * unfold art_cls_refill. rewrite NP. exact PC'.
      * intros X. discriminate X.
      * exists m1, m2, sv. fold r chp in PA1. pose proof G11 as X. unfold apart in X.
        repeat split; ztr_c ltac:(clear - X Er Echp HHI Hsp' G2 G6 G7 G8 Eris Hc G4 Espb).
Qed.
End Spec.
