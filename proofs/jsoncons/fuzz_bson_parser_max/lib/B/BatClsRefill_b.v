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
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatInitCache_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatRefill3_b BatRefillCold_b BatPopulate1_b
     BatCls_b BatFp_b BatClsPop3_b BatClsRep_b BatClsGfa2_b.
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
Lemma art_ic_mem_fine : forall k M ca (x : word), 0 <= ca -> ca + 4096 < 2 ^ 64 -> (k <= 31)%nat ->
  ~ art_pc_hdr_foot ca (U x) -> art_ic_mem M ca k x = M x.
Proof.
  induction k as [|k IH]; intros M ca x Hca Hca' Hk N; [reflexivity|]. rewrite art_ic_mem_S.
  assert (N1 : ~ (ca + 80 * (Z.of_nat k + 1) + 4 <= U x < ca + 80 * (Z.of_nat k + 1) + 16)).
  { intros H. apply N. exists (Z.of_nat k + 1). lia. }
  rewrite Wn_outside; [|lia|cbn; lia|cbn; lia]. rewrite Wn_outside; [|lia|cbn; lia|cbn; lia]. apply IH; [exact Hca|exact Hca'|lia|exact N].
Qed.

Lemma art_pc_hdr_ic : forall M ca, 0 <= ca -> ca + 4096 < 2 ^ 64 -> art_pc_hdr ca true (art_ic_mem M ca 31).
Proof. intros M ca Hca Hca' c Hc. split; [apply cell_ic_mc|apply cell_ic_size]; first [lia | cbn; lia]. Qed.

(* [comment removed for export] *)
Lemma art_pre_take_enough : forall c cl, 1 <= c <= 30 -> art_cls_ok c cl -> (art_refill_n c <= length (cl_free (art_cls_pre_take c cl)))%nat.
Proof.
  intros c cl Hc OK. unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl) eqn:NP.
  - unfold art_cls_needs_populate in NP. apply Nat.ltb_lt in NP.
    destruct OK as (_ & (Hau0 & Haumu) & _).
    destruct (art_refill_need c Hc) as (Hneed & Hn). pose proof (art_class_size_facts c Hc) as (Hsz & _).
    unfold art_cls_populate. cbn [cl_free]. rewrite length_app, art_carved_length.
    assert (Hnew : Z.of_nat (art_refill_n c) <= art_cls_new c cl).
    { unfold art_cls_new. apply Z.div_le_lower_bound; [lia|]. lia. }
    lia.
  - unfold art_cls_needs_populate in NP. apply Nat.ltb_ge in NP. exact NP.
Qed.

Lemma art_pre_take_cache : forall c cl, cl_cache (art_cls_pre_take c cl) = cl_cache cl.
Proof. intros c cl. unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl); reflexivity. Qed.

Lemma art_cls_ok_pre_take : forall c cl, 1 <= c <= 30 -> art_cls_ok c cl ->
  (art_cls_needs_populate c cl = true -> cl_mu cl + 262144 <= 3758096384 /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912) ->
  art_cls_ok c (art_cls_pre_take c cl).
Proof.
  intros c cl Hc OK Room. unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl) eqn:NP; [|exact OK].
  destruct (Room eq_refl) as (R1 & R2). apply art_cls_ok_populate; assumption.
Qed.

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_refill_tail :
  forall (Q : list aev -> machine_state -> Prop) (logE : list aev) regs rG (M MA MG rom : word -> option byte) (raw : word)
         (sp HI t spb ris qs c km : Z) (n : nat) (cl' : art_cls),
    let ca := t + 208 in
    let pcp := ca + 80 * c in
    ret_ok raw -> 1 <= c <= 30 -> HI <= sp - 672 -> sp < 2 ^ 47 ->
    spb = 65536 * qs -> 0x10007fff8000 <= spb -> ris = spb + 2 ^ 37 -> ris + 4096 <= HI -> 4096 <= t -> t + 4096 <= HI ->
    apart t 4096 spb (2 ^ 37 + 4096) -> apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000) -> 0 <= km -> 262144 * km <= 3758096384 ->
    length (cl_cache cl') = n -> (1 <= n <= 8)%nat -> 4 * Z.of_nat (length (cl_free cl')) <= 2 ^ 29 ->
    mem_grows M MA -> (forall x : word, ~ art_refill_fp sp t spb ris qs c km (U x) -> MA x = M x) ->
    mem_grows MA MG -> art_agree (art_gfa_fp (sp - 32) t spb ris qs c km) MA MG ->
    art_pc_hdr ca true MA ->
    cellA MA (sp - 8) 8 (U raw) -> cellA MA (sp - 16) 8 (U (getr regs 8)) -> cellA MA (sp - 24) 8 (U (getr regs 9)) -> wrA MA t 4096 ->
    art_region_rep spb ris c 0 cl' MG ->
    (forall j, (j < n)%nat -> cellA MG (ca + 80 * c + 16 + 4 * Z.of_nat j) 4 (nth j (cl_cache cl') 0)) ->
    getr rG 10 = Z_to_bv 64 1 -> getr rG 2 = Z_to_bv 64 (sp - 32) -> getr rG 8 = Z_to_bv 64 pcp -> getr rG 9 = Z_to_bv 64 (Z.of_nat n) ->
    (forall x : reg, In x [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rG x = getr regs x) ->
    (forall regs' (M' : word -> option byte),
        getr regs' 10 = Z_to_bv 64 1 -> getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
        (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
        mem_grows M M' -> (forall x : word, ~ art_refill_fp sp t spb ris qs c km (U x) -> M' x = M x) ->
        mem_grows MG M' -> art_agree [(pcp, 4)] MG M' ->
        art_pc_hdr ca true M' -> art_cls_rep ca spb ris c cl' M' ->
        Q logE (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q logE (mkst rG (0x574cc : word) MG rom).
Proof.
  intros Q logE regs rG M MA MG rom raw sp HI t spb ris qs c km n cl' ca pcp
         Hret Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Hkm Hkm' Lc Hn Hnf GA AAf GG AG PH F1 F8 F9 Wt RRG CH E10 E2 E8 E9 KG K.
  assert (Eca : ca = t + 208) by reflexivity. assert (Epcp : pcp = t + 208 + 80 * c) by reflexivity.
  assert (UB : forall w : word, 0 <= U w < 2 ^ 64). { intros w. pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
  unfold art_gfa_fp, art_pop_fp in AG.
  pose proof Atk as Xk. unfold apart in Xk. pose proof Ats as Xs. unfold apart in Xs.
  assert (TFR : forall a v, sp - 24 <= a -> a + 8 <= sp -> cellA MA a 8 v -> cellA MG a 8 v).
  { intros a v Ha Ha' C. apply (art_cell_tr1 _ MA MG _ _ _ AG); [|exact C]. clear - Ha Ha' HHI Hsp' Hris Eris Hspb Espb Hc Ht Ht' Hkm Hkm'. zarith_t. }
  pose proof (art_refill_b_fn rG MG rom raw sp pcp (Z.of_nat n) (U (getr regs 8)) (U (getr regs 9)) E2 E8 E9 E10
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret (UB _) (UB _) ltac:(unfold apart; lia)
                ltac:(eapply wr_grows; [exact GG|]; eapply wr_sub; [exact Wt|lia|lia])
                ltac:(apply TFR; [lia|lia|exact F1]) ltac:(apply TFR; [lia|lia|exact F8]) ltac:(apply TFR; [lia|lia|exact F9])) as RUNB.
  match type of RUNB with msteps _ _ (mkst ?R _ ?X _) => set (rB := R) in RUNB; set (MB := X) in RUNB end.
  eapply ar_steps; [exact RUNB|]. apply ar_done.
  assert (AB : art_agree [(pcp, 4)] MG MB). { unfold MB. eapply art_agree_sub; [zagree|]. zsub. }
  assert (GB : mem_grows MG MB) by (unfold MB; apply Wn_grows).
  apply (K rB MB).
  - unfold rB; gres. exact E10.
  - unfold rB; gres. reflexivity.
  - unfold rB; gres. reflexivity.
  - intros x Hx. cbn [In] in Hx.
    destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
      first [ unfold rB; gres; apply Z_to_bv_bv_unsigned | unfold rB; gres; apply KG; inl ].
  - eapply mem_grows_trans; [exact GA|]. eapply mem_grows_trans; [exact GG|exact GB].
  - intros x N. rewrite <- (AAf x N). unfold art_refill_fp in N.
    repeat match goal with H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H end.
    rewrite (AB x) by (cbn; split; [lia|exact I]). apply AG. cbn [art_out fst snd]. fold ca in Epcp. repeat split; lia.
  - exact GB.
  - exact AB.
  - intros c' Hc'. destruct (PH c' Hc') as [P1 P2]. fold ca in AG. split.
    + apply (art_cell_tr1 _ MG MB _ _ _ AB); [clear - Epcp Eca Hc Hc' Ht Ht' HHI Hsp'; zarith_t|].
      apply (art_cell_tr1 _ MA MG _ _ _ AG); [|exact P1]. clear - Epcp Eca Hc Hc' Xk Xs HHI Hsp' Hris Eris Hspb Espb Ht Ht' Hkm Hkm'. zarith_t.
    + apply (art_cell_tr1 _ MG MB _ _ _ AB); [clear - Epcp Eca Hc Hc' Ht Ht' HHI Hsp'; zarith_t|].
      apply (art_cell_tr1 _ MA MG _ _ _ AG); [|exact P2]. clear - Epcp Eca Hc Hc' Xk Xs HHI Hsp' Hris Eris Hspb Espb Ht Ht' Hkm Hkm'. zarith_t.
  - split.
    + split.
      * rewrite Lc. unfold MB. apply cell_Wn_hit; [lia|cbn; lia].
      * intros j Hj. rewrite Lc in Hj. apply (art_cell_tr1 _ MG MB _ _ _ AB); [|apply CH; exact Hj]. clear - Hj Hn Epcp Eca Hc Ht Ht' HHI Hsp'. zarith_t.
    + pose proof RRG as (Rmx & Rnf & _ & _ & _ & _ & _ & Rna & _).
      apply (art_region_rep_upd spb ris c 0 0 cl' cl' MG MB [(pcp, 4)]); try reflexivity;
        first [ lia | exact RRG | exact GB | exact AB | (intros; reflexivity) | idtac ].
      * clear - Epcp Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
      * clear - Epcp Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
      * clear - Epcp Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht' Hnf. zarith_t.
      * apply (art_cell_tr1 _ MG MB _ _ _ AB); [|exact Rmx]. clear - Epcp Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
      * apply (art_cell_tr1 _ MG MB _ _ _ AB); [|exact Rnf]. clear - Epcp Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
      * apply (art_cell_tr1 _ MG MB _ _ _ AB); [|exact Rna]. clear - Epcp Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_refill_prologue :
  forall regs (M rom : word -> option byte) (raw : word) (sp t c : Z) (inited : bool),
    let ca := t + 208 in
    getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ca -> getr regs 11 = Z_to_bv 64 (ca + 80 * c) ->
    getr regs 12 = Z_to_bv 64 1295832 -> getr regs 13 = Z_to_bv 64 c ->
    1 <= c <= 30 -> 0x696000 + 32 <= sp -> sp < 2 ^ 47 -> 4096 <= t -> t + 4096 + 208 <= sp - 32 ->
    wrA M (sp - 32) 32 -> wrA M t 4096 -> art_pc_hdr ca inited M -> cellA M (ca + 80 * c) 4 0 ->
    exists rA MA,
      msteps ASEGS (mkst regs (0x5748c : word) M rom) (mkst rA (0x5758c : word) MA rom)
      /\ getr rA 1 = (0x574cc : bv 64)%bv /\ getr rA 2 = Z_to_bv 64 (sp - 32) /\ getr rA 8 = Z_to_bv 64 (ca + 80 * c) /\ getr rA 9 = Z_to_bv 64 (Z.of_nat (art_refill_n c))
      /\ getr rA 10 = Z_to_bv 64 1295832 /\ getr rA 11 = Z_to_bv 64 (ca + 2560) /\ getr rA 12 = Z_to_bv 64 c /\ getr rA 13 = Z_to_bv 64 (ca + 80 * c + 16)
      /\ getr rA 14 = Z_to_bv 64 (Z.of_nat (art_refill_n c))
      /\ (forall x : reg, In x [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rA x = getr regs x)
      /\ mem_grows M MA /\ art_agree [(sp - 32, 32); (ca + 84, 2412)] M MA
      /\ (forall x : word, ~ (sp - 32 <= U x < sp) -> ~ art_pc_hdr_foot ca (U x) -> MA x = M x)
      /\ art_pc_hdr ca true MA /\ cellA MA (ca + 80 * c) 4 0
      /\ cellA MA (sp - 8) 8 (U raw) /\ cellA MA (sp - 16) 8 (U (getr regs 8)) /\ cellA MA (sp - 24) 8 (U (getr regs 9)).
Proof.
  intros regs M rom raw sp t c inited ca H1 H2 H10 H11 H12 H13 Hc IMG Hsp' Ht Hts W Wt PH C0.
  assert (Eca : ca = t + 208) by reflexivity.
  assert (Emc : art_ic_mc c / 2 = Z.of_nat (art_refill_n c)).
  { unfold art_refill_n. rewrite Z2Nat.id; [reflexivity|]. apply Z.div_pos; [pose proof (art_ic_mc_range c ltac:(lia)); lia|lia]. }
  set (MF := Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))).
  assert (AF : art_agree [(sp - 32, 32)] M MF). { unfold MF. eapply art_agree_sub; [zagree|]. zsub. }
  assert (GF : mem_grows M MF) by (unfold MF; zgrows).
  assert (FC : cellA MF (sp - 8) 8 (U raw) /\ cellA MF (sp - 16) 8 (U (getr regs 8)) /\ cellA MF (sp - 24) 8 (U (getr regs 9))).
  { unfold MF. repeat split; zcell. }
  destruct FC as (FC1 & FC8 & FC9).
  destruct inited.
  - (* [comment removed for export] *)
    destruct (PH c ltac:(lia)) as [Pmc _]. cbn in Pmc.
    pose proof (art_refill_a_fn regs M rom raw sp ca c 1295832 (art_ic_mc c) H1 H2 H10 H11 H12 H13 ltac:(lia) ltac:(lia) IMG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  (art_ic_mc_range c ltac:(lia)) ltac:(unfold apart; lia) W Pmc) as RUN.
    fold MF in RUN. match type of RUN with msteps _ _ (mkst ?R _ _ _) => set (rA := R) in RUN end.
    exists rA, MF. split; [exact RUN|].
    split; [unfold rA; gres; reflexivity|]. split; [unfold rA; gres; reflexivity|]. split; [unfold rA; gres; reflexivity|].
    split; [unfold rA; gres; rewrite Emc; reflexivity|]. split; [unfold rA; gres; reflexivity|]. split; [unfold rA; gres; reflexivity|].
    split; [unfold rA; gres; reflexivity|]. split; [unfold rA; gres; reflexivity|]. split; [unfold rA; gres; rewrite Emc; reflexivity|].
    split. { intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; (unfold rA; gres; reflexivity). }
    split; [exact GF|]. split; [eapply art_agree_sub; [exact AF|]; zsub|].
    split. { intros x N1 _. apply AF. cbn. split; [lia|exact I]. }
    split. { intros c' Hc'. destruct (PH c' Hc') as [P1 P2]. cbn in P1, P2. split; ztr. }
    split; [ztr|]. split; [exact FC1|]. split; [exact FC8|exact FC9].
  - (* [comment removed for export] *)
    destruct (PH c ltac:(lia)) as [Pmc _]. cbn in Pmc.
    destruct (art_refill_a_cold regs M rom raw sp ca c 1295832 H1 H2 H10 H11 H12 H13 ltac:(lia) ltac:(lia) IMG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold apart; lia) W ltac:(eapply wr_sub; [exact Wt|lia|lia]) Pmc)
      as (rA & RUN & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & KA).
    fold MF in RUN. set (MA := art_ic_mem MF ca 31) in *.
    assert (AI : art_agree [(ca + 84, 2412)] MF MA).
    { intros x Hx. cbn in Hx. destruct Hx as [Hx _]. unfold MA. apply art_ic_mem_outside; [lia|lia|lia|]. cbn. lia. }
    assert (GI : mem_grows MF MA) by apply art_ic_mem_grows.
    exists rA, MA. split; [exact RUN|].
    split; [exact A1|]. split; [exact A2|]. split; [exact A8|]. split; [rewrite A9, Emc; reflexivity|]. split; [exact A10|]. split; [exact A11|].
    split; [exact A12|]. split; [exact A13|]. split; [rewrite A14, Emc; reflexivity|]. split; [exact KA|].
    split; [eapply mem_grows_trans; [exact GF|exact GI]|].
    split; [exact (art_agree_trans _ _ _ _ _ AF AI)|].
    split. { intros x N1 N2. unfold MA. rewrite art_ic_mem_fine by (first [lia | exact N2]). apply AF. cbn. split; [lia|exact I]. }
    split; [apply art_pc_hdr_ic; lia|].
    split. { unfold MA. apply cell_ic_count; [lia|lia|lia|lia|]. ztr. }
    split; [ztr|]. split; ztr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem art_refill_rspec_holds : art_refill_rspec EVOK GR.
Proof.
  unfold art_refill_rspec.
  intros Q log regs M rom raw sp HI t ctx tp key tsd spb ris qs c km inited cl
         H1 Hret H2 H4 H10 H11 H12 H13 Hc HHI Hsp' GEO W Wt PC L T PH RC OK Ecache Emu ST Room EV K.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  clear G9 G10 G15 G16.
  destruct RC as [[CR0 _] RR]. rewrite Ecache in CR0. cbn in CR0.
  destruct ST as (m1 & m2 & sv & Cm1 & Cm2 & Csv).
  pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & _ & _).
  assert (Hkm : 0 <= km) by lia.
  set (n := art_refill_n c). set (ca := t + 208) in *. assert (Eca : ca = t + 208) by reflexivity.
  destruct (art_refill_need c Hc) as (_ & Hn). fold n in Hn.
  destruct (art_refill_prologue regs M rom raw sp t c inited H1 H2 H10 H11 H12 H13 Hc ltac:(lia) Hsp' G7 ltac:(lia)
              ltac:(eapply wr_sub; [exact W|lia|lia]) Wt PH CR0)
    as (rA & MA & RUNA & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & KA & GA & AA & AAf & PHA & CRA & F1 & F8 & F9).
  fold ca n in A8, A9, A11, A13, A14, AA, AAf, PHA, CRA.
  eapply ar_steps; [exact RUNA|].
  pose proof G11 as X11. unfold apart in X11. pose proof G18 as X18. unfold apart in X18. pose proof At_i as Xi. unfold apart in Xi.
  assert (PCA : art_prim_consts spb ris MA). { eapply art_prim_consts_fp; [exact AA| |exact PC]. intros z Hz. cbn. clear - Hz Xi Eca HHI G1 G7 G8. repeat split; lia. }
  assert (LA : art_layout MA). { eapply art_layout_fp; [exact AA| |exact L]. intros z Hz. cbn. clear - Hz Xi Eca HHI G1 G7 G8. repeat split; lia. }
  assert (TA : art_tsd MA tp key tsd ctx t).
  { eapply art_tsd_fp; [exact AA| | |exact G19|exact G20|exact G21|exact G22|exact T].
    - intros z Hz. cbn. clear - Hz Xi Eca HHI G1 G7 G8. repeat split; lia.
    - intros z Hz. cbn. clear - Hz X18 Eca HHI G1 G7 G8 G13 G14. repeat split; lia. }
  assert (RRA : art_region_rep spb ris c 0 cl MA).
  { pose proof RR as (Rmx & Rnf & _ & _ & _ & _ & _ & Rna & _).
    apply (art_region_rep_upd spb ris c 0 0 cl cl M MA [(sp - 32, 32); (ca + 84, 2412)]); try reflexivity;
      first [ lia | exact RR | exact GA | exact AA | (intros; reflexivity) | idtac ].
    - clear - X11 Eca HHI Hsp' G1 G2 G6 Eris G4 Espb Hc G7 G8. zarith_t.
    - clear - X11 Eca HHI Hsp' G1 G2 G6 Eris G4 Espb Hc G7 G8. zarith_t.
    - clear - X11 Eca HHI Hsp' G1 G2 G6 Eris G4 Espb Hc G7 G8 Hnf4 Hmfa1. zarith_t.
    - apply (art_cell_tr1 _ M MA _ _ _ AA); [|exact Rmx]. clear - X11 Eca HHI Hsp' G1 G2 G6 Eris G4 Espb Hc G7 G8. zarith_t.
    - apply (art_cell_tr1 _ M MA _ _ _ AA); [|exact Rnf]. clear - X11 Eca HHI Hsp' G1 G2 G6 Eris G4 Espb Hc G7 G8. zarith_t.
    - apply (art_cell_tr1 _ M MA _ _ _ AA); [|exact Rna]. clear - X11 Eca HHI Hsp' G1 G2 G6 Eris G4 Espb Hc G7 G8. zarith_t. }
  assert (OK1 : art_cls_ok c (art_cls_pre_take c cl)).
  { apply art_cls_ok_pre_take; [exact Hc|exact OK|]. intros NP. destruct (Room NP) as (R1 & R2 & _). split; assumption. }
  pose proof (art_pre_take_enough c cl Hc OK) as Hen. fold n in Hen.
  apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
  apply (art_gfa_aruns EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) log rA MA rom (0x574cc : bv 64)%bv (sp - 32) HI t ctx tp key tsd spb ris qs c km m1 m2 sv cl
           A1 ltac:(unfold ret_ok; bveq) A2 ltac:(rewrite KA by inl; exact H4) A10 ltac:(rewrite A11; f_equal; lia) A12 ltac:(rewrite A13; f_equal; lia) A14
           Hc ltac:(lia) ltac:(lia) GEO ltac:(eapply wr_grows; [exact GA|]; eapply wr_sub; [exact W|lia|lia]) ltac:(eapply wr_grows; [exact GA|exact Wt])
           PCA LA TA RRA OK Emu
           ltac:(apply (art_cell_tr1 _ M MA _ _ _ AA); [clear - Eca HHI Hsp' G2 G7 G8; zarith_t|exact Cm1])
           ltac:(apply (art_cell_tr1 _ M MA _ _ _ AA); [clear - Eca HHI Hsp' G2 G7 G8; zarith_t|exact Cm2])
           ltac:(replace (t + 2792) with (ca + 2584) by lia; apply (art_cell_tr1 _ M MA _ _ _ AA); [clear - Eca HHI Hsp' G2 G7 G8; zarith_t|exact Csv])
           ltac:(intros NP; destruct (Room NP) as (R1 & R2 & R3 & R4); repeat split; first [assumption | eapply wr_grows; [exact GA|assumption]]) EV).
  intros rG MG Q10 Q2 Q1' QK QG QA QRR QCH QSH QST.
  assert (Lc : length (cl_cache (art_cls_refill c cl)) = n).
  { rewrite art_cls_refill_eq. fold n. cbn [art_cls_take cl_cache]. rewrite length_skipn. lia. }
  pose proof OK1 as (_ & _ & _ & _ & _ & _ & _ & (_ & Hmfa11) & Hnf41 & _ & _).
  assert (Hnf' : 4 * Z.of_nat (length (cl_free (art_cls_refill c cl))) <= 2 ^ 29).
  { rewrite art_cls_refill_eq. fold n. cbn [art_cls_take cl_free]. rewrite length_firstn. lia. }
  apply (art_refill_tail Q (log ++ art_refill_events spb c cl) regs rG M MA MG rom raw sp HI t spb ris qs c km n (art_cls_refill c cl)
           Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 At_s Hkm ltac:(lia) Lc Hn Hnf' GA).
  - intros x N. apply AAf.
    + intros H. apply N. unfold art_refill_fp. left. lia.
    + intros H. apply N. unfold art_refill_fp. right. right. left. exact H.
  - exact QG.
  - exact QA.
  - exact PHA.
  - exact F1.
  - exact F8.
  - exact F9.
  - eapply wr_grows; [exact GA|exact Wt].
  - exact QRR.
  - intros j Hj. pose proof (QCH j Hj) as C. fold ca. replace (ca + 80 * c + 16 + 4 * Z.of_nat j) with (t + 208 + 80 * c + 16 + 4 * Z.of_nat j) by lia. exact C.
  - exact Q10.
  - exact Q2.
  - rewrite QK by inl. exact A8.
  - rewrite QK by inl. exact A9.
  - intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; (rewrite QK by inl; apply KA; inl).
  - intros regs' M' P10 P2 P1 PK PG PAf PGG PAB PPH PCR.
    apply (K regs' M' P10 P2 P1 PK PG PAf PPH PCR).
    + rewrite art_cls_refill_eq. apply art_cls_ok_take; [exact OK1|rewrite art_pre_take_cache; exact Ecache|exact Hen|lia].
    + intros NP j Hj. pose proof (QSH NP j Hj) as C. pose proof At_s as Xs. unfold apart in Xs.
      apply (art_cell_tr1 _ MG M' _ _ _ PAB); [|exact C]. clear - Hj Xs Eca Hc G4 Espb Hkm Emu Hmu3 G6 Eris G2 G7 G8. zarith_t.
Qed.
End Spec.
