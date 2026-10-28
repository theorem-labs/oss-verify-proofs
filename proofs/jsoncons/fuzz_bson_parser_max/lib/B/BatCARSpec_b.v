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
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatInitCache_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatClassId_b BatCachePop_b BatCombAlloc_b BatCombAllocHit_b BatRefill3_b BatPopulate1_b
     BatCls_b BatFp_b BatClsPop3_b BatClsRep_b BatClsGfa2_b BatClsRefill_b BatCellEx_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_ca_pre (c : Z) (cl : art_cls) : art_cls := match cl_cache cl with [] => art_cls_refill c cl | _ :: _ => cl end.
Definition art_ca_events (spb c : Z) (cl : art_cls) : list aev := match cl_cache cl with [] => art_refill_events spb c cl | _ :: _ => [] end.
Definition art_cls_pop (cl : art_cls) : art_cls := CLS (removelast (cl_cache cl)) (cl_free cl) (cl_au cl) (cl_mu cl) (cl_mfa cl) (cl_na cl) (cl_nfr cl).
Definition art_ca_cptr (c : Z) (cl : art_cls) : Z := last (cl_cache (art_ca_pre c cl)) 0.
Definition art_ca_result (spb c : Z) (cl : art_cls) : Z := spb + c * 2 ^ 32 + art_ca_cptr c cl * 16.
(* [comment removed for export] *)
Definition art_ca_fp (sp t spb ris qs c km : Z) (x : Z) : Prop :=
  (sp - 48 <= x < sp) \/ art_refill_fp (sp - 48) t spb ris qs c km x \/ (t + 208 + 2576 <= x < t + 208 + 2584).

(* [comment removed for export] *)
Lemma art_removelast_length : forall (l : list Z), l <> [] -> length (removelast l) = (length l - 1)%nat.
Proof. intros l H. rewrite removelast_firstn_len. rewrite length_firstn. lia. Qed.
Lemma art_removelast_nth : forall (l : list Z) j, (j < length l - 1)%nat -> nth j (removelast l) 0 = nth j l 0.
Proof. intros l j Hj. rewrite removelast_firstn_len, nth_firstn. replace (j <? Nat.pred (length l))%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. Qed.
Lemma art_last_nth : forall (l : list Z), last l 0 = nth (length l - 1) l 0.
Proof.
  induction l as [|a l IH]; [reflexivity|]. destruct l as [|b l]; [reflexivity|].
  change (last (a :: b :: l) 0) with (last (b :: l) 0). rewrite IH. cbn [length]. rewrite !Nat.sub_succ, !Nat.sub_0_r. reflexivity.
Qed.

Lemma art_cls_ok_pop : forall c cl, art_cls_ok c cl -> cl_cache cl <> [] -> art_cls_ok c (art_cls_pop cl).
Proof.
  intros c cl OK Hne.
  destruct OK as (Hlc & Hau & Hrem0 & Hmu & Hau' & Hmu3 & Hmfa & Hmfa' & Hnf4 & Hfor & Hnd).
  unfold art_cls_ok, art_cls_pop. cbn [cl_cache cl_free cl_au cl_mu cl_mfa].
  assert (E : cl_cache cl = removelast (cl_cache cl) ++ [last (cl_cache cl) 0]) by (apply app_removelast_last; exact Hne).
  split; [rewrite art_removelast_length by exact Hne; lia|]. split; [exact Hau|]. split; [exact Hrem0|]. split; [exact Hmu|]. split; [exact Hau'|]. split; [exact Hmu3|].
  split; [exact Hmfa|]. split; [exact Hmfa'|]. split; [exact Hnf4|].
  rewrite E in Hfor, Hnd. rewrite <- app_assoc in Hfor, Hnd.
  split.
  - apply Forall_app in Hfor. destruct Hfor as [F1 F2]. apply Forall_app in F2. destruct F2 as [_ F3]. apply Forall_app. split; assumption.
  - apply NoDup_ListNoDup. apply NoDup_ListNoDup in Hnd. cbn [app] in Hnd. eapply NoDup_remove_1. exact Hnd.
Qed.

Lemma art_ca_pre_cache_ne : forall c cl, 1 <= c <= 30 -> art_cls_ok c cl -> cl_cache (art_ca_pre c cl) <> [].
Proof.
  intros c cl Hc OK. unfold art_ca_pre. destruct (cl_cache cl) eqn:E; [|rewrite E; discriminate].
  rewrite art_cls_refill_eq. cbn [art_cls_take cl_cache]. pose proof (art_pre_take_enough c cl Hc OK) as Hen.
  destruct (art_refill_need c Hc) as (_ & Hn). intros H. apply (f_equal (@length Z)) in H. rewrite length_skipn in H. cbn in H. lia.
Qed.

(* [comment removed for export] *)
Lemma art_cache_rep_tr : forall W ca c cache M M', 0 <= ca -> ca + 4096 < 2 ^ 64 -> 1 <= c <= 31 -> (length cache <= 16)%nat ->
  art_agree W M M' -> art_gap W (ca + 80 * c) 4 -> art_gap W (ca + 80 * c + 16) 64 -> art_cache_rep ca c cache M -> art_cache_rep ca c cache M'.
Proof.
  intros W ca c cache M M' Hca Hca' Hc Hl A G0 G16 [C0 CW]. split.
  - apply (art_cell_tr W M M'); [exact A|exact G0|lia|cbn; lia|exact C0].
  - intros j Hj. apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G16|lia|cbn; lia]|lia|cbn; lia|exact (CW j Hj)].
Qed.
Lemma art_pc_hdr_tr : forall W ca b M M', 0 <= ca -> ca + 4096 < 2 ^ 64 -> art_agree W M M' ->
  (forall c, 1 <= c <= 31 -> art_gap W (ca + 80 * c + 4) 12) -> art_pc_hdr ca b M -> art_pc_hdr ca b M'.
Proof.
  intros W ca b M M' Hca Hca' A G PH c Hc. destruct (PH c Hc) as [P1 P2]. split.
  - apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact (G c Hc)|lia|cbn; lia]|lia|cbn; lia|exact P1].
  - apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact (G c Hc)|lia|cbn; lia]|lia|cbn; lia|exact P2].
Qed.

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition art_ca_rspec : Prop :=
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
         (sp HI t ctx tp key tsd spb ris qs s km : Z) (inited : bool) (cl : art_cls),
    let c := AsanTab.class_id s in
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp ->
    getr regs 10 = Z_to_bv 64 1295832 -> getr regs 11 = Z_to_bv 64 (t + 208) -> getr regs 12 = Z_to_bv 64 s -> getr regs 13 = Z_to_bv 64 8 ->
    1 <= s <= 65536 -> s mod 8 = 0 -> HI <= sp - 720 -> sp < 2 ^ 47 -> art_geo HI t ctx tp tsd spb ris qs ->
    wrA M (sp - 720) 720 -> wrA M t 4096 ->
    art_prim_consts spb ris M -> art_layout M -> art_tsd M tp key tsd ctx t ->
    art_pc_hdr (t + 208) inited M -> art_cls_rep (t + 208) spb ris c cl M -> art_cls_ok c cl -> (cl_cache cl <> [] -> inited = true) -> cl_mu cl = 262144 * km ->
    (cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
       cl_mu cl + 262144 <= 3758096384
       /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912
       /\ wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km) 32768
       /\ wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048) 67108864) ->
    art_evok_list EVOK log (art_ca_events spb c cl) ->
    (forall regs' (M' : word -> option byte),
        getr regs' 10 = Z_to_bv 64 (art_ca_result spb c cl) -> getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
        mem_grows M M' ->
        (forall x : word, ~ art_ca_fp sp t spb ris qs c km (U x) -> M' x = M x) ->
        art_pc_hdr (t + 208) true M' -> art_cls_rep (t + 208) spb ris c (art_cls_pop (art_ca_pre c cl)) M' -> art_cls_ok c (art_cls_pop (art_ca_pre c cl)) ->
        art_cptr_ok (AsanTab.class_size c) (cl_au (art_ca_pre c cl)) (art_ca_cptr c cl) ->
        (cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
           forall j, 0 <= j < 32768 -> cellA M' (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + j) 1 250) ->
        Q (log ++ art_ca_events spb c cl) (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x56d3c : word) M rom).

(* [comment removed for export] *)
#[using="Type"] Lemma art_ca_finish :
  forall (Q : list aev -> machine_state -> Prop) (logE : list aev) regs rP (M MX rom : word -> option byte) (raw : word)
         (sp HI t spb ris qs c km st res : Z) (clp : art_cls),
    let ca := t + 208 in
    let cnt := Z.of_nat (length (cl_cache clp)) in
    ret_ok raw -> 1 <= c <= 30 -> HI <= sp - 720 -> sp < 2 ^ 47 ->
    spb = 65536 * qs -> 0x10007fff8000 <= spb -> ris = spb + 2 ^ 37 -> ris + 4096 <= HI -> 4096 <= t -> t + 4096 <= HI ->
    apart t 4096 spb (2 ^ 37 + 4096) ->
    cl_cache clp <> [] -> (length (cl_cache clp) <= 16)%nat -> 4 * Z.of_nat (length (cl_free clp)) <= 2 ^ 29 ->
    mem_grows M MX -> (forall x : word, ~ art_ca_fp sp t spb ris qs c km (U x) -> MX x = M x) ->
    art_pc_hdr ca true MX -> art_cls_rep ca spb ris c clp MX ->
    cellA MX (sp - 8) 8 (U raw) -> cellA MX (sp - 16) 8 (U (getr regs 8)) -> cellA MX (sp - 24) 8 (U (getr regs 9)) -> cellA MX (sp - 32) 8 (U (getr regs 18)) ->
    cellA MX (sp - 40) 8 (U (getr regs 19)) -> cellA MX (sp - 48) 8 (U (getr regs 20)) ->
    getr rP 13 = Z_to_bv 64 8 -> getr rP 2 = Z_to_bv 64 (sp - 48) -> getr rP 10 = Z_to_bv 64 res ->
    (forall x : reg, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rP x = getr regs x) ->
    (forall regs' (M' : word -> option byte),
        getr regs' 10 = Z_to_bv 64 res -> getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
        mem_grows M M' ->
        (forall x : word, ~ art_ca_fp sp t spb ris qs c km (U x) -> M' x = M x) ->
        mem_grows MX M' -> art_agree [(ca + 80 * c, 4); (ca + 2576, 8)] MX M' ->
        art_pc_hdr ca true M' -> art_cls_rep ca spb ris c (art_cls_pop clp) M' ->
        Q logE (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q logE (mkst rP (0x56f2c : word) (Wn 8 (Wn 4 MX (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + art_ic_size c)) rom).
Proof.
  intros Q logE regs rP M MX rom raw sp HI t spb ris qs c km st res clp ca cnt
         Hret Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Hne Hl16 Hnf GX AXf PH CR F1 F8 F9 F18 F19 F20 P13 P2 P10 KP K.
  assert (Eca : ca = t + 208) by reflexivity.
  pose proof Atk as Xk. unfold apart in Xk.
  assert (Hcnt : 1 <= cnt <= 16). { unfold cnt. destruct (cl_cache clp); [contradiction|]. cbn [length] in *. lia. }
  set (M2 := Wn 8 (Wn 4 MX (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + art_ic_size c)).
  assert (A2 : art_agree [(ca + 80 * c, 4); (ca + 2576, 8)] MX M2). { unfold M2. eapply art_agree_sub; [zagree|]. zsub. }
  assert (G2 : mem_grows MX M2) by (unfold M2; zgrows).
  assert (TF : forall a v, sp - 48 <= a -> a + 8 <= sp -> cellA MX a 8 v -> cellA M2 a 8 v).
  { intros a v Ha Ha' C. apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact C]. clear - Ha Ha' Eca HHI Hsp' Ht Ht' Hc. zarith_t. }
  destruct (art_cache_pop_tail8 rP M2 rom (sp - 48) raw (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))
              P13 P2 ltac:(lia) ltac:(lia)
              ltac:(replace (sp - 48 + 40) with (sp - 8) by lia; apply TF; [lia|lia|exact F1]) Hret
              ltac:(replace (sp - 48 + 32) with (sp - 16) by lia; apply TF; [lia|lia|exact F8])
              ltac:(replace (sp - 48 + 24) with (sp - 24) by lia; apply TF; [lia|lia|exact F9])
              ltac:(replace (sp - 48 + 16) with (sp - 32) by lia; apply TF; [lia|lia|exact F18])
              ltac:(replace (sp - 48 + 8) with (sp - 40) by lia; apply TF; [lia|lia|exact F19])
              ltac:(apply TF; [lia|lia|exact F20]))
    as (rT & RUNT & T10 & T2 & T1 & T8 & T9 & T18 & T19 & T20 & KT).
  eapply ar_steps; [exact RUNT|]. apply ar_done.
  destruct CR as [[C0 CW] RR].
  apply (K rT M2).
  - rewrite T10. exact P10.
  - rewrite T2. f_equal. lia.
  - exact T1.
  - intros x Hx. cbn [In] in Hx.
    destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
      first [ rewrite T8; apply Z_to_bv_bv_unsigned | rewrite T9; apply Z_to_bv_bv_unsigned | rewrite T18; apply Z_to_bv_bv_unsigned
            | rewrite T19; apply Z_to_bv_bv_unsigned | rewrite T20; apply Z_to_bv_bv_unsigned
            | rewrite KT by (unfold art_pop_kept; repeat split; intros E; discriminate E); apply KP; inl ].
  - eapply mem_grows_trans; [exact GX|exact G2].
  - intros x N. rewrite <- (AXf x N). apply A2. unfold art_ca_fp, art_refill_fp in N.
    repeat match goal with H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H end.
    cbn [art_out fst snd]. repeat split; lia.
  - exact G2.
  - exact A2.
  - apply (art_pc_hdr_tr _ ca true MX M2 ltac:(lia) ltac:(lia) A2); [|exact PH]. intros c' Hc'. clear - Hc Hc' Eca Ht Ht' HHI Hsp'. zarith_t.
  - split.
    + split.
      * cbn [art_cls_pop cl_cache]. rewrite art_removelast_length by exact Hne.
        replace (Z.of_nat (length (cl_cache clp) - 1)) with (cnt - 1) by (unfold cnt; lia). unfold M2.
        apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; [lia|cbn; lia].
      * cbn [art_cls_pop cl_cache]. intros j Hj. rewrite art_removelast_length in Hj by exact Hne. rewrite art_removelast_nth by exact Hj.
        apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|apply CW; lia]. clear - Hj Hl16 Hc Eca Ht Ht' HHI Hsp'. zarith_t.
    + pose proof RR as (Rmx & Rnf & _ & _ & _ & _ & _ & Rna & _).
      apply (art_region_rep_upd spb ris c 0 0 clp (art_cls_pop clp) MX M2 [(ca + 80 * c, 4); (ca + 2576, 8)]); try reflexivity;
        first [ lia | exact RR | exact G2 | exact A2 | (intros; reflexivity) | idtac ].
      * clear - Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
      * clear - Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
      * cbn [art_cls_pop cl_free]. clear - Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht' Hnf. zarith_t.
      * apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact Rmx]. clear - Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
      * apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact Rnf]. clear - Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
      * apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact Rna]. clear - Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_tcell_exists : forall (M : word -> option byte) t d, apart t 4096 0x10000 (0x696000 - 0x10000) -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= d -> d + 8 <= 4096 ->
  wrA M t 4096 -> exists v, 0 <= v < 2 ^ 64 /\ cellA M (t + d) 8 v.
Proof.
  intros M t d A Ht Ht' Hd Hd' W. unfold apart in A.
  apply (art_cell_exists M (t + d) 8 ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)). cbn. eapply wr_sub; [exact W|lia|lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_refill_fp_out_frame : forall sp HI t spb ris qs c km x, 1 <= c <= 30 -> HI <= sp - 720 -> spb = 65536 * qs -> 0x10007fff8000 <= spb -> ris = spb + 2 ^ 37 -> ris + 4096 <= HI ->
  4096 <= t -> t + 4096 <= HI -> 0 <= km -> 262144 * km <= 3758096384 -> sp - 48 <= x < sp -> ~ art_refill_fp (sp - 48) t spb ris qs c km x.
Proof.
  intros sp HI t spb ris qs c km x Hc HHI Espb Hspb Eris Hris Ht Ht' Hkm Hkm' Hx F. unfold art_refill_fp in F.
  destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]; try lia. destruct F as (c' & Hc' & F). lia.
Qed.
#[using="Type"] Lemma art_refill_fp_out_stat : forall sp HI t spb ris qs c km x, 1 <= c <= 30 -> HI <= sp - 720 -> sp < 2 ^ 47 -> spb = 65536 * qs -> 0x10007fff8000 <= spb -> ris = spb + 2 ^ 37 -> ris + 4096 <= HI ->
  4096 <= t -> t + 4096 <= HI -> apart t 4096 spb (2 ^ 37 + 4096) -> apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000) -> 0 <= km -> 262144 * km <= 3758096384 ->
  t + 208 + 2576 <= x < t + 208 + 2584 -> ~ art_refill_fp (sp - 48) t spb ris qs c km x.
Proof.
  intros sp HI t spb ris qs c km x Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Hkm Hkm' Hx F. unfold art_refill_fp in F. unfold apart in Atk, Ats.
  destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]; try lia. destruct F as (c' & Hc' & F). lia.
Qed.

#[using="Type"] Lemma art_refill_fp_out_img : forall sp HI t spb ris qs c km x, 1 <= c <= 30 -> HI <= sp - 720 -> 0x10007fff8000 <= HI -> spb = 65536 * qs -> 0x10007fff8000 <= spb -> ris = spb + 2 ^ 37 ->
  4096 <= t -> apart t 4096 0x10000 (0x696000 - 0x10000) -> 0 <= km -> 0x10000 <= x < 0x696000 -> ~ art_refill_fp (sp - 48) t spb ris qs c km x.
Proof.
  intros sp HI t spb ris qs c km x Hc HHI HHI' Espb Hspb Eris Ht Ati Hkm Hx F. unfold art_refill_fp in F. unfold apart in Ati.
  destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]; try lia. destruct F as (c' & Hc' & F). lia.
Qed.

#[using="Type"] Theorem art_ca_rspec_holds : art_ca_rspec.
Proof.
  unfold art_ca_rspec.
  intros Q log regs M rom raw sp HI t ctx tp key tsd spb ris qs s km inited cl
         H1 Hret H2 H4 H10 H11 H12 H13 Hs Hs8 HHI Hsp' GEO W Wt PC L T PH RC OK Hin Emu Room EV K.
  set (c := AsanTab.class_id s) in *.
  pose proof (AsanTab.class_id_ok s Hs) as (Hc & _ & _). fold c in Hc.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  clear G9 G10 G15 G16.
  pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _).
  assert (Hkm : 0 <= km) by lia.
  set (ca := t + 208) in *. assert (Eca : ca = t + 208) by reflexivity.
  pose proof G11 as X11. unfold apart in X11. pose proof G18 as X18. unfold apart in X18. pose proof At_i as Xi. unfold apart in Xi.
  (* [comment removed for export] *)
  destruct (art_ca_entry8 regs M rom sp s H2 H12 H13 ltac:(lia) ltac:(lia) Hs ltac:(eapply wr_sub; [exact W|lia|lia])) as (r1 & RUN1 & Q2 & Q14 & Q12 & Q15 & K1).
  set (M1 := art_ca_frame M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))) in *.
  assert (A1 : art_agree [(sp - 48, 48)] M M1). { unfold M1, art_ca_frame. eapply art_agree_sub; [zagree|]. zsub. }
  assert (G1' : mem_grows M M1) by (unfold M1, art_ca_frame; zgrows).
  assert (FC : cellA M1 (sp - 8) 8 (U raw) /\ cellA M1 (sp - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 24) 8 (U (getr regs 9)) /\ cellA M1 (sp - 32) 8 (U (getr regs 18))
               /\ cellA M1 (sp - 40) 8 (U (getr regs 19)) /\ cellA M1 (sp - 48) 8 (U (getr regs 20))).
  { rewrite <- H1. unfold M1, art_ca_frame. repeat split; zcell. }
  destruct FC as (FC1 & FC8 & FC9 & FC18 & FC19 & FC20).
  assert (STEP2 : exists r2, msteps ASEGS (mkst r1 (0x56dc0 : word) M1 rom) (mkst r2 (0x56ed0 : word) M1 rom)
            /\ getr r2 8 = Z_to_bv 64 c
            /\ (forall rg : reg, rg <> 8%bv -> rg <> 12%bv -> rg <> 14%bv -> rg <> 15%bv -> rg <> 16%bv -> rg <> 17%bv -> rg <> 5%bv -> rg <> 6%bv ->
                  getr r2 rg = getr r1 rg)).
  { destruct (Z.le_gt_cases s 512) as [Hsm|Hbg].
    - destruct (art_ca_small r1 M1 rom s Q14 Q12 ltac:(lia)) as (r2 & RUN2 & P8 & _ & K2).
      exists r2. split; [exact RUN2|]. split.
      + rewrite P8. unfold c. rewrite class_id_small by lia. reflexivity.
      + intros rg N8 N12 N14 N15 N16 N17 N5 N6. apply K2; assumption.
    - pose proof (art_ca_big r1 M1 rom s Q14 Q12 ltac:(lia)) as RUN2a.
      destruct (art_classid_hi_run r1 M1 rom (Z_to_bv 64 s) Q14) as (r2 & RUN2b & P8 & K2).
      exists r2. split; [eapply msteps_trans; [exact RUN2a | exact RUN2b]|]. split.
      + rewrite P8. rewrite art_cid_w_ok by lia. reflexivity.
      + intros rg N8 N12 N14 N15 N16 N17 N5 N6. apply K2. unfold art_cid_kept. repeat split; assumption. }
  destruct STEP2 as (r2 & RUN2 & P8 & K2).
  assert (KR2 : forall rg : reg, In rg [1; 3; 4; 10; 11; 13; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 rg = getr regs rg).
  { intros rg Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]];
      (rewrite K2 by (intros E; discriminate E); apply K1; unfold art_ca_entry_kept; repeat split; intros E; discriminate E). }
  assert (R2_2 : getr r2 2 = Z_to_bv 64 (sp - 48)) by (rewrite K2 by (intros E; discriminate E); exact Q2).
  eapply ar_steps; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
  (* [comment removed for export] *)
  destruct RC as [CR RR].
  assert (PH1 : art_pc_hdr ca inited M1).
  { apply (art_pc_hdr_tr _ ca inited M M1 ltac:(lia) ltac:(lia) A1); [|exact PH]. intros c' Hc'. clear - Hc' Eca HHI G7 G8. zarith_t. }
  assert (CR1 : art_cache_rep ca c (cl_cache cl) M1).
  { apply (art_cache_rep_tr _ ca c (cl_cache cl) M M1 ltac:(lia) ltac:(lia) ltac:(lia) Hl16 A1); [| |exact CR]; clear - Hc Eca HHI G7 G8; zarith_t. }
  assert (RR1 : art_region_rep spb ris c 0 cl M1).
  { pose proof RR as (Rmx & Rnf & _ & _ & _ & _ & _ & Rna & _).
    apply (art_region_rep_upd spb ris c 0 0 cl cl M M1 [(sp - 48, 48)]); try reflexivity;
      first [ lia | exact RR | exact G1' | exact A1 | (intros; reflexivity) | idtac ].
    - clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hc. zarith_t.
    - clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hc. zarith_t.
    - clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hc Hnf4 Hmfa1. zarith_t.
    - apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact Rmx]. clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hc. zarith_t.
    - apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact Rnf]. clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hc. zarith_t.
    - apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact Rna]. clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hc. zarith_t. }
  assert (PC1 : art_prim_consts spb ris M1). { eapply art_prim_consts_fp; [exact A1| |exact PC]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
  assert (Wt1 : wrA M1 t 4096) by (eapply wr_grows; [exact G1'|exact Wt]).
  assert (Hcase : cl_cache cl = [] \/ cl_cache cl <> []) by (destruct (cl_cache cl); [left; reflexivity|right; discriminate]).
  assert (Xi' : forall d, 0 <= d -> d + 8 <= 4096 -> apart (t + d) 8 (1295832 + 32) 8) by (intros d Hd Hd'; unfold apart; clear - Xi Hd Hd'; lia).
  destruct Hcase as [Ecache|Hne].
  - (* [comment removed for export] *)
    assert (Epre : art_ca_pre c cl = art_cls_refill c cl) by (unfold art_ca_pre; rewrite Ecache; reflexivity).
    assert (Eev : art_ca_events spb c cl = art_refill_events spb c cl) by (unfold art_ca_events; rewrite Ecache; reflexivity).
    rewrite Eev in EV, K. unfold art_ca_result, art_ca_cptr in K. rewrite Epre in K.
    pose proof CR1 as [C0 _]. rewrite Ecache in C0. cbn in C0.
    pose proof (art_miss_a_fn r2 M1 rom c ca 1295832 8 P8 ltac:(rewrite KR2 by inl; exact H10) ltac:(rewrite KR2 by inl; exact H11) ltac:(rewrite KR2 by inl; exact H13)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) C0) as RUN3.
    match type of RUN3 with msteps _ _ (mkst ?R _ _ _) => set (r3 := R) in RUN3 end.
    eapply ar_steps; [exact RUN3|].
    assert (L1 : art_layout M1). { eapply art_layout_fp; [exact A1| |exact L]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
    assert (T1 : art_tsd M1 tp key tsd ctx t).
    { eapply art_tsd_fp; [exact A1| | |exact G19|exact G20|exact G21|exact G22|exact T].
      - intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia.
      - intros z Hz. cbn. clear - Hz HHI G1 G13 G14. repeat split; lia. }
    destruct (art_tcell_exists M1 t 2872 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (m1 & _ & Cm1).
    destruct (art_tcell_exists M1 t 2880 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (m2 & _ & Cm2).
    destruct (art_tcell_exists M1 t 2792 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (sv & _ & Csv).
    apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
    apply (art_refill_rspec_holds EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) log r3 M1 rom (0x56fec : bv 64)%bv (sp - 48) HI t ctx tp key tsd spb ris qs c km inited cl
             ltac:(unfold r3; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold r3; gres; exact R2_2) ltac:(unfold r3; gres; rewrite KR2 by inl; exact H4)
             ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity)
             Hc ltac:(lia) ltac:(lia) GEO ltac:(eapply wr_grows; [exact G1'|]; eapply wr_sub; [exact W|lia|lia]) Wt1 PC1 L1 T1 PH1 (conj CR1 RR1) OK Ecache Emu
             ltac:(exists m1, m2, sv; repeat split; [exact Cm1|exact Cm2|replace (t + 208 + 2584) with (t + 2792) by lia; exact Csv])
             ltac:(intros NP; destruct (Room Ecache NP) as (R1 & R2 & R3 & R4); repeat split; first [assumption | eapply wr_grows; [exact G1'|assumption]]) EV).
    intros rR MR R10 R2 R1 RK RG RA RPH RCR ROK RSH.
    set (clr := art_cls_refill c cl) in *. set (n := art_refill_n c).
    destruct (art_refill_need c Hc) as (_ & Hn). fold n in Hn.
    pose proof (art_pre_take_enough c cl Hc OK) as Hen. fold n in Hen.
    assert (Lc : length (cl_cache clr) = n). { unfold clr. rewrite art_cls_refill_eq. fold n. cbn [art_cls_take cl_cache]. rewrite length_skipn. lia. }
    assert (Hne' : cl_cache clr <> []). { intros E. rewrite E in Lc. cbn in Lc. lia. }
    pose proof ROK as (_ & (Hau0r & Haumur) & _ & _ & _ & Hmu3r & _ & (_ & Hmfa1r) & Hnf4r & Hforr & _).
    pose proof RCR as [[D0 DW] DRR]. rewrite Lc in D0.
    assert (WtR : wrA MR t 4096) by (eapply wr_grows; [exact RG|exact Wt1]).
    pose proof (art_miss_b_fn rR MR rom (ca + 80 * c) (Z.of_nat n) 8 ca 1295832 R10
                  ltac:(rewrite RK by inl; unfold r3; gres; reflexivity) ltac:(rewrite RK by inl; unfold r3; gres; reflexivity)
                  ltac:(rewrite RK by inl; unfold r3; gres; reflexivity) ltac:(rewrite RK by inl; unfold r3; gres; reflexivity)
                  ltac:(lia) ltac:(lia) ltac:(lia) D0) as RUN4.
    match type of RUN4 with msteps _ _ (mkst ?R _ _ _) => set (r4 := R) in RUN4 end.
    destruct (art_tcell_exists MR t 2784 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) WtR) as (st & Hst & Cst).
    destruct (RPH c ltac:(lia)) as [_ Pcsz]. cbn in Pcsz.
    assert (PspbR : cellA MR (1295832 + 32) 8 spb).
    { destruct PC1 as (Pspb & _). apply (art_cell_agree _ M1 MR); [|lia|cbn; lia|exact Pspb]. intros x Hx. apply RA.
      apply (art_refill_fp_out_img sp HI t spb ris qs c km (U x) Hc HHI G1 Espb G4 Eris G7 At_i Hkm). cbn in Hx. lia. }
    assert (Hch : art_cptr_ok (AsanTab.class_size c) (cl_au clr) (last (cl_cache clr) 0)).
    { apply (proj1 (Forall_forall _ _) Hforr). apply in_or_app. left. rewrite (app_removelast_last 0 Hne') at 2. apply in_or_app. right. left. reflexivity. }
    pose proof (art_class_size_facts c Hc) as (Hsz & _).
    pose proof (art_cptr_lt (AsanTab.class_size c) (cl_au clr) (last (cl_cache clr) 0) ltac:(lia) ltac:(lia) Hch) as Hch'.
    destruct (art_cache_pop50 r4 MR rom c ca 1295832 (Z.of_nat n) (art_ic_size c) (last (cl_cache clr) 0) st spb
                ltac:(unfold r4; gres; rewrite RK by inl; unfold r3; gres; exact P8) ltac:(unfold r4; gres; rewrite RK by inl; unfold r3; gres; reflexivity)
                ltac:(unfold r4; gres; reflexivity) ltac:(unfold r4; gres; reflexivity) ltac:(unfold r4; gres; reflexivity)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Eca, Et; replace (4096 * qt + 208) with ((512 * qt + 26) * 8) by lia; apply Z_mod_mult) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(pose proof (art_ic_size_pos c ltac:(lia)); lia) ltac:(lia) Hst ltac:(lia)
                Pcsz ltac:(rewrite art_last_nth, Lc; replace (ca + 80 * c + 16 + 4 * (Z.of_nat n - 1)) with (ca + 80 * c + 16 + 4 * Z.of_nat (n - 1)) by lia; apply DW; lia)
                ltac:(replace (ca + 2576) with (t + 2784) by lia; exact Cst) PspbR
                ltac:(eapply (wr_wok _ _ _ _ WtR); [lia|cbn; lia]) ltac:(eapply (wr_wok _ _ _ _ WtR); [lia|cbn; lia])
                ltac:(replace (ca + 80 * c) with (t + (208 + 80 * c)) by lia; pose proof (Xi' (208 + 80 * c) ltac:(lia) ltac:(lia)) as X; unfold apart in X |- *; lia)
                ltac:(replace (ca + 2576) with (t + 2784) by lia; apply Xi'; lia))
      as (rP & RUNP & P10 & KP).
    eapply ar_steps; [eapply msteps_trans; [exact RUN4|exact RUNP]|].
    assert (TFR : forall a v, sp - 48 <= a -> a + 8 <= sp -> cellA M1 a 8 v -> cellA MR a 8 v).
    { intros a v Ha Ha' C. apply (art_cell_agree _ M1 MR); [|lia|cbn; lia|exact C]. intros x Hx. apply RA.
      apply (art_refill_fp_out_frame sp HI t spb ris qs c km (U x) Hc HHI Espb G4 Eris G6 G7 G8 Hkm ltac:(lia)). cbn in Hx. lia. }
    replace (Z.of_nat n) with (Z.of_nat (length (cl_cache clr))) by (rewrite Lc; reflexivity).
    apply (art_ca_finish Q (log ++ art_refill_events spb c cl) regs rP M MR rom raw sp HI t spb ris qs c km st (spb + c * 2 ^ 32 + last (cl_cache clr) 0 * 16) clr
             Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 Hne' ltac:(lia) ltac:(lia) ltac:(eapply mem_grows_trans; [exact G1'|exact RG])).
    + intros x N. rewrite (RA x) by (intros F; apply N; unfold art_ca_fp; right; left; exact F).
      apply A1. cbn. split; [|exact I]. intros H. apply N. unfold art_ca_fp. left. lia.
    + exact RPH.
    + exact RCR.
    + apply TFR; [lia|lia|exact FC1].
    + apply TFR; [lia|lia|exact FC8].
    + apply TFR; [lia|lia|exact FC9].
    + apply TFR; [lia|lia|exact FC18].
    + apply TFR; [lia|lia|exact FC19].
    + apply TFR; [lia|lia|exact FC20].
    + rewrite KP by (intros E; discriminate E). unfold r4; gres. reflexivity.
    + rewrite KP by (intros E; discriminate E). unfold r4; gres. exact R2.
    + exact P10.
    + intros x Hx. cbn [In] in Hx.
      destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; (rewrite KP by (intros E; discriminate E); unfold r4; gres; rewrite RK by inl; unfold r3; gres; apply KR2; inl).
    + intros regs' M' S10 S2 S1 SK SG SA SGX SAX SPH SCR.
      apply (K regs' M' S10 S2 S1 SK SG SA SPH SCR).
      * apply art_cls_ok_pop; assumption.
      * exact Hch.
      * intros _ NP j Hj. pose proof (RSH NP j Hj) as C. pose proof At_s as Xs. unfold apart in Xs.
        apply (art_cell_tr1 _ MR M' _ _ _ SAX); [|exact C]. clear - Hj Xs Eca Hc G4 Espb Hkm Emu Hmu3 G6 Eris G2 G7 G8. zarith_t.
  - (* [comment removed for export] *)
    assert (Epre : art_ca_pre c cl = cl) by (unfold art_ca_pre; destruct (cl_cache cl); [contradiction|reflexivity]).
    assert (Eev : art_ca_events spb c cl = []) by (unfold art_ca_events; destruct (cl_cache cl); [contradiction|reflexivity]).
    rewrite Eev in K. rewrite app_nil_r in K. unfold art_ca_result, art_ca_cptr in K. rewrite Epre in K.
    pose proof (Hin Hne) as ->.
    set (cnt := Z.of_nat (length (cl_cache cl))).
    assert (Hcnt : 1 <= cnt <= 16). { unfold cnt. destruct (cl_cache cl); [contradiction|]. cbn [length] in *. lia. }
    destruct (art_tcell_exists M1 t 2784 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (st & Hst & Cst).
    destruct CR1 as [C0 CW]. destruct (PH1 c ltac:(lia)) as [_ Pcsz]. cbn in Pcsz.
    pose proof PC1 as (Pspb & _).
    assert (Hch : art_cptr_ok (AsanTab.class_size c) (cl_au cl) (last (cl_cache cl) 0)).
    { apply (proj1 (Forall_forall _ _) Hfor). apply in_or_app. left. rewrite (app_removelast_last 0 Hne) at 2. apply in_or_app. right. left. reflexivity. }
    pose proof (art_class_size_facts c Hc) as (Hsz & _).
    pose proof (art_cptr_lt (AsanTab.class_size c) (cl_au cl) (last (cl_cache cl) 0) ltac:(lia) ltac:(lia) Hch) as Hch'.
    destruct (art_cache_pop_core r2 M1 rom c ca 1295832 cnt (art_ic_size c) (last (cl_cache cl) 0) st spb P8
                ltac:(rewrite KR2 by inl; exact H11) ltac:(rewrite KR2 by inl; exact H10)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Eca, Et; replace (4096 * qt + 208) with ((512 * qt + 26) * 8) by lia; apply Z_mod_mult) ltac:(lia) ltac:(lia)
                Hcnt ltac:(pose proof (art_ic_size_pos c ltac:(lia)); lia) ltac:(lia) Hst ltac:(lia)
                C0 Pcsz ltac:(rewrite art_last_nth; replace (ca + 80 * c + 16 + 4 * (cnt - 1)) with (ca + 80 * c + 16 + 4 * Z.of_nat (length (cl_cache cl) - 1)) by (unfold cnt; lia); apply CW; lia)
                ltac:(replace (ca + 2576) with (t + 2784) by lia; exact Cst) Pspb
                ltac:(eapply (wr_wok _ _ _ _ Wt1); [lia|cbn; lia]) ltac:(eapply (wr_wok _ _ _ _ Wt1); [lia|cbn; lia])
                ltac:(replace (ca + 80 * c) with (t + (208 + 80 * c)) by lia; pose proof (Xi' (208 + 80 * c) ltac:(lia) ltac:(lia)) as X; unfold apart in X |- *; lia)
                ltac:(replace (ca + 2576) with (t + 2784) by lia; apply Xi'; lia))
      as (rP & RUNP & P10 & KP).
    eapply ar_steps; [exact RUNP|].
    apply (art_ca_finish Q log regs rP M M1 rom raw sp HI t spb ris qs c km st (spb + c * 2 ^ 32 + last (cl_cache cl) 0 * 16) cl
             Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 Hne Hl16 ltac:(lia) G1').
    + intros x N. apply A1. cbn. split; [|exact I]. intros H. apply N. unfold art_ca_fp. left. lia.
    + exact PH1.
    + split; [split; [exact C0|exact CW]|exact RR1].
    + exact FC1.
    + exact FC8.
    + exact FC9.
    + exact FC18.
    + exact FC19.
    + exact FC20.
    + rewrite KP by (intros E; discriminate E). rewrite KR2 by inl. exact H13.
    + rewrite KP by (intros E; discriminate E). exact R2_2.
    + exact P10.
    + intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; (rewrite KP by (intros E; discriminate E); apply KR2; inl).
    + intros regs' M' R10 R2 R1 RK RG RA RGX RAX RPH RCR.
      apply (K regs' M' R10 R2 R1 RK RG RA RPH RCR).
      * apply art_cls_ok_pop; assumption.
      * exact Hch.
      * intros E. contradiction.
Qed.
End Spec.
