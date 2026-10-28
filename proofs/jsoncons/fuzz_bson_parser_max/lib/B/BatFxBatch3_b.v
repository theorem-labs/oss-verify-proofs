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
     ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatClsRefill_b
     BatCellEx_b BatCARSpec_b BatAlloc3Pure_b BatAllocate3_b BatFree1_b BatFxBatch1_b BatFxBatch2_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_enq_newb (L cntB : Z) : bool := (L =? 0) || (cntB =? 1021).
Definition art_enq_events (newb : bool) (spb : Z) (cl : art_cls) : list aev := if newb then art_ca_events spb 24 cl else [].
Definition art_enq_cls (newb : bool) (cl : art_cls) : art_cls := if newb then art_cls_pop (art_ca_pre 24 cl) else cl.
Definition art_enq_fp (newb : bool) (sp t spb ris qs km b L B cntB : Z) (x : Z) : Prop :=
  if newb then art_enq_new_fp sp t spb ris qs km b L B x
  else (sp - 64 <= x < sp) \/ (B + 8 <= x < B + 24) \/ (B + 24 + 8 * cntB <= x < B + 32 + 8 * cntB) \/ (t + 104 <= x < t + 112).

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Theorem art_enqueue_rspec_holds :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
         (sp HI t ctx tp key tsd spb ris qs km st m n L B wB cntB bszB bytes : Z) (inited : bool) (cl : art_cls),
    let c := t + 80 in
    let ca := t + 208 in
    let b := spb + 24 * 2 ^ 32 + 16 * art_ca_cptr 24 cl in
    let newb := art_enq_newb L cntB in
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp ->
    getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 ca -> getr regs 12 = Z_to_bv 64 st -> getr regs 13 = Z_to_bv 64 m -> getr regs 14 = Z_to_bv 64 n ->
    HI <= sp - 736 -> sp < 2 ^ 47 -> art_geo HI t ctx tp tsd spb ris qs ->
    wrA M (sp - 736) 736 -> wrA M t 4096 ->
    art_prim_consts spb ris M -> art_layout M -> art_tsd M tp key tsd ctx t ->
    art_pc_hdr ca inited M -> art_cls_rep ca spb ris 24 cl M -> art_cls_ok 24 cl -> (cl_cache cl <> [] -> inited = true) -> cl_mu cl = 262144 * km ->
    (newb = true -> cl_cache cl = [] -> art_cls_needs_populate 24 cl = true ->
       cl_mu cl + 262144 <= 3758096384
       /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new 24 cl) <= 536870912
       /\ wrA M (2147450880 + 8192 * qs + 24 * 2 ^ 29 + 32768 * km) 32768
       /\ wrA M (2147450880 + 8192 * qs + 24 * 2 ^ 29 + 469762048) 67108864) ->
    art_evok_list EVOK log (art_enq_events newb spb cl) ->
    0 <= L < 2 ^ 63 -> 0 <= B < 2 ^ 63 -> 0 <= bytes -> bytes + n + 8192 < 2 ^ 64 -> 0 <= n -> 0 <= m < 2 ^ 64 ->
    cellA M c 8 L -> cellA M (c + 24) 8 bytes ->
    (L <> 0 -> B = spb + 24 * 2 ^ 32 + 16 * wB /\ art_cptr_ok 8192 (cl_au cl) wB /\ ~ In wB (cl_cache cl ++ cl_free cl)
               /\ cellA M (c + 16) 8 B /\ cellA M (B + 16) 8 cntB /\ cellA M (B + 8) 8 bszB /\ 0 <= cntB <= 1021 /\ 0 <= bszB /\ bszB + n < 2 ^ 64) ->
    (forall regs' (M' : word -> option byte),
        getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
        mem_grows M M' ->
        (forall x : word, ~ art_enq_fp newb sp t spb ris qs km b L B cntB (U x) -> M' x = M x) ->
        art_pc_hdr ca (if newb then true else inited) M' -> art_cls_rep ca spb ris 24 (art_enq_cls newb cl) M' -> art_cls_ok 24 (art_enq_cls newb cl) ->
        (newb = true ->
           art_cptr_ok 8192 (cl_au (art_ca_pre 24 cl)) (art_ca_cptr 24 cl)
           /\ (cl_cache cl = [] -> art_cls_needs_populate 24 cl = true ->
                 forall j, 0 <= j < 32768 -> cellA M' (2147450880 + 8192 * qs + 24 * 2 ^ 29 + 32768 * km + j) 1 250)
           /\ cellA M' b 8 0 /\ cellA M' (b + 8) 8 (n + 8192) /\ cellA M' (b + 16) 8 1 /\ cellA M' (b + 24) 8 m
           /\ cellA M' c 8 (L + 1) /\ cellA M' (c + 16) 8 b /\ (L = 0 -> cellA M' (c + 8) 8 b) /\ (L <> 0 -> cellA M' B 8 b)) ->
        (newb = false -> cellA M' (B + 16) 8 (cntB + 1) /\ cellA M' (B + 8) 8 (bszB + n) /\ cellA M' (B + 24 + 8 * cntB) 8 m) ->
        cellA M' (c + 24) 8 (bytes + n + (if newb then 8192 else 0)) ->
        Q (log ++ art_enq_events newb spb cl) (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x56b58 : word) M rom).
Proof.
  intros Q log regs M rom raw sp HI t ctx tp key tsd spb ris qs km st m n L B wB cntB bszB bytes inited cl c ca b newb
         H1 Hret H2 H4 H10 H11 H12 H13 H14 HHI Hsp' GEO W Wt PC LY T PH RC OK Hin Emu Room EV HL HB0 Hby Hby' Hn Hm CL Cby HB K.
  destruct newb eqn:ENB.
  - (* [comment removed for export] *)
    unfold art_enq_events, art_enq_cls, art_enq_fp in *.
    apply (art_enq_new_aruns EVOK GR Q log regs M rom raw sp HI t ctx tp key tsd spb ris qs km st m n L B wB bytes inited cl
             H1 Hret H2 H4 H10 H11 H12 H13 H14 HHI Hsp' GEO W Wt PC LY T PH RC OK Hin Emu (Room eq_refl) EV HL HB0 Hby Hby' Hn Hm CL Cby).
    + intros NL. destruct (HB NL) as (EB & CPB & NIB & X1 & X2 & _). split; [exact EB|]. split; [exact CPB|]. split; [exact NIB|]. split; [exact X1|].
      unfold newb, art_enq_newb in ENB. apply orb_true_iff in ENB. destruct ENB as [E|E]; [apply Z.eqb_eq in E; contradiction|]. apply Z.eqb_eq in E. rewrite E in X2. exact X2.
    + intros regs' M' S2 S1 SK SG SA SPH SCR SOK SCP SSH B1 B2 B3 B4 L1 L2 L3 LE LN.
      apply (K regs' M' S2 S1 SK SG SA SPH SCR SOK).
      * intros _. exact (conj SCP (conj SSH (conj B1 (conj B2 (conj B3 (conj B4 (conj L1 (conj L2 (conj LE LN))))))))).
      * intros E. discriminate E.
      * replace (bytes + n + 8192) with (bytes + (n + 8192)) by lia. exact L3.
  - (* [comment removed for export] *)
    unfold art_enq_events, art_enq_cls, art_enq_fp in *. rewrite app_nil_r in K.
    unfold newb, art_enq_newb in ENB. apply orb_false_iff in ENB. destruct ENB as [E1 E2]. apply Z.eqb_neq in E1, E2.
    destruct (HB E1) as (EB & CPB & NIB & CB & Ccnt & Cbsz & Hcnt & Hbsz & Hbsz').
    pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
    pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _).
    pose proof CPB as (HwB0 & HwB1 & _).
    destruct RC as [CR RR]. pose proof RR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wu).
    assert (Ec : c = t + 80) by reflexivity. assert (Eca : ca = t + 208) by reflexivity. clearbody c ca.
    pose proof G11 as X11. unfold apart in X11.
    pose proof (art_enqueue_fn regs M rom raw sp c B L cntB bszB bytes m n H1 Hret H2 H10 H13 H14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia) Hbsz Hbsz' Hby ltac:(lia) Hn Hm ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia)
                  ltac:(eapply wr_sub; [exact W|lia|lia]) ltac:(eapply wr_sub; [exact Wt|lia|lia]) ltac:(eapply wr_sub; [exact Wu|lia|lia]) CL CB Ccnt Cbsz Cby) as RUN.
    eapply ar_steps; [exact RUN|]. apply ar_done. clear RUN.
    set (M2 := art_enq_mem M sp raw regs B cntB bszB bytes c m n).
    assert (A2 : art_agree [(sp - 64, 64); (B + 8, 16); (B + 24 + 8 * cntB, 8); (c + 24, 8)] M M2).
    { unfold M2, art_enq_mem. eapply art_agree_sub; [zagree|]. intros z Hz Hout. cbn [art_out app fst snd] in Hout |- *. repeat split; lia. }
    assert (G2' : mem_grows M M2) by (unfold M2, art_enq_mem; zgrows).
    apply (K _ M2).
    + gres. reflexivity.
    + gres. reflexivity.
    + intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; reflexivity.
    + exact G2'.
    + intros x N. apply A2. cbn [art_out fst snd]. rewrite Ec. repeat split; lia.
    + apply (art_pc_hdr_tr _ ca inited M M2 ltac:(lia) ltac:(lia) A2); [|exact PH]. intros c' Hc'. clear - Hc' Ec Eca HHI Hsp' G7 G8 X11 EB HwB0 HwB1 Haumu Hmu3 Hcnt E2 G4. zarith_t.
    + apply (art_cls_rep_tr [(sp - 64, 64); (B + 8, 16); (B + 24 + 8 * cntB, 8); (c + 24, 8)] ca spb ris 24 cl M M2); first [ exact G2' | exact A2 | exact (conj CR RR) | exact Hl16 | idtac ];
        clear - Ec Eca HHI Hsp' G1 G2 G6 G7 G8 X11 EB HwB0 HwB1 Haumu Hmu3 Hcnt E2 G4 Eris Espb Hnf4 Hmfa1; first [ lia | zarith_t ].
    + exact OK.
    + intros E. discriminate E.
    + intros _. unfold M2, art_enq_mem. repeat split.
      * apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; [lia|cbn; lia].
      * do 3 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]). apply cell_Wn_hit; [lia|cbn; lia].
      * apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; [lia|cbn; lia].
    + replace (bytes + n + 0) with (bytes + n) by lia. unfold M2, art_enq_mem. apply cell_Wn_hit; [lia|cbn; lia].
Qed.
End Spec.
