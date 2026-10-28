(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatInitCache_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b BatPopulate1_b BatCls_b BatClsRep_b BatSecAllocPost_b
     BatRecycle2C_b BatRecycle3L_b BatRecycle4P_b BatRecycle4S_b BatRecycle5A_b BatRecycle5B_b BatRecycle5I_b BatRecycle5G_b BatRecycle5T_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_evok_list_app : forall EVOK l1 l2 log, art_evok_list EVOK log (l1 ++ l2) <-> art_evok_list EVOK log l1 /\ art_evok_list EVOK (log ++ l1) l2.
Proof.
  intros EVOK l1. induction l1 as [|e r IH]; intros l2 log; cbn [app art_evok_list]; [rewrite app_nil_r; tauto|].
  rewrite IH. rewrite <- app_assoc. cbn [app]. tauto.
Qed.

Section Loop.
Variables (HI t ctx tp key tsd spb ris qs parr : Z).
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Hypothesis GEO : art_geo HI t ctx tp tsd spb ris qs.
Hypothesis Htp0 : 0x661b28 <= tp - 88.
Hypothesis Htsd0 : 0x661b28 <= tsd.

#[local] Notation INV := (art_rcy_inv HI t ctx tp key tsd spb ris qs parr).
#[local] Notation TR := (art_rcy_tr HI t spb ris parr).

Definition art_rel_is_item (e : art_rel) : Prop := match e with REB _ => False | _ => True end.

#[using="GEO Htp0 Htsd0"] Lemma art_dr_items_aruns : forall (r : list art_rel) (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (sp1 wb ni j nt : Z) (G : art_rg),
  let b := spb + 24 * 2 ^ 32 + 16 * wb in
  getr regs 2 = Z_to_bv 64 sp1 -> getr regs 4 = Z_to_bv 64 tp -> getr regs 23 = Z_to_bv 64 (b + 152 + 8 * j) -> getr regs 24 = Z_to_bv 64 (ni + 16) -> getr regs 25 = Z_to_bv 64 (16 + j) ->
  HI <= sp1 - 320 -> sp1 + 16 < 2 ^ 47 -> 0 <= nt -> 0 <= j -> r <> [] -> j + Z.of_nat (length r) = ni -> ni <= 1021 -> 0 <= wb -> 16 * wb + 8192 <= 3758096384 ->
  wrA M (sp1 - 320) 320 -> cellA M (sp1 + 8) 8 (t + 208) ->
  (forall i e, nth_error r i = Some e -> cellA M (b + 24 + 8 * (j + Z.of_nat i)) 8 (art_rel_addr spb e)) ->
  INV (nt + Z.of_nat (length r)) G M -> art_rels_pre G r -> art_rels_sep spb r -> Forall (fun e => art_rel_mem spb e M) r -> Forall art_rel_is_item r ->
  Forall (fun e => art_zapart spb e b 8192) r ->
  art_evok_list EVOK log (art_rels_events r) ->
  (forall regs' (M' : word -> option byte),
      (forall x : reg, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27]%bv -> getr regs' x = getr regs x) ->
      INV nt (art_rel_steps r G) M' -> TR sp1 G r M M' ->
      Q (log ++ art_rels_events r) (mkst regs' (0x5488c : word) M' rom)) ->
  aruns ASEGS EVOK GR Q log (mkst regs (0x54874 : word) M rom).
Proof.
  induction r as [|e r' IH]; intros Q log regs M rom sp1 wb ni j nt G b H2 H4 H23 H24 H25 HHI Hsp' Hnt Hj Hne Hlen Hni Hwb0 Hwb1 W Ccb Hcells INV0 PRE SEP MEM ITEMS ZB EV K; [contradiction|].
  clear Hne. cbn [length] in Hlen, INV0. destruct PRE as [PRE1 PRE']. destruct SEP as [SEP1 SEP']. 
  pose proof (Forall_inv MEM) as MEM1. pose proof (Forall_inv_tail MEM) as MEM'. pose proof (Forall_inv ITEMS) as IT1. pose proof (Forall_inv_tail ITEMS) as ITEMS'.
  pose proof (Forall_inv ZB) as ZB1. pose proof (Forall_inv_tail ZB) as ZB'.
  change (art_rels_events (e :: r')) with (art_rel_events e ++ art_rels_events r') in EV, K. apply art_evok_list_app in EV. destruct EV as [EV1 EV'].
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & _ & _ & _ & _ & G13 & G14 & _ & _ & _ & _ & G19 & G20 & G21 & G22).
  assert (Eb : b = spb + 24 * 2 ^ 32 + 16 * wb) by reflexivity. clearbody b.
  replace (nt + Z.of_nat (S (length r'))) with (nt + Z.of_nat (length r') + 1) in INV0 by lia.
  destruct (art_rel_geo_of_inv HI t ctx tp key tsd spb ris qs parr (nt + Z.of_nat (length r') + 1) G M e ltac:(lia) INV0 PRE1) as (RG & BG).
  assert (Haddr : 0 <= art_rel_addr spb e < 2 ^ 64).
  { destruct e as [c w d b1 n|mb ms m b1 n|wb']; cbn [art_rel_addr art_rel_geo art_rel_pre art_rel_is_item] in *; [| |contradiction].
    - destruct RG as (Hc & Hw0 & Hwsz & Hd & _ & Hdsz & Hn' & _). pose proof (art_class_size_facts c Hc) as (Hsz & _). pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)) as Hq.
      clear - Hc Hw0 Hwsz Hd Hdsz Hsz Hq G1 G2 G4 G6 Eris. lia.
    - destruct BG as ((_ & _ & _ & _ & _ & _ & GB & _) & _). destruct (GB _ RG) as (_ & _ & _ & Y0 & Y1 & _). destruct PRE1 as (_ & Y2 & Y3 & _). cbn [fst snd] in *.
      clear - Y0 Y1 Y2 Y3 G1 G2. lia. }
  (* [comment removed for export] *)
  destruct (art_dr_item_call regs M rom sp1 b j (art_rel_addr spb e) H2 H23 ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) ltac:((clear - Eb G4 Espb Hwb0; lia)) ltac:((clear - Eb G1 G2 G6 Eris Hwb0 Hwb1; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia))
              Haddr
              ltac:(replace (b + 24 + 8 * j) with (b + 24 + 8 * (j + Z.of_nat 0)) by lia; apply (Hcells O e eq_refl)))
    as (r1 & RUN1 & A1 & A10 & A11 & AK).
  (* [comment removed for export] *)
  assert (REST : forall r2 (M2 : word -> option byte),
            (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 x = getr r1 x) -> getr r2 2 = Z_to_bv 64 sp1 ->
            INV (nt + Z.of_nat (length r')) (art_rel_step e G) M2 -> art_agree (art_rel_fp t spb ris parr sp1 G e) M M2 ->
            (forall a n, 0 <= a -> a + n < 2 ^ 64 -> (HI <= a \/ art_zapart spb e a n) -> wrA M a n -> wrA M2 a n) ->
            aruns ASEGS EVOK GR Q (log ++ art_rel_events e) (mkst r2 (0x54880 : bv 64)%bv M2 rom)).
  { intros r2 M2 BK B2 INV2 AG2 WT2.
    pose proof (art_rcy_tr_one HI t ctx tp tsd spb ris qs parr GEO sp1 G e M M2 RG BG HHI ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) AG2 WT2) as TR1.
    pose proof TR1 as (F1 & W1 & P1 & _).
    assert (PB : art_rcy_prot spb G b 8192) by (left; exists 24; split; [lia|(clear - Eb Hwb0 Hwb1; lia)]).
    destruct (P1 b 8192 ltac:(lia) PB ltac:(constructor; [exact ZB1|constructor])) as (_ & TB).
    assert (Ccb2 : cellA M2 (sp1 + 8) 8 (t + 208)).
    { apply (art_cell_agree _ M M2); [intros x Hx; apply F1; cbn in Hx; lia|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)|cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)|exact Ccb]. }
    assert (W2 : wrA M2 (sp1 - 320) 320) by (apply W1; [(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)|exact W]).
    pose proof (art_rels_pre_static r' _ PRE') as ST'.
    assert (MEM2 : Forall (fun e' => art_rel_mem spb e' M2) r').
    { apply Forall_forall. intros e' Hin'. pose proof (proj1 (Forall_forall _ _) MEM' e' Hin') as Me'. pose proof (proj1 (Forall_forall _ _) ST' e' Hin') as Se'.
      pose proof (art_rel_static_back e G e' Se') as Se0.
      destruct (art_rel_static_prot HI t ctx tp key tsd spb ris qs parr _ G M e' INV0 Se0) as (Pz & Hz & _ & Z1 & Z2).
      pose proof (proj1 (Forall_forall _ _) SEP1 e' Hin') as Ap. unfold art_zapart in Ap.
      destruct (P1 _ _ Hz Pz ltac:(constructor; [unfold art_zapart, apart in *; clear - Ap Z1 Z2; lia|constructor])) as (_ & Te').
      apply (art_rel_mem_tr spb G e' M M2 Se0); [|exact Me'].
      intros a k v Ha Hk C. apply Te'; [exact Ha|exact Hk| | |exact C].
      - destruct Pz as [(c' & Hc' & Y1 & Y2)|(bb & Hbb & Y1 & Y2)]; [(clear - Ha Y1 Hc' G4; lia)|]. destruct BG as ((_ & _ & _ & _ & _ & _ & GB & _) & _). destruct (GB _ Hbb) as (_ & _ & _ & ? & _). (clear - Ha Y1 H; lia).
      - destruct Pz as [(c' & Hc' & Y1 & Y2)|(bb & Hbb & Y1 & Y2)]; [(clear - Hk Y2 Hc' G1 G2 G6 Eris; lia)|]. destruct BG as ((_ & _ & _ & _ & _ & _ & GB & _) & _). destruct (GB _ Hbb) as (_ & _ & _ & _ & ? & _). (clear - Hk Y2 H G1 G2; lia). }
    assert (Hcells2 : forall i e', nth_error r' i = Some e' -> cellA M2 (b + 24 + 8 * (j + 1 + Z.of_nat i)) 8 (art_rel_addr spb e')).
    { intros i e' Hi. assert (Hil : (i < length r')%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      apply TB; [(clear - Hj; lia)|cbn; (clear - Hil Hlen Hni; lia)|(clear - Eb G4 Espb Hwb0 Hj; lia)|cbn; (clear - Eb G1 G2 G6 Eris Hwb0 Hwb1 Hil Hlen Hni; lia)|].
      replace (j + 1 + Z.of_nat i) with (j + Z.of_nat (S i)) by lia. apply (Hcells (S i) e' Hi). }
    destruct r' as [|e2 r''].
    - (* [comment removed for export] *)
      destruct (art_dr_item_last r2 M2 rom b j ni ltac:(rewrite BK by inl; rewrite AK by inl; exact H23) ltac:(rewrite BK by inl; rewrite AK by inl; exact H24)
                  ltac:(rewrite BK by inl; rewrite AK by inl; exact H25) Hj ltac:(cbn [length] in Hlen; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) ltac:((clear - Eb G4 Espb Hwb0; lia)) ltac:((clear - Eb G1 G2 G6 Eris Hwb0 Hwb1; lia)))
        as (r3 & RUN3 & CK).
      eapply ar_steps; [exact RUN3|]. apply ar_done.
      cbn [art_rels_events flat_map] in K. rewrite app_nil_r in K. cbn [length] in INV2. replace (nt + Z.of_nat 0) with nt in INV2 by lia.
      apply (K r3 M2); [|exact INV2|exact TR1].
      intros x Hx. cbn [In] in Hx. destruct Hx as [<-|Hx]; [rewrite CK by inl; rewrite B2; symmetry; exact H2|].
      repeat (destruct Hx as [<-|Hx]; [rewrite CK by inl; rewrite BK by inl; apply AK; inl|]). destruct Hx.
    - (* [comment removed for export] *)
      destruct (art_dr_item_more r2 M2 rom b j ni ltac:(rewrite BK by inl; rewrite AK by inl; exact H23) ltac:(rewrite BK by inl; rewrite AK by inl; exact H24)
                  ltac:(rewrite BK by inl; rewrite AK by inl; exact H25) Hj ltac:(cbn [length] in Hlen; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) ltac:((clear - Eb G4 Espb Hwb0; lia)) ltac:((clear - Eb G1 G2 G6 Eris Hwb0 Hwb1; lia)))
        as (r3 & RUN3 & C23 & C25 & CK).
      eapply ar_steps; [exact RUN3|].
      apply (IH Q (log ++ art_rel_events e) r3 M2 rom sp1 wb ni (j + 1) nt (art_rel_step e G)
               ltac:(rewrite CK by inl; exact B2) ltac:(rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H4)
               ltac:(rewrite <- Eb; exact C23) ltac:(rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H24) C25
               HHI Hsp' Hnt ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) ltac:(discriminate) ltac:(cbn [length] in *; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) Hni Hwb0 Hwb1 W2 Ccb2
               ltac:(rewrite <- Eb; exact Hcells2) INV2 PRE' SEP' MEM2 ITEMS' ltac:(rewrite <- Eb; exact ZB') EV').
      intros r4 M4 DK INV4 TR4.
      rewrite app_assoc in K.
      apply (K r4 M4); [|exact INV4|exact (art_rcy_tr_app HI t spb ris parr sp1 G [e] (e2 :: r'') M M2 M4 TR1 TR4)].
      intros x Hx. rewrite (DK x Hx). cbn [In] in Hx. destruct Hx as [<-|Hx]; [rewrite CK by inl; rewrite B2; symmetry; exact H2|].
      repeat (destruct Hx as [<-|Hx]; [rewrite CK by inl; rewrite BK by inl; apply AK; inl|]). destruct Hx. }
  (* [comment removed for export] *)
  eapply ar_steps; [exact RUN1|].
  destruct e as [c w d b1 n|mb ms m b1 n|wb']; [| |contradiction].
  - destruct (art_rcy_prim_step HI t ctx tp key tsd spb ris qs parr GEO r1 M rom (0x54880 : bv 64)%bv sp1 (sp1 + 8) (nt + Z.of_nat (length r')) c w d b1 n G
                A1 ltac:(unfold ret_ok; bveq) ltac:(rewrite AK by inl; exact H2) ltac:(rewrite AK by inl; exact H4) A10 A11 HHI ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) W Ccb ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) INV0 PRE1 MEM1)
      as (r2 & M2 & RUN2 & B2 & BK & INV2 & GRW & AG2).
    eapply ar_steps; [exact RUN2|]. cbn [art_rel_events] in REST. rewrite app_nil_r in REST.
    apply (REST r2 M2 BK B2 INV2 AG2). intros a k _ _ _ Wa. eapply wr_grows; [exact GRW|exact Wa].
  - apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st X; exact X].
    apply (art_rcy_sec_step HI t ctx tp key tsd spb ris qs parr EVOK GR GEO (fun lg st => aruns ASEGS EVOK GR Q lg st) log r1 M rom (0x54880 : bv 64)%bv sp1 (sp1 + 8) (nt + Z.of_nat (length r')) mb ms m b1 n G
             A1 ltac:(unfold ret_ok; bveq) ltac:(rewrite AK by inl; exact H2) ltac:(rewrite AK by inl; exact H4) A10 A11 HHI ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) W ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Hnt Hj Hni Hwb0 Hwb1 Hlen; lia)) Htp0 Htsd0 INV0 PRE1 MEM1 EV1).
    intros r2 M2 _ B2 BK INV2 AG2 FW. apply (REST r2 M2 BK B2 INV2 AG2).
    intros a k Ha Hk Hh Wa. apply FW; [exact Ha|exact Hk| |exact Wa]. destruct Hh as [Hh|Hh]; [|exact Hh].
    cbn [art_rel_geo] in RG. destruct BG as ((_ & _ & _ & _ & _ & _ & GB & _) & _). destruct (GB _ RG) as (_ & _ & _ & _ & X & _). cbn [fst snd] in X. unfold apart. (clear - X Hh; lia).
Qed.
End Loop.
