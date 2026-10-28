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
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatInitCache_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b BatPopulate1_b BatCls_b BatClsRep_b BatCARSpec_b BatSecAllocPost_b BatFxQ_b BatImgCell_b BatAllocate3_b
     BatFree1_b BatFxDrain_b
     BatRecycle2C_b BatRecycle3L_b BatRecycle4P_b BatRecycle4S_b BatRecycle5A_b BatRecycle5B_b BatRecycle5R_b BatRecycle5I_b BatRecycle5G_b BatRecycle5T_b BatRecycle5C_b BatRecycle5D_b BatRecycle5E_b BatRecycle5F_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_drain_W5 (sp c GL GB : Z) : list (Z * Z) :=
  [(sp - 48, 48); (0x13c8b0 + 152, 16); (0x13c8b0 + 176, 16); (c, 32); ((if GL =? 0 then 0x13c8b0 + 168 else GB), 8)].

Lemma art_drain_mem_facts : forall (M : word -> option byte) (raw : word) (regs : bvmap 5 word) (sp c L F B bytes GL GB gbytes : Z),
  0x696000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> (c + 32 <= 0x10000 \/ 0x696000 <= c) -> apart (sp - 48) 48 c 32 ->
  (GL <> 0 -> 0x696000 <= GB /\ GB + 8 < 2 ^ 64 /\ apart (sp - 48) 48 GB 8 /\ apart c 32 GB 8 /\ wrA M GB 8) ->
  wrA M (sp - 48) 48 -> wrA M c 32 -> wrA M (0x13c8b0 + 152) 40 ->
  let M1 := art_drain_mem M sp raw regs c L F B bytes GL GB gbytes in
  mem_grows M M1 /\ art_agree (art_drain_W5 sp c GL GB) M M1
  /\ cellA M1 c 8 0 /\ cellA M1 (c + 8) 8 0 /\ cellA M1 (c + 16) 8 0 /\ cellA M1 (c + 24) 8 0
  /\ cellA M1 (0x13c8b0 + 160) 8 (GL + L) /\ cellA M1 (0x13c8b0 + 176) 8 B /\ cellA M1 (0x13c8b0 + 184) 8 (gbytes + bytes)
  /\ (GL = 0 -> cellA M1 (0x13c8b0 + 168) 8 F) /\ (GL <> 0 -> cellA M1 GB 8 F)
  /\ cellA M1 (sp - 8) 8 (U raw) /\ cellA M1 (sp - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 24) 8 (U (getr regs 9)) /\ cellA M1 (sp - 32) 8 (U (getr regs 18))
  /\ cellA M1 (sp - 40) 8 (U (getr regs 19)) /\ cellA M1 (0x13c8b0 + 152) 4 0.
Proof.
  intros M raw regs sp c L F B bytes GL GB gbytes IMG Hsp' Hc Hc' Hci Ac HGB W Wc Wq M1.
  pose proof Ac as Xc. unfold apart in Xc.
  assert (FACTS : mem_grows M M1 /\ art_agree (art_drain_W5 sp c GL GB) M M1
            /\ cellA M1 c 8 0 /\ cellA M1 (c + 8) 8 0 /\ cellA M1 (c + 16) 8 0 /\ cellA M1 (c + 24) 8 0
            /\ cellA M1 (0x13c8b0 + 160) 8 (GL + L) /\ cellA M1 (0x13c8b0 + 176) 8 B /\ cellA M1 (0x13c8b0 + 184) 8 (gbytes + bytes)
            /\ (GL = 0 -> cellA M1 (0x13c8b0 + 168) 8 F) /\ (GL <> 0 -> cellA M1 GB 8 F)
            /\ cellA M1 (sp - 8) 8 (U raw) /\ cellA M1 (sp - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 24) 8 (U (getr regs 9)) /\ cellA M1 (sp - 32) 8 (U (getr regs 18))
            /\ cellA M1 (sp - 40) 8 (U (getr regs 19))).
  { unfold art_drain_W5, M1, art_drain_mem, art_drain_frame. destruct (Z.eqb_spec GL 0) as [EG|NG].
    - split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia|].
      repeat split; try (intros E; try contradiction); try zcell. rewrite EG. zcell.
    - destruct (HGB NG) as (GB0 & GB1 & AGs & AGc & WGB). unfold apart in AGs, AGc.
      split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia|].
      repeat split; try (intros E; try contradiction); try zcell. }
  destruct FACTS as (G1 & A1 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & F1 & F8 & F9 & F18 & F19).
  repeat (split; [assumption|]).
  unfold M1. apply art_drain_mem_lock; try assumption. intros NG. destruct (HGB NG) as (GB0 & GB1 & _). split; assumption.
Qed.

Section DrainRcy.
Variables (HI t ctx tp key tsd spb ris qs parr : Z).
Hypothesis GEO : art_geo HI t ctx tp tsd spb ris qs.
Hypothesis Htp0 : 0x661b28 <= tp - 88.
Hypothesis Htsd0 : 0x661b28 <= tsd.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[local] Abbreviation INV := (art_rcy_inv HI t ctx tp key tsd spb ris qs parr).
#[local] Abbreviation rbq := (art_rb_q spb).
#[local] Abbreviation TRQ := (art_rcy_trq HI t spb ris parr).

(* [comment removed for export] *)
#[using="GEO Htp0 Htsd0"] Lemma art_recycle_locked_aruns : forall (pre rest : list art_rbatch) (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M1 rom : word -> option byte) (raw : word)
    (sp mn cbs GL : Z) (G : art_rg),
  let gq := map rbq (pre ++ rest) in
  let work := art_rb_work pre in
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 0x13c8b0 -> getr regs 11 = Z_to_bv 64 mn ->
  getr regs 12 = Z_to_bv 64 (t + 208) -> getr regs 13 = Z_to_bv 64 cbs ->
  HI <= sp - 512 -> sp < 2 ^ 47 -> 0 <= cbs < 2 ^ 64 ->
  art_rcy_npop mn gq = length pre -> Forall (art_rb_ok) pre ->
  16384 * Z.of_nat (length gq) <= art_qbytes gq -> art_qbytes gq < 2 ^ 54 -> 0 <= mn < art_qbytes gq ->
  art_qsep gq -> Forall (art_qin HI) gq -> Forall (art_qin24 spb) gq ->
  Forall (fun b => Forall (fun e => art_zapart spb e (qb_addr b) 8192) work) (map rbq rest) ->
  Forall (fun e => art_rel_is_item e -> Forall (fun b => art_zapart spb e (qb_addr b) 8) gq) work ->
  wrA M1 (sp - 512) 512 -> Forall (fun b => wrA M1 (qb_addr b) 8) gq ->
  cellA M1 (0x13c8b0 + 152) 4 0 -> cellA M1 (0x13c8b0 + 184) 8 (art_qbytes gq) -> cellA M1 (0x13c8b0 + 160) 8 (Z.of_nat (length gq)) -> cellA M1 (0x13c8b0 + 168) 8 (art_qhead gq) ->
  cellA M1 (0x13c8b0 + 176) 8 GL -> art_qlist M1 gq (art_qhead gq) GL ->
  INV (Z.of_nat (length work)) G M1 -> art_rels_pre G work -> art_rels_sep spb work -> Forall (fun e => art_rel_mem spb e M1) work ->
  art_evok_list EVOK log (art_rels_events work) ->
  (forall regs' (M' : word -> option byte),
      getr regs' 1 = raw -> getr regs' 2 = Z_to_bv 64 sp -> (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
      INV 0 (art_rel_steps work G) M' -> TRQ sp G work gq M1 M' ->
      cellA M' (0x13c8b0 + 160) 8 (Z.of_nat (length rest)) -> cellA M' (0x13c8b0 + 168) 8 (art_qhead (map rbq rest)) -> cellA M' (0x13c8b0 + 184) 8 (art_qbytes (map rbq rest)) ->
      (rest = [] -> cellA M' (0x13c8b0 + 176) 8 0) -> (rest <> [] -> cellA M' (0x13c8b0 + 176) 8 GL) -> cellA M' (0x13c8b0 + 152) 4 0 ->
      art_qlist M' (map rbq rest) (art_qhead (map rbq rest)) GL -> art_qbytes (map rbq rest) <= mn ->
      Q (log ++ art_rels_events work) (mkst regs' raw M' rom)) ->
  aruns ASEGS EVOK GR Q log (mkst regs (0x54454 : word) (Wn 4 M1 (0x13c8b0 + 152) 256) rom).
Proof.
  intros pre rest Q log regs M1 rom raw sp mn cbs GL G gq work H1 Hret H2 H4 H10 H11 H12 H13 HHI HS47 Hcbs Hnp OKS Hmerge Hqb Hmn SEP QIN Q24 SEPR SEPI W WL Clk Cgb Ccnt Cgf Cgl QL INV0 PRE RSEP MEM EV K.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & Gti & _).
  assert (QB : forall b, In b gq -> 0x696000 <= qb_addr b /\ qb_addr b + 8192 <= HI) by (intros b Hb; destruct (proj1 (Forall_forall _ _) QIN b Hb) as (X1 & X2 & _); split; assumption).
  set (M2 := Wn 4 M1 (0x13c8b0 + 152) 256).
  assert (WK : wokA M1 (0x13c8b0 + 152) 4) by (apply (wr_wok _ _ _ _ (art_img_wr M1 (0x13c8b0 + 152) 4 ltac:(lia) ltac:(lia) ltac:(lia))); cbn; lia).
  assert (GR12 : mem_grows M1 M2) by (unfold M2; zgrows).
  assert (AG12 : art_agree [(0x13c8b0 + 152, 4)] M1 M2) by (unfold M2; exact (art_agree_Wn 4%nat M1 (0x13c8b0 + 152) 256 ltac:(lia) ltac:(cbn; lia))).
  assert (GAPq : forall a n, (a + n <= 0x13c8b0 + 152 \/ 0x13c8b0 + 156 <= a) -> art_gap [(0x13c8b0 + 152, 4)] a n).
  { intros a n Ha. cbn [art_gap fst snd]. unfold apart. clear - Ha. repeat split; try exact I; lia. }
  assert (TC : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= 0x13c8b0 + 152 \/ 0x13c8b0 + 156 <= a) -> cellA M1 a k v -> cellA M2 a k v).
  { intros a k v Ha Hk Hq C. apply (art_cell_tr _ M1 M2 a k v AG12); [apply GAPq; exact Hq|exact Ha|exact Hk|exact C]. }
  assert (AGW : art_agree (art_rcy_W HI []) M1 M2).
  { eapply art_agree_sub; [exact AG12|]. intros z Hz Ho. unfold art_rcy_W in Ho. cbn [art_out app map fst snd] in Ho |- *. clear - Ho. repeat split; try exact I; lia. }
  assert (INV2 : INV (Z.of_nat (length work)) G M2) by exact (art_rcy_inv_trq HI t ctx tp key tsd spb ris qs parr GEO Htp0 Htsd0 [] _ G M1 M2 (Forall_nil _) GR12 AGW INV0).
  pose proof (art_rels_pre_static _ _ PRE) as STall.
  assert (MEM2 : Forall (fun e => art_rel_mem spb e M2) work).
  { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) MEM e He) as Me. pose proof (proj1 (Forall_forall _ _) STall e He) as Se.
    destruct e as [c w d b1 n'|mb ms m b1 n'|wb]; [| |exact I].
    - destruct (art_rel_static_prot HI t ctx tp key tsd spb ris qs parr _ G M1 _ INV0 Se) as (Pz & Hz & _ & Z1 & Z2).
      destruct (art_rcy_prot_below HI t ctx tp tsd spb ris qs parr GEO G _ _ ltac:(destruct INV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ISG & IBK & IPK); exact (conj ISG (conj IBK IPK))) Pz) as (Lo & Hi).
      apply (art_rel_mem_tr spb G _ M1 M2 Se); [|exact Me]. intros a kk v Ha Hkk C. apply TC; [clear - Ha Lo; lia|clear - Hkk Hi G2; lia|right; clear - Ha Lo; lia|exact C].
    - destruct (art_rel_static_prot HI t ctx tp key tsd spb ris qs parr _ G M1 _ INV0 Se) as (Pz & Hz & _ & Z1 & Z2).
      destruct (art_rcy_prot_below HI t ctx tp tsd spb ris qs parr GEO G _ _ ltac:(destruct INV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ISG & IBK & IPK); exact (conj ISG (conj IBK IPK))) Pz) as (Lo & Hi).
      apply (art_rel_mem_tr spb G _ M1 M2 Se); [|exact Me]. intros a kk v Ha Hkk C. apply TC; [clear - Ha Lo; lia|clear - Hkk Hi G2; lia|right; clear - Ha Lo; lia|exact C]. }
  assert (QG2 : Forall (art_qgeo [(0x13c8b0 + 152, 4)]) gq).
  { apply Forall_forall. intros b Hb. destruct (QB b Hb) as (X1 & X2). split; [clear - X1; lia|]. split; [clear - X2 G2; lia|]. apply GAPq. right. clear - X1. lia. }
  apply (art_recycle_aruns HI t ctx tp key tsd spb ris qs parr GEO Htp0 Htsd0 EVOK GR pre rest Q log regs M2 rom raw sp mn cbs GL G H1 Hret H2 H4 H10 H11 H12 H13 HHI HS47 Hcbs Hnp OKS Hmerge Hqb Hmn SEP QIN Q24 SEPR SEPI
           ltac:(eapply wr_grows; [exact GR12|exact W]) ltac:(eapply Forall_impl; [|exact WL]; intros b Wb; eapply wr_grows; [exact GR12|exact Wb])
           ltac:(unfold M2; apply cell_Wn_hit; [lia|cbn; lia])
           ltac:(apply TC; [lia|cbn; lia|right; cbn; lia|exact Cgb]) ltac:(apply TC; [lia|cbn; lia|right; cbn; lia|exact Ccnt]) ltac:(apply TC; [lia|cbn; lia|right; cbn; lia|exact Cgf])
           ltac:(apply TC; [lia|cbn; lia|right; cbn; lia|exact Cgl]) (art_qlist_tr _ M1 M2 gq _ _ AG12 QG2 QL) INV2 PRE RSEP MEM2 EV).
  intros regs' M' R1' R2' K' INV' TR C160 C168 C184 C176a C176b Clk' QL' Hrest.
  apply (K regs' M' R1' R2' K' INV'); try assumption.
  destruct TR as (FR & WR & PT & AG). split; [|split; [|split]].
  - intros x Hx. rewrite (FR x Hx). apply AG12. cbn [art_out fst snd]. clear - Hx HHI G1. repeat split; try exact I; lia.
  - intros a n Ha Hn HHa Wr. apply WR; [exact Ha|exact Hn|exact HHa|]. eapply wr_grows; [exact GR12|exact Wr].
  - intros zlo zlen Hz Hhi Pz FZ FLk Hq. destruct (PT zlo zlen Hz Hhi Pz FZ FLk Hq) as (P' & CT). split; [exact P'|].
    intros a k v Ha Hka Ha0 Hak C. apply (CT a k v Ha Hka Ha0 Hak). apply TC; [exact Ha0|exact Hak|clear - Ha Hka Hq; lia|exact C].
  - eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ AG12 AG)|]. intros z Hz Ho. apply art_out_app. split; [|exact Ho].
    unfold art_rcy_W2 in Ho. cbn [art_out app fst snd] in Ho |- *. clear - Ho. repeat split; try exact I; lia.
Qed.

(* [comment removed for export] *)
#[using="GEO Htp0 Htsd0"] Theorem art_drain_rcy_aruns : forall (pre rest : list art_rbatch) (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
    (sp L F B bytes GL GB gbytes msz cbs : Z) (G : art_rg),
  let M1 := art_drain_mem M sp raw regs (t + 80) L F B bytes GL GB gbytes in
  let gq := map rbq (pre ++ rest) in
  let work := art_rb_work pre in
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 0x13c8b0 -> getr regs 11 = Z_to_bv 64 (t + 80) ->
  getr regs 12 = Z_to_bv 64 (t + 208) -> getr regs 13 = Z_to_bv 64 cbs ->
  HI <= sp - 560 -> sp < 2 ^ 47 -> 0 <= cbs < 2 ^ 64 ->
  1 <= L < 2 ^ 63 -> 0 <= F < 2 ^ 64 -> 0 <= B < 2 ^ 64 -> 0 <= bytes -> 0 <= gbytes -> 2 ^ 28 < gbytes + bytes -> 0 <= GL -> GL + L < 2 ^ 63 ->
  (GL <> 0 -> 0x696000 <= GB /\ GB + 8 <= HI /\ apart (t + 80) 32 GB 8 /\ wrA M GB 8) ->
  wrA M (sp - 560) 560 -> wrA M (t + 80) 32 ->
  cellA M (0x13c8b0 + 152) 4 0 -> cellA M (0x13c8b0 + 64) 8 (2 ^ 28) -> cellA M (0x13c8b0 + 72) 8 msz -> 0 <= msz < 2 ^ 64 ->
  cellA M (t + 80) 8 L -> cellA M (t + 80 + 8) 8 F -> cellA M (t + 80 + 16) 8 B -> cellA M (t + 80 + 24) 8 bytes ->
  cellA M (0x13c8b0 + 160) 8 GL -> (GL <> 0 -> cellA M (0x13c8b0 + 176) 8 GB) -> cellA M (0x13c8b0 + 184) 8 gbytes ->
  (* [comment removed for export] *)
  art_qbytes gq = gbytes + bytes -> Z.of_nat (length gq) = GL + L ->
  art_rcy_npop msz gq = length pre -> Forall (art_rb_ok) pre ->
  16384 * Z.of_nat (length gq) <= art_qbytes gq -> art_qbytes gq < 2 ^ 54 -> msz < art_qbytes gq ->
  art_qsep gq -> Forall (art_qin HI) gq -> Forall (art_qin24 spb) gq ->
  Forall (fun b => Forall (fun e => art_zapart spb e (qb_addr b) 8192) work) (map rbq rest) ->
  Forall (fun e => art_rel_is_item e -> Forall (fun b => art_zapart spb e (qb_addr b) 8) gq) work ->
  Forall (fun b => wrA M1 (qb_addr b) 8) gq ->
  cellA M1 (0x13c8b0 + 168) 8 (art_qhead gq) -> art_qlist M1 gq (art_qhead gq) B ->
  INV (Z.of_nat (length work)) G M1 -> art_rels_pre G work -> art_rels_sep spb work -> Forall (fun e => art_rel_mem spb e M1) work ->
  art_evok_list EVOK log (art_rels_events work) ->
  (forall regs' (M' : word -> option byte),
      getr regs' 1 = raw -> getr regs' 2 = Z_to_bv 64 sp -> (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
      INV 0 (art_rel_steps work G) M' -> TRQ sp G work gq M1 M' ->
      cellA M' (0x13c8b0 + 160) 8 (Z.of_nat (length rest)) -> cellA M' (0x13c8b0 + 168) 8 (art_qhead (map rbq rest)) -> cellA M' (0x13c8b0 + 184) 8 (art_qbytes (map rbq rest)) ->
      (rest = [] -> cellA M' (0x13c8b0 + 176) 8 0) -> (rest <> [] -> cellA M' (0x13c8b0 + 176) 8 B) -> cellA M' (0x13c8b0 + 152) 4 0 ->
      art_qlist M' (map rbq rest) (art_qhead (map rbq rest)) B -> art_qbytes (map rbq rest) <= msz ->
      Q (log ++ art_rels_events work) (mkst regs' raw M' rom)) ->
  aruns ASEGS EVOK GR Q log (mkst regs (0x542b0 : word) M rom).
Proof.
  intros pre rest Q log regs M rom raw sp L F B bytes GL GB gbytes msz cbs G M1 gq work H1 Hret H2 H4 H10 H11 H12 H13 HHI HS47 Hcbs HL HF HB Hby Hgb Hbig HGL HGL' HGB0 W Wc
         Clk Cmax Cmin Hmsz CL CF CB Cby CGL CGB Cgb Eqb Elen Hnp OKS Hmerge Hqb Hmn SEP QIN Q24 SEPR SEPI WL Cgf QL INV0 PRE RSEP MEM EV K.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & Gt0 & Gt1 & Gti & _).
  assert (Ac : apart (sp - 48) 48 (t + 80) 32) by (unfold apart; clear - Gt1 HHI; lia).
  assert (HGB : GL <> 0 -> 0x696000 <= GB /\ GB + 8 < 2 ^ 64 /\ apart (sp - 48) 48 GB 8 /\ apart (t + 80) 32 GB 8 /\ wrA M GB 8).
  { intros NG. destruct (HGB0 NG) as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [clear - X2 G2; lia|]. split; [unfold apart; clear - X2 HHI; lia|]. split; assumption. }
  assert (W48 : wrA M (sp - 48) 48) by (eapply wr_sub; [exact W|clear; lia|clear; lia]).
  assert (Wq : wrA M (0x13c8b0 + 152) 40) by (apply art_img_wr; lia).
  destruct (art_drain_pre regs M rom raw sp (t + 80) L F B bytes GL GB gbytes H1 H2 H10 H11 ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) ltac:(clear - Gt0; lia) ltac:(clear - Gt1 G2; lia)
              ltac:(clear - Gti; lia) Ac HL HF HB Hby Hgb ltac:(clear - Hqb Eqb; unfold gq in *; lia) HGL HGL' HGB W48 Wc Wq Clk CL CF CB Cby CGL CGB Cgb)
    as (r1 & RUN1 & R1_2 & R1_10 & RK1).
  destruct (art_drain_mem_facts M raw regs sp (t + 80) L F B bytes GL GB gbytes ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) ltac:(clear - Gt0; lia) ltac:(clear - Gt1 G2; lia)
              ltac:(clear - Gti; lia) Ac HGB W48 Wc Wq)
    as (GR1 & AG1 & C1 & C2 & C3 & C4 & C160 & C176 & C184 & C168a & C168b & F1 & F8 & F9 & F18 & F19 & LK1).
  fold M1 in RUN1, GR1, AG1, C160, C176, C184, F1, F8, F9, F18, F19, LK1.
  assert (GAPi : forall a n, (a + n <= 0x13c8b0 + 152 \/ 0x13c8b0 + 192 <= a) -> 0 <= n -> a + n <= 0x696000 -> apart a n (t + 80) 32 -> art_gap (art_drain_W5 sp (t + 80) GL GB) a n).
  { intros a n Hq Hn0 Han At. unfold apart in At. unfold art_drain_W5. cbn [art_gap fst snd]. unfold apart. destruct (Z.eqb_spec GL 0) as [EG|NG].
    - clear - Hq Hn0 Han At HHI G1. repeat split; try exact I; lia.
    - destruct (HGB0 NG) as (X1 & _). clear - Hq Hn0 Han At HHI G1 X1. repeat split; try exact I; lia. }
  assert (Cmax1 : cellA M1 (0x13c8b0 + 64) 8 (2 ^ 28)).
  { apply (art_cell_tr _ M M1 _ 8%nat _ AG1); [apply GAPi; [left; cbn; clear; lia|cbn; clear; lia|cbn; clear; lia|unfold apart; cbn; clear - Gti; lia]|lia|cbn; lia|exact Cmax]. }
  assert (Cmin1 : cellA M1 (0x13c8b0 + 72) 8 msz).
  { apply (art_cell_tr _ M M1 _ 8%nat _ AG1); [apply GAPi; [left; cbn; clear; lia|cbn; clear; lia|cbn; clear; lia|unfold apart; cbn; clear - Gti; lia]|lia|cbn; lia|exact Cmin]. }
  pose proof (art_drain_rcy_fn r1 M1 rom raw sp (gbytes + bytes) msz (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) R1_2 R1_10
                ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) ltac:(clear - Hbig Hqb Eqb; unfold gq in *; lia) Hmsz (u64_range _) (u64_range _) (u64_range _) (u64_range _)
                ltac:(clear - HHI G1; lia) C184 Cmax1 Cmin1 LK1 (art_img_wr M1 (0x13c8b0 + 152) 4 ltac:(lia) ltac:(lia) ltac:(lia)) F1 F8 F9 F18 F19) as RUN2.
  eapply ar_steps; [exact RUN1|]. eapply ar_steps; [exact RUN2|].
  match goal with |- aruns _ _ _ _ _ (mkst ?r _ _ _) => set (r2 := r) end.
  assert (R2K : forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 x = getr regs x).
  { intros x Hx. unfold r2. cbn [In] in Hx.
    destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; first [apply Z_to_bv_bv_unsigned | apply RK1; inl]. }
  apply (art_recycle_locked_aruns pre rest Q log r2 M1 rom raw sp msz cbs B G).
  - unfold r2. gres. reflexivity.
  - exact Hret.
  - unfold r2. gres. reflexivity.
  - rewrite R2K by inl. exact H4.
  - unfold r2. gres. exact R1_10.
  - unfold r2. gres. reflexivity.
  - unfold r2. gres. rewrite RK1 by inl. exact H12.
  - unfold r2. gres. rewrite RK1 by inl. exact H13.
  - clear - HHI. lia.
  - exact HS47.
  - exact Hcbs.
  - exact Hnp.
  - exact OKS.
  - exact Hmerge.
  - exact Hqb.
  - split; [clear - Hmsz; lia|exact Hmn].
  - exact SEP.
  - exact QIN.
  - exact Q24.
  - exact SEPR.
  - exact SEPI.
  - eapply wr_grows; [exact GR1|]. eapply wr_sub; [exact W|clear; lia|clear; lia].
  - exact WL.
  - exact LK1.
  - fold gq. rewrite Eqb. exact C184.
  - fold gq. rewrite Elen. exact C160.
  - exact Cgf.
  - exact C176.
  - exact QL.
  - exact INV0.
  - exact PRE.
  - exact RSEP.
  - exact MEM.
  - exact EV.
  - intros regs' M' R1' R2' K' INV' TR D160 D168 D184 D176a D176b Dlk QL' Hrest.
    apply (K regs' M'); try assumption.
    intros x Hx. rewrite (K' x Hx). exact (R2K x Hx).
Qed.
End DrainRcy.
