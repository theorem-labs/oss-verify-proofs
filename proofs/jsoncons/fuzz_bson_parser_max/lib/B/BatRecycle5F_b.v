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
     BatRecycle2C_b BatRecycle3L_b BatRecycle4P_b BatRecycle4S_b BatRecycle5A_b BatRecycle5B_b BatRecycle5R_b BatRecycle5I_b BatRecycle5G_b BatRecycle5T_b BatRecycle5C_b BatRecycle5D_b BatRecycle5E_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_gap_app : forall W1 W2 a n, art_gap W1 a n -> art_gap W2 a n -> art_gap (W1 ++ W2) a n.
Proof. induction W1 as [|p r IH]; intros W2 a n G1 G2; cbn [app art_gap] in *; [exact G2|]. destruct G1 as (A & G1). split; [exact A|exact (IH W2 a n G1 G2)]. Qed.
Lemma art_gap_links : forall (l : list art_qbatch) a n, Forall (fun b => apart a n (qb_addr b) 8) l -> art_gap (map (fun b => (qb_addr b, 8)) l) a n.
Proof. induction l as [|b r IH]; intros a n F; cbn [map art_gap fst snd]; [exact I|]. inversion F as [|? ? Hb Hr]; subst. split; [exact Hb|exact (IH a n Hr)]. Qed.

Section Recycle.
Variables (HI t ctx tp key tsd spb ris qs parr : Z).
Hypothesis GEO : art_geo HI t ctx tp tsd spb ris qs.
Hypothesis Htp0 : 0x661b28 <= tp - 88.
Hypothesis Htsd0 : 0x661b28 <= tsd.

#[local] Abbreviation INV := (art_rcy_inv HI t ctx tp key tsd spb ris qs parr).

(* [comment removed for export] *)
Definition art_rcy_W (l : list art_qbatch) : list (Z * Z) := [(HI, 2 ^ 64 - HI); (0x13c8b0 + 152, 40)] ++ map (fun b => (qb_addr b, 8)) l.
(* [comment removed for export] *)
Definition art_rcy_W2 (sp : Z) (l : list art_qbatch) : list (Z * Z) := [(sp - 80, 80); (0x13c8b0 + 152, 40)] ++ map (fun b => (qb_addr b, 8)) l.
Definition art_qin24 (b : art_qbatch) : Prop := spb + 24 * 2 ^ 32 <= qb_addr b /\ qb_addr b + 8192 <= spb + 24 * 2 ^ 32 + 3758096384.

#[using="Type"] Lemma art_rcy_W_gap : forall l a n, Forall art_qin24 l -> a + n <= HI ->
  (a + n <= 0x13c8b0 + 152 \/ 0x13c8b0 + 192 <= a) -> (a + n <= spb + 24 * 2 ^ 32 \/ spb + 24 * 2 ^ 32 + 3758096384 <= a) -> art_gap (art_rcy_W l) a n.
Proof.
  intros l a n F Hhi Hq Hk. unfold art_rcy_W. apply art_gap_app.
  - cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia.
  - apply art_gap_links. apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) F b Hb) as (B0 & B1). unfold apart. lia.
Qed.

#[using="GEO Htp0 Htsd0"] Lemma art_rcy_inv_trq : forall l nt G (M M' : word -> option byte), Forall art_qin24 l -> mem_grows M M' -> art_agree (art_rcy_W l) M M' -> INV nt G M -> INV nt G M'.
Proof.
  intros l nt G M M' FL GRW AG INV0.
  destruct INV0 as (ICLS & IPH & IPC & ILAY & ITSD & IGOT & IMAG & IWT & IWSH & ISC & ISG & IBK & IPK).
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & Gti & Gts & Atk & (qt & Et) & G13 & G14 & Gci & Gcs & Ack & Atc & G19 & G20 & G21 & G22).
  pose proof ITSD as (_ & _ & _ & _ & _ & _ & _ & Hkey & _).
  pose proof ISG as (Gp1 & Gp2 & Gp3 & Gp4 & Apt & Apc & GB & GD).
  assert (GAP : forall a n, a + n <= HI -> (a + n <= 0x13c8b0 + 152 \/ 0x13c8b0 + 192 <= a) -> (a + n <= spb + 24 * 2 ^ 32 \/ spb + 24 * 2 ^ 32 + 3758096384 <= a) -> art_gap (art_rcy_W l) a n)
    by (intros a n; exact (art_rcy_W_gap l a n FL)).
  unfold art_rcy_inv.
  split.
  { intros c' Hc'. destruct (ICLS c' Hc') as (R1 & O1 & L1 & Rm1).
    pose proof O1 as (L16' & _ & _ & _ & _ & _ & _ & (_ & Hmfa1') & Hnf4' & _ & _).
    split; [|split; [exact O1|split; [exact L1|exact Rm1]]].
    apply (art_cls_rep_tr _ (t + 208) spb ris c' (rg_cls G c') M M' ltac:(clear - G7; lia) ltac:(clear - G8 G2; lia) ltac:(clear - Hc'; lia) L16'
             ltac:(clear - G4 Eris Hc'; lia) ltac:(clear - G6 G2 Eris Hc'; lia) ltac:(clear - G4 Hc'; lia) ltac:(clear - G6 G2 Eris Hc'; lia) ltac:(clear - Hnf4' Hmfa1'; lia) GRW AG); [| | | |exact R1];
      apply GAP; unfold apart in Atk; clear - G1 G2 Espb G4 Eris G6 G7 G8 Gti Atk Hc' Hnf4' Hmfa1'; lia. }
  split. { apply (art_pc_hdr_tr _ (t + 208) true M M' ltac:(clear - G7; lia) ltac:(clear - G8 G2; lia) AG); [|exact IPH]. intros c' Hc'. apply GAP; unfold apart in Atk; clear - G1 G4 G7 G8 Gti Atk Hc'; lia. }
  split. { apply (art_prim_consts_tr _ M M' spb ris AG); [| | | | |exact IPC]; apply GAP; clear - G1 G4; lia. }
  split. { apply (art_layout_tr _ M M' AG); [| | |exact ILAY]; apply GAP; clear - G1 G4; lia. }
  split. { apply (art_tsd_tr _ M M' tp key tsd ctx t AG); [| | | |exact ITSD]; apply GAP; unfold apart in Ack; clear - G1 G4 G13 G14 Gci Ack G19 G20 G21 G22 Hkey Htp0 Htsd0; lia. }
  split. { apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact IGOT]. apply GAP; clear - G1 G4; lia. }
  split. { apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact IMAG]. apply GAP; clear - G1 G4; lia. }
  split; [eapply wr_grows; [exact GRW|exact IWT]|]. split; [eapply wr_grows; [exact GRW|exact IWSH]|].
  split. { apply (art_sec_cells_tr _ M M' HI t ctx parr (rg_bl G) ISG ltac:(clear - G2; lia) GRW AG); [| | | |exact ISC].
           - apply GAP; clear - G1 G4; lia.
           - destruct ISC as (_ & _ & _ & CL & _). apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact CL]. apply GAP; clear - G1 G4; lia.
           - apply GAP; [clear - Gp2; lia|clear - Gp1; lia|]. unfold apart in IPK. clear - IPK Gp1 G4. lia.
           - intros b Hb. destruct (GB _ Hb) as (_ & _ & Hs & Hb0 & Hb1' & _). pose proof (IBK b Hb) as AB. unfold apart in AB. apply GAP; [clear - Hs Hb1'; lia|clear - Hb0; lia|clear - AB Hs; lia]. }
  split; [exact ISG|]. split; [exact IBK|exact IPK].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_rcy_head_mem_facts : forall (M : word -> option byte) sp raw regs, 0x696000 + 80 <= sp -> sp < 2 ^ 64 ->
  let M1 := art_rcy_head_mem M sp raw regs in
  mem_grows M M1 /\ art_agree [(sp - 80, 80); (0x13c8b0 + 152, 4)] M M1
  /\ cellA M1 (sp - 8) 8 (U raw) /\ cellA M1 (sp - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 24) 8 (U (getr regs 9)) /\ cellA M1 (sp - 32) 8 (U (getr regs 18))
  /\ cellA M1 (sp - 40) 8 (U (getr regs 19)) /\ cellA M1 (sp - 48) 8 (U (getr regs 20))
  /\ cellA M1 (sp - 72) 8 0 /\ cellA M1 (sp - 56) 8 0 /\ cellA M1 (0x13c8b0 + 152) 4 257.
Proof.
  intros M sp raw regs Hsp Hsp' M1. unfold M1, art_rcy_head_mem.
  split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia|]. repeat split; zcell.
Qed.

#[using="Type"] Lemma art_firstn_map_app : forall (A B : Type) (f : A -> B) l1 l2, firstn (length l1) (map f (l1 ++ l2)) = map f l1.
Proof. intros A B f l1 l2. rewrite map_app. rewrite <- (length_map f l1). rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. apply app_nil_r. Qed.
#[using="Type"] Lemma art_skipn_map_app : forall (A B : Type) (f : A -> B) l1 l2, skipn (length l1) (map f (l1 ++ l2)) = map f l2.
Proof. intros A B f l1 l2. rewrite map_app. rewrite <- (length_map f l1). rewrite skipn_app, Nat.sub_diag, skipn_all. reflexivity. Qed.

(* [comment removed for export] *)
#[using="ctx tp tsd qs GEO"] Lemma art_rels_fp_gap_lo : forall sp1 es G a n, art_rels_pre G es -> (forall b, In b (rg_bl G) -> 0x696000 <= fst b) -> 0x696000 <= parr -> HI <= sp1 - 320 ->
  0 <= n -> a + n <= 0x696000 -> (a + n <= 0x13c618 \/ 0x13c8a8 <= a) -> apart a n t 4096 ->
  art_gap (art_rels_fp t spb ris parr sp1 G es) a n.
Proof.
  intros sp1 es. induction es as [|e r IH]; intros G a n PRE BL Hparr HHI Hn0 Hlo Hsec At; cbn [art_rels_fp]; [exact I|]. destruct PRE as (Pe & Pr).
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & _).
  apply art_gap_app; [|apply IH; [exact Pr|intros b Hb; apply BL; exact (art_rel_step_bl_in e G b Hb)|exact Hparr|exact HHI|exact Hn0|exact Hlo|exact Hsec|exact At]].
  unfold apart in At. destruct e as [c w d b1 n'|mb ms m b1 n'|wb]; cbn [art_rel_fp art_rel_pre] in *.
  - destruct Pe as (Hc & (Hw0 & _) & _ & Hd & _).
    assert (Hq : 0 <= (spb + c * 2 ^ 32 + 16 * w + d + 16) / 8) by (apply Z.div_pos; [clear - G4 Hc Hw0 Hd; lia|clear; lia]).
    unfold art_cbr_prim_fp, art_lcd_fp, SB. cbn [art_gap app fst snd]. unfold apart. clear - Hq Hc Hw0 Hd At HHI G1 G4 Eris Hlo Hn0. repeat split; try exact I; lia.
  - destruct Pe as (Hi0 & _). pose proof (BL _ Hi0) as Hmb. cbn [fst] in Hmb.
    assert (Hlast : 0x696000 <= fst (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0))).
    { apply BL. apply nth_In. destruct (rg_bl G); [contradiction|cbn [length]; lia]. }
    assert (Hq : 0 <= mb / 8) by (apply Z.div_pos; [clear - Hmb; lia|clear; lia]).
    unfold art_cbr_sec_fp, art_secd_fp, SB. cbn [art_gap app fst snd]. unfold apart. clear - Hq Hmb Hlast At HHI G1 Hparr Hlo Hsec Hn0. repeat split; try exact I; lia.
  - destruct Pe as ((Hw0 & _) & _).
    unfold art_lcd_fp. cbn [art_gap app fst snd]. unfold apart. clear - Hw0 At HHI G1 G4 Eris Hlo Hn0. repeat split; try exact I; lia.
Qed.

Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[local] Abbreviation TRX := (art_rcy_trx HI t spb ris parr).
#[local] Abbreviation rbq := (art_rb_q spb).

(* [comment removed for export] *)
Definition art_rcy_trq (sp : Z) (G : art_rg) (work : list art_rel) (gq : list art_qbatch) (M M' : word -> option byte) : Prop :=
  (forall x : word, sp <= U x -> M' x = M x)
  /\ (forall a n, 0 <= a -> a + n < 2 ^ 64 -> (HI <= a \/ Forall (fun e => art_zapart spb e a n) work) -> wrA M a n -> wrA M' a n)
  /\ (forall zlo zlen, 0 < zlen -> zlo + zlen <= HI -> art_rcy_prot spb G zlo zlen -> Forall (fun e => art_zapart spb e zlo zlen) work ->
        Forall (fun b => apart zlo zlen (qb_addr b) 8) gq -> (zlo + zlen <= 0x13c8b0 + 152 \/ 0x13c8b0 + 192 <= zlo) ->
        art_rcy_prot spb (art_rel_steps work G) zlo zlen
        /\ forall a (k : nat) v, zlo <= a -> a + Z.of_nat k <= zlo + zlen -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA M' a k v)
  /\ art_agree (art_rcy_W2 sp gq ++ art_rels_fp t spb ris parr (sp - 192) G work ++ [(sp - 192, 144)]) M M'.

#[using="GEO Htp0 Htsd0"] Theorem art_recycle_aruns : forall (pre rest : list art_rbatch) (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
    (sp mn cbs GL : Z) (G : art_rg),
  let gq := map rbq (pre ++ rest) in
  let work := art_rb_work pre in
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 0x13c8b0 -> getr regs 11 = Z_to_bv 64 mn ->
  getr regs 12 = Z_to_bv 64 (t + 208) -> getr regs 13 = Z_to_bv 64 cbs ->
  HI <= sp - 512 -> sp < 2 ^ 47 -> 0 <= cbs < 2 ^ 64 ->
  art_rcy_npop mn gq = length pre -> Forall (art_rb_ok) pre ->
  16384 * Z.of_nat (length gq) <= art_qbytes gq -> art_qbytes gq < 2 ^ 54 -> 0 <= mn < art_qbytes gq ->
  art_qsep gq -> Forall (art_qin HI) gq -> Forall art_qin24 gq ->
  Forall (fun b => Forall (fun e => art_zapart spb e (qb_addr b) 8192) work) (map rbq rest) ->
  Forall (fun e => art_rel_is_item e -> Forall (fun b => art_zapart spb e (qb_addr b) 8) gq) work ->
  wrA M (sp - 512) 512 -> Forall (fun b => wrA M (qb_addr b) 8) gq ->
  cellA M (0x13c8b0 + 152) 4 256 -> cellA M (0x13c8b0 + 184) 8 (art_qbytes gq) -> cellA M (0x13c8b0 + 160) 8 (Z.of_nat (length gq)) -> cellA M (0x13c8b0 + 168) 8 (art_qhead gq) ->
  cellA M (0x13c8b0 + 176) 8 GL -> art_qlist M gq (art_qhead gq) GL ->
  INV (Z.of_nat (length work)) G M -> art_rels_pre G work -> art_rels_sep spb work -> Forall (fun e => art_rel_mem spb e M) work ->
  art_evok_list EVOK log (art_rels_events work) ->
  (forall regs' (M' : word -> option byte),
      getr regs' 1 = raw -> getr regs' 2 = Z_to_bv 64 sp -> (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
      INV 0 (art_rel_steps work G) M' -> art_rcy_trq sp G work gq M M' ->
      cellA M' (0x13c8b0 + 160) 8 (Z.of_nat (length rest)) -> cellA M' (0x13c8b0 + 168) 8 (art_qhead (map rbq rest)) -> cellA M' (0x13c8b0 + 184) 8 (art_qbytes (map rbq rest)) ->
      (rest = [] -> cellA M' (0x13c8b0 + 176) 8 0) -> (rest <> [] -> cellA M' (0x13c8b0 + 176) 8 GL) -> cellA M' (0x13c8b0 + 152) 4 0 ->
      art_qlist M' (map rbq rest) (art_qhead (map rbq rest)) GL -> art_qbytes (map rbq rest) <= mn ->
      Q (log ++ art_rels_events work) (mkst regs' raw M' rom)) ->
  aruns ASEGS EVOK GR Q log (mkst regs (0x54454 : word) M rom).
Proof.
  intros pre rest Q log regs M rom raw sp mn cbs GL G gq work H1 Hret H2 H4 H10 H11 H12 H13 HHI HS47 Hcbs Hnp OKS Hmerge Hqb Hmn SEP QIN Q24 SEPR SEPI W WL Clk Cgb Ccnt Cgf Cgl QL INV0 PRE RSEP MEM EV K.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & Gti & _).
  assert (QB : forall b, In b gq -> 0x696000 <= qb_addr b /\ qb_addr b + 8192 <= HI) by (intros b Hb; destruct (proj1 (Forall_forall _ _) QIN b Hb) as (X1 & X2 & _); split; assumption).
  assert (NEg : gq <> []) by (intros E; rewrite E in Hmn; cbn in Hmn; lia).
  assert (Hlen : 1 <= Z.of_nat (length gq)) by (destruct gq; [contradiction|cbn [length]; lia]).
  assert (HGF : 0 <= art_qhead gq < 2 ^ 64). { destruct gq as [|b0 r0] eqn:Eg; [contradiction|]. cbn [art_qhead]. destruct (QB b0 (or_introl eq_refl)) as (X1 & X2). clear - X1 X2 G2. lia. }
  (* [comment removed for export] *)
  destruct (art_rcy_head regs M rom raw sp mn (Z.of_nat (length gq)) (art_qbytes gq) (art_qhead gq) H1 H2 H10 H11 ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia)
              ltac:(eapply wr_sub; [exact W|clear; lia|clear; lia]) (art_img_wr M (0x13c8b0 + 152) 4 ltac:(lia) ltac:(lia) ltac:(lia)) Hlen Hmerge ltac:(clear - Hqb; lia) Hmn HGF Clk Cgb Ccnt Cgf)
    as (r1 & RUN1 & R1_2 & R1_10 & R1_11 & R1_14 & R1_15 & R1_16 & R1_5 & K1).
  destruct (art_rcy_head_mem_facts M sp raw regs ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia)) as (GR1 & AG1 & F1 & F8 & F9 & F18 & F19 & F20 & T8 & T24 & LK1).
  set (M1 := art_rcy_head_mem M sp raw regs) in *.
  eapply ar_steps; [exact RUN1|].
  assert (GAP1 : forall a n, 0x696000 <= a -> a + n <= HI -> art_gap [(sp - 80, 80); (0x13c8b0 + 152, 4)] a n).
  { intros a n Ha Hn. cbn [art_gap fst snd]. unfold apart. clear - Ha Hn HHI. repeat split; try exact I; lia. }
  (* [comment removed for export] *)
  assert (QG1 : Forall (art_qgeo [(sp - 80, 80); (0x13c8b0 + 152, 4)]) gq).
  { apply Forall_forall. intros b Hb. destruct (QB b Hb) as (X1 & X2). split; [clear - X1; lia|]. split; [clear - X2 G2; lia|]. apply GAP1; [exact X1|exact X2]. }
  pose proof (art_rcy_deq_run gq [] r1 M1 rom HI (sp - 80) mn GL 0 R1_2 R1_10 R1_11 R1_14 R1_15 R1_16 R1_5 Hmn SEP QIN ltac:(clear - G1; lia) ltac:(clear - HHI; lia) ltac:(clear - HS47; lia)
                ltac:(cbn [app]; clear - Hmerge Hqb; lia) ltac:(cbn [app]; clear - Hqb; lia)
                ltac:(eapply wr_grows; [exact GR1|]; eapply wr_sub; [exact W|clear; lia|clear; lia]) (art_img_wr M1 (0x13c8b0 + 160) 32 ltac:(lia) ltac:(lia) ltac:(lia))
                ltac:(cbn [app]; eapply Forall_impl; [|exact WL]; intros b Wb; eapply wr_grows; [exact GR1|exact Wb])
                ltac:(apply (art_cell_tr _ M M1 _ 8%nat _ AG1); [cbn [art_gap fst snd]; unfold apart; clear - HHI G1; repeat split; try exact I; lia|lia|cbn; lia|exact Cgb])
                ltac:(apply (art_cell_tr _ M M1 _ 8%nat _ AG1); [cbn [art_gap fst snd]; unfold apart; clear - HHI G1; repeat split; try exact I; lia|lia|cbn; lia|exact Cgl])
                ltac:(replace (sp - 80 + 24) with (sp - 56) by lia; exact T24) ltac:(replace (sp - 80 + 8) with (sp - 72) by lia; exact T8)
                ltac:(intros X; exfalso; apply X; reflexivity) ltac:(reflexivity) (art_qlist_tr _ M M1 gq _ _ AG1 QG1 QL)) as DEQ.
  assert (Efp : firstn (length pre) gq = map rbq pre) by (unfold gq; apply art_firstn_map_app).
  assert (Esk : skipn (length pre) gq = map rbq rest) by (unfold gq; apply art_skipn_map_app).
  rewrite Hnp in DEQ. cbn [app] in DEQ. rewrite !Efp, !Esk in DEQ.
  destruct DEQ as (r2 & M2 & RUN2 & R2_14 & R2_6 & K2 & GR2 & AG2 & D160 & D168 & D184 & D176a & D176b & Dt8 & Dt24 & QLpre & QLrest & Hrest & Hk).
  eapply ar_steps; [exact RUN2|].
  (* [comment removed for export] *)
  assert (NEp : pre <> []) by (intros E; rewrite E in Hk; cbn in Hk; lia).
  assert (NEpq : map rbq pre <> []) by (intros E; apply NEp; apply map_eq_nil in E; exact E).
  assert (INpre : forall b, In b (map rbq pre) -> In b gq) by (intros b Hb; unfold gq; rewrite map_app; apply in_or_app; left; exact Hb).
  assert (INrest : forall b, In b (map rbq rest) -> In b gq) by (intros b Hb; unfold gq; rewrite map_app; apply in_or_app; right; exact Hb).
  destruct (art_qlast_in (map rbq pre) NEpq) as (bl0 & Hbl0 & Ebl0). destruct (QB bl0 (INpre bl0 Hbl0)) as (L0 & L1).
  assert (GAP2 : forall a n, (a + n <= 0x13c8b0 + 160 \/ 0x13c8b0 + 192 <= a) -> (a + n <= sp - 80 \/ sp - 48 <= a) -> Forall (fun b => apart a n (qb_addr b) 8) gq ->
                 art_gap ([(0x13c8b0 + 160, 32); (sp - 80, 32)] ++ map (fun b => (qb_addr b, 8)) gq) a n).
  { intros a n Hq Ht Hl. apply art_gap_app; [|apply art_gap_links; exact Hl]. cbn [art_gap fst snd]. unfold apart. clear - Hq Ht. repeat split; try exact I; lia. }
  assert (LNK_hi : forall a n, HI <= a -> Forall (fun b => apart a n (qb_addr b) 8) gq).
  { intros a n Ha. apply Forall_forall. intros b Hb. destruct (QB b Hb) as (X1 & X2). unfold apart. clear - Ha X2. lia. }
  assert (LNK_lo : forall a n, a + n <= 0x696000 -> Forall (fun b => apart a n (qb_addr b) 8) gq).
  { intros a n Ha. apply Forall_forall. intros b Hb. destruct (QB b Hb) as (X1 & X2). unfold apart. clear - Ha X1. lia. }
  assert (LK2 : cellA M2 (0x13c8b0 + 152) 4 257).
  { apply (art_cell_tr _ M1 M2 _ 4%nat _ AG2); [apply GAP2; [left; clear; lia|left; clear - HHI G1; lia|apply LNK_lo; clear; lia]|lia|cbn; lia|exact LK1]. }
  assert (Hkp : 0 <= Z.of_nat (length ([] ++ map rbq pre)) < 2 ^ 64).
  { cbn [app]. rewrite length_map. pose proof Hmerge as Hm'. pose proof Hqb as Hq'. unfold gq in Hm', Hq'. rewrite length_map, length_app in Hm'. clear - Hm' Hq'. lia. }
  destruct (art_rcy_tail r2 M2 rom (sp - 80) (Z.of_nat (length ([] ++ map rbq pre))) (art_qlast ([] ++ map rbq pre)) ltac:(rewrite K2 by inl; exact R1_2) ltac:(rewrite K2 by inl; exact R1_10) R2_14 R2_6
              ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) Hkp ltac:(cbn [app]; rewrite Ebl0; clear - L0 L1 G2; lia)
              ltac:(eapply wr_grows; [exact GR2|]; eapply wr_grows; [exact GR1|]; eapply wr_sub; [exact W|clear; lia|clear; lia]) (art_img_wr M2 (0x13c8b0 + 152) 4 ltac:(lia) ltac:(lia) ltac:(lia)))
    as (r3 & RUN3 & R3_1 & R3_11 & K3).
  destruct (art_rcy_tail_mem_facts M2 (sp - 80) (Z.of_nat (length ([] ++ map rbq pre))) (art_qlast ([] ++ map rbq pre)) ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) LK2)
    as (GR3 & AG3 & T0 & T16 & LK3).
  set (M3 := art_rcy_tail_mem M2 (sp - 80) (Z.of_nat (length ([] ++ map rbq pre))) (art_qlast ([] ++ map rbq pre))) in *.
  cbn [app] in T0, T16. rewrite length_map in T0.
  eapply ar_steps; [exact RUN3|].
  assert (GAP3 : forall a n, (a + n <= sp - 80 \/ (sp - 72 <= a /\ a + n <= sp - 64) \/ sp - 56 <= a) -> (a + n <= 0x13c8b0 + 152 \/ 0x13c8b0 + 156 <= a) ->
                 art_gap [(sp - 80, 8); (sp - 80 + 16, 8); (0x13c8b0 + 152, 4)] a n).
  { intros a n Ht Hq. cbn [art_gap fst snd]. unfold apart. clear - Ht Hq. repeat split; try exact I; lia. }
  (* [comment removed for export] *)
  assert (GR03 : mem_grows M M3) by (eapply mem_grows_trans; [exact GR1|]; eapply mem_grows_trans; [exact GR2|exact GR3]).
  assert (AG03 : art_agree (art_rcy_W gq) M M3).
  { eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ AG1 (art_agree_trans _ _ _ _ _ AG2 AG3))|]. intros z Hz Ho. unfold art_rcy_W in Ho. apply art_out_app in Ho. destruct Ho as (Ho1 & Ho2).
    cbn [art_out fst snd] in Ho1.
    apply art_out_app. split; [cbn [art_out fst snd]; clear - Ho1 HHI Hz; repeat split; try exact I; lia|]. apply art_out_app. split.
    + cbn [art_out fst snd]. split; [clear - Ho1 HHI Hz; lia|]. split; [clear - Ho1 HHI Hz; lia|exact Ho2].
    + cbn [art_out fst snd]. clear - Ho1 HHI Hz. repeat split; try exact I; lia. }
  assert (AG03' : art_agree (art_rcy_W2 sp gq) M M3).
  { eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ AG1 (art_agree_trans _ _ _ _ _ AG2 AG3))|]. intros z Hz Ho. unfold art_rcy_W2 in Ho. apply art_out_app in Ho. destruct Ho as (Ho1 & Ho2).
    cbn [art_out fst snd] in Ho1.
    apply art_out_app. split; [cbn [art_out fst snd]; clear - Ho1 HHI Hz; repeat split; try exact I; lia|]. apply art_out_app. split.
    + cbn [art_out fst snd]. split; [clear - Ho1 HHI Hz; lia|]. split; [clear - Ho1 HHI Hz; lia|exact Ho2].
    + cbn [art_out fst snd]. clear - Ho1 HHI Hz. repeat split; try exact I; lia. }
  assert (INV3 : INV (Z.of_nat (length work)) G M3) by exact (art_rcy_inv_trq gq _ G M M3 Q24 GR03 AG03 INV0).
  pose proof (art_rels_pre_static _ _ PRE) as STall.
  assert (MEM3 : Forall (fun e => art_rel_mem spb e M3) work).
  { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) MEM e He) as Me. pose proof (proj1 (Forall_forall _ _) STall e He) as Se.
    destruct e as [c w d b1 n'|mb ms m b1 n'|wb]; [| |exact I].
    - destruct (art_rel_static_prot HI t ctx tp key tsd spb ris qs parr _ G M _ INV0 Se) as (Pz & Hz & _ & Z1 & Z2).
      destruct (art_rcy_prot_below HI t ctx tp tsd spb ris qs parr GEO G _ _ ltac:(destruct INV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ISG & IBK & IPK); exact (conj ISG (conj IBK IPK))) Pz) as (Lo & Hi).
      pose proof (proj1 (Forall_forall _ _) SEPI _ He I) as SQ.
      apply (art_rel_mem_tr spb G _ M M3 Se); [|exact Me]. intros a kk v Ha Hkk C. apply (art_cell_tr _ M M3 a kk v AG03); [|clear - Ha Lo; lia|clear - Hkk Hi G2; lia|exact C].
      unfold art_rcy_W. apply art_gap_app; [cbn [art_gap fst snd]; unfold apart; clear - Ha Hkk Lo Hi; repeat split; try exact I; lia|]. apply art_gap_links.
      eapply Forall_impl; [|exact SQ]. intros b Ab. unfold art_zapart, apart in Ab |- *. clear - Ab Ha Hkk Z1 Z2. lia.
    - destruct (art_rel_static_prot HI t ctx tp key tsd spb ris qs parr _ G M _ INV0 Se) as (Pz & Hz & _ & Z1 & Z2).
      destruct (art_rcy_prot_below HI t ctx tp tsd spb ris qs parr GEO G _ _ ltac:(destruct INV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ISG & IBK & IPK); exact (conj ISG (conj IBK IPK))) Pz) as (Lo & Hi).
      pose proof (proj1 (Forall_forall _ _) SEPI _ He I) as SQ.
      apply (art_rel_mem_tr spb G _ M M3 Se); [|exact Me]. intros a kk v Ha Hkk C. apply (art_cell_tr _ M M3 a kk v AG03); [|clear - Ha Lo; lia|clear - Hkk Hi G2; lia|exact C].
      unfold art_rcy_W. apply art_gap_app; [cbn [art_gap fst snd]; unfold apart; clear - Ha Hkk Lo Hi; repeat split; try exact I; lia|]. apply art_gap_links.
      eapply Forall_impl; [|exact SQ]. intros b Ab. unfold art_zapart, apart in Ab |- *. clear - Ab Ha Hkk Z1 Z2. lia. }
  (* [comment removed for export] *)
  assert (QGpre : forall W', (forall b, In b gq -> art_gap W' (qb_addr b) 8192) -> Forall (art_qgeo W') (map rbq pre)).
  { intros W' HW. apply Forall_forall. intros b Hb. destruct (QB b (INpre b Hb)) as (X1 & X2). split; [clear - X1; lia|]. split; [clear - X2 G2; lia|exact (HW b (INpre b Hb))]. }
  assert (QGrest : forall W', (forall b, In b gq -> art_gap W' (qb_addr b) 8192) -> Forall (art_qgeo W') (map rbq rest)).
  { intros W' HW. apply Forall_forall. intros b Hb. destruct (QB b (INrest b Hb)) as (X1 & X2). split; [clear - X1; lia|]. split; [clear - X2 G2; lia|exact (HW b (INrest b Hb))]. }
  assert (GAP3r : forall b, In b gq -> art_gap [(sp - 80, 8); (sp - 80 + 16, 8); (0x13c8b0 + 152, 4)] (qb_addr b) 8192).
  { intros b Hb. destruct (QB b Hb) as (X1 & X2). cbn [art_gap fst snd]. unfold apart. clear - X1 X2 HHI. repeat split; try exact I; lia. }
  assert (Hqpre : 0 <= art_qbytes (map rbq pre) <= art_qbytes gq).
  { unfold gq. rewrite map_app, art_qbytes_app. assert (QIN' : Forall (art_qin HI) (map rbq pre) /\ Forall (art_qin HI) (map rbq rest)) by (unfold gq in QIN; rewrite map_app in QIN; apply Forall_app in QIN; exact QIN).
    destruct QIN' as (Q1' & Q2'). pose proof (art_qbytes_nonneg HI _ Q1'). pose proof (art_qbytes_nonneg HI _ Q2'). lia. }
  apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st Hst; exact Hst].
  apply (art_dorecycle_aruns HI t ctx tp key tsd spb ris qs parr EVOK GR GEO Htp0 Htsd0 pre (fun lg st => aruns ASEGS EVOK GR Q lg st) log r3 M3 rom (0x545c4 : bv 64)%bv (sp - 80) cbs (art_qlast (map rbq pre)) G
           R3_1 ltac:(unfold ret_ok; bveq) ltac:(rewrite K3 by inl; rewrite K2 by inl; exact R1_2) ltac:(rewrite K3 by inl; rewrite K2 by inl; rewrite K1 by inl; exact H4) R3_11
           ltac:(rewrite K3 by inl; rewrite K2 by inl; rewrite K1 by inl; exact H12) ltac:(rewrite K3 by inl; rewrite K2 by inl; rewrite K1 by inl; exact H13)
           ltac:(clear - HHI; lia) ltac:(clear - HS47; lia) Hcbs NEp OKS ltac:(clear - Hqpre Hqb; lia)
           ltac:(eapply wr_grows; [exact GR03|]; eapply wr_sub; [exact W|clear; lia|clear; lia]) ltac:(eapply wr_grows; [exact GR03|]; eapply wr_sub; [exact W|clear; lia|clear; lia])
           T0
           ltac:(apply (art_cell_tr _ M2 M3 _ 8%nat _ AG3); [apply GAP3; [right; left; cbn; clear; lia|right; cbn; clear - HHI G1; lia]|clear - HHI G1; lia|cbn; clear - HS47; lia|exact Dt8])
           ltac:(apply (art_cell_tr _ M2 M3 _ 8%nat _ AG3); [apply GAP3; [right; right; cbn; clear; lia|right; cbn; clear - HHI G1; lia]|clear - HHI G1; lia|cbn; clear - HS47; lia|exact Dt24])
           (art_qlist_tr _ M2 M3 _ _ _ AG3 (QGpre _ GAP3r) QLpre) INV3 PRE RSEP MEM3 EV).
  intros r4 M4 R4_2 K4 INV4 TRX4.
  destruct TRX4 as (FR4 & WR4 & PT4 & AG4).
  (* [comment removed for export] *)
  assert (TF : forall a v, sp - 48 <= a -> a + 8 <= sp -> cellA M1 a 8 v -> cellA M4 a 8 v).
  { intros a v Ha Ha' C. apply (art_cell_agree _ M3 M4); [intros x Hx; apply FR4; cbn in Hx; clear - Hx Ha; lia|clear - Ha HHI G1; lia|clear - Ha' HS47; cbn; lia|].
    apply (art_cell_tr _ M2 M3 _ 8%nat _ AG3); [apply GAP3; [right; right; cbn; clear - Ha; lia|right; cbn; clear - Ha HHI G1; lia]|clear - Ha HHI G1; lia|cbn; clear - Ha' HS47; lia|].
    apply (art_cell_tr _ M1 M2 _ 8%nat _ AG2); [apply GAP2; [right; cbn; clear - Ha HHI G1; lia|right; exact Ha|apply LNK_hi; clear - Ha HHI; lia]|clear - Ha HHI G1; lia|cbn; clear - Ha' HS47; lia|exact C]. }
  destruct (art_rcy_epi r4 M4 rom raw sp (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) R4_2 Hret ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia)
              ltac:(apply TF; [clear; lia|clear; lia|exact F1]) ltac:(apply TF; [clear; lia|clear; lia|exact F8]) ltac:(apply TF; [clear; lia|clear; lia|exact F9])
              ltac:(apply TF; [clear; lia|clear; lia|exact F18]) ltac:(apply TF; [clear; lia|clear; lia|exact F19]) ltac:(apply TF; [clear; lia|clear; lia|exact F20]))
    as (r5 & RUN5 & R5_1 & R5_2 & R5_8 & R5_9 & R5_18 & R5_19 & R5_20 & K5).
  eapply ar_steps; [exact RUN5|]. apply ar_done.
  pose proof INV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ISG0 & _). pose proof ISG0 as (Gp1 & _ & _ & _ & _ & _ & GB0 & _).
  assert (GAP4 : forall a n, 0 <= n -> 0x13c8a8 <= a -> a + n <= 0x696000 -> art_gap (art_rels_fp t spb ris parr (sp - 80 - 112) G work ++ [(sp - 80 - 112, sp - 80 + 32 - (sp - 80 - 112))]) a n).
  { intros a n Hn0 Ha Han. apply art_gap_app.
    - apply (art_rels_fp_gap_lo (sp - 80 - 112) work G a n PRE); [intros b Hb; destruct (GB0 b Hb) as (_ & _ & _ & X & _); exact X|exact Gp1|clear - HHI; lia|exact Hn0|exact Han|right; exact Ha|unfold apart; clear - Gti Ha Han; lia].
    - cbn [art_gap fst snd]. unfold apart. clear - Ha Han HHI G1. repeat split; try exact I; lia. }
  assert (TQ : forall a (k : nat) v, 0x13c8b0 + 156 <= a -> a + Z.of_nat k <= 0x13c8b0 + 192 -> cellA M2 a k v -> cellA M4 a k v).
  { intros a k v Ha Hka C. apply (art_cell_tr _ M3 M4 a k v AG4); [apply GAP4; clear - Ha Hka; lia|clear - Ha; lia|clear - Hka; lia|].
    apply (art_cell_tr _ M2 M3 a k v AG3); [apply GAP3; [left; clear - Hka HHI G1; lia|right; exact Ha]|clear - Ha; lia|clear - Hka; lia|exact C]. }
  apply (K r5 M4).
  - exact R5_1.
  - exact R5_2.
  - intros x Hx. cbn [In] in Hx.
    destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
      first [ rewrite R5_8; apply Z_to_bv_bv_unsigned | rewrite R5_9; apply Z_to_bv_bv_unsigned | rewrite R5_18; apply Z_to_bv_bv_unsigned | rewrite R5_19; apply Z_to_bv_bv_unsigned
            | rewrite R5_20; apply Z_to_bv_bv_unsigned
            | rewrite K5 by inl; rewrite K4 by inl; rewrite K3 by inl; rewrite K2 by inl; rewrite K1 by inl; reflexivity ].
  - exact INV4.
  - (* [comment removed for export] *)
    split; [|split; [|split]].
    + intros x Hx. rewrite (FR4 x ltac:(clear - Hx; lia)).
      rewrite (AG3 x ltac:(apply (art_gap_out _ (U x) 1); [apply GAP3; [right; right; clear - Hx; lia|right; clear - Hx HHI G1; lia]|clear; lia])).
      rewrite (AG2 x ltac:(apply (art_gap_out _ (U x) 1); [apply GAP2; [right; clear - Hx HHI G1; lia|right; clear - Hx; lia|apply LNK_hi; clear - Hx HHI; lia]|clear; lia])).
      apply AG1. cbn [art_out fst snd]. clear - Hx HHI G1. repeat split; try exact I; lia.
    + intros a n Ha Hn HHa Wr. apply WR4; [exact Ha|exact Hn|exact HHa|]. eapply wr_grows; [exact GR03|exact Wr].
    + intros zlo zlen Hz Hhi Pz FZ FLk Hq. destruct (PT4 zlo zlen Hz Hhi Pz FZ) as (P' & CT). split; [exact P'|].
      intros a k v Ha Hka Ha0 Hak C. apply (CT a k v Ha Hka Ha0 Hak). apply (art_cell_tr _ M M3 a k v AG03); [|exact Ha0|exact Hak|exact C].
      unfold art_rcy_W. apply art_gap_app; [cbn [art_gap fst snd]; unfold apart; clear - Ha Hka Hhi Hq; repeat split; try exact I; lia|]. apply art_gap_links.
      eapply Forall_impl; [|exact FLk]. intros b Ab. unfold apart in Ab |- *. clear - Ab Ha Hka. lia.
    + eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ AG03' AG4)|]. intros z Hz Ho. apply art_out_app in Ho. destruct Ho as (O1 & O23). apply art_out_app in O23. destruct O23 as (O2 & O3).
      apply art_out_app. split; [exact O1|]. apply art_out_app. split; [replace (sp - 80 - 112) with (sp - 192) by (clear; lia); exact O2|].
      cbn [art_out fst snd] in O3 |- *. clear - O3. repeat split; try exact I; lia.
  - apply TQ; [clear; lia|cbn; clear; lia|]. rewrite length_map in D160. exact D160.
  - apply TQ; [clear; lia|cbn; clear; lia|exact D168].
  - apply TQ; [clear; lia|cbn; clear; lia|exact D184].
  - intros E. apply TQ; [clear; lia|cbn; clear; lia|]. apply D176a. rewrite E. reflexivity.
  - intros NE. apply TQ; [clear; lia|cbn; clear; lia|]. apply D176b. intros E. apply NE. apply map_eq_nil in E. exact E.
  - apply (art_cell_tr _ M3 M4 _ 4%nat _ AG4); [|lia|cbn; lia|exact LK3]. apply art_gap_app.
    + apply (art_rels_fp_gap_lo (sp - 80 - 112) work G _ _ PRE); [intros b Hb; destruct (GB0 b Hb) as (_ & _ & _ & X & _); exact X|exact Gp1|clear - HHI; lia|cbn; lia|cbn; lia|right; cbn; lia|unfold apart; cbn; clear - Gti; lia].
    + cbn [art_gap fst snd]. unfold apart. cbn. clear - HHI G1. repeat split; try exact I; lia.
  - apply (art_qlist_trf M3 M4); [|exact (art_qlist_tr _ M2 M3 _ _ _ AG3 (QGrest _ GAP3r) QLrest)].
    intros b Hb. destruct (QB b (INrest b Hb)) as (X1 & X2). destruct (proj1 (Forall_forall _ _) Q24 b (INrest b Hb)) as (Y1 & Y2).
    destruct (PT4 (qb_addr b) 8192 ltac:(clear; lia) X2 ltac:(left; exists 24; split; [clear; lia|split; [exact Y1|exact Y2]]) (proj1 (Forall_forall _ _) SEPR b Hb)) as (_ & CT).
    intros a k v Ha Hka C. apply (CT a k v Ha Hka); [clear - Ha X1; lia|clear - Hka X2 G2; lia|exact C].
  - exact Hrest.
Qed.
End Recycle.
