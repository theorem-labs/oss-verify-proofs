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
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatPoisonRun_b BatPoison3_b BatInitCache_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b BatFree1_b BatPopulate1_b BatCellEx_b
     BatCls_b BatClsRep_b BatClsGfa2_b BatCARSpec_b BatAllocate3_b BatSecAllocPost_b BatRecycle2C_b BatRecycle3_b BatRecycle3L_b BatRecycle4_b BatRecycle4P_b BatRecycle4S_b BatRecycle5A_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Lemma art_cls_rep_tr_w : forall W ca spb ris c cl (M M' : word -> option byte),
  0 <= ca -> ca + 4096 < 2 ^ 64 -> 1 <= c <= 31 -> (length (cl_cache cl) <= 16)%nat ->
  0 <= ris + 128 * c -> ris + 128 * c + 128 < 2 ^ 64 -> 0 <= spb + c * 2 ^ 32 + 3758096384 -> spb + c * 2 ^ 32 + 3758096384 + 2 ^ 29 < 2 ^ 64 ->
  4 * Z.of_nat (length (cl_free cl)) <= 2 ^ 29 ->
  art_agree W M M' ->
  art_gap W (ca + 80 * c) 4 -> art_gap W (ca + 80 * c + 16) 64 -> art_gap W (ris + 128 * c) 128 ->
  art_gap W (spb + c * 2 ^ 32 + 3758096384) (4 * Z.of_nat (length (cl_free cl))) ->
  wrA M' (ris + 128 * c) 128 -> wrA M' (spb + c * 2 ^ 32 + 3758096384) (cl_mfa cl) -> wrA M' (spb + c * 2 ^ 32) (cl_mu cl) ->
  art_cls_rep ca spb ris c cl M -> art_cls_rep ca spb ris c cl M'.
Proof.
  intros W ca spb ris c cl M M' Hca Hca' Hc Hl Hr Hr' Hfa Hfa' Hnf A G1 G2 G3 G4 W1 W2 W3 [CR RR].
  split; [apply (art_cache_rep_tr W ca c (cl_cache cl) M M' Hca Hca' Hc Hl A G1 G2 CR)|].
  destruct RR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & RF & _ & _ & _).
  assert (T : forall a (n : nat) v, ris + 128 * c <= a -> a + Z.of_nat n <= ris + 128 * c + 128 -> cellA M a n v -> cellA M' a n v).
  { intros a n v Ha Hn C. apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G3|lia|lia]|lia|lia|exact C]. }
  unfold art_region_rep.
  split; [apply T; [lia|cbn; lia|exact R1]|]. split; [apply T; [lia|cbn; lia|exact R2]|]. split; [apply T; [lia|cbn; lia|exact R3]|].
  split; [apply T; [lia|cbn; lia|exact R4]|]. split; [apply T; [lia|cbn; lia|exact R5]|]. split; [apply T; [lia|cbn; lia|exact R6]|].
  split; [apply T; [lia|cbn; lia|exact R7]|]. split; [apply T; [lia|cbn; lia|exact R8]|]. split; [apply T; [lia|cbn; lia|exact R9]|].
  split. { intros j Hj. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'.
           apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G4|lia|cbn; lia]|lia|cbn; lia|exact (RF j Hj)]. }
  split; [exact W1|]. split; [exact W2|exact W3].
Qed.

Lemma art_prim_consts_tr : forall W (M M' : word -> option byte) spb ris, art_agree W M M' ->
  art_gap W (1295832 + 32) 32 -> art_gap W 0x10420 8 -> art_gap W 0x1374a0 8 -> art_gap W 0x1cf6e0 8 -> art_gap W 0x1d1768 268 ->
  art_prim_consts spb ris M -> art_prim_consts spb ris M'.
Proof.
  intros W M M' spb ris A G1 G2 G3 G4 G5 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9). unfold art_prim_consts.
  split; [apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G1|lia|cbn; lia]|lia|cbn; lia|exact C1]|].
  split; [apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G1|lia|cbn; lia]|lia|cbn; lia|exact C2]|].
  split; [apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G1|lia|cbn; lia]|lia|cbn; lia|exact C3]|].
  split; [apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G1|lia|cbn; lia]|lia|cbn; lia|exact C4]|].
  split; [apply (art_cell_tr W M M' _ _ _ A); [exact G2|lia|cbn; lia|exact C5]|].
  split; [apply (art_cell_tr W M M' _ _ _ A); [exact G3|lia|cbn; lia|exact C6]|].
  split; [apply (art_cell_tr W M M' _ _ _ A); [exact G4|lia|cbn; lia|exact C7]|].
  split; [apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G5|lia|cbn; lia]|lia|cbn; lia|exact C8]|].
  apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G5|lia|cbn; lia]|lia|cbn; lia|exact C9].
Qed.

Section Inv.
Variables (HI t ctx tp key tsd spb ris qs parr : Z).

Definition art_rcy_inv (nt : Z) (G : art_rg) (M : word -> option byte) : Prop :=
  (forall c, 1 <= c <= 30 ->
      art_cls_rep (t + 208) spb ris c (rg_cls G c) M /\ art_cls_ok c (rg_cls G c) /\ Z.of_nat (length (cl_cache (rg_cls G c))) <= art_ic_mc c
      /\ (0 < cl_au (rg_cls G c) -> 4 * (Z.of_nat (length (cl_cache (rg_cls G c))) + Z.of_nat (length (cl_free (rg_cls G c))) + nt) <= cl_mfa (rg_cls G c)
                                  /\ Z.of_nat (length (cl_cache (rg_cls G c))) + Z.of_nat (length (cl_free (rg_cls G c))) + nt <= 134217720))
  /\ art_pc_hdr (t + 208) true M /\ art_prim_consts spb ris M /\ art_layout M /\ art_tsd M tp key tsd ctx t
  /\ cellA M 0x137500 8 1 /\ cellA M 0x10360 8 0xcc6e96b9cc6e96b9
  /\ wrA M t 4096 /\ wrA M (SB + 8192 * qs) (2 ^ 34)
  /\ art_sec_cells M parr (rg_bl G) /\ art_sec_geo HI t ctx parr (rg_bl G)
  /\ (forall b, In b (rg_bl G) -> apart (fst b) (snd b) spb (2 ^ 37 + 4096))
  /\ apart parr (8 * Z.of_nat (length (rg_bl G))) spb (2 ^ 37 + 4096).

Definition art_rcy_prot (G : art_rg) (zlo zlen : Z) : Prop :=
  (exists c', 1 <= c' <= 30 /\ spb + c' * 2 ^ 32 <= zlo /\ zlo + zlen <= spb + c' * 2 ^ 32 + 3758096384)
  \/ (exists b, In b (rg_bl G) /\ fst b + 4096 <= zlo /\ zlo + zlen <= fst b + snd b).

Definition art_rel_pre (G : art_rg) (e : art_rel) : Prop :=
  match e with
  | REP c w d b1 n => 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (rg_cls G c)) w /\ ~ In w (cl_cache (rg_cls G c) ++ cl_free (rg_cls G c))
                      /\ 0 <= d /\ d mod 16 = 0 /\ d + 16 + (n + 7) / 8 * 8 <= AsanTab.class_size c /\ 0 <= b1 < 256 /\ 0 <= n < 2 ^ 32
  | RES mb ms m b1 n => In (mb, ms) (rg_bl G) /\ mb + 4096 <= m /\ m + 16 <= mb + ms /\ 0 <= b1 < 256 /\ 0 <= n < 2 ^ 32
  | REB wb => art_cptr_ok 8192 (cl_au (rg_cls G 24)) wb /\ ~ In wb (cl_cache (rg_cls G 24) ++ cl_free (rg_cls G 24))
  end.
Definition art_rel_mem (e : art_rel) (M : word -> option byte) : Prop :=
  match e with
  | REP c w d b1 n => cellA M (spb + c * 2 ^ 32 + 16 * w + d) 4 (3 + 256 * b1) /\ cellA M (spb + c * 2 ^ 32 + 16 * w + d + 4) 4 n
                      /\ (d <> 0 -> cellA M (spb + c * 2 ^ 32 + 16 * w) 8 0xcc6e96b9cc6e96b9)
  | RES mb ms m b1 n => cellA M m 4 (3 + 256 * b1) /\ cellA M (m + 4) 4 n
  | REB wb => True
  end.
(* [comment removed for export] *)
Definition art_rel_events (e : art_rel) : list aev :=
  match e with RES mb ms _ _ _ => art_flush_events mb ms ++ [AMunmap mb ms] | _ => [] end.
Definition art_rel_fp (sp1 : Z) (G : art_rg) (e : art_rel) : list (Z * Z) :=
  match e with
  | REP c w d b1 n => art_cbr_prim_fp sp1 t spb ris c (Z.of_nat (length (cl_free (rg_cls G c)))) (spb + c * 2 ^ 32 + 16 * w) (spb + c * 2 ^ 32 + 16 * w + d) ((n + 7) / 8 * 8)
  | RES mb ms m b1 n => art_cbr_sec_fp sp1 t parr (Z.of_nat (art_bl_idx mb (rg_bl G))) (fst (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0))) mb ms
  | REB wb => art_lcd_fp sp1 (t + 208) spb ris 24 (Z.of_nat (length (cl_free (rg_cls G 24))))
  end.

Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Hypothesis GEO : art_geo HI t ctx tp tsd spb ris qs.

#[using="GEO"] Lemma art_rcy_prim_step : forall regs (M rom : word -> option byte) (raw : word) (sp cb nt c w d b1 n : Z) (G : art_rg),
  let e := REP c w d b1 n in
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 cb -> getr regs 11 = Z_to_bv 64 (art_rel_addr spb e) ->
  HI <= sp - 320 -> sp < 2 ^ 47 -> sp <= cb -> cb + 8 < 2 ^ 47 -> wrA M (sp - 320) 320 -> cellA M cb 8 (t + 208) -> 0 <= nt ->
  art_rcy_inv (nt + 1) G M -> art_rel_pre G e -> art_rel_mem e M ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x548f4 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x)
    /\ art_rcy_inv nt (art_rel_step e G) M'
    /\ mem_grows M M'
    /\ art_agree (art_rel_fp sp G e) M M'.
Proof.
  intros regs M rom raw sp cb nt c w d b1 n G e H1 Hret H2 H4 H10 H11 HHI Hsp' Hcb Hcb' W Ccb Hnt INV PRE MEM.
  unfold e in *. cbn [art_rel_addr] in H11. clear e.
  destruct INV as (ICLS & IPH & IPC & ILAY & ITSD & IGOT & IMAG & IWT & IWSH & ISC & ISG & IBK & IPK).
  destruct PRE as (Hc & Hw & Hnin & Hd & Hd16 & Hdsz & Hb1 & Hn). destruct MEM as (Chw & Cn & Cmag).
  destruct (ICLS c Hc) as (REP & OK & Hlen & Hroom).
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & Gti & Gts & Atk & (qt & Et) & G13 & G14 & Gci & Gcs & Ack & Atc & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; lia).
  assert (Ac_i : apart ctx 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; lia).
  assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; lia).
  clear Gti Gts Gci Gcs.
  pose proof Hw as (Hw0 & Hwsz & (i & Ei)).
  pose proof OK as (L16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (_ & Hmfa1) & Hnf4 & _ & _).
  pose proof (art_class_size_facts c Hc) as (Hsz & _).
  pose proof ITSD as (_ & _ & _ & _ & _ & _ & _ & Hkey & _).
  assert (Hc32 : 2 ^ 32 <= c * 2 ^ 32 <= 30 * 2 ^ 32) by lia.
  set (ab := spb + c * 2 ^ 32 + 16 * w) in *. set (m := ab + d) in *. set (rs := (n + 7) / 8 * 8) in *.
  assert (Eab : ab = spb + c * 2 ^ 32 + 16 * w) by reflexivity. assert (Em : m = ab + d) by reflexivity.
  assert (Hrs : 0 <= rs /\ rs mod 8 = 0 /\ n <= rs < n + 8).
  { unfold rs. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as B. split; [lia|]. split; [apply Z_mod_mult|lia]. }
  destruct Hrs as (Hrs0 & Hrs8 & Hrsn).
  assert (Hm8 : (m + 16) mod 8 = 0).
  { unfold m, ab. rewrite Espb. pose proof (Z.div_mod d 16 ltac:(lia)) as D. rewrite Hd16 in D.
    replace (65536 * qs + c * 2 ^ 32 + 16 * w + d + 16) with ((8192 * qs + c * 2 ^ 29 + 2 * w + 2 * (d / 16) + 2) * 8) by lia. apply Z_mod_mult. }
  assert (Eq8 : m + 16 = 8 * ((m + 16) / 8)). { pose proof (Z.div_mod (m + 16) 8 ltac:(lia)) as D. rewrite Hm8 in D. lia. }
  assert (Er8 : rs = 8 * (rs / 8)). { pose proof (Z.div_mod rs 8 ltac:(lia)) as D. rewrite Hrs8 in D. lia. }
  (* [comment removed for export] *)
  destruct (art_cell_exists M (t + 208 + 2576) 8 ltac:(lia) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt At_i; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:(cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:(eapply wr_sub; [exact IWT|cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)|cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)])) as (sv & _ & Csv).
  destruct (art_cell_exists M (t + 2800 + 40) 8 ltac:(lia) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt At_i; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:(cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:(eapply wr_sub; [exact IWT|cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)|cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)])) as (f1 & _ & Cf1).
  destruct (art_cell_exists M (t + 2800 + 48) 8 ltac:(lia) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt At_i; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:(cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:(eapply wr_sub; [exact IWT|cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)|cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)])) as (f2 & _ & Cf2).
  destruct (art_cbr_prim_run regs M rom raw sp HI tp key tsd ctx t qs cb spb ris c w d m b1 n sv f1 f2 (rg_cls G c) H1 Hret H2 H4 H10 H11 GEO HHI Hsp' Hcb Hcb' W IWT IPC ILAY ITSD
              Hc IPH REP OK Hlen
              ltac:(intros EF; unfold art_cls_full in EF; apply Z.eqb_eq in EF; destruct (art_ic_mc_half c ltac:(lia)) as (Emc2 & Hh); specialize (Hroom ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia))); clear - Hroom Hh Hnt EF Emc2; lia)
              Hw Em Hd Hdsz Hd16 Hb1 Hn Ccb Chw Cn IMAG Cmag
              ltac:(eapply wr_sub; [exact IWSH|unfold SB; (clear - Eq8 Em Eab Espb Hc32 Hw0 Hd; lia)|fold rs; unfold SB; (clear - Eq8 Er8 Em Eab Espb Hc32 Hw0 Hd Hdsz Hwsz Haumu Hmu3; lia)]) Csv Cf1 Cf2)
    as (r' & M' & RUN & R2 & RK & GRW & AG & REP' & _ & _ & _).
  exists r', M'. split; [exact RUN|]. split; [exact R2|]. split; [exact RK|].
  split; [|split; [exact GRW|exact AG]].
  (* [comment removed for export] *)
  unfold art_rel_fp, art_cbr_prim_fp, art_lcd_fp in AG. fold ab m rs in AG.
  unfold art_rcy_inv. cbn [art_rel_step rg_cls rg_bl].
  split.
  { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite art_cls_upd_same. split; [exact REP'|]. split; [apply art_cls_dealloc_ok; [exact Hc|exact OK|exact Hlen|exact Hw|exact Hnin|]|].
      { intros EF. unfold art_cls_full in EF. apply Z.eqb_eq in EF. destruct (art_ic_mc_half c ltac:(lia)) as (Emc2 & Hh). specialize (Hroom ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia))). clear - Hroom Hh Hnt EF Emc2. lia. }
      split; [apply art_cls_dealloc_cache_le; [exact Hlen|lia]|].
      destruct (art_cls_dealloc_au c w (rg_cls G c)) as (Ea & _ & Ef). rewrite Ea, Ef. intros Hau'. specialize (Hroom Hau').
      pose proof (art_cls_dealloc_total c w (rg_cls G c) Hlen ltac:(lia)) as Tt. clear - Hroom Tt Hnt. lia.
    - rewrite art_cls_upd_other by exact NE. destruct (ICLS c' Hc') as (R1 & O1 & L1 & Rm1).
      pose proof O1 as (L16' & _ & _ & _ & _ & _ & _ & (_ & Hmfa1') & Hnf4' & _ & _).
      split; [|split; [exact O1|split; [exact L1|intros X; specialize (Rm1 X); clear - Rm1 Hnt; lia]]].
      apply (art_cls_rep_tr _ (t + 208) spb ris c' (rg_cls G c') M M' ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:(clear - Hc'; lia) L16' ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc'; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc'; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc'; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc'; unfold apart in *; cbn in *; lia))
               ltac:(clear - Hnf4' Hmfa1'; lia) GRW AG); [| | | |exact R1].
      + cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc' NE Atk At_s; unfold apart in *; cbn in *; lia)].
      + cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc' NE Atk At_s; unfold apart in *; cbn in *; lia)].
      + cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc' NE Atk At_s; unfold apart in *; cbn in *; lia)].
      + cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc' NE Atk At_s Hnf4' Hmfa1'; unfold apart in *; cbn in *; lia)]. }
  split. { apply (art_pc_hdr_tr _ (t + 208) true M M' ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) AG); [|exact IPH]. intros c' Hc'. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc' Atk At_s; unfold apart in *; cbn in *; lia)]. }
  split. { apply (art_prim_consts_fp _ M M' spb ris AG); [|exact IPC]. intros z Hz. cbn [art_out app fst snd]. unfold SB. repeat split; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hz At_i; unfold apart in *; cbn in *; lia). }
  split. { apply (art_layout_fp _ M M' AG); [|exact ILAY]. intros z Hz. cbn [art_out app fst snd]. unfold SB. repeat split; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hz At_i; unfold apart in *; cbn in *; lia). }
  split. { apply (art_tsd_fp _ M M' tp key tsd ctx t AG); [| |(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)|exact ITSD].
           - intros z Hz. cbn [art_out app fst snd]. unfold SB. repeat split; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hz At_i; unfold apart in *; cbn in *; lia).
           - intros z Hz. cbn [art_out app fst snd]. unfold SB. repeat split; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hz Atc Ack Ac_s; unfold apart in *; cbn in *; lia). }
  pose proof ISG as (Gp1 & Gp2 & Gp3 & Gp4 & Apt & Apc & GB & GD).
  split. { apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact IGOT]. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt At_i; unfold apart in *; cbn in *; lia)]. }
  split. { apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact IMAG]. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt At_i; unfold apart in *; cbn in *; lia)]. }
  split; [eapply wr_grows; [exact GRW|exact IWT]|]. split; [eapply wr_grows; [exact GRW|exact IWSH]|].
  split. { apply (art_sec_cells_tr _ M M' HI t ctx parr (rg_bl G) ISG ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) GRW AG); [| | | |exact ISC].
           - cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt At_i; unfold apart in *; cbn in *; lia)].
           - destruct ISC as (_ & _ & _ & CL & _). apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact CL]. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt At_i; unfold apart in *; cbn in *; lia)].
           - pose proof Gp4 as Gp4'. unfold appmem, kHighMemBeg, SB in Gp4'. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Gp1 Gp2 Gp3 Gp4' Apt IPK; unfold apart in *; cbn in *; lia)].
           - intros b Hb. destruct (GB _ Hb) as (_ & _ & Hs & Hb0 & Hb1' & Hbapp & _ & Hbt & _). pose proof (IBK _ Hb) as Hbk. unfold appmem in Hbapp.
             cbn [art_gap app fst snd]. unfold SB, kHighMemBeg in *. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hs Hb0 Hb1' Hbapp Hbt Hbk; unfold apart in *; cbn in *; lia)]. }
  split; [exact ISG|]. split; [exact IBK|exact IPK].
Qed.

(* [comment removed for export] *)
#[using="GEO"] Lemma art_rcy_batch_step : forall regs (M rom : word -> option byte) (raw : word) (sp nt wb : Z) (G : art_rg),
  let e := REB wb in
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 (t + 208) -> getr regs 11 = Z_to_bv 64 1295832 -> getr regs 12 = Z_to_bv 64 24 ->
  getr regs 13 = Z_to_bv 64 (art_rel_addr spb e) ->
  HI <= sp - 320 -> sp < 2 ^ 47 -> wrA M (sp - 320) 320 -> 0 <= nt ->
  art_rcy_inv (nt + 1) G M -> art_rel_pre G e ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x54cf8 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x)
    /\ art_rcy_inv nt (art_rel_step e G) M'
    /\ mem_grows M M'
    /\ art_agree (art_rel_fp sp G e) M M'.
Proof.
  intros regs M rom raw sp nt wb G e H1 Hret H2 H10 H11 H12 H13 HHI Hsp' W Hnt INV PRE.
  unfold e in *. cbn [art_rel_addr] in H13. clear e.
  destruct INV as (ICLS & IPH & IPC & ILAY & ITSD & IGOT & IMAG & IWT & IWSH & ISC & ISG & IBK & IPK).
  destruct PRE as (Hw & Hnin).
  set (c := 24) in *. assert (Hc : 1 <= c <= 30) by (unfold c; lia). set (w := wb) in *.
  change 8192 with (AsanTab.class_size c) in Hw.
  destruct (ICLS c Hc) as (REP & OK & Hlen & Hroom).
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & Gti & Gts & Atk & (qt & Et) & G13 & G14 & Gci & Gcs & Ack & Atc & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; lia).
  assert (Ac_i : apart ctx 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; lia).
  assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; lia).
  clear Gti Gts Gci Gcs.
  pose proof Hw as (Hw0 & Hwsz & (i & Ei)).
  pose proof OK as (L16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (_ & Hmfa1) & Hnf4 & _ & _).
  pose proof (art_class_size_facts c Hc) as (Hsz & _).
  pose proof ITSD as (_ & _ & _ & _ & _ & _ & _ & Hkey & _).
  assert (Hc32 : 2 ^ 32 <= c * 2 ^ 32 <= 30 * 2 ^ 32) by (unfold c; lia).
  (* [comment removed for export] *)
  assert (Hcb : True) by exact I. assert (Hcb' : True) by exact I. assert (Hd : True) by exact I. assert (Hdsz : True) by exact I. assert (Hn : True) by exact I. assert (Hb1 : True) by exact I.
  assert (Hrs0 : True) by exact I. assert (Hrsn : True) by exact I. assert (Eq8 : True) by exact I. assert (Er8 : True) by exact I. assert (Eab : True) by exact I. assert (Em : True) by exact I.
  assert (Hca8 : (t + 208) mod 8 = 0). { rewrite Et. replace (4096 * qt + 208) with ((512 * qt + 26) * 8) by lia. apply Z_mod_mult. }
  destruct (art_cell_exists M (t + 208 + 2576) 8 ltac:(lia) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt At_i; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:(cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:(eapply wr_sub; [exact IWT|cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)|cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)])) as (sv & _ & Csv).
  destruct (art_lcd_run regs M rom raw sp HI (t + 208) c (spb + c * 2 ^ 32 + 16 * w) spb ris (512 * qs + 2 ^ 30) w sv (rg_cls G c) H1 Hret H2 H10 H11 H12 H13
              ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) HHI ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) Hc ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) Eris ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) Hca8 ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt At_i; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Atk; unfold apart in *; cbn in *; lia))
              W ltac:(eapply wr_sub; [exact IWT|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)]) IPC IPH REP OK Hlen eq_refl ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) Csv
              ltac:(intros EF; unfold art_cls_full in EF; apply Z.eqb_eq in EF; destruct (art_ic_mc_half c ltac:(lia)) as (Emc2 & Hh); specialize (Hroom ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia))); clear - Hroom Hh Hnt EF Emc2; lia))
    as (r' & M' & RUN & R2 & RK & GRW & AG & REP' & _).
  exists r', M'. split; [exact RUN|]. split; [exact R2|]. split; [exact RK|].
  split; [|split; [exact GRW|exact AG]].
  unfold art_rel_fp, art_lcd_fp in AG. fold c in AG.
  change (art_rcy_inv nt (RG (art_cls_upd (rg_cls G) c (art_cls_dealloc c w (rg_cls G c))) (rg_bl G)) M').
  unfold art_rcy_inv. cbn [rg_cls rg_bl].
  split.
  { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite art_cls_upd_same. split; [exact REP'|]. split; [apply art_cls_dealloc_ok; [exact Hc|exact OK|exact Hlen|exact Hw|exact Hnin|]|].
      { intros EF. unfold art_cls_full in EF. apply Z.eqb_eq in EF. destruct (art_ic_mc_half c ltac:(lia)) as (Emc2 & Hh). specialize (Hroom ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia))). clear - Hroom Hh Hnt EF Emc2. lia. }
      split; [apply art_cls_dealloc_cache_le; [exact Hlen|lia]|].
      destruct (art_cls_dealloc_au c w (rg_cls G c)) as (Ea & _ & Ef). rewrite Ea, Ef. intros Hau'. specialize (Hroom Hau').
      pose proof (art_cls_dealloc_total c w (rg_cls G c) Hlen ltac:(lia)) as Tt. clear - Hroom Tt Hnt. lia.
    - rewrite art_cls_upd_other by exact NE. destruct (ICLS c' Hc') as (R1 & O1 & L1 & Rm1).
      pose proof O1 as (L16' & _ & _ & _ & _ & _ & _ & (_ & Hmfa1') & Hnf4' & _ & _).
      split; [|split; [exact O1|split; [exact L1|intros X; specialize (Rm1 X); clear - Rm1 Hnt; lia]]].
      apply (art_cls_rep_tr _ (t + 208) spb ris c' (rg_cls G c') M M' ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:(clear - Hc'; lia) L16' ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc'; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc'; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc'; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc'; unfold apart in *; cbn in *; lia))
               ltac:(clear - Hnf4' Hmfa1'; lia) GRW AG); [| | | |exact R1].
      + cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc' NE Atk At_s; unfold apart in *; cbn in *; lia)].
      + cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc' NE Atk At_s; unfold apart in *; cbn in *; lia)].
      + cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc' NE Atk At_s; unfold apart in *; cbn in *; lia)].
      + cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc' NE Atk At_s Hnf4' Hmfa1'; unfold apart in *; cbn in *; lia)]. }
  split. { apply (art_pc_hdr_tr _ (t + 208) true M M' ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) AG); [|exact IPH]. intros c' Hc'. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hc' Atk At_s; unfold apart in *; cbn in *; lia)]. }
  split. { apply (art_prim_consts_fp _ M M' spb ris AG); [|exact IPC]. intros z Hz. cbn [art_out app fst snd]. unfold SB. repeat split; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hz At_i; unfold apart in *; cbn in *; lia). }
  split. { apply (art_layout_fp _ M M' AG); [|exact ILAY]. intros z Hz. cbn [art_out app fst snd]. unfold SB. repeat split; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hz At_i; unfold apart in *; cbn in *; lia). }
  split. { apply (art_tsd_fp _ M M' tp key tsd ctx t AG); [| |(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)|exact ITSD].
           - intros z Hz. cbn [art_out app fst snd]. unfold SB. repeat split; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hz At_i; unfold apart in *; cbn in *; lia).
           - intros z Hz. cbn [art_out app fst snd]. unfold SB. repeat split; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hz Atc Ack Ac_s; unfold apart in *; cbn in *; lia). }
  pose proof ISG as (Gp1 & Gp2 & Gp3 & Gp4 & Apt & Apc & GB & GD).
  split. { apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact IGOT]. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt At_i; unfold apart in *; cbn in *; lia)]. }
  split. { apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact IMAG]. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt At_i; unfold apart in *; cbn in *; lia)]. }
  split; [eapply wr_grows; [exact GRW|exact IWT]|]. split; [eapply wr_grows; [exact GRW|exact IWSH]|].
  split. { apply (art_sec_cells_tr _ M M' HI t ctx parr (rg_bl G) ISG ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt; lia)) GRW AG); [| | | |exact ISC].
           - cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt At_i; unfold apart in *; cbn in *; lia)].
           - destruct ISC as (_ & _ & _ & CL & _). apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact CL]. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt At_i; unfold apart in *; cbn in *; lia)].
           - pose proof Gp4 as Gp4'. unfold appmem, kHighMemBeg, SB in Gp4'. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Gp1 Gp2 Gp3 Gp4' Apt IPK; unfold apart in *; cbn in *; lia)].
           - intros b Hb. destruct (GB _ Hb) as (_ & _ & Hs & Hb0 & Hb1' & Hbapp & _ & Hbt & _). pose proof (IBK _ Hb) as Hbk. unfold appmem in Hbapp.
             cbn [art_gap app fst snd]. unfold SB, kHighMemBeg in *. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hcb' Hc Hc32 Hsz Hw0 Hwsz Hau0 Haumu Hmu3 Hd Hdsz Hn Hb1 Hrs0 Hrsn Eq8 Er8 Eab Em Hkey Hnf4 Hmfa1 Hnt Hs Hb0 Hb1' Hbapp Hbt Hbk; unfold apart in *; cbn in *; lia)]. }
  split; [exact ISG|]. split; [exact IBK|exact IPK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="GEO"] Lemma art_rcy_sec_step : forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word) (sp cb nt mb ms m b1 n : Z) (G : art_rg),
  let e := RES mb ms m b1 n in
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 cb -> getr regs 11 = Z_to_bv 64 (art_rel_addr spb e) ->
  HI <= sp - 320 -> sp < 2 ^ 47 -> 0 <= cb < 2 ^ 64 -> wrA M (sp - 320) 320 -> 0 <= nt -> 0x661b28 <= tp - 88 -> 0x661b28 <= tsd ->
  art_rcy_inv (nt + 1) G M -> art_rel_pre G e -> art_rel_mem e M ->
  art_evok_list EVOK log (art_rel_events e) ->
  (forall regs' (M' : word -> option byte),
     getr regs' 1 = raw -> getr regs' 2 = Z_to_bv 64 sp ->
     (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
     art_rcy_inv nt (art_rel_step e G) M' ->
     art_agree (art_rel_fp sp G e) M M' ->
     (forall a k, 0 <= a -> a + k < 2 ^ 64 -> apart mb ms a k -> wrA M a k -> wrA M' a k) ->
     Q (log ++ art_rel_events e) (mkst regs' raw M' rom)) ->
  aruns ASEGS EVOK GR Q log (mkst regs (0x548f4 : word) M rom).
Proof.
  intros Q log regs M rom raw sp cb nt mb ms m b1 n G e H1 Hret H2 H4 H10 H11 HHI Hsp' Hcb W Hnt Htp0 Htsd0 INV PRE MEM EV K.
  unfold e in *. cbn [art_rel_addr] in H11. cbn [art_rel_events] in EV, K. cbn [art_rel_step art_rel_fp] in K. clear e.
  destruct INV as (ICLS & IPH & IPC & ILAY & ITSD & IGOT & IMAG & IWT & IWSH & ISC & ISG & IBK & IPK).
  destruct PRE as (Hin & Hm1 & Hm2 & Hb1 & Hn). destruct MEM as (Chw & Cn).
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & Gti & Gts & Atk & (qt & Et) & G13 & G14 & Gci & Gcs & Ack & Atc & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; lia).
  assert (Ac_i : apart ctx 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; lia).
  pose proof IPC as (Cspb & _ & _ & _ & _ & Cpc & Cpg & _ & Cmm).
  pose proof ITSD as (_ & _ & _ & _ & _ & _ & _ & Hkey & _).
  pose proof ISG as (Gp1 & Gp2 & Gp3 & Gp4 & Apt & Apc & GB & GD).
  destruct (GB _ Hin) as (Hmb4k & Hms4k & Hmb0 & Hmb1 & Hmb2 & Hmbapp & Abp & Abt & Abc). cbn [fst snd] in Hmb4k, Hms4k, Hmb0, Hmb1, Hmb2, Hmbapp, Abp, Abt, Abc.
  pose proof (IBK _ Hin) as Abk. cbn [fst snd] in Abk.
  pose proof (art_bl_idx_nth (rg_bl G) mb ms Hin (art_sec_geo_inj HI t ctx parr (rg_bl G) ISG)) as Hnth.
  set (idx := art_bl_idx mb (rg_bl G)) in *.
  assert (Hidx : (idx < length (rg_bl G))%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
  set (last := fst (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0))) in *.
  assert (Hlastin : In (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0)) (rg_bl G)) by (apply nth_In; lia).
  destruct (GB _ Hlastin) as (_ & _ & Hl0 & Hl1 & Hl2 & Hlapp & _ & Hlt & Hlc). pose proof (IBK _ Hlastin) as Hlk. fold last in Hl1, Hl2, Hlapp, Hlt, Hlc, Hlk.
  unfold appmem, SB, kHighMemBeg in Hlapp, Hmbapp. pose proof Gp4 as Gp4'. unfold appmem, kHighMemBeg, SB in Gp4'.
  destruct (art_cell_exists M (t + 2800 + 40) 8 ltac:(lia) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp At_i; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)) ltac:(cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)) ltac:(eapply wr_sub; [exact IWT|cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)|cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)])) as (f1 & _ & Cf1).
  destruct (art_cell_exists M (t + 2800 + 48) 8 ltac:(lia) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp At_i; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)) ltac:(cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)) ltac:(eapply wr_sub; [exact IWT|cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)|cbn; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)])) as (f2 & _ & Cf2).
  apply (art_cbr_sec_aruns EVOK GR Q log regs M rom raw sp HI tp key tsd ctx t cb spb parr mb ms m b1 n f1 f2 (rg_bl G) idx H1 Hret H2 H4 H10 H11
           ltac:(unfold kHighMemBeg; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)) Hsp' ltac:(eapply wr_sub; [exact W|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)]) Hcb ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)) Cspb Hnth ISC ISG ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Abk; unfold apart in *; cbn in *; lia)) Hm1 Hm2 Hb1 Hn Chw Cn ILAY ITSD
           G7 G8 ltac:(unfold appmem, SB, kHighMemBeg; exact Gts) Gti IWT G13 G14 ltac:(unfold appmem, SB, kHighMemBeg; exact Gcs) Gci Atc Htp0 ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)) Htsd0 ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia))
           Cpc Cpg IGOT Cmm Cf1 Cf2 EV).
  intros r' M' F1 F2 FK FA FN FS FW FSC.
  apply (K r' M' F1 F2 FK); [|exact FA|exact FW].
  (* [comment removed for export] *)
  unfold art_cbr_sec_fp, art_secd_fp in FA.
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; lia).
  assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; lia).
  clear Gti Gts Gci Gcs.
  pose proof (proj1 (Nat2Z.inj_lt _ _) Hidx) as Hidx'.
  assert (Hsh : mb = 8 * (mb / 8) /\ ms = 8 * (ms / 8)).
  { pose proof (Z.div_mod mb 4096 ltac:(lia)) as D1. rewrite Hmb4k in D1. pose proof (Z.div_mod ms 4096 ltac:(lia)) as D2. rewrite Hms4k in D2.
    assert (M1 : mb mod 8 = 0) by (rewrite D1; replace (4096 * (mb / 4096) + 0) with (512 * (mb / 4096) * 8) by lia; apply Z_mod_mult).
    assert (M2 : ms mod 8 = 0) by (rewrite D2; replace (4096 * (ms / 4096) + 0) with (512 * (ms / 4096) * 8) by lia; apply Z_mod_mult).
    pose proof (Z.div_mod mb 8 ltac:(lia)) as E1. pose proof (Z.div_mod ms 8 ltac:(lia)) as E2. rewrite M1 in E1. rewrite M2 in E2. clear - E1 E2. lia. }
  destruct Hsh as (Emb8 & Ems8).
  unfold art_rcy_inv. cbn [rg_cls rg_bl].
  split.
  { intros c' Hc'. destruct (ICLS c' Hc') as (R1 & O1 & L1 & Rm1).
    pose proof O1 as (L16' & (Hau0' & Haumu') & _ & _ & _ & Hmu3' & _ & (Hmfa0' & Hmfa1') & Hnf4' & _ & _).
    pose proof R1 as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wr1 & Wfa1 & Wu1)).
    assert (X : 0 <= 4 * Z.of_nat (length (cl_free (rg_cls G c'))) <= 2 ^ 29 /\ 0 <= cl_mfa (rg_cls G c') <= 2 ^ 29 /\ 0 <= cl_mu (rg_cls G c') <= 3758096384) by (clear - Hnf4' Hmfa0' Hmfa1' Hau0' Haumu' Hmu3'; lia).
    split; [|split; [exact O1|split; [exact L1|intros Y; specialize (Rm1 Y); clear - Rm1 Hnt; lia]]].
    apply (art_cls_rep_tr_w _ (t + 208) spb ris c' (rg_cls G c') M M' ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)) ltac:(clear - Hc'; lia) L16' ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc'; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc'; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc'; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc'; unfold apart in *; cbn in *; lia))
             ltac:(clear - X; lia) FA); [| | | | | | |exact R1].
    + cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' At_i; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' Apt Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' Hlt; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' At_s Emb8 Ems8; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' Abt; unfold apart in *; cbn in *; lia)].
    + cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' At_i; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' Apt Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' Hlt; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' At_s Emb8 Ems8; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' Abt; unfold apart in *; cbn in *; lia)].
    + cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X Atk; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X IPK Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X Hlk; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X Emb8 Ems8; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X Abk; unfold apart in *; cbn in *; lia)].
    + cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X Atk; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X IPK Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X Hlk; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X Emb8 Ems8; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X Abk; unfold apart in *; cbn in *; lia)].
    + apply FW; [(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' Abk; unfold apart in *; cbn in *; lia)|exact Wr1].
    + apply FW; [(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X Abk; unfold apart in *; cbn in *; lia)|exact Wfa1].
    + apply FW; [(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' X Abk; unfold apart in *; cbn in *; lia)|exact Wu1]. }
  split. { apply (art_pc_hdr_tr _ (t + 208) true M M' ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)) FA); [|exact IPH]. intros c' Hc'. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' At_i; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' Apt Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' Hlt; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' At_s Emb8 Ems8; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hc' Abt; unfold apart in *; cbn in *; lia)]. }
  split. { apply (art_prim_consts_tr _ M M' spb ris FA); [| | | | |exact IPC]; cbn [art_gap app fst snd]; unfold SB; repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp ; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp At_i; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Emb8 Ems8; unfold apart in *; cbn in *; lia)]. }
  split. { apply (art_layout_tr _ M M' FA); [| | |exact ILAY]; cbn [art_gap app fst snd]; unfold SB; repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp ; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp At_i; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Emb8 Ems8; unfold apart in *; cbn in *; lia)]. }
  split. { apply (art_tsd_tr _ M M' tp key tsd ctx t FA); [| | | |exact ITSD]; cbn [art_gap app fst snd]; unfold SB; repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp ; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp At_i; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Ac_i; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Atc; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Apc Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hlc; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Ac_s Emb8 Ems8; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Abc; unfold apart in *; cbn in *; lia)]. }
  split. { apply (art_cell_tr _ M M' _ _ _ FA); [|lia|cbn; lia|exact IGOT]. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp ; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp At_i; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Emb8 Ems8; unfold apart in *; cbn in *; lia)]. }
  split. { apply (art_cell_tr _ M M' _ _ _ FA); [|lia|cbn; lia|exact IMAG]. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp ; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp At_i; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Emb8 Ems8; unfold apart in *; cbn in *; lia)]. }
  split. { apply FW; [(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp Abt; unfold apart in *; cbn in *; lia)|exact IWT]. }
  split. { apply FW; [unfold SB; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)|unfold SB; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp; lia)|unfold SB; (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et HHI Hsp' Hcb Hkey Hnt Htp0 Htsd0 Hmb0 Hmb1 Hmb2 Hmbapp Hm1 Hm2 Hb1 Hn Gp1 Gp2 Gp3 Gp4' Hl0 Hl1 Hl2 Hlapp ; unfold apart in *; cbn in *; lia)|exact IWSH]. }
  split; [exact FSC|]. split; [apply art_sec_geo_remove; exact ISG|].
  split. { intros b Hb. apply IBK. eapply art_swap_remove_in. exact Hb. }
  rewrite art_swap_remove_length. clear - IPK Hidx. unfold apart in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="GEO"] Lemma art_rcy_inv_above : forall nt G (M M' : word -> option byte), mem_grows M M' -> art_agree [(HI, 2 ^ 64 - HI)] M M' -> art_rcy_inv nt G M -> art_rcy_inv nt G M'.
Proof.
  intros nt G M M' GRW AG INV.
  destruct INV as (ICLS & IPH & IPC & ILAY & ITSD & IGOT & IMAG & IWT & IWSH & ISC & ISG & IBK & IPK).
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & Gti & Gts & Atk & (qt & Et) & G13 & G14 & Gci & Gcs & Ack & Atc & G19 & G20 & G21 & G22).
  pose proof ITSD as (_ & _ & _ & _ & _ & _ & _ & Hkey & _).
  pose proof ISG as (Gp1 & Gp2 & Gp3 & Gp4 & Apt & Apc & GB & GD).
  unfold art_rcy_inv.
  split.
  { intros c' Hc'. destruct (ICLS c' Hc') as (R1 & O1 & L1 & Rm1).
    pose proof O1 as (L16' & _ & _ & _ & _ & _ & _ & (_ & Hmfa1') & Hnf4' & _ & _).
    split; [|split; [exact O1|split; [exact L1|exact Rm1]]].
    apply (art_cls_rep_tr _ (t + 208) spb ris c' (rg_cls G c') M M' ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey; lia)) ltac:(clear - Hc'; lia) L16' ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey Hc'; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey Hc'; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey Hc'; unfold apart in *; cbn in *; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey Hc'; unfold apart in *; cbn in *; lia))
             ltac:(clear - Hnf4' Hmfa1'; lia) GRW AG); [| | | |exact R1]; cbn [art_gap fst snd]; (split; [|exact I]); (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey Hc' Hnf4' Hmfa1'; unfold apart in *; cbn in *; lia). }
  split. { apply (art_pc_hdr_tr _ (t + 208) true M M' ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey; lia)) ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey; lia)) AG); [|exact IPH]. intros c' Hc'. cbn [art_gap fst snd]. split; [|exact I]. (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey Hc'; unfold apart in *; cbn in *; lia). }
  split. { apply (art_prim_consts_tr _ M M' spb ris AG); [| | | | |exact IPC]; cbn [art_gap fst snd]; (split; [|exact I]); (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey ; unfold apart in *; cbn in *; lia). }
  split. { apply (art_layout_tr _ M M' AG); [| | |exact ILAY]; cbn [art_gap fst snd]; (split; [|exact I]); (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey ; unfold apart in *; cbn in *; lia). }
  split. { apply (art_tsd_tr _ M M' tp key tsd ctx t AG); [| | | |exact ITSD]; cbn [art_gap fst snd]; (split; [|exact I]); (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey ; unfold apart in *; cbn in *; lia). }
  split. { apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact IGOT]. cbn [art_gap fst snd]. split; [|exact I]. (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey ; unfold apart in *; cbn in *; lia). }
  split. { apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact IMAG]. cbn [art_gap fst snd]. split; [|exact I]. (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey ; unfold apart in *; cbn in *; lia). }
  split; [eapply wr_grows; [exact GRW|exact IWT]|]. split; [eapply wr_grows; [exact GRW|exact IWSH]|].
  split. { apply (art_sec_cells_tr _ M M' HI t ctx parr (rg_bl G) ISG ltac:((clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey; lia)) GRW AG); [| | | |exact ISC].
           - cbn [art_gap fst snd]. split; [|exact I]. (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey ; unfold apart in *; cbn in *; lia).
           - destruct ISC as (_ & _ & _ & CL & _). apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact CL]. cbn [art_gap fst snd]. split; [|exact I]. (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey ; unfold apart in *; cbn in *; lia).
           - cbn [art_gap fst snd]. split; [|exact I]. (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey Gp1 Gp2; unfold apart in *; cbn in *; lia).
           - intros b Hb. destruct (GB _ Hb) as (_ & _ & Hs & Hb0 & Hb1' & _). cbn [art_gap fst snd]. split; [|exact I]. (clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 Et Hkey Hs Hb0 Hb1'; unfold apart in *; cbn in *; lia). }
  split; [exact ISG|]. split; [exact IBK|exact IPK].
Qed.
End Inv.
