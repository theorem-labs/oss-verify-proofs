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
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatPoisonRun_b BatInitCache_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatMmapFixed_b BatPopulate1_b BatPopulate2_b BatPopulate3_b
     BatCls_b BatFp_b BatClsPop1_b BatClsPop2_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r719b0_719e8_b.
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
Definition art_pop_events (spb c : Z) (cl : art_cls) : list aev :=
  let tot := Z.of_nat (length (cl_free cl)) + art_cls_new c cl in
  AMmapFixed (spb + c * 2 ^ 32 + cl_mu cl) 262144
  :: (if 4 * tot <=? cl_mfa cl then [] else [AMmapFixed (spb + c * 2 ^ 32 + 3758096384 + cl_mfa cl) (art_cls_mfa' cl tot - cl_mfa cl)]).

(* [comment removed for export] *)
Definition art_pop_fp (sp t spb ris qs c km : Z) : list (Z * Z) :=
  [ (sp - 512, 512); (ris + 128 * c, 128); (spb + c * 2 ^ 32 + 262144 * km, 262144); (spb + c * 2 ^ 32 + 3758096384, 536870912);
    (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km, 32768); (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864);
    (t + 2872, 16); (t + 2792, 8) ].

Lemma art_at_ecall_mmap : art_at_ecall ASEGS (0x8bc80 : word).
Proof. exists W_8b868. split; [exact F_8b868 | exact E_8b868]. Qed.

(* [comment removed for export] *)
Lemma art_region_rep_populate : forall spb ris c mx (cl : art_cls) (M M' : word -> option byte) (W : list (Z * Z)) (new mfa' : Z),
  let sz := AsanTab.class_size c in
  let nf := Z.of_nat (length (cl_free cl)) in
  let fa := spb + c * 2 ^ 32 + 3758096384 in
  let r := ris + 128 * c in
  new = art_cls_new c cl -> 1 <= new -> mfa' = art_cls_mfa' cl (nf + new) ->
  0 <= r -> r + 128 < 2 ^ 64 -> 0 <= fa -> fa + 2 ^ 29 < 2 ^ 64 -> 4 * nf <= 2 ^ 29 ->
  art_region_rep spb ris c mx cl M -> mem_grows M M' -> art_agree W M M' ->
  art_gap W r 16 -> art_gap W (r + 40) 8 -> art_gap W (r + 56) 8 -> art_gap W (r + 72) 16 -> art_gap W fa (4 * nf) ->
  cellA M' (r + 16) 8 (nf + new) -> cellA M' (r + 24) 8 mfa' -> cellA M' (r + 32) 8 (cl_au cl + new * sz) -> cellA M' (r + 48) 8 (cl_mu cl + 262144) ->
  (forall j, 0 <= j < new -> cellA M' (fa + 4 * (nf + new) - 4 * (j + 1)) 4 ((cl_au cl + j * sz) / 16)) ->
  wrA M' fa mfa' -> wrA M' (spb + c * 2 ^ 32) (cl_mu cl + 262144) ->
  art_region_rep spb ris c mx (art_cls_populate c cl) M'.
Proof.
  intros spb ris c mx cl M M' W new mfa' sz nf fa r Enew Hnew Emfa Hr Hr' Hfa Hfa' Hnf RR G A G0 G40 G56 G72 GFA C16 C24 C32 C48 CFA WFA WU.
  destruct RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
  fold r in Rmx, Rnf, Rmfa, Rau, Ram, Rmu, Rmm, Rna, Rnfr, Wr. fold fa in Rfa, Wfa.
  assert (Hnf0 : 0 <= nf) by (unfold nf; lia).
  unfold art_region_rep, art_cls_populate. cbn [cl_free cl_au cl_mu cl_mfa cl_na cl_nfr cl_cache]. fold sz nf fa r. rewrite <- Enew.
  assert (Elen : Z.of_nat (length (cl_free cl ++ art_carved (cl_au cl) sz (Z.to_nat new))) = nf + new).
  { rewrite length_app, art_carved_length, Nat2Z.inj_add, Z2Nat.id by lia. reflexivity. }
  rewrite Elen, <- Emfa.
  split. { apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G0|lia|cbn; lia]|lia|cbn; lia|exact Rmx]. }
  split; [exact C16|]. split; [exact C24|]. split; [exact C32|].
  split. { apply (art_cell_tr W M M'); [exact A|exact G40|lia|cbn; lia|exact Ram]. }
  split; [exact C48|].
  split. { apply (art_cell_tr W M M'); [exact A|exact G56|lia|cbn; lia|exact Rmm]. }
  split. { apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G72|lia|cbn; lia]|lia|cbn; lia|exact Rna]. }
  split. { apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G72|lia|cbn; lia]|lia|cbn; lia|exact Rnfr]. }
  split.
  { intros j Hj. rewrite length_app, art_carved_length in Hj.
    destruct (Nat.lt_ge_cases j (length (cl_free cl))) as [Lt|Ge].
    - rewrite app_nth1 by exact Lt. pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Lt'. fold nf in Lt'.
      apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact GFA|lia|cbn; lia]|lia|cbn; lia|exact (Rfa j Lt)].
    - rewrite app_nth2 by exact Ge. set (k := (j - length (cl_free cl))%nat).
      assert (Hk : (k < Z.to_nat new)%nat) by (unfold k; lia).
      rewrite art_carved_nth by exact Hk. rewrite Z2Nat.id by lia.
      assert (Ej : Z.of_nat j = nf + Z.of_nat k) by (unfold k, nf; lia).
      pose proof (CFA (new - 1 - Z.of_nat k) ltac:(lia)) as C.
      replace (fa + 4 * (nf + new) - 4 * (new - 1 - Z.of_nat k + 1)) with (fa + 4 * Z.of_nat j) in C by lia. exact C. }
  split; [eapply wr_grows; [exact G|exact Wr]|]. split; [exact WFA|exact WU].
Qed.

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition art_pop_fpE (sp t spb ris qs c km mfa : Z) : list (Z * Z) :=
  [ (sp - 512, 448); (sp - 64, 64); (spb + c * 2 ^ 32 + 262144 * km, 262144); (spb + c * 2 ^ 32 + 3758096384 + mfa, 536870912 - mfa);
    (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km, 32768); (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864);
    (t + 2872, 16); (t + 2792, 8); (ris + 128 * c + 24, 8); (ris + 128 * c + 48, 8) ].

(* [comment removed for export] *)
#[using="Type"] Lemma art_populate_tail :
  forall (Q : list aev -> machine_state -> Prop) (logE : list aev) regs rE (M ME rom : word -> option byte) (raw : word)
         (sp HI t spb ris qs c km mx new mfa' : Z) (cl : art_cls),
    let sz := AsanTab.class_size c in
    let nf := Z.of_nat (length (cl_free cl)) in
    let fa := spb + c * 2 ^ 32 + 3758096384 in
    let r := ris + 128 * c in
    ret_ok raw -> 1 <= c <= 30 -> HI <= sp - 512 -> sp < 2 ^ 47 ->
    spb = 65536 * qs -> 0x10007fff8000 <= spb -> ris = spb + 2 ^ 37 -> ris + 4096 <= HI -> 4096 <= t -> t + 4096 <= HI ->
    apart t 4096 spb (2 ^ 37 + 4096) -> apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
    cl_mu cl = 262144 * km -> 0 <= cl_au cl -> cl_au cl <= cl_mu cl -> cl_mu cl + 262144 <= 3758096384 -> 0 <= cl_mfa cl -> 4 * nf <= cl_mfa cl ->
    new = art_cls_new c cl -> 1 <= new -> cl_au cl + new * sz <= cl_mu cl + 262144 -> sz <= cl_mu cl + 262144 - cl_au cl ->
    mfa' = art_cls_mfa' cl (nf + new) -> cl_mfa cl <= mfa' -> mfa' <= 536870912 -> 4 * (nf + new) <= mfa' ->
    art_region_rep spb ris c mx cl M ->
    getr rE 10 = Z_to_bv 64 1 -> getr rE 2 = Z_to_bv 64 (sp - 64) -> getr rE 8 = Z_to_bv 64 r -> getr rE 9 = Z_to_bv 64 (nf + new) ->
    getr rE 18 = Z_to_bv 64 (spb + c * 2 ^ 32) -> getr rE 19 = Z_to_bv 64 new -> getr rE 20 = Z_to_bv 64 (cl_mu cl + 262144 - cl_au cl) -> getr rE 21 = Z_to_bv 64 sz ->
    (forall x : reg, In x [3; 4; 23; 24; 25; 26; 27]%bv -> getr rE x = getr regs x) ->
    mem_grows M ME -> art_agree (art_pop_fpE sp t spb ris qs c km (cl_mfa cl)) M ME ->
    cellA ME (sp - 8) 8 (U raw) -> cellA ME (sp - 16) 8 (U (getr regs 8)) -> cellA ME (sp - 24) 8 (U (getr regs 9)) -> cellA ME (sp - 32) 8 (U (getr regs 18)) ->
    cellA ME (sp - 40) 8 (U (getr regs 19)) -> cellA ME (sp - 48) 8 (U (getr regs 20)) -> cellA ME (sp - 56) 8 (U (getr regs 21)) -> cellA ME (sp - 64) 8 (U (getr regs 22)) ->
    cellA ME (r + 48) 8 (cl_mu cl + 262144) -> cellA ME (r + 24) 8 mfa' ->
    wrA ME fa mfa' -> wrA ME (spb + c * 2 ^ 32) (cl_mu cl + 262144) ->
    (forall j, 0 <= j < 32768 -> cellA ME (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + j) 1 250) ->
    (exists m1' m2' sv', cellA ME (t + 2872) 8 m1' /\ cellA ME (t + 2880) 8 m2' /\ cellA ME (t + 2792) 8 sv') ->
    (forall regs' (M' : word -> option byte),
        getr regs' 10 = Z_to_bv 64 1 -> getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
        (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
        mem_grows M M' -> art_agree (art_pop_fp sp t spb ris qs c km) M M' ->
        art_region_rep spb ris c mx (art_cls_populate c cl) M' ->
        (forall j, 0 <= j < 32768 -> cellA M' (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + j) 1 250) ->
        (exists m1' m2' sv', cellA M' (t + 2872) 8 m1' /\ cellA M' (t + 2880) 8 m2' /\ cellA M' (t + 2792) 8 sv') ->
        Q logE (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q logE (mkst rE (0x57a28 : word) ME rom).
Proof.
  intros Q logE regs rE M ME rom raw sp HI t spb ris qs c km mx new mfa' cl sz nf fa r
         Hret Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Emu Hau0 Haumu Room1 Hmfa0 Hnf4 Enew Hnew Hcarve Hfb Emfa Hmfa1 Hmfa2 Htot RR
         E10 E2 E8 E9 E18 E19 E20 E21 KE GE AE FP1 FP8 FP9 FP18 FP19 FP20 FP21 FP22 Emu' Emfa' WFA WU SH ST K.
  destruct (art_class_size_facts c Hc) as (Hsz & _). fold sz in Hsz.
  assert (Hnf0 : 0 <= nf) by (unfold nf; lia).
  assert (Hr : r = ris + 128 * c) by reflexivity. assert (Hfa : fa = spb + c * 2 ^ 32 + 3758096384) by reflexivity.
  pose proof RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
  fold r in Rmx, Rnf, Rmfa, Rau, Ram, Rmu, Rmm, Rna, Rnfr, Wr. fold nf in Rnf.
  unfold art_pop_fpE in AE. rewrite <- Hr, <- Hfa in AE.
  (* [comment removed for export] *)
  destruct (art_clspop_D rE ME rom raw sp r (spb + c * 2 ^ 32) sz (cl_au cl) (cl_mu cl + 262144) nf new (cl_mu cl + 262144 - cl_au cl)
              (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
              E2 E8 E9 E10 E18 E19 E20 E21 ltac:(lia) Hsp' Hret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; lia)
              Hsz ltac:(lia) Hau0 Hnew Hcarve ltac:(lia) Hnf0 ltac:(lia)
              ltac:(eapply wr_grows; [exact GE|exact Wr]) ltac:(eapply wr_sub; [exact WFA|lia|lia])
              ltac:(ztr) ltac:(ztr) Emu' ltac:(ztr) ltac:(ztr) FP1 FP8 FP9 FP18 FP19 FP20 FP21 FP22)
    as (rD & MD & RUND & D10 & D2 & D1 & D8 & D9 & D18 & D19 & D20 & D21 & D22 & KD & GD & AD & Dnf & Dau & Dfa).
  fold fa in AD, Dfa.
  eapply ar_steps; [exact RUND|]. apply ar_done.
  assert (AMD : art_agree (art_pop_fpE sp t spb ris qs c km (cl_mfa cl) ++ [(fa + 4 * nf, 4 * new); (r + 16, 8); (r + 32, 8); (r + 68, 1)]) M MD).
  { unfold art_pop_fpE. rewrite <- Hr, <- Hfa. eapply art_agree_trans; [exact AE|exact AD]. }
  apply (K rD MD D10 D2 D1).
  - intros x Hx. cbn [In] in Hx.
    destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
      first [ exact D8 | exact D9 | exact D18 | exact D19 | exact D20 | exact D21 | exact D22 | rewrite KD by inl; apply KE; inl ].
  - eapply mem_grows_trans; [exact GE|exact GD].
  - eapply art_agree_sub; [exact AMD|]. unfold art_pop_fp, art_pop_fpE. rewrite <- Hr, <- Hfa. clear - Hmfa0 Hmfa2 Htot Hnf0 Hnew. zsub.
  - apply (art_region_rep_populate spb ris c mx cl M MD _ new mfa' Enew Hnew Emfa ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RR
             ltac:(eapply mem_grows_trans; [exact GE|exact GD]) AMD).
    + unfold art_pop_fpE. fold r fa. clear - Hr Hfa Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Emu Room1 Hmfa0 Hnf4 Hnf0 Hnew Htot Hmfa2. unfold apart in Atk, Ats. zgap.
    + unfold art_pop_fpE. fold r fa. clear - Hr Hfa Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Emu Room1 Hmfa0 Hnf4 Hnf0 Hnew Htot Hmfa2. unfold apart in Atk, Ats. zgap.
    + unfold art_pop_fpE. fold r fa. clear - Hr Hfa Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Emu Room1 Hmfa0 Hnf4 Hnf0 Hnew Htot Hmfa2. unfold apart in Atk, Ats. zgap.
    + unfold art_pop_fpE. fold r fa. clear - Hr Hfa Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Emu Room1 Hmfa0 Hnf4 Hnf0 Hnew Htot Hmfa2. unfold apart in Atk, Ats. zgap.
    + unfold art_pop_fpE. fold r fa. clear - Hr Hfa Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Emu Room1 Hmfa0 Hnf4 Hnf0 Hnew Htot Hmfa2. unfold apart in Atk, Ats. zgap.
    + exact Dnf.
    + ztr.
    + exact Dau.
    + ztr.
    + exact Dfa.
    + eapply wr_grows; [exact GD|exact WFA].
    + eapply wr_grows; [exact GD|exact WU].
  - intros j Hj. pose proof (SH j Hj) as C. ztr.
  - destruct ST as (m1' & m2' & sv' & S1 & S2 & S3). exists m1', m2', sv'. unfold apart in Atk. repeat split; ztr.
Qed.


#[using="Type"] Lemma art_populate_aruns :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
         (sp HI t ctx tp key tsd spb ris qs c km req mx m1 m2 sv : Z) (cl : art_cls),
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp ->
    getr regs 10 = Z_to_bv 64 1295832 -> getr regs 11 = Z_to_bv 64 (t + 2768) -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 (ris + 128 * c) ->
    getr regs 14 = Z_to_bv 64 req ->
    1 <= c <= 30 -> HI <= sp - 512 -> sp < 2 ^ 47 -> art_geo HI t ctx tp tsd spb ris qs ->
    1 <= req <= 8 -> AsanTab.class_size c * req <= 262144 ->
    wrA M (sp - 512) 512 -> wrA M t 4096 ->
    art_prim_consts spb ris M -> art_layout M -> art_tsd M tp key tsd ctx t ->
    art_region_rep spb ris c mx cl M -> art_cls_ok c cl -> cl_mu cl = 262144 * km ->
    cellA M (t + 2872) 8 m1 -> cellA M (t + 2880) 8 m2 -> cellA M (t + 2792) 8 sv ->
    cl_mu cl + 262144 <= 3758096384 ->
    art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912 ->
    wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km) 32768 ->
    wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048) 67108864 ->
    art_evok_list EVOK log (art_pop_events spb c cl) ->
    (forall regs' (M' : word -> option byte),
        getr regs' 10 = Z_to_bv 64 1 -> getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
        mem_grows M M' -> art_agree (art_pop_fp sp t spb ris qs c km) M M' ->
        art_region_rep spb ris c mx (art_cls_populate c cl) M' ->
        (forall j, 0 <= j < 32768 -> cellA M' (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + j) 1 250) ->
        (exists m1' m2' sv', cellA M' (t + 2872) 8 m1' /\ cellA M' (t + 2880) 8 m2' /\ cellA M' (t + 2792) 8 sv') ->
        Q (log ++ art_pop_events spb c cl) (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x57894 : word) M rom).
Proof.
  intros Q log regs M rom raw sp HI t ctx tp key tsd spb ris qs c km req mx m1 m2 sv cl
         H1 Hret H2 H4 H10 H11 H12 H13 H14 Hc HHI Hsp' GEO Hreq Hneed W Wt PC L T RR OK Emu Cm1 Cm2 Csv Room1 Room2 Wsh1 Wsh2 EV K.
  destruct GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  assert (Ac_i : apart ctx 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G15; lia).
  assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G16; lia).
  clear G9 G10 G15 G16.
  destruct PC as (Pspb & Pris & Prel & Ppm & Pmask & Ppg1 & Ppg2 & Pdec & Plim).
  destruct RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
  destruct OK as (_ & (Hau0 & Haumu) & Hrem0 & _ & _ & Hmu3 & (kf & Emfa) & (Hmfa0 & Hmfa1) & Hnf4 & _ & _).
  destruct (art_class_size_facts c Hc) as (Hsz & Hsz16).
  set (sz := AsanTab.class_size c) in *. set (nf := Z.of_nat (length (cl_free cl))) in *.
  set (au := cl_au cl) in *. set (mu := cl_mu cl) in *. set (mfa := cl_mfa cl) in *.
  assert (Hnf0 : 0 <= nf) by (unfold nf; lia).
  set (new := art_cls_new c cl). set (rem := (mu + 262144 - au) mod sz).
  assert (Enew : mu + 262144 - au = new * sz + rem).
  { unfold new, art_cls_new, rem. fold sz au mu. rewrite Z.mul_comm. apply Z.div_mod. lia. }
  assert (Hrem : 0 <= rem < sz) by (unfold rem; apply Z.mod_pos_bound; lia).
  assert (Hnew : 1 <= new). { destruct (Z_lt_le_dec new 1) as [Lt|Ge]; [|exact Ge]. exfalso. assert (new * sz <= 0) by nia. lia. }
  set (r := ris + 128 * c) in *. set (rb := spb + c * 2 ^ 32) in *.
  assert (Hr : 0x696000 <= r /\ r + 128 <= HI) by (unfold r; lia).
  assert (Er : r = ris + 128 * c) by reflexivity.
  assert (Hkm : 0 <= km) by lia.
  set (shb := 2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km) in *.
  set (addr := rb + mu).
  cbn [art_pop_events art_evok_list] in EV. fold nf new mu mfa in EV. destruct EV as [EV1 EV2].
  assert (Hneed1 : mu < au + sz * req). { assert (sz * 1 <= sz * req) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  (* [comment removed for export] *)
  destruct (art_clspop_A regs M rom raw sp (t + 2768) c r req spb qs au mu km (sz * req) H1 H2 H10 H11 H12 H13 H14
              ltac:(lia) Hsp' ltac:(lia) Hc ltac:(lia) ltac:(lia) Hreq ltac:(reflexivity) ltac:(lia) ltac:(lia) Espb Emu Hau0 Haumu Hneed1 Hneed Room1
              ltac:(unfold apart; lia) ltac:(eapply wr_sub; [exact W|lia|lia]) Pspb Rau Rmu Rmm Ppm ltac:(exact Prel) Ppg1 Ppg2 ltac:(destruct L as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X) Pdec)
    as (rA & MA & RUNA & ARGS & A1 & A2 & A8 & A21 & A22 & KA & GA & AA & FP1 & FP8 & FP9 & FP18 & FP19 & FP20 & FP21 & FP22 & FM1 & FM8 & FM9 & FM18 & EM1 & EM8 & EM9 & EM18 & EM19 & EM20).
  eapply ar_steps; [exact RUNA|].
  eapply (ar_mmap_fixed ASEGS EVOK GR Q log rA (0x8bc80 : word) (0x8bc84 : word) MA rom addr 262144 art_at_ecall_mmap ltac:(apply bv_eq; reflexivity) ARGS EV1).
  set (MZ := art_zfill MA addr 262144). set (rZ := regupd rA 10 (Z_to_bv 64 addr)).
  assert (AZ : art_agree [(addr, 262144)] MA MZ) by apply art_agree_zfill.
  assert (GZ : mem_grows MA MZ) by apply art_zfill_grows.
  assert (AMZ : art_agree [(sp - 464, 464); (addr, 262144)] M MZ). { eapply art_agree_sub; [eapply art_agree_trans; [exact AA|exact AZ]|]. zsub. }
  assert (GMZ : mem_grows M MZ) by (eapply mem_grows_trans; eassumption).
  pose proof (art_cell_norm _ _ _ _ Cm1) as Cm1n. pose proof (art_cell_norm _ _ _ _ Cm2) as Cm2n. pose proof (art_cell_norm _ _ _ _ Csv) as Csvn.
  pose proof (art_mod64_range m1) as Hm1n. pose proof (art_mod64_range m2) as Hm2n. pose proof (art_mod64_range sv) as Hsvn.
  set (m1n := m1 mod 2 ^ 64) in *. set (m2n := m2 mod 2 ^ 64) in *. set (svn := sv mod 2 ^ 64) in *.
  assert (Ccf : cellA M 0x1374b0 8 0x1d1768) by (destruct L as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (Hshb : shb = 2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km) by reflexivity.
  assert (Haddr : addr = spb + c * 2 ^ 32 + mu) by reflexivity.
  assert (Hrb : rb = spb + c * 2 ^ 32) by reflexivity.
  assert (LZ : art_layout MZ). { eapply art_layout_fp; [exact AMZ| |exact L]. intros z Hz. cbn. repeat split; lia. }
  assert (TZ : art_tsd MZ tp key tsd ctx t).
  { eapply art_tsd_fp; [exact AMZ| | |exact G19|exact G20|exact G21|exact G22|exact T].
    - intros z Hz. cbn. repeat split; lia.
    - intros z Hz. cbn. pose proof G17 as X. unfold apart in X. repeat split; lia. }
  assert (Ash_t : apart shb 32768 t 4096) by (pose proof At_s as X; unfold apart in X |- *; lia).
  assert (Ash_c : apart shb 32768 ctx 4096) by (pose proof Ac_s as X; unfold apart in X |- *; lia).
  assert (At_r : apart t 4096 r 128) by (pose proof G11 as X; unfold apart in X |- *; unfold r; lia).
  assert (At_a : apart t 4096 addr 262144) by (pose proof G11 as X; unfold apart in X |- *; lia).
  (* [comment removed for export] *)
  destruct (art_clspop_B rZ MZ rom sp tp key tsd ctx t r c spb qs au mu km nf sz new rem m1n m2n svn addr shb Haddr Hshb
              ltac:(unfold rZ; gres; exact A1) ltac:(unfold rZ; gres; exact A2) ltac:(unfold rZ; gres; rewrite KA by inl; exact H4) ltac:(unfold rZ; gres; exact A8)
              ltac:(unfold rZ; gres; f_equal; lia) ltac:(unfold rZ; gres; exact A21) ltac:(unfold rZ; gres; exact A22)
              ltac:(lia) Hsp' Hc Espb Emu Hkm ltac:(unfold kHighMemBeg; lia) ltac:(lia) Room1 Hsz Hau0 Haumu Enew Hrem ltac:(lia) ltac:(lia) Hm1n Hm2n Hsvn
              ltac:(lia) ltac:(lia) ltac:(rewrite Et; replace (4096 * qt + 2792) with ((512 * qt + 349) * 8) by lia; apply Z_mod_mult) ltac:(lia) ltac:(lia) At_r
              G19 G20 G21 G22 ltac:(lia) ltac:(lia) Ash_t ltac:(unfold apart; lia) Ash_c ltac:(lia)
              ltac:(eapply wr_grows; [exact GMZ|]; eapply wr_sub; [exact W|lia|lia]) ltac:(eapply wr_grows; [exact GMZ|exact Wsh1])
              ltac:(eapply wr_grows; [exact GMZ|]; eapply wr_sub; [exact Wt|lia|lia]) ltac:(eapply wr_grows; [exact GMZ|]; eapply wr_sub; [exact Wt|lia|lia])
              ltac:(eapply wr_grows; [exact GMZ|exact Wr]) LZ TZ
              ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a))
              ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(rewrite Haddr; ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(rewrite Haddr; ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a))
              ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a)))
    as (rB & MB & RUNB & B1 & B2 & B4 & B8 & B9 & B10 & B11 & B12 & B13 & B18 & B19 & B20 & B21 & B22 & KB & GB & AB & SH & Sm1 & Sm2 & Ssv & Smu).
  eapply ar_steps; [exact RUNB|].
  set (fa := spb + c * 2 ^ 32 + 3758096384) in *.
  assert (Hfa : fa = spb + c * 2 ^ 32 + 3758096384) by reflexivity.
  assert (WUZ : wrA MZ rb (mu + 262144)).
  { apply wr_join; [lia|lia|lia|lia|eapply wr_grows; [exact GMZ|exact Wu]|]. replace (rb + mu) with addr by lia. unfold MZ. apply wr_zfill; lia. }
  assert (AMB : art_agree [(sp - 464, 464); (addr, 262144); (shb, 32768); (t + 2872, 16); (t + 2792, 8); (r + 48, 8)] M MB).
  { eapply art_agree_sub; [eapply art_agree_trans; [exact AMZ|exact AB]|]. zsub_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a). }
  assert (GMB : mem_grows M MB) by (eapply mem_grows_trans; eassumption).
  assert (Ash_r : apart shb 32768 r 128) by (unfold apart, r; lia).
  assert (Hcarve : au + new * sz <= mu + 262144) by lia.
  assert (Hfb : sz <= mu + 262144 - au) by lia.
  assert (KBR : forall x : reg, In x [3; 4; 23; 24; 25; 26; 27]%bv -> getr rB x = getr regs x).
  { intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
      first [ rewrite B4; symmetry; exact H4 | rewrite KB by inl; unfold rZ; gres; apply KA; inl ]. }
  destruct (Z_le_gt_dec (4 * (nf + new)) mfa) as [Hwarm|Hmap].
  - (* [comment removed for export] *)
    assert (Eleb : (4 * (nf + new) <=? mfa) = true) by (apply Z.leb_le; exact Hwarm).
    assert (Emfa' : mfa = art_cls_mfa' cl (nf + new)) by (unfold art_cls_mfa'; fold mfa; rewrite Eleb; reflexivity).
    assert (Eev : art_pop_events spb c cl = [AMmapFixed addr 262144]).
    { unfold art_pop_events. fold nf new mfa mu. rewrite Eleb. unfold addr, rb. reflexivity. }
    destruct (art_clspop_Cw rB MB rom sp r (nf + new) mfa B1 B2 B11 B13 ltac:(lia) Hsp' ltac:(lia) ltac:(lia) ltac:(lia) Hwarm ltac:(lia)
                ltac:(eapply wr_grows; [exact GMB|]; eapply wr_sub; [exact W|lia|lia]) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)))
      as (rC & MC & RUNC & C10 & C2 & KC & GC & AC).
    eapply ar_steps; [exact RUNC|]. rewrite Eev in K.
    apply (art_populate_tail Q (log ++ [AMmapFixed addr 262144]) regs rC M MC rom raw sp HI t spb ris qs c km mx new mfa cl
             Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 At_s Emu Hau0 Haumu Room1 Hmfa0 Hnf4 eq_refl Hnew Hcarve Hfb Emfa' ltac:(lia) Hmfa1 Hwarm
             ltac:(unfold art_region_rep; fold r fa nf; repeat split; assumption)
             C10 C2 ltac:(rewrite KC by inl; exact B8) ltac:(rewrite KC by inl; exact B9) ltac:(rewrite KC by inl; exact B18)
             ltac:(rewrite KC by inl; exact B19) ltac:(rewrite KC by inl; exact B20) ltac:(rewrite KC by inl; exact B21)).
    + intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; (rewrite KC by inl; apply KBR; inl).
    + eapply mem_grows_trans; [exact GMB|exact GC].
    + eapply art_agree_sub; [eapply art_agree_trans; [exact AMB|exact AC]|]. unfold art_pop_fpE. fold r fa. clear - Haddr Hshb Emu Hmfa0 Hmfa1. zsub.
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
    + fold r mu. ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
    + fold r. ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
    + fold fa. eapply wr_grows; [eapply mem_grows_trans; [exact GMB|exact GC]|exact Wfa].
    + fold rb mu. eapply wr_grows; [eapply mem_grows_trans; [exact GB|exact GC]|exact WUZ].
    + intros j Hj. pose proof (SH j Hj) as C. rewrite Hshb in C. ztr_c ltac:(clear - Hj Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
    + exists (m1n + 1), (m2n + 262144), (svn + 262144). repeat split; ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew).
    + exact K.
  - (* [comment removed for export] *)
    assert (Eleb : (4 * (nf + new) <=? mfa) = false) by (apply Z.leb_gt; lia).
    set (q := (4 * (nf + new) + 262143) / 262144). set (rr := (4 * (nf + new) + 262143) mod 262144).
    assert (Eq : 4 * (nf + new) + 262143 = 262144 * q + rr) by (unfold q, rr; apply Z.div_mod; lia).
    assert (Hrr : 0 <= rr < 262144) by (unfold rr; apply Z.mod_pos_bound; lia).
    assert (Emfa' : 262144 * q = art_cls_mfa' cl (nf + new)) by (unfold art_cls_mfa'; fold mfa; rewrite Eleb; fold q; lia).
    assert (Hq : 262144 * q <= 536870912) by (rewrite Emfa'; exact Room2).
    clearbody q rr.
    set (addr2 := fa + mfa). set (len2 := 262144 * q - mfa). set (shb2 := 2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048 + 32768 * kf).
    assert (Haddr2 : addr2 = spb + c * 2 ^ 32 + 3758096384 + mfa) by reflexivity.
    assert (Hlen2 : len2 = 262144 * q - mfa) by reflexivity.
    assert (Hshb2 : shb2 = 2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048 + 32768 * kf) by reflexivity.
    rewrite Eleb in EV2. cbn [art_evok_list] in EV2. destruct EV2 as [EV2 _]. rewrite <- Emfa' in EV2. fold fa addr2 len2 in EV2.
    assert (Eev : art_pop_events spb c cl = [AMmapFixed addr 262144; AMmapFixed addr2 len2]).
    { unfold art_pop_events. fold nf new mfa mu. rewrite Eleb, <- Emfa'. unfold addr, rb, addr2, len2, fa. reflexivity. }
    assert (Hkf : 0 <= kf) by lia. assert (Hq1 : kf + 1 <= q) by lia.
    destruct (art_clspop_Cm1 rB MB rom sp r c spb qs (nf + new) mfa kf q rr addr2 Haddr2 B1 B2 B10 B11 B12 B13
                ltac:(lia) Hsp' Hc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Espb ltac:(lia) ltac:(lia) Emfa Eq Hrr Hq
                ltac:(eapply wr_grows; [exact GMB|]; eapply wr_sub; [exact W|lia|lia])
                ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew)))
      as (r1 & M1 & RUN1 & ARGS2 & C1_1 & C1_2 & C1_8 & K1 & G1m & A1m & E1c & E8c & E9c & E18c & E19c & F1c & F8c & F9c & F18c & D1c & D8c & D9c & D18c & D19c & D20c).
    fold len2 in F18c, D8c, D18c, C1_8, ARGS2.
    eapply ar_steps; [exact RUN1|].
    eapply (ar_mmap_fixed ASEGS EVOK GR Q (log ++ [AMmapFixed addr 262144]) r1 (0x8bc80 : word) (0x8bc84 : word) M1 rom addr2 len2 art_at_ecall_mmap ltac:(apply bv_eq; reflexivity) ARGS2 EV2).
    set (MZ2 := art_zfill M1 addr2 len2). set (rZ2 := regupd r1 10 (Z_to_bv 64 addr2)).
    assert (AZ2 : art_agree [(addr2, len2)] M1 MZ2) by apply art_agree_zfill.
    assert (GZ2 : mem_grows M1 MZ2) by apply art_zfill_grows.
    assert (AM2 : art_agree [(sp - 512, 512); (addr, 262144); (shb, 32768); (t + 2872, 16); (t + 2792, 8); (r + 48, 8); (addr2, len2)] M MZ2).
    { eapply art_agree_sub; [eapply art_agree_trans; [eapply art_agree_trans; [exact AMB|exact A1m]|exact AZ2]|]. zsub_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2). }
    assert (GM2 : mem_grows M MZ2) by (eapply mem_grows_trans; [eapply mem_grows_trans; [exact GMB|exact G1m]|exact GZ2]).
    assert (LZ2 : art_layout MZ2).
    { eapply art_layout_fp; [exact AM2| |exact L]. intros z Hz. pose proof At_i as X. unfold apart in X. cbn. clear - Hz X HHI G1 G4 Eris G6 Hc Haddr Hshb Haddr2 Espb Emu Hr Hkm Hmfa0. repeat split; lia. }
    assert (TZ2 : art_tsd MZ2 tp key tsd ctx t).
    { eapply art_tsd_fp; [exact AM2| | |exact G19|exact G20|exact G21|exact G22|exact T].
      - intros z Hz. pose proof At_i as X. unfold apart in X. cbn. clear - Hz X HHI G1 G4 Eris G6 Hc Haddr Hshb Haddr2 Espb Emu Hr Hkm Hmfa0. repeat split; lia.
      - intros z Hz. pose proof G17 as X1. pose proof G18 as X2. pose proof Ac_s as X3. unfold apart in X1, X2, X3. cbn.
        clear - Hz X1 X2 X3 HHI G1 G2 G4 Eris G6 G13 G14 Hc Haddr Hshb Haddr2 Espb Emu Hr Er Hkm Room1 Hmfa0 Hq Hlen2 Hfa. repeat split; lia. }
    pose proof (art_cell_norm _ _ _ _ Sm1) as Sm1n. pose proof (art_cell_norm _ _ _ _ Sm2) as Sm2n.
    pose proof (art_mod64_range (m1n + 1)) as Hm1n'. pose proof (art_mod64_range (m2n + 262144)) as Hm2n'.
    set (m1n' := (m1n + 1) mod 2 ^ 64) in *. set (m2n' := (m2n + 262144) mod 2 ^ 64) in *.
    assert (Ash2_t : apart shb2 (32768 * (q - kf)) t 4096) by (pose proof At_s as X; unfold apart in X |- *; clear - X Hshb2 Espb G4 Eris G6 G1 G2 HHI Hc Hkf Hq1 Hq; lia).
    assert (Ash2_c : apart shb2 (32768 * (q - kf)) ctx 4096) by (pose proof Ac_s as X; unfold apart in X |- *; clear - X Hshb2 Espb G4 Eris G6 G1 G2 HHI Hc Hkf Hq1 Hq; lia).
    assert (Ash2_r : apart shb2 (32768 * (q - kf)) r 128) by (unfold apart, r; clear - Hshb2 Espb G4 Eris G6 G1 G2 HHI Hc Hkf Hq1 Hq; lia).
    assert (Wsh2' : wrA MZ2 shb2 (32768 * (q - kf))). { eapply wr_grows; [exact GM2|]. eapply wr_sub; [exact Wsh2|lia|lia]. }
    destruct (art_clspop_Cm2 rZ2 MZ2 rom sp tp key tsd ctx t r c spb qs mfa kf q m1n' m2n' addr2 len2 shb2 (getr rB 8) (getr rB 9) (getr rB 18) (getr rB 19) (getr rB 20)
                Haddr2 Hlen2 Hshb2
                ltac:(unfold rZ2; gres; exact C1_1) ltac:(unfold rZ2; gres; exact C1_2) ltac:(unfold rZ2; gres; rewrite K1 by inl; exact B4)
                ltac:(unfold rZ2; gres; exact C1_8) ltac:(unfold rZ2; gres; reflexivity)
                ltac:(lia) Hsp' Hc Espb Emfa Hkf Hq1 Hq ltac:(unfold kHighMemBeg; lia) ltac:(lia) Hm1n' Hm2n'
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) At_r G19 G20 G21 G22 ltac:(lia) ltac:(lia) Ash2_t Ash2_r Ash2_c ltac:(lia)
                ltac:(eapply wr_grows; [exact GM2|]; eapply wr_sub; [exact W|lia|lia]) Wsh2'
                ltac:(eapply wr_grows; [exact GM2|]; eapply wr_sub; [exact Wt|lia|lia]) ltac:(eapply wr_grows; [exact GM2|exact Wr]) LZ2 TZ2
                ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r))
                ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r))
                ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)) ltac:(ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)))
    as (rC & MC & RUNC & C10 & C2 & C8 & C9 & C18 & C19 & C20 & KC & GC & AC & Tm1 & Tm2 & Tmfa).
    eapply ar_steps; [exact RUNC|]. rewrite Eev in K. rewrite <- app_assoc. cbn [app].
    assert (GMC : mem_grows M MC) by (eapply mem_grows_trans; [exact GM2|exact GC]).
    assert (AMC : art_agree [(sp - 512, 512); (addr, 262144); (shb, 32768); (t + 2872, 16); (t + 2792, 8); (r + 48, 8); (addr2, len2); (shb2, 32768 * (q - kf)); (r + 24, 8)] M MC).
    { eapply art_agree_sub; [eapply art_agree_trans; [exact AM2|exact AC]|]. zsub_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r). }
    assert (KCR : forall x : reg, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rC x = getr rB x).
    { intros x Hx. cbn [In] in Hx.
      destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; (rewrite KC by inl; unfold rZ2; gres; apply K1; inl). }
    apply (art_populate_tail Q (log ++ [AMmapFixed addr 262144; AMmapFixed addr2 len2]) regs rC M MC rom raw sp HI t spb ris qs c km mx new (262144 * q) cl
             Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 At_s Emu Hau0 Haumu Room1 Hmfa0 Hnf4 eq_refl Hnew Hcarve Hfb Emfa' ltac:(lia) Hq ltac:(lia)
             ltac:(unfold art_region_rep; fold r fa nf; repeat split; assumption)
             C10 C2 ltac:(rewrite C8; exact B8) ltac:(rewrite C9; exact B9) ltac:(rewrite C18; exact B18)
             ltac:(rewrite C19; exact B19) ltac:(rewrite C20; exact B20) ltac:(rewrite KCR by inl; exact B21)).
    + intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; (rewrite KCR by inl; apply KBR; inl).
    + exact GMC.
    + eapply art_agree_sub; [exact AMC|]. unfold art_pop_fpE. fold r fa. clear - Haddr Hshb Emu Hmfa0 Hmfa1 Haddr2 Hlen2 Hshb2 Hfa Hq Hq1 Hkf Emfa. zsub.
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
    + ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
    + fold r mu. ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
    + fold r. exact Tmfa.
    + fold fa. eapply wr_grows; [exact GC|]. replace (262144 * q) with (mfa + len2) by lia.
      apply wr_join; [lia|lia|lia|lia|eapply wr_grows; [exact GM2|exact Wfa]|]. fold addr2. unfold MZ2. apply wr_zfill; lia.
    + fold rb mu. eapply wr_grows; [eapply mem_grows_trans; [exact GB|]; eapply mem_grows_trans; [exact G1m|]; eapply mem_grows_trans; [exact GZ2|exact GC]|exact WUZ].
    + intros j Hj. pose proof (SH j Hj) as C. rewrite Hshb in C. ztr_c ltac:(clear - Hj Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r).
    + exists (m1n' + 1), (m2n' + len2), (svn + 262144). repeat split; [exact Tm1|exact Tm2|ztr_c ltac:(clear - Hc HHI Hsp' G1 G2 Espb G4 Eris G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 At_i At_s Ac_i Ac_s Emu Hmu3 Emfa Hmfa0 Hmfa1 Hnf4 Room1 Hnf0 Hr Er Hkm Hshb Haddr Hrb Ash_t Ash_c At_r At_a Hfa Ash_r Hnew Hq Hq1 Hkf Haddr2 Hlen2 Hshb2 Ash2_t Ash2_c Ash2_r)].
    + exact K.
Qed.
End Spec.
