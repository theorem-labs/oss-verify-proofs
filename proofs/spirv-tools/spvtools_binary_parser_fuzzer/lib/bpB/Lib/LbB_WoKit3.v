(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoSt LbB_WoR2 LbB_WoE0.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma addressable_sub8 : forall m A n o w, addressable m A n -> n mod 8 = 0 -> o mod 8 = 0 -> w mod 8 = 0 ->
  0 <= o -> 0 <= w -> o + w <= n -> addressable m (A + o) w.
Proof.
  intros m A n o w AD Hn Ho Hw H1 H2 H3.
  destruct (addressable_split8 m A n o AD Hn Ho ltac:(lia)) as [_ AA2].
  destruct (addressable_split8 m (A + o) (n - o) w AA2 ltac:(Z.div_mod_to_equations; lia) Hw ltac:(lia)) as [AA3 _].
  exact AA3.
Qed.

Section S0.
Context {HCEIL : HeapCeil}.

Lemma stack0_addr : forall m lo hi A n, stack0 m lo hi -> lo <= A -> A + n <= hi -> A mod 8 = 0 -> n mod 8 = 0 -> 0 <= n ->
  addressable m A n.
Proof.
  intros m lo hi A n (g & G1 & G2 & G3 & AD) H1 H2 H3 H4 H5.
  pose proof aceil_facts as ACF.
  replace A with (g + (A - g)) by lia.
  eapply addressable_sub8; [exact AD | exact G3 | | exact H4 | lia | lia | lia].
  assert (g mod 8 = 0).
  { destruct AD as (_ & _ & G8 & _). exact G8. }
  Z.div_mod_to_equations. lia.
Qed.
End S0.

Section WKit3.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma wscr_blk : forall LF s LB (mr m : mem) p A n iv, as_RFS H LF mr -> as_RHEAP H s LB m -> In (p, A, n) LB -> fs_scratch H LF iv ->
    (A + n <= fst iv \/ snd iv <= A) /\ (sh A + nsh n <= fst iv \/ snd iv <= sh A).
  Proof.
    intros LF s LB mr m p A n iv RF RH IN FS.
    pose proof (ah_blocks H HH _ _ _ _ RH IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
    pose proof aceil_facts as ACF.
    assert (OB : fsobj H LF A n) by (left; lia).
    split.
    - exact (fsobj_scratch H HH LF A n mr iv RF OB ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia) BAPP FS).
    - exact (fsobj_scratch_sh H HH LF A n mr iv RF OB ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia) FS).
  Qed.

  Lemma wscr_apart : forall e ff fp m iv, wpre H e -> as_RFS H ((6, ff, fp) :: w_LF e) m -> fresh_frame H (w_LF e) 6 ff fp ->
    fs_scratch H ((6, ff, fp) :: w_LF e) iv -> wfc_apart H e ff iv.
  Proof.
    intros e ff fp m iv HP RF FF FS.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    destruct (wfsw_ok H HH e ff fp m iv RF FF CE FS) as (_ & _ & _ & B4 & B5 & B6 & B7 & _ & _).
    unfold wfc_apart. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | lia].
  Qed.

  Lemma xpres_u8arr : forall LB SP X m m' A bs, xpres H LB SP X m m' -> u8arr asegs m A bs ->
    xclient_range H LB SP X A (Z.of_nat (length bs)) -> u8arr asegs m' A bs.
  Proof.
    intros LB SP X m m' A bs XP [B W] CR. split; [eapply xpres_bytes_at; [exact XP | exact B | exact CR] | eapply xpres_wr_at; [exact XP | exact W | exact CR]].
  Qed.

  Lemma wfc_xpres : forall e ff fp LB X m m', wpre H e -> fresh_frame H (w_LF e) 6 ff fp ->
    wfc H e ff m -> xpres H LB (wS1 e) X m m' -> Forall (wfc_apart H e ff) X -> wfc H e ff m'.
  Proof.
    intros e ff fp LB X m m' HP FF (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) XP FX.
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    assert (FA : forall iv, In iv X -> wfc_apart H e ff iv) by (intros iv Hiv; exact (proj1 (Forall_forall _ _) FX iv Hiv)).
    assert (XC : forall A n, aclient_range H LB (wS1 e) A n -> (forall iv, In iv X -> A + n <= fst iv \/ snd iv <= A) ->
                   xclient_range H LB (wS1 e) X A n).
    { intros A n CR K. split; [exact CR|]. apply Forall_forall. exact K. }
    assert (FR : forall A n, ff <= A -> A + n <= ff + 4096 -> aclient_range H LB (wS1 e) A n)
      by (intros A n K1 K2; right; right; right; right; left; lia).
    assert (SR : forall A n, wS1 e <= A -> aclient_range H LB (wS1 e) A n) by (intros A n K; left; exact K).
    split; [eapply xpres_rw_cells; [exact XP | exact C1 | apply XC; [apply FR; cbn; lia | intros iv Hiv; destruct (FA iv Hiv) as (K & _); cbn; lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C2 | apply XC; [apply FR; cbn; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & K & _); cbn; lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C3 | apply XC; [apply FR; cbn; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & K & _); cbn; lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C4 | apply XC; [apply FR; cbn; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & K & _); cbn; lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C5 | apply XC; [apply FR; cbn; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & K & _); cbn; lia]]|].
    split; [eapply xpres_u8arr; [exact XP | exact C6 | rewrite length_map; cbn [length WO_SH2C app repeat];
              apply XC; [right; right; right; right; right; left; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & K & _); cbn; lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C7 | apply XC; [apply SR; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & _ & K & _); cbn; lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C8 | apply XC; [apply SR; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & _ & K & _); cbn; lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C9 | apply XC; [apply SR; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & _ & K & _); cbn; lia]]|].
    split; [eapply xpres_rw_cells; [exact XP | exact C10 | apply XC; [apply SR; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & _ & K & _); cbn; lia]]|].
    eapply xpres_rw_cells; [exact XP | exact C11 | apply XC; [apply SR; lia | intros iv Hiv; destruct (FA iv Hiv) as (_ & _ & _ & _ & _ & _ & K); cbn; lia]].
  Qed.
End WKit3.

Lemma state_sh_emptied : forall {HCEIL : HeapCeil} m c, state_sh m (state_emptied c).
Proof.
  intros HCEIL m c. unfold state_sh, state_emptied. cbn [st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
  refine (conj (umap_sh_empty _ _ _) (conj (umap_sh_empty _ _ _) (conj (umap_sh_empty _ _ _) (conj _ (conj _ _)))));
    intros X; exfalso; apply X; reflexivity.
Qed.
