(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac InitMem ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt
     FsKit AFake_iface F_m2s_b AFake_arep AFake_sf5 AU_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afake_untouched_ns (L : alayout) (W : list (Z * Z)) : Prop :=
  Forall (fun iv => (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
                 /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
                 /\ (snd iv <= 0x1148e8 \/ 0x1148e8 + 8 <= fst iv)
                 /\ (snd iv <= 0x64e9e8 \/ 0x64e9e8 + 16 <= fst iv)
                 /\ (snd iv <= 0x64e9f8 \/ 0x64e9f8 + 8 <= fst iv)
                 /\ (snd iv <= 0x64ea18 \/ 0x64ea18 + 8 <= fst iv)
                 /\ (snd iv <= 0x1ad231 \/ 0x1ad231 + 1 <= fst iv)
                 /\ (snd iv <= 0x1ab118 \/ 0x1ab118 + 4 <= fst iv)) W.

Lemma afake_frame_ns : forall L LB m m' W,
  AFAKE L LB m -> munch W m m' -> wmono bsegs m m' -> afake_untouched_ns L W -> AFAKE L LB m'.
Proof.
  intros L LB m m' W (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV) MU WM UT.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11). unfold FAKESZ in *.
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1. destruct G5 as (G5s & G5i & G5). destruct G7 as (G7s & G7i & G7).
  unfold iclr, sclr, AIMG_LO, AIMG_HI, KLS in G5s, G5i, G7s, G7i.
  assert (DF : disjoint_from W (al_fake L) 11571200) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8); exact X1).
  assert (DD : disjoint_from W (al_dtls L) 4096) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8); exact X2).
  assert (D1 : disjoint_from W 0x1148e8 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8); exact X3).
  assert (D2 : disjoint_from W 0x64e9e8 16) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8); exact X4).
  assert (D3 : disjoint_from W 0x64e9f8 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8); exact X5).
  assert (D4 : disjoint_from W 0x64ea18 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8); exact X6).
  assert (D5 : disjoint_from W 0x1ad231 1) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8); exact X7).
  assert (D6 : disjoint_from W 0x1ab118 4) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8); exact X8).
  split; [exact G|].
  split.
  { destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). unfold afake_cells.
    repeat lazymatch goal with |- _ /\ _ => split end;
      try (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize Nat.add]; first [assumption | eapply disjoint_from_sub; [exact DD| lia| lia| lia]]]).
    eapply dc_at_any2; [exact C8| exact WM| clear -G7i; lia]. }
  split.
  { exists h0, h1, h2, hs. eapply rw_cells_transport; [exact HS| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]. }
  split; [eapply rw_cells_transport; [exact LOG| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply rw_cells_transport; [exact NGC| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
  split.
  { eapply dc_at_any; [exact DC2| exact WM|]. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations; lia. }
  split.
  - intros c pos b Hc Hp Hb NZ. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) in Hb by (assumption || lia). eauto.
  - intros c F n Hin. destruct (LV c F n Hin) as (Hc & Hn & pos & Hp & HF & Hb). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) by (assumption || lia). exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation FB5 F := (mkABlock (ABFake 5) F 2048).
Definition SF5_STACK_P : Z := 16.

Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Hypothesis HL : ahole_laws (AFake_arep.AH DI AQ ASEC).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation AH := (AFake_arep.AH DI AQ ASEC).

Definition sf5_postP (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st LB m'
    /\ (forall a, in_block LB a -> m' (wa (shad a)) = m (wa (shad a))).

Theorem stack_free_5_P : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo F : Z),
  AHEAP_P AH L RNG st (FB5 F :: LB) m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SF5_STACK_P ->
  a0 = Z_to_bv 64 F ->
  rw_cells bsegs m (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))] ->
  rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (sf5_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASF5_ENTRY) fc None m (seg_rom bsegs)).
Proof.
  intros until F. intros AHP MI ST LO SPL A0 C2040 RSTK. unfold SF5_STACK_P in SPL.
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AFake_arep.AH ah_fake] in HFK.
  pose proof (fake_flag_P DI AQ ASEC CI CI_OK L RNG st (FB5 F :: LB) m 5 F 2048 AHP ltac:(left; reflexivity))
    as (FLC & FLR & FLB & FLT & FLD & FLCI).
  pose proof (afake_lb L _ m 5 F 2048 HFK ltac:(left; reflexivity)) as (Hc & Hn & Npos & F64 & FLO & FHI & FK & FC & pos & Hp & HF & EF & FR5).
  assert (NI : ~ In (FB5 F) LB) by (destruct BL as (_ & _ & _ & ND); inversion ND; assumption).
  pose proof HFK as (G & CE & HS & LOG & NGC & DC1 & DC2 & FL & LV).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof (ablk_lin _ _ FK) as (FK1 & FK2 & FK3 & FK4).
  pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, iclr, AIMG_LO, AIMG_HI, KLS in G5s, G5i, G7s, G7i. unfold AIMG_HI in GL1, FK1. pose proof atop_range as ATR.
  destruct (AREP_cells DI AQ ASEC L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  unfold FAKESZ in *.
  set (flag := fflag L 5 F) in *.
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) <= shad F /\ shad F + 256 <= shad (al_fake L) + 1446400).
  { rewrite SHF, SHS. clear - FLO FHI F64. Z.div_mod_to_equations. lia. }
  destruct SHB as [SB1 SB2].
  assert (SBAND : 0x7fff8000 <= shad F /\ shad F + 256 <= 0x10007fff8000).
  { rewrite SHF. pose proof FK as FKb. unfold ablk, AIMG_HI, KLS in FKb. clear - FKb FHI F64 ATR. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 256 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DSH.
  destruct DSH as [shj CSH]. change (Z.to_nat 256) with 256%nat in CSH.
  (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (stack_free5_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m lo F flag
              (Z_to_bv 8 1) shj);
      first [ eassumption
            | lia
            | (pose proof FK as FKb; unfold ablk, AIMG_HI, KLS, KLOW, KHIGH, KEND in FKb |- *; destruct FKb as [FKb|FKb]; [left|right]; clear - FKb ATR; lia)
            | (clear - FLO GL2; lia)
            | (clear - FC; lia)
            | (clear - FLB; apply ablk_lin in FLB; unfold AIMG_HI in FLB; lia)
            | (clear - FLT; lia)
            | (subst flag; clear - FR5 FLO; lia)
            | (pose proof G2 as G2b; unfold ablk, AIMG_HI, KLS in G2b; subst flag; clear - G2b FR5 SBAND; lia)
            | (pose proof FK as FKb; unfold ablk, AIMG_HI, KLS in FKb; clear - FKb SBAND; lia)
            | (clear - SBAND ATR; lia)
            | (eapply rng_sub'; [exact A7| clear - FLO FHI; lia])
            | (eapply rng_sub'; [exact A7| subst flag; clear - FR5; lia])
            | (eapply rng_sub'; [exact A8| clear - SB1 SB2; lia])
            | idtac ]. }
  cbv beta. intros ms' (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & EQ & MU & WM & MI' & ST' & FL' & SH').
  unfold sf5_W in MU.
  (* [comment removed for export] *)
  assert (AR' : AREP AH L st X m').
  { eapply (AREP_frame_ext' DI AQ ASEC HL L st X m m' _ ALO AR MU WM).
    rewrite SHL. repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; subst flag; clear - FR5; lia| right; left; lia| constructor]. }
  (* [comment removed for export] *)
  set (m1 := write_to_mem m (wa flag) [Z_to_bv 8 0]).
  assert (AF1 : AFAKE L LB m1) by (subst m1 flag; exact (afake_release L LB m 5 F 2048 HFK NI)).
  assert (FLV : m' (wa flag) = Some (Z_to_bv 8 0)).
  { apply (rw_C1_high m' flag _ FL'). subst flag. clear - FR5 GL1. lia. }
  assert (M1F : m1 (wa flag) = Some (Z_to_bv 8 0)).
  { subst m1. rewrite write_to_mem_spec by (cbn; subst flag; clear - FR5 GL1 G3 ATR; lia). rewrite wa_unsigned by (subst flag; clear - FR5 GL1 G3 ATR; lia).
    replace (flag <=? flag) with true by (symmetry; apply Z.leb_refl). cbn [length andb]. rewrite Z.sub_diag.
    replace (flag <? flag + Z.of_nat 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  assert (MU1 : munch [(bv_unsigned sp - 16, bv_unsigned sp); (shad F, shad F + 256)] m1 m').
  { intros x Hx. destruct (Z.eq_dec (bv_unsigned x) flag) as [E|NE].
    - rewrite <- (Z_to_bv_bv_unsigned x). rewrite E. fold (wa flag). rewrite FLV, M1F. reflexivity.
    - rewrite MU; [| cbn in Hx |- *; lia]. subst m1. rewrite write_to_mem_spec by (cbn; subst flag; clear - FR5 GL1 G3 ATR; lia).
      pose proof (bv_unsigned_in_range _ x) as XR.
      replace ((flag <=? bv_unsigned x) && (bv_unsigned x <? flag + Z.of_nat (length [Z_to_bv 8 0])))%bool with false; [reflexivity|].
      cbn [length]. symmetry. apply andb_false_iff. destruct (Z.le_gt_cases flag (bv_unsigned x)); [right; apply Z.ltb_ge; lia| left; apply Z.leb_gt; lia]. }
  assert (WM1 : wmono bsegs m1 m').
  { intros x Hx. apply WM. subst m1. unfold wview in *. rewrite write_to_mem_spec in Hx by (cbn; subst flag; clear - FR5 GL1 G3 ATR; lia).
    destruct ((flag <=? bv_unsigned x) && (bv_unsigned x <? flag + Z.of_nat (length [Z_to_bv 8 0])))%bool eqn:B; [| exact Hx].
    apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. cbn [length] in B2.
    assert (XE : x = wa flag) by (rewrite <- (Z_to_bv_bv_unsigned x); unfold wa; f_equal; lia). subst x.
    destruct FLC as [_ [_ [_ WR]]]. specialize (WR 0 ltac:(cbn; lia)). rewrite Z.add_0_r in WR. exact WR. }
  assert (AF' : AFAKE L LB m').
  { apply (afake_frame_ns L LB m1 m' _ AF1 MU1 WM1). unfold afake_untouched_ns.
    pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd]; (repeat split); lia. }
  (* [comment removed for export] *)
  assert (BL' : ablocks L st X LB) by exact (ablocks_tail L st X _ LB BL).
  assert (AHP' : AHEAP_P AH L RNG st LB m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AFake_arep.AH ah_fake]. exact AF'. }
  (* [comment removed for export] *)
  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= F \/ F + 2048 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE DI AQ ASEC L RNG st (FB5 F :: LB) m p A' n' AHP ltac:(right; exact Hb)) as [[Q1 [Q2 [Q3 Q4]]] D].
      split; [exact Q1|]. clear - Q2 Q3 Q4 D FLO FHI ATR. lia.
    - pose proof (afake_lb L (FB5 F :: LB) m c' A' n' HFK ltac:(right; exact Hb)) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & _).
      pose proof (afake_lb_disjoint L (FB5 F :: LB) m c' A' n' 5 F 2048 HFK ltac:(right; exact Hb) ltac:(left; reflexivity)
                    ltac:(intros E; apply NI; rewrite <- E; exact Hb)) as DJ.
      split; [exact X3|]. clear - X4 DJ. lia. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') -> 0 <= a' < 2^47 /\ ~ (F <= a' < F + 2048)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ clear - X1 FK3 FHI ATR; lia | pose proof (CI_OK iv Hiv); unfold AIMG_HI in H; clear - Hr H FK1; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3). cbn in Y1, Y2, Y3, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Hr ATR. lia. }
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hca. split; [| intros W0; apply WM; exact W0].
    assert (FLCIB : forall iv, In iv CI -> ~ (fst iv <= flag < snd iv)) by (intros iv Hiv Hr; apply FLCI; exists iv; split; [exact Hiv| exact Hr]).
    destruct Hca as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply MU. cbn. rewrite wa_unsigned by lia. clear - Hs SPL LO FLT SBAND ATR. lia.
    - pose proof (CI_OK iv Hiv). pose proof (FLCIB iv Hiv). unfold AIMG_HI in H. apply MU. cbn. rewrite wa_unsigned by lia.
      clear - H H0 Hr SPL LO SBAND ATR. lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3). pose proof (FLD b ltac:(right; exact Hb)) as FDB. unfold ablk, AIMG_HI, KLS in Y1. apply MU. cbn. rewrite wa_unsigned by lia.
      clear - Hr Y1 Y2 Y3 FDB SPL LO SBAND ATR. lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *. apply MU. cbn. rewrite wa_unsigned by lia.
      assert (FLA : flag < 0x7fff7000 \/ 0x10007fff8000 <= flag) by (pose proof G2 as G2b; unfold ablk, AIMG_HI, KLS in G2b; subst flag; clear - G2b FR5; lia).
      rewrite SHF in *. clear - A'R NA F64 FLA SPL LO ATR SBAND. Z.div_mod_to_equations. lia. }
  subst ms'. unfold sf5_postP.
  exists x0, x1, x2, y0, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  (* [comment removed for export] *)
  intros a (b & Hb & Hr). destruct (BLK b Hb) as (Y1 & Y2 & Y3). pose proof (ablk_lin _ _ Y1) as (YL1 & YL2 & YL3 & YL4). unfold AIMG_HI in YL1.
  assert (SHA : shad a = 2147450880 + a / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (FLA : flag < 0x7fff7000 \/ 0x10007fff8000 <= flag) by (pose proof G2 as G2b; unfold ablk, AIMG_HI, KLS in G2b; subst flag; clear - G2b FR5; lia).
  rewrite SHA in *. apply MU. cbn. rewrite wa_unsigned by (clear - YL1 YL2 YL4 Hr; Z.div_mod_to_equations; lia).
  rewrite SHF. clear - Hr YL1 YL2 YL3 YL4 Y3 FLA F64 SPL LO SBAND ATR. Z.div_mod_to_equations. lia.
Qed.
End S.

(* [comment removed for export] *)
Section Inst.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Hypothesis HL : ahole_laws (AFake_arep.AH DI AQ ASEC).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Variable AI : AMallocIface.
Hypothesis E : AHEAP AI = AHEAP_P (AFake_arep.AH DI AQ ASEC).
Hypothesis EC : aci AI = CI.
Lemma stack_free_5_AI : stack_free_5_stmt AI fflag.
Proof.
  unfold stack_free_5_stmt. intros until F. intros AHx MI ST LO SPL A0 C2040 RSTK.
  rewrite E in AHx.
  eapply evtF_mono; [eapply (stack_free_5_P DI AQ ASEC HL CI CI_OK); try eassumption; unfold SF5_STACK_P, SF5_STACK in *; lia|].
  cbv beta. intros ms' PO. unfold sf5_postP in PO. unfold sf5_post.
  destruct PO as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & EQ & MI' & ST' & HPR & AH' & HSH).
  exists x0, x1, x2, y0, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m'.
  rewrite E, EC. repeat (split; [assumption|]). exact HSH.
Qed.
End Inst.
End CANSEC1.
