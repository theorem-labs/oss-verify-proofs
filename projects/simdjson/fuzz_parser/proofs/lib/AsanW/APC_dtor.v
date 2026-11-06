(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import ShadowTac APC_kit APC_kit2 APC_kit3 APC_docdtor APC_impldtor.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Section CANSEC1. Context {rc : runConstT}.
Definition ADTOR : Z := 0x95b40.
Definition ADTOR_STACK : Z := 32 + ADOCDTOR_STACK.

(* [comment removed for export] *)
Definition acopy_blk (lb : option AsanCtrl.aptr) (ACP ncp : Z) : list ablock := match lb with Some p => [HB p ACP ncp] | None => [] end.
Definition acopy_addr (lb : option AsanCtrl.aptr) (ACP : Z) : Z := match lb with Some _ => ACP | None => 0 end.
(* [comment removed for export] *)
Definition asix_blks (pia poc psi pim ptp psb : AsanCtrl.aptr) (AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb : Z) : list ablock :=
  [HB pia AIA nia; HB poc AOC noc; HB psi ASI nsi; HB pim AIM nim; HB ptp TPA ntp; HB psb SBA nsb].
Definition afour_blks (pia poc psi pim : AsanCtrl.aptr) (AIA AOC ASI AIM nia noc nsi nim : Z) : list ablock :=
  [HB pia AIA nia; HB poc AOC noc; HB psi ASI nsi; HB pim AIM nim].

(* [comment removed for export] *)
Lemma hb_ids_cons_heap : forall p A n L, hb_ids (HB p A n :: L) = p :: hb_ids L.
Proof. reflexivity. Qed.
Lemma lb_remove_mid : forall L1 p A n L2, List.NoDup (hb_ids (L1 ++ HB p A n :: L2)) ->
  lb_remove p (L1 ++ HB p A n :: L2) = L1 ++ L2 /\ List.NoDup (hb_ids (L1 ++ L2)).
Proof.
  intros L1 p A n L2 ND. rewrite hb_ids_app, hb_ids_cons_heap in ND. apply NoDup_remove in ND as [ND' NI].
  split.
  - rewrite lb_remove_app, lb_remove_cons_hd. rewrite (lb_remove_notin p L1), (lb_remove_notin p L2); [reflexivity| |];
      intros H; apply NI; apply in_or_app; [right| left]; exact H.
  - rewrite hb_ids_app. exact ND'.
Qed.
Lemma acopy_rm : forall pcp ACP ncp L, List.NoDup (hb_ids (HB pcp ACP ncp :: L)) ->
  lb_remove pcp (HB pcp ACP ncp :: L) = L /\ List.NoDup (hb_ids L).
Proof. intros pcp ACP ncp L ND. exact (lb_remove_mid [] pcp ACP ncp L ND). Qed.
Lemma asix_facts : forall pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb LB0,
  List.NoDup (hb_ids (asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0)) ->
  psb <> ptp /\ List.NoDup [pim; psi; poc; pia]
  /\ lb_remove ptp (lb_remove psb (asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0))
     = afour_blks pia poc psi pim AIA AOC ASI AIM nia noc nsi nim ++ LB0
  /\ aimpl_rm pim psi poc pia (afour_blks pia poc psi pim AIA AOC ASI AIM nia noc nsi nim ++ LB0) = LB0.
Proof.
  intros until LB0. intros ND.
  assert (ND0 := ND). cbn [asix_blks app hb_ids flat_map ab_kind] in ND0.
  apply NoDup_cons_iff in ND0 as [N1 ND0]. apply NoDup_cons_iff in ND0 as [N2 ND0]. apply NoDup_cons_iff in ND0 as [N3 ND0].
  apply NoDup_cons_iff in ND0 as [N4 ND0]. apply NoDup_cons_iff in ND0 as [N5 _].
  cbn [In app] in N1, N2, N3, N4, N5.
  split; [intros E; subst; apply N5; left; reflexivity|].
  split.
  { repeat constructor; cbn [In]; intros H; repeat destruct H as [H|H]; subst; try tauto;
      first [apply N1 | apply N2 | apply N3 | apply N4]; cbn [In]; tauto. }
  change (asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0)
    with ([HB pia AIA nia; HB poc AOC noc; HB psi ASI nsi; HB pim AIM nim; HB ptp TPA ntp] ++ HB psb SBA nsb :: LB0) in ND |- *.
  destruct (lb_remove_mid _ _ _ _ _ ND) as [E1 ND1]. rewrite E1.
  change ([HB pia AIA nia; HB poc AOC noc; HB psi ASI nsi; HB pim AIM nim; HB ptp TPA ntp] ++ LB0)
    with ([HB pia AIA nia; HB poc AOC noc; HB psi ASI nsi; HB pim AIM nim] ++ HB ptp TPA ntp :: LB0) in ND1 |- *.
  destruct (lb_remove_mid _ _ _ _ _ ND1) as [E2 ND2]. rewrite E2.
  split; [reflexivity|].
  unfold aimpl_rm, afour_blks. change ([HB pia AIA nia; HB poc AOC noc; HB psi ASI nsi; HB pim AIM nim] ++ LB0)
    with ([] ++ HB pia AIA nia :: (HB poc AOC noc :: HB psi ASI nsi :: HB pim AIM nim :: LB0)) in ND2 |- *.
  destruct (lb_remove_mid _ _ _ _ _ ND2) as [E3 ND3]. rewrite E3. cbn [app] in ND3 |- *.
  change (HB poc AOC noc :: HB psi ASI nsi :: HB pim AIM nim :: LB0) with ([] ++ HB poc AOC noc :: (HB psi ASI nsi :: HB pim AIM nim :: LB0)) in ND3 |- *.
  destruct (lb_remove_mid _ _ _ _ _ ND3) as [E4 ND4]. rewrite E4. cbn [app] in ND4 |- *.
  change (HB psi ASI nsi :: HB pim AIM nim :: LB0) with ([] ++ HB psi ASI nsi :: (HB pim AIM nim :: LB0)) in ND4 |- *.
  destruct (lb_remove_mid _ _ _ _ _ ND4) as [E5 ND5]. rewrite E5. cbn [app] in ND5 |- *.
  change (HB pim AIM nim :: LB0) with ([] ++ HB pim AIM nim :: LB0) in ND5 |- *.
  destruct (lb_remove_mid _ _ _ _ _ ND5) as [E6 _]. rewrite E6. reflexivity.
Qed.

Lemma implMA_retb : forall {A B} RNG (a : A) (f : A -> MA B) (s : APS) Q ms,
  implMA RNG (f a) s Q ms -> implMA RNG (Monad.mbind (Monad.mret a) f) s Q ms.
Proof. intros A B RNG a f s Q ms H. exact H. Qed.

Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Definition apdtor_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB0 : list ablock) (lo P : Z) (m : amem) (r : unit) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres_x CI LB0 (bv_unsigned sp) (P + 8) 64 m m'
    /\ aps_rest s' = aps_rest s
    /\ AHEAP AI L RNG' (aps_m s') LB0 m'.

Definition apdtor_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB0 : list ablock) (lb : option AsanCtrl.aptr)
         (pia poc psi pim ptp psb : AsanCtrl.aptr) (ACP AIA AOC ASI AIM TPA SBA ncp nia noc nsi nim ntp nsb lo P : Z) (tr : list Z),
  AHEAP AI L RNG (aps_m s) (acopy_blk lb ACP ncp ++ asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0) m ->
  72 <= nim ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ADTOR_STACK ->
  bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m (P + 8) [C8 (Z_to_bv 64 AIM)] ->
  rw_cells asegs m (P + 24) [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)] ->
  rw_cells asegs m (P + 64) [C8 (Z_to_bv 64 (acopy_addr lb ACP))] ->
  0 <= P -> P + 80 <= ATOP -> P mod 8 = 0 ->
  (exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB0 /\ FA <= P /\ P + 80 <= FA + FN /\ ablk FA (FA + FN)) ->
  shc m (P + 8) -> shc m (P + 24) -> shc m (P + 32) -> shc m (P + 64) ->
  rng RNG P 80 -> rng RNG (shx P) 10 ->
  rw_cells asegs m AIM [C8 (Z_to_bv 64 AVTAB_DOM)] -> rw_cells asegs m (AIM + 16) [C8 (Z_to_bv 64 ASI)] ->
  rw_cells asegs m (AIM + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)] ->
  client_img m -> client_sh m ->
  uchain m (al_top L) AFREE_PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr -> bv_unsigned sp + 16 <= bv_unsigned s0 ->
  In (AFREE_PC :: bv_unsigned ra :: tr) (al_U L) -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> (length tr <= 28)%nat ->
  HU L ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> aps_ok L s ->
  a0 = Z_to_bv 64 P ->
  implMA RNG (HarnessP.parser_dtor afree_M (psb, ptp, (pim, psi, poc, pia), lb)) s
        (apdtor_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo P m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADTOR) fc None m (seg_rom asegs)).

Lemma HU_in : forall L tr, HU L -> In tr HU_TRACES -> In tr (al_U L).
Proof. intros L tr H Hin. unfold HU in H. rewrite Forall_forall in H. apply H. exact Hin. Qed.
Ltac hu_tr HUL := eapply (HU_in _ _ HUL); unfold HU_TRACES; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Local Ltac keepF HPR H INF2 := eapply aheap_pres_rw_cells; [exact HPR| exact H| eapply aclient_range_fake; [exact INF2| lia| cbn; lia]].
Local Ltac keepFs HPR H INF2 P8 := eapply aheap_pres_rw_cells;
  [exact HPR| exact H| eapply aclient_range_fake_sh; [exact INF2| lia| lia| rewrite Z.add_mod by lia; rewrite P8; reflexivity| lia]].
Local Ltac keepB HPR H INM2 := eapply aheap_pres_rw_cells; [exact HPR| exact H| right; left; eexists; split; [exact INM2| cbn; lia]].

(* [comment removed for export] *)
Local Ltac DJF3 := lazymatch goal with AH3 : AHEAP _ _ _ _ _ _, INM3 : In (HB _ _ _) _, INF3 : In (mkABlock (ABFake _) _ _) _ |- _ =>
  pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH3 INM3 INF3 ltac:(discriminate)) as DJ; cbn [ab_addr ab_size] in DJ; lia end.

Section Proof.
  Hypothesis ODA : opdelete_arr_stmtA AI.
  Hypothesis OD : opdelete_stmtA AI.
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.

  (* [comment removed for export] *)
  Lemma apdtor_tail : forall (L : alayout) (RNG RNG1 : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m m1 : amem) (s s1' : APS) (LB0 : list ablock) (pia poc psi pim ptp psb : AsanCtrl.aptr)
         (AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb lo P : Z) (tr : list Z) (j8 : list byte)
         (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    AHEAP AI L RNG1 (aps_m s1') (asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0) m1 ->
    72 <= nim ->
    mem_inv asegs m1 ->
    stk asegs m1 lo (bv_unsigned sp + -32) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ADTOR_STACK ->
    bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 ATP ->
    rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m1 (P + 8) [C8 (Z_to_bv 64 AIM)] ->
    rw_cells asegs m1 (P + 24) [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)] ->
    0 <= P -> P + 80 <= ATOP -> P mod 8 = 0 ->
    (exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB0 /\ FA <= P /\ P + 80 <= FA + FN /\ ablk FA (FA + FN)) ->
    shc m1 (P + 8) -> shc m1 (P + 24) -> shc m1 (P + 32) ->
    rng RNG1 P 80 -> rng RNG1 (shx P) 10 ->
    rw_cells asegs m1 AIM [C8 (Z_to_bv 64 AVTAB_DOM)] -> rw_cells asegs m1 (AIM + 16) [C8 (Z_to_bv 64 ASI)] ->
    rw_cells asegs m1 (AIM + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)] ->
    rw_cells asegs m1 AVTAB_DOM vtab_dom_cells -> rw_cells asegs m1 2147583987 [C1 (Z_to_bv 8 0)] ->
    uchain m1 (al_top L) AFREE_PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr -> bv_unsigned sp + 16 <= bv_unsigned s0 ->
    In (AFREE_PC :: bv_unsigned ra :: tr) (al_U L) -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> (length tr <= 28)%nat ->
    HU L ->
    rng RNG1 lo (al_top L - lo) -> rng_aimg RNG1 -> rng_aimg_sh RNG1 -> aps_ok L s1' ->
    fp_le RNG RNG1 -> aps_rest s1' = aps_rest s -> aheap_pres_x CI LB0 (bv_unsigned sp) (P + 8) 64 m m1 ->
    implMA RNG1 (HarnessP.doc_dtor afree_M psb ptp ;;; HarnessP.impl_dtor afree_M (pim, psi, poc, pia)) s1'
          (apdtor_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo P m)
          (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x95b88) fc None m1 (seg_rom asegs)).
  Proof.
    intros until t6.
    intros AH NIM MI ST LOA LOS STOP SP16 TP FR PIM PDOC P0 PTOP P8 FK SC8 SC24 SC32 RP RSP80 IM0 IM16 IM56 VTD VSH9
      UC S0SP TRU RA4 RAF TRL HUL RSTK RI RISH AOK FPL0 ARS0 PRE.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ADTOR_STACK, ADOCDTOR_STACK, AFREE_STACK in LOS. atop_facts.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT & RIC & REAL & SHB & SUA & INI & LAY).
    pose proof (AI_hb_ids AI _ _ _ _ _ AH) as ND.
    destruct (asix_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ND) as (NEsbtp & ND4 & E2 & E4). clear ND.
    boxm NEsbtp. boxm RAF.
    destruct FK as (fcls & FA & FN & INF & FK1 & FK2 & FKB).
    pose proof (ablk_lin _ _ FKB) as (FKB1 & FKB2 & FKB3 & FKB4). unfold AIMG_HI in FKB1. band_ind FKB bF.
    assert (T9622c : In [AFREE_PC; 0x96580] (al_U L)) by hu_tr HUL.
    assert (T9583c : In [AFREE_PC; 0x95b90] (al_U L)) by hu_tr HUL.
    assert (Tc043c : In [AFREE_PC; 0xc0790] (al_U L)) by hu_tr HUL.
    assert (Tc0464 : In [AFREE_PC; 0xc07b8] (al_U L)) by hu_tr HUL.
    assert (Tc04a8 : In [AFREE_PC; 0xc07fc] (al_U L)) by hu_tr HUL.
    clear HUL.
    assert (INF0 : In (mkABlock (ABFake fcls) FA FN) (asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0))
      by (apply in_or_app; right; exact INF).
    assert (SUB0 : forall b, In b LB0 -> In b (asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0))
      by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (RD : rng RNG1 (P + 24) 16) by (eapply rng_sub'; [exact RP| lia]).
    assert (SHP : forall k, 0 <= k -> shx (P + 8 * k) = shx P + k)
      by (intros k Hk; unfold shx; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
    assert (RS24 : rng RNG1 (shx (P + 24)) 1) by (replace (P + 24) with (P + 8 * 3) by lia; rewrite (SHP 3) by lia; eapply rng_sub'; [exact RSP80| lia]).
    assert (RS32 : rng RNG1 (shx (P + 24 + 8)) 1) by (replace (P + 24 + 8) with (P + 8 * 4) by lia; rewrite (SHP 4) by lia; eapply rng_sub'; [exact RSP80| lia]).
    assert (RS8 : rng RNG1 (shx (P + 8)) 1) by (replace (P + 8) with (P + 8 * 1) by lia; rewrite (SHP 1) by lia; eapply rng_sub'; [exact RSP80| lia]).
    clear SHP.
    (* [comment removed for export] *)
    apply implMA_from_evtF.
    steps_to 0x96538.
    apply evtF_done.
    eapply implMA_bind.
    { eapply (adocdtor_proof AI ODA) with (lo := lo) (DOC := P + 24) (SBA := SBA) (TPA := TPA) (nsb := nsb) (ntp := ntp);
        try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH | (unfold asix_blks; cbn; tauto) | (unbox NEsbtp; exact NEsbtp) | exact MI | exact ST | exact TP | exact GOT | exact SHB | exact PDOC
              | (exists fcls, FA, FN; split; [exact INF0| split; [lia| split; [lia| exact FKB]]])
              | exact SC24 | (replace (P + 24 + 8) with (P + 32) by lia; exact SC32)
              | exact RD | exact RS24 | exact RS32 | exact T9622c | exact T9583c | exact RSTK | exact RI | exact AOK
              | (unfold ADOCDTOR_STACK, AFREE_STACK; lia) | (unfold AFREE_PC; lia) | lia]. }
    cbv beta. intros [] s2' RNG2 ms2 (FPL2 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & -> & MI3 & ST3 & HPX & ARS2 & AH3).
    rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPX by lia.
    retlit.
    rewrite E2 in HPX, AH3.
    assert (INM3 : In (HB pim AIM nim) (afour_blks pia poc psi pim AIA AOC ASI AIM nia noc nsi nim ++ LB0)) by (unfold afour_blks; cbn; tauto).
    assert (INF3 : In (mkABlock (ABFake fcls) FA FN) (afour_blks pia poc psi pim AIA AOC ASI AIM nia noc nsi nim ++ LB0))
      by (apply in_or_app; right; exact INF).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH3 INM3) as (_ & (BM1 & BM2 & BM3 & BM4) & RIM & _).
    pose proof (ablk_lin _ _ BM1) as (BM1a & BM1b & BM1c & BM1d). unfold AIMG_HI in BM1a. band_ind BM1 bM.
    assert (AM8 : AIM mod 8 = 0) by (Z.div_mod_to_equations; lia).
    pose proof (blk_shx_bounds AIM ltac:(lia) ltac:(lia)) as SB0.
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -32) cs)
        by (eapply aheap_pres_x_rw_cells; [exact HPX| exact FR| apply aclient_range_stack; cbn; lia| cbn; lia]) end.
    assert (PIM3 : rw_cells asegs m3 (P + 8) [C8 (Z_to_bv 64 AIM)])
      by (eapply aheap_pres_x_rw_cells; [exact HPX| exact PIM| eapply aclient_range_fake; [exact INF3| lia| cbn; lia]| cbn; lia]).
    unfold shc, shx, ASHOFF in SC8.
    assert (SC83 : rw_cells asegs m3 (Z.shiftr (P + 8) 3 + 2147450880) [C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_x_rw_cells; [exact HPX| exact SC8| eapply aclient_range_fake_sh; [exact INF3| lia| lia| rewrite Z.add_mod by lia; rewrite P8; reflexivity| lia]
                                        | cbn; pose proof (blk_shx_bounds (P + 8) ltac:(lia) ltac:(lia)); lia]).
    lazymatch type of IM0 with rw_cells _ _ _ ?cs =>
      assert (IM03 : rw_cells asegs m3 AIM cs)
        by (eapply aheap_pres_x_rw_cells; [exact HPX| exact IM0| right; left; exists (HB pim AIM nim); split; [exact INM3| cbn; lia]| cbn; DJF3]) end.
    lazymatch type of IM16 with rw_cells _ _ _ ?cs =>
      assert (IM163 : rw_cells asegs m3 (AIM + 16) cs)
        by (eapply aheap_pres_x_rw_cells; [exact HPX| exact IM16| right; left; exists (HB pim AIM nim); split; [exact INM3| cbn; lia]| cbn; DJF3]) end.
    lazymatch type of IM56 with rw_cells _ _ _ ?cs =>
      assert (IM563 : rw_cells asegs m3 (AIM + 56) cs)
        by (eapply aheap_pres_x_rw_cells; [exact HPX| exact IM56| right; left; exists (HB pim AIM nim); split; [exact INM3| cbn; lia]| cbn; DJF3]) end.
    unfold AVTAB_DOM, vtab_dom_cells in VTD. unfold AVTAB_DOM in IM03.
    lazymatch type of VTD with rw_cells _ _ _ ?cs =>
      assert (VTD3 : rw_cells asegs m3 0x103f50 cs)
        by (eapply aheap_pres_x_rw_cells; [exact HPX| exact VTD| left; right; left; exists (0x103f50, 0x103fa0); split; [apply IMG_CI; cbn; tauto| cbn; lia]| cbn; lia]) end.
    assert (VSH93 : rw_cells asegs m3 2147583987 [C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_x_rw_cells; [exact HPX| exact VSH9| right; right; right; left; exists (0x103f50, 0x103fa0); split; [apply IMG_CI; cbn; tauto| cbn; unfold ASHOFF; lia]| cbn; lia]).
    clear FR PIM SC8 SC24 SC32 IM0 IM16 IM56 VTD VSH9 PDOC GOT RIC REAL SHB SUA INI LAY.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH3) as (GOT3 & RIC3 & REAL3 & SHB3 & SUA3 & INI3 & LAY3).
    destruct (blk_shc8 AI _ _ _ _ _ _ _ _ AIM AH3 INM3 ltac:(lia) ltac:(lia) AM8) as (SM0 & RM0).
    pose proof (rng_fp_le _ _ _ _ FPL2 RSTK) as RSTK2. pose proof (rng_fp_le _ _ _ _ FPL2 RI) as RI2. pose proof (rng_fp_le _ _ _ _ FPL2 RISH) as RISH2.
    pose proof (rng_fp_le _ _ _ _ FPL2 RP) as RP2. pose proof (rng_fp_le _ _ _ _ FPL2 RS8) as RS82. unfold shx, ASHOFF in RS82.
    clear RSTK RI RISH RP RS8 RS24 RS32 RD RSP80.
    (* [comment removed for export] *)
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH3 INM3 INF3 ltac:(discriminate)) as DJF. cbn [ab_addr ab_size] in DJF.
    pose proof (blk_shx_bounds (P + 8) ltac:(lia) ltac:(lia)) as SB8.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (P + 8, P + 72)] m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
    steps_to 0x95bac. zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia| clear K1].
    steps_to 0xc0748.
    release_frame FR3 ST3 (bv_unsigned sp).
    apply evtF_done. clear DJF.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH4 : AHEAP AI L RNG2 (aps_m s2') (afour_blks pia poc psi pim AIA AOC ASI AIM nia noc nsi nim ++ LB0) mx)
        by (eapply (AI_frame AI); [exact AH3| exact MU3| exact WM3|];
            apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF3| cbn; lia]| apply Forall_nil])
    end.
    (* [comment removed for export] *)
    assert (SUB3 : forall b, In b LB0 -> In b (afour_blks pia poc psi pim AIA AOC ASI AIM nia noc nsi nim ++ LB0))
      by (intros b Hb; apply in_or_app; right; exact Hb).
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (P14 : aheap_pres_x CI LB0 (bv_unsigned sp) (P + 8) 64 m1 mx)
    end.
    { eapply aheap_pres_x_trans.
      { eapply aheap_pres_x_weaken; [exact HPX| lia| exact SUB3| intros a _ Hy Hx; apply Hy; lia]. }
      eapply aheap_pres_x_of_munch; [exact MU3| exact WM3|]. intros a Ha Hc Hx.
      destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH SUB0 Hc) as [Y|Y]; cbn; lia. }
    pose proof (uchain_of_pres_x CI _ _ _ _ _ _ _ _ _ _ _ P14 ltac:(lia) LY3 ltac:(lia) UC S0SP) as UC4.
    pose proof (aimpldtor_proof AI ODA OD) as IMPD. unfold aimpldtor_stmt in IMPD.
    eapply implMA_mono.
    { eapply IMPD with (lo := lo) (AIM := AIM) (ASI := ASI) (AOC := AOC) (AIA := AIA) (nim := nim) (nsi := nsi) (noc := noc) (nia := nia)
        (tr := tr);
        try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH4 | (unfold afour_blks; cbn; tauto) | exact ND4 | exact NIM | eassumption | exact TP | exact UC4 | exact S0SP
              | exact TRU | exact RA4 | (unbox RAF; exact RAF) | exact TRL | exact Tc043c | exact Tc0464 | exact Tc04a8 | exact RSTK2 | exact RI2
              | (eapply aps_ok_rest; [exact ARS2| exact AOK])
              | (unfold AIMPLDTOR_STACK, AFREE_STACK; lia) | lia]. }
    cbv beta. intros [] s4' RNG4 ms4 (FPL4 & x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m5 & -> & MI5 & ST5 & HPR5 & ARS4 & AH5).
    rewrite E4 in HPR5, AH5.
    unfold apdtor_post. split; [eapply fp_le_trans; [exact FPL0| eapply fp_le_trans; [exact FPL2| exact FPL4]]|].
    do 15 eexists. exists m5. split; [reflexivity|].
    split; [exact MI5|]. split; [exact ST5|].
    split.
    { eapply aheap_pres_x_trans; [exact PRE|]. eapply aheap_pres_x_trans; [exact P14|].
      eapply aheap_pres_x_of_pres; [exact HPR5| lia| intros b Hb; exact Hb]. }
    split; [rewrite ARS4, ARS2, ARS0; reflexivity| exact AH5].
  Qed.

  Theorem apdtor_proof : apdtor_stmt.
  Proof.
    unfold apdtor_stmt. intros until tr.
    intros AH NIM MI ST LOA LOS STOP SP16 TP PIM PDOC PCP P0 PTOP P8 FK SC8 SC24 SC32 SC64 RP RSP80 IM0 IM16 IM56 CI0 CSH
      UC S0SP TRU RA4 RAF TRL HUL RSTK RI RISH AOK A0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ADTOR_STACK, ADOCDTOR_STACK, AFREE_STACK in LOS. atop_facts.
    pose proof ODA as ODA'. unfold opdelete_arr_stmtA, opdelete_stmtA_at in ODA'.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT & RIC & REAL & SHB & SUA & INI & LAY).
    pose proof (AI_hb_ids AI _ _ _ _ _ AH) as ND.
    boxm RAF.
    assert (FK' := FK). destruct FK' as (fcls & FA & FN & INF & FK1 & FK2 & FKB).
    pose proof (ablk_lin _ _ FKB) as (FKB1 & FKB2 & FKB3 & FKB4). unfold AIMG_HI in FKB1. band_ind FKB bF.
    assert (T95834 : In [AFREE_PC; 0x95b88] (al_U L)) by hu_tr HUL.
    destruct CI0 as (CGOT & VTI & VTD & _). clear CGOT VTI. unfold AVTAB_DOM, vtab_dom_cells in VTD. unfold AVTAB_DOM in IM0.
    pose proof (client_sh_cell m 0x103f98 CSH ltac:(cbn; tauto)) as VSH9.
    change (Z.shiftr 0x103f98 3 + 2147450880) with 2147583987 in VSH9. clear CSH.
    assert (INF0 : In (mkABlock (ABFake fcls) FA FN)
                     (acopy_blk lb ACP ncp ++ asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0))
      by (apply in_or_app; right; apply in_or_app; right; exact INF).
    assert (SUB0 : forall b, In b LB0 -> In b (acopy_blk lb ACP ncp ++ asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0))
      by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
    assert (SHP : shx (P + 64) = shx P + 8)
      by (unfold shx; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
    assert (RS64 : rng RNG (Z.shiftr (P + 64) 3 + 2147450880) 1)
      by (change (Z.shiftr (P + 64) 3 + 2147450880) with (shx (P + 64)); rewrite SHP; eapply rng_sub'; [exact RSP80| lia]).
    clear SHP.
    unfold shc, shx, ASHOFF in SC64, SC8, SC24, SC32.
    pose proof (blk_shx_bounds (P + 64) ltac:(lia) ltac:(lia)) as SB64. pose proof (blk_shx_bounds (P + 8) ltac:(lia) ltac:(lia)) as SB8.
    pose proof (blk_shx_bounds (P + 24) ltac:(lia) ltac:(lia)) as SB24. pose proof (blk_shx_bounds (P + 32) ltac:(lia) ltac:(lia)) as SB32.
    (* [comment removed for export] *)
    assert (OUTW : forall a, 0 <= a < 2^64 -> aclient_addr CI LB0 (bv_unsigned sp) a -> ~ (P + 8 <= a < P + 8 + 64) ->
              outside [(lo, bv_unsigned sp); (P + 8, P + 72)] a).
    { intros a Ha Hc Hx. destruct (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH SUB0 Hc) as [Y|Y]; cbn; lia. }
    assert (INM0 : In (HB pim AIM nim) (acopy_blk lb ACP ncp ++ asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0))
      by (apply in_or_app; right; cbn; tauto).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH INM0 INF0 ltac:(discriminate)) as DJF. cbn [ab_addr ab_size] in DJF.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH INM0) as (_ & (BM1 & BM2 & BM3 & BM4) & _).
    pose proof (ablk_lin _ _ BM1) as (BM1a & BM1b & BM1c & BM1d). unfold AIMG_HI in BM1a.
    unfold HarnessP.parser_dtor.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (P + 8, P + 72)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    subst a0. unfold ADTOR.
    steps_to 0x95b7c. clear DJF.
    destruct lb as [pcp|]; cbn [acopy_blk acopy_addr app HarnessP.odelete] in *.
    - (* [comment removed for export] *)
      assert (INC : In (HB pcp ACP ncp) (HB pcp ACP ncp :: asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0))
        by (left; reflexivity).
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH INC) as (_ & (BC1 & BC2 & BC3 & BC4) & _).
      pose proof (ablk_lin _ _ BC1) as (BC1a & BC1b & BC1c & BC1d). unfold AIMG_HI in BC1a.
      zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia| clear K0].
      steps_to 0xe2e9c.
      apply evtF_done.
      lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (AH1 : AHEAP AI L RNG (aps_m s) (HB pcp ACP ncp :: asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0) mx)
          by (eapply (AI_frame AI); [exact AH| exact MU| exact WM|];
              apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF0| cbn; lia]| apply Forall_nil])
      end.
      eapply implMA_bind.
      { eapply ODA' with (lo := lo) (A := ACP) (n := ncp) (tr := []); try reflexivity; rewrite ?unsigned_lit by lia;
          first [exact AH1 | exact INC | eassumption | exact TP | exact T95834 | exact RSTK | exact AOK
                | apply uchain_data; lia | (cbn; lia) | (unfold AFREE_STACK; lia) | (unfold AFREE_PC; lia) | lia]. }
      cbv beta. intros [] s1' RNG1 ms1 (ARS1 & FPL1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & HPR1 & AH2).
      destruct (acopy_rm _ _ _ _ ND) as [E0 _]. rewrite E0 in HPR1, AH2.
      rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR1 by lia.
      retlit.
      assert (PRE : aheap_pres_x CI LB0 (bv_unsigned sp) (P + 8) 64 m m2).
      { eapply aheap_pres_x_trans; [eapply aheap_pres_x_of_munch; [exact MU| exact WM| exact OUTW]|].
        eapply aheap_pres_x_of_pres; [exact HPR1| lia| intros b Hb; apply in_or_app; right; exact Hb]. }
      assert (INF2 : In (mkABlock (ABFake fcls) FA FN) (asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0))
        by (apply in_or_app; right; exact INF).
      assert (INM2 : In (HB pim AIM nim) (asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0)) by (cbn; tauto).
      lazymatch goal with FR : rw_cells asegs _ (bv_unsigned sp + -32) ?cs |- _ =>
        assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) cs) by (eapply aheap_pres_rw_cells; [exact HPR1| exact FR| apply aclient_range_stack; cbn; lia]); clear FR end.
      assert (PIM2 : rw_cells asegs m2 (P + 8) [C8 (Z_to_bv 64 AIM)]) by keepF HPR1 PIM INF2.
      assert (PDOC2 : rw_cells asegs m2 (P + 24) [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)]) by keepF HPR1 PDOC INF2.
      assert (SC82 : rw_cells asegs m2 (Z.shiftr (P + 8) 3 + 2147450880) [C1 (Z_to_bv 8 0)]) by keepFs HPR1 SC8 INF2 P8.
      assert (SC242 : rw_cells asegs m2 (Z.shiftr (P + 24) 3 + 2147450880) [C1 (Z_to_bv 8 0)]) by keepFs HPR1 SC24 INF2 P8.
      assert (SC322 : rw_cells asegs m2 (Z.shiftr (P + 32) 3 + 2147450880) [C1 (Z_to_bv 8 0)]) by keepFs HPR1 SC32 INF2 P8.
      assert (IM02 : rw_cells asegs m2 AIM [C8 (Z_to_bv 64 AVTAB_DOM)]) by keepB HPR1 IM0 INM2.
      assert (IM162 : rw_cells asegs m2 (AIM + 16) [C8 (Z_to_bv 64 ASI)]) by keepB HPR1 IM16 INM2.
      assert (IM562 : rw_cells asegs m2 (AIM + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)]) by keepB HPR1 IM56 INM2.
      lazymatch type of VTD with rw_cells _ _ _ ?cs =>
        assert (VTD2 : rw_cells asegs m2 0x103f50 cs)
          by (eapply aheap_pres_rw_cells; [exact HPR1| exact VTD| left; right; left; exists (0x103f50, 0x103fa0); split; [apply IMG_CI; cbn; tauto| cbn; lia]]) end.
      assert (VSH92 : rw_cells asegs m2 2147583987 [C1 (Z_to_bv 8 0)])
        by (eapply aheap_pres_rw_cells; [exact HPR1| exact VSH9| right; right; right; left; exists (0x103f50, 0x103fa0); split; [apply IMG_CI; cbn; tauto| cbn; unfold ASHOFF; lia]]).
      pose proof (uchain_of_pres_x CI _ _ _ _ _ _ _ _ _ _ _ PRE ltac:(lia) LY3 ltac:(lia) UC S0SP) as UC2.
      eapply (apdtor_tail L RNG RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m2 s s1' LB0 pia poc psi pim ptp psb
                AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb lo P tr);
        first [eassumption | reflexivity | (unbox RAF; exact RAF) | (eapply rng_fp_le; [exact FPL1| eassumption])
              | (eapply aps_ok_rest; [exact ARS1| exact AOK])
              | (exists fcls, FA, FN; split; [exact INF| split; [lia| split; [lia| exact FKB]]])
              | (unfold ADTOR_STACK, ADOCDTOR_STACK, AFREE_STACK; lia) | lia].
    - (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0; [clear K0| exfalso; rewrite ?unsigned_lit in K0 by lia; apply K0; reflexivity].
      apply evtF_done. apply implMA_retb.
      lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (AH1 : AHEAP AI L RNG (aps_m s) (asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb ++ LB0) mx)
          by (eapply (AI_frame AI); [exact AH| exact MU| exact WM|];
              apply Forall_cons; [left; left; cbn; lia|]; apply Forall_cons; [right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF0| cbn; lia]| apply Forall_nil]);
        assert (PRE : aheap_pres_x CI LB0 (bv_unsigned sp) (P + 8) 64 m mx) by (eapply aheap_pres_x_of_munch; [exact MU| exact WM| exact OUTW])
      end.
      pose proof (uchain_of_pres_x CI _ _ _ _ _ _ _ _ _ _ _ PRE ltac:(lia) LY3 ltac:(lia) UC S0SP) as UC2.
      eapply (apdtor_tail L RNG RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m _ s s LB0 pia poc psi pim ptp psb
                AIA AOC ASI AIM TPA SBA nia noc nsi nim ntp nsb lo P tr);
        first [eassumption | reflexivity | (unbox RAF; exact RAF) | exact (fp_le_refl RNG)
              | (exists fcls, FA, FN; split; [exact INF| split; [lia| split; [lia| exact FKB]]])
              | (unfold ADTOR_STACK, ADOCDTOR_STACK, AFREE_STACK; lia) | lia].
  Qed.
End Proof.
End S.
End CANSEC1.
