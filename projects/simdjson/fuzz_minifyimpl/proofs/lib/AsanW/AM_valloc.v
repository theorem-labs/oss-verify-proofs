(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase ARep AMalloc_iface F_apoison F_annot F_annot_sg F_annot_grow APoisonR_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac AU_h_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import ShadowTac AM_kitA AM_kitB AM_annotw.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_prune_relevant; OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.
Definition bxv (P : Prop) : Prop := P.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxv P) in H end.
(* [comment removed for export] *)
Local Ltac pose_hr i SHVi :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VSHx : rw_cells asegs mm (shad ?V) [C1 _; C1 _; C1 _] |- _ =>
      let H := fresh "HR" in pose proof (sh3_read mm (shad V) i ltac:(lia) VSHx) as H;
      unfold bxv in SHVi; rewrite <- SHVi in H; box SHVi end end.
Local Ltac pose_hr0 SHV :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VSHx : rw_cells asegs mm (shad ?V) [C1 _; C1 _; C1 _] |- _ =>
      let H := fresh "HR" in pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSHx) as H; rewrite Z.add_0_r in H;
      unfold bxv in SHV; rewrite SHV in H; box SHV end end.

Section CANSEC1. Context {rc : runConstT}.
Definition AVALLOC : Z := 0xb2560.
Definition AVALLOC_RET : Z := 0xb2594.                    (* [comment removed for export] *)
Definition AVALLOC_STACK : Z := 32 + OPNEW_STACK_A.       (* [comment removed for export] *)

Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Definition avalloc_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (V n lo : Z) (m : amem) (p : AsanCtrl.aptr) (s' : APS) (RNG' : footprint)
    : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (mq1 m' : amem) (A : Z) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aps_rest s' = aps_rest s
    /\ ablock_range A n
    (* [comment removed for export] *)
    /\ aheap_pres CI LB (bv_unsigned sp) m mq1
    /\ AHEAP AI L RNG' (aps_m s') (HB p A n :: LB) mq1
    /\ mem_inv asegs mq1
    (* [comment removed for export] *)
    /\ munch [(lo, bv_unsigned sp); (V, V + 24); (shad A, shad A + granules n)] mq1 m'
    /\ wmono asegs mq1 m'
    /\ rw_cells asegs m' V [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + n))]
    /\ rw_cells asegs m' (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
    /\ rw_cells asegs m' (shad A) [CB (Z.to_nat (granules n)) (repeat (Z_to_bv 8 252) (Z.to_nat (granules n)))]
    /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7)).

Definition avalloc_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (lo V n : Z) (v0 v1 v2 : word) (cls FA FN : Z),
  AHEAP AI L RNG (aps_m s) LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AVALLOC_STACK ->
  bv_unsigned sp < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  In (mkABlock (ABFake cls) FA FN) LB -> FA <= V -> V + 24 <= FA + FN -> V mod 8 = 0 -> ablk V (V + 24) ->
  rw_cells asegs m V [C8 v0; C8 v1; C8 v2] ->
  rw_cells asegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  In [AMALLOC_PC; AOPNEW_RET] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  aps_ok L s ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 n -> 0 < n < 2^26 ->
  implMA RNG (HarnessM.opnew amalloc_M (new_handlerA AAllocAsan) n) s
        (avalloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB V n lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AVALLOC) fc None m (seg_rom asegs)).

Section Proof.
  Hypothesis ONTA : opnew_stmtA AI.

  Theorem avalloc_proof : avalloc_stmt.
  Proof.
    unfold avalloc_stmt. intros until FN. intros AH MI ST LOA LOS STOP SP16 TP FIN FV1 FV2 V8 VBLK VEC VSH HU RSTK RI RV RVS AOK -> -> NR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AVALLOC_STACK, OPNEW_STACK_A, AMALLOC_STACK in LOS. atop_facts.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH FIN) as FB. cbn [ab_addr ab_size] in FB.
    pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO, FB.
    assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
    assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
    assert (SHV16 : Z.shiftr (V + 16) 3 + 2147450880 = shad V + 2) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
    assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI H; Z.div_mod_to_equations; lia).
    box SHV; box SHV8; box SHV16.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT & _ & _ & SHB & _).
    unfold HarnessM.opnew in |- *.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    unfold AVALLOC.
    zstep. zstep. zstep. zstep. zstep.      (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K NR; lia| clear K]).   (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx) by (eapply AHEAP_stack_frame; [exact AH| exact MU| exact WM| repeat constructor; cbn; lia]) end.
    name_sp sp (-32)%Z.
    eapply implMA_post_evtF.
    { eapply ONTA with (lo := lo); try reflexivity; rewrite ?Hsp; rewrite ?unsigned_lit by lia;
        first [exact AH1 | exact TP | exact RSTK | exact HU | exact AOK | eassumption
              | (unfold OPNEW_STACK_A, AMALLOC_STACK; lia) | (unfold AREQMAX; lia) | (clear - SP16 RSP LOS LOA H; Z.div_mod_to_equations; lia) | lia]. }
    cbv beta. intros p s' RNG' ms1 PO.
    destruct PO as (FLE & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mq1 & A & bjk & -> & MI1 & ST1 & HPR1 & ARS1 & BR & AH2 & BLK & RA & RSA).
    rewrite ?Hsp in ST1, HPR1. rewrite ?unsigned_lit in ST1, HPR1 by lia.
    unname_sp. retlit.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      assert (FR1 : rw_cells asegs mq1 (bv_unsigned sp + -32) cs) by (eapply aheap_pres_rw_cells; [exact HPR1| exact FR| apply aclient_range_stack; cbn; lia]) end.
    assert (VEC1 : rw_cells asegs mq1 V [C8 v0; C8 v1; C8 v2])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact VEC| eapply aclient_range_fake; [exact FIN| lia| cbn; lia]]).
    assert (VSH1 : rw_cells asegs mq1 (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
    { eapply aheap_pres_rw_cells; [exact HPR1| exact VSH|]. right; right. right; right. exists cls, FA, FN. split; [exact FIN|].
      rewrite shad_div. unfold ASHOFF. cbn [cells_size csize Nat.add]. clear - V8 FV1 FV2. Z.div_mod_to_equations. lia. }
    clear FR VEC VSH AH1 GOT SHB MI. box MU. box WM. pose proof MI1 as MIq. box MIq.
    pose proof (rng_fp_le _ _ _ _ FLE RSTK) as RSTK1. pose proof (rng_fp_le _ _ _ _ FLE RV) as RV1. pose proof (rng_fp_le _ _ _ _ FLE RVS) as RVS1.
    pose proof (rng_fp_le _ _ _ _ FLE RI) as RI1.
    pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
    (* [comment removed for export] *)
    pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH2 FIN) as DJ1. cbn [ab_addr ab_size] in DJ1.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH2) as (GOT1 & _ & _ & SHB1 & _).
    assert (ACC0 : rng RNG' (Z.shiftr V 3 + 2147450880) 1) by (unfold bxv in SHV; rewrite <- SHV; eapply rng_sub'; [exact RVS1| lia]).
    assert (ACC1 : rng RNG' (Z.shiftr (V + 8) 3 + 2147450880) 1) by (unfold bxv in SHV8; rewrite SHV8; eapply rng_sub'; [exact RVS1| lia]).
    assert (ACC2 : rng RNG' (Z.shiftr (V + 16) 3 + 2147450880) 1) by (unfold bxv in SHV16; rewrite SHV16; eapply rng_sub'; [exact RVS1| lia]).
    pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] mq1) as MU1. pose proof (wmono_refl asegs mq1) as WM1.
    (* [comment removed for export] *)
    pose_hr0 SHV.
    zstep. zstep. astep. astep.      (* [comment removed for export] *)
    zstep.                           (* [comment removed for export] *)
    pose_hr 1 SHV8.
    zstep. zstep. zstep. astep. astep.   (* [comment removed for export] *)
    zstep.                           (* [comment removed for export] *)
    pose_hr 2 SHV16.
    zstep. zstep. zstep. astep. astep.   (* [comment removed for export] *)
    zstep. zstep.                    (* [comment removed for export] *)
    zstep. zstep.                    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
    lazymatch goal with H : stk asegs _ lo _ |- _ => release_frame FR1 H (bv_unsigned sp) end.
    zstep.                           (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_introl eq_refl)) as (NRA & _ & _ & _ & BSH & WRA & CH & ARENA).
    pose proof (cells_of_ablock_shadow mq1 A n ltac:(lia) ltac:(lia) ltac:(lia) BSH) as FULL1.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FULL2 : rw_cells asegs mm (shad A) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)])
        by (eapply rw_cells_transport; [exact FULL1| exact MU1| exact WM1|];
            cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (pose proof (granules_mono 0 n ltac:(lia)); rewrite granules_0 in *; lia);
            rewrite shad_div, granules_div by lia; unfold ASHOFF; clear - VNS BL1 BL3 LOA H NR; Z.div_mod_to_equations; lia) end.
    pose proof (poison_cells_of_aheap AI _ _ _ _ _ AH2) as PC1. pose proof (annot_cells_of_aheap AI _ _ _ _ _ AH2 (hrt_cells_of_aheap AI _ _ _ _ _ AH2)) as AC1.
    assert (HWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(lo, bv_unsigned sp); (V, V + 24)])
      by (repeat constructor; cbn; unfold AIMG_HI; clear - LOA VLO H; lia).
    pose proof (poison_cells_frame _ _ _ PC1 MU1 WM1 HWI) as PC2. pose proof (annot_cells_frame _ _ _ AC1 MU1 WM1 HWI) as AC2.
    eapply evtF_mono.
    { lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with VECx : rw_cells asegs mm V [C8 _; C8 _; C8 _], STx : stk asegs mm lo _, MIx : mem_inv asegs mm |- _ =>
        eapply (annotw_new_shrink _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V A n A lo (block_shadow_bytes n));
        first [ exact MIx | exact STx | exact VECx | exact VSH1 | exact FULL2 | exact PC2 | exact AC2 | exact GOT1 | exact SHB1 | exact RI1 | exact V8 | exact VBLK | reflexivity
              | (apply bsb_hsb; lia)
              | (clear - BR4; Z.div_mod_to_equations; lia)
              | (apply ablk_rup8; [exact BR1| clear - BR4; Z.div_mod_to_equations; lia| lia])
              | (pose proof (ablk_lin _ _ (ablk_rup8 _ _ BR1 ltac:(clear - BR4; Z.div_mod_to_equations; lia) ltac:(lia))) as (_ & _ & _ & U4); clear - U4; lia)
              | (unfold rup8, rdn8; clear - DJ1 FV1 FV2 NR V8 BR4; Z.div_mod_to_equations; lia)
              | (rewrite granules_rup8 by lia; exact FULL2)
              | (eapply rng_sub'; [exact RSTK1| lia])
              | (rewrite granules_rup8 by lia; eapply rng_sub'; [exact RSA| unfold granules; lia])
              | exact RV1 | exact RVS1
              | (unfold ANNOTW_STACK; lia) | lia ]
        end end. }
    (* [comment removed for export] *)
    cbv beta. intros ms2 PO2. unfold annotw_sg_post in PO2.
    destruct PO2 as (w0 & w1 & w2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & mq2 & -> & MU2 & WM2 & MI2 & ST2 & OUT2).
    unfold avalloc_post. split; [exact FLE|].
    rewrite sg_out_tight_all in OUT2 by lia. rewrite granules_rup8 in OUT2 by lia.
    assert (MU12 : munch [(lo, bv_unsigned sp); (V, V + 24); (shad A, shad A + granules n)] mq1 mq2)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros x (X1 & X2 & X3 & _); clear - X1 X2 X3; lia|];
          eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; unfold ANNOTW_STACK; rewrite granules_rup8 by lia;
          intros x (X1 & X2 & X3 & _); clear - X1 X2 X3 LOS; Z.div_mod_to_equations; lia).
    assert (DJW : forall B k, (B + k <= bv_unsigned sp - 2736 \/ bv_unsigned sp <= B) -> (B + k <= shad A \/ shad A + granules n <= B) ->
              disjoint_from [(bv_unsigned sp - ANNOTW_STACK, bv_unsigned sp); (shad A + 0 / 8, shad A + shlen (rup8 n))] B k)
      by (intros B k D1 D2; cbn [disjoint_from]; unfold ANNOTW_STACK; rewrite granules_rup8 by lia; change (0 / 8) with 0; clear - D1 D2; lia).
    do 15 eexists. exists mq1, mq2, A, bjk. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact ARS1|]. split; [exact BR|].
    split.
    { unfold bxv in MU, WM. eapply aheap_pres_trans; [| eapply aheap_pres_weaken; [exact HPR1| lia| intros b Hb; exact Hb]].
      eapply aheap_pres_of_munch; [exact MU| exact WM|]. intros a Hc. cbn [outside].
      pose proof (aclient_lo_or_sp AI _ _ _ _ LB _ _ a AH2 ltac:(intros b Hb; right; exact Hb) Hc). clear - H0 LOA. lia. }
    split; [exact AH2|]. split; [unfold bxv in MIq; exact MIq|]. split; [exact MU12|]. split; [eapply wmono_trans; [exact WM1| exact WM2]|].
    split.
    { lazymatch type of MU2 with munch _ ?mm _ => lazymatch goal with VECx : rw_cells asegs mm V _ |- _ =>
        eapply rw_cells_transport; [exact VECx| exact MU2| exact WM2| apply DJW; cbn [cells_size csize Nat.add];
          [clear - VLO VHI LOS LOA H; lia| rewrite shad_div, granules_div by lia; unfold ASHOFF; clear - VNS BL1 BL3 H NR; Z.div_mod_to_equations; lia]] end end. }
    split.
    { lazymatch type of MU2 with munch _ ?mm _ => lazymatch goal with VSHx : rw_cells asegs mm (shad V) _ |- _ =>
        eapply rw_cells_transport; [exact VSHx| exact MU2| exact WM2| apply DJW; cbn [cells_size csize Nat.add];
          [rewrite shad_div; unfold ASHOFF; clear - VLO VHI LOS LOA H RSP; Z.div_mod_to_equations; lia
          | rewrite !shad_div, granules_div by lia; unfold ASHOFF; clear - DJ1 FV1 FV2 VLO BL1 NR V8 BR4; Z.div_mod_to_equations; lia]] end end. }
    split.
    { lazymatch type of MU2 with munch _ ?mm _ => lazymatch goal with BLKx : rw_cells asegs mm A _ |- _ =>
        eapply rw_cells_transport; [exact BLKx| exact MU2| exact WM2| apply DJW; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia;
          [clear - BL1 BL3 LOS LOA H; lia
          | pose proof BR1 as BNS; unfold ablk, AIMG_HI, KLS in BNS; rewrite shad_div, granules_div by lia; unfold ASHOFF; clear - BNS NR; Z.div_mod_to_equations; lia]] end end. }
    split; [exact OUT2|]. split; [exact RA| exact RSA].
  Qed.
End Proof.
End S.
End CANSEC1.
