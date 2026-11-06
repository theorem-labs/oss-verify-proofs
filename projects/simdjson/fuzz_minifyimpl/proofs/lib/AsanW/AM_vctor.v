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
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase ARep AMalloc_iface F_apoison F_annot F_annot_sg F_annot_grow APoisonR_iface I_asan_memset.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac AU_h_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import ShadowTac AM_kitA AM_kitB AM_kitC AM_annotw AM_valloc AM_model.
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
Definition bxc (P : Prop) : Prop := P.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxc P) in H end.

Section CANSEC1. Context {rc : runConstT}.
Definition AVCTOR : Z := 0xb2280.
Definition AVCTOR_VRET : Z := 0xb22d4.                     (* [comment removed for export] *)
Definition AVCTOR_STACK : Z := 64 + AVALLOC_STACK.         (* [comment removed for export] *)

(* [comment removed for export] *)
Section Fresh.
  Variable AI : AMallocIface.
  Lemma fresh_block_outside : forall L RNG st p A n LB m SP a,
    AHEAP AI L RNG st (HB p A n :: LB) m -> ATOP <= SP -> aclient_addr (aci AI) LB SP a -> (a < A \/ A + n <= a).
  Proof.
    intros L RNG st p A n LB m SP a AH HS Hc. pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ SP a AH HS Hc). lia.
  Qed.
End Fresh.

Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).

(* [comment removed for export] *)
Definition avctor_zero_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (V lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m' : amem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (V, V + 24)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' V [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Lemma avctor_zero : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo V : Z) (v0 v1 v2 : word) (cls FA FN RLO2 RHI2 : Z),
  AHEAP AI L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AVCTOR_STACK ->
  bv_unsigned sp <= al_top L -> bv_unsigned sp mod 16 = 0 ->
  In (mkABlock (ABFake cls) FA FN) LB -> FA <= V -> V + 24 <= FA + FN -> V mod 8 = 0 -> ablk V (V + 24) ->
  rw_cells asegs m V [C8 v0; C8 v1; C8 v2] ->
  rw_cells asegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  FA <= RLO2 -> RLO2 <= V -> V + 24 <= RHI2 -> RHI2 <= FA + FN -> RLO2 mod 64 = 0 -> RHI2 mod 64 = 0 ->
  wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 0 ->
  evtF asegs RNG (avctor_zero_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc V lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 AVCTOR) fc None m (seg_rom asegs)).
Proof.
  intros until RHI2. intros AH MI ST LOA LOS STOP SP16 FIN FV1 FV2 V8 VBLK VEC VSH Q1 Q2 Q3 Q4 Q5 Q6 WR2 RR2 RSTK RI RV RVS -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold AVCTOR_STACK, AVALLOC_STACK, OPNEW_STACK_A, AMALLOC_STACK in LOS. atop_facts.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
  pose proof (AI_block_bounds AI _ _ _ _ _ _ AH FIN) as FB. cbn [ab_addr ab_size] in FB.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO, FB.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF; clear - VLO VHI H; Z.div_mod_to_equations; lia).
  pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT & RIC & REAL & SHB & _ & INI & LAY).
  unfold avctor_zero_post, AVCTOR.
  pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.     (* [comment removed for export] *)
  zstep.                                              (* [comment removed for export] *)
  zstep. zstep. zstep.                                (* [comment removed for export] *)
  zstep. zstep. zstep.                                (* [comment removed for export] *)
  zstep.                                              (* [comment removed for export] *)
  name_sp sp (-64)%Z.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VECx : rw_cells asegs mm V _, VSHx : rw_cells asegs mm (shad V) _ |- _ =>
    pose proof (vec3_as_CB mm V v0 v1 v2 VECx) as VCB;
    pose proof (sh3_unpoisoned mm V VSHx V8 ltac:(lia) ltac:(lia)) as UNP;
    eapply evtF_cut;
    [ eapply (asan_memset_spec RNG) with (lo := lo) (RLO2 := RLO2) (RHI2 := RHI2); rewrite ?Hsp; rewrite ?unsigned_lit by lia;
      first [ exact VCB | exact UNP | exact RI | eassumption
            | (unfold KHIGH; clear - LOA H; lia)
            | (left; clear - VHI LOA H; lia)
            | (apply ablk_app_blk; [exact VBLK| lia])
            | (unfold KEND; repeat split; first [assumption | lia])
            | (eapply wr_at_transport; [exact WR2| eassumption])
            | (eapply rng_sub'; [exact RSTK| clear - LOS LOA STOP LO0; lia])
            | lia ]
    | cbv beta; unfold asan_memset_post; rewrite ?Hsp; rewrite ?unsigned_lit by lia; clear VCB UNP; post_call asegs mm ]
    end end.
  all: rewrite ?unsigned_lit in * by lia.
  try unname_sp.
  (* [comment removed for export] *)
  lazymatch goal with SET : rw_cells asegs ?mm V [CB (Z.to_nat 24) _] |- _ =>
    change (Z.to_nat 24) with 24%nat in SET; change (0 mod 256) with 0 in SET; pose proof (vec3_of_zeros mm V SET) as VEC0; clear SET end.
  zstep. zstep.                                       (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K; lia]).   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.    (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  zstep.                                              (* [comment removed for export] *)
  finish.
Qed.

(* [comment removed for export] *)
Definition avctor_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (V n lo : Z) (m : amem) (p : AsanCtrl.aptr) (s' : APS) (RNG' : footprint)
    : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m' : amem) (A : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aps_rest s' = aps_rest s
    /\ ablock_range A n
    /\ aheap_pres_x CI LB (bv_unsigned sp) V 24 m m'
    /\ AHEAP AI L RNG' (aps_m s') (HB p A n :: LB) m'
    /\ rw_cells asegs m' V [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + n)); C8 (Z_to_bv 64 (A + n))]
    /\ rw_cells asegs m' (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
    /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7)).

Definition avctor_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (lo V n : Z) (v0 v1 v2 : word) (cls FA FN RLO2 RHI2 : Z),
  AHEAP AI L RNG (aps_m s) LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AVCTOR_STACK ->
  bv_unsigned sp <= al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  In (mkABlock (ABFake cls) FA FN) LB -> FA <= V -> V + 24 <= FA + FN -> V mod 8 = 0 -> ablk V (V + 24) ->
  rw_cells asegs m V [C8 v0; C8 v1; C8 v2] ->
  rw_cells asegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  FA <= RLO2 -> RLO2 <= V -> V + 24 <= RHI2 -> RHI2 <= FA + FN -> RLO2 mod 64 = 0 -> RHI2 mod 64 = 0 ->
  wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  In [AMALLOC_PC; AOPNEW_RET] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  aps_ok L s ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 n -> 0 < n < 2^26 ->
  implMA RNG (opnewA n) s
        (avctor_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB V n lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AVCTOR) fc None m (seg_rom asegs)).

Section Proof.
  Hypothesis ONTA : opnew_stmtA AI.
  Hypothesis AI_kind : forall L RNG st LB m p A n, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n.
  Hypothesis AI_premap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> premap_cells m.

  Theorem avctor_proof : avctor_stmt.
  Proof.
    unfold avctor_stmt. intros until RHI2. intros AH MI ST LOA LOS STOP SP16 TP FIN FV1 FV2 V8 VBLK VEC VSH Q1 Q2 Q3 Q4 Q5 Q6 WR2 RR2 HU RSTK RI RV RVS AOK -> -> NR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AVCTOR_STACK, AVALLOC_STACK, OPNEW_STACK_A, AMALLOC_STACK in LOS. atop_facts.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH FIN) as FB. cbn [ab_addr ab_size] in FB.
    pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO, FB.
    assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
    assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
    assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI H; Z.div_mod_to_equations; lia).
    box SHV; box SHV8.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT & RIC & REAL & SHB & _ & INI & LAY).
    unfold opnewA, HarnessM.opnew in |- *.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 64%nat ST.
    unfold AVCTOR.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.     (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    zstep. zstep. zstep.                                (* [comment removed for export] *)
    zstep. zstep. zstep.                                (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    name_sp sp (-64)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with VECx : rw_cells asegs mm V _, VSHx : rw_cells asegs mm (shad V) _ |- _ =>
      pose proof (vec3_as_CB mm V v0 v1 v2 VECx) as VCB;
      pose proof (sh3_unpoisoned mm V VSHx V8 ltac:(lia) ltac:(lia)) as UNP;
      eapply evtF_cut;
      [ eapply (asan_memset_spec RNG) with (lo := lo) (RLO2 := RLO2) (RHI2 := RHI2); rewrite ?Hsp; rewrite ?unsigned_lit by lia;
        first [ exact VCB | exact UNP | exact RI | eassumption
              | (unfold KHIGH; clear - LOA H; lia)
              | (left; clear - VHI LOA H; lia)
              | (apply ablk_app_blk; [exact VBLK| lia])
              | (unfold KEND; repeat split; first [assumption | lia])
              | (eapply wr_at_transport; [exact WR2| eassumption])
              | (eapply rng_sub'; [exact RSTK| clear - LOS LOA STOP LO0; lia])
              | lia ]
      | cbv beta; unfold asan_memset_post; rewrite ?Hsp; rewrite ?unsigned_lit by lia; clear VCB UNP; post_call asegs mm ]
      end end.
    all: rewrite ?unsigned_lit in * by lia.
    try unname_sp.
    (* [comment removed for export] *)
    lazymatch goal with SET : rw_cells asegs ?mm V [CB (Z.to_nat 24) _] |- _ =>
      change (Z.to_nat 24) with 24%nat in SET; change (0 mod 256) with 0 in SET; pose proof (vec3_of_zeros mm V SET) as VEC0; clear SET end.
    zstep. zstep.                                       (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K NR; lia| clear K]).   (* [comment removed for export] *)
    zstep. zstep.                                       (* [comment removed for export] *)
    zstep.                                              (* [comment removed for export] *)
    apply evtF_done.
    (* [comment removed for export] *)
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MUx : munch _ m mx, WMx : wmono asegs m mx |- _ =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
        by (eapply (AI_frame AI); [exact AH| exact MUx| exact WMx|];
            constructor; [apply aclient_range_stack; cbn; clear - LOA STOP LY3; lia| constructor; [eapply aclient_range_fake; [exact FIN| cbn; lia| cbn; lia]| constructor]]);
      pose proof (aheap_pres_x_of_munch CI LB (bv_unsigned sp) V 24 _ m mx MUx WMx) as HPX1;
      box MUx; box WMx
      end end.
    lazymatch type of HPX1 with ?PREM -> _ =>
      assert (OUT1 : PREM)
        by (intros a Ha Hc Hx; cbn [outside]; pose proof (aclient_lo_or_sp AI _ _ _ _ LB _ _ a AH ltac:(intros b Hb; exact Hb) Hc); clear - H0 Hx LOA; lia);
      specialize (HPX1 OUT1); clear OUT1 end.
    name_sp sp (-64)%Z.
    eapply implMA_post_evtF.
    { eapply (avalloc_proof AI ONTA) with (lo := lo) (L := L) (LB := LB) (V := V) (n := n) (cls := cls) (FA := FA) (FN := FN); try reflexivity; rewrite ?Hsp; rewrite ?unsigned_lit by lia;
        first [ exact AH1 | exact TP | exact FIN | exact V8 | exact VBLK | exact HU | exact RI | exact RV | exact RVS | exact AOK | eassumption
              | (unfold AVALLOC_STACK, OPNEW_STACK_A, AMALLOC_STACK; clear - LOS; lia)
              | (clear - STOP; lia)
              | (clear - SP16 RSP LOS LOA H; Z.div_mod_to_equations; lia)
              | (eapply rng_sub'; [exact RSTK| clear - LOS LOA STOP LO0; lia])
              | lia ]. }
    cbv beta. intros p s' RNG' ms1 PO.
    destruct PO as (FLE & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mq1 & mq2 & A & jk & -> & MI2 & ST2 & ARS1 & BR & HPR1 & AH2 & MI1 & MU12 & WM12
                    & VEC2 & VSH2 & BLK2 & OUT2 & RA & RSA).
    rewrite ?Hsp in ST2, HPR1, MU12. rewrite ?unsigned_lit in ST2, HPR1, MU12 by lia.
    unname_sp. unfold AVCTOR_VRET. retlit.
    pose proof (rng_fp_le _ _ _ _ FLE RSTK) as RSTK1. pose proof (rng_fp_le _ _ _ _ FLE RV) as RV1. pose proof (rng_fp_le _ _ _ _ FLE RVS) as RVS1.
    pose proof (rng_fp_le _ _ _ _ FLE RI) as RI1.
    pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
    assert (AL : A mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
    assert (R8B : n <= rup8 n <= n + 7) by (unfold rup8, rdn8; clear - NR; Z.div_mod_to_equations; lia).
    assert (AR : exists G, shlen (rup8 n) = G /\ G = granules n /\ shlen (n + 7) = G /\ n / 8 <= G /\ 0 <= n / 8 /\ 8 * G <= n + 7)
      by (exists (shlen (rup8 n)); rewrite <- granules_rup8 by lia; unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
          repeat split; clear - NR; Z.div_mod_to_equations; lia).
    destruct AR as (G & EG & EGG & EG7 & GNG & N80 & G8).
    rewrite EG7 in RSA. rewrite <- EGG in OUT2, MU12.
    assert (SHBB : 0x7fff8000 <= shad A /\ shad A + G <= 0x10007fff8000)
      by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - BL1 BL3 NR H G8 R8B; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH2 FIN) as DJ1. cbn [ab_addr ab_size] in DJ1.
    assert (DJ8 : V + 24 <= A \/ A + rup8 n <= V) by (clear - DJ1 FV1 FV2 V8 AL R8B NR; unfold rup8, rdn8 in *; Z.div_mod_to_equations; lia).
    assert (SHDJ : shad V + 3 <= shad A \/ shad A + G <= shad V)
      by (unfold bxc in SHV; rewrite SHV; unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - DJ8 V8 AL G8 R8B NR GNG N80; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs ?mo (bv_unsigned sp + -64) ?cs |- _ =>
      assert (FR1 : rw_cells asegs mq1 (bv_unsigned sp + -64) cs) by (eapply aheap_pres_rw_cells; [exact HPR1| exact FRx| apply aclient_range_stack; cbn; lia]); clear FRx end.
    lazymatch goal with FRx : rw_cells asegs mq1 (bv_unsigned sp + -64) ?cs |- _ =>
      assert (FR2 : rw_cells asegs mq2 (bv_unsigned sp + -64) cs); [eapply rw_cells_transport; [exact FRx| exact MU12| exact WM12| cbn [disjoint_from cells_size csize Nat.add]; clear - LOA LOS VHI SHBB H RSP; lia] |];
      clear FRx end.
    (* [comment removed for export] *)
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_introl eq_refl)) as (_ & _ & _ & RSB & BSH & WRB & _ & ARENA).
    destruct (AI_kind _ _ _ _ _ _ _ _ AH2 (or_introl eq_refl)) as (ch & LIVE & CSZ & UBEG & KIND).
    pose proof (cells_of_ablock_shadow mq1 A n ltac:(lia) ltac:(lia) ltac:(lia) BSH) as FULL1. rewrite <- EGG in FULL1.
    (* [comment removed for export] *)
    assert (MU2 : munch [(shad A, shad A + G); (lo, bv_unsigned sp + -64); (V, V + 24); (A, A + n)] mq1 mq2)
      by (eapply munch_weaken; [| exact MU12]; unfold sub_fp; cbn [outside]; intros xq (X1 & X2 & X3 & X4 & _); clear - X1 X2 X3 X4; lia).
    clear MU12. pose proof WM12 as WM2. clear WM12.
    (* [comment removed for export] *)
    pose proof (aheap_pres_x_of_pres CI LB LB (bv_unsigned sp) (bv_unsigned sp + -64) V 24 _ _ HPR1 ltac:(lia) ltac:(intros b Hb; exact Hb)) as HPXv.
    clear HPR1 AH1 AH GOT RIC REAL SHB INI LAY MI1. try clear MI.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH2) as (GOT1 & _ & _ & SHB1 & _).
    assert (ACC1 : rng RNG' (Z.shiftr (V + 8) 3 + 2147450880) 1) by (unfold bxc in SHV8; rewrite SHV8; eapply rng_sub'; [exact RVS1| lia]).
    pose proof (sh3_read mq2 (shad V) 1 ltac:(lia) VSH2) as HR1. unfold bxc in SHV8. rewrite <- SHV8 in HR1. box SHV8.
    (* [comment removed for export] *)
    assert (ADJ : A + n <= shad A \/ shad A + G <= A)
      by (unfold ablk, AIMG_HI, KLS in BR1; unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - BR1 BL1 BL3 NR G8 R8B H; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. astep. astep.      (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with VECx : rw_cells asegs mm V _, OUTx : rw_cells asegs mm (shad A) [CB _ (repeat _ _)], MUx : munch _ mq1 mm, WMx : wmono asegs mq1 mm |- _ =>
      assert (HWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(shad A, shad A + G); (lo, bv_unsigned sp + -64); (V, V + 24); (A, A + n)])
        by (repeat constructor; cbn; unfold AIMG_HI; clear - SHBB LOA H VLO BL1; lia);
      pose proof (poison_cells_frame _ _ _ (poison_cells_of_aheap AI _ _ _ _ _ AH2) MUx WMx HWI) as PC1;
      pose proof (annot_cells_frame _ _ _ (annot_cells_of_aheap AI _ _ _ _ _ AH2 (hrt_cells_of_aheap AI _ _ _ _ _ AH2)) MUx WMx HWI) as AC1;
      pose proof (artcells_frame _ _ _ (AI_rtcells AI _ _ _ _ _ AH2) MUx WMx HWI) as ART1;
      pose proof (premap_cells_frameA _ _ _ (AI_premap _ _ _ _ _ AH2) MUx WMx HWI) as PRM1;
      pose proof (arelro_munchA _ _ _ (arelro_of_aheap AI _ _ _ _ _ AH2) MUx HWI) as RR1;
      pose proof (client_rt_of_aheap AI _ _ _ _ _ AH2) as (_ & _ & _ & _ & _);
      assert (ARENA1 : exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
                 /\ rng RNG' (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs mm (shad RLO) (shlen (RHI - RLO)))
        by (destruct ARENA as (RLO & RHI & X1 & X2 & X3 & X4 & X5 & X6); exists RLO, RHI; repeat (split; [assumption|]); eapply wr_at_transport; [exact X6| exact WMx]);
      name_sp sp (-64)%Z;
      eapply evtF_cut;
      [ eapply (annotw_increase_grow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V A n lo (aps_m s') p ch);
        first [ exact PC1 | exact AC1 | exact ART1 | exact PRM1 | exact RR1 | exact VECx | exact V8 | exact VBLK | exact DJ8 | exact BR | exact LIVE | exact CSZ | exact UBEG | exact KIND
              | exact ARENA1 | exact RI1 | exact RV1 | exact RVS1 | reflexivity
              | (pose proof ART1 as (_ & Xg & _ & _ & Xs & _); first [exact Xg | exact Xs])      (* [comment removed for export] *)
              | (rewrite Hsp; eassumption) | (rewrite EG; exact OUTx) | eassumption
              | (rewrite Hsp; unfold ANNOTW_STACK; clear - LOS; lia) | (rewrite Hsp; clear - RSP LOS LOA H STOP LY3; lia)
              | (unfold AREQMAX; clear - NR; lia)
              | (rewrite EG; eapply rng_sub'; [exact RSA| lia])
              | (rewrite Hsp; eapply rng_sub'; [exact RSTK1| clear - LOS LOA STOP LO0; lia])
              | lia ]
      | cbv beta; unfold annotw_grow_post, ANNOTW_STACK; rewrite ?EG; clear PC1 AC1 ART1 PRM1 RR1 ARENA1; post_call asegs mm ]
      end end.
    unname_sp.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with BODY : rw_cells asegs mm (shad A) [CB _ (repeat _ _)], LAST : (n mod 8 <> 0 -> rw_cells asegs mm _ [C1 _]), MUx : munch _ mq1 mm, WMx : wmono asegs mq1 mm |- _ =>
      pose proof (bsb_cells_join mm (shad A) n ltac:(lia) BODY LAST) as FULL3; rewrite <- EGG in FULL3;
      assert (MU3 : munch [(lo, bv_unsigned sp + -64); (V, V + 24); (A, A + n)] mq1 mm)
        by (eapply (munch_unwrite _ mq1 mm (shad A) (shad A + G) (Z.to_nat G) (block_shadow_bytes n)); [exact MUx| clear - GNG N80; lia| exact FULL1| exact FULL3| clear - SHBB; lia| clear - SHBB GNG N80; lia]);
      assert (AH3 : AHEAP AI L RNG' (aps_m s') (HB p A n :: LB) mm)
        by (eapply (AI_frame AI); [exact AH2| exact MU3| exact WMx|];
            constructor; [apply aclient_range_stack; cbn; clear - LOA STOP LY3; lia|
            constructor; [eapply aclient_range_fake; [right; exact FIN| cbn; lia| cbn; lia]|
            constructor; [right; left; exists (HB p A n); split; [left; reflexivity| cbn; lia]| constructor]]]);
      clear BODY LAST      (* [comment removed for export] *)
      end end.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (ADJV : shad V + 3 <= A \/ A + n <= shad V) by (unfold ablk, AIMG_HI, KLS in BR1; clear - BR1 SHVB NR; lia).
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with BLKx : rw_cells asegs mm A [CB _ jk], STx : stk asegs mm lo _ |- _ =>
      destruct (blk_window_facts AI _ _ _ _ _ _ _ _ A n AH3 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as (APPb & UNPb & RWb & (RLOb & RHIb & HUb & WHb & RHb));
      pose proof (client_rt_of_aheap AI _ _ _ _ _ AH3) as (GOT3 & RIC3 & REAL3 & SHB3 & _ & INI3 & LAY3);
      name_sp sp (-64)%Z;
      eapply evtF_cut;
      [ eapply (asan_memset_spec RNG') with (lo := lo) (RLO2 := RLOb) (RHI2 := RHIb); rewrite ?Hsp; rewrite ?unsigned_lit by lia;
        first [ exact BLKx | exact APPb | exact UNPb | exact RWb | exact HUb | exact WHb | exact RHb | exact RI1 | eassumption
              | (unfold KHIGH; clear - LOA H; lia)
              | (left; clear - BL3 LOA H; lia)
              | (eapply rng_sub'; [exact RSTK1| clear - LOS LOA STOP LO0; lia])
              | (clear - NR; lia) | lia ]
      | cbv beta; unfold asan_memset_post; rewrite ?Hsp; rewrite ?unsigned_lit by lia; clear APPb UNPb RWb HUb WHb RHb GOT3 RIC3 REAL3 SHB3 INI3 LAY3; post_call asegs mm ]
      end end.
    all: rewrite ?unsigned_lit in * by lia.
    try unname_sp.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with MU3x : munch [(lo, _); (V, _); (A, _)] mq1 mm, WMx : wmono asegs mq1 mm, VSHx : rw_cells asegs mm (shad V) _ |- _ =>
        rename MU3x into MU3f; rename WMx into WM3f; rename VSHx into VSH4; rename mm into mq4 end end.
    assert (AH4 : AHEAP AI L RNG' (aps_m s') (HB p A n :: LB) mq4).
    { eapply (AI_frame AI); [exact AH2| exact MU3f| exact WM3f|].
      constructor; [apply aclient_range_stack; cbn; clear - LOA STOP LY3; lia|].
      constructor; [eapply aclient_range_fake; [right; exact FIN| cbn; lia| cbn; lia]|].
      constructor; [right; left; exists (HB p A n); split; [left; reflexivity| cbn; lia]| constructor]. }
    clear AH3.
    pose proof (sh3_read mq4 (shad V) 1 ltac:(lia) VSH4) as HR4. unfold bxc in SHV8. rewrite <- SHV8 in HR4. box SHV8.
    astep. astep.                           (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.    (* [comment removed for export] *)
    lazymatch goal with H : stk asegs _ lo _ |- _ => release_frame FR2 H (bv_unsigned sp) end.
    zstep.                                  (* [comment removed for export] *)
    apply evtF_done. unfold avctor_post. split; [exact FLE|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
      lazymatch goal with MU3x : munch [(lo, _); (V, _); (A, _)] mq1 mm, WMx : wmono asegs mq1 mm, VECx : rw_cells asegs mm V _, VSHx : rw_cells asegs mm (shad V) _,
                          SETx : rw_cells asegs mm A [CB _ (repeat _ _)], MIx : mem_inv asegs mm, STx : stk asegs mm lo (bv_unsigned sp) |- _ =>
        rename MU3x into MUe; rename WMx into WMe; rename VECx into VECe; rename VSHx into VSHe; rename SETx into SETe; rename MIx into MIe; rename STx into STe;
        rename mm into me end end.
    (* [comment removed for export] *)
    assert (AH5 : AHEAP AI L RNG' (aps_m s') (HB p A n :: LB) me).
    { eapply (AI_frame AI); [exact AH2| exact MUe| exact WMe|].
      constructor; [apply aclient_range_stack; cbn; clear - LOA STOP LY3; lia|].
      constructor; [eapply aclient_range_fake; [right; exact FIN| cbn; lia| cbn; lia]|].
      constructor; [right; left; exists (HB p A n); split; [left; reflexivity| cbn; lia]| constructor]. }
    do 15 eexists. exists me, A. split; [reflexivity|].
    split; [exact MIe|]. split; [exact STe|]. split; [exact ARS1|]. split; [exact BR|].
    split.
    { (* [comment removed for export] *)
      eapply aheap_pres_x_trans; [exact HPX1|]. eapply aheap_pres_x_trans; [exact HPXv|].
      eapply aheap_pres_x_of_munch; [exact MUe| exact WMe|].
      intros a Ha Hc Hx. cbn [outside].
      pose proof (aclient_lo_or_sp AI _ _ _ _ LB _ _ a AH2 ltac:(intros b Hb; right; exact Hb) Hc) as Y1.
      assert (HSP0 : ATOP <= bv_unsigned sp) by (clear - LOA LOS; lia).
      pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ _ a AH2 HSP0 Hc) as Y2.
      clear - Y1 Y2 Hx LOA LOS. lia. }
    split; [exact AH5|]. split; [exact VECe|]. split; [exact VSHe|].
    split; [first [exact SETe | (eapply rw_cells_recast; [exact SETe| cbn; repeat split; exact I| reflexivity| reflexivity])]|].
    split; [exact RA| first [exact RSA | (rewrite EG7; exact RSA) | (rewrite <- EG7 in RSA; exact RSA)]].
  Qed.
End Proof.
End S.
End CANSEC1.
