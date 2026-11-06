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
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase ARep AMalloc_iface F_apoison F_annot F_annot_sg F_annot_grow APoisonR_iface I_asan_memset.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac AU_h_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import ShadowTac AM_kitA AM_kitB AM_kitC AM_annotw BM_clear.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UM_guards.
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
Definition bxd (P : Prop) : Prop := P.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxd P) in H end.
(* [comment removed for export] *)
Local Ltac pose_hr i SHVi :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VSHx : rw_cells bsegs mm (shad ?V) [C1 _; C1 _; C1 _] |- _ =>
      let H := fresh "HR" in pose proof (sh3_read mm (shad V) i ltac:(lia) VSHx) as H;
      unfold bxd in SHVi; rewrite <- SHVi in H; box SHVi end end.
Local Ltac pose_hr0 SHV :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VSHx : rw_cells bsegs mm (shad ?V) [C1 _; C1 _; C1 _] |- _ =>
      let H := fresh "HR" in pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSHx) as H; rewrite Z.add_0_r in H;
      unfold bxd in SHV; rewrite SHV in H; box SHV end end.

Section CANSEC1. Context {rc : runConstT}.
Definition AVDEALLOC : Z := 0xb33e8.
Definition AVDEALLOC_RET : Z := 0xb3460.                  (* [comment removed for export] *)
Definition AVDEALLOC_STACK : Z := 32 + AFREE_STACK.       (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vec2_as_CB : forall m V (a b : word), rw_cells bsegs m V [C8 a; C8 b] -> rw_cells bsegs m V [CB 16 (le8 a ++ le8 b)].
Proof.
  intros m V a b H. eapply rw_cells_recast; [exact H| | |]; cbn; repeat split; reflexivity.
Qed.
Lemma vec2_of_zeros : forall m V, rw_cells bsegs m V [CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells bsegs m V [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m V H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity].
Qed.

Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Definition avdealloc_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (pv : AsanCtrl.aptr) (V lo : Z) (m : amem) (u : unit) (s' : APS) (RNG' : footprint)
    : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m' : amem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aps_rest s' = aps_rest s
    /\ aheap_pres_x CI (lb_remove pv LB) (bv_unsigned sp) V 24 m m'
    /\ AHEAP AI L RNG' (aps_m s') (lb_remove pv LB) m'
    /\ rw_cells bsegs m' V [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Definition avdealloc_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (lo V beg n : Z) (pv : AsanCtrl.aptr) (cls FA FN RLO2 RHI2 : Z),
  AHEAP AI L RNG (aps_m s) LB m -> In (HB pv beg n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AVDEALLOC_STACK ->
  bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  In (mkABlock (ABFake cls) FA FN) LB -> FA <= V -> V + 24 <= FA + FN -> V mod 8 = 0 -> ablk V (V + 24) ->
  rw_cells bsegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + n)); C8 (Z_to_bv 64 (beg + n))] ->
  rw_cells bsegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  FA <= RLO2 -> RLO2 <= V -> V + 24 <= RHI2 -> RHI2 <= FA + FN -> RLO2 mod 64 = 0 -> RHI2 mod 64 = 0 ->
  wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  In [AFREE_PC; AVDEALLOC_RET] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  aps_ok L s ->
  a0 = Z_to_bv 64 V ->
  implMA RNG (HarnessM.opdelete afree_M pv) s
        (avdealloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB pv V lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AVDEALLOC) fc None m (seg_rom bsegs)).

Section Proof.
  Hypothesis OD : opdelete_stmtA AI.
  Hypothesis AI_kind : forall L RNG st LB m p A n, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n.
  Hypothesis AI_premap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> premap_cells m.

  Theorem avdealloc_proof : avdealloc_stmt.
  Proof.
    unfold avdealloc_stmt. intros until RHI2. intros AH HIN MI ST LOA LOS STOP SP16 TP FIN FV1 FV2 V8 VBLK VEC VSH Q1 Q2 Q3 Q4 Q5 Q6 WR2 RR2 HU RSTK RI RV RVS AOK ->.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AVDEALLOC_STACK, AFREE_STACK in LOS. atop_facts.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH FIN) as FB. cbn [ab_addr ab_size] in FB.
    pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO, FB.
    assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (NR & BR & _ & RSB & BSH & WRB & _ & ARENA).
    destruct (AI_kind _ _ _ _ _ _ _ _ AH HIN) as (ch & LIVE & CSZ & UBEG & KIND).
    pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1. unfold AREQMAX in NR.
    assert (AL : beg mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
    assert (R8B : n <= rup8 n <= n + 7) by (unfold rup8, rdn8; clear - NR; Z.div_mod_to_equations; lia).
    pose proof (ablk_rup8 _ _ BR1 AL ltac:(lia)) as BRU. pose proof (ablk_lin _ _ BRU) as (_ & _ & BU3 & BU4).
    (* [comment removed for export] *)
    assert (DJ : V + 24 <= beg \/ beg + n <= V).
    { pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH FIN HIN ltac:(discriminate)) as D. cbn [ab_addr ab_size] in D. clear - D FV1 FV2. lia. }
    assert (DJ8 : V + 24 <= beg \/ beg + rup8 n <= V).
    { destruct DJ as [D|D]; [left; exact D| right]. clear - D V8 AL R8B NR. unfold rup8, rdn8 in *. Z.div_mod_to_equations. lia. }
    assert (AR : exists G, shlen (rup8 n) = G /\ G = granules n /\ 0 / 8 = 0 /\ n / 8 <= G /\ 0 <= n / 8 /\ 8 * G <= n + 7)
      by (exists (shlen (rup8 n)); rewrite <- granules_rup8 by lia; unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
          repeat split; clear - NR; Z.div_mod_to_equations; lia).
    destruct AR as (G & EG & EGG & E08 & GNG & N80 & G8).
    assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
    assert (SHV16 : Z.shiftr (V + 16) 3 + 2147450880 = shad V + 2) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
    assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI H; Z.div_mod_to_equations; lia).
    assert (SHBB : 0x7fff8000 <= shad beg /\ shad beg + G <= 0x10007fff8000)
      by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - BL1 BU3 NR H G8 R8B; Z.div_mod_to_equations; lia).
    assert (SHDJ : shad V + 3 <= shad beg \/ shad beg + G <= shad V).
    { rewrite SHV. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. clear - DJ8 V8 AL G8 R8B NR GNG N80. Z.div_mod_to_equations. lia. }
    box SHV; box SHV16.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT & _ & _ & SHB & _).
    assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (unfold bxd in SHV; rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
    assert (ACC2 : rng RNG (Z.shiftr (V + 16) 3 + 2147450880) 1) by (unfold bxd in SHV16; rewrite SHV16; eapply rng_sub'; [exact RVS| lia]).
    (* [comment removed for export] *)
    pose proof (cells_of_ablock_shadow m beg n ltac:(lia) ltac:(lia) ltac:(lia) BSH) as FULL. rewrite <- EGG in FULL.
    pose proof FULL as FULL0. box FULL0.     (* [comment removed for export] *)
    rewrite <- vpat_tight in FULL.
    unfold HarnessM.opdelete in |- *.
    apply implMA_from_evtF.
    pose proof (munch_refl [(shad beg, shad beg + G); (lo, bv_unsigned sp); (V + 8, V + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    carve_frame 32%nat ST.
    unfold AVDEALLOC.
    zstep. zstep. zstep. zstep. zstep.      (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    pose_hr0 SHV.
    zstep. zstep. astep. astep.             (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K BL1 BL4 NR; lia| clear K]).   (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with VECx : rw_cells bsegs mm V _ |- _ =>
      assert (HWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(shad beg, shad beg + G); (lo, bv_unsigned sp); (V + 8, V + 16)])
        by (repeat constructor; cbn; unfold AIMG_HI; clear - SHBB LOA H VLO; lia);
      pose proof (poison_cells_frame _ _ _ (poison_cells_of_aheap AI _ _ _ _ _ AH) MU WM HWI) as PCq;
      pose proof (annot_cells_frame _ _ _ (annot_cells_of_aheap AI _ _ _ _ _ AH (hrt_cells_of_aheap AI _ _ _ _ _ AH)) MU WM HWI) as ACq;
      name_sp sp (-32)%Z;
      eapply evtF_cut;
      [ eapply (aclear _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg n n lo);
        first [ exact PCq | exact ACq | exact VECx | exact V8 | exact VBLK | exact DJ8 | exact AL | exact BRU | exact RI | exact RV | exact RVS | reflexivity
              | (rewrite Hsp; eassumption) | (rewrite EG; exact FULL) | eassumption
              | (rewrite Hsp; unfold ANNOTW_STACK; clear - LOS; lia) | (rewrite Hsp; clear - RSP LOS LOA H; lia)
              | (rewrite EG; eapply rng_sub'; [exact RSB| rewrite EGG; unfold granules; lia])
              | (rewrite Hsp; eapply rng_sub'; [exact RSTK| clear - LOS LOA STOP LO0; lia])
              | (clear - NR; lia) | lia ]
      | cbv beta; unfold aclear_post, ANNOTW_STACK; rewrite ?EG; clear PCq ACq HWI; post_call bsegs mm ]
      end end.
    unname_sp.
    (* [comment removed for export] *)
    try lazymatch goal with LEGS : (exists mx, munch _ _ mx /\ _ /\ _ /\ _) |- _ => clear LEGS end.
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with VECx : rw_cells bsegs mm V _, OUTx : rw_cells bsegs mm (shad beg) [CB _ (repeat _ _)] |- _ =>
      assert (HWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(shad beg, shad beg + G); (lo, bv_unsigned sp); (V + 8, V + 16)])
        by (repeat constructor; cbn; unfold AIMG_HI; clear - SHBB LOA H VLO; lia);
      pose proof (poison_cells_frame _ _ _ (poison_cells_of_aheap AI _ _ _ _ _ AH) MU WM HWI) as PCq;
      pose proof (annot_cells_frame _ _ _ (annot_cells_of_aheap AI _ _ _ _ _ AH (hrt_cells_of_aheap AI _ _ _ _ _ AH)) MU WM HWI) as ACq;
      pose proof (artcells_frame _ _ _ (AI_rtcells AI _ _ _ _ _ AH) MU WM HWI) as ARTq;
      pose proof (premap_cells_frameA _ _ _ (AI_premap _ _ _ _ _ AH) MU WM HWI) as PRMq;
      pose proof (arelro_munchA _ _ _ (arelro_of_aheap AI _ _ _ _ _ AH) MU HWI) as RRq;
      assert (ARENAq : exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= beg /\ beg + n + 64 <= RHI
                 /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at bsegs mm (shad RLO) (shlen (RHI - RLO)))
        by (destruct ARENA as (RLO & RHI & X1 & X2 & X3 & X4 & X5 & X6); exists RLO, RHI; repeat (split; [assumption|]); eapply wr_at_transport; [exact X6| exact WM]);
      name_sp sp (-32)%Z;
      eapply evtF_cut;
      [ eapply (annotw_delete_grow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg n lo (aps_m s) pv ch);
        first [ exact PCq | exact ACq | exact ARTq | exact PRMq | exact RRq | exact VECx | exact V8 | exact VBLK | exact DJ8 | exact BR | exact LIVE | exact CSZ | exact UBEG | exact KIND
              | exact ARENAq | exact RI | exact RV | exact RVS | reflexivity
              | (rewrite Hsp; eassumption) | (rewrite EG; exact OUTx) | eassumption
              | (rewrite Hsp; unfold ANNOTW_STACK; clear - LOS; lia) | (rewrite Hsp; clear - RSP LOS LOA H; lia)
              | (unfold AREQMAX; clear - NR; lia)
              | (rewrite EG; eapply rng_sub'; [exact RSB| rewrite EGG; unfold granules; lia])
              | (rewrite Hsp; eapply rng_sub'; [exact RSTK| clear - LOS LOA STOP LO0; lia])
              | lia ]
      | cbv beta; unfold annotw_grow_post, ANNOTW_STACK; rewrite ?EG; clear PCq ACq ARTq PRMq RRq ARENAq HWI; post_call bsegs mm ]
      end end.
    unname_sp.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with BODY : rw_cells bsegs mm (shad beg) [CB _ (repeat _ _)], LAST : (n mod 8 <> 0 -> rw_cells bsegs mm _ [C1 _]) |- _ =>
      pose proof (bsb_cells_join mm (shad beg) n ltac:(lia) BODY LAST) as FULL3; rewrite <- EGG in FULL3;
      assert (MU3 : munch [(lo, bv_unsigned sp); (V + 8, V + 16)] m mm)
        by (unfold bxd in FULL0; eapply (munch_unwrite _ m mm (shad beg) (shad beg + G) (Z.to_nat G) (block_shadow_bytes n)); [exact MU| clear - GNG N80; lia| exact FULL0| exact FULL3| clear - SHBB; lia| clear - SHBB GNG N80; lia]);
      assert (AH3 : AHEAP AI L RNG (aps_m s) LB mm)
        by (eapply (AI_frame AI); [exact AH| exact MU3| exact WM|]; constructor; [apply aclient_range_stack; cbn; clear - LOA STOP LY3; lia| constructor; [eapply aclient_range_fake; [exact FIN| cbn; lia| cbn; lia]| constructor]]);
      clear BODY LAST FULL3; box MU3
      end end.
    pose_hr0 SHV.
    astep. astep.                           (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    pose_hr 2 SHV16.
    astep. astep.                           (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    try replace (beg + n - beg) with n by lia.
    zstep.                                  (* [comment removed for export] *)
    apply evtF_done.
    name_sp sp (-32)%Z.
    eapply implMA_post_evtF.
    { lazymatch goal with AH3 : AHEAP AI L RNG (aps_m s) LB ?mm |- implMA _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (proj1 OD) with (lo := lo) (tr := []); try reflexivity; rewrite ?Hsp; rewrite ?unsigned_lit by lia;
        first [ exact AH3 | exact HIN | exact TP | exact RSTK | exact AOK | eassumption
              | (apply uc_stop; intros (X1 & _); clear - X1 VHI LOA LOS; lia)
              | (unfold AVDEALLOC_RET in HU; exact HU)
              | (unfold AFREE_PC; lia) | (unfold AFREE_STACK; clear - LOS; lia) | (cbn; lia)
              | (clear - SP16 RSP LOS LOA H; Z.div_mod_to_equations; lia) | lia ] end. }
    cbv beta. intros [] s' RNG' ms1 (ARS1 & PO).
    destruct PO as (FLE & u0 & u1 & u2 & c0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mq4 & -> & MI4 & ST4 & HPR4 & AH4).
    rewrite ?Hsp in ST4, HPR4. rewrite ?unsigned_lit in ST4, HPR4 by lia.
    unname_sp. unfold AVDEALLOC_RET. retlit.
    (* [comment removed for export] *)
    pose proof (lb_remove_keep_fake pv cls FA FN LB FIN) as FIN4.
    pose proof (rng_fp_le _ _ _ _ FLE RSTK) as RSTK4. pose proof (rng_fp_le _ _ _ _ FLE RV) as RV4. pose proof (rng_fp_le _ _ _ _ FLE RVS) as RVS4.
    pose proof (rng_fp_le _ _ _ _ FLE RI) as RI4. pose proof (rng_fp_le _ _ _ _ FLE RR2) as RR4.
    lazymatch type of AH3 with AHEAP _ _ _ _ _ ?m3 =>
      lazymatch goal with FRx : rw_cells bsegs m3 (bv_unsigned sp + -32) ?cs, VECx : rw_cells bsegs m3 V ?vcs, VSHx : rw_cells bsegs m3 (shad V) ?scs, WRx : wr_at bsegs m3 (shad RLO2) _ |- _ =>
      assert (FR4 : rw_cells bsegs mq4 (bv_unsigned sp + -32) cs) by (eapply aheap_pres_rw_cells; [exact HPR4| exact FRx| apply aclient_range_stack; cbn; lia]);
      assert (VEC4 : rw_cells bsegs mq4 V vcs) by (eapply aheap_pres_rw_cells; [exact HPR4| exact VECx| eapply aclient_range_fake; [exact FIN4| cbn; lia| cbn; lia]]);
      assert (VSH4 : rw_cells bsegs mq4 (shad V) scs)
        by (eapply aheap_pres_rw_cells; [exact HPR4| exact VSHx|]; right; right; right; right; exists cls, FA, FN; split; [exact FIN4|];
            rewrite shad_div; unfold ASHOFF; cbn [cells_size csize Nat.add]; clear - V8 FV1 FV2; Z.div_mod_to_equations; lia);
      assert (WR4 : wr_at bsegs mq4 (shad RLO2) (shad RHI2 - shad RLO2))
        by (eapply aheap_pres_wr_at; [exact HPR4| exact WRx|]; right; right; right; right; exists cls, FA, FN; split; [exact FIN4|];
            rewrite !shad_div; unfold ASHOFF; clear - Q1 Q2 Q3 Q4 Q5 Q6 V8 FB; Z.div_mod_to_equations; lia);
      clear FRx VECx VSHx WRx
      end end.
    (* [comment removed for export] *)
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH4) as (GOT4 & RIC4 & REAL4 & SHB4 & _ & INI4 & LAY4).
    pose proof (munch_refl [(lo, bv_unsigned sp + -32); (V, V + 24)] mq4) as MU5. pose proof (wmono_refl bsegs mq4) as WM5.
    pose proof (rng_fp_le _ _ _ _ FLE ACC2) as ACC6.   (* [comment removed for export] *)
    pose_hr 2 SHV16.
    astep. astep.                           (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with VECx : rw_cells bsegs mm V [C8 _; C8 _; C8 _], VSHx : rw_cells bsegs mm (shad V) _ |- _ =>
      destruct (rw_cells_cut bsegs mm V _ 2 VECx) as [V12 V3x]; cbn [firstn skipn cells_size csize Nat.add] in V12, V3x; change (Z.of_nat 16) with 16 in V3x;
      pose proof (vec2_as_CB mm V _ _ V12) as VCB; clear V12 VECx;
      pose proof (unpoisoned_sub mm V (V + 24) V (V + 16) (sh3_unpoisoned mm V VSHx V8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as UNP
      end end.
    name_sp sp (-32)%Z.
    eapply evtF_cut.
    { eapply (asan_memset_spec RNG') with (lo := lo) (RLO2 := RLO2) (RHI2 := RHI2); rewrite ?Hsp; rewrite ?unsigned_lit by lia;
        first [ exact VCB | exact UNP | exact RI4 | exact RR4 | eassumption
              | (unfold KHIGH; clear - LOA H; lia)
              | (left; clear - VHI LOA H; lia)
              | (apply ablk_app_blk; [eapply ablk_sub; [exact VBLK| lia| lia]| lia])
              | (pose proof (AI_block_bounds AI _ _ _ _ _ _ AH4 FIN4) as FB4; cbn [ab_addr ab_size] in FB4; unfold KEND; unfold AIMG_HI in FB4; clear - Q1 Q2 Q3 Q4 Q5 Q6 FB4 H; repeat split; lia)
              | (eapply rng_sub'; [exact RSTK4| clear - LOS LOA STOP LO0; lia])
              | (eapply rng_sub'; [exact RV4| lia])
              | lia ]. }
    cbv beta. unfold asan_memset_post. rewrite ?Hsp. rewrite ?unsigned_lit by lia. clear VCB UNP.   (* [comment removed for export] *)
    lazymatch goal with MU5x : munch _ mq4 ?mcur |- forall ms', _ -> evtF _ _ _ _ => post_call bsegs mcur end.
    all: rewrite ?unsigned_lit in * by lia.
    try unname_sp.
    lazymatch goal with SET : rw_cells bsegs ?mm V [CB (Z.to_nat 16) _], V3x : rw_cells bsegs ?mm' (V + 16) [C8 _] |- _ =>
      change (Z.to_nat 16) with 16%nat in SET; change (0 mod 256) with 0 in SET;
      pose proof (rw_cells_app_join bsegs mm V _ _ (vec2_of_zeros mm V SET) V3x) as VEC5; cbn [app] in VEC5; clear SET V3x end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with MUx : munch _ mq4 mm, WMx : wmono bsegs mq4 mm |- _ =>
      assert (AH5 : AHEAP AI L RNG' (aps_m s') (lb_remove pv LB) mm)
        by (eapply (AI_frame AI); [exact AH4| exact MUx| exact WMx|];
            constructor; [apply aclient_range_stack; cbn; clear - LOA STOP LY3; lia| constructor; [eapply aclient_range_fake; [exact FIN4| cbn; lia| cbn; lia]| constructor]])
      end end.
    zstep. zstep. zstep. zstep. zstep.      (* [comment removed for export] *)
    lazymatch goal with H : stk bsegs _ lo (bv_unsigned sp + -32) |- _ => release_frame FR4 H (bv_unsigned sp) end.
    zstep.                                  (* [comment removed for export] *)
    apply evtF_done. unfold avdealloc_post. split; [exact FLE|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
      lazymatch goal with MUx : munch _ mq4 mm, WMx : wmono bsegs mq4 mm, MIx : mem_inv bsegs mm, STx : stk bsegs mm lo _ |- _ =>
      do 15 eexists; exists mm; split; [reflexivity|];
      split; [exact MIx|]; split; [exact STx|]; split; [exact ARS1|];
      split;
      [ (* [comment removed for export] *)
        unfold bxd in MU3;
        eapply aheap_pres_x_trans;
        [ eapply aheap_pres_x_of_munch; [exact MU3| exact WM|];
          intros a Ha Hc Hx; cbn [outside];
          pose proof (aclient_lo_or_sp AI _ _ _ _ (lb_remove pv LB) _ _ a AH ltac:(intros b Hb; exact (lb_remove_sub _ _ _ Hb)) Hc); clear - H0 Hx LOA; lia
        | eapply aheap_pres_x_trans;
          [ eapply aheap_pres_x_of_pres; [exact HPR4| lia| intros b Hb; exact Hb]
          | eapply aheap_pres_x_of_munch; [exact MUx| exact WMx|];
            intros a Ha Hc Hx; cbn [outside];
            pose proof (aclient_lo_or_sp AI _ _ _ _ (lb_remove pv LB) _ _ a AH5 ltac:(intros b Hb; exact Hb) Hc); clear - H0 Hx LOA LOS; lia ] ]
      | split; [exact AH5| split; [exact VEC5| eassumption]] ]
      end end.
  Qed.
End Proof.
End S.
End CANSEC1.
