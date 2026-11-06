(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase ARep AMalloc_iface F_apoison APoisonR_iface I_strlen I_asan_memmove.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac AU_h_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import ShadowTac AM_kitA AM_kitB AM_kitC AM_model AM_annotw.
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
Definition bxs (P : Prop) : Prop := P.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxs P) in H end.
Local Ltac pose_hr i SHVi :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VSHx : rw_cells asegs mm (shad ?V) [C1 _; C1 _; C1 _] |- _ =>
      let H := fresh "HR" in pose proof (sh3_read mm (shad V) i ltac:(lia) VSHx) as H;
      unfold bxs in SHVi; rewrite <- SHVi in H; box SHVi end end.
Local Ltac pose_hr0 SHV :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VSHx : rw_cells asegs mm (shad ?V) [C1 _; C1 _; C1 _] |- _ =>
      let H := fresh "HR" in pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSHx) as H; rewrite Z.add_0_r in H;
      unfold bxs in SHV; rewrite SHV in H; box SHV end end.

Section CANSEC1. Context {rc : runConstT}.
Definition ASTRCTOR : Z := 0xb2364.
Definition ASTRLEN_STUB : Z := 0x6c220.
Definition AMEMMOVE_I : Z := 0x81224.
Definition ASTRCTOR_STACK : Z := 64 + OPNEW_STACK_A.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ERRMSG : list Z := str "UNCLOSED_STRING: A string is opened, but never closed.".
Definition errmsg : list byte := map (Z_to_bv 8) ERRMSG.

Lemma errmsg_len : length errmsg = 54%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma errmsg_zlen : Z.of_nat (length errmsg) = 54.
Proof. rewrite errmsg_len. reflexivity. Qed.

(* [comment removed for export] *)
Lemma errmsg_bytes_at : forall m, mem_inv asegs m -> bytes_at asegs m AERRMSG (errmsg ++ Z_to_bv 8 0 :: [Z_to_bv 8 0]).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold AERRMSG; lia| unfold AERRMSG; vm_compute; discriminate|].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma errmsg_bytes_at54 : forall m, mem_inv asegs m -> bytes_at asegs m AERRMSG errmsg.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold AERRMSG; lia| unfold AERRMSG; vm_compute; discriminate|].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma errmsg_nonul : ~ In (Z_to_bv 8 0) errmsg.
Proof.
  unfold errmsg. rewrite in_map_iff. intros (z & E & IN).
  assert (F : forallb (fun z => (1 <=? z) && (z <? 256))%bool ERRMSG = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. specialize (F z IN). cbn beta in F. apply andb_prop in F as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2.
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned, !bv_wrap_small in E by (unfold bv_modulus; cbn; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma errmsg_unpoisoned : forall m, client_x m -> unpoisoned m AERRMSG (AERRMSG + 55).
Proof.
  intros m [X _]. unfold unpoisoned, AERRMSG, ASHOFF. split; [lia|]. split; [lia|].
  intros G LT H1 H2.
  assert (HG : 18580 <= G <= 18586) by lia.
  specialize (X (G - 18576) ltac:(lia)). unfold AMSG_SH in X.
  replace (2147469456 + (G - 18576)) with (2147450880 + G) in X by lia.
  exists (Z_to_bv 8 (amsg_shb (G - 18576))). split; [exact X|].
  unfold gran_ok, amsg_shb.
  destruct (Z.ltb_spec (G - 18576) 4) as [L4|L4]; [lia|].
  destruct (Z.ltb_spec (G - 18576) 10) as [L10|L10].
  - left. rewrite sval_lit by lia. reflexivity.
  - assert (EG : G = 18586) by lia. subst G. cbn [Z.sub Z.eqb Pos.eqb]. replace (18586 - 18576 =? 10) with true by reflexivity.
    right. rewrite sval_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma errmsg_hull_wr_at : forall m, client_x m -> wr_at asegs m (shad 0x24480) (shad 0x24500 - shad 0x24480).
Proof.
  intros m [X _]. rewrite !shad_div. unfold ASHOFF. change (2147450880 + 148608 / 8) with AMSG_SH. change (2147450880 + 148736 / 8 - AMSG_SH) with 16.
  unfold wr_at, AMSG_SH. split; [lia|]. split; [lia|]. intros i Hi. unfold AMSG_SH in X. unfold wview. rewrite (X i Hi). discriminate.
Qed.

(* [comment removed for export] *)
Lemma rt_isl_of_artcells : forall m, artcells m -> rt_isl m.
Proof. intros m A. unfold artcells in A. decompose [and] A. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Definition astrctor_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (T lo : Z) (m : amem) (p : AsanCtrl.aptr) (s' : APS) (RNG' : footprint)
    : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m' : amem) (A : Z) (jb : byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aps_rest s' = aps_rest s
    /\ ablock_range A 56
    /\ aheap_pres_x CI LB (bv_unsigned sp) T 24 m m'
    /\ AHEAP AI L RNG' (aps_m s') (HB p A 56 :: LB) m'
    /\ rw_cells asegs m' T [C8 (Z_to_bv 64 57); C8 (Z_to_bv 64 54); C8 (Z_to_bv 64 A)]
    /\ rw_cells asegs m' (shad T) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' A [CB 54 errmsg; C1 (Z_to_bv 8 0); C1 jb]
    /\ rng RNG' A 56 /\ rng RNG' (shad A) (shlen (56 + 7)).

Definition astrctor_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (lo T : Z) (v0 v1 v2 : word) (cls FA FN : Z),
  AHEAP AI L RNG (aps_m s) LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ASTRCTOR_STACK ->
  bv_unsigned sp < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  In (mkABlock (ABFake cls) FA FN) LB -> FA <= T -> T + 24 <= FA + FN -> T mod 8 = 0 -> ablk T (T + 24) ->
  rw_cells asegs m T [C8 v0; C8 v1; C8 v2] ->
  rw_cells asegs m (shad T) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  client_x m -> rt_real_strlen m ->
  In [AMALLOC_PC; AOPNEW_RET] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng RNG T 24 -> rng RNG (shad T) 3 ->
  aps_ok L s ->
  a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 AERRMSG ->
  implMA RNG (opnewA ERRSTR_BYTES) s
        (astrctor_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB T lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASTRCTOR) fc None m (seg_rom asegs)).

Section Proof.
  Hypothesis ONTA : opnew_stmtA AI.
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.

  Theorem astrctor_proof : astrctor_stmt.
  Proof.
    unfold astrctor_stmt. intros until FN. intros AH MI ST LOA LOS STOP SP16 TP FIN FV1 FV2 V8 VBLK VEC VSH CX RSL HU RSTK RI RISH RV RVS AOK -> ->.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ASTRCTOR_STACK, OPNEW_STACK_A, AMALLOC_STACK in LOS. unfold AERRMSG in *. pose proof atop_range as ATR.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH FIN) as FB. cbn [ab_addr ab_size] in FB.
    pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO, FB.
    assert (VNS : T + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= T) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (SHV : shad T = Z.shiftr T 3 + 2147450880) by (unfold shad, ASHOFF; lia).
    assert (SHV8 : Z.shiftr (T + 8) 3 + 2147450880 = shad T + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
    assert (SHV16 : Z.shiftr (T + 16) 3 + 2147450880 = shad T + 2) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
    assert (SHVB : 0x7fff8000 <= shad T /\ shad T + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
    box SHV; box SHV8; box SHV16.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT & RIC & REAL & SHB & _ & INI & LAY).
    pose proof (rt_isl_of_artcells m (AI_rtcells AI _ _ _ _ _ AH)) as ISL.
    unfold opnewA, HarnessM.opnew in |- *.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 64%nat ST.
    unfold ASTRCTOR.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.      (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with MIx : mem_inv asegs mm |- _ =>
      assert (CX1 : client_x mm) by (eapply client_x_munch_gen; [exact CX| exact MU| exact WM| unfold AMSG_SH; cbn [disjoint_from]; clear - LOA ATR; lia| unfold AJT_SH; cbn [disjoint_from]; clear - LOA ATR; lia| unfold AREAL_STRLEN; cbn [disjoint_from]; clear - LOA ATR; lia]);
      pose proof (errmsg_bytes_at mm MIx) as MSGB; unfold AERRMSG in MSGB;
      pose proof (errmsg_unpoisoned mm CX1) as MSGU; unfold AERRMSG in MSGU;
      pose proof (errmsg_hull_wr_at mm CX1) as MSGW;
      name_sp sp (-64)%Z;
      eapply evtF_cut;
      [ eapply (strlen_icpt_spec RNG) with (lo := lo) (str := errmsg) (slack := [Z_to_bv 8 0]) (RLO := 0x24480) (RHI := 0x24500);
        cbv zeta; rewrite ?Hsp; rewrite ?unsigned_lit by lia; rewrite ?length_app, ?errmsg_len; cbn [length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
        first [ exact MSGB | exact MSGU | exact MSGW | exact errmsg_nonul | exact RI | eassumption
              | (unfold KHIGH; clear - LOA ATR; lia)
              | (left; clear - LOA ATR; lia)
              | (unfold app_blk, KLOW, KHIGH, KEND; clear; lia)
              | (unfold KEND; clear; repeat split; lia)
              | (eapply rng_sub'; [exact RSTK| clear - LOS LOA STOP LO0; lia])
              | (eapply rng_sub'; [exact RI| clear; lia])
              | (rewrite !shad_div; unfold ASHOFF; eapply rng_sub'; [exact RISH| clear; lia])
              | (clear; Z.div_mod_to_equations; lia)
              | lia ]
      | cbv beta; unfold strlen_i_post; rewrite ?Hsp; rewrite ?unsigned_lit by lia; rewrite ?errmsg_zlen; clear MSGB MSGU MSGW; post_call asegs mm ]
      end end.
    all: rewrite ?unsigned_lit in * by lia.
    try unname_sp.
    (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K;
            [exfalso; rewrite ?unsigned_lit in K by lia; rewrite ?unsigned_lit_wrap in K; clear - K; Z.div_mod_to_equations; lia| clear K]).   (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K; lia]).   (* [comment removed for export] *)
    zstep. fold_lits.                       (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K; lia]).   (* [comment removed for export] *)
    zstep. fold_lits.                       (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MUx : munch _ m mx, WMx : wmono asegs m mx |- _ =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx) by (eapply AHEAP_stack_frame; [exact AH| exact MUx| exact WMx| repeat constructor; cbn; lia]);
      pose proof (aheap_pres_x_of_munch CI LB (bv_unsigned sp) T 24 _ m mx MUx WMx) as HPX1;
      assert (CXq : client_x mx)
        by (eapply client_x_munch_gen; [exact CX| exact MUx| exact WMx| unfold AMSG_SH; cbn [disjoint_from]; clear - LOA ATR; lia| unfold AJT_SH; cbn [disjoint_from]; clear - LOA ATR; lia| unfold AREAL_STRLEN; cbn [disjoint_from]; clear - LOA ATR; lia]);
      box MUx; box WMx
      end end.
    lazymatch type of HPX1 with ?PREM -> _ =>
      assert (OUT1 : PREM)
        by (intros a Ha Hc Hx; cbn [outside]; pose proof (aclient_lo_or_sp AI _ _ _ _ LB _ _ a AH ltac:(intros b Hb; exact Hb) Hc); clear - H Hx LOA; lia);
      specialize (HPX1 OUT1); clear OUT1 end.
    name_sp sp (-64)%Z.
    eapply implMA_post_evtF.
    { eapply ONTA with (lo := lo); try reflexivity; rewrite ?Hsp; rewrite ?unsigned_lit by lia;
        first [exact AH1 | exact TP | exact HU | exact AOK | eassumption
              | (unfold OPNEW_STACK_A, AMALLOC_STACK; clear - LOS; lia) | (unfold ERRSTR_BYTES, AREQMAX; clear; lia) | (clear - STOP; lia)
              | (clear - SP16 RSP LOS LOA ATR; Z.div_mod_to_equations; lia)
              | (eapply rng_sub'; [exact RSTK| clear - LOS LOA STOP LO0; lia]) | lia]. }
    cbv beta. intros p s' RNG' ms1 PO.
    destruct PO as (FLE & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mq1 & A & bjk & -> & MI1 & ST1 & HPR1 & ARS1 & BR & AH2 & BLK & RA & RSA).
    rewrite ?Hsp in ST1, HPR1. rewrite ?unsigned_lit in ST1, HPR1 by lia.
    unname_sp. retlit. change ERRSTR_BYTES with 56 in *. change (Z.to_nat 56) with 56%nat in BLK. change (shlen (56 + 7)) with 7 in RSA.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs ?mo (bv_unsigned sp + -64) ?cs |- _ =>
      assert (FR1 : rw_cells asegs mq1 (bv_unsigned sp + -64) cs) by (eapply aheap_pres_rw_cells; [exact HPR1| exact FRx| apply aclient_range_stack; cbn; lia]); clear FRx end.
    assert (VEC1 : rw_cells asegs mq1 T [C8 v0; C8 v1; C8 v2])
      by (eapply aheap_pres_rw_cells; [exact HPR1| exact VEC| eapply aclient_range_fake; [exact FIN| lia| cbn; lia]]).
    assert (VSH1 : rw_cells asegs mq1 (shad T) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
    { eapply aheap_pres_rw_cells; [exact HPR1| exact VSH|]. right; right. right; right. exists cls, FA, FN. split; [exact FIN|].
      rewrite shad_div. unfold ASHOFF. cbn [cells_size csize Nat.add]. clear - V8 FV1 FV2. Z.div_mod_to_equations. lia. }
    pose proof (client_x_pres AI IMG_CI _ _ _ _ HPR1 CXq) as CX2. clear CXq CX1.
    pose proof (aheap_pres_x_of_pres CI LB LB (bv_unsigned sp) (bv_unsigned sp + -64) T 24 _ _ HPR1 ltac:(lia) ltac:(intros b Hb; exact Hb)) as HPXv.
    clear VEC VSH AH1 GOT RIC REAL SHB INI LAY ISL HPR1. try clear MI. try clear RSL.
    repeat match goal with H : rw_cells asegs ?mo _ _ |- _ => lazymatch mo with mq1 => fail | _ => clear H end end.
    repeat match goal with H : stk asegs ?mo _ _ |- _ => lazymatch mo with mq1 => fail | _ => clear H end end.
    repeat match goal with H : mem_inv asegs ?mo |- _ => lazymatch mo with mq1 => fail | _ => clear H end end.
    repeat match goal with H : bytes_at asegs ?mo _ _ |- _ => lazymatch mo with mq1 => fail | _ => clear H end end.
    pose proof (rng_fp_le _ _ _ _ FLE RSTK) as RSTK1. pose proof (rng_fp_le _ _ _ _ FLE RV) as RV1. pose proof (rng_fp_le _ _ _ _ FLE RVS) as RVS1.
    pose proof (rng_fp_le _ _ _ _ FLE RI) as RI1. pose proof (rng_fp_le _ _ _ _ FLE RISH) as RISH1.
    pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
    assert (AL : A mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
    assert (ANS : A + 56 <= 0x7fff7000 \/ 0x10007fff8000 <= A) by (unfold ablk, AIMG_HI, KLS in BR1; clear - BR1; lia).
    (* [comment removed for export] *)
    pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH2 FIN) as DJ1. cbn [ab_addr ab_size] in DJ1.
    assert (SHA : shad A = Z.shiftr A 3 + 2147450880) by (unfold shad, ASHOFF; lia).
    assert (SHA54 : Z.shiftr (A + 54) 3 + 2147450880 = shad A + 6) by (rewrite SHA, !Z.shiftr_div_pow2 by lia; clear - AL; Z.div_mod_to_equations; lia).
    assert (SHAB : 0x7fff8000 <= shad A /\ shad A + 7 <= 0x10007fff8000) by (rewrite SHA, Z.shiftr_div_pow2 by lia; clear - BL1 BL3 ATR; Z.div_mod_to_equations; lia).
    assert (SHDJ : shad T + 3 <= shad A \/ shad A + 7 <= shad T)
      by (unfold bxs in SHV; rewrite SHV, SHA; rewrite !Z.shiftr_div_pow2 by lia; clear - DJ1 FV1 FV2 V8 AL; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    assert (ADJV : shad T + 3 <= A \/ A + 56 <= shad T) by (clear - ANS SHVB; lia).
    assert (ADJA : shad A + 7 <= A \/ A + 56 <= shad A) by (clear - ANS SHAB; lia).
    box SHA; box SHA54.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH2) as (GOT1 & RIC1 & REAL1 & SHB1 & _ & INI1 & LAY1).
    assert (ACC0 : rng RNG' (Z.shiftr T 3 + 2147450880) 1) by (unfold bxs in SHV; rewrite <- SHV; eapply rng_sub'; [exact RVS1| lia]).
    assert (ACC1 : rng RNG' (Z.shiftr (T + 8) 3 + 2147450880) 1) by (unfold bxs in SHV8; rewrite SHV8; eapply rng_sub'; [exact RVS1| lia]).
    assert (ACC2 : rng RNG' (Z.shiftr (T + 16) 3 + 2147450880) 1) by (unfold bxs in SHV16; rewrite SHV16; eapply rng_sub'; [exact RVS1| lia]).
    assert (ACCB : rng RNG' (Z.shiftr (A + 54) 3 + 2147450880) 1) by (unfold bxs in SHA54; rewrite SHA54; eapply rng_sub'; [exact RSA| clear; lia]).
    (* [comment removed for export] *)
    assert (LJ : length bjk = 56%nat) by (destruct BLK as [[WF _] _]; cbn in WF; clear - WF; tauto).
    assert (BLK2 : rw_cells asegs mq1 A [CB 54 (firstn 54 bjk); CB 2 (skipn 54 bjk)])
      by (eapply rw_cells_recast; [exact BLK| cbn; rewrite firstn_length_le, skipn_length by lia; clear - LJ; split; [lia| split; [lia| exact I]]
                                 | cbn [cells_bytes cbytes app]; rewrite !app_nil_r, firstn_skipn; reflexivity| cbn; clear; lia]).
    apply (rw_cells_app_split asegs mq1 A [CB 54 (firstn 54 bjk)] [CB 2 (skipn 54 bjk)]) in BLK2 as [BLKa BLKt]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BLKt. clear BLK.
    destruct (skipn 54 bjk) as [|j54 [|j55 [|jx jl]]] eqn:EJ;
      [exfalso; apply (f_equal (@length byte)) in EJ; rewrite skipn_length, LJ in EJ; cbn in EJ; lia
      |exfalso; apply (f_equal (@length byte)) in EJ; rewrite skipn_length, LJ in EJ; cbn in EJ; lia| 
      |exfalso; apply (f_equal (@length byte)) in EJ; rewrite skipn_length, LJ in EJ; cbn in EJ; lia].
    assert (BLKt2 : rw_cells asegs mq1 (A + 54) [C1 j54; C1 j55])
      by (eapply rw_cells_recast; [exact BLKt| cbn; repeat split; exact I| reflexivity| reflexivity]).
    clear BLKt EJ.
    pose proof (munch_refl [(lo, bv_unsigned sp); (T, T + 24); (A, A + 56)] mq1) as MU1. pose proof (wmono_refl asegs mq1) as WM1.
    (* [comment removed for export] *)
    pose_hr 2 SHV16.
    zstep. zstep. zstep. astep. astep.      (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    pose_hr0 SHV.
    zstep. zstep. astep. astep.             (* [comment removed for export] *)
    zstep. fold_lits.                       (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    pose_hr 1 SHV8.
    zstep. zstep. astep. astep.             (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with BLKx : rw_cells asegs mm A [CB 54 _], MIx : mem_inv asegs mm, MUx : munch _ mq1 mm, WMx : wmono asegs mq1 mm |- _ =>
      assert (AH3 : AHEAP AI L RNG' (aps_m s') (HB p A 56 :: LB) mm)
        by (eapply (AI_frame AI); [exact AH2| exact MUx| exact WMx|];
            constructor; [apply aclient_range_stack; cbn; clear - LOA STOP LY3; lia|];
            constructor; [eapply aclient_range_fake; [right; exact FIN| cbn; lia| cbn; lia]|];
            constructor; [right; left; exists (HB p A 56); split; [left; reflexivity| cbn; lia]| constructor]);
      destruct (blk_window_facts AI _ _ _ _ _ _ _ _ A 54 AH3 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(lia)) as (APPb & UNPb & RWb & (RLOb & RHIb & HUb & WHb & RHb));
      assert (CX3 : client_x mm)
        by (eapply client_x_munch_gen; [exact CX2| exact MUx| exact WMx| unfold AMSG_SH; cbn [disjoint_from]; clear - LOA ATR VNS ANS; lia| unfold AJT_SH; cbn [disjoint_from]; clear - LOA ATR VNS ANS; lia| unfold AREAL_STRLEN; cbn [disjoint_from]; clear - LOA ATR VNS ANS VLO BL1; lia]);
      pose proof (errmsg_bytes_at54 mm MIx) as MSGB; unfold AERRMSG in MSGB;
      pose proof (unpoisoned_sub _ _ _ 148640 (148640 + 54) (errmsg_unpoisoned mm CX3) ltac:(unfold AERRMSG; lia) ltac:(unfold AERRMSG; lia)) as MSGU;
      pose proof (errmsg_hull_wr_at mm CX3) as MSGW;
      name_sp sp (-64)%Z;
      eapply evtF_cut;
      [ eapply (asan_memmove_spec RNG') with (lo := lo) (src := errmsg) (RLO1 := 0x24480) (RHI1 := 0x24500) (RLO2 := RLOb) (RHI2 := RHIb);
        rewrite ?Hsp; rewrite ?unsigned_lit by lia; change (Z.to_nat 54) with 54%nat;
        first [ exact BLKx | exact MSGB | exact MSGU | exact MSGW | exact APPb | exact UNPb | exact RWb | exact HUb | exact WHb | exact RHb | exact RI1 | exact errmsg_len | eassumption
              | (unfold KHIGH; clear - LOA ATR; lia)
              | (left; clear - BL1; lia)
              | (left; clear - LOA ATR; lia)
              | (left; clear - BL3 LOA ATR; lia)
              | (unfold app_blk, KLOW, KHIGH, KEND; clear; lia)
              | (unfold KEND; clear; repeat split; lia)
              | (eapply rng_sub'; [exact RSTK1| clear - LOS LOA STOP LO0; lia])
              | (eapply rng_sub'; [exact RI1| clear; lia])
              | (rewrite !shad_div; unfold ASHOFF; eapply rng_sub'; [exact RISH1| clear; lia])
              | (clear; lia) | lia ]
      | cbv beta; unfold asan_memmove_post; rewrite ?Hsp; rewrite ?unsigned_lit by lia; change (Z.to_nat 54) with 54%nat;
        clear APPb UNPb RWb HUb WHb RHb MSGB MSGU MSGW; post_call asegs mm ]
      end end.
    all: rewrite ?unsigned_lit in * by lia.
    try unname_sp.
    (* [comment removed for export] *)
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_introl eq_refl)) as (_ & _ & _ & _ & BSH & _ & _ & _).
    pose proof (cells_of_ablock_shadow mq1 A 56 ltac:(lia) ltac:(lia) ltac:(lia) BSH) as FULL1.
    change (Z.to_nat (granules 56)) with 7%nat in FULL1. change (block_shadow_bytes 56) with (repeat (Z_to_bv 8 0) 7) in FULL1.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with MUx : munch _ mq1 mm, WMx : wmono asegs mq1 mm |- _ =>
      assert (FULL4 : rw_cells asegs mm (shad A) [CB 7 (repeat (Z_to_bv 8 0) 7)])
        by (eapply rw_cells_transport; [exact FULL1| exact MUx| exact WMx| cbn [disjoint_from cells_size csize Nat.add]; clear - SHAB LOA ATR VNS ADJA; lia]);
      assert (HRB0 : mm (wa (shad A + 6)) = Some (Z_to_bv 8 0)) by (pose proof (CB_pointwise mm (shad A) 7 _ 6 FULL4 ltac:(clear - SHAB; lia) ltac:(lia)) as Q; exact Q);
      pose proof (ov_read1_of_byte asegs mm (shad A + 6) (Z_to_bv 8 0) ltac:(clear - SHAB; lia) ltac:(clear - SHAB; lia) HRB0) as HRB;
      unfold bxs in SHA54; rewrite <- SHA54 in HRB; box SHA54; clear HRB0
      end end.
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep. astep. astep.             (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.      (* [comment removed for export] *)
    lazymatch goal with H : stk asegs _ lo _ |- _ => release_frame FR1 H (bv_unsigned sp) end.
    zstep.                                  (* [comment removed for export] *)
    apply evtF_done. unfold astrctor_post. split; [exact FLE|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
      lazymatch goal with MUq : munch [(lo, _); (T, _); (A, _)] mq1 mm, WMq : wmono asegs mq1 mm, VECx : rw_cells asegs mm T _, VSHx : rw_cells asegs mm (shad T) _,
                          BA : rw_cells asegs mm A [CB 54 _], BT : rw_cells asegs mm (A + 54) _, MIx : mem_inv asegs mm, STx : stk asegs mm lo (bv_unsigned sp) |- _ =>
        rename MUq into MUe; rename WMq into WMe; rename VECx into VECe; rename VSHx into VSHe; rename BA into BAe; rename BT into BTe; rename MIx into MIe; rename STx into STe;
        rename mm into me end end.
    assert (AH5 : AHEAP AI L RNG' (aps_m s') (HB p A 56 :: LB) me).
    { eapply (AI_frame AI); [exact AH2| exact MUe| exact WMe|].
      constructor; [apply aclient_range_stack; cbn; clear - LOA STOP LY3; lia|].
      constructor; [eapply aclient_range_fake; [right; exact FIN| cbn; lia| cbn; lia]|].
      constructor; [right; left; exists (HB p A 56); split; [left; reflexivity| cbn; lia]| constructor]. }
    do 15 eexists. exists me, A, j55. split; [reflexivity|].
    split; [exact MIe|]. split; [exact STe|]. split; [exact ARS1|]. split; [exact BR|].
    split.
    { eapply aheap_pres_x_trans; [exact HPX1|]. eapply aheap_pres_x_trans; [exact HPXv|].
      eapply aheap_pres_x_of_munch; [exact MUe| exact WMe|].
      intros a Ha Hc Hx. cbn [outside].
      pose proof (aclient_lo_or_sp AI _ _ _ _ LB _ _ a AH2 ltac:(intros b Hb; right; exact Hb) Hc) as Y1.
      assert (HSP0 : ATOP <= bv_unsigned sp) by (clear - LOA LOS; lia).
      pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ _ a AH2 HSP0 Hc) as Y2.
      clear - Y1 Y2 Hx LOA LOS. lia. }
    split; [exact AH5|]. split; [exact VECe|]. split; [exact VSHe|].
    split.
    { pose proof (rw_cells_app_join asegs me A [CB 54 errmsg] _ BAe ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; exact BTe)) as J. exact J. }
    split; [exact RA| exact RSA].
  Qed.
End Proof.
End S.
End CANSEC1.
