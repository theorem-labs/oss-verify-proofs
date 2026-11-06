(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Img0 Img0 V_Co10c V_Leaves.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_memset.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_WSwg5.

Module V_WSd07.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Img0 Img0 V_Co10c V_Leaves.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import R_memset V_WSwg5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

Definition ws_emu_alloc_entry : Z := 0x18cf0.
(* [comment removed for export] *)
Definition WSEMU_STACK : Z := 64 + CALLOC_STACK.

(* [comment removed for export] *)
Definition ws_changed (H : henv) (a : Z) : Prop :=
  h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  Lemma ws_emu_alloc_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (H : henv) (lo : Z) (T : TSet),
      ainv A m md -> mem_inv rsegs m -> (exists r k, a_live A r = Some k) ->
      a0 = Z_to_bv 64 (h_ws H) -> a1 = Z_to_bv 64 312 ->
      ws0_obj LayoutP0 H m -> glob_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      a_livebytes A + 352 <= LIVE_MAX -> a_nlive A + 2 <= NLIVE_MAX ->
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + WSEMU_STACK <= bv_unsigned sp ->
      bv_unsigned sp <= h_sp H ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> glob_ok LayoutP0 VI0 H m' ->
          (* [comment removed for export] *)
              (exists vep junk, r <> 0 /\ ws1_obj LayoutP0 H A' m' r vep /\ rw_cells rsegs m' vep [CB 312 junk] /\
               a_live A r = None /\ a_live A vep = None /\
               (forall p, p <> r -> p <> vep -> a_live A' p = a_live A p) /\
               a_livebytes A' = a_livebytes A + 352 /\ a_nlive A' = a_nlive A + 2 /\
               cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) WSEMU_STACK
                      (fun a => h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32)
                      (fun a => blk r 40 a \/ blk vep 312 a) m m') ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 ws_emu_alloc_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. intros AINV MI LIVEX Ha0 Ha1 WS0 GLOB HG IMG LBUD NBUD TP SP16 RA2 ST CEIL LO SPH K.
    rewrite Ha0, Ha1.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutP0)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY.
    pose proof alloc_ceiling_val as ACV.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G16 GCE GHI | pose proof HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    assert (Ebss : h_bss H = 0x41830) by (destruct GLOB as [E _]; rewrite E; reflexivity).
    pose proof IMG as IMG0. (first [ dand5 IMG as _ GMS _ GCP _ | destruct IMG as (_ & GMS & _ & GCP & _) ]). unfold GOT_cp in GCP. unfold GOT_memset in GMS.
    unfold WSEMU_STACK, CALLOC_STACK in *. unfold ws_emu_alloc_entry.
    rewrite Ews.
    (* [comment removed for export] *)
    (first [ dex1 WS0 as id; dand3 WS0 as IDOK WSC WEC | dand4 WS0 as id IDOK WSC WEC | destruct WS0 as (id & IDOK & WSC & WEC) ]). cbn [al_segs LayoutP0] in WSC, WEC.
    assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
    unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
    unfold wsemu_cells, wsemu_WS0 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
    rewrite Ews in WSC. rewrite Ewb in WSC, WEC.
    (* [comment removed for export] *)
    assert (WS0P : forall mq,
      rw_cells rsegs mq (h_sp H + 1080) [C4 (Z_to_bv 64 WS_MAGIC); CB 4 id; C8 (Z_to_bv 64 (h_sp H + 16)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_sp H + 16 + 1016))] ->
      rw_cells rsegs mq (h_sp H + 16) [C4 (Z_to_bv 64 WS_EMU_MAGIC); C4 (Z_to_bv 64 1016); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_sp H + 32))] ->
      ws0_obj LayoutP0 H mq).
    { intros mq X1 X2. apply (ws0_obj_intro LayoutP0 H mq id IDOK); cbn [al_segs LayoutP0]; rewrite ?Ews, ?Ewb; [exact X1|].
      unfold wsemu_cells, wsemu_WS0. cbn [we_len we_ws we_first we_last]. replace (h_sp H + 16 + 16) with (h_sp H + 32) by lia. exact X2. }
    replace (h_sp H + 16 + 16) with (h_sp H + 32) in WEC by lia.
    assert (GLOBP : forall W mp mq, glob_ok LayoutP0 VI0 H mp -> munch W mp mq -> wmono rsegs mp mq ->
      (forall a, (0x41830 <= a < 0x41830 + 16 \/ h_sp H + 1488 <= a < h_sp H + 1488 + 752 \/ h_sp H + 2240 + 1304 <= a < h_sp H + 2240 + 1320) -> outside W a) ->
      glob_ok LayoutP0 VI0 H mq).
    { intros W mp mq G MUx WMx OUT. eapply (glob_ok_munch LayoutP0); [exact G| exact MUx| exact WMx|].
      intros a Ha. apply OUT. rewrite Ebss in Ha. unfold h_cp, h_vsc in Ha. exact Ha. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8288, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 8288, bv_unsigned sp)]).
    { cbn. split; [left; lia| exact I]. }
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    do 6 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    call_lit (WS_Assert_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H None lo) by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- ws_state _ _ _ => cbn [ws_state]; apply WS0P; assumption
      | |- glob_ok _ _ _ _ => eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
      | |- henv_geom _ => exact HG
      | |- img_ok0 _ => eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG0]
      | |- mem_inv _ _ => assumption
      | |- @eq word _ _ => rewrite ?Ews; reflexivity
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    zstep. zstep.
    call_lit (ws_emu_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h_sp H + 1080)
              (WSR id (h_sp H + 16) 0 0 (h_sp H + 16 + 1016)) (WER 1016 0 0 (h_sp H + 32)) lo) by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- rw_cells _ _ _ (ws_cells _) => exact WSC
      | |- rw_cells _ _ _ (wsemu_cells _) => exact WEC
      | |- length _ = _ => exact IDL
      | |- mem_inv _ _ => assumption
      | |- @eq word _ _ => reflexivity
      | |- _ => cbn [ws_s]; rewrite ?unsigned_lit by lia; lia
      end).
    match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST. cbn [ws_s].
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. zstep. zstep. if_cases K1; zify_cond K1. 2:{ kill K1. } clear K1.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ kill K2. } clear K2.
    zstep. if_cases K3; zify_cond K3. 2:{ kill K3. } clear K3.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    apply rz_stop.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (ainv_munch LayoutP0 A m mx md _ AINV MU WM CFP) as AINV1;
      pose_cranges LayoutP0 A mx AINV1 end.
    eapply (as_calloc_cps (L:=LayoutP0)) with (cnt := 1) (sz := 40);
      [ exact AINV1 | assumption | exact LIVEX | reflexivity | reflexivity | lia | lia | lia | lia | lia | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; unfold CALLOC_STACK; lia
      | rewrite unsigned_lit by lia; eapply (stk_mapped (L:=LayoutP0)); [exact ST| exact CEIL | unfold CALLOC_STACK; lia | lia]
      | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' wa A1 m1 md1 AINV' MI' MDF OUT FRK.
    pose proof (as_lazy_nil A1 m1 md1 AINV') as [MDL' MDH'].
    rewrite unsigned_lit in FRK by lia.
    (* [comment removed for export] *)
    lazymatch type of FRK with frame_ok _ _ _ _ _ _ _ ?mx _ =>
      assert (GLOB1 : glob_ok LayoutP0 VI0 H m1)
        by (eapply (glob_ok_ccall LayoutP0 VI0 H A A1 mx md m1); [exact AINV1| apply (cframe_of_frame_ok LayoutP0); exact FRK| exact HG
            | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
            | lia| unfold CALLOC_STACK; lia
            | rewrite Ebss; cbn; lia| rewrite Ebss; cbn; lia
            | intros i Hi; rewrite Ebss; cbn; unfold p0_static; lia
            | rewrite Ebss; cbn; change (al_errno LayoutP0) with 0x420b4; lia
            | intros a _ X; exact X]);
      assert (IMG1 : img_ok0 m1)
        by (eapply (img_ok0_ccall A A1 mx md m1); [exact AINV1| apply (cframe_of_frame_ok LayoutP0); exact FRK
            | unfold IMG0_HI, CALLOC_STACK; lia| intros a _ X; exact X
            | eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG0]])
    end.
    clear GCP GMS.
    destruct OUT as (NZ & FRESH & LIVEwa & LIVEq & ZERO & LB1 & NL1).
    - (* [comment removed for export] *)
      change (1 * 40) with 40 in LB1.
      change (1 * 40) with 40 in LIVEwa, ZERO, FRK.
      acall_xfer FRK. clear AINV1.
      (first [ pose proof ((as_live_ok A1 m1 md1 wa _ AINV' LIVEwa)) as dR_4; dand7 dR_4 as _ WA16 WAlo WAhi WAimg WAmap WAown | pose proof (as_live_ok A1 m1 md1 wa _ AINV' LIVEwa) as (_ & WA16 & WAlo & WAhi & WAimg & WAmap & WAown) ]).
      assert (WAbss : wa + 40 <= 0x10000 \/ 0x63000 <= wa) by (unfold in_image in WAimg; cbn [al_image_lo al_image_hi LayoutP0] in WAimg; lia).
      clear WAimg.
      (first [ pose proof ((newblock_cells (L:=LayoutP0) A1 m1 md1 wa _ AINV' LIVEwa)) as dR_5; dex1 dR_5 as junk1; dand3 dR_5 as LJ1 NB1 CRwa | pose proof ((newblock_cells (L:=LayoutP0) A1 m1 md1 wa _ AINV' LIVEwa)) as dR_5; dand4 dR_5 as junk1 LJ1 NB1 CRwa | destruct (newblock_cells (L:=LayoutP0) A1 m1 md1 wa _ AINV' LIVEwa) as (junk1 & LJ1 & NB1 & CRwa) ]).
      cbn [al_segs LayoutP0] in NB1.
      pose proof (all_zero_CB rsegs m1 wa _ junk1 NB1 ZERO) as EJ. change (Z.to_nat 40) with 40%nat in EJ. subst junk1.
      apply (rw_cells_recast rsegs m1 wa _
               [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0];
                C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in NB1; [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity | reflexivity].
      pose proof (munch_refl [(bv_unsigned sp - 8288, bv_unsigned sp); (wa, wa + 40)] m1) as MU2.
      pose proof (wmono_refl rsegs m1) as WM2.
      assert (CFP2 : client_fp LayoutP0 A1 [(bv_unsigned sp - 8288, bv_unsigned sp); (wa, wa + 40)]).
      { cbn. split; [left; lia|]. split; [right; left; exists wa, 40; split; [exact LIVEwa|lia]| exact I]. }
      rz_resume MDH' MDL'.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
      zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KL; zify_cond KL. { kill KL. } clear KL.
      zstep. zstep. zstep.
      apply rz_stop.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        pose proof (ainv_munch LayoutP0 A1 m1 mx md1 _ AINV' MU2 WM2 CFP2) as AINV2;
        pose_cranges LayoutP0 A1 mx AINV2 end.
      eapply (as_malloc_cps (L:=LayoutP0)) with (n := 312);
        [ exact AINV2 | assumption | exists wa, 40; exact LIVEwa | reflexivity | lia | rewrite NREQ_CAP_eq; lia | lia | lia | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; unfold MALLOC_STACK; lia
        | rewrite unsigned_lit by lia; eapply (stk_mapped (L:=LayoutP0)); [exact ST| exact CEIL | unfold MALLOC_STACK; lia | lia]
        | ].
      intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' vep A2 m3 md3 AINV3 MI3 MDF3 OUT2 FRK2.
      pose proof (as_lazy_nil A2 m3 md3 AINV3) as [MDL3 MDH3].
      rewrite unsigned_lit in FRK2 by lia.
      (* [comment removed for export] *)
      lazymatch type of MU2 with munch _ _ ?mx =>
        assert (CFa : cframe LayoutP0 (owned A) (owned A1) (bv_unsigned sp) 8288 nowhere (blk wa 40) m mx)
          by (eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m _ m1 _ _ _);
              [ exact MU | | exact FRK | unfold CALLOC_STACK; lia | lia | intros a X; destruct X | intros a X; left; exact X
              | exact MU2 | | eapply (window_mapped LayoutP0 _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia] ];
              [ intros a Ha NO; cbn [outside] in NO; lia
              | intros a Ha NO; cbn [outside] in NO; unfold blk; lia ]);
        assert (GLOB2 : glob_ok LayoutP0 VI0 H m3)
          by (eapply (glob_ok_ccall LayoutP0 VI0 H A1 A2 mx md1 m3); [exact AINV2| apply (cframe_of_frame_ok LayoutP0); exact FRK2| exact HG
              | eapply GLOBP; [exact GLOB1| exact MU2| exact WM2| intros a Ha; cbn [outside]; lia]
              | lia| unfold MALLOC_STACK; lia
              | rewrite Ebss; cbn; lia| rewrite Ebss; cbn; lia
              | intros i Hi; rewrite Ebss; cbn; unfold p0_static; lia
              | rewrite Ebss; cbn; change (al_errno LayoutP0) with 0x420b4; lia
              | intros a _ X; exact X]);
        assert (IMG2 : img_ok0 m3)
          by (eapply (img_ok0_ccall A1 A2 mx md1 m3); [exact AINV2| apply (cframe_of_frame_ok LayoutP0); exact FRK2
              | unfold IMG0_HI, MALLOC_STACK; lia| intros a _ X; exact X
              | eapply (img_ok0_munch _ m1); [exact MU2| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG1]])
      end.
      clear MU MU2 WM WM2 CFP CFP2 FRK.
      destruct OUT2 as (NZv & FRESHv & LIVEv & LIVEq3 & LB2 & NL2).
      + (* [comment removed for export] *)
        acall_xfer FRK2. clear AINV2.
        assert (NEwv : wa <> vep) by (intros ->; rewrite FRESHv in LIVEwa; discriminate LIVEwa).
        assert (LIVEwa3 : a_live A2 wa = Some 40) by (rewrite (LIVEq3 wa NEwv); exact LIVEwa).
        (first [ pose proof ((as_live_ok A2 m3 md3 vep _ AINV3 LIVEv)) as dR_7; dand7 dR_7 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A2 m3 md3 vep _ AINV3 LIVEv) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]). clear VEPimg.
        (first [ pose proof ((newblock_cells (L:=LayoutP0) A2 m3 md3 vep _ AINV3 LIVEv)) as dR_8; dex1 dR_8 as junkv; dand3 dR_8 as LJv NBv CRv | pose proof ((newblock_cells (L:=LayoutP0) A2 m3 md3 vep _ AINV3 LIVEv)) as dR_8; dand4 dR_8 as junkv LJv NBv CRv | destruct (newblock_cells (L:=LayoutP0) A2 m3 md3 vep _ AINV3 LIVEv) as (junkv & LJv & NBv & CRv) ]).
        cbn [al_segs LayoutP0] in NBv. change (Z.to_nat 312) with 312%nat in NBv, LJv.
        pose proof (as_live_disjoint A2 m3 md3 wa 40 vep 312 AINV3 LIVEwa3 LIVEv NEwv) as DJ.
        pose proof (munch_refl [(bv_unsigned sp - 8288, bv_unsigned sp); (wa, wa + 40); (h_sp H + 16, h_sp H + 16 + 32)] m3) as MU3.
        pose proof (wmono_refl rsegs m3) as WM3.
        assert (CFP3 : client_fp LayoutP0 A2 [(bv_unsigned sp - 8288, bv_unsigned sp); (wa, wa + 40); (h_sp H + 16, h_sp H + 16 + 32)]).
        { cbn. split; [left; lia|]. split; [right; left; exists wa, 40; split; [exact LIVEwa3|lia]|]. split; [left; lia| exact I]. }
        rz_resume MDH3 MDL3.
        (* [comment removed for export] *)
        zstep. zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. do 5 zstep. zstep. zstep.
        try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
        release_frame FR ST (bv_unsigned sp).
        cps_done.
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          lazymatch type of MU3 with munch ?W _ _ =>
            pose proof (ainv_munch LayoutP0 A2 m3 mx md3 W AINV3 MU3 WM3 CFP3) as AINV9 end end.
        eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ wa A2 _ md3);
          [ exact AINV9 | assumption | eapply md_frame_trans; [exact MDF| exact MDF3] | exact ST
          | eapply GLOBP; [exact GLOB2| exact MU3| exact WM3| intros a Ha; cbn [outside]; lia] | ].
        exists vep, junkv. split; [exact NZ|].
        split.
        { apply (ws1_obj_intro LayoutP0 H A2 _ wa vep id (repeat (Z_to_bv 8 0) 4) IDOK eq_refl); cbn [al_segs LayoutP0].
          - exact WSC.
          - unfold wsemu_cells, wsemu_WS1. cbn [we_len we_ws we_first we_last]. rewrite Ewb. exact WEC.
          - exact LIVEwa3.
          - unfold wsalloc_cells, wsalloc_WS1. cbn [wa_off wa_len wa_ptr wa_next wa_prev repeat]. rewrite Ewb.
            replace (h_sp H + 16 + 16) with (h_sp H + 32) by lia. exact NB1.
          - exact LIVEv. }
        split; [exact NBv|]. split; [exact FRESH|]. split; [rewrite <- (LIVEq vep (fun E => NEwv (eq_sym E))); exact FRESHv|].
        split; [intros p P1 P2; rewrite (LIVEq3 p P2); apply LIVEq; exact P1|].
        split; [lia|]. split; [lia|].
        lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?mfin =>
          assert (CF2 : cframe LayoutP0 (owned A1) (owned A2) (bv_unsigned sp) 8288 (fun a => blk wa 40 a \/ ws_changed H a) (blk vep 312) m0 mfin)
            by (eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m0 m0 m3 _ [] _);
                [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK2 | unfold MALLOC_STACK; lia | lia
                | intros a X; destruct X | intros a X; left; exact X | exact MU3 |
                | eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | lia | lia] ];
                intros a Ha NO; cbn [outside] in NO; unfold ws_changed, h_ws, h_wsbuf, blk; lia);
          eapply (cframe_seq LayoutP0 _ _ _ _ _ _ _ _ _ _ _ _ _ m m0 mfin CFa CF2); [lia | lia
            | eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | lia | lia]
            | intros a X; destruct X | intros a [X|X]; [left; exact X| right; unfold ws_changed in X; exact X]
            | intros a [X|X]; [left; exact X| right; left; exact X] ]
        end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma WS_Alloc_ok : WS_Alloc_stmt.
  Proof.
    unfold WS_Alloc_stmt.
    intros H lo. intros until T. intros AINV MI LIVEX Ha0 Ha1 WS0 GLOB HG IMG LBUD NBUD TP SP16 RA2 ST CEIL LO SPH K.
    rewrite Ha0, Ha1.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutP0)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY.
    pose proof alloc_ceiling_val as ACV.
    (first [ pose proof (HG) as dR_9; dand3 dR_9 as G16 GCE GHI | pose proof HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    assert (Ebss : h_bss H = 0x41830) by (destruct GLOB as [E _]; rewrite E; reflexivity).
    unfold WSALLOC_STACK, CALLOC_STACK in *. unfold WS_Alloc_entry.
    assert (GLOBP : forall W mp mq, glob_ok LayoutP0 VI0 H mp -> munch W mp mq -> wmono rsegs mp mq ->
      (forall a, (0x41830 <= a < 0x41830 + 16 \/ h_sp H + 1488 <= a < h_sp H + 1488 + 752 \/ h_sp H + 2240 + 1304 <= a < h_sp H + 2240 + 1320) -> outside W a) ->
      glob_ok LayoutP0 VI0 H mq).
    { intros W mp mq G MUx WMx OUT. eapply (glob_ok_munch LayoutP0); [exact G| exact MUx| exact WMx|].
      intros a Ha. apply OUT. rewrite Ebss in Ha. unfold h_cp, h_vsc in Ha. exact Ha. }
    pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 8320, bv_unsigned sp)]).
    { cbn. split; [left; lia| exact I]. }
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 32%nat ST.
    do 5 zstep.
    (* [comment removed for export] *)
    zstep. if_cases KB; zify_cond KB. { kill KB. } clear KB.
    zstep. zstep. zstep.
    apply rz_stop.
    pose proof (ainv_munch LayoutP0 A m _ md _ AINV MU WM CFP) as AINV1.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (crange_stack (L:=LayoutP0) A mx md (bv_unsigned sp - 32) 32 AINV1 ltac:(lia) ltac:(lia)
                    (rw_cells_mapped LayoutP0 mx _ _ FR ltac:(off_image_solve LayoutP0))) as CF end.
    eapply ws_emu_alloc_cps;
      [ exact AINV1 | assumption | exact LIVEX | rewrite Ews; reflexivity | reflexivity
      | eapply (ws0_obj_munch LayoutP0); [exact WS0| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]
      | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
      | exact HG
      | eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG]
      | exact LBUD | exact NBUD
      | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; exact ST | exact CEIL
      | rewrite unsigned_lit by lia; unfold WSEMU_STACK, CALLOC_STACK; lia
      | rewrite unsigned_lit by lia; lia | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' AINV' MI' MDF ST' GLOB' OUT.
    pose proof (as_lazy_nil A' m' md' AINV') as [MDL' MDH'].
    rewrite unsigned_lit in OUT, ST' by lia. unfold WSEMU_STACK, CALLOC_STACK in OUT.
    destruct OUT as (vep & junkv & NZ & WS1' & NBv & FRESHwa & FRESHv & LIVEq & LB' & NL' & FRK).
    - (* [comment removed for export] *)
      clear ST.
      lazymatch type of FRK with cframe _ _ _ _ _ _ _ ?mx _ =>
        assert (IMG' : img_ok0 m')
          by (eapply (img_ok0_ccall A A' mx md m'); [exact AINV1| exact FRK| unfold IMG0_HI; lia| intros a Ha X; cbn beta in X; unfold IMG0_LO, IMG0_HI, h_ws, h_wsbuf in *; lia
              | eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG]]) end.
      acall_xfer FRK. clear AINV1. rename ST' into ST.
      pose proof WS1' as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL WSC WEC LWA WAC LVEP | dand9 WS1x as id pad IDOK PADL WSC WEC LWA WAC LVEP | destruct WS1x as (id & pad & IDOK & PADL & WSC & WEC & LWA & WAC & LVEP) ]). cbn [al_segs LayoutP0] in WSC, WEC, WAC.
      (first [ pose proof ((as_live_ok A' m' md' r _ AINV' LWA)) as dR_11; dand7 dR_11 as _ WA16 WAlo WAhi WAimg WAmap WAown | pose proof (as_live_ok A' m' md' r _ AINV' LWA) as (_ & WA16 & WAlo & WAhi & WAimg & WAmap & WAown) ]). clear WAimg.
      (first [ pose proof ((as_live_ok A' m' md' vep _ AINV' LVEP)) as dR_12; dand7 dR_12 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A' m' md' vep _ AINV' LVEP) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]). clear VEPimg.
      unfold wsalloc_cells, wsalloc_WS1 in WAC. cbn [wa_off wa_len wa_ptr wa_next wa_prev] in WAC.
      lazymatch type of MU with munch ?W _ _ =>
        pose proof (munch_refl W m') as MU2; pose proof (wmono_refl rsegs m') as WM2;
        assert (CFP2 : client_fp LayoutP0 A' W) by (cbn; split; [left; lia| exact I]) end.
      rz_resume MDH' MDL'.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      call_lit (WS_Assert_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H (Some (A', r, vep)) lo) by (idtac;
        lazymatch goal with
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
        | |- ws_state _ _ _ => cbn [ws_state]; split; [exact WS1'| lia]
        | |- glob_ok _ _ _ _ => exact GLOB'
        | |- henv_geom _ => exact HG
        | |- img_ok0 _ => exact IMG'
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => rewrite ?Ews; reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
      zstep. zstep. if_cases KV; zify_cond KV. { kill KV. } clear KV.
      (* [comment removed for export] *)
      pose proof IMG' as IMGx.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (IMGc : img_ok0 mx) by (eapply (img_ok0_munch _ m'); [exact MU2| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG']) end.
      (first [ dand5 IMGc as _ _ _ GCP _ | destruct IMGc as (_ & _ & _ & GCP & _) ]). unfold GOT_cp in GCP. cbn [al_segs LayoutP0] in GCP.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (GLOBc : glob_ok LayoutP0 VI0 H mx) by (eapply GLOBP; [exact GLOB'| exact MU2| exact WM2| intros a Ha; cbn [outside]; lia]) end.
      (first [ pose proof (GLOBc) as dR_14; dand4 dR_14 as EBSS BSS CP _ | pose proof GLOBc as (EBSS & BSS & CP & _) ]). rewrite EBSS in BSS. cbn [vi_bss VI0 al_segs LayoutP0] in BSS. cbn [al_segs LayoutP0] in CP.
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases KD; zify_cond KD. 2:{ kill KD. } clear KD.
      (* [comment removed for export] *)
      zstep. do 4 zstep. zstep. zstep.
      try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      cps_done.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        lazymatch type of MU2 with munch ?W _ _ =>
          pose proof (ainv_munch LayoutP0 A' m' mx md' W AINV' MU2 WM2 CFP2) as AINV9 end end.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ vep A' _ md');
        [ exact AINV9 | assumption | exact MDF | exact ST
        | eapply GLOBP; [exact GLOB'| exact MU2| exact WM2| intros a Ha; cbn [outside]; lia] | ].
      exists r, junkv. split; [lia|].
      split; [eapply (ws1_obj_munch LayoutP0); [exact WS1'| exact MU2| exact WM2| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]|].
      split; [assumption|]. split; [exact FRESHwa|]. split; [exact FRESHv|]. split; [exact LIVEq|]. split; [exact LB'|]. split; [exact NL'|].
      eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m _ m' _ _ _);
        [ exact MU | | exact FRK | lia | lia | intros a X; exact X | intros a X; left; exact X
        | exact MU2 | | eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | lia | lia] ];
        intros a Ha NO; cbn [outside] in NO; lia.
  Qed.
End S.

End V_WSd07.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VS6ai.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_memset OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_WSwg5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VEz1x.V_WSd07 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VS6ai.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module V_WSitf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Img0 Img0 V_Co10c V_Leaves.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import R_memset V_WSwg5.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac akit_plia := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac akit_avoids_false X :=
  lazymatch type of X with
  | _ \/ _ => destruct X as [X|X]; akit_avoids_false X
  | False => destruct X
  | _ => try (lazymatch type of X with (_ <> _) /\ _ => destruct X as [_ X] end);
         first [ match goal with D : _ \/ _ |- _ => solve [ destruct D; akit_plia ] end | akit_plia ]
  end.
Local Ltac avoids_solve ::=
  cbn [Cells.cells_size Cells.csize Nat.add length app];
  split; [ lia | intros ? ? X; unfold blk, nowhere in X; cbn beta in X; first [ solve [ akit_avoids_false X ] | lia ] ].
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition keptR (P : Prop) : Prop := P.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hide_slowR :=
  repeat match goal with H : (?x <> ?y) |- _ => (lazymatch type of H with ?T__ => change (keptR T__) in H end) end;
  repeat match goal with H : (?x mod ?y = ?z)%Z |- _ => (lazymatch type of H with ?T__ => change (keptR T__) in H end) end;
  (* [comment removed for export] *)
  repeat match goal with H : keptR ((bv_unsigned _ mod _ = _)%Z) |- _ => (lazymatch type of H with keptR ?T__ => change T__ in H | _ => idtac end) end.
Ltac unhide_slowR := repeat match goal with H : keptR _ |- _ => (lazymatch type of H with keptR ?T__ => change T__ in H | _ => idtac end) end.
(* [comment removed for export] *)
Ltac hide_disjR := repeat match goal with H : (_ \/ _) |- _ => (lazymatch type of H with ?T__ => change (keptR T__) in H end) end.
Ltac unhide_disjR := repeat match goal with H : keptR (_ \/ _) |- _ => (lazymatch type of H with keptR ?T__ => change T__ in H | _ => idtac end) end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ws_alloc_free_entry : Z := 0x18b38.
Definition WS_Reset_entry : Z := 0x1899c.
(* [comment removed for export] *)
Definition WSAFREE_STACK : Z := 32 + FREE_STACK.
(* [comment removed for export] *)
Definition WSRESET_STACK : Z := 48 + WSAFREE_STACK.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma cframe_trimV {AI : AllocSpec LayoutP0} : forall o o' sp win (V V' N : Z -> Prop) m m',
  cframe LayoutP0 o o' sp win V N m m' ->
  (forall a, V a -> V' a \/ (sp - win <= a < sp)) -> (forall a, N a -> False) ->
  cframe LayoutP0 o o' sp win V' N m m'.
Proof.
  (intros o o' sp win V V' N m m'; (first [ intro dR_21; dand3 dR_21 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros HV HN). split; [|split; [exact C2|]].
  - intros a Ha NO VIS NW NE NV. apply C1; [exact Ha| exact NO| exact VIS| exact NW| exact NE|].
    intros X. destruct (HV a X) as [Y|Y]; [exact (NV Y)| exact (NW Y)].
  - intros a _ _ _ X. destruct (HN a X).
Qed.

End CEIL.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ws_alloc_free_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (H : henv) (WAP wa vep : Z) (pad : list byte) (lo : Z) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 (h_wsbuf H) -> a1 = Z_to_bv 64 WAP ->
      rw_cells rsegs m WAP [C8 (Z_to_bv 64 wa)] ->
      rw_cells rsegs m (h_wsbuf H) (wsemu_cells (wsemu_WS1 wa)) ->
      a_live A wa = Some 40 -> rw_cells rsegs m wa (wsalloc_cells (wsalloc_WS1 (h_wsbuf H) vep) pad) -> length pad = 4%nat ->
      a_live A vep = Some 312 ->
      henv_geom H -> img_ok0 m ->
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->   (* [comment removed for export] *)
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + WSAFREE_STACK <= bv_unsigned sp ->
      bv_unsigned sp <= WAP -> WAP + 8 <= h_sp H ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) ->
          rw_cells rsegs m' WAP [C8 (Z_to_bv 64 0)] ->
          rw_cells rsegs m' (h_wsbuf H) (wsemu_cells (wsemu_WS0 (h_wsbuf H))) ->
          a_live A' wa = None -> a_live A' vep = None ->
          (forall q, q <> wa -> q <> vep -> a_live A' q = a_live A q) ->
          a_livebytes A' = a_livebytes A - 352 -> a_nlive A' = a_nlive A - 2 ->   (* [comment removed for export] *)
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) WSAFREE_STACK
                 (fun a => blk wa 40 a \/ blk vep 312 a \/ h_wsbuf H + 16 <= a < h_wsbuf H + 32 \/ WAP <= a < WAP + 8) nowhere m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 ws_alloc_free_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. intros AINV MI Ha0 Ha1 WAPC WEC LWA WAC PADL LVEP HG IMG TP SP16 RA4 ST CEIL LO WAPlo WAPhi K.
    rewrite Ha0, Ha1.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutP0)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY.
    pose proof alloc_ceiling_val as ACV.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G16 GCE GHI | pose proof HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    pose proof IMG as IMG0. (first [ dand3 IMG as _ GMS _ | destruct IMG as (_ & GMS & _) ]). unfold GOT_memset in GMS.
    unfold WSAFREE_STACK, FREE_STACK in *. unfold ws_alloc_free_entry.
    rewrite Ewb in WEC, WAC |- *.
    (first [ pose proof ((as_live_ok A m md wa _ AINV LWA)) as dR_3; dand7 dR_3 as _ WA16 WAlo WAhi WAimg WAmap WAown | pose proof (as_live_ok A m md wa _ AINV LWA) as (_ & WA16 & WAlo & WAhi & WAimg & WAmap & WAown) ]).
    assert (WAbss : wa + 40 <= 0x10000 \/ 0x63000 <= wa) by (unfold in_image in WAimg; cbn [al_image_lo al_image_hi LayoutP0] in WAimg; lia).
    clear WAimg.
    (first [ pose proof ((as_live_ok A m md vep _ AINV LVEP)) as dR_4; dand7 dR_4 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A m md vep _ AINV LVEP) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]).
    assert (VEPbss : vep + 312 <= 0x10000 \/ 0x63000 <= vep) by (unfold in_image in VEPimg; cbn [al_image_lo al_image_hi LayoutP0] in VEPimg; lia).
    clear VEPimg.
    assert (NEwv : wa <> vep) by (intros ->; rewrite LVEP in LWA; discriminate LWA).
    pose proof (as_live_disjoint A m md wa 40 vep 312 AINV LWA LVEP NEwv) as DJ.
    unfold wsemu_cells, wsemu_WS1 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
    unfold wsalloc_cells, wsalloc_WS1 in WAC. cbn [wa_off wa_len wa_ptr wa_next wa_prev] in WAC.
    replace (h_sp H + 16 + 16) with (h_sp H + 32) in WAC by lia.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8224, bv_unsigned sp); (WAP, WAP + 8); (h_sp H + 32, h_sp H + 48)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 8224, bv_unsigned sp); (WAP, WAP + 8); (h_sp H + 32, h_sp H + 48)]).
    { cbn. split; [left; lia|]. split; [left; lia|]. split; [left; lia| exact I]. }
    apply rz_go; [exact MDH | exact MDL |]. hide_slowR.
    carve_frame 32%nat ST.
    do 3 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1. { kill K1. } clear K1.
    zstep. zstep. if_cases K2; zify_cond K2. { kill K2. } clear K2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (ainv_munch LayoutP0 A m mx md _ AINV MU WM CFP) as AINV1;
      pose_cranges LayoutP0 A mx AINV1 end.
    clear GMS.
    eapply (as_free_cps (L:=LayoutP0)) with (p := vep) (n0 := 312);
      [ exact AINV1 | assumption | reflexivity | right; exact LVEP | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; unfold FREE_STACK; lia
      | rewrite unsigned_lit by lia; eapply (stk_mapped (L:=LayoutP0)); [exact ST| exact CEIL | unfold FREE_STACK; lia | lia]
      | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 AINV' MI' MDF DEADv LIVEq LBf1 NLf1 _ FRK.
    pose proof (as_lazy_nil A1 m1 md1 AINV') as [MDL' MDH'].
    rewrite unsigned_lit in FRK by lia.
    lazymatch type of FRK with frame_ok _ _ _ _ _ _ _ ?mx _ =>
      assert (IMG1 : img_ok0 m1)
        by (eapply (img_ok0_ccall A A1 mx md m1); [exact AINV1| apply (cframe_of_frame_ok LayoutP0); exact FRK
            | unfold IMG0_HI, FREE_STACK; lia| intros a Ha X; unfold IMG0_LO, IMG0_HI, blk in *; lia
            | eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG0]]) end.
    hide_disjR. (lazymatch type of DJ with keptR ?T__ => change T__ in DJ | _ => idtac end). acall_xfer FRK. unhide_disjR. clear AINV1.
    assert (LWA1 : a_live A1 wa = Some 40) by (rewrite (LIVEq wa NEwv); exact LWA).
    pose proof (munch_refl [(bv_unsigned sp - 8224, bv_unsigned sp); (wa, wa + 40)] m1) as MU2.
    pose proof (wmono_refl rsegs m1) as WM2.
    assert (CFP2 : client_fp LayoutP0 A1 [(bv_unsigned sp - 8224, bv_unsigned sp); (wa, wa + 40)]).
    { cbn. split; [left; lia|]. split; [right; left; exists wa, 40; split; [exact LWA1|lia]| exact I]. }
    pose proof IMG1 as IMG1'. (first [ dand3 IMG1' as _ GMS1 _ | destruct IMG1' as (_ & GMS1 & _) ]). unfold GOT_memset in GMS1. cbn [al_segs LayoutP0] in GMS1.
    rz_resume MDH' MDL'.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of WAC with rw_cells _ _ _ (?c0 :: ?rest) =>
        pose proof (proj1 (rw_cells_app rsegs mx wa [c0] rest) WAC) as [WAa WAb] end end.
    clear WAC. destruct (rw_cells_forget _ _ _ _ WAa) as [junkm WAa']. clear WAa. cbn [cells_size csize Nat.add] in WAa', WAb.
    call memset_spec_z.
    1:{ exact WAa'. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    zstep.
    apply rz_stop.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (ainv_munch LayoutP0 A1 m1 mx md1 _ AINV' MU2 WM2 CFP2) as AINV2;
      pose_cranges LayoutP0 A1 mx AINV2 end.
    eapply (as_free_cps (L:=LayoutP0)) with (p := wa) (n0 := 40);
      [ exact AINV2 | assumption | reflexivity | right; exact LWA1 | exact TP
      | exact SP16 | exact RA4
      | unfold FREE_STACK; lia
      | eapply (stk_mapped (L:=LayoutP0)); [exact ST| exact CEIL | unfold FREE_STACK; lia | lia]
      | ].
    intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x A2 m3 md3 AINV3 MI3 MDF3 DEADwa LIVEq3 LBf2 NLf2 _ FRK2.
    pose proof (as_lazy_nil A2 m3 md3 AINV3) as [MDL3 MDH3].
    (* [comment removed for export] *)
    lazymatch type of MU2 with munch _ _ ?mx =>
      assert (CFa : cframe LayoutP0 (owned A) (owned A1) (bv_unsigned sp) 8224
                       (fun a => blk wa 40 a \/ blk vep 312 a \/ h_wsbuf H + 16 <= a < h_wsbuf H + 32 \/ WAP <= a < WAP + 8) nowhere m mx)
        by (eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m _ m1 _ _ _);
            [ exact MU | | exact FRK | unfold FREE_STACK; lia | lia | intros a X; right; left; exact X | intros a X; destruct X
            | exact MU2 | | eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | lia | lia] ];
            [ intros a Ha NO; cbn [outside] in NO; cbn beta; unfold h_wsbuf; lia
            | intros a Ha NO; cbn [outside] in NO; cbn beta; unfold blk; lia ])
    end.
    try clear POST. try clear WAb. try clear GMS1.
    hide_disjR. (lazymatch type of DJ with keptR ?T__ => change T__ in DJ | _ => idtac end). acall_xfer FRK2. unhide_disjR.
    pose proof (bv_unsigned_in_range 64 ra) as RR. unfold bv_modulus in RR. cbn in RR.
    assert (RP : ret_pc ra = ra).
    { rewrite <- (MState.Z_to_bv_bv_unsigned ra). rewrite ret_pc_even; [reflexivity | exact RR | lia]. }
    fold_al_segs. rewrite ?mkst_MS.
    lazymatch goal with |- realizes _ (mkCfg (MS ?R _ _ ?fc ?rv ?mm ?ro) ?mdx) _ =>
      enough (G : realizes rsegs (mkCfg (MS R bvmap_empty (ret_pc ra) fc rv mm ro) mdx) T) by (rewrite RP in G; exact G) end.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A2 m3 md3);
      [ exact AINV3 | assumption | eapply md_frame_trans; [exact MDF| exact MDF3] | exact ST
      | assumption
      | unfold wsemu_cells, wsemu_WS0; cbn [we_len we_ws we_first we_last]; rewrite Ewb; replace (h_sp H + 16 + 16) with (h_sp H + 32) by lia; assumption
      | exact DEADwa
      | rewrite (LIVEq3 vep (fun E => NEwv (eq_sym E))); exact DEADv
      | intros q Q1 Q2; rewrite (LIVEq3 q Q1); apply LIVEq; exact Q2
      | rewrite LBf2, LBf1; lia
      | rewrite NLf2, NLf1;
        replace (vep =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
        replace (wa =? 0) with false by (symmetry; apply Z.eqb_neq; lia); lia
      | ].
    lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?mfin =>
      eapply (cframe_seq LayoutP0 _ _ _ _ _ _ _ _ _ _ _ _ _ m _ mfin CFa FRK2); [lia | lia
        | eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | lia | lia]
        | intros a X; exact X | intros a X; right; left; exact X | intros a X; destruct X ] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ws_E (H : henv) (A : AS) (m : mem) (E : option (Z * Z)) : Prop :=
    match E with None => ws0_obj LayoutP0 H m | Some (wa, vep) => ws1_obj LayoutP0 H A m wa vep end.

  Lemma WS_Reset_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (H : henv) (E : option (Z * Z)) (lo : Z) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 (h_ws H) -> a1 = Z_to_bv 64 (h_wsbuf H) ->
      ws_E H A m E ->
      glob_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + WSRESET_STACK <= bv_unsigned sp ->
      bv_unsigned sp <= h_sp H ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> glob_ok LayoutP0 VI0 H m' -> ws0_obj LayoutP0 H m' ->
          match E with
          | None => (forall p, a_live A' p = a_live A p) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some (wa, vep) => a_live A' wa = None /\ a_live A' vep = None /\
                              (forall p, p <> wa -> p <> vep -> a_live A' p = a_live A p) /\
                              a_livebytes A' = a_livebytes A - 352 /\ a_nlive A' = a_nlive A - 2
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) WSRESET_STACK
                 (fun a => h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32 \/
                           match E with None => False | Some (wa, vep) => blk wa 40 a \/ blk vep 312 a end)
                 nowhere m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 WS_Reset_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. intros AINV MI Ha0 Ha1 WSX GLOB HG IMG TP SP16 RA2 ST CEIL LO SPH K.
    rewrite Ha0, Ha1.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutP0)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY.
    pose proof alloc_ceiling_val as ACV.
    (first [ pose proof (HG) as dR_6; dand3 dR_6 as G16 GCE GHI | pose proof HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (Ebss : h_bss H = 0x41830) by (destruct GLOB as [E0 _]; rewrite E0; reflexivity).
    pose proof IMG as IMG0. (first [ dand5 IMG as _ _ _ GCP _ | destruct IMG as (_ & _ & _ & GCP & _) ]). unfold GOT_cp in GCP.
    unfold WSRESET_STACK, WSAFREE_STACK, FREE_STACK in *. unfold WS_Reset_entry.
    rewrite Ews, Ewb.
    assert (GLOBP : forall W mp mq, glob_ok LayoutP0 VI0 H mp -> munch W mp mq -> wmono rsegs mp mq ->
      (forall a, (0x41830 <= a < 0x41830 + 16 \/ h_sp H + 1488 <= a < h_sp H + 1488 + 752 \/ h_sp H + 2240 + 1304 <= a < h_sp H + 2240 + 1320) -> outside W a) ->
      glob_ok LayoutP0 VI0 H mq).
    { intros W mp mq G MUx WMx OUT. eapply (glob_ok_munch LayoutP0); [exact G| exact MUx| exact WMx|].
      intros a Ha. apply OUT. rewrite Ebss in Ha. unfold h_cp, h_vsc in Ha. exact Ha. }
    pose proof (munch_refl [(bv_unsigned sp - 8272, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 8272, bv_unsigned sp)]).
    { cbn. split; [left; lia| exact I]. }
    destruct E as [[wa vep]|]; cbn [ws_E] in WSX.
    - (* [comment removed for export] *)
      pose proof WSX as WS1. (first [ dex2 WSX as id pad; dand7 WSX as IDOK PADL WSC WEC LWA WAC LVEP | dand9 WSX as id pad IDOK PADL WSC WEC LWA WAC LVEP | destruct WSX as (id & pad & IDOK & PADL & WSC & WEC & LWA & WAC & LVEP) ]). cbn [al_segs LayoutP0] in WSC, WEC, WAC.
      assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
      (first [ pose proof ((as_live_ok A m md wa _ AINV LWA)) as dR_9; dand7 dR_9 as _ WA16 WAlo WAhi WAimg WAmap WAown | pose proof (as_live_ok A m md wa _ AINV LWA) as (_ & WA16 & WAlo & WAhi & WAimg & WAmap & WAown) ]).
      assert (WAbss : wa + 40 <= 0x10000 \/ 0x63000 <= wa) by (unfold in_image in WAimg; cbn [al_image_lo al_image_hi LayoutP0] in WAimg; lia).
      clear WAimg.
      (first [ pose proof ((as_live_ok A m md vep _ AINV LVEP)) as dR_10; dand7 dR_10 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A m md vep _ AINV LVEP) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]).
      assert (VEPbss : vep + 312 <= 0x10000 \/ 0x63000 <= vep) by (unfold in_image in VEPimg; cbn [al_image_lo al_image_hi LayoutP0] in VEPimg; lia).
      clear VEPimg.
      assert (NEwv : wa <> vep) by (intros ->; rewrite LVEP in LWA; discriminate LWA).
      unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
      unfold wsemu_cells, wsemu_WS1 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
      unfold wsalloc_cells, wsalloc_WS1 in WAC. cbn [wa_off wa_len wa_ptr wa_next wa_prev] in WAC.
      rewrite Ews in WSC. rewrite Ewb in WSC, WEC, WAC.
      apply rz_go; [exact MDH | exact MDL |]. hide_slowR.
      carve_frame 48%nat ST.
      do 5 zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      call_lit (WS_Assert_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H (Some (A, wa, vep)) lo) by (idtac;
        lazymatch goal with
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
        | |- ws_state _ _ _ => cbn [ws_state]; split; [eapply (ws1_obj_munch LayoutP0); [exact WS1| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]| lia]
        | |- glob_ok _ _ _ _ => eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | |- henv_geom _ => exact HG
        | |- img_ok0 _ => eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG0]
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => rewrite ?Ews; reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
      zstep. zstep. zstep. if_cases K1; zify_cond K1. 2:{ kill K1. } clear K1.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (GLOBc : glob_ok LayoutP0 VI0 H mx) by (eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]) end.
      (first [ pose proof (GLOBc) as dR_11; dand4 dR_11 as EBSS BSS CP _ | pose proof GLOBc as (EBSS & BSS & CP & _) ]). rewrite EBSS in BSS. cbn [vi_bss VI0 al_segs LayoutP0] in BSS. cbn [al_segs LayoutP0] in CP. clear GLOBc.
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ kill K2. } clear K2.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K3; zify_cond K3. { kill K3. } clear K3.
      zstep. zstep.
      call_lit (ws_emu_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h_sp H + 1080)
                (WSR id (h_sp H + 16) 0 0 (h_sp H + 16 + 1016)) (WER 1016 0 wa (wa + 24)) lo) by (idtac;
        lazymatch goal with
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
        | |- rw_cells _ _ _ (ws_cells _) => exact WSC
        | |- rw_cells _ _ _ (wsemu_cells _) => exact WEC
        | |- length _ = _ => exact IDL
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => reflexivity
        | |- _ => cbn [ws_s]; rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST. cbn [ws_s].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases K4; zify_cond K4. { kill K4. } clear K4.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K5; zify_cond K5. { kill K5. } clear K5.
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
          pose proof (proj1 (rw_cells_app rsegs mx _ [c0] (c1 :: rest)) FR) as [FRa FRbc];
          pose proof (proj1 (rw_cells_app rsegs mx _ [c1] rest) FRbc) as [FRb FRc] end end.
      clear FR FRbc.
      pose proof (rwc_eq _ _ _ (bv_unsigned sp + -40) _ FRb ltac:(cbn; lia)) as WAPC. clear FRb.
      pose proof (rwc_eq _ _ _ (bv_unsigned sp + -32) _ FRc ltac:(cbn; lia)) as FRc'. clear FRc. rename FRc' into FRc.
      apply rz_stop.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        pose proof (ainv_munch LayoutP0 A m mx md _ AINV MU WM CFP) as AINV1;
        pose_cranges LayoutP0 A mx AINV1 end.
      eapply ws_alloc_free_cps;
        [ exact AINV1 | assumption | reflexivity | reflexivity
        | exact WAPC
        | exact WEC | exact LWA | exact WAC | exact PADL | exact LVEP | exact HG
        | eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG0]
        | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; exact ST | exact CEIL
        | rewrite unsigned_lit by lia; unfold WSAFREE_STACK, FREE_STACK; lia
        | rewrite ?unsigned_lit by lia; lia | rewrite ?unsigned_lit by lia; lia | ].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' AINV' MI' MDF ST' WAPC' WEC' DEADwa DEADv LIVEq LBf NLf FRK.
      pose proof (as_lazy_nil A' m' md' AINV') as [MDL' MDH'].
      rewrite unsigned_lit in FRK by lia. rewrite unsigned_lit in ST' by lia. unfold WSAFREE_STACK, FREE_STACK in FRK.
      rewrite Ewb in WEC'. unfold wsemu_cells, wsemu_WS0 in WEC'. cbn [we_len we_ws we_first we_last] in WEC'.
      hide_disjR. (lazymatch type of WAbss with keptR ?T__ => change T__ in WAbss | _ => idtac end). (lazymatch type of VEPbss with keptR ?T__ => change T__ in VEPbss | _ => idtac end).
      lazymatch type of FRK with cframe _ _ _ _ _ _ _ ?mx _ =>
        assert (GLOB1 : glob_ok LayoutP0 VI0 H m')
          by (eapply (glob_ok_ccall LayoutP0 VI0 H A A' mx md m'); [exact AINV1| exact FRK| exact HG
              | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
              | lia| lia
              | rewrite Ebss; cbn; lia| rewrite Ebss; cbn; lia
              | intros i Hi; rewrite Ebss; cbn; unfold p0_static; lia
              | rewrite Ebss; cbn; change (al_errno LayoutP0) with 0x420b4; lia
              | intros a Ha X; cbn beta in X; rewrite Ebss in Ha; unfold h_cp, h_vsc, h_wsbuf, blk in *; lia]);
        assert (IMG1 : img_ok0 m')
          by (eapply (img_ok0_ccall A A' mx md m'); [exact AINV1| exact FRK
              | unfold IMG0_HI; lia| intros a Ha X; cbn beta in X; unfold IMG0_LO, IMG0_HI, h_wsbuf, blk in *; lia
              | eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG0]])
      end.
      clear WAPC BSS WAC WEC GCP.
      repeat match goal with
             | C : crange _ _ wa _ |- _ => clear C
             | C : crange _ _ (h_sp H + 16) _ |- _ => clear C
             | C : crange _ _ (bv_unsigned sp + -40) _ |- _ => clear C end.
      clear ST. hide_disjR. acall_xfer FRK. unhide_disjR. clear AINV1. rename ST' into ST.
      pose proof (munch_refl [(bv_unsigned sp - 8272, bv_unsigned sp)] m') as MU2.
      pose proof (wmono_refl rsegs m') as WM2.
      assert (CFP2 : client_fp LayoutP0 A' [(bv_unsigned sp - 8272, bv_unsigned sp)]) by (cbn; split; [left; lia| exact I]).
      rz_resume MDH' MDL'.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases K6; zify_cond K6. 2:{ kill K6. } clear K6.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K7; zify_cond K7. { kill K7. } clear K7.
      zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (rwc_eq _ _ _ (bv_unsigned sp + -48 + Z.of_nat (cells_size [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 junk)))))])) _ WAPC' ltac:(cbn; lia)) as Wb;
        pose proof (proj2 (rw_cells_app rsegs mx (bv_unsigned sp + -48) _ _) (conj FRa Wb)) as FRab;
        pose proof (rwc_eq _ _ _ (bv_unsigned sp + -48 + Z.of_nat (cells_size ([CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 junk)))))] ++ [C8 (Z_to_bv 64 0)]))) _ FRc ltac:(cbn; lia)) as Wc;
        pose proof (proj2 (rw_cells_app rsegs mx (bv_unsigned sp + -48) _ _) (conj FRab Wc)) as FR end.
      clear Wb Wc FRab FRa FRc WAPC'. cbn [app] in FR.
      try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      zstep.
      call_lit (WS_Assert_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H None lo) by (idtac;
        lazymatch goal with
        | |- stk _ _ _ _ => exact ST
        | |- ws_state _ _ _ => cbn [ws_state]; apply (ws0_obj_intro LayoutP0 H _ id IDOK); cbn [al_segs LayoutP0];
              [exact WSC| unfold wsemu_cells, wsemu_WS0; cbn [we_len we_ws we_first we_last]; rewrite Ewb; exact WEC']
        | |- glob_ok _ _ _ _ => eapply GLOBP; [exact GLOB1| exact MU2| exact WM2| intros a Ha; cbn [outside]; lia]
        | |- henv_geom _ => exact HG
        | |- img_ok0 _ => eapply (img_ok0_munch _ m'); [exact MU2| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG1]
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => rewrite ?Ews; reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
      cps_done.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        lazymatch type of MU2 with munch ?W _ _ =>
          pose proof (ainv_munch LayoutP0 A' m' mx md' W AINV' MU2 WM2 CFP2) as AINV9 end end.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' _ md');
        [ exact AINV9 | assumption | exact MDF | exact ST
        | eapply GLOBP; [exact GLOB1| exact MU2| exact WM2| intros a Ha; cbn [outside]; lia]
        | apply (ws0_obj_intro LayoutP0 H _ id IDOK); cbn [al_segs LayoutP0];
          [exact WSC| unfold wsemu_cells, wsemu_WS0; cbn [we_len we_ws we_first we_last]; rewrite Ewb; exact WEC']
        | split; [exact DEADwa| split; [exact DEADv| split; [exact LIVEq| split; [exact LBf| exact NLf]]]] | ].
      lazymatch goal with |- cframe _ _ _ _ _ ?VV _ _ ?mfin =>
        assert (CFx : cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) 8272
                        (fun a => VV a \/ (bv_unsigned sp + -40 <= a < bv_unsigned sp + -40 + 8)) nowhere m mfin)
          by (eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m _ m' _ _ _);
              [ exact MU | | exact FRK | lia | lia | | intros a X; destruct X
              | exact MU2 | | eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | lia | lia] ];
              [ intros a Ha NO; cbn [outside] in NO; lia
              | intros a X; cbn beta in X |- *; unfold h_wsbuf in *;
                destruct X as [X|[X|[X|X]]]; [left; right; right; left; exact X| left; right; right; right; exact X| left; right; left; lia| right; exact X]
              | intros a Ha NO; cbn [outside] in NO; lia ]);
        eapply (cframe_trimV _ _ _ _ _ _ _ _ _ CFx); [| intros a X; exact X];
        intros a [X|X]; [left; exact X| right; lia]
      end.
    - (* [comment removed for export] *)
      pose proof WSX as WS0. (first [ dex1 WSX as id; dand3 WSX as IDOK WSC WEC | dand4 WSX as id IDOK WSC WEC | destruct WSX as (id & IDOK & WSC & WEC) ]). cbn [al_segs LayoutP0] in WSC, WEC.
      assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
      unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
      unfold wsemu_cells, wsemu_WS0 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
      rewrite Ews in WSC. rewrite Ewb in WSC, WEC.
      apply rz_go; [exact MDH | exact MDL |]. hide_slowR.
      carve_frame 48%nat ST.
      do 5 zstep.
      zstep. zstep. zstep.
      call_lit (WS_Assert_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H None lo) by (idtac;
        lazymatch goal with
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
        | |- ws_state _ _ _ => cbn [ws_state]; eapply (ws0_obj_munch LayoutP0); [exact WS0| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]
        | |- glob_ok _ _ _ _ => eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | |- henv_geom _ => exact HG
        | |- img_ok0 _ => eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG0]
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => rewrite ?Ews; reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
      zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
      zstep. zstep. zstep. if_cases K1; zify_cond K1. 2:{ kill K1. } clear K1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (GLOBc : glob_ok LayoutP0 VI0 H mx) by (eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]) end.
      (first [ pose proof (GLOBc) as dR_13; dand4 dR_13 as EBSS BSS CP _ | pose proof GLOBc as (EBSS & BSS & CP & _) ]). rewrite EBSS in BSS. cbn [vi_bss VI0 al_segs LayoutP0] in BSS. cbn [al_segs LayoutP0] in CP. clear GLOBc.
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ kill K2. } clear K2.
      zstep. zstep. if_cases K3; zify_cond K3. { kill K3. } clear K3.
      zstep. zstep.
      call_lit (ws_emu_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h_sp H + 1080)
                (WSR id (h_sp H + 16) 0 0 (h_sp H + 16 + 1016)) (WER 1016 0 0 (h_sp H + 16 + 16)) lo) by (idtac;
        lazymatch goal with
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
        | |- rw_cells _ _ _ (ws_cells _) => exact WSC
        | |- rw_cells _ _ _ (wsemu_cells _) => exact WEC
        | |- length _ = _ => exact IDL
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => reflexivity
        | |- _ => cbn [ws_s]; rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST. cbn [ws_s].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases K4; zify_cond K4. 2:{ kill K4. } clear K4.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K7; zify_cond K7. { kill K7. } clear K7.
      zstep. zstep. zstep. zstep. zstep. zstep.
      try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      zstep.
      call_lit (WS_Assert_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H None lo) by (idtac;
        lazymatch goal with
        | |- stk _ _ _ _ => exact ST
        | |- ws_state _ _ _ => cbn [ws_state]; eapply (ws0_obj_munch LayoutP0); [exact WS0| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]
        | |- glob_ok _ _ _ _ => eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | |- henv_geom _ => exact HG
        | |- img_ok0 _ => eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG0]
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => rewrite ?Ews; reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
      cps_done.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        lazymatch type of MU with munch ?W _ _ =>
          pose proof (ainv_munch LayoutP0 A m mx md W AINV MU WM CFP) as AINV9 end end.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A _ md);
        [ exact AINV9 | assumption | apply md_frame_refl; [exact MDL| exact MDH] | exact ST
        | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | eapply (ws0_obj_munch LayoutP0); [exact WS0| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]
        | split; [intros p; reflexivity| split; reflexivity] | ].
      eapply (cframe_stores LayoutP0); [exact MU| | eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | lia | lia]].
      intros a Ha NO. cbn [outside] in NO. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma WS_Rollback_ok : WS_Rollback_stmt.
  Proof.
    unfold WS_Rollback_stmt.
    intros H E lo. intros until T. intros AINV MI Ha0 Ha1 WSX GLOB HG IMG TP SP16 RA2 ST CEIL LO SPH K.
    rewrite Ha0, Ha1.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutP0)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY.
    pose proof alloc_ceiling_val as ACV.
    (first [ pose proof (HG) as dR_14; dand3 dR_14 as G16 GCE GHI | pose proof HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (Ebss : h_bss H = 0x41830) by (destruct GLOB as [E0 _]; rewrite E0; reflexivity).
    unfold WSROLLBACK_STACK, FREE_STACK in *. unfold WS_Rollback_entry.
    rewrite Ews.
    assert (GLOBP : forall W mp mq, glob_ok LayoutP0 VI0 H mp -> munch W mp mq -> wmono rsegs mp mq ->
      (forall a, (0x41830 <= a < 0x41830 + 16 \/ h_sp H + 1488 <= a < h_sp H + 1488 + 752 \/ h_sp H + 2240 + 1304 <= a < h_sp H + 2240 + 1320) -> outside W a) ->
      glob_ok LayoutP0 VI0 H mq).
    { intros W mp mq G MUx WMx OUT. eapply (glob_ok_munch LayoutP0); [exact G| exact MUx| exact WMx|].
      intros a Ha. apply OUT. rewrite Ebss in Ha. unfold h_cp, h_vsc in Ha. exact Ha. }
    pose proof (munch_refl [(bv_unsigned sp - 8272, bv_unsigned sp); (h_sp H + 1080, h_sp H + 1080 + 40)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 8272, bv_unsigned sp); (h_sp H + 1080, h_sp H + 1080 + 40)]).
    { cbn. split; [left; lia|]. split; [left; lia| exact I]. }
    destruct E as [[wa vep]|].
    - (* [comment removed for export] *)
      pose proof WSX as WS1. (first [ dex2 WSX as id pad; dand7 WSX as IDOK PADL WSC WEC LWA WAC LVEP | dand9 WSX as id pad IDOK PADL WSC WEC LWA WAC LVEP | destruct WSX as (id & pad & IDOK & PADL & WSC & WEC & LWA & WAC & LVEP) ]). cbn [al_segs LayoutP0] in WSC, WEC, WAC.
      assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
      (first [ pose proof ((as_live_ok A m md wa _ AINV LWA)) as dR_16; dand7 dR_16 as _ WA16 WAlo WAhi WAimg WAmap WAown | pose proof (as_live_ok A m md wa _ AINV LWA) as (_ & WA16 & WAlo & WAhi & WAimg & WAmap & WAown) ]). clear WAimg.
      (first [ pose proof ((as_live_ok A m md vep _ AINV LVEP)) as dR_17; dand7 dR_17 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A m md vep _ AINV LVEP) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]). clear VEPimg.
      unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
      unfold wsemu_cells, wsemu_WS1 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
      unfold wsalloc_cells, wsalloc_WS1 in WAC. cbn [wa_off wa_len wa_ptr wa_next wa_prev] in WAC.
      rewrite Ews in WSC. rewrite Ewb in WSC, WEC, WAC.
      apply rz_go; [exact MDH | exact MDL |]. hide_slowR.
      carve_frame 32%nat ST.
      do 4 zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      call_lit (WS_Assert_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H (Some (A, wa, vep)) lo) by (idtac;
        lazymatch goal with
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
        | |- ws_state _ _ _ => cbn [ws_state]; split; [apply (ws1_obj_intro LayoutP0 H A _ wa vep id pad IDOK PADL); cbn [al_segs LayoutP0];
              [ rewrite Ews; exact WSC | unfold wsemu_cells, wsemu_WS1; cbn [we_len we_ws we_first we_last]; rewrite Ewb; exact WEC | exact LWA
              | unfold wsalloc_cells, wsalloc_WS1; cbn [wa_off wa_len wa_ptr wa_next wa_prev]; rewrite Ewb; exact WAC | exact LVEP] | lia]
        | |- glob_ok _ _ _ _ => eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | |- henv_geom _ => exact HG
        | |- img_ok0 _ => eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG]
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => rewrite ?Ews; reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0. 2:{ kill K0. } clear K0.
      zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1. { kill K1. } clear K1.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (rw_cells_split_CB rsegs mx (h_sp H + 1080) [C4 (Z_to_bv 64 WS_MAGIC)] 4 id
                    [C8 (Z_to_bv 64 (h_sp H + 16)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_sp H + 16 + 1016))]
                    [1; 3]%nat WSC eq_refl) as WS2 end.
      clear WSC. cbn [mk_CB_cells app] in WS2.
      assert (B0 : exists b0 : byte, take 1 id = [b0] /\ drop 1 id = [Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0] /\ Z.lor (bv_unsigned b0) 32 = 114)
        by (destruct IDOK as [-> | ->]; eexists; (split; [reflexivity|]); (split; [reflexivity|]); vm_compute; reflexivity).
      (first [ dex1 B0 as b0; dand3 B0 as Eb1 Eb3 LOR | dand4 B0 as b0 Eb1 Eb3 LOR | destruct B0 as (b0 & Eb1 & Eb3 & LOR) ]). rewrite Eb1, Eb3 in WS2.
      pose proof (bv_unsigned_in_range 8 b0) as B0R. unfold bv_modulus in B0R. cbn in B0R.
      zstep. zstep.
 rewrite LOR. zstep. fix_bstore; mem_after_store.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      zstep.
      pose proof (rw_cells_merge rsegs _ _ [C4 (Z_to_bv 64 WS_MAGIC)] [C1 (Z_to_bv 8 114); CB 3 [Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0]]
                    [C8 (Z_to_bv 64 (h_sp H + 16)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_sp H + 16 + 1016))] WS2) as WSC.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in WSC. clear WS2.
      apply rz_stop.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        pose proof (ainv_munch LayoutP0 A m mx md _ AINV MU WM CFP) as AINV1 end.
      eapply WS_Reset_cps with (H := H) (E := Some (wa, vep)) (lo := lo);
        [ exact AINV1 | assumption | rewrite Ews; reflexivity | rewrite Ewb; reflexivity
        | cbn [ws_E]; apply (ws1_obj_intro LayoutP0 H A _ wa vep ws_id_req pad (or_introl eq_refl) PADL); cbn [al_segs LayoutP0];
          [ rewrite Ews; exact WSC | unfold wsemu_cells, wsemu_WS1; cbn [we_len we_ws we_first we_last]; rewrite Ewb; exact WEC | exact LWA
          | unfold wsalloc_cells, wsalloc_WS1; cbn [wa_off wa_len wa_ptr wa_next wa_prev]; rewrite Ewb; exact WAC | exact LVEP]
        | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | exact HG
        | eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG]
        | exact TP | exact SP16 | exact RA2 | exact ST | exact CEIL | unfold WSRESET_STACK, WSAFREE_STACK, FREE_STACK; lia | exact SPH | ].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' AINV' MI' MDF ST' GLOB' WS0' LIVE' FRK.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' m' md');
        [ exact AINV' | exact MI' | exact MDF | exact ST' | exact GLOB' | exact WS0' | exact LIVE' | ].
      unfold WSRESET_STACK, WSAFREE_STACK, FREE_STACK in FRK.
      lazymatch type of MU with munch _ _ ?mx =>
        eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m mx m' m' _ []);
          [ exact MU | | exact FRK | lia | lia | intros a X; exact X | intros a X; destruct X
          | apply munch_refl | intros a _ X; exfalso; apply X; exact I
          | eapply (stk_mapped (L:=LayoutP0)); [exact ST' | exact CEIL | lia | lia] ] end.
      intros a Ha NO. cbn [outside] in NO. cbn beta. unfold h_ws. lia.
    - (* [comment removed for export] *)
      pose proof WSX as WS0. (first [ dex1 WSX as id; dand3 WSX as IDOK WSC WEC | dand4 WSX as id IDOK WSC WEC | destruct WSX as (id & IDOK & WSC & WEC) ]). cbn [al_segs LayoutP0] in WSC, WEC.
      assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
      unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
      unfold wsemu_cells, wsemu_WS0 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
      rewrite Ews in WSC. rewrite Ewb in WSC, WEC.
      apply rz_go; [exact MDH | exact MDL |]. hide_slowR.
      carve_frame 32%nat ST.
      do 4 zstep.
      zstep. zstep. zstep.
      call_lit (WS_Assert_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H None lo) by (idtac;
        lazymatch goal with
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
        | |- ws_state _ _ _ => cbn [ws_state]; apply (ws0_obj_intro LayoutP0 H _ id IDOK); cbn [al_segs LayoutP0];
              [ rewrite Ews; exact WSC | unfold wsemu_cells, wsemu_WS0; cbn [we_len we_ws we_first we_last]; rewrite Ewb; exact WEC ]
        | |- glob_ok _ _ _ _ => eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | |- henv_geom _ => exact HG
        | |- img_ok0 _ => eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG]
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => rewrite ?Ews; reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
      zstep. if_cases K0; zify_cond K0. 2:{ kill K0. } clear K0.
      zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1. { kill K1. } clear K1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (rw_cells_split_CB rsegs mx (h_sp H + 1080) [C4 (Z_to_bv 64 WS_MAGIC)] 4 id
                    [C8 (Z_to_bv 64 (h_sp H + 16)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_sp H + 16 + 1016))]
                    [1; 3]%nat WSC eq_refl) as WS2 end.
      clear WSC. cbn [mk_CB_cells app] in WS2.
      assert (B0 : exists b0 : byte, take 1 id = [b0] /\ drop 1 id = [Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0] /\ Z.lor (bv_unsigned b0) 32 = 114)
        by (destruct IDOK as [-> | ->]; eexists; (split; [reflexivity|]); (split; [reflexivity|]); vm_compute; reflexivity).
      (first [ dex1 B0 as b0; dand3 B0 as Eb1 Eb3 LOR | dand4 B0 as b0 Eb1 Eb3 LOR | destruct B0 as (b0 & Eb1 & Eb3 & LOR) ]). rewrite Eb1, Eb3 in WS2.
      pose proof (bv_unsigned_in_range 8 b0) as B0R. unfold bv_modulus in B0R. cbn in B0R.
      zstep. zstep. rewrite LOR. zstep. fix_bstore; mem_after_store.
      zstep. zstep. zstep. zstep. zstep. zstep.
      try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      zstep.
      pose proof (rw_cells_merge rsegs _ _ [C4 (Z_to_bv 64 WS_MAGIC)] [C1 (Z_to_bv 8 114); CB 3 [Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0]]
                    [C8 (Z_to_bv 64 (h_sp H + 16)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_sp H + 16 + 1016))] WS2) as WSC.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in WSC. clear WS2.
      apply rz_stop.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        pose proof (ainv_munch LayoutP0 A m mx md _ AINV MU WM CFP) as AINV1 end.
      eapply WS_Reset_cps with (H := H) (E := None) (lo := lo);
        [ exact AINV1 | assumption | rewrite Ews; reflexivity | rewrite Ewb; reflexivity
        | cbn [ws_E]; apply (ws0_obj_intro LayoutP0 H _ ws_id_req (or_introl eq_refl)); cbn [al_segs LayoutP0];
          [ rewrite Ews; exact WSC | unfold wsemu_cells, wsemu_WS0; cbn [we_len we_ws we_first we_last]; rewrite Ewb; exact WEC ]
        | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | exact HG
        | eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG]
        | exact TP | exact SP16 | exact RA2 | exact ST | exact CEIL | unfold WSRESET_STACK, WSAFREE_STACK, FREE_STACK; lia | exact SPH | ].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' AINV' MI' MDF ST' GLOB' WS0' LIVE' FRK.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' m' md');
        [ exact AINV' | exact MI' | exact MDF | exact ST' | exact GLOB' | exact WS0' | exact LIVE' | ].
      unfold WSRESET_STACK, WSAFREE_STACK, FREE_STACK in FRK.
      lazymatch type of MU with munch _ _ ?mx =>
        eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m mx m' m' _ []);
          [ exact MU | | exact FRK | lia | lia | intros a X; exact X | intros a X; destruct X
          | apply munch_refl | intros a _ X; exfalso; apply X; exact I
          | eapply (stk_mapped (L:=LayoutP0)); [exact ST' | exact CEIL | lia | lia] ] end.
      intros a Ha NO. cbn [outside] in NO. cbn beta. unfold h_ws. lia.
  Qed.
End S.
End V_WSitf.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition crc32_null0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma crc32_null0_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  a1 = Z_to_bv 64 0 -> mem_inv rsegs m ->
  evt rsegs (crc32_null0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c6c0) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros -> MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ a2) as Ra2.
  do 3 zstep. zstep. if_cases K0; zify_cond K0. 2:{ kill K0. }
  zstep. zstep. apply evt_done. unfold crc32_null0_post.
  do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition q0 : vep_pads := VPADS (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4)
                                  (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4).
Lemma q0_wf : vep_pads_wf q0. Proof. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Definition ztag : list byte := repeat (Z_to_bv 8 0) 8.
(* [comment removed for export] *)
Definition vep_tail0 : list cell :=
  Eval cbv [skipn vep_cells q0 p36 p124 p140 p196 p236 p268 p308] in skipn 2 (vep_cells (fun _ => 0) ztag q0).
Lemma vep_tail0_wf : cells_wf vep_tail0. Proof. cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Lemma vep_tail0_bytes : cells_bytes vep_tail0 = repeat (Z_to_bv 8 0) 304. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac chunks_hide_except FRAME :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?m _] =>
    lazymatch type of FRAME with rw_cells ?segs _ _ _ =>
      repeat match goal with
      | H : rw_cells segs m _ _ |- _ => first [ constr_eq H FRAME; fail 1 | hide H ]
      | H : ro_cells segs m _ _ |- _ => hide H
      | H : u8arr segs m _ _ |- _ => hide H
      end
    end
  end.
Local Ltac chunks_unhide :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?m _] =>
    repeat match goal with
    | H : kept (rw_cells _ m _ _) |- _ => unhide H
    | H : kept (ro_cells _ m _ _) |- _ => unhide H
    | H : kept (u8arr _ m _ _) |- _ => unhide H
    end
  end.
Local Ltac stub_begin FRAME lo hi :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?m _] =>
    lazymatch type of FRAME with rw_cells ?segs _ _ _ =>
      pose proof (munch_refl [(lo, hi)]%Z m) as MUstub; pose proof (wmono_refl segs m) as WMstub
    end
  end; chunks_hide_except FRAME.
Local Ltac stub_end MUstub WMstub :=
  lazymatch type of MUstub with munch ?W ?ma ?mb =>
    lazymatch type of WMstub with wmono ?segs _ _ =>
      repeat match goal with
      | H : kept (rw_cells segs ma ?B ?cs) |- _ =>
          unhide H; apply (rw_cells_transport segs W ma mb B cs) in H; [| exact MUstub| exact WMstub| cbn [disjoint_from]; simpl_sizes; slia]
      | H : kept (ro_cells segs ma ?B ?cs) |- _ =>
          unhide H; apply (ro_cells_transport segs W ma mb B cs) in H; [| exact MUstub| cbn [disjoint_from]; simpl_sizes; slia]
      | H : kept (u8arr segs ma ?B ?xs) |- _ =>
          unhide H; apply (u8arr_transport segs W ma mb B xs) in H; [| exact MUstub| exact WMstub| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia]
      end
    end
  end; clear MUstub WMstub.

Local Tactic Notation "klia" ne_hyp_list(hs) := clear - hs; lia.

(* [comment removed for export] *)
Local Ltac plia := zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Local Ltac avoids_false X :=
  lazymatch type of X with
  | _ \/ _ => destruct X as [X|X]; avoids_false X
  | False => destruct X
  | _ => try (lazymatch type of X with (_ <> _) /\ _ => destruct X as [_ X] end);
         first [ match goal with D : _ \/ _ |- _ => solve [ destruct D; plia ] end | plia ]
  end.
(* [comment removed for export] *)
Local Ltac plia2 := first [ plia | zify_prune; Zify.zify; xlia zchecker ].
Local Ltac avoids_solve ::=
  cbn [Cells.cells_size Cells.csize Nat.add length app];
  split; [ lia | intros ? ? X; unfold blk, nowhere in X; cbn beta in X; first [ avoids_false X | plia2 ] ].

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  Lemma VEP_Init_ok : VEP_Init_stmt.
  Proof.
    unfold VEP_Init_stmt. intros H flags lo. intros until T. intros AINV MI LIVEX Ha0 Ha1 Ha2 Ha3 Ha4 FL WS0 HENV HG IMG LBUD NBUD TP SP16 RA2 ST CEIL LO SPH K.
    rewrite Ha0, Ha1, Ha2, Ha3, Ha4.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutP0)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY.
    pose proof alloc_ceiling_val as ACV.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G16 GCE GHI | pose proof HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity.
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity.
    assert (Eresp : h_resp H = h_sp H + 1376) by reflexivity.
    assert (Ereq : h_req H = h_sp H + 1432) by reflexivity.
    assert (Ehd : h_hd H = h_sp H + 1040) by reflexivity.
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    destruct HENV as [GLOB HOBJ].
    assert (Ebss : h_bss H = 0x41830) by (destruct GLOB as [E _]; rewrite E; reflexivity).
    unfold VEPINIT_STACK, WSALLOC_STACK, CALLOC_STACK in *. unfold VEP_Init_entry.
    rewrite Evc, Ereq.
    (* [comment removed for export] *)
    (first [ pose proof (HOBJ) as dR_2; dand5 dR_2 as VC WK RQ RS HD | pose proof HOBJ as (VC & WK & RQ & RS & HD) ]).
    (first [ dex2 VC as vcpad vcrest; dand3 VC as LVP LVR VC | dand5 VC as vcpad vcrest LVP LVR VC | destruct VC as (vcpad & vcrest & LVP & LVR & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LWP LWR WK | dand5 WK as wkpad wkrest LWP LWR WK | destruct WK as (wkpad & wkrest & LWP & LWR & WK) ]).
    (first [ dex3 RQ as mid1 tl1 pd1; dand4 RQ as LM1 LT1 LP1 RQ | dand7 RQ as mid1 tl1 pd1 LM1 LT1 LP1 RQ | destruct RQ as (mid1 & tl1 & pd1 & LM1 & LT1 & LP1 & RQ) ]). (first [ dex4 RS as hd2 mid2 tl2 pd2; dand4 RS as LM2 LT2 LP2 RS | dand8 RS as hd2 mid2 tl2 pd2 LM2 LT2 LP2 RS | destruct RS as (hd2 & mid2 & tl2 & pd2 & LM2 & LT2 & LP2 & RS) ]).
    cbn [al_segs LayoutP0] in VC, WK, RQ, RS, HD.
    unfold vc_cells in VC. unfold wrk_cells in WK. unfold http_cells in RQ, RS.
    rewrite Evc, Eresp, Ewrk in VC. rewrite Ewrk in WK. rewrite Ereq, Ehd, Ews in RQ. rewrite Eresp, Ews in RS. rewrite Ehd in HD.
    (* [comment removed for export] *)
    assert (GLOBP : forall W mp mq, glob_ok LayoutP0 VI0 H mp -> munch W mp mq -> wmono rsegs mp mq ->
      (forall a, (0x41830 <= a < 0x41830 + 16 \/ h_sp H + 1488 <= a < h_sp H + 1488 + 752 \/ h_sp H + 2240 + 1304 <= a < h_sp H + 2240 + 1320) -> outside W a) ->
      glob_ok LayoutP0 VI0 H mq).
    { intros W mp mq G MUx WMx OUT. eapply (glob_ok_munch LayoutP0); [exact G| exact MUx| exact WMx|].
      intros a Ha. apply OUT. rewrite Ebss in Ha. unfold h_cp, h_vsc in Ha. exact Ha. }
    assert (HOBJP : forall W mp mq, hobj_ok LayoutP0 VI0 H mp -> munch W mp mq -> wmono rsegs mp mq ->
      (forall a, (h_sp H + 1040 + 16 <= a < h_sp H + 1040 + 24 \/ h_sp H + 1120 <= a < h_sp H + 1432 + 56) -> outside W a) ->
      hobj_ok LayoutP0 VI0 H mq).
    { intros W mp mq O MUx WMx OUT. eapply (hobj_ok_munch LayoutP0); [exact O| exact MUx| exact WMx|].
      intros a Ha. apply OUT. unfold h_hd, h_wrk, h_req, h_resp, h_vc in Ha. lia. }
    pose proof (munch_refl [(bv_unsigned sp - 8384, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 8384, bv_unsigned sp)]).
    { cbn. split; [left; lia| exact I]. }
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 64%nat ST.
    zstep. stub_begin FR (bv_unsigned sp + -64) (bv_unsigned sp). do 7 zstep. stub_end MUstub WMstub.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    pose proof (ainv_munch LayoutP0 A m _ md _ AINV MU WM CFP) as AINV1.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (crange_stack (L:=LayoutP0) A mx md (bv_unsigned sp - 64) 64 AINV1 ltac:(lia) ltac:(lia)
                    (rw_cells_mapped LayoutP0 mx _ _ FR ltac:(off_image_solve LayoutP0))) as CF;
      pose_cranges LayoutP0 A mx AINV1 end.
    eapply WS_Alloc_ok;
      [ exact AINV1 | assumption | exact LIVEX | rewrite Ews; reflexivity | reflexivity
      | eapply (ws0_obj_munch LayoutP0); [exact WS0| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]
      | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
      | exact HG
      | eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG]
      | revert LBUD; clear; intros; lia | revert NBUD; clear; intros; lia
      | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; exact ST | exact CEIL
      | rewrite unsigned_lit by lia; unfold WSALLOC_STACK, CALLOC_STACK; lia
      | rewrite unsigned_lit by lia; lia | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A1 m1 md1 AINV' MI' MDF ST' GLOB1 OUT.
    pose proof (as_lazy_nil A1 m1 md1 AINV') as [MDL' MDH'].
    rewrite unsigned_lit in OUT, ST' by lia. unfold WSALLOC_STACK, CALLOC_STACK in OUT.
    (* [comment removed for export] *)
    assert (XFER1 : forall Vc N, cframe LayoutP0 (owned A) (owned A1) (bv_unsigned sp - 64) 8320 Vc N m0 m1 ->
              (forall a, Vc a -> h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32) ->
              hobj_ok LayoutP0 VI0 H m1 /\ img_ok0 m1).
    { intros Vc N CFR HV. split.
      - eapply (hobj_ok_ccall LayoutP0 VI0 H A A1 m0 md m1); [exact AINV1| exact CFR| exact HG
          | eapply HOBJP; [exact HOBJ| exact MU| exact WM| intros a Ha; cbn [outside]; lia] | lia |].
        intros a Ha X. apply HV in X. unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_ws, h_wsbuf in *. lia.
      - eapply (img_ok0_ccall A A1 m0 md m1); [exact AINV1| exact CFR| unfold IMG0_HI; lia
          | intros a Ha X; apply HV in X; unfold IMG0_LO, IMG0_HI, h_ws, h_wsbuf in *; lia
          | eapply (img_ok0_munch _ m); [exact MU| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; lia| exact IMG]]. }
    (* [comment removed for export] *)
    destruct OUT as (wa & junkv & NZ & WS1' & NBv & FRESHwa & FRESHv & LIVEq & LBw & NLw & FRK).
    rename r into vep.
    - (* [comment removed for export] *)
      destruct (XFER1 _ _ FRK ltac:(intros a X; exact X)) as [HOBJ1 IMG1].
      clear ST. acall_xfer FRK. clear AINV1. rename ST' into ST.
      pose proof WS1' as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL WSC WEC LWA WAC LVEP | dand9 WS1x as id pad IDOK PADL WSC WEC LWA WAC LVEP | destruct WS1x as (id & pad & IDOK & PADL & WSC & WEC & LWA & WAC & LVEP) ]). clear WSC WEC WAC.
      (first [ pose proof ((as_live_ok A1 m1 md1 vep _ AINV' LVEP)) as dR_8; dand7 dR_8 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A1 m1 md1 vep _ AINV' LVEP) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]).
      assert (VEPbss : vep + 312 <= 0x10000 \/ 0x63000 <= vep) by (unfold in_image in VEPimg; cbn [al_image_lo al_image_hi LayoutP0] in VEPimg; lia).
      clear VEPimg.
      (first [ pose proof ((as_live_ok A1 m1 md1 wa _ AINV' LWA)) as dR_9; dand7 dR_9 as _ WA16 WAlo WAhi WAimg WAmap WAown | pose proof (as_live_ok A1 m1 md1 wa _ AINV' LWA) as (_ & WA16 & WAlo & WAhi & WAimg & WAmap & WAown) ]). clear WAimg.
      assert (NEwv : wa <> vep) by (intros ->; rewrite LVEP in LWA; discriminate LWA).
      pose proof (as_live_disjoint A1 m1 md1 wa 40 vep 312 AINV' LWA LVEP NEwv) as DJ.
      pose proof (munch_refl [(bv_unsigned sp - 8384, bv_unsigned sp); (vep, vep + 312)] m1) as MU2.
      pose proof (wmono_refl rsegs m1) as WM2.
      assert (CFP2 : client_fp LayoutP0 A1 [(bv_unsigned sp - 8384, bv_unsigned sp); (vep, vep + 312)]).
      { cbn. split; [left; lia|]. split; [right; left; exists vep, 312; split; [exact LVEP|lia]| exact I]. }
      (* [comment removed for export] *)
      pose proof (rw_cells_split_CB rsegs m1 vep [] 312 junkv [] [4; 4; 304]%nat NBv eq_refl) as NB3. clear NBv. cbn [mk_CB_cells app] in NB3.
      lazymatch type of NB3 with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
        pose proof (proj1 (rw_cells_app rsegs m1 vep [c0; c1] rest) NB3) as [NBa NBb] end.
      clear NB3. pose proof (rwc_eq _ _ _ (vep + 8) _ NBb ltac:(cbn; lia)) as NBb'. clear NBb. rename NBb' into NBb.
      rz_resume MDH' MDL'.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
      zstep. zstep. zstep. zstep.
      call memset_spec_z.
      1:{ exact NBb. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
      match goal with X : rw_cells rsegs _ (vep + 8) _ |- _ => rename X into NBz end.
      change (Z.to_nat 304) with 304%nat in NBz. change (0 mod 256) with 0 in NBz.
      (* [comment removed for export] *)
      lazymatch type of NBz with rw_cells _ ?mx _ _ =>
        apply (rw_cells_recast rsegs mx (vep + 8) _ vep_tail0) in NBz; [| exact vep_tail0_wf | rewrite vep_tail0_bytes; reflexivity ];
        lazymatch type of NBa with rw_cells _ _ _ ?hd =>
          pose proof (proj2 (rw_cells_app rsegs mx vep hd vep_tail0) (conj NBa NBz)) as NB end end.
      clear NBa NBz. unfold vep_tail0 in NB. cbn [app] in NB.
      replace (h_sp H + 1040 + 16) with (h_sp H + 1056) in HD by lia.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      apply rz_stop.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        pose proof (ainv_munch LayoutP0 A1 m1 mx md1 _ AINV' MU2 WM2 CFP2) as AINV2;
        pose_cranges LayoutP0 A1 mx AINV2 end.
      eapply VSB_new_auto_cps;
        [ exact AINV2 | assumption | exists wa, 40; exact LWA
        | revert LBUD LBw; clear; intros; lia | revert NBUD NLw; clear; intros; lia
        | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; exact ST | exact CEIL
        | rewrite unsigned_lit by lia; unfold NEWAUTO_STACK, CALLOC_STACK; lia
        | rewrite unsigned_lit by lia; lia | ].
      intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' S A2 m5 md5 AINV5 MI5 MDF5 ST5 OUT2.
      pose proof (as_lazy_nil A2 m5 md5 AINV5) as [MDL5 MDH5].
      rewrite unsigned_lit in ST5, OUT2 by lia. unfold NEWAUTO_STACK, CALLOC_STACK in OUT2.
      (* [comment removed for export] *)
      lazymatch type of MU2 with munch _ _ ?mx =>
        assert (CFa : cframe LayoutP0 (owned A) (owned A1) (bv_unsigned sp) 8384
                        (fun a => h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32)
                        (fun a => blk wa 40 a \/ blk vep 312 a) m mx)
          by (eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m m0 m1 mx _ _);
              [ exact MU | | exact FRK | lia | lia | intros a X; exact X | intros a X; left; exact X
              | exact MU2 | | eapply (window_mapped LayoutP0 _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia] ];
              [ intros a Ha NO; cbn [outside] in NO; lia
              | intros a Ha NO; cbn [outside] in NO; unfold blk; lia ]);
        assert (XFER2 : forall N, cframe LayoutP0 (owned A1) (owned A2) (bv_unsigned sp + -64) 8256 nowhere N mx m5 ->
                  hobj_ok LayoutP0 VI0 H m5 /\ img_ok0 m5 /\ glob_ok LayoutP0 VI0 H m5)
          by (intros N CFR; split; [|split];
              [ eapply (hobj_ok_ccall LayoutP0 VI0 H A1 A2 mx md1 m5); [exact AINV2| exact CFR| exact HG
                  | eapply HOBJP; [exact HOBJ1| exact MU2| exact WM2| intros a Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ] | lia | intros a _ X; exact X]
              | eapply (img_ok0_ccall A1 A2 mx md1 m5); [exact AINV2| exact CFR| unfold IMG0_HI; lia| intros a _ X; exact X
                  | eapply (img_ok0_munch _ m1); [exact MU2| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ| exact IMG1]]
              | eapply (glob_ok_ccall LayoutP0 VI0 H A1 A2 mx md1 m5); [exact AINV2| exact CFR| exact HG
                  | eapply GLOBP; [exact GLOB1| exact MU2| exact WM2| intros a Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ]
                  | lia| lia
                  | rewrite Ebss; cbn; lia| rewrite Ebss; cbn; lia
                  | intros i Hi; rewrite Ebss; cbn; unfold p0_static; lia
                  | rewrite Ebss; cbn; change (al_errno LayoutP0) with 0x420b4; lia
                  | intros a _ X; exact X] ]);
        assert (WS1x : forall N, cframe LayoutP0 (owned A1) (owned A2) (bv_unsigned sp + -64) 8256 nowhere N mx m5 ->
                  a_live A2 wa = Some 40 -> a_live A2 vep = Some 312 -> ws1_obj LayoutP0 H A2 m5 wa vep)
          by (intros N CFR L1 L2; eapply (ws1_obj_ccall LayoutP0 H A1 A2 mx md1 m5); [exact AINV2| exact CFR| exact HG
              | eapply (ws1_obj_munch LayoutP0); [exact WS1'| exact MU2| exact WM2| intros a Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ]
              | lia | lia | exact L1 | exact L2 | intros a _ X; exact X])
      end.
      clear XFER1.
      (* [comment removed for export] *)
      destruct OUT2 as (b & NZS & VSB5 & FRESHS & FRESHb & LIVEq5 & LBn & NLn & FRK2).
      + (* [comment removed for export] *)
        (first [ pose proof ((XFER2 _ FRK2)) as dR_14; dand3 dR_14 as HOBJ5 IMG5 GLOB5 | destruct (XFER2 _ FRK2) as (HOBJ5 & IMG5 & GLOB5) ]). clear XFER2.
        assert (NESv : S <> vep) by (intros ->; rewrite LVEP in FRESHS; discriminate FRESHS).
        assert (NEbv : b <> vep) by (intros ->; rewrite LVEP in FRESHb; discriminate FRESHb).
        assert (NESw : S <> wa) by (intros ->; rewrite LWA in FRESHS; discriminate FRESHS).
        assert (NEbw : b <> wa) by (intros ->; rewrite LWA in FRESHb; discriminate FRESHb).
        assert (LWA5 : a_live A2 wa = Some 40) by (rewrite (LIVEq5 wa (not_eq_sym NESw) (not_eq_sym NEbw)); exact LWA).
        assert (LVEP5 : a_live A2 vep = Some 312) by (rewrite (LIVEq5 vep (not_eq_sym NESv) (not_eq_sym NEbv)); exact LVEP).
        pose proof (WS1x _ FRK2 LWA5 LVEP5) as WS1_5. clear WS1x.
        pose proof VSB5 as VSBx. (first [ dand6 VSBx as _ _ LS5 LB5 NESb _ | destruct VSBx as (_ & _ & LS5 & LB5 & NESb & _) ]). cbn [vb_buf vb_size vsb_fresh] in LB5, NESb.
        (first [ pose proof ((as_live_ok A2 m5 md5 S _ AINV5 LS5)) as dR_16; dand7 dR_16 as _ S16 Slo Shi _ _ _ | pose proof (as_live_ok A2 m5 md5 S _ AINV5 LS5) as (_ & S16 & Slo & Shi & _ & _ & _) ]).
        (first [ pose proof ((as_live_ok A2 m5 md5 b _ AINV5 LB5)) as dR_17; dand7 dR_17 as _ B16 Blo Bhi _ _ _ | pose proof (as_live_ok A2 m5 md5 b _ AINV5 LB5) as (_ & B16 & Blo & Bhi & _ & _ & _) ]).
        pose proof (as_live_disjoint A2 m5 md5 S 40 vep 312 AINV5 LS5 LVEP5 NESv) as DJS.
        pose proof (as_live_disjoint A2 m5 md5 b 16 vep 312 AINV5 LB5 LVEP5 NEbv) as DJb.
        clear ST. acall_xfer FRK2. clear AINV2. rename ST5 into ST.
        pose proof (munch_refl [(bv_unsigned sp - 8384, bv_unsigned sp); (vep, vep + 312)] m5) as MU3.
        pose proof (wmono_refl rsegs m5) as WM3.
        assert (CFP3 : client_fp LayoutP0 A2 [(bv_unsigned sp - 8384, bv_unsigned sp); (vep, vep + 312)]).
        { cbn. split; [left; lia|]. split; [right; left; exists vep, 312; split; [exact LVEP5|lia]| exact I]. }
        rz_resume MDH5 MDL5.
        (* [comment removed for export] *)
        zstep. zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
        zstep. if_cases KC; zify_cond KC. 2:{ kill KC. } clear KC.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        call crc32_null0_spec. 1:{ reflexivity. } 1:{ assumption. }
        zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        call crc32_null0_spec. 1:{ reflexivity. } 1:{ assumption. }
        zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep. chunks_hide_except FR. do 7 zstep. chunks_unhide. zstep.
        try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
        release_frame FR ST (bv_unsigned sp).
        zstep. cps_done.
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?my _) _) _ =>
          lazymatch type of MU3 with munch ?W _ _ =>
            pose proof (ainv_munch LayoutP0 A2 m5 my md5 W AINV5 MU3 WM3 CFP3) as AINV9 end end.
        eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ vep A2 _ md5);
          [ exact AINV9 | assumption | eapply md_frame_trans; [exact MDF| exact MDF5] | exact ST
          | split; [eapply GLOBP; [exact GLOB5| exact MU3| exact WM3| intros a Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ]
                  | eapply HOBJP; [exact HOBJ5| exact MU3| exact WM3| intros a Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ]]
          | eapply (img_ok0_munch _ m5); [exact MU3| intros a Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ| exact IMG5]
          | ].
        exists wa, ztag, q0, b. split; [exact NZ|].
        split; [eapply (ws1_obj_munch LayoutP0); [exact WS1_5| exact MU3| exact WM3| intros a Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ]|].
        exists S.
        split. { split; [exact LVEP5|]. split; [cbn [al_segs LayoutP0]; exact NB| split; [reflexivity| exact q0_wf]]. }
        split; [exact NZS|].
        split. { eapply (vsb_obj_munch LayoutP0); [exact VSB5| exact MU3| exact WM3
                   | cbn [disjoint_from vb_buf vb_size vsb_fresh]; refine (conj _ (conj _ I)); lia
                   | cbn [disjoint_from vb_buf vb_size vsb_fresh]; refine (conj _ (conj _ I)); lia]. }
        split; [rewrite <- (LIVEq S NESw NESv); exact FRESHS|].
        split; [rewrite <- (LIVEq b NEbw NEbv); exact FRESHb|].
        split; [exact NESv|]. split; [exact NEbv|]. split; [exact NESw|]. split; [exact NEbw|].
        split; [exact FRESHwa|]. split; [exact FRESHv|].
        split; [intros p P1 P2 P3 P4; rewrite (LIVEq5 p P3 P4); apply LIVEq; [exact P1| exact P2]|].
        split; [revert LBw LBn; clear; intros; lia|]. split; [revert NLw NLn; clear; intros; lia|].
        lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?mfin =>
          lazymatch type of CFa with cframe _ _ _ _ _ _ _ _ ?mx =>
            assert (CF2 : cframe LayoutP0 (owned A1) (owned A2) (bv_unsigned sp) 8384
                            (fun a => blk vep 312 a \/ (h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32))
                            (fun a => blk S 40 a \/ blk b 16 a) mx mfin)
              by (eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ mx mx m5 _ [] _);
                  [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK2 | lia | lia
                  | intros a X; destruct X | intros a X; left; exact X | exact MU3 |
                  | eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | lia | lia] ];
                  intros a Ha NO; cbn [outside] in NO; unfold blk; lia);
            eapply (cframe_seq LayoutP0 _ _ _ _ _ _ _ _ _ _ _ _ _ m mx mfin CFa CF2); [lia | lia
              | eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | lia | lia]
              | intros a X; exact X | intros a [X|X]; [left; right; exact X| right; exact X]
              | intros a [X|[X|[X|X]]]; [left; left; exact X| left; right; exact X| right; left; left; exact X| right; left; right; exact X] ]
          end end.
  Qed.
End S.
