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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World U_Img ImgU U_Cov8m U_Leaves.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_WS2nv.

Module U_WS0s9.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World U_Img ImgU U_Cov8m U_Leaves.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import RU_mz6g U_WS2nv.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition keptA (P : Prop) : Prop := P.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hide_slowA :=
  repeat match goal with H : (?x <> ?y) |- _ => (lazymatch type of H with ?T__ => change (keptA T__) in H end) end;
  repeat match goal with H : (?x mod ?y = ?z)%Z |- _ => (lazymatch type of H with ?T__ => change (keptA T__) in H end) end.
Ltac unhide_slowA := repeat match goal with H : keptA _ |- _ => (lazymatch type of H with keptA ?T__ => change T__ in H | _ => idtac end) end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ws_emu_alloc_entry : Z := 0x18c20.
(* [comment removed for export] *)
Definition WSEMU_STACK : Z := 64 + CALLOC_STACK.

(* [comment removed for export] *)
Definition ws_changed (H : henv) (a : Z) : Prop :=
  h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Lemma ws_emu_alloc_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (H : henv) (lo : Z) (T : TSet),
      ainv A m md -> mem_inv rsegs m -> (exists r k, a_live A r = Some k) ->
      a0 = Z_to_bv 64 (h_ws H) -> a1 = Z_to_bv 64 312 ->
      ws0_obj LayoutPU H m -> glob_ok LayoutPU VIU H m -> henv_geom H -> img_okU m ->
      a_livebytes A + 352 <= LIVE_MAX -> a_nlive A + 2 <= NLIVE_MAX ->
      tp = al_tp LayoutPU -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + WSEMU_STACK <= bv_unsigned sp ->
      bv_unsigned sp <= h_sp H ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> glob_ok LayoutPU VIU H m' ->
          (* [comment removed for export] *)
              (exists vep junk, r <> 0 /\ ws1_obj LayoutPU H A' m' r vep /\ rw_cells rsegs m' vep [CB 312 junk] /\
               a_live A r = None /\ a_live A vep = None /\
               (forall p, p <> r -> p <> vep -> a_live A' p = a_live A p) /\
               a_livebytes A' = a_livebytes A + 352 /\ a_nlive A' = a_nlive A + 2 /\
               cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) WSEMU_STACK
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
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY.
    pose proof alloc_ceiling_val as ACV.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G16 GCE GHI | pose proof HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    assert (Ebss : h_bss H = 0x41bd0) by (destruct GLOB as [E _]; rewrite E; reflexivity).
    assert (WS8 : (h_sp H + 1080) mod 8 = 0) by (apply align_mod8_of16; [exact G16| reflexivity]).
    assert (WE8 : (h_sp H + 16) mod 8 = 0) by (apply align_mod8_of16; [exact G16| reflexivity]).
    assert (WL8 : (h_sp H + 32) mod 8 = 0) by (apply align_mod8_of16; [exact G16| reflexivity]).
    pose proof IMG as IMG0. (first [ dand5 IMG as _ GMS _ GCP _ | destruct IMG as (_ & GMS & _ & GCP & _) ]). unfold GOT_cp in GCP. unfold GOT_memset in GMS.
    unfold WSEMU_STACK, CALLOC_STACK in *. unfold ws_emu_alloc_entry.
    rewrite Ews.
    (* [comment removed for export] *)
    (first [ dex1 WS0 as id; dand3 WS0 as IDOK WSC WEC | dand4 WS0 as id IDOK WSC WEC | destruct WS0 as (id & IDOK & WSC & WEC) ]). cbn [al_segs LayoutPU] in WSC, WEC.
    assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
    unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
    unfold wsemu_cells, wsemu_WS0 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
    rewrite Ews in WSC. rewrite Ewb in WSC, WEC.
    (* [comment removed for export] *)
    assert (WS0P : forall mq,
      rw_cells rsegs mq (h_sp H + 1080) [C4 (Z_to_bv 64 WS_MAGIC); CB 4 id; C8 (Z_to_bv 64 (h_sp H + 16)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_sp H + 16 + 1016))] ->
      rw_cells rsegs mq (h_sp H + 16) [C4 (Z_to_bv 64 WS_EMU_MAGIC); C4 (Z_to_bv 64 1016); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_sp H + 32))] ->
      ws0_obj LayoutPU H mq).
    { intros mq X1 X2. apply (ws0_obj_intro LayoutPU H mq id IDOK); cbn [al_segs LayoutPU]; rewrite ?Ews, ?Ewb; [exact X1|].
      unfold wsemu_cells, wsemu_WS0. cbn [we_len we_ws we_first we_last]. replace (h_sp H + 16 + 16) with (h_sp H + 32) by lia. exact X2. }
    replace (h_sp H + 16 + 16) with (h_sp H + 32) in WEC by lia.
    assert (GLOBP : forall W mp mq, glob_ok LayoutPU VIU H mp -> munch W mp mq -> wmono rsegs mp mq ->
      (forall a, (0x41bd0 <= a < 0x41bd0 + 16 \/ h_sp H + 1488 <= a < h_sp H + 1488 + 752 \/ h_sp H + 2240 + 1304 <= a < h_sp H + 2240 + 1320) -> outside W a) ->
      glob_ok LayoutPU VIU H mq).
    { intros W mp mq G MUx WMx OUT. eapply (glob_ok_munch LayoutPU); [exact G| exact MUx| exact WMx|].
      intros a Ha. apply OUT. rewrite Ebss in Ha. unfold h_cp, h_vsc in Ha. exact Ha. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8288, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutPU A [(bv_unsigned sp - 8288, bv_unsigned sp)]).
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
      | |- img_okU _ => eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG0]
      | |- mem_inv _ _ => assumption
      | |- @eq word _ _ => rewrite ?Ews; reflexivity
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    zstep. zstep. if_cases K0; zify_cond K0. { exfalso. apply K0. apply land7_of_mod8; [lia| exact WS8]. } clear K0.
    zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    zstep. zstep.
    call_lit (ws_emu_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h_sp H + 1080)
              (WSR id (h_sp H + 16) 0 0 (h_sp H + 16 + 1016)) (WER 1016 0 0 (h_sp H + 32))) by (idtac;
      lazymatch goal with
      | |- rw_cells _ _ _ (ws_cells _) => exact WSC
      | |- rw_cells _ _ _ (wsemu_cells _) => exact WEC
      | |- length _ = _ => exact IDL
      | |- mem_inv _ _ => assumption
      | |- @eq word _ _ => reflexivity
      | |- _ => cbn [ws_s]; first [exact WS8 | exact WE8 | lia]
      end).
    cbn [ws_s].
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. apply K1. apply land7_of_mod8; [lia| exact WE8]. } clear K1.
    zstep. zstep. if_cases K1; zify_cond K1. { kill K1. } clear K1.
    zstep. zstep. if_cases K1; zify_cond K1. { exfalso. apply K1. apply land7_of_mod8; [lia| exact WL8]. } clear K1.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K1; zify_cond K1. { kill K1. } clear K1.
    zstep. zstep. if_cases K1; zify_cond K1. { exfalso. apply K1. apply land7_of_mod8; [lia| exact WL8]. } clear K1.
    zstep. zstep. if_cases K1; zify_cond K1. 2:{ kill K1. } clear K1.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ kill K2. } clear K2.
    zstep. if_cases K3; zify_cond K3. 2:{ kill K3. } clear K3.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    apply rz_stop.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (ainv_munch LayoutPU A m mx md _ AINV MU WM CFP) as AINV1;
      pose_cranges LayoutPU A mx AINV1 end.
    eapply (as_calloc_cps (L:=LayoutPU)) with (cnt := 1) (sz := 40);
      [ exact AINV1 | assumption | exact LIVEX | reflexivity | reflexivity | lia | lia | lia | lia | lia | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; unfold CALLOC_STACK; lia
      | rewrite unsigned_lit by lia; eapply (stk_mapped (L:=LayoutPU)); [exact ST| exact CEIL | unfold CALLOC_STACK; lia | lia]
      | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' wa A1 m1 md1 AINV' MI' MDF OUT FRK.
    pose proof (as_lazy_nil A1 m1 md1 AINV') as [MDL' MDH'].
    rewrite unsigned_lit in FRK by lia.
    (* [comment removed for export] *)
    lazymatch type of FRK with frame_ok _ _ _ _ _ _ _ ?mx _ =>
      assert (GLOB1 : glob_ok LayoutPU VIU H m1)
        by (eapply (glob_ok_ccall LayoutPU VIU H A A1 mx md m1); [exact AINV1| apply (cframe_of_frame_ok LayoutPU); exact FRK| exact HG
            | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
            | lia| unfold CALLOC_STACK; lia
            | rewrite Ebss; cbn; lia| rewrite Ebss; cbn; lia
            | intros i Hi; rewrite Ebss; cbn; unfold pu_static; lia
            | rewrite Ebss; cbn; change (al_errno LayoutPU) with 0x42454; lia
            | intros a _ X; exact X]);
      assert (IMG1 : img_okU m1)
        by (eapply (img_okU_ccall A A1 mx md m1); [exact AINV1| apply (cframe_of_frame_ok LayoutPU); exact FRK
            | unfold IMGU_HI, CALLOC_STACK; lia| intros a _ X; exact X
            | eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG0]])
    end.
    clear GCP GMS.
    destruct OUT as (NZ & FRESH & LIVEwa & LIVEq & ZERO & LB1 & NL1).
    - (* [comment removed for export] *)
      change (1 * 40) with 40 in LB1.
      change (1 * 40) with 40 in LIVEwa, ZERO, FRK.
      acall_xfer FRK. clear AINV1.
      (first [ pose proof ((as_live_ok A1 m1 md1 wa _ AINV' LIVEwa)) as dR_4; dand7 dR_4 as _ WA16 WAlo WAhi WAimg WAmap WAown | pose proof (as_live_ok A1 m1 md1 wa _ AINV' LIVEwa) as (_ & WA16 & WAlo & WAhi & WAimg & WAmap & WAown) ]).
      assert (WAbss : wa + 40 <= 0x10000 \/ 0x64000 <= wa) by (unfold in_image in WAimg; cbn [al_image_lo al_image_hi LayoutPU] in WAimg; lia).
      clear WAimg.
      (first [ pose proof ((newblock_cells (L:=LayoutPU) A1 m1 md1 wa _ AINV' LIVEwa)) as dR_5; dex1 dR_5 as junk1; dand3 dR_5 as LJ1 NB1 CRwa | pose proof ((newblock_cells (L:=LayoutPU) A1 m1 md1 wa _ AINV' LIVEwa)) as dR_5; dand4 dR_5 as junk1 LJ1 NB1 CRwa | destruct (newblock_cells (L:=LayoutPU) A1 m1 md1 wa _ AINV' LIVEwa) as (junk1 & LJ1 & NB1 & CRwa) ]).
      cbn [al_segs LayoutPU] in NB1.
      pose proof (all_zero_CB rsegs m1 wa _ junk1 NB1 ZERO) as EJ. change (Z.to_nat 40) with 40%nat in EJ. subst junk1.
      apply (rw_cells_recast rsegs m1 wa _
               [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0];
                C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in NB1; [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity | reflexivity].
      pose proof (munch_refl [(bv_unsigned sp - 8288, bv_unsigned sp); (wa, wa + 40)] m1) as MU2.
      pose proof (wmono_refl rsegs m1) as WM2.
      assert (CFP2 : client_fp LayoutPU A1 [(bv_unsigned sp - 8288, bv_unsigned sp); (wa, wa + 40)]).
      { cbn. split; [left; lia|]. split; [right; left; exists wa, 40; split; [exact LIVEwa|lia]| exact I]. }
      rz_resume MDH' MDL'.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
      zstep. zstep. zstep. if_cases KZ; zify_cond KZ. { exfalso. apply KZ. apply land7_of_mod8; [lia| apply mod8_of_mod16; exact WA16]. } clear KZ.
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KL; zify_cond KL. { kill KL. } clear KL.
      zstep. zstep. zstep.
      apply rz_stop. hide_slowA.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        pose proof (ainv_munch LayoutPU A1 m1 mx md1 _ AINV' MU2 WM2 CFP2) as AINV2;
        pose_cranges LayoutPU A1 mx AINV2 end.
      eapply (as_malloc_cps (L:=LayoutPU)) with (n := 312);
        [ exact AINV2 | assumption | exists wa, 40; exact LIVEwa | reflexivity | lia | rewrite NREQ_CAP_eq; lia | lia | lia | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; unfold MALLOC_STACK; lia
        | rewrite unsigned_lit by lia; eapply (stk_mapped (L:=LayoutPU)); [exact ST| exact CEIL | unfold MALLOC_STACK; lia | lia]
        | ].
      intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' vep A2 m3 md3 AINV3 MI3 MDF3 OUT2 FRK2.
      pose proof (as_lazy_nil A2 m3 md3 AINV3) as [MDL3 MDH3].
      rewrite unsigned_lit in FRK2 by lia.
      (* [comment removed for export] *)
      lazymatch type of MU2 with munch _ _ ?mx =>
        assert (CFa : cframe LayoutPU (owned A) (owned A1) (bv_unsigned sp) 8288 nowhere (blk wa 40) m mx)
          by (eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m _ m1 _ _ _);
              [ exact MU | | exact FRK | unfold CALLOC_STACK; lia | lia | intros a X; destruct X | intros a X; left; exact X
              | exact MU2 | | eapply (window_mapped LayoutPU _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia] ];
              [ intros a Ha NO; cbn [outside] in NO; lia
              | intros a Ha NO; cbn [outside] in NO; unfold blk; lia ]);
        assert (GLOB2 : glob_ok LayoutPU VIU H m3)
          by (eapply (glob_ok_ccall LayoutPU VIU H A1 A2 mx md1 m3); [exact AINV2| apply (cframe_of_frame_ok LayoutPU); exact FRK2| exact HG
              | eapply GLOBP; [exact GLOB1| exact MU2| exact WM2| intros a Ha; cbn [outside]; lia]
              | lia| unfold MALLOC_STACK; lia
              | rewrite Ebss; cbn; lia| rewrite Ebss; cbn; lia
              | intros i Hi; rewrite Ebss; cbn; unfold pu_static; lia
              | rewrite Ebss; cbn; change (al_errno LayoutPU) with 0x42454; lia
              | intros a _ X; exact X]);
        assert (IMG2 : img_okU m3)
          by (eapply (img_okU_ccall A1 A2 mx md1 m3); [exact AINV2| apply (cframe_of_frame_ok LayoutPU); exact FRK2
              | unfold IMGU_HI, MALLOC_STACK; lia| intros a _ X; exact X
              | eapply (img_okU_munch _ m1); [exact MU2| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG1]])
      end.
      clear MU MU2 WM WM2 CFP CFP2 FRK. unhide_slowA.
      destruct OUT2 as (NZv & FRESHv & LIVEv & LIVEq3 & LB2 & NL2).
      + (* [comment removed for export] *)
        acall_xfer FRK2. clear AINV2.
        assert (NEwv : wa <> vep) by (intros ->; rewrite FRESHv in LIVEwa; discriminate LIVEwa).
        assert (LIVEwa3 : a_live A2 wa = Some 40) by (rewrite (LIVEq3 wa NEwv); exact LIVEwa).
        (first [ pose proof ((as_live_ok A2 m3 md3 vep _ AINV3 LIVEv)) as dR_7; dand7 dR_7 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A2 m3 md3 vep _ AINV3 LIVEv) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]). clear VEPimg.
        (first [ pose proof ((newblock_cells (L:=LayoutPU) A2 m3 md3 vep _ AINV3 LIVEv)) as dR_8; dex1 dR_8 as junkv; dand3 dR_8 as LJv NBv CRv | pose proof ((newblock_cells (L:=LayoutPU) A2 m3 md3 vep _ AINV3 LIVEv)) as dR_8; dand4 dR_8 as junkv LJv NBv CRv | destruct (newblock_cells (L:=LayoutPU) A2 m3 md3 vep _ AINV3 LIVEv) as (junkv & LJv & NBv & CRv) ]).
        cbn [al_segs LayoutPU] in NBv. change (Z.to_nat 312) with 312%nat in NBv, LJv.
        pose proof (as_live_disjoint A2 m3 md3 wa 40 vep 312 AINV3 LIVEwa3 LIVEv NEwv) as DJ.
        pose proof (munch_refl [(bv_unsigned sp - 8288, bv_unsigned sp); (wa, wa + 40); (h_sp H + 16, h_sp H + 16 + 32)] m3) as MU3.
        pose proof (wmono_refl rsegs m3) as WM3.
        assert (CFP3 : client_fp LayoutPU A2 [(bv_unsigned sp - 8288, bv_unsigned sp); (wa, wa + 40); (h_sp H + 16, h_sp H + 16 + 32)]).
        { cbn. split; [left; lia|]. split; [right; left; exists wa, 40; split; [exact LIVEwa3|lia]|]. split; [left; lia| exact I]. }
        rz_resume MDH3 MDL3.
        (* [comment removed for export] *)
        zstep. zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. if_cases KN; zify_cond KN. { kill KN. } clear KN.
        (* [comment removed for export] *)
        zstep. zstep. if_cases KN; zify_cond KN. { exfalso. apply KN. apply land7_of_mod8; [lia| exact WL8]. } clear KN.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. do 5 zstep. zstep. zstep.
        try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
        release_frame FR ST (bv_unsigned sp).
        cps_done. hide_slowA.
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          lazymatch type of MU3 with munch ?W _ _ =>
            pose proof (ainv_munch LayoutPU A2 m3 mx md3 W AINV3 MU3 WM3 CFP3) as AINV9 end end.
        eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ wa A2 _ md3);
          [ exact AINV9 | assumption | eapply md_frame_trans; [exact MDF| exact MDF3] | exact ST
          | eapply GLOBP; [exact GLOB2| exact MU3| exact WM3| intros a Ha; cbn [outside]; lia] | ].
        exists vep, junkv. split; [exact NZ|].
        split.
        { apply (ws1_obj_intro LayoutPU H A2 _ wa vep id (repeat (Z_to_bv 8 0) 4) IDOK eq_refl); cbn [al_segs LayoutPU].
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
          assert (CF2 : cframe LayoutPU (owned A1) (owned A2) (bv_unsigned sp) 8288 (fun a => blk wa 40 a \/ ws_changed H a) (blk vep 312) m0 mfin)
            by (eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m0 m0 m3 _ [] _);
                [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK2 | unfold MALLOC_STACK; lia | lia
                | intros a X; destruct X | intros a X; left; exact X | exact MU3 |
                | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia] ];
                intros a Ha NO; cbn [outside] in NO; unfold ws_changed, h_ws, h_wsbuf, blk; lia);
          eapply (cframe_seq LayoutPU _ _ _ _ _ _ _ _ _ _ _ _ _ m m0 mfin CFa CF2); [lia | lia
            | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia]
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
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY.
    pose proof alloc_ceiling_val as ACV.
    (first [ pose proof (HG) as dR_9; dand3 dR_9 as G16 GCE GHI | pose proof HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    assert (Ebss : h_bss H = 0x41bd0) by (destruct GLOB as [E _]; rewrite E; reflexivity).
    unfold WSALLOC_STACK, CALLOC_STACK in *. unfold WS_Alloc_entry.
    assert (GLOBP : forall W mp mq, glob_ok LayoutPU VIU H mp -> munch W mp mq -> wmono rsegs mp mq ->
      (forall a, (0x41bd0 <= a < 0x41bd0 + 16 \/ h_sp H + 1488 <= a < h_sp H + 1488 + 752 \/ h_sp H + 2240 + 1304 <= a < h_sp H + 2240 + 1320) -> outside W a) ->
      glob_ok LayoutPU VIU H mq).
    { intros W mp mq G MUx WMx OUT. eapply (glob_ok_munch LayoutPU); [exact G| exact MUx| exact WMx|].
      intros a Ha. apply OUT. rewrite Ebss in Ha. unfold h_cp, h_vsc in Ha. exact Ha. }
    pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutPU A [(bv_unsigned sp - 8320, bv_unsigned sp)]).
    { cbn. split; [left; lia| exact I]. }
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 32%nat ST.
    do 5 zstep.
    (* [comment removed for export] *)
    zstep. if_cases KB; zify_cond KB. { kill KB. } clear KB.
    zstep. zstep. zstep.
    apply rz_stop.
    pose proof (ainv_munch LayoutPU A m _ md _ AINV MU WM CFP) as AINV1.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (crange_stack (L:=LayoutPU) A mx md (bv_unsigned sp - 32) 32 AINV1 ltac:(lia) ltac:(lia)
                    (rw_cells_mapped LayoutPU mx _ _ FR ltac:(off_image_solve LayoutPU))) as CF end.
    eapply ws_emu_alloc_cps;
      [ exact AINV1 | assumption | exact LIVEX | rewrite Ews; reflexivity | reflexivity
      | eapply (ws0_obj_munch LayoutPU); [exact WS0| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]
      | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
      | exact HG
      | eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG]
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
        assert (IMG' : img_okU m')
          by (eapply (img_okU_ccall A A' mx md m'); [exact AINV1| exact FRK| unfold IMGU_HI; lia| intros a Ha X; cbn beta in X; unfold IMGU_LO, IMGU_HI, h_ws, h_wsbuf in *; lia
              | eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG]]) end.
      acall_xfer FRK. clear AINV1. rename ST' into ST.
      pose proof WS1' as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL WSC WEC LWA WAC LVEP | dand9 WS1x as id pad IDOK PADL WSC WEC LWA WAC LVEP | destruct WS1x as (id & pad & IDOK & PADL & WSC & WEC & LWA & WAC & LVEP) ]). cbn [al_segs LayoutPU] in WSC, WEC, WAC.
      (first [ pose proof ((as_live_ok A' m' md' r _ AINV' LWA)) as dR_11; dand7 dR_11 as _ WA16 WAlo WAhi WAimg WAmap WAown | pose proof (as_live_ok A' m' md' r _ AINV' LWA) as (_ & WA16 & WAlo & WAhi & WAimg & WAmap & WAown) ]). clear WAimg.
      (first [ pose proof ((as_live_ok A' m' md' vep _ AINV' LVEP)) as dR_12; dand7 dR_12 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A' m' md' vep _ AINV' LVEP) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]). clear VEPimg.
      unfold wsalloc_cells, wsalloc_WS1 in WAC. cbn [wa_off wa_len wa_ptr wa_next wa_prev] in WAC.
      lazymatch type of MU with munch ?W _ _ =>
        pose proof (munch_refl W m') as MU2; pose proof (wmono_refl rsegs m') as WM2;
        assert (CFP2 : client_fp LayoutPU A' W) by (cbn; split; [left; lia| exact I]) end.
      rz_resume MDH' MDL'.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      call_lit (WS_Assert_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H (Some (A', r, vep)) lo) by (idtac;
        lazymatch goal with
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
        | |- ws_state _ _ _ => cbn [ws_state]; split; [exact WS1'| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [lia | exact WA16]]
        | |- glob_ok _ _ _ _ => exact GLOB'
        | |- henv_geom _ => exact HG
        | |- img_okU _ => exact IMG'
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => rewrite ?Ews; reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
      zstep. zstep. if_cases KZ; zify_cond KZ. { exfalso. apply KZ. apply land7_of_mod8; [lia| apply mod8_of_mod16; exact WA16]. } clear KZ.
      zstep. zstep. if_cases KV; zify_cond KV. { kill KV. } clear KV.
      (* [comment removed for export] *)
      pose proof IMG' as IMGx.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (IMGc : img_okU mx) by (eapply (img_okU_munch _ m'); [exact MU2| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG']) end.
      (first [ dand5 IMGc as _ _ _ GCP _ | destruct IMGc as (_ & _ & _ & GCP & _) ]). unfold GOT_cp in GCP. cbn [al_segs LayoutPU] in GCP.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (GLOBc : glob_ok LayoutPU VIU H mx) by (eapply GLOBP; [exact GLOB'| exact MU2| exact WM2| intros a Ha; cbn [outside]; lia]) end.
      (first [ pose proof (GLOBc) as dR_14; dand4 dR_14 as EBSS BSS CP _ | pose proof GLOBc as (EBSS & BSS & CP & _) ]). rewrite EBSS in BSS. cbn [vi_bss VIU al_segs LayoutPU] in BSS. cbn [al_segs LayoutPU] in CP.
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases KD; zify_cond KD. 2:{ kill KD. } clear KD.
      (* [comment removed for export] *)
      zstep. do 4 zstep. zstep. zstep.
      try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      cps_done.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        lazymatch type of MU2 with munch ?W _ _ =>
          pose proof (ainv_munch LayoutPU A' m' mx md' W AINV' MU2 WM2 CFP2) as AINV9 end end.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ vep A' _ md');
        [ exact AINV9 | assumption | exact MDF | exact ST
        | eapply GLOBP; [exact GLOB'| exact MU2| exact WM2| intros a Ha; cbn [outside]; lia] | ].
      exists r, junkv. split; [lia|].
      split; [eapply (ws1_obj_munch LayoutPU); [exact WS1'| exact MU2| exact WM2| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]|].
      split; [assumption|]. split; [exact FRESHwa|]. split; [exact FRESHv|]. split; [exact LIVEq|]. split; [exact LB'|]. split; [exact NL'|].
      eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m _ m' _ _ _);
        [ exact MU | | exact FRK | lia | lia | intros a X; exact X | intros a X; left; exact X
        | exact MU2 | | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia] ];
        intros a Ha NO; cbn [outside] in NO; lia.
  Qed.
End S.

End U_WS0s9.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_VS4cn.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_WS2nv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_VExcu.U_WS0s9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_VS4cn.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
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
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma crc32_null0_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  a1 = Z_to_bv 64 0 -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp ->
  evt rsegs (crc32_null0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ca54) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros -> MI ST LO. unfold crc32_null0_post.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as Rsp. pose proof (bv_unsigned_in_range _ a2) as Ra2.
  do 3 zstep.
  carve_frame 112%nat ST.
  do 14 zstep.
  zstep. if_cases K0; zify_cond K0. 2:{ kill K0. }
  zstep. zstep.
  do 14 zstep.
  try replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
  release_frame FR ST (bv_unsigned sp).
  zstep. finish.
Qed.

(* [comment removed for export] *)
Definition q0 : vep_pads := VPADS (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4)
                                  (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4).
Lemma q0_wf : vep_pads_wf q0. Proof. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Definition ztag : list byte := repeat (Z_to_bv 8 0) 8.
(* [comment removed for export] *)
Definition vep_all0 : list cell :=
  Eval cbv [tl vep_cells q0 p36 p124 p140 p196 p236 p268 p308 app] in
    ([C4 (Z_to_bv 64 0)] ++ tl (vep_cells (fun _ => 0) ztag q0)).
Lemma vep_all0_wf : cells_wf vep_all0. Proof. cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Lemma vep_all0_bytes : cells_bytes vep_all0 = repeat (Z_to_bv 8 0) 312. Proof. vm_compute. reflexivity. Qed.

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
  Context {AI : AllocSpec LayoutPU}.

  Lemma VEP_Init_ok : VEP_Init_stmt.
  Proof.
    unfold VEP_Init_stmt. intros H flags lo. intros until T. intros AINV MI LIVEX Ha0 Ha1 Ha2 Ha3 Ha4 FL WS0 HENV HG IMG LBUD NBUD TP SP16 RA2 ST CEIL LO SPH K.
    rewrite Ha0, Ha1, Ha2, Ha3, Ha4.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY.
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
    assert (Ebss : h_bss H = 0x41bd0) by (destruct GLOB as [E _]; rewrite E; reflexivity).
    unfold VEPINIT_STACK, WSALLOC_STACK, CALLOC_STACK in *. unfold VEP_Init_entry.
    rewrite Evc, Ereq.
    (* [comment removed for export] *)
    (first [ pose proof (HOBJ) as dR_2; dand5 dR_2 as VC WK RQ RS HD | pose proof HOBJ as (VC & WK & RQ & RS & HD) ]).
    (first [ dex2 VC as vcpad vcrest; dand3 VC as LVP LVR VC | dand5 VC as vcpad vcrest LVP LVR VC | destruct VC as (vcpad & vcrest & LVP & LVR & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LWP LWR WK | dand5 WK as wkpad wkrest LWP LWR WK | destruct WK as (wkpad & wkrest & LWP & LWR & WK) ]).
    (first [ dex3 RQ as mid1 tl1 pd1; dand4 RQ as LM1 LT1 LP1 RQ | dand7 RQ as mid1 tl1 pd1 LM1 LT1 LP1 RQ | destruct RQ as (mid1 & tl1 & pd1 & LM1 & LT1 & LP1 & RQ) ]). (first [ dex4 RS as hd2 mid2 tl2 pd2; dand4 RS as LM2 LT2 LP2 RS | dand8 RS as hd2 mid2 tl2 pd2 LM2 LT2 LP2 RS | destruct RS as (hd2 & mid2 & tl2 & pd2 & LM2 & LT2 & LP2 & RS) ]).
    cbn [al_segs LayoutPU] in VC, WK, RQ, RS, HD.
    unfold vc_cells in VC. unfold wrk_cells in WK. unfold http_cells in RQ, RS.
    rewrite Evc, Eresp, Ewrk in VC. rewrite Ewrk in WK. rewrite Ereq, Ehd, Ews in RQ. rewrite Eresp, Ews in RS. rewrite Ehd in HD.
    replace (h_sp H + 1040 + 16) with (h_sp H + 1056) in HD by lia.
    (* [comment removed for export] *)
    assert (GLOBP : forall W mp mq, glob_ok LayoutPU VIU H mp -> munch W mp mq -> wmono rsegs mp mq ->
      (forall a, (0x41bd0 <= a < 0x41bd0 + 16 \/ h_sp H + 1488 <= a < h_sp H + 1488 + 752 \/ h_sp H + 2240 + 1304 <= a < h_sp H + 2240 + 1320) -> outside W a) ->
      glob_ok LayoutPU VIU H mq).
    { intros W mp mq G MUx WMx OUT. eapply (glob_ok_munch LayoutPU); [exact G| exact MUx| exact WMx|].
      intros a Ha. apply OUT. rewrite Ebss in Ha. unfold h_cp, h_vsc in Ha. exact Ha. }
    assert (HOBJP : forall W mp mq, hobj_ok LayoutPU VIU H mp -> munch W mp mq -> wmono rsegs mp mq ->
      (forall a, (h_sp H + 1040 + 16 <= a < h_sp H + 1040 + 24 \/ h_sp H + 1120 <= a < h_sp H + 1432 + 56) -> outside W a) ->
      hobj_ok LayoutPU VIU H mq).
    { intros W mp mq O MUx WMx OUT. eapply (hobj_ok_munch LayoutPU); [exact O| exact MUx| exact WMx|].
      intros a Ha. apply OUT. unfold h_hd, h_wrk, h_req, h_resp, h_vc in Ha. lia. }
    pose proof (munch_refl [(bv_unsigned sp - 8384, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutPU A [(bv_unsigned sp - 8384, bv_unsigned sp)]).
    { cbn. split; [left; lia| exact I]. }
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 64%nat ST.
    zstep. stub_begin FR (bv_unsigned sp + -64) (bv_unsigned sp). do 7 zstep. stub_end MUstub WMstub.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K0; zify_cond K0. { kill_align K0 G16. } clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    zstep. zstep. if_cases K0; zify_cond K0. { kill_align K0 G16. } clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    zstep. zstep. if_cases K0; zify_cond K0. { kill_align K0 G16. } clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    pose proof (ainv_munch LayoutPU A m _ md _ AINV MU WM CFP) as AINV1.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (crange_stack (L:=LayoutPU) A mx md (bv_unsigned sp - 64) 64 AINV1 ltac:(lia) ltac:(lia)
                    (rw_cells_mapped LayoutPU mx _ _ FR ltac:(off_image_solve LayoutPU))) as CF;
      pose_cranges LayoutPU A mx AINV1 end.
    eapply WS_Alloc_ok;
      [ exact AINV1 | assumption | exact LIVEX | rewrite Ews; reflexivity | reflexivity
      | eapply (ws0_obj_munch LayoutPU); [exact WS0| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]
      | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
      | exact HG
      | eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG]
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
    assert (XFER1 : forall Vc N, cframe LayoutPU (owned A) (owned A1) (bv_unsigned sp - 64) 8320 Vc N m0 m1 ->
              (forall a, Vc a -> h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32) ->
              hobj_ok LayoutPU VIU H m1 /\ img_okU m1).
    { intros Vc N CFR HV. split.
      - eapply (hobj_ok_ccall LayoutPU VIU H A A1 m0 md m1); [exact AINV1| exact CFR| exact HG
          | eapply HOBJP; [exact HOBJ| exact MU| exact WM| intros a Ha; cbn [outside]; lia] | lia |].
        intros a Ha X. apply HV in X. unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_ws, h_wsbuf in *. lia.
      - eapply (img_okU_ccall A A1 m0 md m1); [exact AINV1| exact CFR| unfold IMGU_HI; lia
          | intros a Ha X; apply HV in X; unfold IMGU_LO, IMGU_HI, h_ws, h_wsbuf in *; lia
          | eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG]]. }
    (* [comment removed for export] *)
    destruct OUT as (wa & junkv & NZ & WS1' & NBv & FRESHwa & FRESHv & LIVEq & LBw & NLw & FRK).
    rename r into vep.
    - (* [comment removed for export] *)
      destruct (XFER1 _ _ FRK ltac:(intros a X; exact X)) as [HOBJ1 IMG1].
      clear ST. acall_xfer FRK. clear AINV1. rename ST' into ST.
      pose proof WS1' as WS1x. (first [ dex2 WS1x as id pad; dand7 WS1x as IDOK PADL WSC WEC LWA WAC LVEP | dand9 WS1x as id pad IDOK PADL WSC WEC LWA WAC LVEP | destruct WS1x as (id & pad & IDOK & PADL & WSC & WEC & LWA & WAC & LVEP) ]). clear WSC WEC WAC.
      (first [ pose proof ((as_live_ok A1 m1 md1 vep _ AINV' LVEP)) as dR_8; dand7 dR_8 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A1 m1 md1 vep _ AINV' LVEP) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]).
      assert (VEPbss : vep + 312 <= 0x10000 \/ 0x64000 <= vep) by (unfold in_image in VEPimg; cbn [al_image_lo al_image_hi LayoutPU] in VEPimg; lia).
      clear VEPimg.
      (first [ pose proof ((as_live_ok A1 m1 md1 wa _ AINV' LWA)) as dR_9; dand7 dR_9 as _ WA16 WAlo WAhi WAimg WAmap WAown | pose proof (as_live_ok A1 m1 md1 wa _ AINV' LWA) as (_ & WA16 & WAlo & WAhi & WAimg & WAmap & WAown) ]). clear WAimg.
      assert (NEwv : wa <> vep) by (intros ->; rewrite LVEP in LWA; discriminate LWA).
      pose proof (as_live_disjoint A1 m1 md1 wa 40 vep 312 AINV' LWA LVEP NEwv) as DJ.
      pose proof (munch_refl [(bv_unsigned sp - 8384, bv_unsigned sp); (vep, vep + 312)] m1) as MU2.
      pose proof (wmono_refl rsegs m1) as WM2.
      assert (CFP2 : client_fp LayoutPU A1 [(bv_unsigned sp - 8384, bv_unsigned sp); (vep, vep + 312)]).
      { cbn. split; [left; lia|]. split; [right; left; exists vep, 312; split; [exact LVEP|lia]| exact I]. }
      rz_resume MDH' MDL'.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
      zstep. zstep. zstep. zstep.
      call memset_spec_z.
      1:{ exact NBv. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
      try clear NBv. match goal with X : rw_cells rsegs _ vep [CB _ _] |- _ => rename X into NBz end.
      change (Z.to_nat 312) with 312%nat in NBz. change (0 mod 256) with 0 in NBz.
      (* [comment removed for export] *)
      lazymatch type of NBz with rw_cells _ ?mx _ _ =>
        apply (rw_cells_recast rsegs mx vep _ vep_all0) in NBz; [| exact vep_all0_wf | rewrite vep_all0_bytes; reflexivity ] end.
      rename NBz into NB. unfold vep_all0 in NB.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KZ; zify_cond KZ. { exfalso; apply KZ; apply land7_of_mod8; [lia| apply mod8_of_mod16; exact VEP16]. } clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
      zstep. zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
      zstep. zstep. zstep. if_cases KZ; zify_cond KZ. { kill_align KZ G16. } clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      apply rz_stop.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        pose proof (ainv_munch LayoutPU A1 m1 mx md1 _ AINV' MU2 WM2 CFP2) as AINV2;
        pose_cranges LayoutPU A1 mx AINV2 end.
      eapply VSB_new_auto_cps;
        [ exact AINV2 | assumption | exists wa, 40; exact LWA
        | revert LBUD LBw; clear; intros; lia | revert NBUD NLw; clear; intros; lia
        | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; exact ST | exact CEIL
        | rewrite unsigned_lit by lia; unfold NEWAUTO_STACK, MALLOC_STACK, CALLOC_STACK; lia
        | rewrite unsigned_lit by lia; lia | ].
      intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' S A2 m5 md5 AINV5 MI5 MDF5 ST5 OUT2.
      pose proof (as_lazy_nil A2 m5 md5 AINV5) as [MDL5 MDH5].
      rewrite unsigned_lit in ST5, OUT2 by lia. unfold NEWAUTO_STACK, MALLOC_STACK, CALLOC_STACK in OUT2.
      (* [comment removed for export] *)
      lazymatch type of MU2 with munch _ _ ?mx =>
        assert (CFa : cframe LayoutPU (owned A) (owned A1) (bv_unsigned sp) 8384
                        (fun a => h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32)
                        (fun a => blk wa 40 a \/ blk vep 312 a) m mx)
          by (eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m m0 m1 mx _ _);
              [ exact MU | | exact FRK | lia | lia | intros a X; exact X | intros a X; left; exact X
              | exact MU2 | | eapply (window_mapped LayoutPU _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia] ];
              [ intros a Ha NO; cbn [outside] in NO; lia
              | intros a Ha NO; cbn [outside] in NO; unfold blk; lia ]);
        assert (XFER2 : forall N, cframe LayoutPU (owned A1) (owned A2) (bv_unsigned sp + -64) 8256 nowhere N mx m5 ->
                  hobj_ok LayoutPU VIU H m5 /\ img_okU m5 /\ glob_ok LayoutPU VIU H m5)
          by (intros N CFR; split; [|split];
              [ eapply (hobj_ok_ccall LayoutPU VIU H A1 A2 mx md1 m5); [exact AINV2| exact CFR| exact HG
                  | eapply HOBJP; [exact HOBJ1| exact MU2| exact WM2| intros a Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ] | lia | intros a _ X; exact X]
              | eapply (img_okU_ccall A1 A2 mx md1 m5); [exact AINV2| exact CFR| unfold IMGU_HI; lia| intros a _ X; exact X
                  | eapply (img_okU_munch _ m1); [exact MU2| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ| exact IMG1]]
              | eapply (glob_ok_ccall LayoutPU VIU H A1 A2 mx md1 m5); [exact AINV2| exact CFR| exact HG
                  | eapply GLOBP; [exact GLOB1| exact MU2| exact WM2| intros a Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ]
                  | lia| lia
                  | rewrite Ebss; cbn; lia| rewrite Ebss; cbn; lia
                  | intros i Hi; rewrite Ebss; cbn; unfold pu_static; lia
                  | rewrite Ebss; cbn; change (al_errno LayoutPU) with 0x42454; lia
                  | intros a _ X; exact X] ]);
        assert (WS1x : forall N, cframe LayoutPU (owned A1) (owned A2) (bv_unsigned sp + -64) 8256 nowhere N mx m5 ->
                  a_live A2 wa = Some 40 -> a_live A2 vep = Some 312 -> ws1_obj LayoutPU H A2 m5 wa vep)
          by (intros N CFR L1 L2; eapply (ws1_obj_ccall LayoutPU H A1 A2 mx md1 m5); [exact AINV2| exact CFR| exact HG
              | eapply (ws1_obj_munch LayoutPU); [exact WS1'| exact MU2| exact WM2| intros a Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ]
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
        assert (CFP3 : client_fp LayoutPU A2 [(bv_unsigned sp - 8384, bv_unsigned sp); (vep, vep + 312)]).
        { cbn. split; [left; lia|]. split; [right; left; exists vep, 312; split; [exact LVEP5|lia]| exact I]. }
        rz_resume MDH5 MDL5.
        (* [comment removed for export] *)
        zstep. zstep. if_cases KZ; zify_cond KZ. { kill KZ. } clear KZ.
        zstep. if_cases KC; zify_cond KC. 2:{ kill KC. } clear KC.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        call_lit crc32_null0_spec by (idtac; lazymatch goal with
          | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
          | |- mem_inv _ _ => assumption
          | |- @eq word _ _ => reflexivity
          | |- _ => rewrite ?unsigned_lit by lia; lia end).
        try clear ST. match goal with X : stk rsegs _ lo _ |- _ => rename X into ST end.
        zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        call_lit crc32_null0_spec by (idtac; lazymatch goal with
          | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
          | |- mem_inv _ _ => assumption
          | |- @eq word _ _ => reflexivity
          | |- _ => rewrite ?unsigned_lit by lia; lia end).
        try clear ST. match goal with X : stk rsegs _ lo _ |- _ => rename X into ST end.
        zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep. chunks_hide_except FR. do 7 zstep. chunks_unhide. zstep.
        try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
        release_frame FR ST (bv_unsigned sp).
        zstep. cps_done.
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?my _) _) _ =>
          lazymatch type of MU3 with munch ?W _ _ =>
            pose proof (ainv_munch LayoutPU A2 m5 my md5 W AINV5 MU3 WM3 CFP3) as AINV9 end end.
        eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ vep A2 _ md5);
          [ exact AINV9 | assumption | eapply md_frame_trans; [exact MDF| exact MDF5] | exact ST
          | split; [eapply GLOBP; [exact GLOB5| exact MU3| exact WM3| intros a Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ]
                  | eapply HOBJP; [exact HOBJ5| exact MU3| exact WM3| intros a Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ]]
          | eapply (img_okU_munch _ m5); [exact MU3| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ| exact IMG5]
          | ].
        exists wa, ztag, q0, b. split; [exact NZ|].
        split; [eapply (ws1_obj_munch LayoutPU); [exact WS1_5| exact MU3| exact WM3| intros a Ha; cbn [outside]; klia Ha SPH ACV GCE VEPhi VEPbss VEPlo Ews Ewb WAhi DJ]|].
        exists S.
        split. { split; [exact LVEP5|]. split; [cbn [al_segs LayoutPU]; exact NB| split; [reflexivity| exact q0_wf]]. }
        split; [exact NZS|].
        split. { eapply (vsb_obj_munch LayoutPU); [exact VSB5| exact MU3| exact WM3
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
            assert (CF2 : cframe LayoutPU (owned A1) (owned A2) (bv_unsigned sp) 8384
                            (fun a => blk vep 312 a \/ (h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32))
                            (fun a => blk S 40 a \/ blk b 16 a) mx mfin)
              by (eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ mx mx m5 _ [] _);
                  [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK2 | lia | lia
                  | intros a X; destruct X | intros a X; left; exact X | exact MU3 |
                  | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia] ];
                  intros a Ha NO; cbn [outside] in NO; unfold blk; lia);
            eapply (cframe_seq LayoutPU _ _ _ _ _ _ _ _ _ _ _ _ _ m mx mfin CFa CF2); [lia | lia
              | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia]
              | intros a X; exact X | intros a [X|X]; [left; right; exact X| right; exact X]
              | intros a [X|[X|[X|X]]]; [left; left; exact X| left; right; exact X| right; left; left; exact X| right; left; right; exact X] ]
          end end.
  Qed.
End S.
