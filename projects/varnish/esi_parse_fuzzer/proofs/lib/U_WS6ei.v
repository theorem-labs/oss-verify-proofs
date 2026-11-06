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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import RU_ssdc RU_ssga U_WS2nv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module U_WSwbl.
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
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@ACV; @LO; @GCE; @GHI; @CEIL; @SPH; @IDL; @PADL; @Ha; @WAPlo; @WAlo; @SP16; @WAhi; @WAPhi; @K0; @H0; @VEPhi; @NO; @VEPlo; @K4; @K1; @X; @K2; @K3; @K6; @WAimg; @VEPimg; @K7; @RA4; @RR; @K5; @Hi; @WAbss; @VEPbss])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
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

Definition ws_alloc_free_entry : Z := 0x18a68.
Definition WS_Reset_entry : Z := 0x188a8.
(* [comment removed for export] *)
Definition WSAFREE_STACK : Z := 32 + FREE_STACK.
(* [comment removed for export] *)
Definition WSRESET_STACK : Z := 48 + WSAFREE_STACK.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma cframe_trimV {AI : AllocSpec LayoutPU} : forall o o' sp win (V V' N : Z -> Prop) m m',
  cframe LayoutPU o o' sp win V N m m' ->
  (forall a, V a -> V' a \/ (sp - win <= a < sp)) -> (forall a, N a -> False) ->
  cframe LayoutPU o o' sp win V' N m m'.
Proof.
  (intros o o' sp win V V' N m m'; (first [ intro dR_21; dand3 dR_21 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros HV HN). split; [|split; [exact C2|]].
  - intros a Ha NO VIS NW NE NV. apply C1; [exact Ha| exact NO| exact VIS| exact NW| exact NE|].
    intros X. destruct (HV a X) as [Y|Y]; [exact (NV Y)| exact (NW Y)].
  - intros a _ _ _ X. destruct (HN a X).
Qed.

End CEIL.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

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
      henv_geom H -> img_okU m ->
      tp = al_tp LayoutPU -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->   (* [comment removed for export] *)
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + WSAFREE_STACK <= bv_unsigned sp ->
      bv_unsigned sp <= WAP -> WAP + 8 <= h_sp H -> WAP mod 8 = 0 ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) ->
          rw_cells rsegs m' WAP [C8 (Z_to_bv 64 0)] ->
          rw_cells rsegs m' (h_wsbuf H) (wsemu_cells (wsemu_WS0 (h_wsbuf H))) ->
          a_live A' wa = None -> a_live A' vep = None ->
          (forall q, q <> wa -> q <> vep -> a_live A' q = a_live A q) ->
          a_livebytes A' = a_livebytes A - 352 -> a_nlive A' = a_nlive A - 2 ->   (* [comment removed for export] *)
          cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) WSAFREE_STACK
                 (fun a => blk wa 40 a \/ blk vep 312 a \/ h_wsbuf H + 16 <= a < h_wsbuf H + 32 \/ WAP <= a < WAP + 8) nowhere m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 ws_alloc_free_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. intros AINV MI Ha0 Ha1 WAPC WEC LWA WAC PADL LVEP HG IMG TP SP16 RA4 ST CEIL LO WAPlo WAPhi WAP8 K.
    rewrite Ha0, Ha1.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY.
    pose proof alloc_ceiling_val as ACV.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G16 GCE GHI | pose proof HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (WE8 : (h_sp H + 16) mod 8 = 0) by (apply align_mod8_of16; [exact G16| reflexivity]).
    assert (WL8 : (h_sp H + 32) mod 8 = 0) by (apply align_mod8_of16; [exact G16| reflexivity]).
    pose proof IMG as IMG0. (first [ dand3 IMG as _ GMS _ | destruct IMG as (_ & GMS & _) ]). unfold GOT_memset in GMS.
    unfold WSAFREE_STACK, FREE_STACK in *. unfold ws_alloc_free_entry.
    rewrite Ewb in WEC, WAC |- *.
    (first [ pose proof ((as_live_ok A m md wa _ AINV LWA)) as dR_3; dand7 dR_3 as _ WA16 WAlo WAhi WAimg WAmap WAown | pose proof (as_live_ok A m md wa _ AINV LWA) as (_ & WA16 & WAlo & WAhi & WAimg & WAmap & WAown) ]).
    assert (WAbss : wa + 40 <= 0x10000 \/ 0x64000 <= wa) by (unfold in_image in WAimg; cbn [al_image_lo al_image_hi LayoutPU] in WAimg; lia).
    clear WAimg.
    (first [ pose proof ((as_live_ok A m md vep _ AINV LVEP)) as dR_4; dand7 dR_4 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A m md vep _ AINV LVEP) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]).
    assert (VEPbss : vep + 312 <= 0x10000 \/ 0x64000 <= vep) by (unfold in_image in VEPimg; cbn [al_image_lo al_image_hi LayoutPU] in VEPimg; lia).
    clear VEPimg.
    assert (NEwv : wa <> vep) by (intros ->; rewrite LVEP in LWA; discriminate LWA).
    pose proof (as_live_disjoint A m md wa 40 vep 312 AINV LWA LVEP NEwv) as DJ.
    unfold wsemu_cells, wsemu_WS1 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
    unfold wsalloc_cells, wsalloc_WS1 in WAC. cbn [wa_off wa_len wa_ptr wa_next wa_prev] in WAC.
    replace (h_sp H + 16 + 16) with (h_sp H + 32) in WAC by lia.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8224, bv_unsigned sp); (WAP, WAP + 8); (h_sp H + 32, h_sp H + 48)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutPU A [(bv_unsigned sp - 8224, bv_unsigned sp); (WAP, WAP + 8); (h_sp H + 32, h_sp H + 48)]).
    { cbn. split; [left; lia|]. split; [left; lia|]. split; [left; lia| exact I]. }
    apply rz_go; [exact MDH | exact MDL |]. hide_slowR.
    carve_frame 32%nat ST.
    do 3 zstep.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K0; zify_cond K0. { exfalso. apply K0. apply land7_of_mod8; [lia| exact WAP8]. } clear K0.
    zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K1; zify_cond K1. { exfalso. apply K1. apply land7_of_mod8; [lia| apply mod8_of_mod16; exact WA16]. } clear K1.
    zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1. { kill K1. } clear K1.
    zstep. zstep. if_cases K2; zify_cond K2. { kill K2. } clear K2.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K2; zify_cond K2. { exfalso. apply K2. apply land7_of_mod8; [lia| exact WE8]. } clear K2.
    zstep. zstep. zstep. if_cases K2; zify_cond K2. { kill K2. } clear K2.
    zstep. zstep. if_cases K2; zify_cond K2. { exfalso. apply K2. apply land7_of_mod8; [lia| exact WL8]. } clear K2.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    apply rz_stop.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (ainv_munch LayoutPU A m mx md _ AINV MU WM CFP) as AINV1;
      pose_cranges LayoutPU A mx AINV1 end.
    clear GMS.
    eapply (as_free_cps (L:=LayoutPU)) with (p := vep) (n0 := 312);
      [ exact AINV1 | assumption | reflexivity | right; exact LVEP | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; unfold FREE_STACK; lia
      | rewrite unsigned_lit by lia; eapply (stk_mapped (L:=LayoutPU)); [exact ST| exact CEIL | unfold FREE_STACK; lia | lia]
      | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 AINV' MI' MDF DEADv LIVEq LBf1 NLf1 _ FRK.
    pose proof (as_lazy_nil A1 m1 md1 AINV') as [MDL' MDH'].
    rewrite unsigned_lit in FRK by lia.
    lazymatch type of FRK with frame_ok _ _ _ _ _ _ _ ?mx _ =>
      assert (IMG1 : img_okU m1)
        by (eapply (img_okU_ccall A A1 mx md m1); [exact AINV1| apply (cframe_of_frame_ok LayoutPU); exact FRK
            | unfold IMGU_HI, FREE_STACK; lia| intros a Ha X; unfold IMGU_LO, IMGU_HI, blk in *; first [ solve [ akit_avoids_false X ] | lia ]
            | eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG0]]) end.
    hide_disjR. (lazymatch type of DJ with keptR ?T__ => change T__ in DJ | _ => idtac end). acall_xfer FRK. unhide_disjR. clear AINV1.
    assert (LWA1 : a_live A1 wa = Some 40) by (rewrite (LIVEq wa NEwv); exact LWA).
    pose proof (munch_refl [(bv_unsigned sp - 8224, bv_unsigned sp); (wa, wa + 40)] m1) as MU2.
    pose proof (wmono_refl rsegs m1) as WM2.
    assert (CFP2 : client_fp LayoutPU A1 [(bv_unsigned sp - 8224, bv_unsigned sp); (wa, wa + 40)]).
    { cbn. split; [left; lia|]. split; [right; left; exists wa, 40; split; [exact LWA1|lia]| exact I]. }
    pose proof IMG1 as IMG1'. (first [ dand3 IMG1' as _ GMS1 _ | destruct IMG1' as (_ & GMS1 & _) ]). unfold GOT_memset in GMS1. cbn [al_segs LayoutPU] in GMS1.
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
      pose proof (ainv_munch LayoutPU A1 m1 mx md1 _ AINV' MU2 WM2 CFP2) as AINV2;
      pose_cranges LayoutPU A1 mx AINV2 end.
    eapply (as_free_cps (L:=LayoutPU)) with (p := wa) (n0 := 40);
      [ exact AINV2 | assumption | reflexivity | right; exact LWA1 | exact TP
      | exact SP16 | exact RA4
      | unfold FREE_STACK; lia
      | eapply (stk_mapped (L:=LayoutPU)); [exact ST| exact CEIL | unfold FREE_STACK; lia | lia]
      | ].
    intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x A2 m3 md3 AINV3 MI3 MDF3 DEADwa LIVEq3 LBf2 NLf2 _ FRK2.
    pose proof (as_lazy_nil A2 m3 md3 AINV3) as [MDL3 MDH3].
    (* [comment removed for export] *)
    lazymatch type of MU2 with munch _ _ ?mx =>
      assert (CFa : cframe LayoutPU (owned A) (owned A1) (bv_unsigned sp) 8224
                       (fun a => blk wa 40 a \/ blk vep 312 a \/ h_wsbuf H + 16 <= a < h_wsbuf H + 32 \/ WAP <= a < WAP + 8) nowhere m mx)
        by (eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m _ m1 _ _ _);
            [ exact MU | | exact FRK | unfold FREE_STACK; lia | lia | intros a X; right; left; exact X | intros a X; destruct X
            | exact MU2 | | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia] ];
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
      eapply (cframe_seq LayoutPU _ _ _ _ _ _ _ _ _ _ _ _ _ m _ mfin CFa FRK2); [lia | lia
        | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia]
        | intros a X; exact X | intros a X; right; left; exact X | intros a X; destruct X ] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ws_E (H : henv) (A : AS) (m : mem) (E : option (Z * Z)) : Prop :=
    match E with None => ws0_obj LayoutPU H m | Some (wa, vep) => ws1_obj LayoutPU H A m wa vep end.

  Lemma WS_Reset_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (H : henv) (E : option (Z * Z)) (lo : Z) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 (h_ws H) -> a1 = Z_to_bv 64 (h_wsbuf H) ->
      ws_E H A m E ->
      glob_ok LayoutPU VIU H m -> henv_geom H -> img_okU m ->
      tp = al_tp LayoutPU -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + WSRESET_STACK <= bv_unsigned sp ->
      bv_unsigned sp <= h_sp H ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> glob_ok LayoutPU VIU H m' -> ws0_obj LayoutPU H m' ->
          match E with
          | None => (forall p, a_live A' p = a_live A p) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some (wa, vep) => a_live A' wa = None /\ a_live A' vep = None /\
                              (forall p, p <> wa -> p <> vep -> a_live A' p = a_live A p) /\
                              a_livebytes A' = a_livebytes A - 352 /\ a_nlive A' = a_nlive A - 2
          end ->
          cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) WSRESET_STACK
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
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY.
    pose proof alloc_ceiling_val as ACV.
    (first [ pose proof (HG) as dR_6; dand3 dR_6 as G16 GCE GHI | pose proof HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (Ebss : h_bss H = 0x41bd0) by (destruct GLOB as [E0 _]; rewrite E0; reflexivity).
    assert (WS8 : (h_sp H + 1080) mod 8 = 0) by (apply align_mod8_of16; [exact G16| reflexivity]).
    assert (WE8 : (h_sp H + 16) mod 8 = 0) by (apply align_mod8_of16; [exact G16| reflexivity]).
    assert (WL8 : (h_sp H + 32) mod 8 = 0) by (apply align_mod8_of16; [exact G16| reflexivity]).
    pose proof IMG as IMG0. (first [ dand5 IMG as _ _ _ GCP _ | destruct IMG as (_ & _ & _ & GCP & _) ]). unfold GOT_cp in GCP.
    unfold WSRESET_STACK, WSAFREE_STACK, FREE_STACK in *. unfold WS_Reset_entry.
    rewrite Ews, Ewb.
    assert (GLOBP : forall W mp mq, glob_ok LayoutPU VIU H mp -> munch W mp mq -> wmono rsegs mp mq ->
      (forall a, (0x41bd0 <= a < 0x41bd0 + 16 \/ h_sp H + 1488 <= a < h_sp H + 1488 + 752 \/ h_sp H + 2240 + 1304 <= a < h_sp H + 2240 + 1320) -> outside W a) ->
      glob_ok LayoutPU VIU H mq).
    { intros W mp mq G MUx WMx OUT. eapply (glob_ok_munch LayoutPU); [exact G| exact MUx| exact WMx|].
      intros a Ha. apply OUT. rewrite Ebss in Ha. unfold h_cp, h_vsc in Ha. exact Ha. }
    pose proof (munch_refl [(bv_unsigned sp - 8272, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutPU A [(bv_unsigned sp - 8272, bv_unsigned sp)]).
    { cbn. split; [left; lia| exact I]. }
    destruct E as [[wa vep]|]; cbn [ws_E] in WSX.
    - (* [comment removed for export] *)
      pose proof WSX as WS1. (first [ dex2 WSX as id pad; dand7 WSX as IDOK PADL WSC WEC LWA WAC LVEP | dand9 WSX as id pad IDOK PADL WSC WEC LWA WAC LVEP | destruct WSX as (id & pad & IDOK & PADL & WSC & WEC & LWA & WAC & LVEP) ]). cbn [al_segs LayoutPU] in WSC, WEC, WAC.
      assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
      (first [ pose proof ((as_live_ok A m md wa _ AINV LWA)) as dR_9; dand7 dR_9 as _ WA16 WAlo WAhi WAimg WAmap WAown | pose proof (as_live_ok A m md wa _ AINV LWA) as (_ & WA16 & WAlo & WAhi & WAimg & WAmap & WAown) ]).
      assert (WAbss : wa + 40 <= 0x10000 \/ 0x64000 <= wa) by (unfold in_image in WAimg; cbn [al_image_lo al_image_hi LayoutPU] in WAimg; lia).
      clear WAimg.
      (first [ pose proof ((as_live_ok A m md vep _ AINV LVEP)) as dR_10; dand7 dR_10 as _ VEP16 VEPlo VEPhi VEPimg VEPmap VEPown | pose proof (as_live_ok A m md vep _ AINV LVEP) as (_ & VEP16 & VEPlo & VEPhi & VEPimg & VEPmap & VEPown) ]).
      assert (VEPbss : vep + 312 <= 0x10000 \/ 0x64000 <= vep) by (unfold in_image in VEPimg; cbn [al_image_lo al_image_hi LayoutPU] in VEPimg; lia).
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
        | |- ws_state _ _ _ => cbn [ws_state]; split; [eapply (ws1_obj_munch LayoutPU); [exact WS1| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [lia | exact WA16]]
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
      zstep. zstep. zstep. if_cases K1; zify_cond K1. 2:{ kill K1. } clear K1.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (GLOBc : glob_ok LayoutPU VIU H mx) by (eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]) end.
      (first [ pose proof (GLOBc) as dR_11; dand4 dR_11 as EBSS BSS CP _ | pose proof GLOBc as (EBSS & BSS & CP & _) ]). rewrite EBSS in BSS. cbn [vi_bss VIU al_segs LayoutPU] in BSS. cbn [al_segs LayoutPU] in CP. clear GLOBc.
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ kill K2. } clear K2.
      (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3. { kill K3. } clear K3.
      zstep. zstep. if_cases K3; zify_cond K3. { exfalso. apply K3. apply land7_of_mod8; [lia| exact WS8]. } clear K3.
      zstep. zstep. if_cases K3; zify_cond K3. { kill K3. } clear K3.
      zstep. zstep.
      call_lit (ws_emu_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h_sp H + 1080)
                (WSR id (h_sp H + 16) 0 0 (h_sp H + 16 + 1016)) (WER 1016 0 wa (wa + 24))) by (idtac;
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
      zstep. zstep. zstep. if_cases K4; zify_cond K4. { exfalso. apply K4. apply land7_of_mod8; [lia| exact WE8]. } clear K4.
      zstep. zstep. if_cases K4; zify_cond K4. { kill K4. } clear K4.
      zstep. zstep. if_cases K4; zify_cond K4. { exfalso. apply K4. apply land7_of_mod8; [lia|]. apply align_mod8_of16; [exact WA16| reflexivity]. } clear K4.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K4; zify_cond K4. { kill K4. } clear K4.
      zstep. zstep. if_cases K4; zify_cond K4. { exfalso. apply K4. apply land7_of_mod8; [lia| exact WL8]. } clear K4.
      zstep. try clear CP. zstep. zstep. if_cases K4; zify_cond K4. { kill K4. } clear K4.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K5; zify_cond K5. { exfalso. apply K5. apply land7_of_mod8; [lia| apply mod8_of_mod16; exact WA16]. } clear K5.
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
        pose proof (ainv_munch LayoutPU A m mx md _ AINV MU WM CFP) as AINV1;
        pose_cranges LayoutPU A mx AINV1 end.
      eapply ws_alloc_free_cps;
        [ exact AINV1 | assumption | reflexivity | reflexivity
        | exact WAPC
        | exact WEC | exact LWA | exact WAC | exact PADL | exact LVEP | exact HG
        | eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG0]
        | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; exact ST | exact CEIL
        | rewrite unsigned_lit by lia; unfold WSAFREE_STACK, FREE_STACK; lia
        | rewrite ?unsigned_lit by lia; lia | rewrite ?unsigned_lit by lia; lia
        | rewrite ?unsigned_lit by lia; apply align_mod8_of16; [exact SP16| reflexivity] | ].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' AINV' MI' MDF ST' WAPC' WEC' DEADwa DEADv LIVEq LBf NLf FRK.
      pose proof (as_lazy_nil A' m' md' AINV') as [MDL' MDH'].
      rewrite unsigned_lit in FRK by lia. rewrite unsigned_lit in ST' by lia. unfold WSAFREE_STACK, FREE_STACK in FRK.
      rewrite Ewb in WEC'. unfold wsemu_cells, wsemu_WS0 in WEC'. cbn [we_len we_ws we_first we_last] in WEC'.
      hide_disjR. (lazymatch type of WAbss with keptR ?T__ => change T__ in WAbss | _ => idtac end). (lazymatch type of VEPbss with keptR ?T__ => change T__ in VEPbss | _ => idtac end).
      lazymatch type of FRK with cframe _ _ _ _ _ _ _ ?mx _ =>
        assert (GLOB1 : glob_ok LayoutPU VIU H m')
          by (eapply (glob_ok_ccall LayoutPU VIU H A A' mx md m'); [exact AINV1| exact FRK| exact HG
              | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
              | lia| lia
              | rewrite Ebss; cbn; lia| rewrite Ebss; cbn; lia
              | intros i Hi; rewrite Ebss; cbn; unfold pu_static; lia
              | rewrite Ebss; cbn; change (al_errno LayoutPU) with 0x42454; lia
              | intros a Ha X; cbn beta in X; rewrite Ebss in Ha; unfold h_cp, h_vsc, h_wsbuf, blk in *; first [ solve [ akit_avoids_false X ] | lia ]]);
        assert (IMG1 : img_okU m')
          by (eapply (img_okU_ccall A A' mx md m'); [exact AINV1| exact FRK
              | unfold IMGU_HI; lia| intros a Ha X; cbn beta in X; unfold IMGU_LO, IMGU_HI, h_wsbuf, blk in *; first [ solve [ akit_avoids_false X ] | lia ]
              | eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG0]])
      end.
      clear WAPC BSS WAC WEC GCP.
      repeat match goal with
             | C : crange _ _ wa _ |- _ => clear C
             | C : crange _ _ (h_sp H + 16) _ |- _ => clear C
             | C : crange _ _ (bv_unsigned sp + -40) _ |- _ => clear C end.
      clear ST. hide_disjR. acall_xfer FRK. unhide_disjR. clear AINV1. rename ST' into ST.
      pose proof (munch_refl [(bv_unsigned sp - 8272, bv_unsigned sp)] m') as MU2.
      pose proof (wmono_refl rsegs m') as WM2.
      assert (CFP2 : client_fp LayoutPU A' [(bv_unsigned sp - 8272, bv_unsigned sp)]) by (cbn; split; [left; lia| exact I]).
      rz_resume MDH' MDL'.
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K6; zify_cond K6. { kill K6. } clear K6.
      zstep. zstep. if_cases K6; zify_cond K6. { exfalso. apply K6. apply land7_of_mod8; [lia| exact WL8]. } clear K6.
      zstep. zstep. if_cases K6; zify_cond K6. { kill K6. } clear K6.
      zstep. zstep. if_cases K6; zify_cond K6. { exfalso. apply K6. apply land7_of_mod8; [lia| exact WL8]. } clear K6.
      zstep. zstep. zstep. if_cases K6; zify_cond K6. 2:{ kill K6. } clear K6.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K7; zify_cond K7. { kill K7. } clear K7.
      zstep. zstep.
      call_lit (WS_Assert_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H None lo) by (idtac;
        lazymatch goal with
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
        | |- ws_state _ _ _ => cbn [ws_state]; apply (ws0_obj_intro LayoutPU H _ id IDOK); cbn [al_segs LayoutPU];
              [exact WSC| unfold wsemu_cells, wsemu_WS0; cbn [we_len we_ws we_first we_last]; rewrite Ewb; exact WEC']
        | |- glob_ok _ _ _ _ => eapply GLOBP; [exact GLOB1| exact MU2| exact WM2| intros a Ha; cbn [outside]; lia]
        | |- henv_geom _ => exact HG
        | |- img_okU _ => eapply (img_okU_munch _ m'); [exact MU2| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG1]
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => rewrite ?Ews; reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        match goal with Xa : rw_cells rsegs mx (bv_unsigned sp + -48) _, Xb : rw_cells rsegs mx (bv_unsigned sp + -40) _, Xc : rw_cells rsegs mx (bv_unsigned sp + -32) _ |- _ =>
        pose proof (rwc_eq _ _ _ (bv_unsigned sp + -48 + Z.of_nat (cells_size [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 junk)))))])) _ Xb ltac:(cbn; lia)) as Wb;
        pose proof (proj2 (rw_cells_app rsegs mx (bv_unsigned sp + -48) _ _) (conj Xa Wb)) as FRab;
        pose proof (rwc_eq _ _ _ (bv_unsigned sp + -48 + Z.of_nat (cells_size ([CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 junk)))))] ++ [C8 (Z_to_bv 64 0)]))) _ Xc ltac:(cbn; lia)) as Wc;
        pose proof (proj2 (rw_cells_app rsegs mx (bv_unsigned sp + -48) _ _) (conj FRab Wc)) as FR;
        clear Wb Wc FRab Xa Xb Xc end end.
      cbn [app] in FR.
      try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      cps_done.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        lazymatch type of MU2 with munch ?W _ _ =>
          pose proof (ainv_munch LayoutPU A' m' mx md' W AINV' MU2 WM2 CFP2) as AINV9 end end.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' _ md');
        [ exact AINV9 | assumption | exact MDF | exact ST
        | eapply GLOBP; [exact GLOB1| exact MU2| exact WM2| intros a Ha; cbn [outside]; lia]
        | apply (ws0_obj_intro LayoutPU H _ id IDOK); cbn [al_segs LayoutPU];
          [exact WSC| unfold wsemu_cells, wsemu_WS0; cbn [we_len we_ws we_first we_last]; rewrite Ewb; exact WEC']
        | split; [exact DEADwa| split; [exact DEADv| split; [exact LIVEq| split; [exact LBf| exact NLf]]]] | ].
      lazymatch goal with |- cframe _ _ _ _ _ ?VV _ _ ?mfin =>
        assert (CFx : cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) 8272
                        (fun a => VV a \/ (bv_unsigned sp + -40 <= a < bv_unsigned sp + -40 + 8)) nowhere m mfin)
          by (eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m _ m' _ _ _);
              [ exact MU | | exact FRK | lia | lia | | intros a X; destruct X
              | exact MU2 | | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia] ];
              [ intros a Ha NO; cbn [outside] in NO; lia
              | intros a X; cbn beta in X |- *; unfold h_wsbuf in *;
                destruct X as [X|[X|[X|X]]]; [left; right; right; left; exact X| left; right; right; right; exact X| left; right; left; lia| right; exact X]
              | intros a Ha NO; cbn [outside] in NO; lia ]);
        eapply (cframe_trimV _ _ _ _ _ _ _ _ _ CFx); [| intros a X; exact X];
        intros a [X|X]; [left; exact X| right; lia]
      end.
    - (* [comment removed for export] *)
      pose proof WSX as WS0. (first [ dex1 WSX as id; dand3 WSX as IDOK WSC WEC | dand4 WSX as id IDOK WSC WEC | destruct WSX as (id & IDOK & WSC & WEC) ]). cbn [al_segs LayoutPU] in WSC, WEC.
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
        | |- ws_state _ _ _ => cbn [ws_state]; eapply (ws0_obj_munch LayoutPU); [exact WS0| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]
        | |- glob_ok _ _ _ _ => eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | |- henv_geom _ => exact HG
        | |- img_okU _ => eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG0]
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => rewrite ?Ews; reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
      zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
      zstep. zstep. zstep. if_cases K1; zify_cond K1. 2:{ kill K1. } clear K1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (GLOBc : glob_ok LayoutPU VIU H mx) by (eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]) end.
      (first [ pose proof (GLOBc) as dR_13; dand4 dR_13 as EBSS BSS CP _ | pose proof GLOBc as (EBSS & BSS & CP & _) ]). rewrite EBSS in BSS. cbn [vi_bss VIU al_segs LayoutPU] in BSS. cbn [al_segs LayoutPU] in CP. clear GLOBc.
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ kill K2. } clear K2.
      zstep. if_cases K3; zify_cond K3. { kill K3. } clear K3.
      zstep. zstep. if_cases K3; zify_cond K3. { exfalso. apply K3. apply land7_of_mod8; [lia| exact WS8]. } clear K3.
      zstep. zstep. if_cases K3; zify_cond K3. { kill K3. } clear K3.
      zstep. zstep.
      call_lit (ws_emu_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h_sp H + 1080)
                (WSR id (h_sp H + 16) 0 0 (h_sp H + 16 + 1016)) (WER 1016 0 0 (h_sp H + 16 + 16))) by (idtac;
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
      zstep. zstep. zstep. if_cases K4; zify_cond K4. { exfalso. apply K4. apply land7_of_mod8; [lia| exact WE8]. } clear K4.
      zstep. zstep. if_cases K4; zify_cond K4. { kill K4. } clear K4.
      zstep. zstep. if_cases K4; zify_cond K4. { exfalso. apply K4. apply land7_of_mod8; [lia| exact WL8]. } clear K4.
      zstep. zstep. if_cases K4; zify_cond K4. { kill K4. } clear K4.
      zstep. zstep. if_cases K4; zify_cond K4. { exfalso. apply K4. apply land7_of_mod8; [lia| exact WL8]. } clear K4.
      zstep. try clear CP. zstep. zstep. if_cases K4; zify_cond K4. 2:{ kill K4. } clear K4.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K7; zify_cond K7. { kill K7. } clear K7.
      zstep. zstep.
      call_lit (WS_Assert_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H None lo) by (idtac;
        lazymatch goal with
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
        | |- ws_state _ _ _ => cbn [ws_state]; eapply (ws0_obj_munch LayoutPU); [exact WS0| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]
        | |- glob_ok _ _ _ _ => eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | |- henv_geom _ => exact HG
        | |- img_okU _ => eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG0]
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => rewrite ?Ews; reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
      zstep. zstep. zstep. zstep. zstep. zstep.
      try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      cps_done.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        lazymatch type of MU with munch ?W _ _ =>
          pose proof (ainv_munch LayoutPU A m mx md W AINV MU WM CFP) as AINV9 end end.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A _ md);
        [ exact AINV9 | assumption | apply md_frame_refl; [exact MDL| exact MDH] | exact ST
        | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | eapply (ws0_obj_munch LayoutPU); [exact WS0| exact MU| exact WM| intros a Ha; unfold h_ws, h_wsbuf in Ha; cbn [outside]; lia]
        | split; [intros p; reflexivity| split; reflexivity] | ].
      eapply (cframe_stores LayoutPU); [exact MU| | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia]].
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
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY.
    pose proof alloc_ceiling_val as ACV.
    (first [ pose proof (HG) as dR_14; dand3 dR_14 as G16 GCE GHI | pose proof HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (Ebss : h_bss H = 0x41bd0) by (destruct GLOB as [E0 _]; rewrite E0; reflexivity).
    assert (WS8 : (h_sp H + 1080) mod 8 = 0) by (apply align_mod8_of16; [exact G16| reflexivity]).
    unfold WSROLLBACK_STACK, FREE_STACK in *. unfold WS_Rollback_entry.
    rewrite Ews.
    assert (GLOBP : forall W mp mq, glob_ok LayoutPU VIU H mp -> munch W mp mq -> wmono rsegs mp mq ->
      (forall a, (0x41bd0 <= a < 0x41bd0 + 16 \/ h_sp H + 1488 <= a < h_sp H + 1488 + 752 \/ h_sp H + 2240 + 1304 <= a < h_sp H + 2240 + 1320) -> outside W a) ->
      glob_ok LayoutPU VIU H mq).
    { intros W mp mq G MUx WMx OUT. eapply (glob_ok_munch LayoutPU); [exact G| exact MUx| exact WMx|].
      intros a Ha. apply OUT. rewrite Ebss in Ha. unfold h_cp, h_vsc in Ha. exact Ha. }
    pose proof (munch_refl [(bv_unsigned sp - 8272, bv_unsigned sp); (h_sp H + 1080, h_sp H + 1080 + 40)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutPU A [(bv_unsigned sp - 8272, bv_unsigned sp); (h_sp H + 1080, h_sp H + 1080 + 40)]).
    { cbn. split; [left; lia|]. split; [left; lia| exact I]. }
    destruct E as [[wa vep]|].
    - (* [comment removed for export] *)
      pose proof WSX as WS1. (first [ dex2 WSX as id pad; dand7 WSX as IDOK PADL WSC WEC LWA WAC LVEP | dand9 WSX as id pad IDOK PADL WSC WEC LWA WAC LVEP | destruct WSX as (id & pad & IDOK & PADL & WSC & WEC & LWA & WAC & LVEP) ]). cbn [al_segs LayoutPU] in WSC, WEC, WAC.
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
        | |- ws_state _ _ _ => cbn [ws_state]; split; [apply (ws1_obj_intro LayoutPU H A _ wa vep id pad IDOK PADL); cbn [al_segs LayoutPU];
              [ rewrite Ews; exact WSC | unfold wsemu_cells, wsemu_WS1; cbn [we_len we_ws we_first we_last]; rewrite Ewb; exact WEC | exact LWA
              | unfold wsalloc_cells, wsalloc_WS1; cbn [wa_off wa_len wa_ptr wa_next wa_prev]; rewrite Ewb; exact WAC | exact LVEP] | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [lia | exact WA16]]
        | |- glob_ok _ _ _ _ => eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | |- henv_geom _ => exact HG
        | |- img_okU _ => eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG]
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => rewrite ?Ews; reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0. 2:{ kill K0. } clear K0.
      zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
      zstep. zstep. if_cases K0; zify_cond K0. { exfalso. apply K0. apply land7_of_mod8; [lia| exact WS8]. } clear K0.
      zstep. zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1. { kill K1. } clear K1.
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
        pose proof (ainv_munch LayoutPU A m mx md _ AINV MU WM CFP) as AINV1 end.
      eapply WS_Reset_cps with (H := H) (E := Some (wa, vep)) (lo := lo);
        [ exact AINV1 | assumption | rewrite Ews; reflexivity | rewrite Ewb; reflexivity
        | cbn [ws_E]; apply (ws1_obj_intro LayoutPU H A _ wa vep ws_id_req pad (or_introl eq_refl) PADL); cbn [al_segs LayoutPU];
          [ rewrite Ews; exact WSC | unfold wsemu_cells, wsemu_WS1; cbn [we_len we_ws we_first we_last]; rewrite Ewb; exact WEC | exact LWA
          | unfold wsalloc_cells, wsalloc_WS1; cbn [wa_off wa_len wa_ptr wa_next wa_prev]; rewrite Ewb; exact WAC | exact LVEP]
        | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | exact HG
        | eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG]
        | exact TP | exact SP16 | exact RA2 | exact ST | exact CEIL | unfold WSRESET_STACK, WSAFREE_STACK, FREE_STACK; lia | exact SPH | ].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' AINV' MI' MDF ST' GLOB' WS0' LIVE' FRK.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' m' md');
        [ exact AINV' | exact MI' | exact MDF | exact ST' | exact GLOB' | exact WS0' | exact LIVE' | ].
      unfold WSRESET_STACK, WSAFREE_STACK, FREE_STACK in FRK.
      lazymatch type of MU with munch _ _ ?mx =>
        eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m mx m' m' _ []);
          [ exact MU | | exact FRK | lia | lia | intros a X; exact X | intros a X; destruct X
          | apply munch_refl | intros a _ X; exfalso; apply X; exact I
          | eapply (stk_mapped (L:=LayoutPU)); [exact ST' | exact CEIL | lia | lia] ] end.
      intros a Ha NO. cbn [outside] in NO. cbn beta. unfold h_ws. lia.
    - (* [comment removed for export] *)
      pose proof WSX as WS0. (first [ dex1 WSX as id; dand3 WSX as IDOK WSC WEC | dand4 WSX as id IDOK WSC WEC | destruct WSX as (id & IDOK & WSC & WEC) ]). cbn [al_segs LayoutPU] in WSC, WEC.
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
        | |- ws_state _ _ _ => cbn [ws_state]; apply (ws0_obj_intro LayoutPU H _ id IDOK); cbn [al_segs LayoutPU];
              [ rewrite Ews; exact WSC | unfold wsemu_cells, wsemu_WS0; cbn [we_len we_ws we_first we_last]; rewrite Ewb; exact WEC ]
        | |- glob_ok _ _ _ _ => eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | |- henv_geom _ => exact HG
        | |- img_okU _ => eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG]
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => rewrite ?Ews; reflexivity
        | |- _ => rewrite ?unsigned_lit by lia; lia
        end).
      match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
      zstep. if_cases K0; zify_cond K0. 2:{ kill K0. } clear K0.
      zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
      zstep. zstep. if_cases K0; zify_cond K0. { exfalso. apply K0. apply land7_of_mod8; [lia| exact WS8]. } clear K0.
      zstep. zstep. zstep. if_cases K0; zify_cond K0. { kill K0. } clear K0.
      zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1. { kill K1. } clear K1.
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
        pose proof (ainv_munch LayoutPU A m mx md _ AINV MU WM CFP) as AINV1 end.
      eapply WS_Reset_cps with (H := H) (E := None) (lo := lo);
        [ exact AINV1 | assumption | rewrite Ews; reflexivity | rewrite Ewb; reflexivity
        | cbn [ws_E]; apply (ws0_obj_intro LayoutPU H _ ws_id_req (or_introl eq_refl)); cbn [al_segs LayoutPU];
          [ rewrite Ews; exact WSC | unfold wsemu_cells, wsemu_WS0; cbn [we_len we_ws we_first we_last]; rewrite Ewb; exact WEC ]
        | eapply GLOBP; [exact GLOB| exact MU| exact WM| intros a Ha; cbn [outside]; lia]
        | exact HG
        | eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG]
        | exact TP | exact SP16 | exact RA2 | exact ST | exact CEIL | unfold WSRESET_STACK, WSAFREE_STACK, FREE_STACK; lia | exact SPH | ].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' AINV' MI' MDF ST' GLOB' WS0' LIVE' FRK.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' m' md');
        [ exact AINV' | exact MI' | exact MDF | exact ST' | exact GLOB' | exact WS0' | exact LIVE' | ].
      unfold WSRESET_STACK, WSAFREE_STACK, FREE_STACK in FRK.
      lazymatch type of MU with munch _ _ ?mx =>
        eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m mx m' m' _ []);
          [ exact MU | | exact FRK | lia | lia | intros a X; exact X | intros a X; destruct X
          | apply munch_refl | intros a _ X; exfalso; apply X; exact I
          | eapply (stk_mapped (L:=LayoutPU)); [exact ST' | exact CEIL | lia | lia] ] end.
      intros a Ha NO. cbn [outside] in NO. cbn beta. unfold h_ws. lia.
  Qed.
End S.
End U_WSwbl.

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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition REQ9 : list byte :=
  Eval vm_compute in match image_bytes rsegs 0x10577 9 with Some bs => bs | None => [] end.
Lemma REQ9_ro : ro_bytes_b rsegs 0x10577 REQ9 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma REQ9_eq : REQ9 = [Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 113] ++ Z_to_bv 8 0 :: skipn 4 REQ9.
Proof. reflexivity. Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  #[using="AI"] Lemma WS_Init_ok : WS_Init_stmt.
  Proof.
    unfold WS_Init_stmt.
    intros H junk40 junk32 lo. intros until m.
    intros A0 A1 A2 A3 WSC WEC GLOB HG IMG SPH ST LO CEIL MI.
    rewrite A0, A1, A2, A3. unfold WS_Init_entry. unfold WSINIT_STACK in *.
    pose proof alloc_ceiling_val as ACV.
    (first [ dand3 HG as G16 GCE GHI | destruct HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    assert (WS8 : (h_sp H + 1080) mod 8 = 0) by (apply align_mod8_of16; [exact G16| reflexivity]).
    assert (WE8 : (h_sp H + 16) mod 8 = 0) by (apply align_mod8_of16; [exact G16| reflexivity]).
    (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as EBSS BSS CP [cnt CNT] | pose proof GLOB as (EBSS & BSS & CP & [cnt CNT]) ]). rewrite EBSS in BSS. cbn [vi_bss VIU al_segs LayoutPU] in BSS.
    cbn [al_segs LayoutPU] in CP, CNT.
    pose proof IMG as IMG0. (first [ dand5 IMG as _ _ _ GCP _ | destruct IMG as (_ & _ & _ & GCP & _) ]). unfold GOT_cp in GCP.
    rewrite Ews in WSC |- *. rewrite Ewb in WEC |- *.
    pose proof (rw_cells_bound _ _ _ _ WSC) as WSB. pose proof (rw_cells_bound _ _ _ _ WEC) as WEB.
    cbn [cells_size csize Nat.add] in WSB, WEB.
    pose proof (rw_CB_length _ _ _ _ _ WSC) as L40. pose proof (rw_CB_length _ _ _ _ _ WEC) as L32.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (h_sp H + 1080, h_sp H + 1080 + 40); (h_sp H + 16, h_sp H + 16 + 32)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rw_cells_split_CB rsegs m (h_sp H + 16) [] 32 junk32 [] [8; 8; 8; 8]%nat WEC eq_refl) as WE1. clear WEC.
    cbn [mk_CB_cells app] in WE1.
    carve_frame 48%nat ST.
    do 6 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases K; zify_cond K. 2:{ kill K. } clear K.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K. { kill K. } clear K.
    zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; [lia| exact WE8]. } clear K.
    zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    call memset_spec_z.
    1:{ exact WSC. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
    match goal with X : rw_cells rsegs _ (h_sp H + 1080) _ |- _ => rename X into WSZ end.
    change (Z.to_nat 40) with 40%nat in WSZ. cbn [repeat Z.modulo] in WSZ.
    (* [comment removed for export] *)
    lazymatch type of WSZ with rw_cells _ ?mx _ _ =>
      assert (WS2 : rw_cells rsegs mx (h_sp H + 1080)
                ([C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                  C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]))
        by (apply (rw_cells_recast _ _ _ _ _ WSZ); [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity| reflexivity]) end.
    clear WSZ.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K. { kill K. } clear K.
    zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; [lia| exact WS8]. } clear K.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases K; zify_cond K. { exfalso. rewrite lxor_ones in K by lia. lia. } clear K.
    zstep. zstep.
    zstep. if_cases K; zify_cond K. { kill K. } clear K.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (ro_bytes_at rsegs mx 0x10577 REQ9 ltac:(assumption) ltac:(lia) ltac:(cbn; lia) (ro_bytes_b_sound _ _ _ REQ9_ro)) as STR end.
    rewrite REQ9_eq in STR.
    call_lit strlen_spec by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ _ _ => rewrite unsigned_lit by lia; exact STR
      | |- ~ In _ _ => cbn; intros [X|[X|[X|X]]]; try discriminate X; exact X
      | |- mem_inv _ _ => assumption
      | |- _ => rewrite unsigned_lit by lia; cbn; lia
      end).
    clear POST STR. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
    zstep. zstep. zstep.
    lazymatch type of WS2 with rw_cells _ ?mx _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
      pose proof (proj1 (rw_cells_app rsegs mx (h_sp H + 1080) [c0] (c1 :: c2 :: c3 :: c4 :: rest)) WS2) as [WSa WSbc];
      pose proof (proj1 (rw_cells_app rsegs mx _ [c1; c2; c3; c4] rest) WSbc) as [WSb WSc] end.
    clear WS2 WSbc.
    pose proof (rwc_eq _ _ _ (h_sp H + 1084) _ WSb ltac:(cbn; lia)) as WSb'. clear WSb. rename WSb' into WSb.
    pose proof (rwc_eq _ _ _ (h_sp H + 1088) _ WSc ltac:(cbn; lia)) as WSc'. clear WSc. rename WSc' into WSc.
    call_lit (strcpy_req_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h_sp H + 1084) lo) by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- rw_cells _ _ _ _ => exact WSb
      | |- mem_inv _ _ => assumption
      | |- @eq word _ _ => reflexivity
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    match goal with X : rw_cells rsegs _ (h_sp H + 1084) _ |- _ => rename X into WID end.
    match goal with X : stk rsegs _ lo _ |- _ => rename X into STK end. rename STK into ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch type of WE1 with rw_cells _ ?mx _ (_ :: ?rest) =>
      assert (WE2 : rw_cells rsegs mx (h_sp H + 16) ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ rest))
        by (apply (rw_cells_recast _ _ _ _ _ WE1);
            [ cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; rewrite ?firstn_length, ?skipn_length; lia
            | reflexivity ]) end.
    clear WE1. cbn [app] in WE2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    zstep.
    assert (WS0P : forall mq,
      rw_cells rsegs mq (h_sp H + 1080) [C4 (Z_to_bv 64 905626964)] ->
      rw_cells rsegs mq (h_sp H + 1084) (map C1 REQ_BYTES) ->
      rw_cells rsegs mq (h_sp H + 1088) [C8 (Z_to_bv 64 (h_sp H + 16)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_sp H + 1032))] ->
      rw_cells rsegs mq (h_sp H + 16) [C4 (Z_to_bv 64 478787243); C4 (Z_to_bv 64 1016); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_sp H + 32))] ->
      ws0_obj LayoutPU H mq).
    { intros mq Xa Xb Xc Xe.
      pose proof (rwc_eq _ _ _ (h_sp H + 1084 + Z.of_nat (cells_size (map C1 REQ_BYTES))) _ Xc ltac:(cbn; lia)) as Xc'.
      pose proof (proj2 (rw_cells_app rsegs mq (h_sp H + 1084) _ _) (conj Xb Xc')) as Xbc.
      pose proof (rwc_eq _ _ _ (h_sp H + 1080 + Z.of_nat (cells_size [C4 (Z_to_bv 64 905626964)])) _ Xbc ltac:(cbn; lia)) as Xbc'.
      pose proof (proj2 (rw_cells_app rsegs mq (h_sp H + 1080) _ _) (conj Xa Xbc')) as Xabc.
      cbn [map app REQ_BYTES] in Xabc.
      apply (ws0_obj_intro LayoutPU H mq ws_id_req); [left; reflexivity| |].
      - unfold ws_cells, ws_rec_of, ws_id_req, WS_MAGIC. cbn [ws_id ws_s ws_f ws_r ws_e al_segs LayoutPU].
        rewrite Ews, Ewb. replace (h_sp H + 16 + 1016) with (h_sp H + 1032) by lia.
        apply (rw_cells_recast _ _ _ _ _ Xabc); [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity| reflexivity].
      - unfold wsemu_cells, wsemu_WS0, WS_EMU_MAGIC. cbn [we_len we_ws we_first we_last al_segs LayoutPU].
        rewrite Ewb. replace (h_sp H + 16 + 16) with (h_sp H + 32) by lia. exact Xe. }
    call_lit (WS_Assert_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H None lo) by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => exact ST
      | |- ws_state _ _ _ => cbn [ws_state]; apply WS0P; assumption
      | |- glob_ok _ _ _ _ => eapply (glob_ok_munch LayoutPU); [exact GLOB| exact MU| exact WM| intros a Ha; unfold h_cp, h_vsc in Ha; rewrite EBSS in Ha; cbn [vi_bss VIU] in Ha; cbn [outside]; lia]
      | |- henv_geom _ => split; [exact G16| split; [exact GCE| unfold HFRAME; lia]]
      | |- img_okU _ => eapply (img_okU_munch _ m); [exact MU| intros a Ha; unfold IMGU_LO, IMGU_HI in Ha; cbn [outside]; lia| exact IMG0]
      | |- mem_inv _ _ => assumption
      | |- @eq word _ _ => rewrite ?Ews; reflexivity
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    apply evt_done. unfold WS_Init_post.
    do 16 eexists. split; [reflexivity|]. split; [rewrite Ews, Ewb; exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [exact POST|]. split; [apply WS0P; assumption|].
    eapply (glob_ok_munch LayoutPU); [exact GLOB| exact MU| exact WM|].
    intros a Ha; unfold h_cp, h_vsc in Ha; rewrite EBSS in Ha; cbn [vi_bss VIU] in Ha; cbn [outside]; lia.
  Qed.
End S.
