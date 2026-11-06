(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb U_Leaves ImgU U_VSe1y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.RL.sec := Ltac2.Init.true.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

Definition VSB_new_auto_entry := 0x19310.
(* [comment removed for export] *)
Definition NEWAUTO_STACK := 64 + MALLOC_STACK.

(* [comment removed for export] *)
Definition vsb_zero_cells : list cell :=
  [ C4 (w64 0); C4 (w64 0); C8 (w64 0); C8 (w64 0); C8 (w64 0); C4 (w64 0); C4 (w64 0) ].
Lemma vsb_zero_cells_bytes : cells_bytes vsb_zero_cells = cells_bytes [CB 40 (repeat (Z_to_bv 8 0) 40)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma extendsize0_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv rsegs m ->
  evt rsegs (extendsize_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 extendsize_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI. unfold extendsize_entry.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  zstep. zstep. zstep. if_false.
  (* [comment removed for export] *)
  zstep. zstep. if_true. zstep. zstep. if_true. zstep. zstep.
  apply evt_done. unfold extendsize_post. change (vsb_extendsize 0) with 16.
  eexists _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. exact MI.
Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  (* [comment removed for export] *)
  #[using="AI"] Lemma window_mapped2 : forall m lo a a2 sp W cs1 cs2,
    stk (al_segs LayoutPU) m lo a -> rw_cells (al_segs LayoutPU) m a cs1 ->
    rw_cells (al_segs LayoutPU) m a2 cs2 ->
    a + Z.of_nat (cells_size cs1) = a2 -> a2 + Z.of_nat (cells_size cs2) = sp ->
    alloc_ceiling <= lo -> lo <= sp - W -> sp - W <= a -> mapped m (sp - W) W.
  Proof.
    intros m lo a a2 sp W cs1 cs2 ST F1 F2 SZ1 SZ2 CE LO HA i Hi.
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. pose proof alloc_ceiling_val as CV.
    destruct (Z_lt_le_dec (sp - W + i) a) as [Hb|Hb].
    - apply (stk_mapped (L:=LayoutPU) m lo a (sp - W) (a - (sp - W)) ST CE ltac:(lia) ltac:(lia)). lia.
    - destruct (Z_lt_le_dec (sp - W + i) a2) as [Hc|Hc].
      + pose proof (rw_cells_mapped LayoutPU m a cs1 F1 ltac:(apply (@off_image_stack _ LayoutPU _); lia)) as M.
        replace (sp - W + i) with (a + (sp - W + i - a)) by lia. apply M. lia.
      + pose proof (rw_cells_mapped LayoutPU m a2 cs2 F2 ltac:(apply (@off_image_stack _ LayoutPU _); lia)) as M.
        replace (sp - W + i) with (a2 + (sp - W + i - a2)) by lia. apply M. lia.
  Qed.

  Lemma VSB_new_auto_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (lo : Z) (T : TSet),
      ainv A m md -> mem_inv rsegs m -> (exists q k, a_live A q = Some k) ->
      a_livebytes A + 56 <= LIVE_MAX -> a_nlive A + 2 <= NLIVE_MAX ->   (* [comment removed for export] *)
      tp = al_tp LayoutPU -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + NEWAUTO_STACK <= bv_unsigned sp ->
      bv_unsigned sp + 64 <= 2^47 ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) ->
          (* [comment removed for export] *)
          (exists b, r <> 0 /\ vsb_obj LayoutPU A' m' r (vsb_fresh b) false /\
               a_live A r = None /\ a_live A b = None /\
               (forall q, q <> r -> q <> b -> a_live A' q = a_live A q) /\
               a_livebytes A' = a_livebytes A + 56 /\ a_nlive A' = a_nlive A + 2 /\
               cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) NEWAUTO_STACK nowhere
                      (fun a => blk r 40 a \/ blk b 16 a) m m') ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 VSB_new_auto_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. intros AINV MI LIVEX LBUD NBUD TP SP16 RA2 ST CEIL LO SPHI K.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY.
    pose proof alloc_ceiling_val as CV.
    unfold NEWAUTO_STACK, MALLOC_STACK in *. unfold VSB_new_auto_entry.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8256, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutPU A [(bv_unsigned sp - 8256, bv_unsigned sp)]).
    { cbn. split; [left; lia| exact I]. }
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 16%nat ST.
    do 3 zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    apply rz_stop.
    pose proof (ainv_munch LayoutPU A m _ md _ AINV MU WM CFP) as AINV1.
    eapply (as_malloc_cps (L:=LayoutPU)) with (n := 40);
      [ exact AINV1 | exact MI | exact LIVEX | reflexivity | lia | rewrite NREQ_CAP_eq; lia | lia | lia | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; unfold MALLOC_STACK; lia
      | rewrite unsigned_lit by lia; eapply (stk_mapped (L:=LayoutPU)); [exact ST| exact CEIL | unfold MALLOC_STACK; lia | lia]
      | ].
    lazymatch goal with |- context [frame_ok] => idtac end.
    lazymatch type of FR with rw_cells _ ?mx _ _ =>
      pose proof (crange_stack (L:=LayoutPU) A mx md (bv_unsigned sp - 16) 16 AINV1 ltac:(lia) ltac:(lia)
                  (rw_cells_mapped LayoutPU mx _ _ FR ltac:(off_image_solve LayoutPU))) as CF end.
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A1 mc1 md1 AINV' MI' MDF OUT FRK.
    pose proof (as_lazy_nil A1 mc1 md1 AINV') as [MDL' MDH'].
    rewrite unsigned_lit in FRK by lia.
    destruct OUT as (NZ & FRESH & LIVEr & LIVEq & LB1 & NL1).   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      acall_xfer FRK. clear AINV1.
      (first [ pose proof ((as_live_ok A1 mc1 md1 r _ AINV' LIVEr)) as dR_1; dand7 dR_1 as _ R16 Rlo Rhi Rimg Rmap Rown | pose proof (as_live_ok A1 mc1 md1 r _ AINV' LIVEr) as (_ & R16 & Rlo & Rhi & Rimg & Rmap & Rown) ]). clear Rimg.
      assert (R8 : r mod 8 = 0) by (apply mod8_of_mod16; exact R16).
      (first [ pose proof ((newblock_cells (L:=LayoutPU) A1 mc1 md1 r _ AINV' LIVEr)) as dR_2; dex1 dR_2 as junk1; dand3 dR_2 as LJ1 NB1 CR1 | pose proof ((newblock_cells (L:=LayoutPU) A1 mc1 md1 r _ AINV' LIVEr)) as dR_2; dand4 dR_2 as junk1 LJ1 NB1 CR1 | destruct (newblock_cells (L:=LayoutPU) A1 mc1 md1 r _ AINV' LIVEr) as (junk1 & LJ1 & NB1 & CR1) ]).
      cbn [al_segs LayoutPU] in NB1.
      (* [comment removed for export] *)
      carve_frame 48%nat ST.
      (* [comment removed for export] *)
      pose proof (munch_refl [(bv_unsigned sp - 8256, bv_unsigned sp); (r, r + 40)] mc1) as MU2.
      pose proof (wmono_refl rsegs mc1) as WM2.
      assert (CFP2 : client_fp LayoutPU A1 [(bv_unsigned sp - 8256, bv_unsigned sp); (r, r + 40)]).
      { cbn. split; [left; lia|]. split; [right; left; exists r, 40; split; [exact LIVEr|lia]| exact I]. }
      rz_resume MDH' MDL'.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ. { exfalso. klia KZ. } clear KZ.
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. do 5 zstep. do 4 zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      call memset_spec_z.
      1:{ exact NB1. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
      rename POST into ZB. change (0 mod 256) with 0 in ZB. change (Z.to_nat 40) with 40%nat in ZB.
      apply (rw_cells_recast rsegs _ r _ vsb_zero_cells) in ZB; [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity | exact vsb_zero_cells_bytes].
      unfold vsb_zero_cells in ZB.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KT; zify_cond KT. { exfalso. rewrite (land7_of_mod8 r) in KT by lia. klia KT. } clear KT.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_false. zstep. if_false.
      (* [comment removed for export] *)
      zstep. zstep. call extendsize0_spec. 1:{ assumption. }
      change (vsb_extendsize 0) with 16.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      apply rz_stop.
      clear CF CR1.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        pose proof (ainv_munch LayoutPU A1 mc1 mx md1 _ AINV' MU2 WM2 CFP2) as AINV2;
        pose_cranges LayoutPU A1 mx AINV2 end.
      eapply (as_malloc_cps (L:=LayoutPU)) with (n := 16);
        [ exact AINV2 | assumption | exists r, 40; exact LIVEr | reflexivity | lia | rewrite NREQ_CAP_eq; lia | lia | lia | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; unfold MALLOC_STACK; lia
        | rewrite unsigned_lit by lia; eapply (stk_mapped (L:=LayoutPU)); [exact ST| exact CEIL | unfold MALLOC_STACK; lia | lia]
        | ].
      intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' b A2 mc2 md3 AINV3 MI3 MDF3 OUT2 FRK2.
      pose proof (as_lazy_nil A2 mc2 md3 AINV3) as [MDL3 MDH3].
      rewrite unsigned_lit in FRK2 by lia.
      (* [comment removed for export] *)
      lazymatch type of MU2 with munch _ _ ?mx =>
        assert (CFa : cframe LayoutPU (owned A) (owned A1) (bv_unsigned sp) 8256 nowhere (blk r 40) m mx)
      end.
      { lazymatch goal with F1 : rw_cells _ _ (bv_unsigned sp + -64) ?cs1, F2 : rw_cells _ _ (bv_unsigned sp + -16) ?cs2 |- _ =>
        eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m _ mc1 _ _ _);
          [ exact MU | | exact FRK | lia | lia | intros a X; destruct X | intros a X; left; exact X
          | exact MU2 |
          | eapply (window_mapped2 _ lo _ _ _ _ cs1 cs2); [exact ST | exact F1 | exact F2 | cbn; lia | cbn; lia | exact CEIL | lia | lia] ] end.
        - intros a Ha NO. cbn [outside] in NO. lia.
        - intros a Ha NO. cbn [outside] in NO. unfold blk. lia. }
      clear MU MU2 WM WM2 CFP CFP2 FRK.
      destruct OUT2 as (NZb & FRESHb & LIVEb & LIVEq3 & LB2 & NL2).   (* [comment removed for export] *)
      + (* [comment removed for export] *)
        acall_xfer FRK2.
        assert (NErb : r <> b) by (intros ->; rewrite FRESHb in LIVEr; discriminate).
        assert (LIVEr3 : a_live A2 r = Some 40) by (rewrite (LIVEq3 r NErb); exact LIVEr).
        (first [ pose proof ((as_live_ok A2 mc2 md3 b _ AINV3 LIVEb)) as dR_3; dand7 dR_3 as _ B16 Blo Bhi Bimg Bmap Bown | pose proof (as_live_ok A2 mc2 md3 b _ AINV3 LIVEb) as (_ & B16 & Blo & Bhi & Bimg & Bmap & Bown) ]). clear Bimg.
        pose proof (as_live_disjoint A2 mc2 md3 r 40 b 16 AINV3 LIVEr3 LIVEb NErb) as DRB.
        (first [ pose proof ((newblock_cells (L:=LayoutPU) A2 mc2 md3 b _ AINV3 LIVEb)) as dR_4; dex1 dR_4 as junkb; dand3 dR_4 as LJb NBb CRb | pose proof ((newblock_cells (L:=LayoutPU) A2 mc2 md3 b _ AINV3 LIVEb)) as dR_4; dand4 dR_4 as junkb LJb NBb CRb | destruct (newblock_cells (L:=LayoutPU) A2 mc2 md3 b _ AINV3 LIVEb) as (junkb & LJb & NBb & CRb) ]).
        cbn [al_segs LayoutPU] in NBb.
        pose proof (munch_refl [(bv_unsigned sp - 8256, bv_unsigned sp); (r, r + 40)] mc2) as MU3.
        pose proof (wmono_refl rsegs mc2) as WM3.
        assert (CFP3 : client_fp LayoutPU A2 [(bv_unsigned sp - 8256, bv_unsigned sp); (r, r + 40)]).
        { cbn. split; [left; lia|]. split; [right; left; exists r, 40; split; [exact LIVEr3|lia]| exact I]. }
        rz_resume MDH3 MDL3.
        zstep. zstep. if_cases KZ; zify_cond KZ. { exfalso. klia KZ. } clear KZ.
        zstep. zstep. zstep. zstep.
        match type of ZB with context [Z.lor ?x ?y] => let v := eval vm_compute in (Z.lor x y) in change (Z.lor x y) with v in ZB end.
        zstep.
        (* [comment removed for export] *)
        zstep. do 5 zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. if_cases KZ; zify_cond KZ. { exfalso. klia KZ. } clear KZ.
        zstep. zstep. if_cases KT; zify_cond KT. { exfalso. rewrite (land7_of_mod8 r) in KT by lia. klia KT. } clear KT.
        zstep. zstep. zstep. zstep.
        match type of ZB with context [Z.lor ?x ?y] => let v := eval vm_compute in (Z.lor x y) in change (Z.lor x y) with v in ZB end.
        zstep.
        (* [comment removed for export] *)
        zstep. do 2 zstep. zstep. zstep.
        lazymatch goal with F1 : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => release_frame F1 ST (bv_unsigned sp + -16) end.
        try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
        release_frame FR ST (bv_unsigned sp).
        cps_done.
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          lazymatch type of MU3 with munch ?W _ _ =>
            pose proof (ainv_munch LayoutPU A2 mc2 mx md3 W AINV3 MU3 WM3 CFP3) as AINV9 end end.
        eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ r A2 _ md3);
          [ exact AINV9 | assumption | eapply md_frame_trans; [exact MDF| exact MDF3] | exact ST | ].
        exists b. split; [exact NZ|]. split; [|split; [exact FRESH|]; split; [|split; [|split; [lia|split; [lia|]]]]].
        * (* [comment removed for export] *)
          unfold vsb_fresh. split. { unfold vsb_cells, VSB_MAGIC, VSB_FLAGS_LIVE. cbn [vb_error vb_buf vb_size vb_len vb_flags vb_indent]. exact ZB. }
          split. { unfold vsb_inv, VSB_FLAGS_LIVE; cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf]. lia. }
          cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf].
          split; [exact LIVEr3|]. split; [exact LIVEb|]. split; [exact NErb|].
          exists junkb. split; [eapply u8arr_of_rw_cells; exact NBb|]. split; [cbn [vb_size]; lia| intros X; discriminate X].
        * rewrite <- (LIVEq b ltac:(intros E; exact (NErb (eq_sym E)))). exact FRESHb.
        * intros q Q1 Q2. rewrite (LIVEq3 q Q2). apply LIVEq, Q1.
        * lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?mx =>
            lazymatch type of CFa with cframe _ _ _ _ _ _ _ _ ?ma =>
            assert (CFb : cframe LayoutPU (owned A1) (owned A2) (bv_unsigned sp) 8256 (blk r 40) (blk b 16) ma mx)
              by (eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ ma ma mc2 _ [] _);
                  [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK2 | lia | lia
                  | intros a X; destruct X | intros a X; left; exact X | exact MU3 |
                  | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia] ];
                  intros a Ha NO; cbn [outside] in NO; unfold blk; lia);
            eapply (cframe_seq LayoutPU _ _ _ _ _ _ _ _ _ _ _ _ _ m ma mx CFa CFb); [lia | lia
                | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia]
                | intros a X; destruct X | intros a X; left; exact X
                | intros a [X|X]; [left; exact X| right; left; exact X] ]
          end end.
  Qed.
End S.

