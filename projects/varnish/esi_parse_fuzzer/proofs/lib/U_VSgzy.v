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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac mem_side := cbn; first [ (let E := fresh "E" in intros E; discriminate E) | solve [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ exact I | reflexivity ] ] | solve [ repeat first [ left; reflexivity | right ] ] | tauto ].
Local Ltac mem_hyp Hr := cbn in Hr; first [ solve [ repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]); first [ discriminate Hr | destruct Hr ] ] | intuition discriminate ].
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

Definition VSB_destroy_entry := 0x19d18.
(* [comment removed for export] *)
Definition DESTROY_STACK := 16 + FREE_STACK.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Lemma VSB_destroy_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (PS S : Z) (v : vsb_rec) (fin : bool) (lo : Z) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 PS ->
      rw_cells rsegs m PS [C8 (w64 S)] -> cvar LayoutPU A (bv_unsigned sp) [S; vb_buf v] PS 8 -> PS mod 8 = 0 ->
      vsb_obj LayoutPU A m S v fin ->
      tp = al_tp LayoutPU -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + DESTROY_STACK <= bv_unsigned sp ->
      bv_unsigned sp + 64 <= 2^47 ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) ->
          rw_cells rsegs m' PS [C8 (w64 0)] ->
          a_live A' S = None -> a_live A' (vb_buf v) = None ->
          (forall q, q <> S -> q <> vb_buf v -> a_live A' q = a_live A q) ->
          a_livebytes A' = a_livebytes A - 40 - vb_size v -> a_nlive A' = a_nlive A - 2 ->   (* [comment removed for export] *)
          cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) DESTROY_STACK
                 (fun a => blk S 40 a \/ blk (vb_buf v) (vb_size v) a \/ PS <= a < PS + 8) nowhere m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 VSB_destroy_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. intros AINV MI A0 PSC CV PS8 VOBJ TP SP16 RA2 ST CEIL LO SPHI K.
    rewrite A0.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY.
    pose proof alloc_ceiling_val as ACV.
    (first [ pose proof ((vsb_obj_geom LayoutPU A m md S v fin AINV VOBJ)) as dR_1; dand11 dR_1 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutPU A m md S v fin AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    vsb_open VOBJ. (first [ dex1 VBUF as bs0; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs0 U8 LBS _ | destruct VBUF as (bs0 & U8 & LBS & _) ]). cbn [al_segs LayoutPU] in U8.
    pose proof VINV as VINV0. (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    unfold DESTROY_STACK, FREE_STACK in *. unfold VSB_destroy_entry.
    (* [comment removed for export] *)
    (first [ pose proof ((cvar_facts LayoutPU A m md _ _ PS 8 lo AINV CV CEIL ltac:(lia))) as dR_4; dand6 dR_4 as PScfp PSW PSlo PShi PSimg PSX | pose proof (cvar_facts LayoutPU A m md _ _ PS 8 lo AINV CV CEIL ltac:(lia)) as (PScfp & PSW & PSlo & PShi & PSimg & PSX) ]).
    assert (PSS : PS + 8 <= S \/ S + 40 <= PS) by (apply (PSX S 40); [mem_side| exact VLS]).
    assert (PSB : PS + 8 <= vb_buf v \/ vb_buf v + vb_size v <= PS) by (apply (PSX (vb_buf v) (vb_size v)); [mem_side| exact VLB]).
    clear PSX.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8208, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutPU A [(bv_unsigned sp - 8208, bv_unsigned sp)]).
    { cbn. split; [left; lia| exact I]. }
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 16%nat ST.
    assert (S8 : S mod 8 = 0) by (apply mod8_of_mod16; exact S16).
    do 3 zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { exfalso. klia K0. } clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KT; zify_cond KT. { exfalso. rewrite (land7_of_mod8 PS) in KT by lia. klia KT. } clear KT.
    (* [comment removed for export] *)
    zstep. zstep. call (assert_integrity_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S v fin).
    1:{ reflexivity. } 1:{ exact VSBC. } 1:{ exact VINV0. } 1:{ exact Slo. } 1:{ exact S8. } 1:{ assumption. }
    (* [comment removed for export] *)
    zstep. zstep. if_cases KT; zify_cond KT. { exfalso. klia KT. } clear KT.
    zstep. zstep. if_cases KT; zify_cond KT. { exfalso. rewrite (land7_of_mod8 S) in KT by lia. klia KT. } clear KT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KD; zify_cond KD. { exfalso. revert KD. rewrite Vfl. destruct fin; vm_compute; congruence. } clear KD.
    zstep. zstep. if_cases KT; zify_cond KT. { exfalso. revert KT. rewrite Vfl. destruct fin; vm_compute; congruence. } clear KT.
    (* [comment removed for export] *)
    zstep. zstep.
    apply rz_stop.
    pose proof (ainv_munch LayoutPU A m _ md _ AINV MU WM CFP) as AINV1.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose_cranges LayoutPU A mx AINV1;
      pose proof (crange_of_cfp LayoutPU A mx md PS 8 AINV1 PScfp (rw_cells_mapped LayoutPU mx PS _ PSC PSimg) ltac:(lia) PSimg) as CRPS end.
    eapply (as_free_cps (L:=LayoutPU)) with (p := vb_buf v) (n0 := vb_size v);
      [ exact AINV1 | assumption | reflexivity | right; exact VLB | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; unfold FREE_STACK; lia
      | rewrite unsigned_lit by lia; eapply (stk_mapped (L:=LayoutPU)); [exact ST| exact CEIL | unfold FREE_STACK; lia | lia]
      | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 AINV' MI' MDF DEADb LIVEq LBf1 NLf1 _ FRK.
    pose proof (as_lazy_nil A1 m1 md1 AINV') as [MDL' MDH'].
    rewrite unsigned_lit in FRK by lia.
    try clear U8. acall_xfer FRK. clear AINV1.
    assert (LS1 : a_live A1 S = Some 40) by (rewrite (LIVEq S VNE); exact VLS).
    assert (CV1 : cvar LayoutPU A1 (bv_unsigned sp) [S] PS 8).
    { eapply (cvar_keep LayoutPU A A1); [exact CV|]. intros p k LP NI. cbn in NI.
      split; [rewrite LIVEq; [exact LP| intros ->; apply NI; right; left; reflexivity]
            | cbn; intros [X|X]; [apply NI; left; exact X| exact X] ]. }
    pose proof (proj1 (cvar_facts LayoutPU A1 m1 md1 _ _ PS 8 lo AINV' CV1 CEIL ltac:(lia))) as PScfp1.
    (* [comment removed for export] *)
    destruct (rw_cells_forget _ _ _ _ VSBC) as [junkS VSBS]. cbn [cells_size csize Nat.add] in VSBS.
    pose proof (munch_refl [(bv_unsigned sp - 8208, bv_unsigned sp); (S, S + 40); (PS, PS + 8)] m1) as MU2.
    pose proof (wmono_refl rsegs m1) as WM2.
    assert (CFP2 : client_fp LayoutPU A1 [(bv_unsigned sp - 8208, bv_unsigned sp); (S, S + 40); (PS, PS + 8)]).
    { cbn. split; [left; lia|]. split; [right; left; exists S, 40; split; [exact LS1|lia]|]. split; [exact PScfp1| exact I]. }
    rz_resume MDH' MDL'.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    call memset_spec_z.
    1:{ exact VSBS. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep.
    apply rz_stop.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (ainv_munch LayoutPU A1 m1 mx md1 _ AINV' MU2 WM2 CFP2) as AINV2;
      pose_cranges LayoutPU A1 mx AINV2;
      pose proof (crange_of_cfp LayoutPU A1 mx md1 PS 8 AINV2 PScfp1 (rw_cells_mapped LayoutPU mx PS _ PSC PSimg) ltac:(lia) PSimg) as CRPS2
    end.
    eapply (as_free_cps (L:=LayoutPU)) with (p := S) (n0 := 40);
      [ exact AINV2 | assumption | reflexivity | right; exact LS1 | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; unfold FREE_STACK; lia
      | rewrite unsigned_lit by lia; eapply (stk_mapped (L:=LayoutPU)); [exact ST| exact CEIL | unfold FREE_STACK; lia | lia]
      | ].
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A2 m3 md3 AINV3 MI3 MDF3 DEADS LIVEq3 LBf2 NLf2 _ FRK2.
    pose proof (as_lazy_nil A2 m3 md3 AINV3) as [MDL3 MDH3].
    rewrite unsigned_lit in FRK2 by lia.
    (* [comment removed for export] *)
    lazymatch type of MU2 with munch _ _ ?mx =>
      assert (CFa : cframe LayoutPU (owned A) (owned A1) (bv_unsigned sp) 8208
                       (fun a => blk S 40 a \/ blk (vb_buf v) (vb_size v) a \/ PS <= a < PS + 8) nowhere m mx)
        by (eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m _ m1 _ _ _);
            [ exact MU | | exact FRK | unfold FREE_STACK; lia | lia | intros a X; right; left; exact X | intros a X; destruct X
            | exact MU2 | | eapply (window_mapped LayoutPU _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia] ];
            [ intros a Ha NO; cbn [outside] in NO; lia
            | intros a Ha NO; cbn [outside] in NO; unfold blk; lia ])
    end.
    try clear POST. acall_xfer FRK2. clear AINV2 MU2 WM2 CFP2.
    assert (CV3 : cvar LayoutPU A2 (bv_unsigned sp) [] PS 8).
    { eapply (cvar_keep LayoutPU A1 A2); [exact CV1|]. intros p k LP NI. cbn in NI.
      split; [rewrite LIVEq3; [exact LP| intros ->; apply NI; left; reflexivity] | cbn; intros X; exact X]. }
    pose proof (proj1 (cvar_facts LayoutPU A2 m3 md3 _ _ PS 8 lo AINV3 CV3 CEIL ltac:(lia))) as PScfp3.
    pose proof (munch_refl [(bv_unsigned sp - 8208, bv_unsigned sp); (PS, PS + 8)] m3) as MU3.
    pose proof (wmono_refl rsegs m3) as WM3.
    assert (CFP3 : client_fp LayoutPU A2 [(bv_unsigned sp - 8208, bv_unsigned sp); (PS, PS + 8)]).
    { cbn. split; [left; lia|]. split; [exact PScfp3| exact I]. }
    rz_resume MDH3 MDL3.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    cps_done.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      lazymatch type of MU3 with munch ?W _ _ =>
        pose proof (ainv_munch LayoutPU A2 m3 mx md3 W AINV3 MU3 WM3 CFP3) as AINV9 end end.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A2 _ md3);
      [ exact AINV9 | assumption | eapply md_frame_trans; [exact MDF| exact MDF3] | exact ST
      | assumption | exact DEADS | rewrite (LIVEq3 _ (fun E => VNE (eq_sym E))); exact DEADb
      | intros q Q1 Q2; rewrite (LIVEq3 q Q1); apply LIVEq, Q2
      | rewrite LBf2, LBf1; lia
      | rewrite NLf2, NLf1;
        replace (vb_buf v =? 0) with false by (symmetry; apply Z.eqb_neq; unfold vsb_inv in *; lia);
        replace (S =? 0) with false by (symmetry; apply Z.eqb_neq; lia); lia
      | ].
    lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?mx =>
      assert (CFb : cframe LayoutPU (owned A1) (owned A2) (bv_unsigned sp) 8208
                       (fun a => blk S 40 a \/ blk (vb_buf v) (vb_size v) a \/ PS <= a < PS + 8) nowhere _ mx)
        by (eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ _ _ m3 _ [] _);
            [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK2 | unfold FREE_STACK; lia | lia
            | intros a X; left; exact X | intros a X; destruct X | exact MU3 |
            | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia] ];
            intros a Ha NO; cbn [outside] in NO; lia);
      eapply (cframe_seq LayoutPU _ _ _ _ _ _ _ _ _ _ _ _ _ m _ mx CFa CFb); [lia | lia
          | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia]
          | intros a X; exact X | intros a X; right; exact X | intros a X; destruct X ]
    end.
  Qed.
End S.
