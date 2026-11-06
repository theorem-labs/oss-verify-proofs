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
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_PMark V_PD648.

Module V_VS1zl.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb Img0 V_VSgtv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
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

Definition VSB_putc_entry := 0x19a34.
(* [comment removed for export] *)
Definition PUTC_STACK := 32 + EXT_STACK.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  Lemma VSB_putc_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (S : Z) (v : vsb_rec) (lo : Z) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 S ->
      vsb_obj LayoutP0 A m S v false ->
      vb_size v + 1 <= EXT_MAX ->
      a_livebytes A + vsb_extendsize (vb_size v + 1) <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + PUTC_STACK <= bv_unsigned sp ->
      bv_unsigned sp + 64 <= 2^47 ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          vsb_obj LayoutP0 A' m' S v' false ->
          vb_len v <= vb_len v' <= vb_len v + 1 -> vb_size v <= vb_size v' <= Z.max (vb_size v) (vb_len v' + 4096) ->   (* [comment removed for export] *)
          (forall q, q <> vb_buf v -> q <> vb_buf v' -> a_live A' q = a_live A q) ->
          (vb_buf v' = vb_buf v \/ (a_live A (vb_buf v') = None /\ a_live A' (vb_buf v) = None)) ->
          a_livebytes A' = a_livebytes A + vb_size v' - vb_size v -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
          stk rsegs m' lo (bv_unsigned sp) ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) PUTC_STACK
                   (fun a => blk (vb_buf v) (vb_size v) a \/ (S <= a < S + 40))
                   (blk (vb_buf v') (vb_size v')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 VSB_putc_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. intros AINV MI A0 VOBJ EM LBUD NBUD TP SP16 ST CEIL LO SPHI K.
    rewrite A0.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md S v false AINV VOBJ)) as dR_1; dand11 dR_1 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md S v false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof alloc_ceiling_val as CV.
    vsb_open VOBJ. (first [ dex1 VBUF as bs0; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs0 U8 LBS _ | destruct VBUF as (bs0 & U8 & LBS & _) ]). cbn [al_segs LayoutP0] in U8.
    pose proof VINV as VINV0. (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
    unfold PUTC_STACK, EXT_STACK, REALLOC_STACK, EXT_MAX in *. unfold VSB_putc_entry.
    pose proof (munch_refl [(bv_unsigned sp - 8336, bv_unsigned sp); (S, S + 40); (vb_buf v, vb_buf v + vb_size v)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 8336, bv_unsigned sp); (S, S + 40); (vb_buf v, vb_buf v + vb_size v)]).
    { cbn. split; [left; lia|]. split; [right; left; exists S, 40; split; [exact VLS|lia]|].
      split; [right; left; exists (vb_buf v), (vb_size v); split; [exact VLB|lia]| exact I]. }
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 32%nat ST.
    do 4 zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep.
    carve_frame 16%nat ST.
    zstep. zstep.
    zstep. if_cases K1; zify_cond K1. { exfalso. klia K1. } clear K1.
    zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. revert K2. vm_compute. congruence. } clear K2.
    zstep. zstep. if_cases K3; zify_cond K3. { exfalso. klia K3. } clear K3.
    zstep. zstep. zstep. if_cases K4; zify_cond K4. { exfalso. unsign K4. klia K4. } clear K4.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    release_frame FR0 ST (bv_unsigned sp - 32).
    (* [comment removed for export] *)
    pose proof (rw_cells_read_sub rsegs _ _ _ 34 1 VSBC ltac:(lia) ltac:(cbn; lia)) as RDF.
    rewrite Vfl in RDF. unfold VSB_FLAGS_LIVE in RDF.
    match type of RDF with _ = Some ?r => let r' := eval vm_compute in r in change r with r' in RDF end.
    zstep. zstep. zstep. if_cases K5; zify_cond K5. { dead K5. } clear K5 RDF.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases KI; zify_cond KI. 2:{ rewrite Vind in KI. dead KI. } clear KI.
      zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. if_cases KR; zify_cond KR.
      + (* [comment removed for export] *)
        unsign KR.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        pose proof (u8arr_store_ok rsegs _ _ _ (vb_len v) _ U8 ltac:(lia) eq_refl) as SOK.
        zstep. rewrite le1_single.
        pose proof (u8arr_write rsegs _ _ _ (vb_len v) (Z_to_bv 8 (bv_unsigned a1)) U8 ltac:(lia)) as U8'. clear U8. store_done.
        (* [comment removed for export] *)
        zstep. zstep. zstep. do 4 zstep. zstep.
        try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
        release_frame FR ST (bv_unsigned sp).
        cps_done.
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          lazymatch type of MU with munch ?W _ _ =>
          pose proof (ainv_munch LayoutP0 A m mx md W AINV MU WM CFP) as AINV9
          end end.
        eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A _ md (vsb_set_len v (vb_len v + 1)));
          [ exact AINV9 | exact MI | | | cbn [vsb_set_len vb_len]; lia | cbn [vsb_set_len vb_size vb_len]; lia
          | intros q _ _; reflexivity | left; reflexivity | cbn [vsb_set_len vb_size]; lia | reflexivity | exact ST | ].
        * (* [comment removed for export] *) OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity; assumption.
        * (* [comment removed for export] *)
          split; [exact VSBC|]. split; [unfold vsb_inv; cbn [vsb_set_len vb_size vb_len vb_error vb_indent vb_flags vb_buf]; lia|].
          split; [exact VLS|]. split; [exact VLB|]. split; [exact VNE|].
          eexists. split; [exact U8'|]. split; [rewrite upd_length; cbn [vsb_set_len vb_size vb_len]; lia| intros X; discriminate X].
        * cbn [vsb_set_len vb_buf vb_size].
          eapply (cframe_noalloc LayoutP0); [exact MU | | | intros a X; left; exact X].
          -- intros a Ha NO. cbn [outside] in NO. unfold blk. lia.
          -- eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | lia | lia].
      + (* [comment removed for export] *)
        unsign KR.
        zstep. zstep. zstep.
        apply rz_stop.
        pose proof (ainv_munch LayoutP0 A m _ md _ AINV MU WM CFP) as AINV1.
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          pose proof (crange_stack (L:=LayoutP0) A mx md (bv_unsigned sp - 32) 32 AINV1 ltac:(lia) ltac:(lia)
                        (rw_cells_mapped LayoutP0 mx _ _ FR ltac:(off_image_solve LayoutP0))) as CF end.
        eapply VSB_extend_cps;
          [ exact AINV1 | exact MI | reflexivity | reflexivity
          | split; [exact VSBC|]; split; [exact VINV0|]; split; [exact VLS|]; split; [exact VLB|]; split; [exact VNE|];
            exists bs0; split; [exact U8|]; split; [exact LBS| intros X; discriminate X]
          | lia | exact EM | exact LBUD | exact NBUD | exact TP
          | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
          | rewrite unsigned_lit by lia; reflexivity
          | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; unfold EXT_STACK, REALLOC_STACK; lia
          | rewrite unsigned_lit by lia; lia | ].
        clear VSBC U8.
        intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' v' AINV' MI' MDF VOBJ' LIVEq ST' OUT.
        pose proof (as_lazy_nil A' m' md' AINV') as [MDL' MDH'].
        rewrite unsigned_lit in OUT, ST' by lia.
        (first [ pose proof ((vsb_obj_geom LayoutP0 A' m' md' S v' false AINV' VOBJ')) as dR_4; dand11 dR_4 as _ _ _ _ B16' Blo' Bhi' Bimg' DSB' Smap' Bmap' | pose proof (vsb_obj_geom LayoutP0 A' m' md' S v' false AINV' VOBJ') as (_ & _ & _ & _ & B16' & Blo' & Bhi' & Bimg' & DSB' & Smap' & Bmap') ]).
        clear Bimg'.
        vsb_open VOBJ'. (first [ dex1 VBUF as bs1; dand3 VBUF as U8n LBS1 _ | dand4 VBUF as bs1 U8n LBS1 _ | destruct VBUF as (bs1 & U8n & LBS1 & _) ]). cbn [al_segs LayoutP0] in U8n.
        pose proof VINV as VINV1. (first [ dand8 VINV as Vsz' Vlen' Verr' Vind' Vfl' Vb0' Vb47' Vbm' | destruct VINV as (Vsz' & Vlen' & Verr' & Vind' & Vfl' & Vb0' & Vb47' & Vbm') ]).
        destruct OUT as (nb & Er & Ev & COPY & REL & LBx & NLx & FRK); subst r.   (* [comment removed for export] *)
        * (* [comment removed for export] *)
          assert (E0 : vb_error v = 0) by exact Verr.
          pose proof (vsb_extendsize_tight (vb_size v + 1)) as NST.
          subst v'. cbn [vb_buf vb_size vb_len vb_error vb_flags vb_indent vsb_set_buf_size] in *.
          (first [ pose proof ((vsb_extendsize_spec (vb_size v + 1) ltac:(lia))) as dR_7; dand3 dR_7 as NS1 NS2 NS3 | pose proof (vsb_extendsize_spec (vb_size v + 1) ltac:(lia)) as (NS1 & NS2 & NS3) ]).
          clear ST. acall_xfer FRK. clear AINV1. rename ST' into ST.
          set (W2 := [(bv_unsigned sp - 8336, bv_unsigned sp); (S, S + 40); (nb, nb + vsb_extendsize (vb_size v + 1))]).
          pose proof (munch_refl W2 m') as MU2. pose proof (wmono_refl rsegs m') as WM2.
          subst W2.
          rz_resume MDH' MDL'.
          zstep. if_cases KX; zify_cond KX. { dead KX. } clear KX.
          (* [comment removed for export] *)
          zstep. zstep. if_cases KY; zify_cond KY. { exfalso. rewrite E0 in KY. revert KY. vm_compute. congruence. } clear KY.
          (* [comment removed for export] *)
          zstep.
          zstep. zstep. zstep. zstep.
          pose proof (u8arr_store_ok rsegs _ _ _ (vb_len v) _ U8n ltac:(lia) eq_refl) as SOK.
          zstep. rewrite le1_single.
          pose proof (u8arr_write rsegs _ _ _ (vb_len v) (Z_to_bv 8 (bv_unsigned a1)) U8n ltac:(lia)) as U8'. clear U8n. store_done.
          zstep. zstep. zstep. do 4 zstep. zstep.
          try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
          release_frame FR ST (bv_unsigned sp).
          cps_done.
          lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
            lazymatch type of MU2 with munch ?W _ _ =>
            assert (CFP' : client_fp LayoutP0 A' W)
              by (cbn; split; [left; lia|]; split; [right; left; exists S, 40; split; [exact VLS0|lia]|];
                  split; [right; left; eexists _, _; split; [exact VLB0| lia]| exact I]);
            pose proof (ainv_munch LayoutP0 A' m' mx md' W AINV' MU2 WM2 CFP') as AINV9
            end end.
          eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' _ md'
                    (vsb_set_len (vsb_set_buf_size v nb (vsb_extendsize (vb_size v + 1))) (vb_len v + 1)));
            [ exact AINV9 | exact MI' | exact MDF | | cbn [vsb_set_len vsb_set_buf_size vb_len]; lia
            | cbn [vsb_set_len vsb_set_buf_size vb_size vb_len]; lia
            | exact LIVEq | exact REL | cbn [vsb_set_len vsb_set_buf_size vb_size]; lia | exact NLx | exact ST | ].
          -- split; [exact VSBC|]. split; [unfold vsb_inv; cbn [vsb_set_len vsb_set_buf_size vb_size vb_len vb_error vb_indent vb_flags vb_buf]; unfold vsb_inv in VINV1; cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf vsb_set_buf_size] in VINV1; lia|].
             split; [exact VLS0|]. split; [exact VLB0|]. split; [exact VNE0|].
             eexists; split; [exact U8'|]. split; [rewrite upd_length; cbn [vsb_set_len vsb_set_buf_size vb_size]; lia| intros X; discriminate X].
          -- cbn [vsb_set_len vsb_set_buf_size vb_buf vb_size].
             eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m _ m' _ _ _);
               [ exact MU | | exact FRK | unfold EXT_STACK, REALLOC_STACK; lia | lia | intros a X; exact X
               | intros a X; left; exact X
               | exact MU2 | | eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | lia | lia] ].
             ++ intros a Ha NO. cbn [outside] in NO. unfold blk. lia.
             ++ intros a Ha NO. cbn [outside] in NO. unfold blk. lia.
    - (* [comment removed for export] *)
      exfalso. rewrite Verr in KE. revert KE. vm_compute. congruence.
  Qed.
End S.
End V_VS1zl.

Module V_PPutc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c V_Paq9r V_PKit V_VSgtv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSgtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH4jn.V_VS1zl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  Definition after_putc (x : pst) (y1 : vsb_rec) : pst :=
    PST (x_p x + 1) (x_st x) (x_v x) (x_tag x) (x_q x) (x_vv x) (Some y1) (x_vi x).

  Lemma putc_call : forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet) (ret : Z) (y : vsb_rec)
      (fj0 fj8 : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
    penv_ok E -> pinv E x A m -> ainv A m md ->
    x_va x = Some y -> x_st x = S_AttrValue -> x_p x < pe_e E -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
    rw_cells rsegs m (pe_sp E) (pframe E fj0 fj8) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A1 : AS) (m1 : mem) (md1 : Model)
            (y1 : vsb_rec) (x1 : pst),
        x1 = after_putc x y1 ->
        pinv E x1 A1 m1 -> ainv A1 m1 md1 -> md_frame md md1 ->
        hstep E x x1 A A1 m m1 ->
        vb_len y <= vb_len y1 <= vb_len y + 1 ->
        rw_cells rsegs m1 (pe_sp E) (pframe E fj0 fj8) ->
        realizes rsegs (mkCfg (loop_ms E ret (x_p x) (Z_to_bv 64 ret) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7 t3' t4' t5' t6' m1) md1) T) ->
    realizes rsegs (mkCfg (loop_ms E VSB_putc_entry (x_p x) (Z_to_bv 64 ret) t0 t1 t2
                             (Z_to_bv 64 (x_v x Fattr_vsb)) a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m) md) T.
  Proof.
    intros until t6. intros PE PI AINV EVA STx PLT RR RET FRX K.
    (* [comment removed for export] *)
    (first [ pose proof ((pinv_sizes _ _ _ _ PI)) as dR_s; dand4 dR_s as OUT7 WBB LEN0 SZ0 | pose proof (pinv_sizes _ _ _ _ PI) as (OUT7 & WBB & LEN0 & SZ0) ]).
    pose proof (pw_nlive_range (x_va x) (x_vi x)) as WNL.
    world_open PE PI AINV.
    rewrite EVA in VA. (first [ dand4 VA as ANZ AOBJ AROOM AAP | destruct VA as (ANZ & AOBJ & AROOM & AAP) ]).
    (first [ pose proof (AOBJ) as dR_2; dand6 dR_2 as _ _ LAS LAB ASB _ | pose proof AOBJ as (_ & _ & LAS & LAB & ASB & _) ]).
    unfold oabuf in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI. rewrite EVA in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI.
    assert (SPR : 0 <= pe_sp E < 2^64) by (clear - FRB; lia).
    unfold loop_ms.
    eapply (VSB_putc_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A (x_v x Fattr_vsb) y (pe_lo E)).
    1:{ exact AINV. }
    1:{ exact MI. }
    1:{ reflexivity. }
    1:{ exact AOBJ. }
    1:{ assert (LVV0 : 0 <= vb_len (x_vv x)) by (clear - VSBO; (first [ dand3 VSBO as _ VI' _ | destruct VSBO as (_ & VI' & _) ]); unfold vsb_inv in VI'; lia).
        revert AROOM OUT OI0 CNT VERP PLE NN DLEN EVA LVV0. clear. unfold oacost, oicost, vep_cnt, EXT_MAX.
        intros AROOM OUT OI0 CNT VERP PLE NN DLEN EVA LVV0. rewrite EVA in OUT. lia. }
    1:{ (* [comment removed for export] *)
        pose proof (vsb_extendsize_tight (vb_size y + 1)) as EXT.
        revert LB BUDL WBB EXT AROOM OUT7 OI0 LEN0 NN EVA. clear. unfold PARSE_LIVE, pe_N, oacost.
        intros LB BUDL WBB EXT AROOM OUT7 OI0 LEN0 NN EVA. rewrite EVA in OUT7. lia. }
    1:{ revert NL BUDN WNL. clear. unfold PARSE_NLIVE. intros; lia. }
    1:{ reflexivity. }
    1:{ rewrite unsigned_lit by exact SPR. rewrite PSP, Zminus_mod, G1. reflexivity. }
    1:{ rewrite unsigned_lit by exact SPR. exact STK. }
    1:{ exact CEIL. }
    1:{ rewrite unsigned_lit by exact SPR. revert LOP PSP. clear. unfold PUTC_STACK, EXT_STACK. unfold_stacks_g. intros; lia. }
    1:{ rewrite unsigned_lit by exact SPR. revert G3 PSP. clear. unfold HFRAME. intros; lia. }
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 y1 AINV1 MI1 MDF VSO1 LEN1 SZ1 LIVE1 REL LB1 NL1 ST1 CF1.
    rewrite unsigned_lit in ST1, CF1 by exact SPR.
    rewrite (ret_pc_even ret RR RET).
    pose proof (as_lazy_nil _ _ _ AINV1) as [MDL1 MDH1].
    set (Vp := fun a : Z => blk (vb_buf y) (vb_size y) a \/ x_v x Fattr_vsb <= a < x_v x Fattr_vsb + 40) in CF1.
    (* [comment removed for export] *)
    assert (HC : hcover A [pe_VEP E; pe_S E; vb_buf (x_vv x); pe_DATA E] Vp).
    { intros a [X|X].
      - eapply hcover_blk; [exact LAB| wz_not_in| exact X].
      - eapply hcover_rng; [exact LAS| wz_not_in| exact X]. }
    pose proof (hcover_vcover (pe_H E) _ _ _ HC) as CV1.
    assert (WIN : alloc_ceiling <= pe_sp E - PUTC_STACK) by (revert CEIL LOP PSP; clear; unfold PUTC_STACK, EXT_STACK; unfold_stacks_g; intros; lia).
    assert (WPOS : 0 <= PUTC_STACK) by (clear; unfold PUTC_STACK, EXT_STACK; unfold_stacks_g; lia).
    assert (SPH : pe_sp E <= h_sp (pe_H E)) by (rewrite PSP; clear; lia).
    (* [comment removed for export] *)
    assert (LVEP1 : a_live A1 (pe_VEP E) = Some 312) by (eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LVEP| exact (not_eq_sym D_ABV)]).
    assert (LVS1 : a_live A1 (pe_S E) = Some 40) by (eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LVS| exact (not_eq_sym D_ABS)]).
    assert (LVB1 : a_live A1 (vb_buf (x_vv x)) = Some (vb_size (x_vv x))) by (eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LVB| exact (not_eq_sym D_ABB)]).
    assert (LDATA1 : a_live A1 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))) by (eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LDATA| exact (not_eq_sym D_ABD)]).
    assert (WAL1 : a_live A1 (pe_wa E) = Some 40) by (eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact WAL| exact (not_eq_sym D_ABW)]).
    assert (NB_V : pe_VEP E <> vb_buf y1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LVEP| exact (not_eq_sym D_ABV)]).
    assert (NB_W : pe_wa E <> vb_buf y1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact WAL| exact (not_eq_sym D_ABW)]).
    assert (NB_D : pe_DATA E <> vb_buf y1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LDATA| exact (not_eq_sym D_ABD)]).
    assert (NB_S : pe_S E <> vb_buf y1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LVS| exact (not_eq_sym D_ABS)]).
    assert (NB_B : vb_buf (x_vv x) <> vb_buf y1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LVB| exact (not_eq_sym D_ABB)]).
    (* [comment removed for export] *)
    assert (VEPO1 : vep_obj LayoutP0 A1 m1 (pe_VEP E) (x_v x) (x_tag x) (x_q x)).
    { eapply (vep_obj_call (pe_H E) A A1 m m1 md (pe_sp E) PUTC_STACK Vp _ [pe_VEP E; pe_S E; vb_buf (x_vv x); pe_DATA E] AINV CF1 HG WIN);
        [exact CV1| in_list| exact LVEP1| split; [exact LVEP|]; split; [unfold vep_cells; rewrite STATE; exact VEPC|]; split; [exact TAG| exact PADS]]. }
    assert (FR1 : rw_cells rsegs m1 (pe_sp E) (pframe E fj0 fj8)).
    { eapply (pframe_call E A A1 m m1 md (pe_sp E) PUTC_STACK Vp _ [pe_VEP E; pe_S E; vb_buf (x_vv x); pe_DATA E]);
        [exact PE| exact AINV| exact CF1| exact WIN| exact WPOS| clear; lia| exact CV1| exact FRX]. }
    assert (IMG1 : img_ok0 m1).
    { eapply (img_call (pe_H E) A A1 m m1 md (pe_sp E) PUTC_STACK Vp _ [pe_VEP E; pe_S E; vb_buf (x_vv x); pe_DATA E] AINV CF1 HG WIN); [exact CV1| exact IMG]. }
    assert (HENV1 : henv_ok LayoutP0 VI0 (pe_H E) m1).
    { eapply (henv_call (pe_H E) A A1 m m1 md (pe_sp E) PUTC_STACK Vp _ [pe_VEP E; pe_S E; vb_buf (x_vv x); pe_DATA E] AINV CF1 HG WIN SPH); [exact HC| exact HENV]. }
    assert (DATA1 : data_obj LayoutP0 A1 m1 (pe_DATA E) (pe_inp E)).
    { eapply (data_obj_call (pe_H E) A A1 m m1 md (pe_sp E) PUTC_STACK Vp _ [pe_VEP E; pe_S E; vb_buf (x_vv x); pe_DATA E] AINV CF1 HG WIN);
        [exact CV1| in_list| exact LDATA1| exact DATA]. }
    assert (VSBO1 : vsb_obj LayoutP0 A1 m1 (pe_S E) (x_vv x) false).
    { eapply (vsb_obj_call (pe_H E) A A1 m m1 md (pe_sp E) PUTC_STACK Vp _ [pe_VEP E; pe_S E; vb_buf (x_vv x); pe_DATA E] AINV CF1 HG WIN);
        [exact CV1| in_list| in_list| exact LVS1| exact LVB1| exact VSBO]. }
    assert (VI1 : vi_world E (after_putc x y1) A1 m1).
    { unfold vi_world, after_putc. cbn [x_vi x_v x_va x_vv].
      destruct (x_vi x) as [yi|] eqn:EVI; [| exact VI].
      (first [ dand6 VI as Q1 Q2 Q3 Q3b Q4 Q5 | destruct VI as (Q1 & Q2 & Q3 & Q3b & Q4 & Q5) ]). (first [ pose proof ((D_AI ltac:(discriminate) ltac:(discriminate))) as dR_5; dand4 dR_5 as NIA NIB NBA NBB | destruct (D_AI ltac:(discriminate) ltac:(discriminate)) as (NIA & NIB & NBA & NBB) ]).
      unfold oibuf in NBA, NBB, D_IBV, D_IBS, D_IBB, D_IBD. rewrite EVI in NBA, NBB, D_IBV, D_IBS, D_IBB, D_IBD.
      (first [ pose proof (Q2) as dR_6; dand5 dR_6 as _ _ LIS LIB _ | pose proof Q2 as (_ & _ & LIS & LIB & _) ]).
      assert (HCi : hcover A [x_v x Finclude_src; vb_buf yi] Vp).
      { intros a [X|X].
        - eapply hcover_blk; [exact LAB| wz_not_in| exact X].
        - eapply hcover_rng; [exact LAS| wz_not_in| exact X]. }
      refine (conj Q1 (conj _ (conj Q3 (conj Q3b (conj Q4 _))))).
      - eapply (vsb_obj_call (pe_H E) A A1 m m1 md (pe_sp E) PUTC_STACK Vp _ [x_v x Finclude_src; vb_buf yi] AINV CF1 HG WIN);
          [exact (hcover_vcover (pe_H E) _ _ _ HCi)| in_list| in_list
          | eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LIS| exact NIB]
          | eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LIB| exact NBB]
          | exact Q2].
      - intros z Hz. cbn in Hz. destruct Hz as [<-|[<-|[]]].
        + exact (conj NIA NBA).
        + split; [eapply (fresh_ne _ _ _ _ _ _ REL); [exact LIS| exact NIB] | eapply (fresh_ne _ _ _ _ _ _ REL); [exact LIB| exact NBB]]. }
    assert (PI1 : pinv E (after_putc x y1) A1 m1).
    { unfold after_putc. apply Build_pinv; psimp; rewrite ?STx; cbn beta iota; try pinv_triv.
      - (* [comment removed for export] *) rewrite STATE, STx. reflexivity.
      - (* [comment removed for export] *) clear - VERP. lia.
      - (* [comment removed for export] *) clear - PLT. lia.
      - exact (conj DELIM1 DELIM2).
      - intros X1 _. apply ATTRST; [exact X1| right; rewrite EVA; discriminate].
      - (* [comment removed for export] *)
        clear - OUT LEN1 EVA. unfold oacost, oicost in *. rewrite EVA in OUT. cbn [x_va x_vi x_st x_p x_vv x_v] in *. lia.
      - (* [comment removed for export] *)
        split; [exact ANZ|]. split; [exact VSO1|]. split; [clear - SZ1 LEN1 AROOM; lia|].
        intros z Hz. split; [exact (proj1 (AAP z Hz))|].
        cbn in Hz. destruct Hz as [<-|[<-|[<-|[<-|[<-|[]]]]]]; apply not_eq_sym; [exact NB_V| exact NB_W| exact NB_D| exact NB_S| exact NB_B].
      - exists fj0, fj8. exact FR1.
      - (* [comment removed for export] *) rewrite LB1, LB, EVA. unfold pw_bytes. clear. lia.
      - (* [comment removed for export] *) rewrite NL1, NL, EVA. reflexivity. }
    assert (HS : hstep E x (after_putc x y1) A A1 m m1).
    { eapply (hstep_call1 E x _ A A1 m m1 PUTC_STACK Vp (vb_buf y) (vb_size y1) (vb_buf y1));
        [ exact CF1
        | clear; unfold PUTC_STACK, EXT_STACK; unfold_stacks_g; lia
        | eapply parse_window_mapped; [exact PE| exact ST1| exact FR1]
        | intros a [X|X]; unfold pzone; right; right; right; left; rewrite EVA; [right; exact X| left; unfold blk; split; [exact ANZ| exact X]]
        | exact LIVE1 | exact REL
        | unfold pst_blocks; rewrite EVA; right; left; right; reflexivity
        | unfold pst_blocks, after_putc; cbn [x_vv x_va x_vi x_v]; rewrite EVA; intros p [Hp|[[Hp|Hp]|Hp]];
          [left; left; exact Hp| left; right; left; left; exact Hp| right; exact Hp| left; right; right; exact Hp]
        | unfold parse_new, after_putc, pzone; cbn [x_vv x_va x_vi x_v option_map]; rewrite EVA; intros a [Ha|[[Ha|Ha]|Ha]];
          [ right; right; right; left; exact Ha
          | right; right; right; right; left; left; exact Ha
          | left; exact Ha
          | right; right; right; right; right; left; destruct (x_vi x); [exact Ha| destruct Ha] ] ]. }
    unfold loop_ms in K.
    exact (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 m1 md1 y1 _ eq_refl PI1 AINV1 MDF HS LEN1 FR1).
  Qed.
End S.
End V_PPutc.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Pa4g6 V_PH51p.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5 Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PD648 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH4jn.V_PPutc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Pa4g6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH4jn.V_VS1zl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.

Module V_PHhx7.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_PMark V_PD648 V_Pa4g6 V_PH51p V_VSle5 Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PD648 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Pa4g6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_TagError : handler_stmt S_TagError.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    pose proof PI as PI0.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + 0) by (unfold phi, rank; rewrite ST; reflexivity).
    (* [comment removed for export] *)
    assert (CKPT : forall q, x_p x <= q -> q <= pe_e E ->
      pinv E (PST q S_TagError (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A m
      /\ hstep E x (PST q S_TagError (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A A m m).
    { intros q LQ QE. split.
      - apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
        + (* [comment removed for export] *) clear - VERP LQ. lia.
        + (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
      - eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| unfold pframe; exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
    (* [comment removed for export] *)
    assert (EXIT_E : forall (sv : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      realizes rsegs (mkCfg (loop_ms E 0x1a7d8 sv ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' m) md) T).
    { intros. unfold loop_ms. destruct (CKPT (pe_e E) ltac:(clear - PLT; lia) ltac:(clear; lia)) as [PIc HSc].
      apply rz_go; [exact MDH| exact MDL|].
      zstep. zstep. apply rz_stop.
      eapply (KL (PST (pe_e E) S_TagError (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A m md);
        [exact PIc| exact AINV| apply md_frame_refl; [exact MDL| exact MDH]| exact HSc|].
      cbn [x_p]. intros H. exfalso. clear - H. lia. }
    (* [comment removed for export] *)
    assert (FOUND : forall (q : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      x_p x <= q -> q < pe_e E ->
      realizes rsegs (mkCfg (loop_ms E 0x1a7e0 (q + 1) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' m) md) T).
    { intros until t6'. intros LQ QE. unfold loop_ms.
      destruct (CKPT (q + 1) ltac:(clear - LQ; lia) ltac:(clear - QE; lia)) as [PIc HSc].
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (mark_call HMC E (PST (q + 1) S_TagError (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A m md T (q + 1) (q + 1) 1 0x1a7f0);
        [ exact PE | exact PIc | exact AINV | cbn [x_p]; clear; lia | clear - QE; lia | right; reflexivity | clear; lia | reflexivity
        | cbn [x_st]; intros [X|X]; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (HS2 : hstep E x x1 A A1 m m2) by (eapply hstep_trans; [exact HSc| exact HS]).
      assert (ST1 : x_st x1 = S_TagError) by (rewrite EX1; reflexivity).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = q + 1) by (rewrite EX1; reflexivity).
      clear - HMC PE KL PHI PI1 AINV' MDF HS2 VK VERP1 LM1 OP1 ST1 EV1 EP1 LQ QE.
      pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
      pose proof PI1 as PIk.
      world_open PE PI1 AINV'. rewrite <- EP1.
      unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH'| exact MDL'|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      set (v3 := fupd (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fin_esi_tag 0) Fstate (st0 S_NxtTag)).
      (* [comment removed for export] *)
      assert (ATR : 0 <= x_v x1 Fattr_vsb < 2^64).
      { clear - VA AINV' CV. destruct (x_va x1) as [ya|].
        - destruct VA as (_ & AOBJ & _). pose proof (live_geom LayoutP0 _ _ _ _ _ AINV' (proj1 (proj2 (proj2 AOBJ)))) as (_ & _ & L1 & L2 & _). lia.
        - rewrite VA. lia. }
      zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *)
        apply rz_stop.
        eapply (KL (PST (x_p x1) S_NxtTag v3 (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ md1).
        2:{ eapply (ainv_stores E A1 m2 _ md1 _ _ PE0 AINV' MU WM WZ). }
        2:{ exact MDF. }
        2:{ eapply hstep_trans; [exact HS2|].
            eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                                 | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
            w_in_zone_tac. left. unfold blk. lia. }
        2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. rewrite EP1. clear - LQ. lia. }
        subst v3. apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
        intros X. exact (X K1). }
      (* [comment removed for export] *)
      assert (VNN : x_va x1 <> None).
      { clear - VA K1. destruct (x_va x1); [intros X; discriminate X| exfalso; exact (K1 VA)]. }
      zstep. zstep.
      apply rz_stop.
      eapply (destroy_attr_gen E x1 A1 m2 _ md1 T 0x1a814 [(pe_VEP E, pe_VEP E + 312)] v3 j0 j8);
        [ exact PE | exact PIk | exact AINV' | exact MU | exact WM | exact WZ
        | intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia
        | assumption | exact STK | exact FR
        | subst v3; unfold vep_cells; psimp; exact VEPC
        | subst v3; psimp; reflexivity | subst v3; psimp; reflexivity
        | exact VNN | clear; lia | reflexivity | ].
      intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x A2 m4 md2 AINV2 MI2 MDF2 ST2 FR2 VEPC2 IMG2 HENV2 DATA2 VSBO2 WAL2 LVEP2 VI2 LB2 NL2 HSd.
      pose proof (as_lazy_nil _ _ _ AINV2) as [MDL2 MDH2].
      lazymatch type of MU with munch _ _ ?m3 =>
        assert (HS3 : hstep E x1 (PST (x_p x1) S_NxtTag v3 (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 A1 m2 m3) end.
      { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
      unfold loop_ms. apply rz_go; [exact MDH2| exact MDL2|].
      (* [comment removed for export] *)
      zstep. apply rz_stop.
      eapply (KL (PST (x_p x1) S_NxtTag (fupd v3 Fattr_vsb 0) (x_tag x1) (x_q x1) (x_vv x1) None (x_vi x1)) A2 m4 md2).
      2:{ exact AINV2. }
      2:{ eapply md_frame_trans; [exact MDF| exact MDF2]. }
      2:{ eapply hstep_trans; [exact HS2|]. eapply hstep_trans; [exact HS3| exact (HSd (x_p x1) S_NxtTag)]. }
      2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. rewrite EP1. clear - LQ. lia. }
      subst v3. apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
      + (* [comment removed for export] *) clear - OUT OA0 OI0. unfold oacost, oicost in *. cbn [x_va x_vi x_st x_p x_vv x_v] in *. lia.
      + (* [comment removed for export] *) intros X. apply X. reflexivity. }
    (* [comment removed for export] *)
    assert (LOOP : forall (k : nat) (q : Z) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      q + Z.of_nat k = pe_e E -> x_p x <= q -> q < pe_e E ->
      evt rsegs (rz_at rsegs md T)
          (loop_ms E 0x1a6b4 (q + 1) ra' t0' t1' t2' (Z_to_bv 64 (pe_e E - q)) a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' m)).
    { induction k as [|k IH]; intros until t6'; intros Hk LQ QE.
      { exfalso. clear - Hk QE. lia. }
      unfold loop_ms.
      (* [comment removed for export] *)
      destruct (payload_read rsegs E m q DBY ltac:(clear - LQ VERP; lia) QE) as (b & Hnth & RDP).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      { apply rz_stop. eapply (FOUND q); [exact LQ| exact QE]. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      - replace (pe_e E - q + -1) with (pe_e E - (q + 1)) by (clear; lia). replace (q + 2) with (q + 1 + 1) by (clear; lia).
        eapply (IH (q + 1)); [clear - Hk; lia| clear - LQ; lia| clear - K2 Hk QE; lia].
      - (* [comment removed for export] *)
        zstep. apply rz_stop. apply EXIT_E. }
    (* [comment removed for export] *)
    apply rz_go; [exact MDH| exact MDL|].
    zstep. if_cases K0; zify_cond K0. { dead K0. } clear K0.
    zstep. zstep. zstep.
    eapply (LOOP (Z.to_nat (pe_e E - x_p x)) (x_p x)); [clear - PLT; rewrite Z2Nat.id by lia; lia| clear; lia| exact PLT].
  Qed.
End S.
End V_PHhx7.


Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac call_consts_in H ::= unfold ERRNO0 in H.
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
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@FRB; @TAG; @VEPB; @G2; @Ha; @PSP; @VEPlo; @CV; @VEPhi; @VERP; @LOP; @QE; @HVSC; @H; @LQ; @ABlo; @V6; @Dlo; @Dhi; @EE; @OUT; @ATlo; @Hk; @PLT; @V1; @V2; @Vlen; @EPn; @DR; @LB; @LB4; @NL; @NL4; @G3; @L1; @L2; @NN; @CEIL; @AVI; @LBS; @Ahi; @ABhi; @K2; @K9; @EVS; @VR; @K0; @K1; @EAT; @VIy; @ILEN])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Hypothesis HVE : vep_error_stmt.
  Hypothesis HDIA : vep_do_include_attr_stmt.

  Section X.
    Variables (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet).
    Hypothesis PE : penv_ok E.
    Hypothesis PHI : phi E x = 16 * (pe_e E - x_p x) + 1.
    Hypothesis KL : latch_K E x A m md T.

    Let JTE : word := Z_to_bv 64 (st0 S_TagError).

    (* [comment removed for export] *)
    #[using="KL PHI PE HVE"] Lemma av_gt : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model) (j8c : word)
        (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_AttrValue -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      rw_cells rsegs mc (pe_sp E) (pframe E JTE j8c) ->
      realizes rsegs (mkCfg (loop_ms E 0x1aaa8 (x_p xc) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc HSc STc LQ QE FRX.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms. clear FR. subst JTE. unfold pframe in FRX.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] mc) as MU.
      pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
      assert (EVS : VEPERR_STACK = 48) by reflexivity.
      assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
      assert (ATR : 0 <= x_v xc Fattr_vsb < 2^64).
      { clear - VA AINVc CV. destruct (x_va xc) as [ya|].
        - (first [ dand3 VA as _ AOBJ _ | destruct VA as (_ & AOBJ & _) ]). (first [ pose proof ((live_geom LayoutP0 _ _ _ _ _ AINVc (proj1 (proj2 (proj2 AOBJ))))) as dR_2; dand5 dR_2 as _ _ L1 L2 _ | pose proof (live_geom LayoutP0 _ _ _ _ _ AINVc (proj1 (proj2 (proj2 AOBJ)))) as (_ & _ & L1 & L2 & _) ]). lia.
        - rewrite VA. lia. }
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      hide STK. hide_slow.
      call_fr (HVE (pe_VEP E) (x_v xc) (x_tag xc) (x_q xc) (pe_H E) (pe_lo E)) by idtac.
      1:{ reflexivity. }
      1:{ unfold vep_cells. rewrite STATE. exact VEPC. }
      1:{ exact TAG. }
      1:{ exact PADS. }
      1:{ exact (proj1 BASE). }
      1:{ exact HENV. }
      1:{ exact (proj1 PE0). }
      1:{ exact IMG. }
      1:{ exact VEPlo. }
      1:{ apply mod8_of_mod16. exact VEP16. }
      1:{ clear - VEPhi. lia. }
      1:{ unhide STK. rewrite unsigned_lit by exact SPR. exact STK. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite EVS, PSP. clear - LOP. lia. }
      1:{ exact CEIL. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite PSP. clear. lia. }
      1:{ exact MI. }
      clear STK. unhide_slow.
      try match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      rename PC into HENV1. rename POST into STK.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        pose proof (ainv_stores E Ac mc m1 mdc _ _ PE0 AINVc MU WM WZ) as AINV1;
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m1) as MU2; pose proof (wmono_refl rsegs m1) as WM2 end.
      assert (WZ2 : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                            [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
          by (eapply (henv_stores E Ac _ _ mdc _ _ PE0 AINV1 MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV1])
      end.
      set (xt := PST (x_p xc) S_TagError (fupd (fupd (x_v xc) Fstate (st0 S_TagError)) Fattr_delim 0) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        pose proof (ainv_stores E Ac mc mf mdc _ _ PE0 AINVc MU WM WZ) as AINVt;
        assert (PIt : pinv E xt Ac mf); [| assert (HSt : hstep E x xt A Ac m mf)] end.
      { subst xt. apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ. }
      { eapply hstep_trans; [exact HSc|].
        eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FRX]
                             | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
        w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *)
        apply rz_stop.
        eapply (KL xt Ac _ mdc); [exact PIt| exact AINVt| exact MDFc| exact HSt|].
        subst xt. psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LQ. lia. }
      (* [comment removed for export] *)
      assert (EVAx : exists y, x_va xc = Some y) by (clear - VA K1; destruct (x_va xc) as [y0|]; [exists y0; reflexivity| exfalso; exact (K1 VA)]).
      destruct EVAx as [y EVA].
      rewrite EVA in VA. (first [ dand4 VA as ANZ AOBJc AROOM AAP | destruct VA as (ANZ & AOBJc & AROOM & AAP) ]).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        assert (AOBJ2 : vsb_obj LayoutP0 Ac mf (x_v xc Fattr_vsb) y false)
          by (eapply (vsb_obj_stores E Ac mc mf mdc _ _ PE0 AINVc MU WM WZ); [in_list| in_list| exact AOBJc]) end.
      unfold oabuf in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI. rewrite EVA in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI.
      (first [ pose proof ((vsb_obj_geom LayoutP0 Ac mc mdc _ _ _ AINVc AOBJc)) as dR_g9; dand11 dR_g9 as A16 Alo Ahi Aimg AB16 ABlo ABhi ABimg DSB _ _ | pose proof (vsb_obj_geom LayoutP0 Ac mc mdc _ _ _ AINVc AOBJc) as (A16 & Alo & Ahi & Aimg & AB16 & ABlo & ABhi & ABimg & DSB & _ & _) ]).
      (first [ pose proof (AOBJc) as dR_g10; dand6 dR_g10 as _ _ LAS LAB ASB _ | pose proof AOBJc as (_ & _ & LAS & LAB & ASB & _) ]).
      (first [ pose proof (AOBJ2) as dR_g11; dand6 dR_g11 as AVC AVI _ _ _ (bs & AU8 & LBS & _) | pose proof AOBJ2 as (AVC & AVI & _ & _ & _ & (bs & AU8 & LBS & _)) ]). cbn [al_segs LayoutP0] in AVC, AU8. clear AOBJ2.
      pose proof (as_live_disjoint Ac mc mdc _ _ _ _ AINVc LAS LVEP D_AV) as DXA.
      pose proof (as_live_disjoint Ac mc mdc _ _ _ _ AINVc LAB LVEP D_ABV) as DXB.
      (* [comment removed for export] *)
      lazymatch type of MU with munch _ mc ?mf =>
        assert (MU6 : munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                            (vb_buf y, vb_buf y + vb_size y); (0x420b4, 0x420b4 + 4); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] mc mf)
          by (eapply munch_weaken; [| exact MU]; clear; unfold sub_fp; cbn [outside]; intros; lia) end.
      assert (WZ6 : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Finclude_src; oibuf xc]
                     [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                      (vb_buf y, vb_buf y + vb_size y); (0x420b4, 0x420b4 + 4); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]).
      { assert (NAI : x_v xc Finclude_src <> x_v xc Fattr_vsb /\ x_v xc Finclude_src <> vb_buf y /\
                      oibuf xc <> x_v xc Fattr_vsb /\ oibuf xc <> vb_buf y).
        { clear - VI D_AI D_AA. unfold oibuf in *. destruct (x_vi xc) as [yi|].
          - exact (D_AI ltac:(discriminate) ltac:(discriminate)).
          - rewrite VI. (first [ pose proof ((D_AA ltac:(discriminate))) as dR_g12; dand3 dR_g12 as _ ATlo ABlo | destruct (D_AA ltac:(discriminate)) as (_ & ATlo & ABlo) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
        (first [ dand4 NAI as NIA NIB NBA NBB | destruct NAI as (NIA & NIB & NBA & NBB) ]). wzone_tac. }
      (* [comment removed for export] *)
      assert (WZf : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Finclude_src; oibuf xc]
                     [(pe_sp E - 48, pe_sp E); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40); (vb_buf y, vb_buf y + vb_size y); (0x420b4, 0x420b4 + 4)]).
      { revert WZ6. clear. cbn [wzone]. intros WZ. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; apply WZ. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        pose proof (munch_refl [(pe_sp E - 48, pe_sp E); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40); (vb_buf y, vb_buf y + vb_size y); (0x420b4, 0x420b4 + 4)] mf) as MUf;
        pose proof (wmono_refl rsegs mf) as WMf;
        pose proof (ainv_stores E Ac mc mf mdc _ _ PE0 AINVc MU6 WM WZ6) as AINVf end.
      clear MU MU2 WM2 WZ2 WZ AINV1 AINVt PIt HSt.
      unfold off_image in VEPimg, Dimg. cbn [al_image_lo al_image_hi LayoutP0] in VEPimg, Dimg.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => destruct (rw_errno_any mf) as [e0 ERR] end.
      (* [comment removed for export] *)
      zstep.
      hide DSB. hide Dimg. hide STK. hide_slow.
      try clear DBY. call_fr (VSB_finish_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x_v xc Fattr_vsb) y bs e0 (pe_lo E)) by idtac.
      1:{ reflexivity. }
      1:{ reflexivity. }
      1:{ exact AVC. }
      1:{ exact AVI. }
      1:{ exact AU8. }
      1:{ exact LBS. }
      1:{ exact ERR. }
      1:{ exact Alo. }
      1:{ exact Ahi. }
      1:{ exact ABhi. }
      1:{ exact Aimg. }
      1:{ exact ABimg. }
      1:{ unhide DSB. exact DSB. }
      1:{ unhide STK. rewrite unsigned_lit by exact SPR. exact STK. }
      1:{ rewrite unsigned_lit by exact SPR. revert LOP PSP. clear. intros; lia. }
      1:{ exact CEIL. }
      1:{ rewrite unsigned_lit by exact SPR. revert G3 PSP. clear. unfold HFRAME. intros; lia. }
      1:{ assumption. }
      clear STK. unhide_slow.
      unhide DSB. unhide Dimg.
      try match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      rename PC into AVC3. rename PC0 into AU83. rename PC1 into ERR3. rename POST into STK3.
      (* [comment removed for export] *)
      set (yf := vsb_set_flags y VSB_FLAGS_FIN).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
        assert (AOBJ3 : vsb_obj LayoutP0 Ac m3 (x_v xc Fattr_vsb) yf true) end.
      { subst yf. split; [exact AVC3|]. split; [| split; [exact LAS|]; split; [exact LAB|]; split; [exact ASB|]].
        - clear - AVI. unfold vsb_inv in *. cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf vsb_set_flags].
          (first [ dand6 AVI as V1 V2 V3 V4 V5 V6 | destruct AVI as (V1 & V2 & V3 & V4 & V5 & V6) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; try lia.
        - exists (upd bs (Z.to_nat (vb_len y)) (Z_to_bv 8 0)). cbn [vb_buf vb_size vb_len vsb_set_flags].
          split; [exact AU83|]. split; [rewrite upd_length; exact LBS|].
          intros _. apply nth_error_upd_same. clear - AVI LBS. unfold vsb_inv in AVI. lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) => lazymatch type of MUf with munch _ ?mf _ =>
        assert (HENV3 : henv_ok LayoutP0 VI0 (pe_H E) m3)
          by (eapply (henv_stores E Ac mf m3 mdc _ _ PE0 AINVf MUf WMf WZf); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2 PSP Ahi ABhi; lia| exact HENV2])
      end end.
      (first [ pose proof (AVI) as dR_g15; dand8 dR_g15 as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | pose proof AVI as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
      (* [comment removed for export] *)
      rewrite Verr. change (vsb_result 0 0) with 0.
      zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. } clear K2.
      zstep. zstep.
      apply rz_stop.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?m5 _) _) _ =>
        assert (HS1 : hstep E xc (PST (x_p xc) S_TagError (fupd (fupd (x_v xc) Fstate (st0 S_TagError)) Fattr_delim 0)
                                   (x_tag xc) (x_q xc) (x_vv xc) (Some y) (x_vi xc)) Ac Ac mc m5) end.
      { rewrite <- EVA.
        eapply hstep_stores; [exact MU6 | | eapply parse_window_mapped; [exact PE0| exact STK3| exact FRX]
                             | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
        w_in_zone_tac; [ left; unfold blk; lia
                       | right; right; right; left; rewrite EVA; left; unfold blk; split; [exact ANZ| exact Ha]
                       | right; right; right; left; rewrite EVA; right; unfold blk; split; [clear - ABlo; lia| exact Ha]
                       | do 5 right; exact Ha ]. }
      eapply (destroy_attr_fin E xc Ac mc _ mdc T 0x1a814 _
                (fupd (fupd (x_v xc) Fstate (st0 S_TagError)) Fattr_delim 0) y yf true (Z_to_bv 64 (st0 S_TagError)) j8c);
        [ exact PE| exact PIc0| exact AINVc| exact MU6| exact WM| exact WZ6| assumption| exact STK3| exact FRX
        | exact HENV3| unfold vep_cells; psimp; exact VEPC| psimp; reflexivity| psimp; reflexivity| exact EVA| exact AOBJ3
        | subst yf; reflexivity| subst yf; reflexivity| clear; lia| reflexivity| ].
      intros t0y t1y t2y a0y a1y a2y a3y a4y a5y a6y a7y t3y t4y t5y t6y A5 m6 md5 AINV5 MI5 MDF5 ST5 FR5 VEPC5 IMG5 HENV5 DATA5 VSBO5 WAL5 LVEP5 VI5 LB5 NL5 HS5.
      rewrite EVA in HS5.
      pose proof (as_lazy_nil _ _ _ AINV5) as [MDL5 MDH5].
      unfold loop_ms. apply rz_go; [exact MDH5| exact MDL5|].
      (* [comment removed for export] *)
      zstep. apply rz_stop.
      eapply (KL (PST (x_p xc) S_TagError
                      (fupd (fupd (fupd (x_v xc) Fstate (st0 S_TagError)) Fattr_delim 0) Fattr_vsb 0)
                      (x_tag xc) (x_q xc) (x_vv xc) None (x_vi xc)) A5 m6 md5).
      2:{ exact AINV5. }
      2:{ eapply md_frame_trans; [exact MDFc| exact MDF5]. }
      2:{ eapply hstep_trans; [exact HSc|]. eapply hstep_trans; [exact HS1| exact (HS5 _ _)]. }
      2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LQ. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINVc MU6 WM WZ6.
      - (* [comment removed for export] *) clear - OUT EVA Vlen. unfold oacost, oicost in *. rewrite EVA in OUT. cbn [x_va x_vi x_st x_p x_vv x_v] in *. lia.
    Qed.

    (* [comment removed for export] *)
    Definition av_finish_T : Prop :=
      forall (xc : pst) (Ac : AS) (mc m2 : mem) (mdc : Model) (y : vsb_rec) (j8c : word)
             (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_AttrValue -> x_p x <= x_p xc -> x_p xc < pe_e E -> x_va xc = Some y ->
      munch [(pe_VEP E, pe_VEP E + 312)] mc m2 -> wmono rsegs mc m2 -> mem_inv rsegs m2 ->
      stk rsegs m2 (pe_lo E) (pe_sp E) -> rw_cells rsegs m2 (pe_sp E) (pframe E JTE j8c) ->
      rw_cells rsegs m2 (pe_VEP E) (vep_cells (fupd (fupd (x_v xc) Fstate (st0 S_InTag)) Fattr_delim 0) (x_tag xc) (x_q xc)) ->
      realizes rsegs (mkCfg (loop_ms E 0x1aa84 (x_p xc + 1) ra t0 t1 t2 (Z_to_bv 64 (x_v xc Fattr_vsb)) a1 a2 a3 a4 a5 a6 a7
                               (Z_to_bv 64 (st0 S_InTag)) t3 t4 t5 t6 m2) mdc) T.

    (* [comment removed for export] *)
    #[using="KL PHI PE"] Lemma av_delim (AVF : av_finish_T) : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model) (j8c : word)
        (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_AttrValue -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      rw_cells rsegs mc (pe_sp E) (pframe E JTE j8c) ->
      realizes rsegs (mkCfg (loop_ms E 0x1aa70 (x_p xc) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (st0 S_InTag)) t3 t4 t5 t6 mc) mdc) T.
    Proof.
      intros until t6. intros PIc AINVc MDFc HSc STc LQ QE FRX.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms. clear FR. unfold pframe in FRX.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU. pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (ATR : 0 <= x_v xc Fattr_vsb < 2^64).
      { clear - VA AINVc CV. destruct (x_va xc) as [ya|].
        - (first [ dand3 VA as _ AOBJ _ | destruct VA as (_ & AOBJ & _) ]). (first [ pose proof ((live_geom LayoutP0 _ _ _ _ _ AINVc (proj1 (proj2 (proj2 AOBJ))))) as dR_4; dand5 dR_4 as _ _ L1 L2 _ | pose proof (live_geom LayoutP0 _ _ _ _ _ AINVc (proj1 (proj2 (proj2 AOBJ)))) as (_ & _ & L1 & L2 & _) ]). lia.
        - rewrite VA. lia. }
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *)
        apply rz_stop.
        match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
          assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
            by (eapply (henv_stores E Ac _ _ mdc _ _ PE0 AINVc MU WM WZ); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV])
        end.
        eapply (KL (PST (x_p xc + 1) S_InTag (fupd (fupd (x_v xc) Fstate (st0 S_InTag)) Fattr_delim 0) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)) Ac _ mdc).
        2:{ eapply (ainv_stores E Ac mc _ mdc _ _ PE0 AINVc MU WM WZ). }
        2:{ exact MDFc. }
        2:{ eapply hstep_trans; [exact HSc|].
            eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FRX]
                                 | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
            w_in_zone_tac. left. unfold blk. lia. }
        2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LQ. lia. }
        apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ.
        - (* [comment removed for export] *) clear - VERP. lia.
        - (* [comment removed for export] *) clear - QE. lia.
        - (* [comment removed for export] *) intros X. exact (X K1). }
      (* [comment removed for export] *)
      apply rz_stop.
      destruct (x_va xc) as [y|] eqn:EVA; [| exfalso; exact (K1 VA)].
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        eapply (AVF xc Ac mc mf mdc y j8c) end;
        [ exact PIc0| exact AINVc| exact MDFc| exact HSc| exact STc| exact LQ| exact QE| exact EVA
        | exact MU| exact WM| exact MI| exact STK| unfold pframe; exact FRX
        | unfold vep_cells; psimp; exact VEPC ].
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HVE"] Lemma av_loop (AVF : av_finish_T) : forall (k : nat) (xc : pst) (Ac : AS) (mc : mem) (mdc : Model) (j8c : word)
        (ra t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_AttrValue -> x_p x <= x_p xc -> x_p xc + Z.of_nat k = pe_e E -> x_p xc < pe_e E ->
      rw_cells rsegs mc (pe_sp E) (pframe E JTE j8c) ->
      evt rsegs (rz_at rsegs mdc T)
          (loop_ms E 0x1a8d0 (x_p xc) ra t0 t1 t2 a0 a1 a2 (Z_to_bv 64 (pe_e E - x_p xc)) a4 a5 a6 a7 (Z_to_bv 64 (st0 S_InTag)) t3 t4 t5 t6 mc).
    Proof.
      induction k as [|k IH]; intros until t6; intros PIc AINVc MDFc HSc STc LQ Hk QE FRX.
      { exfalso. clear - Hk QE. lia. }
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms. clear FR. unfold pframe in FRX.
      pose proof (munch_refl [(pe_sp E, pe_sp E + 16)] mc) as MU. pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_sp E, pe_sp E + 16)]) by wzone_tac.
      assert (DR : 0 <= x_v xc Fattr_delim < 2^31) by (destruct (DELIM2 eq_refl) as [D|[D|D]]; rewrite D; clear; lia).
      assert (ATR : 0 <= x_v xc Fattr_vsb < 2^64).
      { clear - VA AINVc CV. destruct (x_va xc) as [ya|].
        - (first [ dand3 VA as _ AOBJ _ | destruct VA as (_ & AOBJ & _) ]). (first [ pose proof ((live_geom LayoutP0 _ _ _ _ _ AINVc (proj1 (proj2 (proj2 AOBJ))))) as dR_6; dand5 dR_6 as _ _ L1 L2 _ | pose proof (live_geom LayoutP0 _ _ _ _ _ AINVc (proj1 (proj2 (proj2 AOBJ)))) as (_ & _ & L1 & L2 & _) ]). lia.
        - rewrite VA. lia. }
      (* [comment removed for export] *)
      assert (TAIL : forall (xn : pst) (An : AS) (mn : mem) (mdn : Model) (j8n : word)
          (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        pinv E xn An mn -> ainv An mn mdn -> md_frame md mdn -> hstep E x xn A An m mn ->
        x_st xn = S_AttrValue -> x_p xn = x_p xc + 1 ->
        rw_cells rsegs mn (pe_sp E) (pframe E JTE j8n) ->
        realizes rsegs (mkCfg (loop_ms E 0x1a914 (x_p xc) ra' t0' t1' t2' a0' a1' a2' (Z_to_bv 64 (pe_e E - x_p xc)) a4' a5' a6' a7'
                                 (Z_to_bv 64 (st0 S_InTag)) t3' t4' t5' t6' mn) mdn) T).
      { intros until t6'. intros PIn AINVn MDFn HSn STn EPn FRn.
        pose proof (as_lazy_nil _ _ _ AINVn) as [MDLn MDHn].
        clear - IH PE PHI KL PIn AINVn MDFn HSn STn EPn FRn MDLn MDHn LQ Hk QE EE Dhi Dlo CV VERP.
        unfold loop_ms. apply rz_go; [exact MDHn| exact MDLn|].
        zstep. zstep. zstep. if_cases K9; zify_cond K9.
        all: try rewrite Z.mod_small in K9 by (clear - QE EE Dhi Dlo CV VERP; unfold pe_e, pe_N in *; lia).
        - (* [comment removed for export] *)
          replace (pe_e E - x_p xc + -1) with (pe_e E - x_p xn) by (clear - EPn; lia). rewrite <- EPn.
          eapply (IH xn An mn mdn j8n); [exact PIn| exact AINVn| exact MDFn| exact HSn| exact STn
            | clear - LQ EPn; lia| clear - Hk EPn; lia| clear - K9 Hk QE EPn; lia| exact FRn].
        - (* [comment removed for export] *)
          zstep. apply rz_stop. rewrite <- EPn.
          eapply (KL xn An mn mdn); [exact PIn| exact AINVn| exact MDFn| exact HSn|].
          rewrite EPn. intros H. exfalso. clear - H K9 Hk QE. lia. }
      (* [comment removed for export] *)
      assert (COLLECT : forall (a0v a2v : word) (b : byte),
        nth_error (pe_inp E) (Z.to_nat (x_p xc - pe_DATA E)) = Some b ->
        evt rsegs (rz_at rsegs mdc T)
            (loop_ms E 0x1a8fc (x_p xc) ra t0 t1 t2 a0v (Z_to_bv 64 (bv_unsigned b)) a2v (Z_to_bv 64 (pe_e E - x_p xc)) a4 a5 a6 a7
                     (Z_to_bv 64 (st0 S_InTag)) t3 t4 t5 t6 mc)).
      { intros a0v a2v b Hnth. unfold loop_ms.
        zstep. zstep. zstep. if_cases K5; zify_cond K5.
        { (* [comment removed for export] *)
          apply rz_stop.
          set (xn := PST (x_p xc + 1) S_AttrValue (x_v xc) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
          assert (PIn : pinv E xn Ac mc); [| assert (HSn : hstep E x xn A Ac m mc)].
          { subst xn. apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ.
            - (* [comment removed for export] *) clear - VERP. lia.
            - (* [comment removed for export] *) clear - QE. lia.
            - exact (conj DELIM1 DELIM2). }
          { eapply hstep_trans; [exact HSc|].
            eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FRX]
                                 | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
            w_in_zone_tac. }
          eapply (TAIL xn Ac mc mdc j8c); [exact PIn| exact AINVc| exact MDFc| exact HSn| reflexivity| reflexivity| unfold pframe; exact FRX]. }
        (* [comment removed for export] *)
        assert (EVA : exists y, x_va xc = Some y).
        { clear - VA K5. destruct (x_va xc) as [y|]; [exists y; reflexivity| exfalso; exact (K5 VA)]. }
        destruct EVA as [y EVA].
        zstep. zstep.
        apply rz_stop.
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
          pose proof (ainv_stores E Ac mc mf mdc _ _ PE0 AINVc MU WM WZ) as AINVp;
          assert (PIp : pinv E xc Ac mf); [| assert (HSp : hstep E x xc A Ac m mf)] end.
        { apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ. all: rewrite ?STc; try assumption. exact (conj DELIM1 DELIM2). }
        { eapply hstep_trans; [exact HSc|].
          eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FRX]
                               | intros p0 X; exact X
                               | intros a X; unfold pzone; unfold parse_new in X; cbn [option_map] in X;
                                 destruct X as [X|[X|X]]; [right; right; left; exact X| right; right; right; left; destruct (x_va xc); [exact X| destruct X]
                                                        | right; right; right; right; left; destruct (x_vi xc); [exact X| destruct X]] ].
          w_in_zone_tac. }
        eapply (putc_call E xc Ac _ mdc T 0x1a910 y JTE (Z_to_bv 64 (pe_e E - x_p xc)));
          [exact PE| exact PIp| exact AINVp| exact EVA| exact STc| exact QE| clear; lia| reflexivity| exact FRX|].
        intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1 y1 x1 EX1 PI1 AINV1 MDF1 HS1 LEN1 FR1. subst x1.
        pose proof (as_lazy_nil _ _ _ AINV1) as [MDL1 MDH1].
        unfold loop_ms. apply rz_go; [exact MDH1| exact MDL1|].
        unfold pframe in FR1.
        (* [comment removed for export] *)
        zstep. apply rz_stop.
        eapply (TAIL (after_putc xc y1) A1 m1 md1); [exact PI1| exact AINV1| eapply md_frame_trans; [exact MDFc| exact MDF1]
          | eapply hstep_trans; [exact HSp| exact HS1]| exact STc| reflexivity| unfold pframe; exact FR1]. }
      (* [comment removed for export] *)
      (first [ pose proof ((look_read rsegs E xc mc DBY ltac:(clear - VERP; lia) QE)) as dR_7; dex1 dR_7 as b; dand3 dR_7 as Hnth Hlook RDP | pose proof ((look_read rsegs E xc mc DBY ltac:(clear - VERP; lia) QE)) as dR_7; dand4 dR_7 as b Hnth Hlook RDP | destruct (look_read rsegs E xc mc DBY ltac:(clear - VERP; lia) QE) as (b & Hnth & Hlook & RDP) ]).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      (* [comment removed for export] *)
      zstep. clear RDP. cbv beta.
      zstep. if_cases K1; zify_cond K1.
      { apply rz_stop. eapply (av_gt xc Ac mc mdc j8c); [exact PIc0| exact AINVc| exact MDFc| exact HSc| exact STc| exact LQ| exact QE| unfold pframe; exact FRX]. }
      (* [comment removed for export] *)
      zstep. rewrite (sx32_small _ DR).
      zstep. if_cases K2; zify_cond K2.
      { apply rz_stop. eapply (av_delim AVF xc Ac mc mdc j8c); [exact PIc0| exact AINVc| exact MDFc| exact HSc| exact STc| exact LQ| exact QE| unfold pframe; exact FRX]. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases K3; zify_cond K3.
      { (* [comment removed for export] *) apply COLLECT. exact Hnth. }
      (* [comment removed for export] *)
      zstep. zstep.
      replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
      pose proof (vct_read0 mc (bv_unsigned b) _ MI BR eq_refl) as RDV. unfold wa in RDV.
      zstep. clear RDV. cbv beta. rewrite zx16_vct.
      pose proof (vct_range (bv_unsigned b)) as VR.
      zstep. zstep. if_cases K4; zify_cond K4.
      { apply rz_stop. eapply (av_delim AVF xc Ac mc mdc j8c); [exact PIc0| exact AINVc| exact MDFc| exact HSc| exact STc| exact LQ| exact QE| unfold pframe; exact FRX]. }
      apply COLLECT. exact Hnth.
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HVE"] Lemma av_body (AVF : av_finish_T) : forall (ra t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      pinv E x A m -> ainv A m md -> x_st x = S_AttrValue -> x_p x < pe_e E ->
      realizes rsegs (mkCfg (loop_ms E 0x1a8c4 (x_p x) ra t0 t1 t2 (Z_to_bv 64 (st0 S_AttrValue)) (Z_to_bv 64 (st0 S_AttrValue)) JTE
                               a3 a4 a5 a6 a7 (Z_to_bv 64 (st0 S_InTag)) t3 t4 t5 t6 m) md) T.
    Proof.
      intros until t6. intros PI AINV ST PLT.
      pose proof (as_lazy_nil _ _ _ AINV) as [MDL MDH]. world_open PE PI AINV. unfold loop_ms.
      pose proof (munch_refl [(pe_sp E, pe_sp E + 16)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                           [(pe_sp E, pe_sp E + 16)]) by wzone_tac.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0 PLT. unfold pe_e, pe_N in *. lia. } clear K0.
      zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        pose proof (ainv_stores E A m mf md _ _ PE0 AINV MU WM WZ) as AINV0;
        assert (PIx : pinv E x A mf); [| assert (HSx : hstep E x x A A m mf)] end.
      { apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ. all: rewrite ?ST; try assumption. exact (conj DELIM1 DELIM2). }
      { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; exact X
                             | intros a X; unfold pzone; unfold parse_new in X; cbn [option_map] in X;
                               destruct X as [X|[X|X]]; [right; right; left; exact X| right; right; right; left; destruct (x_va x); [exact X| destruct X]
                                                      | right; right; right; right; left; destruct (x_vi x); [exact X| destruct X]] ].
        w_in_zone_tac. }
      eapply (av_loop AVF (Z.to_nat (pe_e E - x_p x)) x A _ md j8);
        [exact PIx| exact AINV0| apply md_frame_refl; [exact MDL| exact MDH]| exact HSx| exact ST| clear; lia
        | clear - PLT; rewrite Z2Nat.id by lia; lia| exact PLT| unfold pframe; exact FR].
    Qed.

    (* [comment removed for export] *)
    #[using="KL PHI PE HDIA HVE"] Lemma av_finish : av_finish_T.
    Proof.
      intros xc Ac mc m2 mdc y j8c. intros until t6. intros PIc AINVc MDFc HSc STc LQ QE EVA MU12 WM12 MI2 STK2 FRX VEPC2.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDL MDH].
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. clear FR VEPC STK MI. unfold pframe in FRX.
      (* [comment removed for export] *)
      assert (WZ12 : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                             [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      rewrite EVA in VA. (first [ dand4 VA as ANZ AOBJc AROOM AAP | destruct VA as (ANZ & AOBJc & AROOM & AAP) ]).
      assert (AOBJ2 : vsb_obj LayoutP0 Ac m2 (x_v xc Fattr_vsb) y false)
        by (eapply (vsb_obj_stores E Ac mc m2 mdc _ _ PE0 AINVc MU12 WM12 WZ12); [in_list| in_list| exact AOBJc]).
      clear WZ12 DBY.
      unfold oabuf in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI. rewrite EVA in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI.
      (first [ pose proof ((vsb_obj_geom LayoutP0 Ac mc mdc _ _ _ AINVc AOBJc)) as dR_9; dand11 dR_9 as A16 Alo Ahi Aimg AB16 ABlo ABhi ABimg DSB _ _ | pose proof (vsb_obj_geom LayoutP0 Ac mc mdc _ _ _ AINVc AOBJc) as (A16 & Alo & Ahi & Aimg & AB16 & ABlo & ABhi & ABimg & DSB & _ & _) ]).
      (first [ pose proof (AOBJc) as dR_10; dand6 dR_10 as _ _ LAS LAB ASB _ | pose proof AOBJc as (_ & _ & LAS & LAB & ASB & _) ]).
      (first [ pose proof (AOBJ2) as dR_11; dand6 dR_11 as AVC AVI _ _ _ (bs & AU8 & LBS & _) | pose proof AOBJ2 as (AVC & AVI & _ & _ & _ & (bs & AU8 & LBS & _)) ]). cbn [al_segs LayoutP0] in AVC, AU8. clear AOBJ2.
      pose proof (as_live_disjoint Ac mc mdc _ _ _ _ AINVc LAS LVEP D_AV) as DXA.
      pose proof (as_live_disjoint Ac mc mdc _ _ _ _ AINVc LAB LVEP D_ABV) as DXB.
      pose proof (as_live_disjoint Ac mc mdc _ _ _ _ AINVc LAS LDATA D_AD) as DXAD.
      pose proof (as_live_disjoint Ac mc mdc _ _ _ _ AINVc LAB LDATA D_ABD) as DXBD.
      unfold vep_cells in VEPC2. psimp_in VEPC2.
      assert (SPR : 0 <= pe_sp E < 2^64) by (clear - FRB; lia).
      (* [comment removed for export] *)
      assert (MU : munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                          (vb_buf y, vb_buf y + vb_size y); (0x420b4, 0x420b4 + 4); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] mc m2)
        by (eapply munch_weaken; [| exact MU12]; clear; unfold sub_fp; cbn [outside]; intros; lia).
      assert (MUa : munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                          (vb_buf y, vb_buf y + vb_size y); (0x420b4, 0x420b4 + 4)] mc m2)
        by (eapply munch_weaken; [| exact MU12]; clear; unfold sub_fp; cbn [outside]; intros; lia).
      pose proof WM12 as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Finclude_src; oibuf xc]
                     [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                      (vb_buf y, vb_buf y + vb_size y); (0x420b4, 0x420b4 + 4); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]).
      { assert (NAI : x_v xc Finclude_src <> x_v xc Fattr_vsb /\ x_v xc Finclude_src <> vb_buf y /\
                      oibuf xc <> x_v xc Fattr_vsb /\ oibuf xc <> vb_buf y).
        { clear - VI D_AI D_AA. unfold oibuf in *. destruct (x_vi xc) as [yi|].
          - exact (D_AI ltac:(discriminate) ltac:(discriminate)).
          - rewrite VI. (first [ pose proof ((D_AA ltac:(discriminate))) as dR_12; dand3 dR_12 as _ ATlo ABlo | destruct (D_AA ltac:(discriminate)) as (_ & ATlo & ABlo) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
        (first [ dand4 NAI as NIA NIB NBA NBB | destruct NAI as (NIA & NIB & NBA & NBB) ]). wzone_tac. }
      assert (WZa : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Finclude_src; oibuf xc]
                     [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (x_v xc Fattr_vsb, x_v xc Fattr_vsb + 40);
                      (vb_buf y, vb_buf y + vb_size y); (0x420b4, 0x420b4 + 4)]).
      { revert WZ. clear. cbn [wzone]. intros WZ. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; apply WZ. }
      clear MU12 WM12.
      unfold off_image in VEPimg, Dimg. cbn [al_image_lo al_image_hi LayoutP0] in VEPimg, Dimg.
      destruct (rw_errno_any m2) as [e0 ERR].
      unfold loop_ms. apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep.
      (* [comment removed for export] *)
      hide DXAD. hide DXBD. hide DSB. hide Dimg.
      hide STK2. hide_slow.
      call_fr (VSB_finish_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x_v xc Fattr_vsb) y bs e0 (pe_lo E)) by idtac.
      1:{ reflexivity. }
      1:{ reflexivity. }
      1:{ exact AVC. }
      1:{ exact AVI. }
      1:{ exact AU8. }
      1:{ exact LBS. }
      1:{ exact ERR. }
      1:{ exact Alo. }
      1:{ exact Ahi. }
      1:{ exact ABhi. }
      1:{ exact Aimg. }
      1:{ exact ABimg. }
      1:{ unhide DSB. exact DSB. }
      1:{ unhide STK2. rewrite unsigned_lit by exact SPR. exact STK2. }
      1:{ rewrite unsigned_lit by exact SPR. revert LOP PSP. clear. intros; lia. }
      1:{ exact CEIL. }
      1:{ rewrite unsigned_lit by exact SPR. revert G3 PSP. clear. unfold HFRAME. intros; lia. }
      1:{ exact MI2. }
      clear STK2. unhide_slow.
      unhide DXAD. unhide DXBD. unhide DSB. unhide Dimg.
      try match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      rename PC into AVC3. rename PC0 into AU83. rename PC1 into ERR3. rename POST into STK3.
      (* [comment removed for export] *)
      set (yf := vsb_set_flags y VSB_FLAGS_FIN).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
        assert (AOBJ3 : vsb_obj LayoutP0 Ac m3 (x_v xc Fattr_vsb) yf true) end.
      { subst yf. split; [exact AVC3|]. split; [| split; [exact LAS|]; split; [exact LAB|]; split; [exact ASB|]].
        - clear - AVI. unfold vsb_inv in *. cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf vsb_set_flags]. 
          (first [ dand6 AVI as V1 V2 V3 V4 V5 V6 | destruct AVI as (V1 & V2 & V3 & V4 & V5 & V6) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; try lia. 
        - exists (upd bs (Z.to_nat (vb_len y)) (Z_to_bv 8 0)). cbn [vb_buf vb_size vb_len vsb_set_flags].
          split; [exact AU83|]. split; [rewrite upd_length; exact LBS|].
          intros _. apply nth_error_upd_same. clear - AVI LBS. unfold vsb_inv in AVI. lia. }
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
        pose proof (ainv_stores E Ac mc m3 mdc _ _ PE0 AINVc MU WM WZ) as AINV3;
        assert (HENV3 : henv_ok LayoutP0 VI0 (pe_H E) m3)
          by (eapply (henv_stores E Ac mc m3 mdc _ _ PE0 AINVc MUa WM WZa); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2 PSP Ahi ABhi; lia| exact HENV]);
        assert (IMG3 : img_ok0 m3) by (eapply (img_stores E Ac mc m3 mdc _ _ PE0 AINVc MU WZ); exact IMG)
      end.
      (first [ pose proof (AVI) as dR_15; dand8 dR_15 as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | pose proof AVI as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
      pose proof Verr as E0.
      (* [comment removed for export] *)
      rewrite E0. change (vsb_result 0 0) with 0.
      zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1. lia. } clear K1.
      destruct (ATTRST I ltac:(right; first [discriminate | rewrite EVA; discriminate])) as [EAT MH].
      assert (DI : x_v xc Fdostuff = vi_do_include VI0).
      { clear - ATTR EAT. destruct ATTR as [A0|(A1 & A2 & A3)]; [| exact A2]. exfalso. rewrite A0 in EAT. unfold TBL_attr_include in EAT. lia. }
      assert (NAI : x_v xc Finclude_src <> x_v xc Fattr_vsb /\ x_v xc Finclude_src <> vb_buf y /\
                    oibuf xc <> x_v xc Fattr_vsb /\ oibuf xc <> vb_buf y).
      { clear - VI D_AI D_AA. unfold oibuf in *. destruct (x_vi xc) as [yi|].
        - exact (D_AI ltac:(discriminate) ltac:(discriminate)).
        - rewrite VI. (first [ pose proof ((D_AA ltac:(discriminate))) as dR_16; dand3 dR_16 as _ ATlo ABlo | destruct (D_AA ltac:(discriminate)) as (_ & ATlo & ABlo) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
      (first [ dand4 NAI as NIA NIB NBA NBB | destruct NAI as (NIA & NIB & NBA & NBB) ]).
      (* [comment removed for export] *)
      zstep. rewrite DI. cbn [vi_do_include VI0].
      zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2. lia. } clear K2.
      zstep. zstep. zstep.
      apply rz_stop.
      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?m3 _) _) _ =>
        assert (VI3 : vi_world E xc Ac m3) by (unfold vi_world; world_stores VI PE0 AINVc MUa WM WZa);
        assert (VSBO3 : vsb_obj LayoutP0 Ac m3 (pe_S E) (x_vv xc) false)
          by (eapply (vsb_obj_stores E Ac mc m3 mdc _ _ PE0 AINVc MU WM WZ); [in_list| in_list| exact VSBO]);
        assert (DATA3 : data_obj LayoutP0 Ac m3 (pe_DATA E) (pe_inp E))
          by (eapply (data_obj_stores E Ac mc m3 mdc _ _ PE0 AINVc MU WZ); [in_list| exact DATA])
      end.
      unfold vi_world in VI3. unfold oibuf in NBA, NBB, D_IBV, D_IBS, D_IBB, D_IBD, D_IBW.
      eapply (HDIA (pe_VEP E) (fupd (fupd (x_v xc) Fstate (st0 S_InTag)) Fattr_delim 0) (x_tag xc) (x_q xc) yf (x_vi xc) (pe_H E) (pe_lo E)
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mdc Ac T).
      1:{ exact AINV3. }
      1:{ assumption. }
      1:{ reflexivity. }
      1:{ reflexivity. }
      1:{ split; [exact LVEP|]. split; [unfold vep_cells; psimp; exact VEPC2|]. split; [exact TAG| exact PADS]. }
      1:{ unfold vep_base. psimp. exact BASE. }
      1:{ exact HENV3. }
      1:{ exact HG. }
      1:{ exact IMG3. }
      1:{ psimp. unfold TBL_attr_include in MH. cbn [vi_tbl_attr_include VI0]. unfold TBL_attr_include. exact MH. }
      1:{ psimp. exact B_ic. }
      1:{ psimp. exact ANZ. }
      1:{ psimp. exact AOBJ3. }
      1:{ subst yf. cbn [vb_error vsb_set_flags]. exact E0. }
      1:{ psimp. exact D_AV. }
      1:{ subst yf. cbn [vb_buf vsb_set_flags]. exact D_ABV. }
      1:{ psimp. subst yf. cbn [vb_buf vsb_set_flags]. clear - VI3 D_IV D_IBV NIA NIB NBA NBB.
          destruct (x_vi xc) as [yi|]; [| exact VI3]. (first [ dand5 VI3 as Q1 Q2 Q3 Q4 Q5 | destruct VI3 as (Q1 & Q2 & Q3 & Q4 & Q5) ]).
          exact (conj Q1 (conj Q2 (conj Q3 (conj D_IV (conj D_IBV (conj NIA (conj NIB (conj NBA NBB)))))))). }
      1:{ reflexivity. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite PSP, Zminus_mod, G1. reflexivity. }
      1:{ rewrite unsigned_lit by (clear; lia). reflexivity. }
      1:{ rewrite unsigned_lit by exact SPR. exact STK3. }
      1:{ exact CEIL. }
      1:{ rewrite unsigned_lit by exact SPR. revert LOP PSP. clear. unfold_stacks_g. intros; lia. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite PSP. clear. lia. }
      intros t0z t1z t2z a0z a1z a2z a3z a4z a5z a6z a7z t3z t4z t5z t6z A4 m4 md4 v4 vi4 AINV4 MI4 MDF4 ST4 HENV4 VEPO4 OUT4 VI4 CF4.
      rewrite unsigned_lit in ST4, CF4 by exact SPR.
      replace (ret_pc (Z_to_bv 64 0x1aaa0)) with (Z_to_bv 64 0x1aaa0) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (as_lazy_nil _ _ _ AINV4) as [MDL4 MDH4].
      set (Vx := fun a : Z => blk (pe_VEP E) 312 a \/ vsb_blocks (x_v xc Fattr_vsb) yf a
                           \/ match x_vi xc with Some yi => vsb_blocks (x_v xc Finclude_src) yi a | None => False end
                           \/ (h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320)) in CF4.
      assert (CVx : vcover (pe_H E) Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E] Vx).
      { intros a [X|[X|[X|X]]].
        - eapply cover_blk; [exact LVEP| wz_not_in| exact X].
        - subst yf. unfold vsb_blocks in X. cbn [vb_buf vb_size vsb_set_flags] in X. destruct X as [X|X].
          + eapply cover_blk; [exact LAS| wz_not_in| exact X].
          + eapply cover_blk; [exact LAB| wz_not_in| exact X].
        - clear - X VI3 D_IS D_IB D_ID D_IBS D_IBB D_IBD. destruct (x_vi xc) as [yi|]; [| destruct X].
          (first [ dand3 VI3 as _ IO _ | destruct VI3 as (_ & IO & _) ]). (first [ pose proof (IO) as dR_20; dand5 dR_20 as _ _ LIS LIB _ | pose proof IO as (_ & _ & LIS & LIB & _) ]).
          destruct X as [X|X]; [eapply cover_blk; [exact LIS| wz_not_in| exact X] | eapply cover_blk; [exact LIB| wz_not_in| exact X]].
        - apply cover_vsc. exact X. }
      assert (WIN : alloc_ceiling <= pe_sp E - DOINCL_STACK) by (revert CEIL LOP PSP; clear; unfold_stacks_g; intros; lia).
      assert (WPOS : 0 <= DOINCL_STACK) by (clear; unfold_stacks_g; lia).
      assert (FR4 : rw_cells rsegs m4 (pe_sp E) (pframe E JTE j8c)).
      { eapply (pframe_call E Ac A4 _ m4 mdc (pe_sp E) DOINCL_STACK Vx _ [pe_S E; vb_buf (x_vv xc); pe_DATA E]);
          [exact PE| exact AINV3| exact CF4| exact WIN| exact WPOS| clear; lia| exact CVx| exact FRX]. }
      assert (IMG4 : img_ok0 m4).
      { eapply (img_call (pe_H E) Ac A4 _ m4 mdc (pe_sp E) DOINCL_STACK Vx _ [pe_S E; vb_buf (x_vv xc); pe_DATA E] AINV3 CF4 HG WIN); [exact CVx| exact IMG3]. }
      (first [ dand3 VEPO4 as LVEP4 VEPC4 _ | destruct VEPO4 as (LVEP4 & VEPC4 & _) ]). cbn [al_segs LayoutP0] in VEPC4.
      unfold pframe in FR4.
      (* [comment removed for export] *)
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m4) as MU5. pose proof (wmono_refl rsegs m4) as WM5.
      (* [comment removed for export] *)
      set (xk := PST (x_p xc + 1) S_InTag (fupd (fupd (x_v xc) Fstate (st0 S_InTag)) Fattr_delim 0) (x_tag xc) (x_q xc) (x_vv xc) (Some y) (x_vi xc)).
      lazymatch type of CF4 with cframe _ _ _ _ _ _ _ ?m3 _ => assert (HS1 : hstep E xc xk Ac Ac mc m3) end.
      { subst xk. rewrite <- EVA.
        eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK3| exact FRX]
                             | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
        w_in_zone_tac; [ left; unfold blk; lia
                       | right; right; right; left; rewrite EVA; left; unfold blk; split; [exact ANZ| exact Ha]
                       | right; right; right; left; rewrite EVA; right; unfold blk; split; [clear - ABlo; lia| exact Ha]
                       | do 5 right; exact Ha ]. }
      lazymatch type of CF4 with cframe _ _ _ _ _ _ _ ?m3 _ => rename m3 into mh end.
      destruct OUT4 as [(VIN & EV4 & EVI4 & LQA & LB4 & NL4)|[(VINN & EV4 & EVI4 & DA & DB & DI2 & LQA)|[(VIN & EV4 & EVI4 & DA & DB & LB4 & NL4 & LQA)|(ic & ICB & EV4 & EVI4 & DA & DB & LB4 & NL4 & LQA)]]].
      - (* [comment removed for export] *)
        subst v4 vi4. unfold vep_cells in VEPC4. psimp_in VEPC4. psimp_in VI4.
        assert (LVS4 : a_live A4 (pe_S E) = Some 40) by (rewrite LQA; exact LVS).
        assert (LVB4 : a_live A4 (vb_buf (x_vv xc)) = Some (vb_size (x_vv xc))) by (rewrite LQA; exact LVB).
        assert (LDATA4 : a_live A4 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))) by (rewrite LQA; exact LDATA).
        assert (WAL4 : a_live A4 (pe_wa E) = Some 40) by (rewrite LQA; exact WAL).
        assert (DATA4 : data_obj LayoutP0 A4 m4 (pe_DATA E) (pe_inp E)).
        { eapply (data_obj_call (pe_H E) Ac A4 mh m4 mdc (pe_sp E) DOINCL_STACK Vx _ [pe_S E; vb_buf (x_vv xc); pe_DATA E] AINV3 CF4 HG WIN);
            [exact CVx| in_list| exact LDATA4| exact DATA3]. }
        assert (VSBO4 : vsb_obj LayoutP0 A4 m4 (pe_S E) (x_vv xc) false).
        { eapply (vsb_obj_call (pe_H E) Ac A4 mh m4 mdc (pe_sp E) DOINCL_STACK Vx _ [pe_S E; vb_buf (x_vv xc); pe_DATA E] AINV3 CF4 HG WIN);
            [exact CVx| in_list| in_list| exact LVS4| exact LVB4| exact VSBO3]. }
        assert (WZ5 : wzone E A4 [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; vb_buf y] [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
        set (xo := PST (x_p xc + 1) S_InTag (fupd (fupd (fupd (fupd (x_v xc) Fstate (st0 S_InTag)) Fattr_delim 0) Finclude_src (x_v xc Fattr_vsb)) Fattr_vsb 0)
                       (x_tag xc) (x_q xc) (x_vv xc) None (Some yf)).
        assert (HScall : hstep E xk xo Ac A4 mh m4).
        { eapply (hstep_intro E xk xo Ac A4 mh m4 PARSE_STACK Vx nowhere).
          - eapply cframe_rebase; [exact CF4| clear; unfold_stacks_g; lia| eapply parse_window_mapped; [exact PE| exact ST4| unfold pframe; exact FR4]].
          - clear; lia.
          - eapply parse_window_mapped; [exact PE| exact ST4| unfold pframe; exact FR4].
          - subst xk. intros a [X|[X|[X|X]]]; unfold pzone; cbn [x_v x_va x_vi x_vv];
              [ left; exact X | right; right; right; left; exact X | right; right; right; right; left; exact X | do 5 right; exact X ].
          - subst xo xk. unfold parse_new, pzone. cbn [x_v x_vv x_va x_vi option_map fupd vf_beq vf_index N.eqb Pos.eqb].
            intros a [X|[X|X]]; [right; right; right; left; exact X| destruct X| right; right; right; right; left; exact X].
          - intros p k Hp _. rewrite LQA. exact Hp.
          - subst xo xk. unfold pst_blocks. cbn [x_v x_vv x_va x_vi fupd vf_beq vf_index N.eqb Pos.eqb].
            intros p [X|[X|X]]; [left; left; exact X| destruct X| left; right; left; exact X]. }
        (* [comment removed for export] *)
        apply rz_go; [exact MDH4| exact MDL4|].
        zstep. zstep.
        apply rz_stop.
        match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
          assert (HENV6 : henv_ok LayoutP0 VI0 (pe_H E) mf)
            by (eapply (henv_stores E A4 _ _ md4 _ _ PE0 AINV4 MU5 WM5 WZ5); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV4])
        end.
        eapply (KL (PST (x_p xc + 1) S_InTag
                        (fupd (fupd (fupd (fupd (fupd (x_v xc) Fstate (st0 S_InTag)) Fattr_delim 0) Finclude_src (x_v xc Fattr_vsb)) Fattr_vsb 0) Fattr_vsb 0)
                        (x_tag xc) (x_q xc) (x_vv xc) None (Some yf)) A4 _ md4).
        2:{ eapply (ainv_stores E A4 m4 _ md4 _ _ PE0 AINV4 MU5 WM5 WZ5). }
        2:{ eapply md_frame_trans; [exact MDFc| exact MDF4]. }
        2:{ eapply hstep_trans; [exact HSc|]. eapply hstep_trans; [exact HS1|]. eapply hstep_trans; [exact HScall|].
            eapply hstep_stores; [exact MU5 | | eapply parse_window_mapped; [exact PE0| exact ST4| exact FR4]
                                 | intros p0 X; refine (pst_blocks_same xo _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E xo _ a _ _ X); reflexivity ].
            subst xo. w_in_zone_tac. left. unfold blk. lia. }
        2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LQ. lia. }
        apply Build_pinv; psimp; pinv_close PE0 AINV4 MU5 WM5 WZ5.
        + (* [comment removed for export] *) clear - VERP. lia.
        + (* [comment removed for export] *) clear - QE. lia.
        + (* [comment removed for export] *) subst yf. clear - OUT EVA VIN Vlen. unfold oacost, oicost in *. rewrite EVA, VIN in OUT.
          cbn [x_va x_vi x_st x_p x_vv x_v vb_len vsb_set_flags] in *. lia.
        + (* [comment removed for export] *) intros X. apply X. reflexivity.
        + (* [comment removed for export] *)
          split; [exact ANZ|]. split; [| split; [exact (proj2 (proj2 VI4))| split; [subst yf; cbn [vb_size vb_len vsb_set_flags]; exact AROOM| split; [exact AAP| exact I]]]].
          eapply (vsb_obj_stores E A4 m4 _ md4 _ _ PE0 AINV4 MU5 WM5 WZ5); [in_list| subst yf; in_list| exact (proj1 (proj2 VI4))].
        + (* [comment removed for export] *) try subst yf; revert LB LB4; rewrite ?EVA, ?VIN; clear; unfold pw_bytes; cbn [vb_size vsb_set_flags]; intros; lia.
        + (* [comment removed for export] *) revert NL NL4; rewrite ?EVA, ?VIN; clear; unfold pw_nlive; intros; lia.
      - (* [comment removed for export] *)
        subst v4 vi4. destruct (x_vi xc) as [yi|] eqn:EVI; [| exfalso; exact (VINN eq_refl)].
        subst yf. cbn [vb_buf vsb_set_flags] in LQA, DB, CF4, Vx.
        unfold vep_cells in VEPC4. psimp_in VEPC4. cbn [vi_st VI0] in VEPC4.
        destruct DI2 as (DIx & DIBx & LB4 & NL4).
        (first [ dand5 VI as INZ IO IERR IAP IAP2 | destruct VI as (INZ & IO & IERR & IAP & IAP2) ]). (first [ pose proof (IO) as dR_23; dand5 dR_23 as _ _ LIS LIB _ | pose proof IO as (_ & _ & LIS & LIB & _) ]).
        assert (LK : forall p k, a_live Ac p = Some k -> p <> x_v xc Fattr_vsb -> p <> vb_buf y -> p <> x_v xc Finclude_src -> p <> vb_buf yi -> a_live A4 p = Some k)
          by (intros p k Hp N1 N2 N3 N4; rewrite (LQA p N1 N2 N3 N4); exact Hp).
        assert (LVS4 : a_live A4 (pe_S E) = Some 40) by (apply LK; [exact LVS| exact (not_eq_sym D_AS)| exact (not_eq_sym D_ABS)| exact (not_eq_sym D_IS)| exact (not_eq_sym D_IBS)]).
        assert (LVB4 : a_live A4 (vb_buf (x_vv xc)) = Some (vb_size (x_vv xc))) by (apply LK; [exact LVB| exact (not_eq_sym D_AB)| exact (not_eq_sym D_ABB)| exact (not_eq_sym D_IB)| exact (not_eq_sym D_IBB)]).
        assert (LDATA4 : a_live A4 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))) by (apply LK; [exact LDATA| exact (not_eq_sym D_AD)| exact (not_eq_sym D_ABD)| exact (not_eq_sym D_ID)| exact (not_eq_sym D_IBD)]).
        assert (WAL4 : a_live A4 (pe_wa E) = Some 40) by (apply LK; [exact WAL| exact (not_eq_sym D_AW)| exact (not_eq_sym D_ABW)| exact (not_eq_sym D_IW)| exact (not_eq_sym D_IBW)]).
        assert (DATA4 : data_obj LayoutP0 A4 m4 (pe_DATA E) (pe_inp E)).
        { eapply (data_obj_call (pe_H E) Ac A4 mh m4 mdc (pe_sp E) DOINCL_STACK Vx _ [pe_S E; vb_buf (x_vv xc); pe_DATA E] AINV3 CF4 HG WIN);
            [exact CVx| in_list| exact LDATA4| exact DATA3]. }
        assert (VSBO4 : vsb_obj LayoutP0 A4 m4 (pe_S E) (x_vv xc) false).
        { eapply (vsb_obj_call (pe_H E) Ac A4 mh m4 mdc (pe_sp E) DOINCL_STACK Vx _ [pe_S E; vb_buf (x_vv xc); pe_DATA E] AINV3 CF4 HG WIN);
            [exact CVx| in_list| in_list| exact LVS4| exact LVB4| exact VSBO3]. }
        assert (WZ5 : wzone E A4 [pe_S E; vb_buf (x_vv xc); pe_DATA E] [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
        set (xo := PST (x_p xc + 1) S_TagError (fupd (fupd (fupd (fupd (fupd (x_v xc) Fstate (st0 S_InTag)) Fattr_delim 0) Fstate (st0 S_TagError)) Fattr_vsb 0) Finclude_src 0)
                       (x_tag xc) (x_q xc) (x_vv xc) None None).
        assert (HScall : hstep E xk xo Ac A4 mh m4).
        { eapply (hstep_intro E xk xo Ac A4 mh m4 PARSE_STACK Vx nowhere).
          - eapply cframe_rebase; [exact CF4| clear; unfold_stacks_g; lia| eapply parse_window_mapped; [exact PE| exact ST4| unfold pframe; exact FR4]].
          - clear; lia.
          - eapply parse_window_mapped; [exact PE| exact ST4| unfold pframe; exact FR4].
          - subst xk. intros a [X|[X|[X|X]]]; unfold pzone; cbn [x_v x_va x_vi x_vv];
              [ left; exact X | right; right; right; left; exact X | right; right; right; right; left; exact X | do 5 right; exact X ].
          - subst xo xk. unfold parse_new, pzone. cbn [x_v x_vv x_va x_vi option_map fupd vf_beq vf_index N.eqb Pos.eqb].
            intros a [X|[X|X]]; [right; right; right; left; exact X| destruct X| destruct X].
          - subst xk. intros p k Hp NB. apply LK; [exact Hp| | | |]; intros ->; apply NB; unfold pst_blocks; cbn [x_v x_vv x_va x_vi];
              [right; left; left| right; left; right| right; right; left| right; right; right]; reflexivity.
          - subst xo xk. unfold pst_blocks. cbn [x_v x_vv x_va x_vi fupd vf_beq vf_index N.eqb Pos.eqb].
            intros p [X|[X|X]]; [left; left; exact X| destruct X| destruct X]. }
        (* [comment removed for export] *)
        apply rz_go; [exact MDH4| exact MDL4|].
        zstep. zstep.
        apply rz_stop.
        match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
          assert (HENV6 : henv_ok LayoutP0 VI0 (pe_H E) mf)
            by (eapply (henv_stores E A4 _ _ md4 _ _ PE0 AINV4 MU5 WM5 WZ5); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV4])
        end.
        eapply (KL (PST (x_p xc + 1) S_TagError
                        (fupd (fupd (fupd (fupd (fupd (fupd (x_v xc) Fstate (st0 S_InTag)) Fattr_delim 0) Fstate (st0 S_TagError)) Fattr_vsb 0) Finclude_src 0) Fattr_vsb 0)
                        (x_tag xc) (x_q xc) (x_vv xc) None None) A4 _ md4).
        2:{ eapply (ainv_stores E A4 m4 _ md4 _ _ PE0 AINV4 MU5 WM5 WZ5). }
        2:{ eapply md_frame_trans; [exact MDFc| exact MDF4]. }
        2:{ eapply hstep_trans; [exact HSc|]. eapply hstep_trans; [exact HS1|]. eapply hstep_trans; [exact HScall|].
            eapply hstep_stores; [exact MU5 | | eapply parse_window_mapped; [exact PE0| exact ST4| exact FR4]
                                 | intros p0 X; refine (pst_blocks_same xo _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E xo _ a _ _ X); reflexivity ].
            subst xo. w_in_zone_tac. left. unfold blk. lia. }
        2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LQ. lia. }
        apply Build_pinv; psimp; pinv_close PE0 AINV4 MU5 WM5 WZ5.
        + (* [comment removed for export] *) clear - VERP. lia.
        + (* [comment removed for export] *) clear - QE. lia.
        + (* [comment removed for export] *) assert (ILEN : 0 <= vb_len yi) by (clear - IO; (first [ dand3 IO as _ VIy _ | destruct IO as (_ & VIy & _) ]); unfold vsb_inv in VIy; lia).
          clear - OUT EVA EVI Vlen ILEN. unfold oacost, oicost in *. rewrite EVA, EVI in OUT. cbn [x_va x_vi x_st x_p x_vv x_v] in *. lia.
        + (* [comment removed for export] *) try subst yf; revert LB LB4; rewrite ?EVA, ?EVI; clear; unfold pw_bytes; cbn [vb_size vsb_set_flags]; intros; lia.
        + (* [comment removed for export] *) revert NL NL4; rewrite ?EVA, ?EVI; clear; unfold pw_nlive; intros; lia.
      - (* [comment removed for export] *)
        subst v4 vi4.
        subst yf. cbn [vb_buf vsb_set_flags] in LQA, DB, CF4, Vx.
        unfold vep_cells in VEPC4. psimp_in VEPC4. cbn [vi_st VI0] in VEPC4.
        assert (LK : forall p k, a_live Ac p = Some k -> p <> x_v xc Fattr_vsb -> p <> vb_buf y -> a_live A4 p = Some k)
          by (intros p k Hp N1 N2; rewrite (LQA p N1 N2); exact Hp).
        assert (LVS4 : a_live A4 (pe_S E) = Some 40) by (apply LK; [exact LVS| exact (not_eq_sym D_AS)| exact (not_eq_sym D_ABS)]).
        assert (LVB4 : a_live A4 (vb_buf (x_vv xc)) = Some (vb_size (x_vv xc))) by (apply LK; [exact LVB| exact (not_eq_sym D_AB)| exact (not_eq_sym D_ABB)]).
        assert (LDATA4 : a_live A4 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))) by (apply LK; [exact LDATA| exact (not_eq_sym D_AD)| exact (not_eq_sym D_ABD)]).
        assert (WAL4 : a_live A4 (pe_wa E) = Some 40) by (apply LK; [exact WAL| exact (not_eq_sym D_AW)| exact (not_eq_sym D_ABW)]).
        assert (DATA4 : data_obj LayoutP0 A4 m4 (pe_DATA E) (pe_inp E)).
        { eapply (data_obj_call (pe_H E) Ac A4 mh m4 mdc (pe_sp E) DOINCL_STACK Vx _ [pe_S E; vb_buf (x_vv xc); pe_DATA E] AINV3 CF4 HG WIN);
            [exact CVx| in_list| exact LDATA4| exact DATA3]. }
        assert (VSBO4 : vsb_obj LayoutP0 A4 m4 (pe_S E) (x_vv xc) false).
        { eapply (vsb_obj_call (pe_H E) Ac A4 mh m4 mdc (pe_sp E) DOINCL_STACK Vx _ [pe_S E; vb_buf (x_vv xc); pe_DATA E] AINV3 CF4 HG WIN);
            [exact CVx| in_list| in_list| exact LVS4| exact LVB4| exact VSBO3]. }
        assert (WZ5 : wzone E A4 [pe_S E; vb_buf (x_vv xc); pe_DATA E] [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
        set (xo := PST (x_p xc + 1) S_TagError (fupd (fupd (fupd (fupd (x_v xc) Fstate (st0 S_InTag)) Fattr_delim 0) Fstate (st0 S_TagError)) Fattr_vsb 0)
                       (x_tag xc) (x_q xc) (x_vv xc) None (x_vi xc)).
        assert (HScall : hstep E xk xo Ac A4 mh m4).
        { eapply (hstep_intro E xk xo Ac A4 mh m4 PARSE_STACK Vx nowhere).
          - eapply cframe_rebase; [exact CF4| clear; unfold_stacks_g; lia| eapply parse_window_mapped; [exact PE| exact ST4| unfold pframe; exact FR4]].
          - clear; lia.
          - eapply parse_window_mapped; [exact PE| exact ST4| unfold pframe; exact FR4].
          - subst xk. intros a [X|[X|[X|X]]]; unfold pzone; cbn [x_v x_va x_vi x_vv];
              [ left; exact X | right; right; right; left; exact X | right; right; right; right; left; exact X | do 5 right; exact X ].
          - subst xo xk. unfold parse_new, pzone. cbn [x_v x_vv x_va x_vi option_map fupd vf_beq vf_index N.eqb Pos.eqb]. rewrite VIN.
            intros a [X|[X|X]]; [right; right; right; left; exact X| destruct X| destruct X].
          - subst xk. intros p k Hp NB. apply LK; [exact Hp| |]; intros ->; apply NB; unfold pst_blocks; cbn [x_v x_vv x_va x_vi];
              [right; left; left| right; left; right]; reflexivity.
          - subst xo xk. unfold pst_blocks. cbn [x_v x_vv x_va x_vi fupd vf_beq vf_index N.eqb Pos.eqb]. rewrite VIN.
            intros p [X|[X|X]]; [left; left; exact X| destruct X| destruct X]. }
        (* [comment removed for export] *)
        apply rz_go; [exact MDH4| exact MDL4|].
        zstep. zstep.
        apply rz_stop.
        match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
          assert (HENV6 : henv_ok LayoutP0 VI0 (pe_H E) mf)
            by (eapply (henv_stores E A4 _ _ md4 _ _ PE0 AINV4 MU5 WM5 WZ5); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV4])
        end.
        eapply (KL (PST (x_p xc + 1) S_TagError
                        (fupd (fupd (fupd (fupd (fupd (x_v xc) Fstate (st0 S_InTag)) Fattr_delim 0) Fstate (st0 S_TagError)) Fattr_vsb 0) Fattr_vsb 0)
                        (x_tag xc) (x_q xc) (x_vv xc) None (x_vi xc)) A4 _ md4).
        2:{ eapply (ainv_stores E A4 m4 _ md4 _ _ PE0 AINV4 MU5 WM5 WZ5). }
        2:{ eapply md_frame_trans; [exact MDFc| exact MDF4]. }
        2:{ eapply hstep_trans; [exact HSc|]. eapply hstep_trans; [exact HS1|]. eapply hstep_trans; [exact HScall|].
            eapply hstep_stores; [exact MU5 | | eapply parse_window_mapped; [exact PE0| exact ST4| exact FR4]
                                 | intros p0 X; refine (pst_blocks_same xo _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E xo _ a _ _ X); reflexivity ].
            subst xo. w_in_zone_tac. left. unfold blk. lia. }
        2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LQ. lia. }
        apply Build_pinv; psimp; pinv_close PE0 AINV4 MU5 WM5 WZ5.
        + (* [comment removed for export] *) clear - VERP. lia.
        + (* [comment removed for export] *) clear - QE. lia.
        + (* [comment removed for export] *) clear - OUT EVA VIN Vlen. unfold oacost, oicost in *. rewrite EVA in OUT. rewrite VIN in *. cbn [x_va x_vi x_st x_p x_vv x_v] in *. lia.
        + (* [comment removed for export] *) rewrite VIN. rewrite VIN in VI. exact VI.
        + (* [comment removed for export] *) try subst yf; revert LB LB4; rewrite ?EVA, ?VIN; clear; unfold pw_bytes; cbn [vb_size vsb_set_flags]; intros; lia.
        + (* [comment removed for export] *) revert NL NL4; rewrite ?EVA, ?VIN; clear; unfold pw_nlive; intros; lia.
      - (* [comment removed for export] *)
        subst v4 vi4.
        subst yf. cbn [vb_buf vsb_set_flags] in LQA, DB, CF4, Vx.
        unfold vep_cells in VEPC4. psimp_in VEPC4.
        assert (LK : forall p k, a_live Ac p = Some k -> p <> x_v xc Fattr_vsb -> p <> vb_buf y -> a_live A4 p = Some k)
          by (intros p k Hp N1 N2; rewrite (LQA p N1 N2); exact Hp).
        assert (LVS4 : a_live A4 (pe_S E) = Some 40) by (apply LK; [exact LVS| exact (not_eq_sym D_AS)| exact (not_eq_sym D_ABS)]).
        assert (LVB4 : a_live A4 (vb_buf (x_vv xc)) = Some (vb_size (x_vv xc))) by (apply LK; [exact LVB| exact (not_eq_sym D_AB)| exact (not_eq_sym D_ABB)]).
        assert (LDATA4 : a_live A4 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))) by (apply LK; [exact LDATA| exact (not_eq_sym D_AD)| exact (not_eq_sym D_ABD)]).
        assert (WAL4 : a_live A4 (pe_wa E) = Some 40) by (apply LK; [exact WAL| exact (not_eq_sym D_AW)| exact (not_eq_sym D_ABW)]).
        assert (DATA4 : data_obj LayoutP0 A4 m4 (pe_DATA E) (pe_inp E)).
        { eapply (data_obj_call (pe_H E) Ac A4 mh m4 mdc (pe_sp E) DOINCL_STACK Vx _ [pe_S E; vb_buf (x_vv xc); pe_DATA E] AINV3 CF4 HG WIN);
            [exact CVx| in_list| exact LDATA4| exact DATA3]. }
        assert (VSBO4 : vsb_obj LayoutP0 A4 m4 (pe_S E) (x_vv xc) false).
        { eapply (vsb_obj_call (pe_H E) Ac A4 mh m4 mdc (pe_sp E) DOINCL_STACK Vx _ [pe_S E; vb_buf (x_vv xc); pe_DATA E] AINV3 CF4 HG WIN);
            [exact CVx| in_list| in_list| exact LVS4| exact LVB4| exact VSBO3]. }
        assert (WZ5 : wzone E A4 [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Finclude_src; oibuf xc] [(pe_VEP E, pe_VEP E + 312)]).
        { unfold oibuf. revert LVEP4 NE1 D_VB NE3 D_IV D_IBV. clear. intros. wzone_tac. }
        set (xo := PST (x_p xc + 1) S_InTag (fupd (fupd (fupd (fupd (x_v xc) Fstate (st0 S_InTag)) Fattr_delim 0) Finclude_continue ic) Fattr_vsb 0)
                       (x_tag xc) (x_q xc) (x_vv xc) None (x_vi xc)).
        assert (HScall : hstep E xk xo Ac A4 mh m4).
        { eapply (hstep_intro E xk xo Ac A4 mh m4 PARSE_STACK Vx nowhere).
          - eapply cframe_rebase; [exact CF4| clear; unfold_stacks_g; lia| eapply parse_window_mapped; [exact PE| exact ST4| unfold pframe; exact FR4]].
          - clear; lia.
          - eapply parse_window_mapped; [exact PE| exact ST4| unfold pframe; exact FR4].
          - subst xk. intros a [X|[X|[X|X]]]; unfold pzone; cbn [x_v x_va x_vi x_vv];
              [ left; exact X | right; right; right; left; exact X | right; right; right; right; left; exact X | do 5 right; exact X ].
          - subst xo xk. unfold parse_new, pzone. cbn [x_v x_vv x_va x_vi option_map fupd vf_beq vf_index N.eqb Pos.eqb].
            intros a [X|[X|X]]; [right; right; right; left; exact X| destruct X| right; right; right; right; right; left; destruct (x_vi xc); [exact X| destruct X]].
          - subst xk. intros p k Hp NB. apply LK; [exact Hp| |]; intros ->; apply NB; unfold pst_blocks; cbn [x_v x_vv x_va x_vi];
              [right; left; left| right; left; right]; reflexivity.
          - subst xo xk. unfold pst_blocks. cbn [x_v x_vv x_va x_vi fupd vf_beq vf_index N.eqb Pos.eqb].
            intros p [X|[X|X]]; [left; left; exact X| destruct X| left; right; right; exact X]. }
        (* [comment removed for export] *)
        apply rz_go; [exact MDH4| exact MDL4|].
        zstep. zstep.
        apply rz_stop.
        match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
          assert (HENV6 : henv_ok LayoutP0 VI0 (pe_H E) mf)
            by (eapply (henv_stores E A4 _ _ md4 _ _ PE0 AINV4 MU5 WM5 WZ5); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2; lia| exact HENV4])
        end.
        eapply (KL (PST (x_p xc + 1) S_InTag
                        (fupd (fupd (fupd (fupd (fupd (x_v xc) Fstate (st0 S_InTag)) Fattr_delim 0) Finclude_continue ic) Fattr_vsb 0) Fattr_vsb 0)
                        (x_tag xc) (x_q xc) (x_vv xc) None (x_vi xc)) A4 _ md4).
        2:{ eapply (ainv_stores E A4 m4 _ md4 _ _ PE0 AINV4 MU5 WM5 WZ5). }
        2:{ eapply md_frame_trans; [exact MDFc| exact MDF4]. }
        2:{ eapply hstep_trans; [exact HSc|]. eapply hstep_trans; [exact HS1|]. eapply hstep_trans; [exact HScall|].
            eapply hstep_stores; [exact MU5 | | eapply parse_window_mapped; [exact PE0| exact ST4| exact FR4]
                                 | intros p0 X; refine (pst_blocks_same xo _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E xo _ a _ _ X); reflexivity ].
            subst xo. w_in_zone_tac. left. unfold blk. lia. }
        2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LQ. lia. }
        apply Build_pinv; psimp; pinv_close PE0 AINV4 MU5 WM5 WZ5.
        + (* [comment removed for export] *) clear - VERP. lia.
        + (* [comment removed for export] *) clear - QE. lia.
        + (* [comment removed for export] *) clear - OUT EVA Vlen. unfold oacost, oicost in *. rewrite EVA in OUT. cbn [x_va x_vi x_st x_p x_vv x_v] in *. lia.
        + (* [comment removed for export] *) intros X. apply X. reflexivity.
        + (* [comment removed for export] *)
          destruct (x_vi xc) as [yi|] eqn:EVI; [| cbn in VI4; psimp_in VI4; exact VI4].
          cbn in VI4. psimp_in VI4. (first [ dand3 VI4 as Q1 Q2 Q3 | destruct VI4 as (Q1 & Q2 & Q3) ]). (first [ dand6 VI as _ _ _ Q3b Q4 _ | destruct VI as (_ & _ & _ & Q3b & Q4 & _) ]).
          split; [exact Q1|]. split; [| split; [exact Q3| split; [exact Q3b| split; [exact Q4| exact I]]]].
          eapply (vsb_obj_stores E A4 m4 _ md4 _ _ PE0 AINV4 MU5 WM5 WZ5); [in_list| in_list| exact Q2].
        + (* [comment removed for export] *) try subst yf; revert LB LB4; rewrite ?EVA; clear; unfold pw_bytes; cbn [vb_size vsb_set_flags]; intros; lia.
        + (* [comment removed for export] *) revert NL NL4; rewrite ?EVA; clear; unfold pw_nlive; intros; lia.
    Qed.
  End X.

  #[using="HDIA HVE"] Lemma PH_AttrValue : handler_stmt S_AttrValue.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    unfold disp_ms. rewrite ST. cbn [disp_pc disp_a1 disp_a2 disp_s7 oreg].
    apply (av_body E x A m md T PE); [unfold phi, rank; rewrite ST; reflexivity| exact KL| | exact PI| exact AINV| exact ST| exact PLT].
    apply (av_finish E x A m md T PE); [unfold phi, rank; rewrite ST; reflexivity| exact KL].
  Qed.
End S.
