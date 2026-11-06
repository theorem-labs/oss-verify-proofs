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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
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

Definition VSB_extend_entry := 0x19670.
(* [comment removed for export] *)
Definition EXT_STACK := 48 + REALLOC_STACK.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  (* [comment removed for export] *)
  Section Loop.
    Variables (xra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
              (m : mem) (sz : Z).
    Hypothesis SZ : 0 <= sz <= 4095.

    Notation AT pc xa2 xs2 :=
      (MS (mkR xra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 sz) xa2 a3 a4 a5 a6 a7
              xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          bvmap_empty (Z_to_bv 64 pc) (Z_to_bv 32 0) None m (seg_rom rsegs)).

    #[using="SZ"] Lemma ext_loop : forall (k : nat) (ns : Z) (xs2 : word),
      0 < ns -> sz <= ns * 2 ^ Z.of_nat k -> ns <= 8192 ->
      evt rsegs (fun ms => ms = AT 0x196d4 (Z_to_bv 64 (2 * vsb_dbl k ns sz)) (Z_to_bv 64 (vsb_dbl k ns sz)))
                (AT 0x196b4 (Z_to_bv 64 ns) xs2).
    Proof.
      induction k as [|k IH]; intros ns xs2 Hns Hsz Hle.
      - rewrite Z.pow_0_r in Hsz. cbn [vsb_dbl].
        zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. unsign K. klia K. }
        zstep. apply evt_done. shl1_to_mul. reflexivity.
      - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hsz by lia.
        cbn [vsb_dbl]. destruct (Z.ltb_spec ns sz) as [Hlt|Hge].
        + zstep. zstep. zstep. if_cases K; zify_cond K.
          2:{ exfalso. unsign K. klia K. }
          shl1_to_mul. apply IH; [lia | nia | lia].
        + zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. unsign K. klia K. }
          zstep. apply evt_done. shl1_to_mul. reflexivity.
    Qed.
  End Loop.

  Lemma VSB_extend_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (S addlen : Z) (v : vsb_rec) (lo : Z) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 addlen ->
      vsb_obj LayoutP0 A m S v false ->
      1 <= addlen -> vb_size v + addlen <= EXT_MAX ->
      (* [comment removed for export] *)
      a_livebytes A + vsb_extendsize (vb_size v + addlen) <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX ->
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + EXT_STACK <= bv_unsigned sp ->
      bv_unsigned sp + 64 <= 2^47 ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
              (v' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          vsb_obj LayoutP0 A' m' S v' false ->
          (forall q, q <> vb_buf v -> q <> vb_buf v' -> a_live A' q = a_live A q) ->
          stk rsegs m' lo (bv_unsigned sp) ->
          (* [comment removed for export] *)
          (exists nb, r = 0 /\ v' = vsb_set_buf_size v nb (vsb_extendsize (vb_size v + addlen)) /\
               (forall i, 0 <= i < vb_size v -> m' (Z_to_bv 64 (nb + i)) = m (Z_to_bv 64 (vb_buf v + i))) /\
               (nb = vb_buf v \/ (a_live A nb = None /\ a_live A' (vb_buf v) = None)) /\
               a_livebytes A' = a_livebytes A + vsb_extendsize (vb_size v + addlen) - vb_size v /\ a_nlive A' = a_nlive A /\
               cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) EXT_STACK
                        (fun a => blk (vb_buf v) (vb_size v) a \/ (S <= a < S + 40))
                        (blk nb (vsb_extendsize (vb_size v + addlen))) m m') ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 VSB_extend_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. intros AINV MI A0 A1 VOBJ AL1 AL2 LBUD NBUD TP SP16 RA2 ST CEIL LO SPHI K.
    rewrite A0, A1.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md S v false AINV VOBJ)) as dR_1; dand11 dR_1 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB0 Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md S v false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB0 & Smap & Bmap) ]).
    (first [ dand6 VOBJ as VSBC VINV LS LB SNB VBUF | destruct VOBJ as (VSBC & VINV & LS & LB & SNB & VBUF) ]). (first [ dex1 VBUF as bs0; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs0 U8 LBS _ | destruct VBUF as (bs0 & U8 & LBS & _) ]).
    pose proof VINV as VINV0.
    (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vb16 | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vb16) ]).
    pose proof (as_layout_order (L:=LayoutP0)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY.
    pose proof alloc_ceiling_val as CV.
    cbn [al_segs LayoutP0] in VSBC, U8. unfold vsb_cells in VSBC.
    pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
    unfold EXT_STACK, REALLOC_STACK, EXT_MAX in *. unfold VSB_extend_entry.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8304, bv_unsigned sp); (S, S + 40)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 8304, bv_unsigned sp); (S, S + 40)]).
    { cbn. split; [left; lia|]. split; [right; left; exists S, 40; split; [exact LS|lia]| exact I]. }
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 48%nat ST.
    do 6 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. if_cases KC; zify_cond KC.
    { exfalso. revert KC. rewrite Vfl. vm_compute. discriminate. }
    clear KC.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (first [ pose proof ((vsb_extendsize_spec (vb_size v + addlen) ltac:(lia))) as dR_5; dand3 dR_5 as NS1 NS2 NS3 | pose proof (vsb_extendsize_spec (vb_size v + addlen) ltac:(lia)) as (NS1 & NS2 & NS3) ]).
    (* [comment removed for export] *)
    eapply (evt_cut rsegs (fun ms => exists xa2 xa3, ms =
      MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 (-1))
              (zx32 (Z_to_bv 64 (vb_flags v))) (Z_to_bv 64 (vb_size v + addlen)) xa2 xa3 a4 a5 a6 a7
              (Z_to_bv 64 (vsb_extendsize (vb_size v + addlen))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         bvmap_empty (Z_to_bv 64 0x196d4) (Z_to_bv 32 0) None _ (seg_rom rsegs))).
    { zstep. if_cases KR; zify_cond KR; unsign KR.
      - (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. apply evt_done. eexists _, _.
        rewrite roundup_pagemask by lia. unfold vsb_extendsize.
        rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
      - (* [comment removed for export] *)
        zstep.
        eapply evt_cut; [apply (ext_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (vb_size v + addlen) ltac:(lia) 9 16); cbn; lia|].
        intros ms1 ->. apply evt_done. eexists _, _. unfold vsb_extendsize.
        rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    (intros ms1; (first [ intro dR_8; dand3 dR_8 as xa2 xa3 -> | intros (xa2 & xa3 & ->) ])).
    (* [comment removed for export] *)
    zstep. if_cases KA; zify_cond KA. { exfalso. unsign KA. klia KA. } clear KA.
    zstep. zstep. if_cases KD; zify_cond KD.
    2:{ exfalso. revert KD. rewrite Vfl. vm_compute. discriminate. }
    clear KD.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    apply rz_stop.
    pose proof (ainv_munch LayoutP0 A m _ md _ AINV MU WM CFP) as AINV1.
    eapply (as_realloc_cps (L:=LayoutP0)) with (old := vb_size v);
      [ exact AINV1 | exact MI | reflexivity | reflexivity | lia | lia | exact LB
      | rewrite NREQ_CAP_eq; pose proof (vsb_extendsize_tight (vb_size v + addlen)); lia | exact LBUD | exact NBUD | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; unfold REALLOC_STACK; lia
      | rewrite unsigned_lit by lia; eapply (stk_mapped (L:=LayoutP0)); [exact ST| exact CEIL | unfold REALLOC_STACK; lia | lia]
      | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' AINV' MI' MDF OUT.
    pose proof (as_lazy_nil A' m' md' AINV') as [MDL' MDH'].
    rewrite unsigned_lit in OUT by lia.
    (* [comment removed for export] *)
    pose proof (crange_block (L:=LayoutP0) A m0 md S 40 S 40 AINV1 LS ltac:(lia) ltac:(lia) ltac:(lia)) as CS.
    pose proof (crange_block (L:=LayoutP0) A m0 md _ _ (vb_buf v) (Z.of_nat (length bs0)) AINV1 LB ltac:(lia) ltac:(lia) ltac:(lia)) as CB.
    pose proof (crange_stack (L:=LayoutP0) A m0 md (bv_unsigned sp - 48) 48 AINV1 ltac:(lia) ltac:(lia)
                  (rw_cells_mapped LayoutP0 m0 _ _ FR ltac:(off_image_solve LayoutP0))) as CF.
    destruct OUT as (NZ & LIVEr & REL & LIVEq & COPY & LB1 & NL1 & FRK).   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      pose proof (as_live_disjoint A m0 md S 40 (vb_buf v) (vb_size v) AINV1 LS LB SNB) as DSB.
      try clear U8. acall_xfer FRK. clear AINV1.
      (first [ pose proof ((as_live_ok A' m' md' r _ AINV' LIVEr)) as dR_6; dand7 dR_6 as _ R16 Rlo Rhi Rimg Rmap Rown | pose proof (as_live_ok A' m' md' r _ AINV' LIVEr) as (_ & R16 & Rlo & Rhi & Rimg & Rmap & Rown) ]).
      (first [ pose proof ((newblock_cells (L:=LayoutP0) A' m' md' r _ AINV' LIVEr)) as dR_7; dex1 dR_7 as bs1; dand3 dR_7 as LBS1 NB1 CR1 | pose proof ((newblock_cells (L:=LayoutP0) A' m' md' r _ AINV' LIVEr)) as dR_7; dand4 dR_7 as bs1 LBS1 NB1 CR1 | destruct (newblock_cells (L:=LayoutP0) A' m' md' r _ AINV' LIVEr) as (bs1 & LBS1 & NB1 & CR1) ]).
      cbn [al_segs LayoutP0] in NB1.
      clear Rimg.
      assert (SNR : S <> r). { intros ->. destruct REL as [E|[E _]]; [exact (SNB E)| rewrite LS in E; discriminate]. }
      assert (LS' : a_live A' S = Some 40). { rewrite (LIVEq S SNR SNB). exact LS. }
      pose proof (as_live_disjoint A' m' md' S 40 r _ AINV' LS' LIVEr SNR) as DSR.
      (* [comment removed for export] *)
      lazymatch type of MU with munch ?W _ _ =>
        pose proof (munch_refl W m') as MU2; pose proof (wmono_refl rsegs m') as WM2 end.
      rz_resume MDH' MDL'.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KZ; zify_cond KZ. { exfalso. klia KZ. } clear KZ.
      (* [comment removed for export] *)
      pose proof (rw_cells_read_sub rsegs _ _ _ 34 1 VSBC ltac:(lia) ltac:(cbn; lia)) as RDF.
      rewrite Vfl in RDF. unfold VSB_FLAGS_LIVE in RDF.
      match type of RDF with _ = Some ?r => let r' := eval vm_compute in r in change r with r' in RDF end.
      zstep. zstep. zstep. if_cases KD; zify_cond KD. 2:{ exfalso. dead KD. } clear KD RDF.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. do 5 zstep. zstep. zstep.
      try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. cbv beta.
      set (v' := vsb_set_buf_size v r (vsb_extendsize (vb_size v + addlen))).
      lazymatch type of MU2 with munch ?W _ ?mx =>
        assert (CFP' : client_fp LayoutP0 A' W)
          by (cbn; split; [left; lia|]; split; [right; left; exists S, 40; split; [exact LS'|lia]| exact I]);
        pose proof (ainv_munch LayoutP0 A' m' mx md' W AINV' MU2 WM2 CFP') as AINV2 end.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 A' _ md' v');
        [ exact AINV2 | exact MI' | exact MDF
        | split; [exact VSBC|]; split; [unfold vsb_inv; cbn [v' vsb_set_buf_size vb_size vb_len vb_error vb_indent vb_flags vb_buf]; lia|];
          split; [exact LS'|]; split; [exact LIVEr|]; split; [exact SNR|];
          exists bs1; split; [apply (u8arr_of_rw_cells rsegs _ _ _ _ NB1)|]; split; [cbn [v' vsb_set_buf_size vb_size]; lia| intros X; discriminate X]
        | intros q Q1 Q2; apply LIVEq; [exact Q2|exact Q1] | exact ST | ].
      exists r. split; [reflexivity|]. split; [reflexivity|]. split; [|split; [|split; [exact LB1|split; [exact NL1|]]]].
      + (* [comment removed for export] *)
        intros i Hi.
        rewrite (MU2 (Z_to_bv 64 (r + i))) by (rewrite unsigned_lit by lia; cbn [outside]; lia).
        rewrite (COPY i) by lia.
        apply (MU (Z_to_bv 64 (vb_buf v + i))). rewrite unsigned_lit by lia. cbn [outside]. lia.
      + destruct REL as [E|[E1 E]]; [left; exact E| right; split; [exact E1| exact E]].
      + eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m _ m' _ _ _);
          [ exact MU | | exact FRK | lia | lia | intros a X; left; exact X | intros a X; left; exact X
          | exact MU2 | 
          | eapply (stk_mapped (L:=LayoutP0)); [exact ST | exact CEIL | lia | lia] ].
        * intros a Ha NO. cbn [outside] in NO. lia.
        * intros a Ha NO. cbn [outside] in NO. unfold blk. lia.
  Qed.
End S.
