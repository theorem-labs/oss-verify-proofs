(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel AtpModel OdModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Sj_h_bom F_memcpy F_memset Atp_h_defs Atp_h_push Atp_h_find Atp_kitu Od_pro.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Sj_h_arith Od_setup_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Od_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjStage1.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition cblocks (cpo : option bptr) (COPY n : Z) : list block :=
  match cpo with Some p => [(p, COPY, n)] | None => [] end.

Definition pad_post (sp0 : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (lo B D : Z) (d : list Z) (init : bool) (m0 : mem) (bv : bptr) (A cap : Z) (jr jfd : list byte)
    (cpo : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs3 t3 t4 t5 t6 m' (errv' : word) (COPY BUF : Z) (j0 j289 : list byte),
    ms' = MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 COPY) (Z_to_bv 64 (zlength (od_doc d))) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 BUF) xs3 (Z_to_bv 64 (od_action d)) (Z_to_bv 64 (match cpo with Some _ => 0 | None => 1 end)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x272f8) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo sp0 /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (cblocks cpo COPY (zlength (od_s0 d) + 64) ++ (bv, A, 16 * cap) :: LB) m'
    /\ lx_pres LB (sp0 + 496) [LXW_SJ] m0 m' /\ lx_statics m' /\ sj_statics m' init /\ payload_ok m' LB D d
    /\ vrep m' (sp0 + 344) A (cap, Z.of_nat (od_P d), Some bv) (od_els D d) jr
    /\ match cpo with
       | Some _ => bytes_at usegs m' BUF (padded_bytes (od_doc d)) /\ COPY <= BUF /\ BUF + zlength (od_doc d) <= COPY + zlength (od_s0 d)
                   /\ rblock_range COPY (zlength (od_s0 d) + 64)
       | None => COPY = 0 /\ BUF = 0 /\ od_doc d = []
       end
    /\ rw_cells usegs m' sp0 [CB 288 j0]
    /\ rw_cells usegs m' (sp0 + 288) [C1 (Z_to_bv 8 0); CB 7 j289; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 1024);
                                      C8 (Z_to_bv 64 (zlength (od_doc d))); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' (sp0 + 368) [CB 24 jfd]
    /\ rw_cells usegs m' (sp0 + 392) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Ltac readdr H e := lazymatch type of H with rw_cells _ _ ?a _ => replace a with e in H by lia end.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  Lemma od_pad_cps : forall {R} (k : option bptr -> M PState R) (Q : R -> PState -> machine_state -> Prop)
      (x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (s00 s : PState) (LB : list block) (sp0 lo B D : Z) (d : list Z) (init : bool) (errv : word)
      (A cap : Z) (bv : bptr) (jr j0 j288 jfd : list byte),

    RHEAP s00 LB m0 -> lx_statics m0 ->

    RHEAP s ((bv, A, 16 * cap) :: LB) m -> rauxv_ok m B -> sp0 + 496 <= B -> B < 2^63 ->
    stk usegs m lo sp0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 + 496 - LX_FUZZ_STACK ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> (sp0 + 496) mod 16 = 0 ->
    ps_fa s = ps_fa s00 -> ps_so s = ps_so s00 ->
    vrep m (sp0 + 344) A (cap, Z.of_nat (od_P d), Some bv) (od_els D d) jr -> cap < 2^26 ->
    lx_pres LB (sp0 + 496) [LXW_SJ] m0 m -> sj_statics m init -> payload_ok m LB D d ->
    rw_cells usegs m sp0 [CB 288 j0] ->
    rw_cells usegs m (sp0 + 288) [CB 56 j288] ->
    rw_cells usegs m (sp0 + 368) [CB 24 jfd] ->
    rw_cells usegs m (sp0 + 392) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    (forall cpo s' ms',
        pad_post sp0 gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc s00 LB lo B D d init m0 bv A cap jr jfd cpo s' ms' ->
        implM usegs (k cpo) s' Q ms') ->
    implM usegs
      (mbind (if zlength (od_s0 d) <=? SJ_PADMAX then mbind (newnt lops (SJ_COPY (zlength (od_s0 d)))) (fun p => mret (Some p)) else mret None) k)
      s Q
      (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 (od_action d)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x27180) fc None m (seg_rom usegs)).
  Proof.
    intros until jfd.
    intros HEAP00 LXS0 HEAP AUX QB B63 ST CEIL GLO LO ERR MI AL16 FA SO VR CAPB PRES SJS PL OUT PARS' XFD SAVE HK.
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 609404) by reflexivity. rewrite ELX in ERR.
    pose proof PL as (PB & PRNG & D0 & DN & DLEN & PIN).
    assert (ZD : zlength d = Z.of_nat (length d)) by reflexivity. pose proof DLEN as DLEN'. change (2^26) with 67108864 in DLEN'.
    assert (LBL : length (to_bytes d) = length d) by apply to_bytes_length.
    pose proof (od_s0_len d) as S0L. pose proof (od_doc_len d) as (DCL0 & DCL & DCD & DCP). unfold SJ_PADMAX in DCP.
    remember (zlength (od_s0 d)) as len0 eqn:Elen0.
    assert (LEN0 : 0 <= len0) by (subst len0; unfold zlength; lia).

    apply (rw_cells_split_CB usegs _ _ [] 56 _ [] [1;7; 8;8;8;8;8;8]%nat) in PARS'; [|reflexivity]. cbn [mk_CB_cells app] in PARS'.
    repeat match type of PARS' with context [CB ?n ?t] => lazymatch t with take _ _ => idtac end; let j := fresh "j" in set (j := t) in PARS'; clearbody j end.

    destruct (OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P.Od_setup_kit.od_els_shape D d) as (P0 & rest & EE & HP0 & HS0). rewrite <- Elen0 in EE. rewrite EE in VR.
    destruct VR as (ELS & SZ & SV & BLK). pose proof BLK as BLK'. unfold vblk in BLK'. destruct BLK' as (BE & BJ & BR & CAPGE1).
    pose proof BR as (A0 & A16 & _ & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in AC.
    destruct (rw_cells_split_at1 _ _ _ 2%nat BE) as [BE2 BER]. cbn [velts fst snd firstn skipn cells_size csize Nat.add] in BE2, BER. change (firstn 0 (velts rest)) with (@nil cell) in BE2. hide BER. clear PB.
    assert (P0R : 0 <= P0 < 2^64) by (destruct HP0 as [[-> _] | ->]; lia).
    assert (A8 : A mod 8 = 0) by (clear - A16; pose proof (Z.mod_divide A 16 ltac:(lia)) as [H _]; destruct (H A16) as [q ->]; replace (q * 16) with (2 * q * 8) by lia; apply Z.mod_mul; lia).
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB (sp0 + 496) [LXW_SJ] a -> outside [(sp0, sp0 + 496)] a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(sp0, sp0 + 496)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide BJ. hide BE.
    unfold implM. iprefix.

    step. zstep. hstep. hstep. hstep. hstep. step. hstep. hstep. hstep.

    step. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
    zstep. rewrite (Atp_kitu.land7_mod8 A) by lia. step. if_true.
    step. step. zstep. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    rename PARS' into PA. rename OUT into LOW'.

    pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
    assert (HEAP1 : RHEAP s ((bv, A, 16 * cap) :: LB) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES1 : lx_pres LB (sp0 + 496) [LXW_SJ] m0 m1).
    { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    assert (SJS1 : sj_statics m1 init).
    { eapply sj_statics_agree; [exact AG1| | exact SJS]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]; split; [lia| exact I]. }
    assert (PL1 : payload_ok m1 LB D d).
    { eapply payload_ok_agree; [exact AG1| exact PL|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I]. }
    assert (LXS1 : lx_statics m1).
    { eapply lx_statics_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES1)| | exact LXS0]. intros a Ha. apply lxs_addr_client; [exact Ha|].
      pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_GOT_TABS, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
      unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
    pose proof LXS1 as (_ & _ & GOT1 & _).
    unhide BJ. unhide BER.
    pose proof BLK as BLK0. hide BLK0.
    apply (vblk_agree _ _ _ _ _ _ _ _ _ AG1) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO; lia| exact ELS| lia].
    clear BJ BER BE AG1.
    if_cases KB; zify_cond KB.
    -
      assert (EDOC : od_doc d = []) by (unfold od_doc, od_copied; rewrite <- Elen0; replace (len0 <=? SJ_PADMAX) with false by (symmetry; apply Z.leb_gt; unfold SJ_PADMAX; lia); reflexivity).
      replace (len0 <=? SJ_PADMAX) with false by (symmetry; apply Z.leb_gt; unfold SJ_PADMAX; lia).

      step. step. step. step. zstep. step. step. if_true. step. step. if_false. hstep. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1b end.
      ihere. to_implM. apply implM_ret_bind. apply HK.
      unfold pad_post. do 17 eexists. exists m1b, errv, 0, 0. do 2 eexists.
      split; [rewrite EDOC; cbv delta [mkR]; reflexivity|].
      split; [exact MI|]. split; [exact ST|]. split; [rewrite ELX; exact ERR|].
      split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      split; [exact FA|]. split; [exact SO|].
      split. { cbn [cblocks app]. eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      split. { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
      pose proof (agree_on_of_munch _ _ _ MU WM) as AGb.
      split. { eapply lx_statics_agree; [exact AGb| | eapply lx_statics_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES)| | exact LXS0]].
               - intros a Ha. pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1. cbn [outside]. split; [lia| exact I].
               - intros a Ha. apply lxs_addr_client; [exact Ha|]. pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_GOT_TABS, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
                 unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
      split. { eapply sj_statics_agree; [exact AGb| | exact SJS]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]; split; [lia| exact I]. }
      split. { eapply payload_ok_agree; [exact AGb| exact PL|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
               unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I]. }
      split. { rewrite EE. split; [exact ELS|]. split; [exact SZ|]. split; [exact SV|]. unhide BLK0.
               eapply vblk_agree; [exact AGb| | exact ELS| lia| exact BLK0]. intros a _ Ha. cbn [outside]. clear - Ha AC CEIL LO. lia. }
      split; [split; [reflexivity| split; [reflexivity| exact EDOC]]|].
      split; [exact LOW'|]. split; [rewrite EDOC; exact PA|]. split; [exact XFD| exact SAVE].
    -
      assert (EDOC : od_doc d = SjAlloc.strip_bom (od_s0 d)) by (unfold od_doc, od_copied; rewrite <- Elen0; replace (len0 <=? SJ_PADMAX) with true by (symmetry; apply Z.leb_le; unfold SJ_PADMAX; lia); reflexivity).
      replace (len0 <=? SJ_PADMAX) with true by (symmetry; apply Z.leb_le; unfold SJ_PADMAX; lia).
      unfold SJ_COPY. unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG in GOT1. unfold MallocRep.wz in GOT1.
      clear MU WM BLK0.
      pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.

      step. zstep. step. step. step. step.
      ihere. to_implM. apply implM_bind_assoc.
      eapply implM_bind.
      { eapply (opnew_arr_nt_proof HM) with (B := B) (lo := lo);
          [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| rewrite ELX; eassumption| assumption| lia| lia]. }
      cbv beta. intros pcp st2 ms2 PO. unfold opnew_postZ in PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & COPY & junk2
                      & -> & MI2 & ST2 & ERR2 & AUX2 & HP2 & FA2 & SO2 & BRC & HEAP2 & BLKC).
      replace (ret_pc (Z_to_bv 64 0x271e4)) with (Z_to_bv 64 0x271e4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR2. apply implM_ret_bind.
      pose proof BRC as (C0 & _ & _ & CC & CS). unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in CC.

      pose proof (agree_of_heap_pres _ _ _ _ HP2) as AG2.
      assert (FRH : forall a, sp0 <= a < sp0 + 496 -> rclient_addr ((bv, A, 16 * cap) :: LB) sp0 a) by (intros a Ha; left; lia).
      apply (rw_cells_agree _ _ _ _ _ AG2) in PA; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in LOW'; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in XFD; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in SAVE; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in SV; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG2) in BLK; [| intros a _ Ha; right; right; exists (bv, A, 16 * cap); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| exact ELS| lia].
      assert (PRES2 : lx_pres LB (sp0 + 496) [LXW_SJ] m0 m2).
      { eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP2| lia| intros b Hb; right; exact Hb]. }
      pose proof (statics_heap _ _ _ _ HP2 ltac:(unfold GLOBALS_TOP; lia)) as (LXSf & SJSf & _).
      pose proof (SJSf _ SJS1) as SJS2. pose proof (LXSf LXS1) as LXS2. clear LXSf SJSf.
      assert (PL2 : payload_ok m2 LB D d).
      { eapply payload_ok_agree; [exact AG2| exact PL1|]. intros b a Hb Ha. right; right. exists b. split; [right; exact Hb| exact Ha]. }
      clear AG2 HP2 HEAP1 AUX1 PRES1 SJS1 PL1 LXS1 GOT1 BE2 MU WM HEAP AUX PRES SJS PL.

      replace (Z.to_nat (len0 + 64)) with (Z.to_nat len0 + 64)%nat in BLKC by lia.
      apply rw_cells_CB_split2 in BLKC. destruct BLKC as [BDOC BPAD]. rewrite Z2Nat.id in BPAD by lia.
      pose proof (munch_refl [(sp0, sp0 + 496); (COPY, COPY + (len0 + 64))]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      unfold implM. iprefix.

      step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
      step. zstep. rewrite (OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U.Od_defs.lxor_ones64 COPY) by lia. step.
      if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K CC CS C0 LEN0; lia].
      zstep. step. step. step.
      eapply evt_cut.
      { eapply memset_callZ with (junk := drop (Z.to_nat len0) junk2); [exact BPAD| assumption| lia| lia| lia| lia]. }
      cbv beta. intros ms' PO. unfold memset_postZ in PO.
      destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m3 & -> & MU3 & WM3 & MI3 & PAD3).
      replace (ret_pc (Z_to_bv 64 0x27208)) with (Z_to_bv 64 0x27208) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      change (0 mod 256) with 0 in PAD3.
      hide MU. hide WM. transport_after_call usegs m2 m3 MU3 WM3. unhide MU. unhide WM.

      pose proof (fun p' A' n' H => LH_head_sep _ _ _ _ _ _ p' A' n' HEAP2 H) as SEPC.
      assert (OUTC : forall a, 0x7f000 <= a < GLOBALS_TOP -> outside [(COPY + len0, COPY + len0 + 64)] a).
      { intros a Ha. unfold GLOBALS_TOP in Ha. cbn [outside]. clear - Ha CS C0 LEN0. lia. }
      pose proof (statics_munch _ _ _ rr_guard MU3 WM3 OUTC) as (LXSf & SJSf & _). pose proof (LXSf LXS2) as LXS3. pose proof (SJSf _ SJS2) as SJS3. clear LXSf SJSf.
      pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG3.
      assert (PL3 : payload_ok m3 LB D d).
      { eapply payload_ok_agree; [exact AG3| exact PL2|]. intros [[bi ba] bn] a Hb Ha.
        pose proof (SEPC bi ba bn ltac:(right; exact Hb)) as SP. cbn [blk_addr blk_size blk_id fst snd outside] in *. clear - SP Ha LEN0. lia. }
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG3) in BLK; [| intros a _ Ha; pose proof (SEPC bv A (16 * cap) ltac:(left; reflexivity)) as SP; cbn [outside]; clear - SP Ha LEN0; lia| exact ELS| lia].
      assert (PRES3 : lx_pres LB (sp0 + 496) [LXW_SJ] m0 m3).
      { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU3| exact WM3|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[([[bi ba] bn] & Hb & Hr)|HC]]; [clear - HC CC CEIL LO; lia| | clear - HC CS C0 LEN0; lia].
        pose proof (SEPC bi ba bn ltac:(right; exact Hb)) as SP. cbn [blk_addr blk_size blk_id fst snd] in *. clear - SP Hr LEN0. lia. }

      assert (MU3' : munch [(sp0, sp0 + 496); (COPY, COPY + (len0 + 64))]%Z m2 m3).
      { eapply munch_weaken; [| exact MU3]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
      pose proof (munch_trans _ _ _ _ MU MU3') as MU3''. pose proof (wmono_trans usegs _ _ _ WM WM3) as WM3''.
      clear MU WM MU3 MU3' AG3. rename MU3'' into MU. rename WM3'' into WM.

      assert (PRS0 : Forall (fun c => 0 <= c < 256) (od_s0 d)).
      { rewrite HS0. apply Forall_firstn'. destruct d as [|b0 d']; [constructor| inversion PRNG; assumption]. }
      assert (DOCB : len0 = 0 \/ (bytes_at usegs m3 P0 (to_bytes (od_s0 d)) /\ P0 = D + 1 /\ exists b0, In b0 LB /\ blk_addr b0 <= P0 /\ P0 + len0 <= blk_addr b0 + blk_size b0)).
      { destruct (Z.eq_dec len0 0) as [Z0|NZ]; [left; exact Z0| right].
        destruct HP0 as [[EP ES]|EP]. { exfalso. apply NZ. subst len0. rewrite ES. reflexivity. }
        destruct d as [|b0 d']. { exfalso. apply NZ. subst len0. reflexivity. }
        pose proof (payload_ok_tl _ _ _ _ _ PL3) as (PB3 & _ & _ & _ & _ & PIN3). cbn [list.tail tl] in HS0.
        split. { rewrite HS0, to_bytes_firstn. replace P0 with (D + 1) by lia. apply bytes_at_firstn. exact PB3. }
        split; [lia|].
        destruct PIN3 as [E0|(b1 & Hb & Hb1 & Hb2)]. { exfalso. apply NZ. subst len0. rewrite HS0, E0. destruct (length (od_s0 (b0 :: []))); reflexivity. }
        exists b1. split; [exact Hb|]. assert (len0 <= zlength d') by (rewrite Elen0, HS0; unfold zlength; rewrite firstn_length; lia). lia. }

      lazymatch goal with |- evt _ ?QQ _ =>
      assert (FIN : forall (m4 : mem) (pre bs : list Z) (BUF L : Z) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 : word) (j289 : list byte),
        munch [(sp0 + 328, sp0 + 336); (COPY, COPY + len0)]%Z m3 m4 -> wmono usegs m3 m4 -> mem_inv usegs m4 ->
        rw_cells usegs m4 COPY [CB (Z.to_nat len0) (to_bytes (od_s0 d))] ->
        rw_cells usegs m4 (sp0 + 288) [C1 (Z_to_bv 8 0); CB 7 j289; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 1024);
                                      C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 0)] ->
        SjAlloc.strip_bom (od_s0 d) = bs -> od_s0 d = pre ++ bs -> BUF = COPY + zlength pre -> L = zlength bs ->
        evt usegs QQ (MS (mkR y1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 COPY) (Z_to_bv 64 L) y10 y11 y12 y13 y14 y15 y16 y17
                               (Z_to_bv 64 BUF) y19 (Z_to_bv 64 (od_action d)) (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 0x272f8) fc None m4 (seg_rom usegs))) end.
      { intros m4 pre bs BUF L y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 j289' MU4 WM4 MI4 BDOC4 PA4 EBS EPRE EBUF EL.
        clear BDOC DOCB PA. hide MU. hide WM. transport_after_call usegs m3 m4 MU4 WM4. unhide MU. unhide WM.
        assert (OUTC4 : forall a, 0x7f000 <= a < GLOBALS_TOP -> outside [(sp0 + 328, sp0 + 336); (COPY, COPY + len0)] a).
        { intros a Ha. unfold GLOBALS_TOP in Ha. cbn [outside]. clear - Ha CS C0 LEN0 GLO LO. lia. }
        pose proof (statics_munch _ _ _ rr_guard MU4 WM4 OUTC4) as (LXSf & SJSf & _). pose proof (LXSf LXS3) as LXS4. pose proof (SJSf _ SJS3) as SJS4. clear LXSf SJSf.
        pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
        assert (PL4 : payload_ok m4 LB D d).
        { eapply payload_ok_agree; [exact AG4| exact PL3|]. intros [[bi ba] bn] a Hb Ha.
          pose proof (SEPC bi ba bn ltac:(right; exact Hb)) as SP. pose proof (BLB a ltac:(exists (bi, ba, bn); split; [exact Hb| exact Ha])) as BA.
          cbn [blk_addr blk_size blk_id fst snd outside] in *. clear - SP Ha LEN0 BA CEIL LO. lia. }
        apply (vblk_agree _ _ _ _ _ _ _ _ _ AG4) in BLK; [| intros a _ Ha; pose proof (SEPC bv A (16 * cap) ltac:(left; reflexivity)) as SP; cbn [outside]; clear - SP Ha LEN0 AC CEIL LO; lia| exact ELS| lia].
        assert (PRES4 : lx_pres LB (sp0 + 496) [LXW_SJ] m0 m4).
        { eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_of_munch; [exact MU4| exact WM4|].
          intros a Ha [HX HC]. cbn [outside]. destruct HC as [HC|[([[bi ba] bn] & Hb & Hr)|HC]]; [clear - HC CC CEIL LO LEN0; lia| | clear - HC CS C0 LEN0 GLO LO; lia].
          pose proof (SEPC bi ba bn ltac:(right; exact Hb)) as SP. pose proof (BLB a ltac:(exists (bi, ba, bn); split; [exact Hb| exact Hr])) as BA.
          cbn [blk_addr blk_size blk_id fst snd] in *. clear - SP Hr LEN0 BA CEIL LO. lia. }
        assert (HEAP4 : RHEAP st2 ((pcp, COPY, len0 + 64) :: (bv, A, 16 * cap) :: LB) m4).
        { eapply LH_frame; [eapply LH_frame; [exact HEAP2| exact MU| exact WM|]| exact MU4| exact WM4|].
          - constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor]. eapply (W_ok_block _ (pcp, COPY, len0 + 64)); [left; reflexivity| cbn; lia| cbn; lia].
          - constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor]. eapply (W_ok_block _ (pcp, COPY, len0 + 64)); [left; reflexivity| cbn; lia| cbn; lia]. }
        assert (AUX4 : rauxv_ok m4 B).
        { eapply rauxv_ok_frame; [eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]| exact MU4| exact WM4|].
          - constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; clear - CC CS C0 CEIL LO LEN0 QB; lia| constructor].
          - constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; clear - CC CS C0 CEIL LO LEN0 QB; lia| constructor]. }

        lazymatch goal with H : rw_cells usegs m4 (COPY + len0) _ |- _ => rename H into PAD4 end.
        assert (BUF4 : bytes_at usegs m4 COPY (padded_bytes (od_s0 d))).
        { pose proof (rw_cells_join _ _ _ _ _ BDOC4 PAD4 ltac:(cbn [cells_size csize Nat.add]; lia)) as J. destruct J as [[_ HB] _].
          cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB. unfold padded_bytes, zbytes. exact HB. }
        assert (BUF5 : bytes_at usegs m4 BUF (padded_bytes bs)).
        { rewrite EPRE in BUF4. unfold padded_bytes, zbytes in BUF4 |- *. rewrite map_app, <- app_assoc in BUF4. apply bytes_at_app in BUF4.
          destruct BUF4 as [_ BUF4]. rewrite length_map in BUF4. subst BUF. exact BUF4. }
        assert (LPRE : len0 = zlength pre + zlength bs) by (rewrite Elen0, EPRE; unfold zlength; rewrite length_app; lia).
        ihere. to_implM. apply HK.
        unfold pad_post. do 17 eexists. exists m4, errv2, COPY, BUF. do 2 eexists.
        rewrite EDOC, EBS, <- Elen0.
        split; [subst L; cbv delta [mkR]; reflexivity|].
        split; [exact MI4|]. split; [eassumption|]. split; [rewrite ELX; eassumption|]. split; [exact AUX4|]. split; [congruence|]. split; [congruence|].
        split; [cbn [cblocks app]; exact HEAP4|]. split; [exact PRES4|]. split; [exact LXS4|]. split; [exact SJS4|]. split; [exact PL4|].
        split. { rewrite EE. split; [exact ELS|]. split; [exact SZ|]. split; [eassumption| exact BLK]. }
        split. { split; [exact BUF5|]. split; [unfold zlength in *; lia|]. split; [unfold zlength in *; lia| exact BRC]. }
        split; [eassumption|]. split; [subst L; exact PA4|]. split; eassumption. }

      hide MU. hide WM.
      pose proof (munch_refl [(sp0 + 328, sp0 + 336); (COPY, COPY + len0)]%Z m3) as MUW. pose proof (wmono_refl usegs m3) as WMW.

      step. if_cases KZ; zify_cond KZ.
      +
        rewrite ?unsigned_lit in KZ by lia.
        assert (ES0 : od_s0 d = []) by (destruct (od_s0 d) as [|c l] eqn:E0; [reflexivity| exfalso; rewrite Elen0 in KZ; unfold zlength in KZ; cbn in KZ; lia]).
        step. step. zstep. replace (len0 + 64 + - len0) with 64 by lia. step. step. if_true.
        step. step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia| clear K2].

        step. step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        eapply (FIN m5 [] [] COPY len0); [exact MUW| exact WMW| assumption| | exact PA| rewrite ES0; reflexivity| rewrite ES0; reflexivity| unfold zlength; cbn [length]; lia| rewrite KZ; reflexivity].
        rewrite ES0. rewrite KZ in BDOC. cbn [Z.to_nat take to_bytes map] in BDOC. rewrite KZ. cbn [Z.to_nat]. exact BDOC.
      +
        rewrite ?unsigned_lit in KZ by lia.
        destruct DOCB as [Z0|(SRCB & EP0 & (b0 & Hb0 & Hb01 & Hb02))]; [exfalso; lia|].
        destruct b0 as [[b0i b0a] b0n]. pose proof (SEPC b0i b0a b0n ltac:(right; exact Hb0)) as SP0. cbn [blk_addr blk_size blk_id fst snd] in Hb01, Hb02, SP0.
        step. step. step. step.
        eapply evt_cut.
        { eapply memcpy_callZ with (src := to_bytes (od_s0 d)) (junk := take (Z.to_nat len0) junk2);
            [exact SRCB| rewrite to_bytes_length; rewrite Elen0; unfold zlength; lia| exact BDOC| clear - SP0 Hb01 Hb02 LEN0; lia| lia| lia| lia| assumption]. }
        cbv beta. intros ms' PO. unfold memcpy_postZ in PO.
        destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m4 & -> & MU4 & WM4 & MI4 & DST4 & SRC4).
        replace (ret_pc (Z_to_bv 64 0x2721c)) with (Z_to_bv 64 0x2721c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        clear MUW WMW.
        assert (MUW : munch [(sp0 + 328, sp0 + 336); (COPY, COPY + len0)]%Z m3 m4).
        { eapply munch_weaken; [| exact MU4]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
        pose proof WM4 as WMW.
        hide FIN. hide MUW. hide WMW. transport_after_call usegs m3 m4 MU4 WM4. unhide MUW. unhide WMW. unhide FIN.
        clear MU4 WM4.

        step. step. zstep. replace (len0 + 64 + - len0) with 64 by lia. step. step. if_true.
        step. step.
        if_cases K3; zify_cond K3.
        * rewrite ?unsigned_lit in K3 by lia.
          destruct (od_s0 d) as [|c0 [|c1 [|c2 r]]] eqn:ES0; try (rewrite Elen0 in K3; unfold zlength in K3; cbn [length] in K3; lia).

          do 6 step.
          inversion PRS0 as [|? ? R0 PR1]; subst. inversion PR1 as [|? ? R1 PR2]; subst. inversion PR2 as [|? ? R2 PR3]; subst.
          eapply evt_cut.
          { eapply (bom_spec) with (A := COPY) (c0 := c0) (c1 := c1) (c2 := c2); [assumption| | exact R0| exact R1| exact R2| lia| lia].
            destruct DST4 as [[_ HB] _]. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB. unfold to_bytes in HB. cbn [map] in HB.
            change (Z_to_bv 8 c0 :: Z_to_bv 8 c1 :: Z_to_bv 8 c2 :: map (Z_to_bv 8) r)
              with ([Z_to_bv 8 c0; Z_to_bv 8 c1; Z_to_bv 8 c2] ++ map (Z_to_bv 8) r) in HB.
            apply bytes_at_app in HB. exact (proj1 HB). }
          intros ms' PO. unfold bom_post in PO.
          destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & [(-> & -> & -> & ->)|(NZ & NM)]).
          --
            replace (ret_pc (Z_to_bv 64 0x272d0)) with (Z_to_bv 64 0x272d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
            step. if_true. zstep. step. if_cases K4; zify_cond K4; [clear K4| exfalso; rewrite ?unsigned_lit in K4 by lia; lia].
            zstep. zstep. step. step.
            rewrite (shiftr_small0 (zlength (239 :: 187 :: 191 :: r) + -3) 32) by (change (2^32) with 4294967296; unfold zlength in *; cbn [length] in *; lia).
            if_false.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
            eapply (FIN m5 [239; 187; 191] r (COPY + 3) _); [exact MUW| exact WMW| assumption| exact DST4| exact PA| apply OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P.Sj_h_arith.strip_bom_hit| reflexivity| reflexivity|].
            unfold zlength. cbn [length]. lia.
          --
            replace (ret_pc (Z_to_bv 64 0x272d0)) with (Z_to_bv 64 0x272d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
            step. rewrite NZ. step. step. zstep. step. step.
            rewrite (shiftr_small0 (zlength (c0 :: c1 :: c2 :: r)) 32) by (change (2^32) with 4294967296; unfold zlength in *; cbn [length] in *; lia).
            if_false.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
            eapply (FIN m5 [] (c0 :: c1 :: c2 :: r) COPY _); [exact MUW| exact WMW| assumption| exact DST4| exact PA| | reflexivity| unfold zlength; cbn [length]; lia| reflexivity].
            apply OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P.Sj_h_arith.strip_bom_miss. exact NM.
        *
          rewrite ?unsigned_lit in K3 by lia.
          step. step. step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
          eapply (FIN m5 [] (od_s0 d) COPY len0); [exact MUW| exact WMW| assumption| exact DST4| exact PA| | reflexivity| unfold zlength; cbn [length]; lia| exact Elen0].
          apply OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P.Sj_h_arith.strip_bom_short. rewrite Elen0 in K3. unfold zlength in K3. lia.
  Qed.
End Proofs.
End WithCeiling0.
