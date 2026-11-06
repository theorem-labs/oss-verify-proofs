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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel AtpModel OdModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Sj_h_arith Sj_h_create Sj_h_active Atp_h_defs Od_setup_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjStage1 SjStage1Out.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Sj_stage1_defs Sj_stage1 Atp_pid_s1z.
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

Definition setup_post (sp0 : Z) (gp s3 s4 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LBC : list block) (lo B : Z) (m : mem) (BUF COPY : Z) (bs : list Z)
    (psb pim pix poc pia : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (SB IMPL IDX OC IA code : Z) (idxs : list Z) (ws : list word)
                    (j0 j305 p12 p28 p50 : list byte) (nxt docv : word),
    ms' = MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 1024) (Z_to_bv 64 BUF) (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (blen bs)) s3 s4 (Z_to_bv 64 COPY) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x273ac) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo sp0 /\ rw_cells psegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, OD_IDX (blen bs)) :: (pim, IMPL, 96) :: (psb, SB, OD_SBUF (blen bs)) :: LBC) m'
    /\ lx_pres LBC (sp0 + 360) [LXW_SJ] m m' /\ lx_statics m' /\ sj_statics m' true
    /\ rw_cells psegs m' sp0 [CB 304 j0]
    /\ rw_cells psegs m' (sp0 + 304) [C1 (Z_to_bv 8 0); CB 7 j305; C8 (Z_to_bv 64 IMPL); C8 (Z_to_bv 64 (blen bs)); C8 (Z_to_bv 64 4294967295);
                                      C8 (Z_to_bv 64 1024); C8 (Z_to_bv 64 (blen bs)); C8 (Z_to_bv 64 SB)]
    /\ rw_cells psegs m' IMPL (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) (Z_to_bv 64 (Z.of_nat (length idxs))) p12 (Z_to_bv 64 IDX) nxt p28
                                            (Z_to_bv 64 (blen bs)) (Z_to_bv 64 1024) (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA)
                                            (Z_to_bv 64 BUF) (Z_to_bv 64 (blen bs)) docv)
    /\ u32arr psegs m' IDX ws /\ length ws = Z.to_nat (roundup64 (blen bs) + 9)
    /\ firstn (length idxs + 3) ws = map (Z_to_bv 64) (idxs ++ [blen bs; blen bs; 0])
    /\ wr_at psegs m' SB (OD_SBUF (blen bs))
    /\ rblock_range SB (OD_SBUF (blen bs)) /\ rblock_range IMPL 96 /\ rblock_range IDX (OD_IDX (blen bs))
    /\ 0 <= code < 64
    /\ (code = 0 -> S1OUT bs idxs /\ bytes_at psegs m' BUF (padded_bytes bs)).

Ltac readdr H e := lazymatch type of H with rw_cells _ _ ?a _ => replace a with e in H by lia end.

Lemma rw_cells_split_at1 : forall m A cs n, rw_cells psegs m A cs ->
  rw_cells psegs m A (firstn n cs) /\ rw_cells psegs m (A + Z.of_nat (cells_size (firstn n cs))) (skipn n cs).
Proof. intros m A cs n H. rewrite <- (firstn_skipn n cs) in H. apply Sj_stage1_kit.rw_cells_app in H. exact H. Qed.

Definition s1c_post (E : s1env) (code : Z) (out : list Z) (bf : bool) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m' : mem) (ws' : list word) (nxt' : word),
    ms' = MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) t0 t1 t2 (e_s0 E) (e_s1 E) (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7
                  (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
             (e_F E) (ret_pc (e_ra E)) (e_fc E) None m' (seg_rom psegs)
    /\ munch (s1_W E) (e_m0 E) m' /\ wmono psegs (e_m0 E) m' /\ mem_inv psegs m'
    /\ stk psegs m' (e_lo E) (bv_unsigned (e_sp E))
    /\ rw_cells psegs m' (e_THIS E) (parser_cells E (Z_to_bv 64 (Z.of_nat (length out))) nxt' (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_len E)))
    /\ u32arr psegs m' (e_IDX E) ws' /\ length ws' = e_cap E
    /\ firstn (length out + 3) ws' = map (Z_to_bv 64) (out ++ [e_len E; e_len E; 0%Z])
    /\ (bf = true -> bytes_at psegs m' (e_BUF E) (padded_bytes (e_bs E))).

Lemma s1c_of_s1 : forall E code out ms', s1_post E code out ms' -> s1c_post E code out true ms'.
Proof.
  intros E code out ms' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & ws' & nxt' & EQ & MU & WM & MI & ST & TH & _ & ARR & LWS & FN & BUFB).
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', ws', nxt'. repeat (split; [assumption|]). intros _. exact BUFB.
Qed.
Lemma s1c_of_s1z : forall E code out ms', s1z_post E code out ms' -> s1c_post E code out false ms'.
Proof.
  intros E code out ms' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & ws' & nxt' & EQ & MU & WM & MI & ST & TH & _ & ARR & LWS & FN).
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', ws', nxt'. repeat (split; [assumption|]). intros X. discriminate X.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  Lemma od_setup_cps : forall {R} (k : bptr -> bptr -> bptr -> bptr -> bptr -> M PState R) (Q : R -> PState -> machine_state -> Prop)
      (x1 gp t0 t1 t2 xs0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBC : list block) (sp0 lo B : Z) (init : bool) (errv : word)
      (BUF COPY : Z) (bs : list Z) (j0 j305 : list byte),
    RHEAP s LBC m -> rauxv_ok m B -> sp0 + 512 <= B -> B < 2^63 ->
    stk psegs m lo sp0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 + 512 - LX_FUZZ_STACK ->
    rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m ->
    lx_statics m -> sj_statics m init ->
    bytes_ok bs -> blen bs <= 1048512 -> 0 <= BUF < 2^63 ->
    (bs = [] \/ (bytes_at psegs m BUF (padded_bytes bs)
                 /\ exists b, In b LBC /\ blk_addr b <= BUF /\ BUF + blen bs + 64 <= blk_addr b + blk_size b)) ->
    rw_cells psegs m sp0 [CB 304 j0] ->
    rw_cells psegs m (sp0 + 304) [C1 (Z_to_bv 8 0); CB 7 j305; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 1024);
                                  C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    (forall psb pim pix poc pia s' ms',
        setup_post sp0 gp s3 s4 s6 s7 s8 s9 s10 s11 F fc s LBC lo B m BUF COPY bs psb pim pix poc pia s' ms' ->
        implM psegs (k psb pim pix poc pia) s' Q ms') ->
    implM psegs
      (mbind (newnt lops (OD_SBUF (blen bs))) (fun sb =>
       mbind (newnt lops 96) (fun im =>
       mbind (newnt lops (OD_IDX (blen bs))) (fun ix =>
       mbind (newnt lops 8192) (fun oc =>
       mbind (newnt lops 1024) (fun ia => k sb im ix oc ia))))))
      s Q
      (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 (Z_to_bv 64 BUF) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (blen bs)) s3 s4 (Z_to_bv 64 COPY) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x27318) fc None m (seg_rom psegs)).
  Proof.
    intros until j305.
    intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI LXS SJS BOK BLEN BUFR DOC LOW PA HK.
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 562956) by reflexivity. rewrite ELX in ERR.
    remember (blen bs) as L eqn:EL.
    assert (L0 : 0 <= L) by (subst L; unfold blen; lia).
    pose proof (od_sizes_small L ltac:(change (2^32) with 4294967296; lia)) as (SBR & IXR).
    pose proof (OD_SBUF_room L L0) as SBROOM.
    assert (SBU : OD_SBUF L < 4294967296).
    { unfold OD_SBUF. pose proof (roundup64_lt (5 * (L / 3) + 64)). assert (L / 3 <= L) by (apply Z.div_le_upper_bound; lia). lia. }
    assert (RUL : L <= roundup64 L < L + 64) by (split; [apply roundup64_ge| apply roundup64_lt]).
    assert (BLB : forall a, in_block LBC a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LBC (sp0 + 360) [LXW_SJ] a -> outside [(sp0, sp0 + 360)] a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(sp0, sp0 + 360)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof LXS as (_ & _ & GOT & _).
    unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG, MallocRep.wz in GOT.
    hide DOC.
    unfold implM. iprefix.

    hstep. step. step. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    rewrite (od_sbuf_size_eq L) by (change (2^32) with 4294967296; lia).

    destruct (rw_cells_split_at1 _ _ _ 2%nat PA) as [PA0 Q1]. cbn [firstn skipn cells_size csize Nat.add] in PA0, Q1.
    destruct (rw_cells_split_at1 _ _ _ 1%nat Q1) as [PIMPL PREST]. cbn [firstn skipn cells_size csize Nat.add] in PIMPL, PREST.
    clear PA Q1. readdr PIMPL (sp0 + 312). readdr PREST (sp0 + 320).
    assert (HEAP1 : RHEAP s LBC m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES1 : lx_pres LBC (sp0 + 360) [LXW_SJ] m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
    assert (OUTS : forall a, 0x74000 <= a < GLOBALS_TOP -> outside [(sp0, sp0 + 360)] a).
    { intros a Ha. unfold GLOBALS_TOP in Ha. cbn [outside]. clear - Ha GLO LO. lia. }
    pose proof (statics_munch _ _ _ rr_guard MU WM OUTS) as (LXSf & SJSf & _). pose proof (LXSf LXS) as LXS1. pose proof (SJSf _ SJS) as SJS1. clear LXSf SJSf.
    unhide DOC.
    assert (DOC1 : bs = [] \/ (bytes_at psegs m1 BUF (padded_bytes bs) /\ exists b, In b LBC /\ blk_addr b <= BUF /\ BUF + L + 64 <= blk_addr b + blk_size b)).
    { destruct DOC as [E|(BB & b & Hb & H1 & H2)]; [left; exact E| right]. split; [| exists b; auto].
      eapply bytes_at_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact BB|]. intros a Ha. rewrite padded_bytes_blen in Ha. rewrite <- EL in Ha.
      pose proof (BLB a ltac:(exists b; split; [exact Hb| lia])). cbn [outside]. split; [lia| exact I]. }
    clear DOC MU WM.
    ihere. to_implM.
    eapply implM_bind.
    { eapply (opnew_arr_nt_proof HM) with (B := B) (lo := lo);
        [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| rewrite ELX; eassumption| assumption| lia| lia]. }
    cbv beta. intros psb st2 ms2 PO. unfold opnew_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & SB & junk2
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HP2 & FA2 & SO2 & BRSB & HEAP2 & BLKSB).
    replace (ret_pc (Z_to_bv 64 0x27354)) with (Z_to_bv 64 0x27354) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ELX in ERR2.
    pose proof BRSB as (SB0 & _ & _ & SBC & SBS). unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in SBC.

    pose proof (agree_of_heap_pres _ _ _ _ HP2) as AG2.
    assert (FRH : forall a, sp0 <= a < sp0 + 512 -> rclient_addr LBC sp0 a) by (intros a Ha; left; lia).
    apply (rw_cells_agree _ _ _ _ _ AG2) in PA0; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in PIMPL; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in PREST; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in LOW; [| intros a Ha; cbn in Ha; apply FRH; lia].
    assert (PRES2 : lx_pres LBC (sp0 + 360) [LXW_SJ] m m2).
    { eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP2| lia| intros b Hb; exact Hb]. }
    pose proof (statics_heap _ _ _ _ HP2 ltac:(unfold GLOBALS_TOP; lia)) as (LXSf & SJSf & _).
    pose proof (SJSf _ SJS1) as SJS2. pose proof (LXSf LXS1) as LXS2. clear LXSf SJSf.
    assert (DOC2 : bs = [] \/ (bytes_at psegs m2 BUF (padded_bytes bs) /\ exists b, In b LBC /\ blk_addr b <= BUF /\ BUF + L + 64 <= blk_addr b + blk_size b)).
    { destruct DOC1 as [E|(BB & b & Hb & H1 & H2)]; [left; exact E| right]. split; [| exists b; auto].
      eapply bytes_at_agree; [exact AG2| exact BB|]. intros a Ha. rewrite padded_bytes_blen in Ha. rewrite <- EL in Ha.
      right; right. exists b. split; [exact Hb| lia]. }
    clear AG2 HP2 HEAP1 AUX1 PRES1 SJS1 LXS1 DOC1 GOT.
    pose proof (munch_refl [(sp0, sp0 + 360)]%Z m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    assert (BLB2 : forall a, in_block LBC a -> a < alloc_ceiling /\ ~ (SB <= a < SB + OD_SBUF L)).
    { intros a (b & Hb & Hr). split; [apply BLB; exists b; auto|]. destruct b as [[bi ba] bn].
      pose proof (LH_head_sep _ _ _ _ _ _ bi ba bn HEAP2 Hb) as SP. cbn [blk_addr blk_size fst snd] in Hr. lia. }
    hide DOC2.
    unfold implM. iprefix.

    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    eapply evt_cut.
    { eapply (getact_spec) with (lo := lo) (init := init); [eassumption| unfold GLOBALS_TOP; lia| lia| lia| assumption| ].
      pose proof (statics_munch _ _ _ rr_guard MU WM OUTS) as (_ & SJSf & _). exact (SJSf _ SJS2). }
    intros ms' PO. unfold getact_post in PO.
    destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m4 & -> & MU4 & WM4 & MI4 & ST4 & SJS4).
    unfold SJ_STATICS_LO, SJ_STATICS_HI in MU4.
    replace (ret_pc (Z_to_bv 64 0x2735c)) with (Z_to_bv 64 0x2735c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (HEAP4 : RHEAP st2 ((psb, SB, OD_SBUF L) :: LBC) m4).
    { eapply LH_frame; [eapply LH_frame; [exact HEAP2| exact MU| exact WM|]| exact MU4| exact WM4|].
      - constructor; [apply W_ok_stack; cbn; lia| constructor].
      - constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
        right; left. cbn [fst snd]. unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]| exact MU4| exact WM4|].
      - constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      - constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES4 : lx_pres LBC (sp0 + 360) [LXW_SJ] m m4).
    { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_trans; eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI| exact MU4| exact WM4|].
      intros a Ha [HX HC]. unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI in HX. cbn [rin_ivs fst snd] in HX. cbn [outside].
      split; [| split; [lia| exact I]]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    assert (LXS4 : lx_statics m4).
    { pose proof (statics_munch _ _ _ rr_guard MU WM OUTS) as (LXSf & _). pose proof (LXSf LXS2) as LXS3.
      eapply lx_statics_agree; [exact (agree_on_of_munch _ _ _ MU4 WM4)| | exact LXS3]. intros a Ha.
      pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_GOT_TABS, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
      cbn [outside]. clear - Ha GLO LO. lia. }
    unhide DOC2.
    assert (DOC4 : bs = [] \/ (bytes_at psegs m4 BUF (padded_bytes bs) /\ exists b, In b LBC /\ blk_addr b <= BUF /\ BUF + L + 64 <= blk_addr b + blk_size b)).
    { destruct DOC2 as [E|(BB & b & Hb & H1 & H2)]; [left; exact E| right]. split; [| exists b; auto].
      eapply bytes_at_agree; [exact (agree_on_of_munch _ _ _ MU4 WM4)|
                              eapply bytes_at_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact BB|]|].
      - intros a Ha. rewrite padded_bytes_blen in Ha. rewrite <- EL in Ha.
        pose proof (BLB a ltac:(exists b; split; [exact Hb| lia])). cbn [outside]. split; [lia| exact I].
      - intros a Ha. rewrite padded_bytes_blen in Ha. rewrite <- EL in Ha.
        pose proof (BLB a ltac:(exists b; split; [exact Hb| lia])).
        pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & _ & BS). cbn [outside]. split; [lia| split; [lia| exact I]]. }
    clear DOC2. hide DOC4.
    hide MU. hide WM. transport_after_call psegs m3 m4 MU4 WM4. unhide MU. unhide WM.
    clear MU WM MU4 WM4 PRES2 HEAP2 AUX2 SJS2 LXS2.
    pose proof LXS4 as (_ & _ & GOT & VT24 & VTD & _).
    unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG, MallocRep.wz in GOT. unfold SJ_IMPL_VT24, SJ_CREATE_DPI, MallocRep.wz in VT24. unfold SJ_DPI_VPTR, MallocRep.wz in VTD.
    pose proof (munch_refl [(sp0, sp0 + 360)]%Z m4) as MU. pose proof (wmono_refl psegs m4) as WM.
    pose proof SJS4 as SJC. unfold sj_statics, sj_cells, SJ_STATICS_LO, SJ_FALLBACK, SJ_FALLBACK_VPTR, SJ_STR_NAME, SJ_STR_DESC, MallocRep.wz in SJC.

    unfold SJ_ACTIVE_IMPL.
    do 10 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4' end.
    assert (HEAP4' : RHEAP st2 ((psb, SB, OD_SBUF L) :: LBC) m4').
    { eapply LH_frame; [exact HEAP4| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX4' : rauxv_ok m4' B).
    { eapply rauxv_ok_frame; [exact AUX4| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    ihere. to_implM.
    eapply (create_cps HM) with (B := B) (lo := lo) (DST := sp0 + 312) (cap := L);
      [exact HEAP4'| exact AUX4'| lia| eassumption| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| rewrite ELX; eassumption| assumption| lia| lia| lia
      | change (2^26) with 67108864; lia| exact GOT| exact VTD| exact PIMPL|].
    intros pim pix poc pia s5' ms5 PO. unfold hpost in PO.
    destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m5
                    & -> & MI5 & ST5 & (errv5 & ERR5) & AUX5 & FA5 & SO5 & RR).
    unfold create_R in RR.
    destruct RR as (IMPL & IDX & OC & IA & ws & joc & jia & p12 & p28 & p50 & -> & HEAP5 & PRES45 & DSTC & THISC & ARR & LWS & BLKOC & BLKIA & BRIM & BRIX & BROC & BRIA).
    replace (ret_pc (Z_to_bv 64 0x27384)) with (Z_to_bv 64 0x27384) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ELX in ERR5.
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES45) as AG.
    assert (FRCL : forall a, sp0 <= a < sp0 + 512 -> ~ (sp0 + 312 <= a < sp0 + 320) -> lx_client ((psb, SB, OD_SBUF L) :: LBC) sp0 [(sp0 + 312, sp0 + 312 + 8)] a).
    { intros a Ha N1. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG) in PA0; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in PREST; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in LOW; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in BLKSB;
      [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [cbn [rin_ivs fst snd]; clear - Ha SBC CEIL LO SBR; lia|
           right; left; exists (psb, SB, OD_SBUF L); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; clear - Ha SBR; lia]]].
    assert (WRSB : wr_at psegs m5 SB (OD_SBUF L)).
    { destruct BLKSB as [_ W]. replace (Z.of_nat (cells_size [CB (Z.to_nat (OD_SBUF L)) junk2])) with (OD_SBUF L) in W by (cbn [cells_size csize]; lia). exact W. }
    clear BLKSB.
    assert (STCL : forall a, 0x74000 <= a < 0xab000 -> ~ ralloc_static a -> lx_client ((psb, SB, OD_SBUF L) :: LBC) sp0 [(sp0 + 312, sp0 + 312 + 8)] a).
    { intros a Ha NS. split; [cbn [rin_ivs fst snd]; clear - Ha GLO LO; lia| right; right; split; assumption]. }
    assert (LXS5 : lx_statics m5).
    { eapply lx_statics_agree; [exact AG| | exact LXS4]. intros a Ha. pose proof (lxs_addr_lt a Ha) as [R1 R2]. unfold GLOBALS_TOP in R1. apply STCL; assumption. }
    assert (SJS5 : sj_statics m5 true).
    { eapply sj_statics_agree; [exact AG| | exact SJS4]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [R1 R2]. unfold GLOBALS_TOP in R1. apply STCL; assumption. }
    unhide DOC4.
    assert (DOC5 : bs = [] \/ (bytes_at psegs m5 BUF (padded_bytes bs) /\ exists b, In b LBC /\ blk_addr b <= BUF /\ BUF + L + 64 <= blk_addr b + blk_size b)).
    { destruct DOC4 as [E|(BB & b & Hb & H1 & H2)]; [left; exact E| right]. split; [| exists b; auto].
      eapply bytes_at_agree; [exact AG| exact BB|]. intros a Ha. rewrite padded_bytes_blen in Ha. rewrite <- EL in Ha.
      pose proof (BLB a ltac:(exists b; split; [exact Hb| lia])).
      split; [cbn [rin_ivs fst snd]; lia| right; left; exists b; split; [right; exact Hb| lia]]. }
    clear DOC4.
    assert (PRES5 : lx_pres LBC (sp0 + 360) [LXW_SJ] m m5).
    { eapply lx_pres_trans; [exact PRES4|]. eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]|].
      eapply (lx_pres_sub LBC (sp0 + 360) _ _ _ _ _ _ PRES45); [lia| intros b0 Hb0; right; exact Hb0|].
      intros a Ha NX. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; specialize (BLB a IB); lia| lia]. }
    clear AG PRES45 PRES4 HEAP4 HEAP4' AUX4 AUX4' MU WM LXS4 SJS4 SJC GOT VT24 VTD FRCL STCL PIMPL.
    pose proof BRIM as (IM0 & _ & _ & IMC & IMS). pose proof BRIX as (IX0 & _ & _ & IXC & IXS).
    unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in IMC, IXC.
    pose proof LXS5 as (_ & _ & _ & _ & VTD & _). unfold SJ_DPI_VPTR, MallocRep.wz in VTD.
    unfold SJ_DPI_PARSE, SJ_DPI_STAGE1, SJ_DPI_STAGE2, SJ_DPI_STAGE2_NEXT, SJ_DPI_PARSE_STRING, SJ_DPI_PARSE_WOBBLY, SJ_DPI_SET_CAPACITY, SJ_DPI_SET_MAX_DEPTH, SJ_DPI_DTOR, SJ_DPI_DTOR_DEL in VTD.
    unfold impl_cells16, SJ_DPI_VPTR in THISC.
    pose proof (munch_refl [(sp0, sp0 + 360)]%Z m5) as MU. pose proof (wmono_refl psegs m5) as WM.
    hide DOC5. hide BLKOC. hide BLKIA.
    unfold implM. iprefix.

    step. if_false.
    step. step. step. hstep. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.

    pose proof (rw_cells_join _ _ _ _ _ PA0 DSTC ltac:(cbn [cells_size csize Nat.add]; lia)) as PJ1. cbn [app] in PJ1.
    pose proof (rw_cells_join _ _ _ _ _ PJ1 PREST ltac:(cbn [cells_size csize Nat.add]; lia)) as PA. cbn [app] in PA.
    clear PJ1 PA0 DSTC PREST.
    assert (HEAP6 : RHEAP s5' ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 L + 9)) :: (pim, IMPL, 96) :: (psb, SB, OD_SBUF L) :: LBC) m6).
    { eapply LH_frame; [exact HEAP5| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX6 : rauxv_ok m6 B).
    { eapply rauxv_ok_frame; [exact AUX5| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES6 : lx_pres LBC (sp0 + 360) [LXW_SJ] m m6).
    { eapply lx_pres_trans; [exact PRES5|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    pose proof (statics_munch _ _ _ rr_guard MU WM OUTS) as (LXSf & SJSf & _). pose proof (LXSf LXS5) as LXS6. pose proof (SJSf _ SJS5) as SJS6. clear LXSf SJSf.
    unhide DOC5.
    assert (DOC6 : bs = [] \/ (bytes_at psegs m6 BUF (padded_bytes bs) /\ exists b, In b LBC /\ blk_addr b <= BUF /\ BUF + L + 64 <= blk_addr b + blk_size b)).
    { destruct DOC5 as [E|(BB & b & Hb & H1 & H2)]; [left; exact E| right]. split; [| exists b; auto].
      eapply bytes_at_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact BB|]. intros a Ha. rewrite padded_bytes_blen in Ha. rewrite <- EL in Ha.
      pose proof (BLB a ltac:(exists b; split; [exact Hb| lia])). cbn [outside]. split; [lia| exact I]. }
    clear DOC5 HEAP5 AUX5 PRES5 LXS5 SJS5 MU WM VTD.

    pose proof (RHEAP_pull _ [(pia, IA, 1024); (poc, OC, 8192); (pix, IDX, 4 * (roundup64 L + 9))] _ _ _ HEAP6) as HEAPIM. cbn [app] in HEAPIM.
    pose proof (RHEAP_pull _ [(pia, IA, 1024); (poc, OC, 8192)] _ _ _ HEAP6) as HEAPIX. cbn [app] in HEAPIX.
    pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPIM ltac:(do 2 right; left; reflexivity)) as D_IM_IX.
    assert (LWS' : Z.of_nat (length ws) = roundup64 L + 9) by (rewrite LWS; lia).

    set (mid1 := [CB 4 p28; C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 1024); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 p50; C8 (Z_to_bv 64 OC); C8 (Z_to_bv 64 IA)]).
    assert (WF1 : cells_wf mid1).
    { destruct THISC as [[Hwf _] _]. cbn [cells_wf] in Hwf. subst mid1. cbn [cells_wf].
      destruct Hwf as (_ & _ & _ & _ & _ & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & _). repeat split; assumption. }
    pose proof (rw_cells_merge psegs m6 IMPL [C8 (Z_to_bv 64 476392); C4 (Z_to_bv 64 0); CB 4 p12; C8 (Z_to_bv 64 IDX); C4 (Z_to_bv 64 0)] mid1
                  [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] THISC) as TH1.
    pose proof (rw_cells_merge psegs m6 IMPL ([C8 (Z_to_bv 64 476392); C4 (Z_to_bv 64 0); CB 4 p12; C8 (Z_to_bv 64 IDX); C4 (Z_to_bv 64 0)] ++ [CB (cells_size mid1) (cells_bytes mid1); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
                  [C8 (Z_to_bv 64 0)] [] TH1) as TH2.
    clear TH1. cbn [app] in TH2. change (cells_size mid1) with 44%nat in TH2. change (cells_size [C8 (Z_to_bv 64 0)]) with 8%nat in TH2.
    set (MID := cells_bytes mid1) in TH2. set (DJ8 := cells_bytes [C8 (Z_to_bv 64 0)]) in TH2.
    set (E := mkS1Env (Z_to_bv 64 160684) (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) (Z_to_bv 64 1024) (Z_to_bv 64 BUF)
                      (Z_to_bv 64 (blen bs)) s3 s4 (Z_to_bv 64 COPY) s6 s7 s8 s9 s10 s11 F fc lo IMPL BUF IDX bs (length ws) (Z_to_bv 64 476392) p12 MID DJ8 m6).
    assert (TH0R : 0 <= IMPL /\ IMPL + 96 <= lo) by (clear - IM0 IMC CEIL; lia).
    assert (IX0R : 0 <= IDX /\ IDX + 4 * Z.of_nat (length ws) <= lo) by (rewrite LWS'; clear - IX0 IXC CEIL; lia).
    rewrite EL.
    eapply (evt_cut psegs (fun ms' => exists code idxs bf, s1c_post E code idxs bf ms' /\ 0 <= code < 64 /\ (code = 0 -> S1OUT bs idxs /\ bf = true))).
    { destruct DOC6 as [ENIL|(BUFB & b & Hb & Hb1 & Hb2)].
      -
        assert (OKZ : env_okz E).
        { unfold E. constructor; cbn [e_bs e_lo e_sp e_THIS e_IDX e_BUF e_cap]; unfold S1_LEN_MAX, S1_GTOP, S1_STACK; (rewrite ?unsigned_lit by lia); try assumption.
          all: clear - GLO LO TH0R IX0R LWS' RUL L0 D_IM_IX; lia. }
        eapply evt_mono.
        { eapply evt_eq; [| eapply (s1z_spec E OKZ)]; [cbv delta [mkR E e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_F e_fc e_m0 e_THIS e_BUF e_bs S1_ENTRY]; reflexivity | ..].
          - cbn [e_m0 E]. assumption.
          - cbn [e_m0 e_lo e_sp E]. rewrite unsigned_lit by lia. eassumption.
          - cbn [e_m0 e_THIS E]. unfold parser_cells. cbn [e_vptr e_p12 e_IDX e_mid e_docj E]. exact TH2.
          - cbn [e_m0 e_IDX E]. exact ARR.
          - reflexivity. }
        intros ms' PO. exists 13, [], false. split; [apply s1c_of_s1z; exact PO|]. split; [lia| intros X; discriminate X].
      - assert (OK : env_ok E).
        { destruct b as [[bi ba] bn].
          pose proof (LH_head_sep _ _ _ _ _ _ bi ba bn HEAPIM ltac:(do 4 right; exact Hb)) as D_IM_B.
          pose proof (LH_head_sep _ _ _ _ _ _ bi ba bn HEAPIX ltac:(do 4 right; exact Hb)) as D_IX_B.
          pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC.
          cbn [blk_addr blk_size fst snd] in Hb1, Hb2, BC.
          unfold E. constructor; cbn [e_bs e_lo e_sp e_THIS e_IDX e_BUF e_cap]; unfold S1_LEN_MAX, S1_GTOP, S1_STACK; (rewrite ?unsigned_lit by lia); try assumption.
          all: rewrite <- ?EL; clear - GLO LO TH0R IX0R LWS' RUL L0 D_IM_IX D_IM_B D_IX_B Hb1 Hb2 BC CEIL BUFR BLEN; lia. }
        eapply evt_mono.
        { eapply evt_eq; [| eapply (stage1_spec E OK)]; [cbv delta [mkR E e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_F e_fc e_m0 e_THIS e_BUF e_bs S1_ENTRY]; reflexivity | ..].
          - cbn [e_m0 E]. assumption.
          - cbn [e_m0 e_lo e_sp E]. rewrite unsigned_lit by lia. eassumption.
          - cbn [e_m0 e_THIS E]. unfold parser_cells. cbn [e_vptr e_p12 e_IDX e_mid e_docj E]. exact TH2.
          - cbn [e_m0 e_IDX E]. exact ARR.
          - reflexivity.
          - cbn [e_m0 e_BUF e_bs E]. exact BUFB. }
        cbn [e_bs E].
        intros ms' PO. exists (fst (stage1 bs)), (snd (stage1 bs)), true. split; [apply s1c_of_s1; exact PO|]. split; [apply stage1_code_range|].
        intros C0. split; [apply stage1_success_S1OUT; exact C0| reflexivity]. }
    intros ms' (code & idxs & bf & PO & CR & CS). unfold s1c_post in PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m7 & ws' & nxt' & -> & MU1 & WM1 & MI7 & ST7
                    & TH3 & ARR2 & LWS2 & FIRSTN & BUFB2).
    unfold s1_W_g, parser_cells in *. cbn [E e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_F e_fc e_m0 e_lo e_THIS e_BUF e_IDX e_bs e_cap
                                           e_vptr e_p12 e_mid e_docj] in *.
    rewrite (unsigned_lit sp0) in MU1, ST7 by lia.
    unfold Sj_stage1_kit.wz in TH3.

    subst MID DJ8.
    pose proof (rw_cells_unmerge m7 IMPL ([C8 (Z_to_bv 64 476392); C4 (Z_to_bv 64 (Z.of_nat (length idxs))); CB 4 p12; C8 (Z_to_bv 64 IDX); C4 nxt'] ++ [CB 44 (cells_bytes mid1); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (blen bs))])
                  [C8 (Z_to_bv 64 0)] [] TH3 ltac:(cbn; auto)) as TH4.
    cbn [app] in TH4.
    pose proof (rw_cells_unmerge m7 IMPL [C8 (Z_to_bv 64 476392); C4 (Z_to_bv 64 (Z.of_nat (length idxs))); CB 4 p12; C8 (Z_to_bv 64 IDX); C4 nxt'] mid1
                  [C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (blen bs)); C8 (Z_to_bv 64 0)] TH4 WF1) as TH5.
    subst mid1. cbn [app] in TH5. clear TH3 TH4 TH2 THISC ARR WF1.
    assert (HEAP7 : RHEAP s5' ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 L + 9)) :: (pim, IMPL, 96) :: (psb, SB, OD_SBUF L) :: LBC) m7).
    { eapply LH_frame; [exact HEAP6| exact MU1| exact WM1|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [eapply (W_ok_block _ (pim, IMPL, 96)); [do 3 right; left; reflexivity| cbn; lia| cbn; lia]|].
      constructor; [eapply (W_ok_block _ (pix, IDX, 4 * (roundup64 L + 9))); [do 2 right; left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX7 : rauxv_ok m7 B).
    { eapply rauxv_ok_frame; [exact AUX6| exact MU1| exact WM1|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES7 : lx_pres LBC (sp0 + 360) [LXW_SJ] m m7).
    { eapply lx_pres_trans; [exact PRES6|]. eapply lx_pres_of_munch; [exact MU1| exact WM1|].
      intros a Ha [HX HC]. cbn [outside]. split; [| split; [| split; [| exact I]]].
      - destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
      - destruct HC as [HC|[HC|HC]]; [lia| | lia]. intros IN. apply (LH_head_disj _ _ _ _ _ _ HEAPIM a); [| exact IN]. eapply in_block_incl; [| exact HC]. intros b Hb. do 4 right. exact Hb.
      - destruct HC as [HC|[HC|HC]]; [lia| | lia]. intros IN. apply (LH_head_disj _ _ _ _ _ _ HEAPIX a); [| lia]. eapply in_block_incl; [| exact HC]. intros b Hb. do 4 right. exact Hb. }
    assert (OUT1 : forall a, 0x74000 <= a < GLOBALS_TOP -> outside [(sp0 + -416, sp0); (IMPL, IMPL + 96); (IDX, IDX + 4 * Z.of_nat (length ws))] a).
    { intros a Ha. unfold GLOBALS_TOP in Ha. cbn [outside]. rewrite LWS'. clear - Ha GLO LO IMS IXS IM0 IX0 RUL L0. unfold OD_IDX in IXS. lia. }
    pose proof (statics_munch _ _ _ rr_guard MU1 WM1 OUT1) as (LXSf & SJSf & _). pose proof (LXSf LXS6) as LXS7. pose proof (SJSf _ SJS6) as SJS7. clear LXSf SJSf.
    pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
    apply (rw_cells_agree _ _ _ _ _ AG1) in PA; [| intros a Ha; cbn in Ha; cbn [outside]; clear - Ha TH0R IX0R LO; lia].
    apply (rw_cells_agree _ _ _ _ _ AG1) in LOW; [| intros a Ha; cbn in Ha; cbn [outside]; clear - Ha TH0R IX0R LO; lia].
    apply (rw_cells_agree _ _ _ _ _ AG1) in ERR5; [| intros a Ha; cbn in Ha; cbn [outside]; pose proof (OUT1 a ltac:(unfold GLOBALS_TOP; lia)) as OO; cbn [outside] in OO; exact OO].
    apply (wr_at_transport psegs m6 m7 _ _) in WRSB; [| exact WM1].
    clear AG1 MU1 WM1 HEAP6 AUX6 PRES6 LXS6 SJS6 DOC6 HEAPIM HEAPIX.
    replace (ret_pc (Z_to_bv 64 160684)) with (Z_to_bv 64 160684) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    ihere. to_implM. apply HK.
    unfold setup_post. rewrite <- EL. do 15 eexists. exists m7, errv5, SB, IMPL, IDX, OC, IA, code, idxs, ws'. do 5 eexists. exists nxt'. eexists.
    split; [cbv delta [mkR]; rewrite EL; reflexivity|].
    split; [exact MI7|]. split; [exact ST7|]. split; [rewrite ELX; exact ERR5|]. split; [exact AUX7|]. split; [congruence|]. split; [congruence|].
    split; [exact HEAP7|]. split; [exact PRES7|]. split; [exact LXS7|]. split; [exact SJS7|].
    split; [exact LOW|]. split; [exact PA|].
    split; [unfold impl_cells16, SJ_DPI_VPTR; rewrite EL in TH5; rewrite EL; exact TH5|].
    split; [exact ARR2|]. split; [rewrite LWS2; exact LWS|]. split; [rewrite EL; exact FIRSTN|]. split; [exact WRSB|].
    split; [exact BRSB|]. split; [exact BRIM|]. split; [exact BRIX|]. split; [exact CR|].
    intros C0. destruct (CS C0) as [SO BT]. split; [exact SO| exact (BUFB2 BT)].
  Qed.
End Proofs.
End WithCeiling0.
