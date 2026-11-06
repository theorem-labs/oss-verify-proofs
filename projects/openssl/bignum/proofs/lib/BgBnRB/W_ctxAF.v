(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require W_ctx.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA UnwindA EdgesA AsStruct RtCallA W_cryptoA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import CtxKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2258576 => 2
  | 2258580 => 1
  | 2258584 => 2
  | 2258660 => 2
  | 2258912 => 1
  | 2258916 => 1
  | 2258920 => 2
  | 2259040 => 2
  | 2259044 => 1
  | 2259048 => 1
  | 2259052 => 1
  | 2259056 => 2
  | 2259060 => 2
  | 2259064 => 1
  | 2259068 => 2
  | 2259156 => 2
  | 2259460 => 1
  | 2259464 => 2
  | 2259512 => 2
  | 2259600 => 2
  | 2259604 => 1
  | 2259608 => 1
  | 2259612 => 1
  | 2259616 => 2
  | 2259620 => 2
  | 2259624 => 1
  | 2259628 => 2
  | 2259764 => 2
  | 2259768 => 1
  | 2259772 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Definition BN_CTX_START : Z := 0x227654.
Definition BN_CTX_START_STACK : Z := 112 + CRYPTO_MALLOC_ARRAY_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_cs_marr := (E_BN_CTX_start_2275d0 : uk_call BN_CTX_START 0x2277b8 CRYPTO_MALLOC_ARRAY).
Local Notation E_cs_free := (E_BN_CTX_start_227630 : uk_call BN_CTX_START 0x227818 BnRepDefs.CRYPTO_FREE).

Lemma BN_CTX_start_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo BN_CTX_START_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_CTX_START (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
  implA (BN_CTX_start (tree_ops bptr) ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
              (fun _ _ OW' PL' _ => PL' = PL /\ forall q A n, In (q, A, n) OW -> In (q, A, n) OW'))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_CTX_START) fc None m (seg_rom bgbsegs)).
Proof.
  intros until qc. intros (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR) UW CTX -> EC ->.
  unfold BN_CTX_START_STACK, CRYPTO_MALLOC_ARRAY_STACK, CRYPTO_MALLOC_STACK, RT_STACK, BN_CTX_START, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof WFS as (EL & BOK & EONE & (CE1 & CE2 & CE3 & CE4 & CE5 & CE6 & CE7 & CE8)).
  destruct (lib_state_cx_open [] ls m OW PL EA LS) as (Hs & IX & CV & LSC).
  apply (cx_view_some _ _ _ _ _ _ _ _ EC) in CV. destruct CV as (BC & LHs & CX & STK & HItems & HLinks). change BN_CTX_SZ with 72 in BC.
  pose proof (AH_range _ _ _ _ _ _ _ HEAP BC) as (CA0 & CA16 & _ & CAC & CAI).
  set (c := st_ctx ls) in *.
  unfold ctx_cells in CX. rewrite CE1, CE2 in CX. change (Z.of_nat 0) with 0 in CX. change (Z.b2z false) with 0 in CX.
  assert (INC : In (qc, ac, 72) (OW ++ LB)) by (apply in_or_app; left; exact BC).
  pose proof (AH_acc_in _ _ _ _ (qc, ac, 72) (ac) 72 HEAP INC ltac:(cbn; lia) ltac:(cbn; lia)) as ACC.
  assert (AL : ac mod 8 = 0) by (clear - CA16; Z.div_mod_to_equations; lia).
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  unfold BN_CTX_start, bbind, bgetctx, bret, bunr, bmalloc, bfree_opt, bsetctx, bfree.
  cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd]. fold c.
  rewrite CE1, CE2. cbn [Nat.eqb negb orb].
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (ac, ac + 72)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 112, bv_unsigned sp); (ac, ac + 72)]).
  { pose proof (AH_offsh _ _ _ _ (qc, ac, 72) HEAP INC) as O. cbn [blk_addr blk_size fst snd] in O.
    cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
  apply implA_from_evt.
  carve_frame 112%nat ST.
  apply (rw_cells_split_CB bgbsegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 15 (ub; step). do 3 (ub; step). do 3 (ub; step). ub; shl. ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
  ub; step. if_false.
  do 3 (ub; step). ub; shl. ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
  ub; step. if_true.

  assert (SSZ : gx_ssize c = 0%nat \/ gx_ssize c = 32%nat) by (unfold BG_DEPTH in CE8; lia).
  assert (DEP : (length (gx_frames c) <= 32)%nat) by (unfold BG_DEPTH in CE8; destruct CE8 as [(_ & -> & _)|(_ & _ & ?)]; cbn; lia).
  assert (U48 : (gx_used c <= 48)%nat) by (unfold BN_CTX_POOL_SIZE in CE4; lia).
  do 3 (ub; step). ub; shl. ub; chk0.
  do 3 (ub; step). ub; shl.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (gx_used c))) by lia. ub; chk0.
  do 3 (ub; step). ub; shl.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (length (gx_frames c)))) by lia. ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (gx_ssize c))) by lia.
  do 2 (ub; step). rewrite (unsigned_lit (ac + 32)) by (unfold BnHeapA.ACEIL in *; lia).
  ub; step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia.
  -
    replace (length (gx_frames c) =? gx_ssize c)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    unfold stack_rep in STK. destruct (gx_indexes c) as [q|] eqn:EI; [|exfalso; destruct STK as (_ & E1 & E2); rewrite E2 in KD; cbn in KD; lia].
    destruct STK as (HinI & SZ32 & stale & LEN & ARR). change FRAMES_SZ with 128 in HinI. unfold BN_CTX_START_FRAMES in SZ32, LEN.
    pose proof (AH_range _ _ _ _ _ _ _ HEAP HinI) as (IA0 & IA16 & _ & IAC & IAI).
    assert (NEI : qc <> q) by (eapply ids_pl_m; [exact IDS| eapply in_pl_ids_ctx; exact EC| apply idx_in_m; exact EI]).
    pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HinI NEI) as CXI.
    assert (INI : In (q, IX, 128) (OW ++ LB)) by (apply in_or_app; left; exact HinI).
    pose proof (AH_acc_in _ _ _ _ (q, IX, 128) IX 128 HEAP INI ltac:(cbn; lia) ltac:(cbn; lia)) as ACCI.
    assert (ALI : IX mod 8 = 0) by (clear - IA16; Z.div_mod_to_equations; lia).
    pose proof (AH_offsh _ _ _ _ (q, IX, 128) HEAP INI) as OI. cbn [blk_addr blk_size fst snd] in OI. unfold SHLO, SHHI in OI.
    remember (map (fun k : nat => wz (Z.of_nat k)) (gx_frames c) ++ stale) as ws eqn:Ews.
    assert (LWS : length ws = 32%nat) by (subst ws; rewrite length_app, length_map; exact LEN).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of MU with munch ?W0 _ _ =>
        apply (u32arr_transport bgbsegs W0 m mx IX ws) in ARR; [| exact MU| exact WM| cbn [disjoint_from]; rewrite LWS; lia] end end.
    apply (munch_weaken _ [(bv_unsigned sp + -112, bv_unsigned sp); (ac, ac + 72); (IX, IX + 128)]%Z) in MU;
      [| intros x Hx; cbn [outside] in *; tauto].
    clear OFF.
    assert (OFF : offshW [(bv_unsigned sp + -112, bv_unsigned sp); (ac, ac + 72); (IX, IX + 128)]).
    { pose proof (AH_offsh _ _ _ _ (qc, ac, 72) HEAP INC) as O. cbn [blk_addr blk_size fst snd] in O.
      cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
    ub; step.
    ub; shl. ub; chk0. ub; shl. ub; step. ub; chk0.
    ub; step. unfold MallocRep.wz at 1. rewrite (zx32_small (Z.of_nat (length (gx_frames c)))) by lia.
    do 2 (ub; step). rewrite ?(unsigned_lit (Z.of_nat (length (gx_frames c)))) by lia.
    replace (Z.shiftl (Z.of_nat (length (gx_frames c))) 2) with (4 * Z.of_nat (length (gx_frames c))) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ub; step. ub; step.
    do 2 (ub; step). ub; shl. ub; chk0.
    pose proof (u32arr_store_ok bgbsegs _ IX ws (Z.of_nat (length (gx_frames c))) (wa (IX + 4 * Z.of_nat (length (gx_frames c)))) ARR ltac:(lia) eq_refl) as SOKW.
    ub; step.
    pose proof (u32arr_write bgbsegs _ IX ws (Z.of_nat (length (gx_frames c))) (Z_to_bv 64 (Z.of_nat (gx_used c))) ARR ltac:(lia)) as ARR2.
    store_done.
    ub; step. do 13 (ub; step). release_frame FR ST (bv_unsigned sp). ub; step. ub; step.
    apply evt_done. apply implA_ret.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mF end.
    set (c' := mkGx (gx_items c) (gx_current c) (gx_pused c) (Some q) (gx_frames c ++ [gx_used c]) (gx_ssize c) (gx_used c) 0%nat false).
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -112, bv_unsigned sp); (ac, ac + 72); (IX, IX + 128)]).
    { constructor; [left; cbn; lia|]. constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith|].
      constructor; [right; left; exists (q, IX, 128); cbn; auto with zarith| constructor]. }
    assert (LKF : links mF Hs).
    { eapply (links_keep Σ OW LB m mF ls PL EA ac qc Hs); [exact HEAP| exact PARTS| exact EC| exact LHs| exact HItems| exact HLinks| exact MU| exact WM|].
      constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia|]. constructor; [|constructor].
      right; right. exists q, IX, 128. split; [apply in_or_app; left; exact HinI|]. cbn [fst snd]. split; [lia|]. split; [lia|].
      fold c. intros Hq. eapply (ids_item_idx_neq ls q q); eauto using ids_m_nodup. }
    assert (LSF : lib_state (set_ctx c' ls) mF OW PL EA).
    { unfold lib_state. eapply (lib_state_cx_close [] ls (set_ctx c' ls) mF OW PL EA Hs IX); [| exact ND| reflexivity| reflexivity| reflexivity| reflexivity| | |].
      - eapply (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP); [exact HEAP| exact LSC| exact MU| exact WM| exact FROK|].
        constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
        constructor; [apply w_cx; [reflexivity| intros x Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]|].
        constructor; [apply w_cx; [reflexivity| intros x Hx; right; right; exists q, IX; cbn in Hx; auto]| constructor].
      - apply st_wf_set_ctx; [exact WFS| reflexivity|]. unfold ctx_wf, c'. cbn [gx_items gx_current gx_pused gx_indexes gx_frames gx_ssize gx_used gx_err_stack gx_too_many].
        split; [reflexivity|]. split; [reflexivity|]. split; [exact CE3|]. split; [exact CE4|]. split; [exact CE5|]. split; [exact CE6|].
        split; [rewrite <- app_assoc; apply BnMInv.nondecr_snoc; [exact CE7| lia]|].
        right. subst c'. cbn [gx_indexes gx_ssize gx_frames]. split; [unfold BG_DEPTH; lia|]. split; [discriminate|]. rewrite length_app. cbn [length]. unfold BG_DEPTH in *. lia.
      - apply ids_ok_set_ctx_same; [exact IDS| reflexivity| subst c'; cbn [gx_indexes]; fold c; symmetry; exact EI].
      - apply (cx_view_some _ _ _ _ _ _ _ _ EC). cbn [st_ctx set_ctx]. split; [exact BC|]. split; [exact LHs|]. split; [|split; [|split; [| exact LKF]]].
        + unfold ctx_cells, cur_addr, c'. cbn [gx_items gx_current gx_pused gx_frames gx_ssize gx_used gx_err_stack gx_too_many Z.b2z].
          rewrite length_app. cbn [length]. replace (Z.of_nat (length (gx_frames c) + 1)) with (Z.of_nat (length (gx_frames c)) + 1) by lia.
          unfold cur_addr in CX. exact CX.
        + unfold stack_rep. subst c'. cbn [gx_indexes gx_ssize gx_frames]. split; [exact HinI|]. split; [exact SZ32|].
          destruct stale as [|x0 stale']; [exfalso; cbn in LEN; lia|]. exists stale'. split; [rewrite length_app; cbn [length] in *; unfold BN_CTX_START_FRAMES; lia|].
          rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
          rewrite Ews in ARR2. rewrite Nat2Z.id in ARR2. rewrite <- (length_map (fun k : nat => wz (Z.of_nat k)) (gx_frames c)) in ARR2 at 1.
          rewrite W_ctx.upd_app_mid in ARR2. exact ARR2.
        + apply item_blocks_set_ctx; [reflexivity| exact HItems]. }
    unfold bn_postA. do 17 eexists. exists mF, OW, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|]. split; [exact LSF|].
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))|].
    split; [unfold MC; lia|].
    split. { unfold cnt_eq, cnt_bal, blocks_of. cbn [set_ctx st_bns st_ctx]. subst c'. cbn [gx_items gx_indexes]. fold c. rewrite EI. reflexivity. }
    split; [apply refs_stable_ow; [reflexivity| auto]|]. split; [reflexivity| intros q0 A0 n0 Hq0; exact Hq0].
  -
    replace (length (gx_frames c) =? gx_ssize c)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
    ub; step.
    ub; step. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia.
    { replace (gx_ssize c =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia). cbn [negb].
      apply evt_done. apply implA_unr. }
    replace (gx_ssize c =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia). cbn [negb].
    assert (EF : gx_frames c = []) by (destruct (gx_frames c); [reflexivity| cbn in KZ; lia]).
    unfold stack_rep in STK. destruct (gx_indexes c) as [q|] eqn:EI; [exfalso; destruct STK as (_ & E1 & _); unfold BN_CTX_START_FRAMES in E1; lia|].
    destruct STK as (-> & _ & _).
    do 2 (ub; step). do 6 (ub; step).

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -112, bv_unsigned sp); (ac, ac + 72)]).
    { constructor; [left; cbn; lia|]. constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith| constructor]. }
    assert (HEAP1 : AHEAP Σ OW LB m1) by (exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))).
    assert (AXP1 : ax_pres LB (bv_unsigned sp) (XW PL) m m1) by (exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))).
    assert (LSC1 : lib_state_hc true [] ls m1 OW PL EA).
    { eapply (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP); [exact HEAP| exact LSC| exact MU| exact WM| exact FROK|].
      constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
      constructor; [apply w_cx; [reflexivity| intros x Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]| constructor]. }
    assert (PM1 : links m1 Hs).
    { eapply (links_keep Σ OW LB m m1 ls PL EA ac qc Hs); [exact HEAP| exact PARTS| exact EC| exact LHs| exact HItems| exact HLinks| exact MU| exact WM|].
      constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia| constructor]. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -112) (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { apply (uw_push_frame m1 _ (bv_unsigned sp) 112 [C8 (Z_to_bv 64 (Z.of_nat (gx_used c))); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]
                              (bv_unsigned ra) (bv_unsigned s0) ras);
        [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
      - rewrite !Z_to_bv_bv_unsigned. exact FR.
      - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia |]. constructor; [|constructor].
        cbn. unfold BnHeapA.ACEIL in *. lia. }
    apply evt_done. change (4 * Z.of_nat BN_CTX_START_FRAMES) with (32 * 4).
    eapply (CRYPTO_malloc_array_walkA) with (num := 32) (size := 4) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
    + exact HEAP1.
    + rewrite ESP. exact ST.
    + exact CEIL.
    + rewrite ESP. unfold CRYPTO_MALLOC_ARRAY_STACK, CRYPTO_MALLOC_STACK, RT_STACK. lia.
    + rewrite ESP. unfold USTACK_TOP. lia.
    + rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
    + exact MI.
    + exact (proj1 LSC1).
    + pose proof (cnt_ok_live ls OW LB OW 0 WFS CNT ltac:(lia) ltac:(lia)) as HL. rewrite length_map in HL. exact HL.
    + exact CRED.
    + rewrite ESP. exact UW1.
    + rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_cs_marr CTX).
    + intros pn Σ1 ms1 FRESH PO. unfold calloc_postA in PO. rewrite ?ESP in PO.
      destruct PO as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & F1 & fc1 & m3 & An & -> & MI3 & ST3 & AG3 & CR3 & BR & HEAP3 & ACCN & (junkA & BLK)).
      rewrite (ret_pc_even 2258872) by lia.
      apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG3) in CX; [| intros x Hx; right; right; exists (qc, ac, 72); split; [exact INC| cbn in Hx |- *; lia]].
      assert (LSC3 : lib_state_hc true [] ls m3 OW PL EA).
      { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ (bv_unsigned sp + -112) (bv_unsigned sp) USTACK_TOP); [exact LSC1| exact FROK| lia| lia| exact AG3| | lb_in_heap].
        intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (PM3 : links m3 Hs).
      { eapply (links_heap_pres ls OW (OW ++ LB) (bv_unsigned sp + -112)); [exact LHs| exact HItems| | exact PM1| exact AG3].
        intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (UW3 : uw_chain USTACK_TOP m3 (bv_unsigned sp + -112) (bv_unsigned sp) (bv_unsigned ra :: ras)).
      { eapply uw_chain_agree; [exact UW1|]. eapply agree_on_mono; [exact AG3|]. intros x Hx. left. exact Hx. }
      assert (AXP3 : ax_pres LB (bv_unsigned sp) (XW PL) m m3).
      { eapply ax_pres_trans; [exact AXP1|]. eapply agree_on_mono; [exact AG3|]. intros x [_ [Hx|[Hx|(b0 & Hb0 & Hr)]]];
          [left; lia | right; left; exact Hx | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]]. }
      pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
      assert (EAn : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
      set (OW1 := (pn, An, 32 * 4) :: OW) in *.
      assert (ND1 : List.NoDup (map blk_id OW1)) by (exact (AH_nodup_l _ _ _ _ HEAP3)).
      assert (FRESHA : ~ In pn (all_ids ls PL EA)).
      { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
      assert (NEWSEP : forall q A n, In (q, A, n) OW -> An + 32 * 4 <= A \/ A + n <= An).
      { intros q A n Hq. assert (NE : pn <> q) by (intros ->; apply FRESH; rewrite map_app; apply in_or_app; left; apply (in_map blk_id) in Hq; exact Hq).
        exact (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hq) NE). }
      pose proof (NEWSEP _ _ _ BC) as SEPc.
      assert (LSC3' : lib_state_hc true [] ls m3 OW1 PL EA) by (eapply lib_state_h_ow; [exact LSC3|]; intros q A n _ Hq; right; exact Hq).
      assert (HItems1 : item_blocks ls OW1 Hs) by (eapply item_blocks_ow; [exact HItems| intros b0 Hb0; right; exact Hb0]).
      assert (INC1 : In (qc, ac, 72) (OW1 ++ LB)) by (apply in_or_app; left; right; exact BC).
      assert (INN1 : In (pn, An, 32 * 4) (OW1 ++ LB)) by (apply in_or_app; left; left; reflexivity).
      pose proof (AH_acc_in _ _ _ _ (qc, ac, 72) (ac) 72 HEAP3 INC1 ltac:(cbn; lia) ltac:(cbn; lia)) as ACC3.
      clear ACC MU WM OFF.
      pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)]%Z m3) as MU3. pose proof (wmono_refl bgbsegs m3) as WM3.
      assert (OFF3 : offshW [(bv_unsigned sp + -112, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
      cbn [tbind fst snd]. unfold bret. cbn [ret tree_ops tbind fst snd].
      unfold MallocRep.wz in *.
      apply implA_from_evt.
      ub; step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EAn in KA; lia|]. clear KA.
      ub; step. ub; shl. ub; chk0.
      ub; step. rewrite EF. cbn [length]. change (Z.of_nat 0) with 0. rewrite (zx32_small 0) by lia.
      ub; step. if_true.
      ub; step. ub; shl. ub; chk0.
      do 4 (ub; step). ub; step.
      apply evt_done.
      eapply implA_step_same.
      { eapply (CRYPTO_free_null_cpsA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW1) (LB := LB); try reflexivity.
        - exact HEAP3.
        - rewrite ESP. exact ST3.
        - exact CEIL.
        - rewrite ESP. unfold CRYPTO_FREE_STACK, RT_STACK. lia.
        - rewrite ESP. unfold USTACK_TOP. lia.
        - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
        - exact MI3.
        - exact (proj1 LSC3').
        - rewrite ESP. exact UW3.
        - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_cs_free CTX). }
      intros ms5 PO. unfold cfree_null_post in PO. rewrite ?ESP in PO.
      destruct PO as (v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F5 & fc5 & m5 & -> & MI5 & ST5 & HEAP5 & AG5).
      rewrite (ret_pc_even 2258968) by lia. unfold MallocRep.wz.
      apply (rw_cells_agree _ _ _ _ _ AG5) in FR; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in CX; [| intros x Hx; right; right; exists (qc, ac, 72); split; [exact INC1| cbn in Hx |- *; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG5) in BLK; [| intros x Hx; right; right; exists (pn, An, 32 * 4); split; [exact INN1| cbn in Hx |- *; lia]].
      assert (LSC5 : lib_state_hc true [] ls m5 OW1 PL EA).
      { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ (bv_unsigned sp + -112) (bv_unsigned sp) USTACK_TOP); [exact LSC3'| exact FROK| lia| lia| exact AG5| | lb_in_heap].
        intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      pose proof (lib_state_h_parts _ _ _ _ _ _ LSC5) as PARTS1.
      assert (PM5 : links m5 Hs).
      { eapply (links_heap_pres ls OW1 (OW1 ++ LB) (bv_unsigned sp + -112)); [exact LHs| exact HItems1| | exact PM3| exact AG5].
        intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (AXP5 : ax_pres LB (bv_unsigned sp) (XW PL) m m5).
      { eapply ax_pres_trans; [exact AXP3|]. eapply agree_on_mono; [exact AG5|]. intros x [_ [Hx|[Hx|(b0 & Hb0 & Hr)]]];
          [left; lia | right; left; exact Hx | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]]. }

      destruct (W_ctx.u32s_exists 32 junkA) as (ws & LWS & EWS).
      { destruct BLK as [[[HL _] _] _]. cbn in HL. exact HL. }
      assert (ARR : u32arr bgbsegs m5 An ws).
      { apply u8arr_of_rw_cells in BLK. destruct BLK as [B1 B2]. split; [rewrite EWS; exact B1|].
        rewrite LWS. replace (Z.of_nat (length junkA)) with (4 * Z.of_nat 32) in B2; [exact B2|].
        rewrite <- EWS, u32s_length, LWS. lia. }
      clear BLK.
      pose proof (AH_acc_in _ _ _ _ (qc, ac, 72) (ac) 72 HEAP5 INC1 ltac:(cbn; lia) ltac:(cbn; lia)) as ACC5.
      pose proof (AH_acc_in _ _ _ _ (pn, An, 32 * 4) An 128 HEAP5 INN1 ltac:(cbn; lia) ltac:(cbn; lia)) as ACCN5.
      assert (ALN : An mod 8 = 0) by (clear - BA16; Z.div_mod_to_equations; lia).
      pose proof (AH_offsh _ _ _ _ (pn, An, 32 * 4) HEAP5 INN1) as ON. cbn [blk_addr blk_size fst snd] in ON. unfold SHLO, SHHI in ON.
      clear ACC3 MU3 WM3 OFF3.
      pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (ac, ac + 72); (An, An + 128)]%Z m5) as MU5.
      pose proof (wmono_refl bgbsegs m5) as WM5.
      assert (OFF5 : offshW [(bv_unsigned sp + -112, bv_unsigned sp); (ac, ac + 72); (An, An + 128)]).
      { pose proof (AH_offsh _ _ _ _ (qc, ac, 72) HEAP5 INC1) as O. cbn [blk_addr blk_size fst snd] in O.
        cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
      apply implA_from_evt.
      ub; shl. ub; chk0. ub; step. ub; shl. ub; step. ub; chk0. ub; step.

      ub; step. ub; shl. ub; chk0. ub; shl. ub; step. ub; chk0.
      ub; step. rewrite EF. cbn [length]. change (Z.of_nat 0) with 0. rewrite (zx32_small 0) by lia.
      do 2 (ub; step). ub; step. ub; step.
      do 2 (ub; step). ub; shl. ub; chk0.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      pose proof (u32arr_store_ok bgbsegs m6 An ws 0 (wa An) ARR ltac:(lia) ltac:(f_equal; lia)) as SOKW.
      pose proof (u32arr_write bgbsegs m6 An ws 0 (Z_to_bv 64 (Z.of_nat (gx_used c))) ARR ltac:(lia)) as ARR2.
      rewrite Z.mul_0_r, Z.add_0_r in ARR2. change (Z.to_nat 0) with 0%nat in ARR2.
      ub; step. store_done.
      ub; step. do 13 (ub; step). release_frame FR ST5 (bv_unsigned sp). ub; step. ub; step.
      apply evt_done. apply implA_ret.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mF end.
      lazymatch goal with |- context [set_ctx ?cc ls] => set (c' := cc) end.
      assert (HinN : In (pn, An, 32 * 4) OW1) by (left; reflexivity).
      assert (BC1 : In (qc, ac, 72) OW1) by (right; exact BC).
      assert (HWL5 : Forall (w_lib ls OW1 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -112, bv_unsigned sp); (ac, ac + 72); (An, An + 128)]).
      { constructor; [left; cbn; lia|]. constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith|].
        constructor; [right; left; exists (pn, An, 32 * 4); cbn; auto with zarith| constructor]. }
      assert (LKF : links mF Hs).
      { eapply (links_keep Σ1 OW1 LB m5 mF ls PL EA ac qc Hs); [exact HEAP5| exact PARTS1| exact EC| exact LHs| exact HItems1| exact PM5| exact MU5| exact WM5|].
        constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia|]. constructor; [|constructor].
        right; right. exists pn, An, (32 * 4). split; [exact INN1|]. cbn [fst snd]. split; [lia|]. split; [lia|].
        fold c. intros Hq. apply FRESHA. unfold all_ids. apply in_or_app; right; apply in_or_app; right. apply item_in_m. exact Hq. }
      assert (LSF : lib_state (set_ctx c' ls) mF OW1 PL EA).
      { unfold lib_state. eapply (lib_state_cx_close [] ls (set_ctx c' ls) mF OW1 PL EA Hs An); [| exact ND1| reflexivity| reflexivity| reflexivity| reflexivity| | |].
        - eapply (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP); [exact HEAP5| exact LSC5| exact MU5| exact WM5| exact FROK|].
          constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
          constructor; [apply w_cx; [reflexivity| intros x' Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]|].
          constructor; [|constructor].
          eapply (w_foreign OW1 LB ls PL EA (bv_unsigned sp) true [] _ pn An (32 * 4)); [first [eassumption | left; reflexivity | right; eassumption] | exact FRESHA| cbn; lia| cbn; lia].
        - apply st_wf_set_ctx; [exact WFS| reflexivity|]. unfold ctx_wf, c'. cbn [gx_items gx_current gx_pused gx_indexes gx_frames gx_ssize gx_used gx_err_stack gx_too_many app]. rewrite ?EF. cbn [app length].
          split; [reflexivity|]. split; [reflexivity|]. split; [exact CE3|]. split; [exact CE4|]. split; [exact CE5|]. split; [exact CE6|].
          split; [cbn; lia|]. right. split; [reflexivity|]. split; [discriminate|]. cbn [length]. unfold BG_DEPTH. lia.
        - eapply (ids_ok_set_ctx_new_idx ls PL EA c' pn); [exact IDS| reflexivity| exact EI| reflexivity| exact FRESHA].
        - apply (cx_view_some _ _ _ _ _ _ _ _ EC). cbn [st_ctx set_ctx]. split; [exact BC1|]. split; [exact LHs|]. split; [|split; [|split; [| exact LKF]]].
          + unfold ctx_cells, cur_addr, c'. cbn [gx_items gx_current gx_pused gx_frames gx_ssize gx_used gx_err_stack gx_too_many Z.b2z app length]. rewrite ?EF. cbn [app length].
            unfold cur_addr in CX. exact CX.
          + unfold stack_rep, c'. cbn [gx_indexes gx_ssize gx_frames app]. split; [exact HinN|]. split; [reflexivity|]. rewrite ?EF. cbn [app length map].
            destruct ws as [|w0 ws']; [cbn in LWS; lia|]. exists ws'. split; [cbn [length] in *; unfold BN_CTX_START_FRAMES; lia|]. cbn [map app Arr.upd] in *. exact ARR2.
          + apply item_blocks_set_ctx; [reflexivity| exact HItems1]. }
      unfold bn_postA. do 17 eexists. exists mF, OW1, PL. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap Σ1 ls OW1 LB PL EA _ m5 mF _ lo _ HEAP5 PARTS1 FROK MU5 WM5 HWL5 CEIL ltac:(unfold USTACK_TOP; lia))|]. split; [exact LSF|].
      split; [exact ST5|]. split; [assumption|].
      split. { eapply ax_pres_trans; [exact AXP5|]. exact (seg_ax_pres' Σ1 ls OW1 LB PL EA _ m5 mF _ lo _ HEAP5 PARTS1 FROK MU5 HWL5 CEIL ltac:(lia)). }
      split; [exact CR3|].
      split. { unfold cnt_eq, cnt_bal, blocks_of. cbn [set_ctx st_bns st_ctx]. fold c. unfold c'. cbn [gx_items gx_indexes]. rewrite EI. cbn [opt_block].
               unfold OW1. rewrite !length_app. cbn [length]. lia. }
      split. { apply refs_stable_ow; [reflexivity|]. intros q H0 _ Hq. right. exact Hq. }
      split; [reflexivity|]. intros q0 A0 n0 Hq0. right. exact Hq0.
Qed.

Definition BN_CTX_END : Z := 0x2279f0.
Definition BN_CTX_END_STACK : Z := 16.

End WithRT.
