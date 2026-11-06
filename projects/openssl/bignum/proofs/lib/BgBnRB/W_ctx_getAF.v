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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require StrFun.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2 W_ctx_getA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import CtxKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2260128 => 2
  | 2260136 => 1
  | 2260140 => 2
  | 2260388 => 1
  | 2260392 => 2
  | 2260404 => 1
  | 2260436 => 2
  | 2260548 => 2
  | 2260552 => 1
  | 2260556 => 2
  | 2260660 => 2
  | 2260664 => 1
  | 2260668 => 2
  | 2260832 => 2
  | 2260836 => 1
  | 2260840 => 2
  | 2260880 => 2
  | 2260988 => 1
  | 2260992 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma stack_rep_agreeP : forall (OW : list block) L SP (P : Z -> Prop) m m' IX (c : bg_ctx bptr),
  (forall b, In b OW -> In b L) -> stack_rep m OW IX c -> agree_on P m m' ->
  (forall q, gx_indexes c = Some q -> In (q, IX, 128) OW -> forall x, aclient_addr L SP x -> IX <= x < IX + 128 -> P x) ->
  stack_rep m' OW IX c.
Proof.
  intros OW L SP P m m' IX c HI STK HP HPx. unfold stack_rep in *. destruct (gx_indexes c) as [q|] eqn:EI; [|exact STK].
  destruct STK as (HinI & SZ32 & stale & LEN & ARRI). split; [exact HinI|]. split; [exact SZ32|]. exists stale. split; [exact LEN|].
  change FRAMES_SZ with 128 in HinI. unfold BN_CTX_START_FRAMES in LEN.
  eapply LibKitA.u32arr_agree; [exact HP| exact ARRI|]. intros x Hx. rewrite length_app, length_map in Hx. apply (HPx q eq_refl HinI); [|lia].
  right; right. exists (q, IX, 128). split; [apply HI; exact HinI|]. cbn [blk_addr blk_size fst snd]. lia.
Qed.

Local Notation E_cg_malloc := (E_BN_CTX_get_227bb4 : uk_call BN_CTX_GET 0x227d9c BnRepDefs.CRYPTO_MALLOC).

Lemma BN_CTX_get_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo BN_CTX_GET_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_CTX_GET (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
  implA (BN_CTX_get (tree_ops bptr) ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
              (fun r ls' OW' PL' a0' => PL' = PL /\ (exists i, r = RPool i) /\ (exists a, ref_at ls' OW' PL r a /\ a0' = wz a)
                                    /\ (forall q A n, In (q, A, n) OW -> In (q, A, n) OW')))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_CTX_GET) fc None m (seg_rom bgbsegs)).
Proof.
  intros until qc. intros (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR) UW CTX -> EC ->.
  unfold BN_CTX_GET_STACK, CRYPTO_MALLOC_STACK, RT_STACK, BN_CTX_GET, MallocRep.wz in *.
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
  pose proof (AH_offsh _ _ _ _ (qc, ac, 72) HEAP INC) as OC. cbn [blk_addr blk_size fst snd] in OC. unfold SHLO, SHHI in OC.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  unfold BN_CTX_get, bbind, bgetctx, bret, bunr, bmalloc, bsetctx, bget, bset, bgetst, bsetbns.
  cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd]. fold c.
  rewrite CE1, CE2. cbn [Nat.eqb negb orb].
  set (psize := (BN_CTX_POOL_SIZE * length (gx_items c))%nat) in *.
  assert (P48 : (psize <= 48)%nat /\ (gx_used c <= psize)%nat) by (subst psize; unfold BN_CTX_POOL_SIZE in *; split; lia).
  destruct P48 as [P48 UP].
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (ac, ac + 72)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 112, bv_unsigned sp); (ac, ac + 72)]).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
  assert (CA47 : 0 < ac /\ ac + 72 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; lia).
  apply implA_from_evt.
  carve_frame 112%nat ST.
  apply (rw_cells_split_CB bgbsegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 15 step.
  ub. step. ub.
  do 3 step.
  do 3 step. ub; shl. ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
  ub; step. if_false.
  do 3 (ub; step). ub; shl. ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
  ub; step. if_true.
  do 3 (ub; step). ub; shl. ub; chk0.
  do 3 (ub; step). ub; shl.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
  ub; chk0.
  do 3 (ub; step). ub; shl.
  ub; step. unfold MallocRep.wz at 1. rewrite (zx32_small (Z.of_nat (gx_pused c))) by lia.
  ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat psize)) by lia.
  ub; zstep. rewrite ?Z.add_0_r. rewrite (bn_swrap32_small (Z.of_nat (gx_pused c))) by lia.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jb :: _) => set (jbv := jb) in FR end.
  ub; step. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia.
  -
    replace (gx_pused c =? psize)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    cbn [tbind fst snd].
    set (i := gx_pused c) in *.
    assert (IU : i = gx_used c) by exact CE3.
    assert (ILT : (i < psize)%nat) by lia.
    pose proof (Nat.div_mod_eq i 16) as DM. pose proof (Nat.mod_upper_bound i 16 ltac:(lia)) as MB.
    assert (KLT : (i / 16 < length Hs)%nat).
    { rewrite LHs. apply div16_of_lt. subst psize. unfold BN_CTX_POOL_SIZE in ILT. lia. }
    destruct (nth_error Hs (i / 16)) as [Hk|] eqn:EHk; [|exfalso; apply nth_error_None in EHk; lia].
    pose proof (item_facts Σ OW LB m ls PL EA ac qc Hs _ _ HEAP PARTS EC LHs HItems EHk) as (HK0 & HKC & HKM & HKX & HKK & HKI). change BN_CTX_SZ with 72 in HKX.
    destruct (nth_error (gx_items c) (i / 16)) as [qk|] eqn:Eqk; [|exfalso; apply nth_error_None in Eqk; lia].
    pose proof (HItems _ _ Eqk) as HinK. rewrite (nth_error_nth _ _ _ EHk) in HinK. change ITEM_SZ with 400 in HinK.
    pose proof (AH_range _ _ _ _ _ _ _ HEAP HinK) as (_ & HA16 & _ & _ & _).
    assert (INH : In (qk, Hk, 400) (OW ++ LB)) by (apply in_or_app; left; exact HinK).
    pose proof (AH_offsh _ _ _ _ (qk, Hk, 400) HEAP INH) as OH. cbn [blk_addr blk_size fst snd] in OH. unfold SHLO, SHHI in OH.
    assert (HA : ref_at ls OW PL (RPool i) (Hk + 24 * Z.of_nat (i mod 16))).
    { replace (RPool i) with (RPool (BN_CTX_POOL_SIZE * (i / 16) + i mod 16)) by (unfold BN_CTX_POOL_SIZE; rewrite div16_mod_eq; reflexivity).
      eapply ref_at_item_slot; [exact Eqk| exact HinK| unfold BN_CTX_POOL_SIZE; lia]. }
    assert (NRO : not_one (RPool i)) by (unfold not_one, RPool, ROne, NFIX; lia).
    lazymatch goal with |- context [mkGx (gx_items c) ?cu (S i)] => set (cur := cu) in * end.
    assert (ECUR : cur = Some (i / 16)%nat).
    { subst cur. destruct (Nat.eqb_spec i 0) as [E0|E0]; [rewrite E0; reflexivity|].
      pose proof CE6 as EC6. fold c in EC6. rewrite <- IU in EC6. replace (i =? 0)%nat with false in EC6 by (symmetry; apply Nat.eqb_neq; exact E0).
      unfold BN_CTX_POOL_SIZE in EC6 |- *. destruct (Nat.eqb_spec (i mod 16) 0) as [EM|EM]; rewrite EC6; f_equal.
      - exact (proj1 (div16_pred_bd i E0 EM)).
      - exact (div16_pred_in i EM). }
    destruct (lib_state_open [] ls m OW PL EA (RPool i) _ LSC ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    set (b := getbn (RPool i) ls) in *.
    assert (FLR : 0 <= bn_flags b <= 1) by (destruct OK4 as [E|E]; rewrite E; lia).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSC HA) as HV.
    assert (ALB : (Hk + 24 * Z.of_nat (i mod 16)) mod 8 = 0) by (clear - HA16; Z.div_mod_to_equations; lia).
    assert (H47 : 0 < Hk /\ Hk + 400 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; lia).
    lazymatch goal with |- evt _ ?Q _ => remember Q as QQ eqn:EQQ end.
    lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mx _) =>
      assert (CONT : forall (hk : Z) (mX : mem) (x11 x13 x14 : word),
        hk = Hk ->
        rw_cells bgbsegs mX ac
          [C8 (wz (hd 0 Hs)); C8 (wz hk); C8 (wz (last Hs 0)); C4 (wz (Z.of_nat i)); C4 (wz (Z.of_nat psize)); C8 (wz IX);
           C4 (wz (Z.of_nat (length (gx_frames c)))); C4 (wz (Z.of_nat (gx_ssize c))); C4 (wz (Z.of_nat (gx_used c)));
           C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)] ->
        rw_cells bgbsegs mX (bv_unsigned sp + -112) [CB 8 jbv; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk bgbsegs mX lo (bv_unsigned sp + -112) ->
        munch [(bv_unsigned sp + -112, bv_unsigned sp); (ac, ac + 72)]%Z m mX -> wmono bgbsegs m mX -> mem_inv bgbsegs mX ->
        shb_cells bgbsegs 6147864 6945336 mX ->
        evt bgbsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 ac)
                             (Z_to_bv 64 (ac + 8)) x11 (Z_to_bv 64 (Z.of_nat i)) x13 x14 a5 a6 a7
                             (Z_to_bv 64 (ac + 24)) s3 (Z_to_bv 64 (ac + 28)) (Z_to_bv 64 (ac + 56)) (Z_to_bv 64 SHB)
                             (Z_to_bv 64 ((ac + 24) ≫ 3 + SHB)) (Z_to_bv 64 ((ac + 28) ≫ 3 + SHB)) (Z_to_bv 64 ((ac + 56) ≫ 3 + SHB))
                             (Z_to_bv 64 0) s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x227f4c) fc None mX (seg_rom bgbsegs))) end.
    { intros hk mX x11 x13 x14 -> CXX FRX STX MUX WMX MIX (SHX1 & SHX2).
      clear MU WM MI ST FR CX SHB1 SHB2.
      unfold MallocRep.wz in CXX.
      do 2 step. ub; shl. ub; chk0.
      ub; step.
      ub.
      ub; shl. ub; chk0.
      do 5 (ub; zstep).
      replace (Z.land (Z.of_nat i) 15) with (Z.of_nat (i mod 16)).
      2:{ change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. rewrite Nat2Z.inj_mod. reflexivity. }
      rewrite !Z.shiftl_mul_pow2 by lia. change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia.
      rewrite (Z.mod_small (Z.of_nat (i mod 16) * 2 ^ 3) (2 ^ 64)) by lia.
      setreg 10%Z (Z_to_bv 64 (24 * Z.of_nat (i mod 16))) ltac:(f_equal; lia).
      ub; zstep.
      ub; step.
      zstep. if_cases CT; zify_cond CT.
      { exfalso. rewrite lxor_ones64 in CT by lia. clear - CT H47 MB. lia. }
      clear CT.
      ub; zstep.
      ub; step.
      unfold bn_cells in BN.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?my _) => rename my into m2 end.
      apply rw_cells_CB8_hd in FRX.
      lazymatch type of MUX with munch ?W0 _ _ =>
        apply (rw_cells_transport bgbsegs W0 m m2 (Hk + 24 * Z.of_nat (i mod 16))) in BN; [| exact MUX| exact WMX| cbn [disjoint_from cells_size csize Nat.add]; unfold BnHeapA.ACEIL in *; lia] end.
      pose proof (AH_acc_in _ _ _ _ (qk, Hk, 400) (Hk + 24 * Z.of_nat (i mod 16)) 24 HEAP INH ltac:(cbn; lia) ltac:(cbn; lia)) as ACCB.
      assert (ACCB2 : acc bgbsegs m2 (Hk + 24 * Z.of_nat (i mod 16)) 24) by (eapply (acc_munch bgbsegs _ m m2 _ _ ACCB MUX OFF); unfold BnHeapA.ACEIL in *; lia).
      assert (ACCC2 : acc bgbsegs m2 ac 72) by (eapply (acc_munch bgbsegs _ m m2 _ _ ACC MUX OFF); unfold BnHeapA.ACEIL in *; lia).
      eapply evt_cut.
      { eapply (get_tailA) with (lo := lo) (CTX := ac) (A := Hk + 24 * Z.of_nat (i mod 16)) (D := D) (b := b) (used := Z.of_nat (gx_used c));
          [exact BN | exact FLR | exact CXX | lia | exact FRX | exact STX | unfold BnHeapA.ACEIL in *; lia | exact MIX
          | unfold BnHeapA.ACEIL in *; lia | unfold BnHeapA.ACEIL in *; lia | lia | unfold BnHeapA.ACEIL in *; lia
          | exact (conj SHX1 SHX2) | exact ACCB2 | exact ALB | exact ACCC2 | exact AL
          | unfold SHHI, BnHeapA.ACEIL in *; lia | unfold SHLO, SHHI; lia | unfold SHLO, SHHI; lia | lia ]. }
      intros ms' PO. unfold get_tail_postA in PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & mF & -> & MUt & WMt & MIt & STt & BNt & CXt).
      subst QQ. apply evt_done. apply implA_ret.
      set (bz := bn_zero_pure b).
      set (c2 := mkGx (gx_items c) cur (S i) (gx_indexes c) (gx_frames c) (gx_ssize c) (S (gx_used c)) 0 false).
      lazymatch goal with |- context [(RPool i, ?stM)] => change stM with (set_ctx c2 (setbn (RPool i) bz ls)) end.
      set (WF := [(bv_unsigned sp - 128, bv_unsigned sp); (Hk + 24 * Z.of_nat (i mod 16), Hk + 24 * Z.of_nat (i mod 16) + 24); (ac, ac + 72)]%Z).
      assert (MUF : munch WF m mF).
      { eapply munch_trans; [eapply munch_weaken; [|exact MUX]| exact MUt].
        intros x Hx. subst WF. cbn [outside] in *. clear - Hx. intuition lia. }
      assert (WMF : wmono bgbsegs m mF) by (eapply wmono_trans; eassumption).
      assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) WF).
      { subst WF. constructor; [left; cbn; lia|]. constructor; [right; left; exists (qk, Hk, 400); cbn; split; [exact HinK| lia]|].
        constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith| constructor]. }
      destruct (bn_arr_facts Σ OW LB m HEAP ls PL EA _ _ PARTS FROK (RPool i) D HV NRO ARR) as (U & LENW & D0 & DC & DI & DSEP).
      specialize (DSEP (RPool i) _ HA). fold b in U, LENW, DC, DI, DSEP.
      assert (DCX : ac + 72 <= D \/ D + 8 * Z.of_nat (bn_dmax b) <= ac).
      { pose proof ARR as ARR'. unfold bn_arr in ARR'. rewrite pl_of_pool in ARR'. destruct (bn_d b) as [pd|] eqn:Ed.
        - destruct ARR' as [Hin _]. assert (NE : qc <> pd) by (eapply ids_pl_m; [exact IDS| eapply in_pl_ids_ctx; exact EC| eapply bn_in_m; [exact HV| exact Ed]]).
          exact (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC Hin NE).
        - destruct ARR' as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn. lia. }
      assert (LKF : links mF Hs).
      { eapply links_transport; [exact HLinks| exact MUF| exact WMF|]. intros j H Hj. subst WF. cbn [disjoint_from].
        pose proof (item_facts Σ OW LB m ls PL EA ac qc Hs _ _ HEAP PARTS EC LHs HItems Hj) as (F0 & FC & FM & FX & FK & FI). change BN_CTX_SZ with 72 in FX.
        destruct (Nat.eq_dec j (i / 16)) as [->|NEj].
        - rewrite EHk in Hj. injection Hj as <-. clear - F0 FC FX MB CEIL LO SPR. unfold BnHeapA.ACEIL in *. lia.
        - specialize (FK _ _ EHk ltac:(congruence)). clear - F0 FC FX FK MB CEIL LO SPR. unfold BnHeapA.ACEIL in *. lia. }
      assert (LSF : lib_state (set_ctx c2 (setbn (RPool i) bz ls)) mF OW PL EA).
      { unfold lib_state.
        assert (IDS1 : ids_ok (setbn (RPool i) bz ls) PL EA) by (apply ids_ok_setbn_same; [exact IDS| exact HV| reflexivity]).
        assert (OKz : bg_ok bz).
        { subst bz. unfold bg_ok, bn_zero_pure, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OK1|]. split; [lia|]. split; [exact OK3| exact OK4]. }
        assert (LS1 : lib_state_hc true [] (setbn (RPool i) bz ls) mF OW PL EA).
        { eapply (lib_state_close [] ls mF OW PL EA (RPool i) (Hk + 24 * Z.of_nat (i mod 16)) bz); [| exact ND| exact HA| exact NRO| | exact OKz| exact IDS1].
          - eapply (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP); [exact HEAP| exact LSH| exact MUF| exact WMF| exact FROK|]. subst WF.
            constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
            constructor; [eapply (w_struct OW LB ls PL EA (bv_unsigned sp) true [RPool i] _ (RPool i) (Hk + 24 * Z.of_nat (i mod 16)));
                            [left; reflexivity| exact HA| exact NRO| cbn; lia| cbn; lia]|].
            constructor; [apply w_cx; [reflexivity| intros x Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]| constructor].
          - exists D. split; [exact BNt|]. change (bn_arr mF OW (pl_of PL (RPool i)) D b).
            eapply bn_arr_of_u64arr; [exact ARR|]. eapply u64arr_transport; [exact U| exact MUF| exact WMF|].
            subst WF. cbn [disjoint_from]. rewrite LENW. clear - DSEP DCX DC CEIL LO SPR. unfold BnHeapA.ACEIL in *. lia. }
        eapply (lib_state_cx_close [] (setbn (RPool i) bz ls) _ mF OW PL EA Hs IX); [exact LS1| exact ND| reflexivity| reflexivity| reflexivity| reflexivity| | |].
        - apply st_wf_set_ctx; [apply st_wf_setbn; [exact WFS| exact NRO| exact OKz]| reflexivity|].
          unfold ctx_wf, c2. cbn [gx_items gx_current gx_pused gx_indexes gx_frames gx_ssize gx_used gx_err_stack gx_too_many].
          split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [fold psize; lia|]. split; [exact CE5|].
          split. { rewrite ECUR. cbn [Nat.eqb]. f_equal. rewrite <- IU. unfold BN_CTX_POOL_SIZE. rewrite Nat.sub_succ, Nat.sub_0_r. reflexivity. }
          split; [eapply nondecr_last_incr; [exact CE7| lia]| exact CE8].
        - apply ids_ok_set_ctx_same; [exact IDS1| reflexivity| reflexivity].
        - apply (cx_view_some _ _ _ _ _ _ _ _ EC). cbn [st_ctx set_ctx]. split; [exact BC|]. split; [exact LHs|]. split; [|split; [|split; [| exact LKF]]].
          + unfold ctx_cells, cur_addr, c2. cbn [gx_items gx_current gx_pused gx_frames gx_ssize gx_used gx_err_stack gx_too_many Z.b2z].
            rewrite ECUR. cbn [gx_items]. rewrite (nth_error_nth _ _ _ EHk). unfold MallocRep.wz. rewrite !Nat2Z.inj_succ. unfold Z.succ. exact CXt.
          + apply (stack_rep_same mF OW IX c c2); [reflexivity| reflexivity| reflexivity|].
            eapply (stack_rep_keep Σ OW LB m mF ls PL EA ac qc IX); [exact HEAP| exact PARTS| exact EC| exact STK| exact MUF| exact WMF|]. subst WF.
            constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [|constructor; [right; left; cbn; unfold BN_CTX_SZ; lia| constructor]].
            right; right. exists qk, Hk, 400. split; [apply in_or_app; left; exact HinK|]. cbn [fst snd]. split; [lia|]. split; [lia|].
            fold c. intros E. eapply (ids_item_idx_neq ls qk qk); [eapply ids_m_nodup; exact IDS| eapply nth_error_In; exact Eqk| symmetry; exact E| reflexivity].
          + apply item_blocks_set_ctx; [reflexivity| exact HItems]. }
      unfold bn_postA. do 17 eexists. exists mF, OW, PL. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUF WMF HWL CEIL ltac:(unfold USTACK_TOP; lia))|]. split; [exact LSF|].
      split; [exact STt|]. split; [exact MIt|].
      split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUF HWL CEIL ltac:(lia))|].
      split; [unfold MC; lia|].
      split. { unfold cnt_eq. transitivity (cnt_bal (setbn (RPool i) bz ls) OW); [reflexivity|].
               rewrite (cnt_bal_setbn (RPool i) bz ls OW OW HV). fold b.
               assert (EBL : bn_blocks bz = bn_blocks b) by reflexivity. rewrite EBL. lia. }
      split; [apply refs_stable_ow; [reflexivity| auto]|].
      split; [reflexivity|]. split; [eexists; reflexivity|]. split; [|intros q0 A0 n0 Hq0; exact Hq0].
      exists (Hk + 24 * Z.of_nat (i mod 16)). split; [|reflexivity].
      apply (proj1 (ref_at_same_items (setbn (RPool i) bz ls) c2 OW PL (RPool i) _ ltac:(reflexivity))).
      apply (proj2 (ref_at_setbn ls OW PL (RPool i) bz (RPool i) _)). exact HA. }

    ub; step.
    ub; step. if_cases KU; zify_cond KU; rewrite ?unsigned_lit in KU by lia.
    +
      assert (I0 : i = 0%nat) by lia.
      assert (EH : hd 0 Hs = Hk).
      { rewrite I0 in EHk. cbn in EHk. destruct Hs as [|h0 Hs']; [discriminate EHk|]. injection EHk as ->. reflexivity. }
      do 2 (ub; step). ub; shl. ub; chk0. do 2 (ub; step). ub; shl. ub; chk0.
      ub; step. ub; step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply evt_eq; [| eapply (CONT (hd 0 Hs) mx); [exact EH| exact CX| exact FR| exact ST| exact MU| exact WM| exact MI| exact (conj SHB1 SHB2)] ] end.
      rewrite I0. reflexivity.
    +
      pose proof CE6 as EC6. fold c in EC6. rewrite <- IU in EC6. replace (i =? 0)%nat with false in EC6 by (symmetry; apply Nat.eqb_neq; lia).
      unfold cur_addr in CX. rewrite EC6 in CX. unfold BN_CTX_POOL_SIZE in CX.
      ub; zstep.
      rewrite ?(unsigned_lit (Z.of_nat i)) by lia.
      replace (Z.land (Z.of_nat i) 15) with (Z.of_nat (i mod 16)).
      2:{ change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. rewrite Nat2Z.inj_mod. reflexivity. }
      ub; step. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by lia.
      *
        assert (EK : ((i - 1) / 16 = i / 16)%nat) by (apply div16_pred_in; lia).
        rewrite ?EK, ?(nth_error_nth _ _ _ EHk) in CX.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply (CONT Hk mx); [reflexivity| exact CX| exact FR| exact ST| exact MU| exact WM| exact MI| exact (conj SHB1 SHB2)] end.
      *
        assert (EM : (i mod 16 = 0)%nat) by lia.
        destruct (div16_pred_bd i ltac:(lia) EM) as [EK0 KP1].
        assert (EK : ((i - 1) / 16 = i / 16 - 1)%nat) by lia.
        rewrite ?EK in CX.
        destruct (nth_error Hs (i / 16 - 1)) as [Hp|] eqn:EHp; [|exfalso; apply nth_error_None in EHp; lia].
        pose proof (item_facts Σ OW LB m ls PL EA ac qc Hs _ _ HEAP PARTS EC LHs HItems EHp) as (HP0 & HPC & HPM & HPX & _ & _). change BN_CTX_SZ with 72 in HPX.
        rewrite ?(nth_error_nth _ _ _ EHp) in CX.
        destruct (nth_error (gx_items c) (i / 16 - 1)) as [qp|] eqn:Eqp; [|exfalso; apply nth_error_None in Eqp; lia].
        pose proof (HItems _ _ Eqp) as HinP. rewrite (nth_error_nth _ _ _ EHp) in HinP. change ITEM_SZ with 400 in HinP.
        pose proof (AH_range _ _ _ _ _ _ _ HEAP HinP) as (_ & HP16 & _ & _ & _).
        assert (INP : In (qp, Hp, 400) (OW ++ LB)) by (apply in_or_app; left; exact HinP).
        pose proof (AH_acc_in _ _ _ _ (qp, Hp, 400) Hp 400 HEAP INP ltac:(cbn; lia) ltac:(cbn; lia)) as ACCP.
        assert (ALP : Hp mod 8 = 0) by (clear - HP16; Z.div_mod_to_equations; lia).
        assert (LNK : rw_cells bgbsegs m (Hp + 384) [C8 (wz (match (i / 16 - 1)%nat with O => 0 | S k' => nth k' Hs 0 end)); C8 (wz Hk)]).
        { replace Hk with (nth (S (i / 16 - 1)) Hs 0) by (replace (S (i / 16 - 1)) with (i / 16)%nat by lia; exact (nth_error_nth _ _ _ EHk)).
          exact (HLinks _ _ EHp). }
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          lazymatch type of MU with munch ?W0 _ _ =>
            apply (rw_cells_transport bgbsegs W0 m mx (Hp + 384)) in LNK; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; unfold BnHeapA.ACEIL in *; lia] end end.
        unfold MallocRep.wz in LNK.
        do 2 (ub; step). ub; shl. ub; chk0.
        ub; step. ub.
        ub; step. do 2 (ub; step). ub; shl_with ACCP ALP. ub; chk0.
        ub; shl. ub; chk0.
        ub; step. ub; step. ub; step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply evt_eq; [| eapply (CONT Hk mx); [reflexivity| exact CX| exact FR| exact ST| exact MU| exact WM| exact MI| exact (conj SHB1 SHB2)] ] end.
        rewrite ?EM. reflexivity.
  -
    replace (gx_pused c =? psize)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
    destruct (3 <=? length (gx_items c))%nat eqn:E3.
    { cbn [tbind fst snd]. apply evt_done. apply implA_unr. }
    apply Nat.leb_gt in E3. cbn [tbind fst snd].
    assert (IU : gx_pused c = gx_used c) by exact CE3.
    assert (IP : gx_pused c = psize) by lia.
    do 4 (ub; step). ub; step.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -112, bv_unsigned sp); (ac, ac + 72)]).
    { constructor; [left; cbn; lia|]. constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith| constructor]. }
    assert (HEAP1 : AHEAP Σ OW LB m1) by (exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))).
    assert (AXP1 : ax_pres LB (bv_unsigned sp) (XW PL) m m1) by (exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))).
    assert (LSC1 : lib_state_hc true [] ls m1 OW PL EA).
    { eapply (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP); [exact HEAP| exact LSC| exact MU| exact WM| exact FROK|].
      constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
      constructor; [apply w_cx; [reflexivity| intros x Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]| constructor]. }
    assert (STK1 : stack_rep m1 OW IX c).
    { eapply (stack_rep_keep Σ OW LB m m1 ls PL EA ac qc IX); [exact HEAP| exact PARTS| exact EC| exact STK| exact MU| exact WM|].
      constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia| constructor]. }
    assert (PM1 : links m1 Hs).
    { eapply (links_keep Σ OW LB m m1 ls PL EA ac qc Hs); [exact HEAP| exact PARTS| exact EC| exact LHs| exact HItems| exact HLinks| exact MU| exact WM|].
      constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia| constructor]. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -112) (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { apply (uw_push_frame m1 _ (bv_unsigned sp) 112 [CB 8 jbv; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
        [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
      - rewrite !Z_to_bv_bv_unsigned. exact FR.
      - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia |]. constructor; [|constructor].
        cbn. unfold BnHeapA.ACEIL in *. lia. }
    apply evt_done. unfold POOL_ITEM_BYTES.
    eapply (CRYPTO_malloc_walkA) with (n := 400) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
    + exact HEAP1.
    + rewrite ESP. exact ST.
    + exact CEIL.
    + rewrite ESP. unfold CRYPTO_MALLOC_STACK, RT_STACK. lia.
    + rewrite ESP. unfold USTACK_TOP. lia.
    + rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
    + exact MI.
    + exact (proj1 LSC1).
    + lia.
    + pose proof (cnt_ok_live ls OW LB OW 0 WFS CNT ltac:(lia) ltac:(lia)) as HL. rewrite length_map in HL. exact HL.
    + exact CRED.
    + rewrite ESP. exact UW1.
    + rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_cg_malloc CTX).
    + intros pn Σ1 ms1 FRESH PO. unfold calloc_postA in PO. rewrite ?ESP in PO.
      destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F1 & fc1 & m3 & An & -> & MI3 & ST3 & AG3 & CR3 & BR & HEAP3 & ACCN & (junkA & BLK)).
      rewrite (ret_pc_even 2260380) by lia.
      apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG3) in CX; [| intros x Hx; right; right; exists (qc, ac, 72); split; [exact INC| cbn in Hx |- *; lia]].
      assert (LSC3 : lib_state_hc true [] ls m3 OW PL EA).
      { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ (bv_unsigned sp + -112) (bv_unsigned sp) USTACK_TOP); [exact LSC1| exact FROK| lia| lia| exact AG3| | lb_in_heap].
        intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (STK3 : stack_rep m3 OW IX c).
      { eapply (stack_rep_heap_pres OW (OW ++ LB) (bv_unsigned sp + -112)); [| exact STK1| exact AG3]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (PM3 : links m3 Hs).
      { eapply (links_heap_pres ls OW (OW ++ LB) (bv_unsigned sp + -112)); [exact LHs| exact HItems| | exact PM1| exact AG3].
        intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (AXP3 : ax_pres LB (bv_unsigned sp) (XW PL) m m3).
      { eapply ax_pres_trans; [exact AXP1|]. eapply agree_on_mono; [exact AG3|]. intros x [_ [Hx|[Hx|(b0 & Hb0 & Hr)]]];
          [left; lia | right; left; exact Hx | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]]. }
      pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
      assert (EAn : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
      set (OW1 := (pn, An, 400) :: OW) in *.
      assert (ND1 : List.NoDup (map blk_id OW1)) by (exact (AH_nodup_l _ _ _ _ HEAP3)).
      assert (FRESHA : ~ In pn (all_ids ls PL EA)).
      { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
      assert (NEWSEP : forall q A n, In (q, A, n) OW -> An + 400 <= A \/ A + n <= An).
      { intros q A n Hq. assert (NE : pn <> q) by (intros ->; apply FRESH; rewrite map_app; apply in_or_app; left; apply (in_map blk_id) in Hq; exact Hq).
        exact (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hq) NE). }
      pose proof (NEWSEP _ _ _ BC) as SEPc.
      assert (LSC3' : lib_state_hc true [] ls m3 OW1 PL EA) by (eapply lib_state_h_ow; [exact LSC3|]; intros q A n _ Hq; right; exact Hq).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LSC3') as PARTS1.
      assert (STK3' : stack_rep m3 OW1 IX c) by (eapply stack_rep_ow; [| exact STK3]; intros b0 Hb0; right; exact Hb0).
      assert (HItems1 : item_blocks ls OW1 Hs) by (eapply item_blocks_ow; [exact HItems| intros b0 Hb0; right; exact Hb0]).
      assert (INC1 : In (qc, ac, 72) (OW1 ++ LB)) by (apply in_or_app; left; right; exact BC).
      assert (INN1 : In (pn, An, 400) (OW1 ++ LB)) by (apply in_or_app; left; left; reflexivity).

      assert (HR : forall j H, nth_error Hs j = Some H ->
                0 < H /\ H + 400 <= ACEIL /\ (H + 400 <= 0x10000 \/ 0xbf9000 <= H) /\ (H + 400 <= ac \/ ac + 72 <= H) /\ (An + 400 <= H \/ H + 400 <= An) /\ H mod 8 = 0
                /\ (exists q, nth_error (gx_items c) j = Some q /\ In (q, H, 400) OW)
                /\ (forall j' H', nth_error Hs j' = Some H' -> j' <> j -> H + 400 <= H' \/ H' + 400 <= H)).
      { intros j H Hj. pose proof (item_facts Σ OW LB m ls PL EA ac qc Hs _ _ HEAP PARTS EC LHs HItems Hj) as (F0 & FC & FM & FX & FK & FI). change BN_CTX_SZ with 72 in FX.
        split; [exact F0|]. split; [exact FC|]. split; [exact FM|]. split; [exact FX|].
        assert (Hj' : (j < length (gx_items c))%nat) by (rewrite <- LHs; apply nth_error_Some; congruence).
        destruct (nth_error (gx_items c) j) as [qj|] eqn:Eqj; [|apply nth_error_None in Eqj; lia].
        pose proof (HItems j qj Eqj) as Hin. rewrite (nth_error_nth _ _ _ Hj) in Hin. change ITEM_SZ with 400 in Hin.
        pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & B16 & _ & _ & _).
        split; [exact (NEWSEP _ _ _ Hin)|]. split; [clear - B16; Z.div_mod_to_equations; lia|]. split; [exists qj; split; [reflexivity| exact Hin]| exact FK]. }

      assert (SPLIT : rw_cells bgbsegs m3 An ([CB 384 (firstn 384 junkA)] ++ [CB 16 (skipn 384 junkA)])).
      { pose proof BLK as [[[LJ _] _] _]. cbn in LJ.
        eapply bk_rw_cells_recast; [exact BLK| | |].
        - cbn. rewrite length_firstn, length_skipn. lia.
        - cbn. rewrite !app_nil_r. apply firstn_skipn.
        - cbn. lia. }
      apply bk_rw_cells_app in SPLIT. destruct SPLIT as [B1 B2]. cbn [cells_size csize Nat.add] in B2. change (Z.of_nat 384) with 384 in B2. clear BLK B1.
      clear ACC MU WM OFF SHB1 SHB2.
      unfold MallocRep.wz in *.
      apply implA_from_evt.
      ub; step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EAn in KA; lia|]. clear KA.
      ub; step.
      ub.
      ub; zstep. rewrite ?(unsigned_lit 0) by lia. change (Z.land 0 8) with 0.
      ub; zstep.
      ub.
      ub; zstep.
      setreg 27%Z (Z_to_bv 64 18446744073709551592) ltac:(apply Z_to_bv_eqm; reflexivity).
      setreg 26%Z (Z_to_bv 64 (Z.of_nat 16)) ltac:(reflexivity).
      apply evt_done.
      eapply implA_step_same.
      { eapply (get_init_loopA 15) with (P := An) (bd := (pn, An, 400)) (lo := lo) (OW := OW1) (LB := LB); try reflexivity.
        - exact HEAP3.
        - rewrite ESP. exact ST3.
        - exact CEIL.
        - rewrite ESP. unfold BN_INIT_STACK, RT_STACK. lia.
        - rewrite ESP. unfold USTACK_TOP. lia.
        - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
        - exact MI3.
        - exact INN1.
        - cbn [blk_addr blk_size fst snd]. lia. }
      intros ms5 PO. unfold init_loop_postA in PO. rewrite ?ESP in PO.
      destruct PO as (ra5 & w0 & w1 & w2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F5 & fc5 & m5 & -> & MI5 & ST5 & HEAP5 & WM5 & AG5 & ZR16).
      change (24 * Z.of_nat 16) with 384 in *. change (24 * 16)%nat with 384%nat in ZR16. unfold MallocRep.wz.
      apply (rw_cells_agree _ _ _ _ _ AG5) in FR; [| intros x Hx; cbn in Hx; split; [left; unfold USTACK_TOP; lia | unfold BnHeapA.ACEIL in *; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG5) in CX; [| intros x Hx; cbn in Hx; split; [right; right; exists (qc, ac, 72); split; [exact INC1| cbn; lia] | lia]].
      apply (rw_cells_agree _ _ _ _ _ AG5) in B2; [| intros x Hx; cbn in Hx; split; [right; right; exists (pn, An, 400); split; [exact INN1| cbn; lia] | lia]].
      assert (LSC5 : lib_state_hc true [] ls m5 OW1 PL EA).
      { eapply (lib_state_h_icall Σ1 LB [] ls m3 m5 OW1 PL EA (bv_unsigned sp + -112) (bv_unsigned sp) An 384 HEAP3 LSC3' FROK ltac:(lia) AG5).
        eapply (w_foreign OW1 LB ls PL EA (bv_unsigned sp) true [] _ pn An 400); [first [eassumption | left; reflexivity | right; eassumption] | exact FRESHA | cbn; lia | cbn; lia]. }
      assert (STK5 : stack_rep m5 OW1 IX c).
      { eapply (stack_rep_agreeP OW1 (OW1 ++ LB) (bv_unsigned sp + -112)); [| exact STK3'| exact AG5|].
        - intros b0 Hb0. apply in_or_app. left. exact Hb0.
        - intros q _ HinI x Hx HI. split; [exact Hx|]. intros HAn.
          destruct HinI as [E|HinI]; [injection E as -> -> ; lia|]. pose proof (NEWSEP _ _ _ HinI) as SEPi. lia. }
      assert (PM5 : links m5 Hs).
      { intros k H Hk. destruct (HR k H Hk) as (F0 & FC & FM & FX & FN & FA & (qj & Eqj & Hin) & FK).
        eapply rw_cells_agree; [exact AG5| exact (PM3 k H Hk)|]. intros x Hx. cbn in Hx. split; [|lia].
        right; right. exists (qj, H, 400). split; [apply in_or_app; left; right; exact Hin|]. cbn [blk_addr blk_size fst snd]. lia. }
      assert (AXP5 : ax_pres LB (bv_unsigned sp) (XW PL) m m5).
      { eapply ax_pres_trans; [exact AXP3|]. eapply agree_on_mono; [exact AG5|]. intros x [_ Hc]. split.
        - destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]]; [left; lia | right; left; exact Hc | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]].
        - intros HAr. destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]].
          + unfold BnHeapA.ACEIL in *. lia.
          + eapply (blk_not_static Σ1 OW1 LB m3 (pn, An, 400) x HEAP3 ltac:(left; reflexivity)); [cbn; lia | exact Hc].
          + assert (NE : blk_id b0 <> pn).
            { intros E. apply FRESH. rewrite <- E. apply in_map. apply in_or_app. right. exact Hb0. }
            pose proof (AH_disjoint_gen _ _ _ _ b0 (pn, An, 400) HEAP3 (in_or_app _ _ _ (or_intror Hb0)) INN1 NE) as DJ. cbn in DJ. lia. }
      assert (SPLZ : rw_cells bgbsegs m5 An (bn_cells 0 (bn_nil 0) ++ [CB 360 (repeat (Z_to_bv 8 0) 360)])).
      { eapply bk_rw_cells_recast; [exact ZR16| | |].
        - cbn [bn_cells app cells_wf cell_wf]. rewrite repeat_length. tauto.
        - vm_compute. reflexivity.
        - reflexivity. }
      apply bk_rw_cells_app in SPLZ. destruct SPLZ as [BN0 ZR]. cbn [bn_cells cells_size csize Nat.add] in ZR. change (Z.of_nat 24) with 24 in ZR.
      unfold bn_cells in BN0. clear ZR16.
      pose proof (AH_acc_in _ _ _ _ (qc, ac, 72) ac 72 HEAP5 INC1 ltac:(cbn; lia) ltac:(cbn; lia)) as ACC5.
      pose proof (AH_acc_in _ _ _ _ (pn, An, 400) An 400 HEAP5 INN1 ltac:(cbn; lia) ltac:(cbn; lia)) as ACCN5.
      assert (ALN : An mod 8 = 0) by (clear - BA16; Z.div_mod_to_equations; lia).
      pose proof (AH_offsh _ _ _ _ (pn, An, 400) HEAP5 INN1) as ON. cbn [blk_addr blk_size fst snd] in ON. unfold SHLO, SHHI in ON.
      destruct (AH_shb _ _ _ _ HEAP5) as (SHB51 & SHB52).
      assert (N47 : 0 < An /\ An + 400 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; lia).
      unfold MallocRep.wz in *.
      apply implA_from_evt.
      lazymatch goal with |- evt _ ?Q _ => remember Q as QQ eqn:EQQ end.

      assert (CONTB : forall (WX : list (Z * Z)) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (mX : mem),
        sub_fp [(bv_unsigned sp - 128, bv_unsigned sp); (An, An + 24); (ac, ac + 72)]%Z WX ->
        Forall (w_lib ls OW1 PL lo (bv_unsigned sp)) WX ->
        Forall (w_okc OW1 LB ls PL EA (bv_unsigned sp) true []) WX ->
        Forall (fun iv : Z * Z => ACEIL <= fst iv \/ (ac <= fst iv /\ snd iv <= ac + BN_CTX_SZ)
                                  \/ (exists q A n, In (q, A, n) (OW1 ++ LB) /\ A <= fst iv /\ snd iv <= A + n /\ Some q <> gx_indexes (st_ctx ls))) WX ->
        (forall k H, nth_error Hs k = Some H -> (S k < length Hs)%nat -> disjoint_from WX (H + 384) 16) ->
        munch WX m5 mX -> wmono bgbsegs m5 mX -> mem_inv bgbsegs mX ->
        rw_cells bgbsegs mX ac
          [C8 (Z_to_bv 64 (hd 0 (Hs ++ [An]))); C8 (Z_to_bv 64 An); C8 (Z_to_bv 64 An); C4 (Z_to_bv 64 (Z.of_nat (gx_pused c))); C4 (Z_to_bv 64 (Z.of_nat psize)); C8 (Z_to_bv 64 IX);
           C4 (Z_to_bv 64 (Z.of_nat (length (gx_frames c)))); C4 (Z_to_bv 64 (Z.of_nat (gx_ssize c))); C4 (Z_to_bv 64 (Z.of_nat (gx_used c)));
           C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
        rw_cells bgbsegs mX (bv_unsigned sp + -112) [CB 8 jbv; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk bgbsegs mX lo (bv_unsigned sp + -112) ->
        shb_cells bgbsegs 6147864 6945336 mX -> acc bgbsegs mX ac 72 -> acc bgbsegs mX An 24 ->
        rw_cells bgbsegs mX An [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 (Z.of_nat (bn_top (bn_nil 0 : bignum bptr)))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax (bn_nil 0 : bignum bptr))));
                               C4 (Z_to_bv 64 (Z.b2z (bn_neg (bn_nil 0 : bignum bptr)))); C4 (Z_to_bv 64 (bn_flags (bn_nil 0 : bignum bptr)))] ->
        rw_cells bgbsegs mX (An + 24) [CB 360 (repeat (Z_to_bv 8 0) 360)] ->
        rw_cells bgbsegs mX (An + 384) [C8 (Z_to_bv 64 (last Hs 0)); C8 (Z_to_bv 64 0)] ->
        (forall k H, nth_error Hs k = Some H -> S k = length Hs ->
           rw_cells bgbsegs mX (H + 384) [C8 (Z_to_bv 64 (match k with O => 0 | S k' => nth k' Hs 0 end)); C8 (Z_to_bv 64 An)]) ->
        evt bgbsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 TP_A) y5 y6 y7 sp (Z_to_bv 64 ac)
                              y10 y11 y12 y13 y14 y15 y16 y17
                              (Z_to_bv 64 (ac + 24)) (Z_to_bv 64 An) (Z_to_bv 64 (ac + 28)) (Z_to_bv 64 (An + 384))
                              (Z_to_bv 64 SHB) (Z_to_bv 64 ((ac + 24) ≫ 3 + SHB)) (Z_to_bv 64 ((ac + 28) ≫ 3 + SHB))
                              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 18446744073709551592) y28 y29 y30 y31)
                         F5 (Z_to_bv 64 0x227fcc) fc5 None mX (seg_rom bgbsegs))).
      { intros WX y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 mX SUB HWLX HWOK HWST HWLK MUX WMX MIX CXX FRX STX (SHX1 & SHX2) ACCX ACCNX BNX ZRX LNX LTX.
        clear B2 BN0 ZR CX FR ST5 MI5 SHB51 SHB52 ACC5 ACCN5.
        change (munch WX m5 mX) with (id (munch WX m5 mX)) in MUX.
        pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (An, An + 24); (ac, ac + 72)]%Z mX) as MUc. pose proof (wmono_refl bgbsegs mX) as WMc.
        assert (OFFc : offshW [(bv_unsigned sp - 128, bv_unsigned sp); (An, An + 24); (ac, ac + 72)]).
        { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
        ub; shl. ub; chk0. ub; step. rewrite (sx32_small (Z.of_nat psize)) by lia. do 2 (ub; step).
        ub; shl. ub; chk0. ub; step. rewrite (sx32_small (Z.of_nat (gx_pused c))) by lia. do 2 (ub; step).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
        assert (ACCN7 : acc bgbsegs m7 An 24) by (eapply (acc_munch bgbsegs _ mX m7 _ _ ACCNX MUc OFFc); unfold BnHeapA.ACEIL in *; lia).
        assert (ACCC7 : acc bgbsegs m7 ac 72) by (eapply (acc_munch bgbsegs _ mX m7 _ _ ACCX MUc OFFc); unfold BnHeapA.ACEIL in *; lia).
        apply rw_cells_CB8_hd in FRX.
        eapply evt_cut.
        { eapply (get_tailA) with (lo := lo) (CTX := ac) (A := An) (D := 0) (b := bn_nil 0) (used := Z.of_nat (gx_used c));
            [exact BNX | cbn; lia | exact CXX | lia | exact FRX | exact STX | unfold BnHeapA.ACEIL in *; lia | eassumption
            | unfold BnHeapA.ACEIL in *; lia | unfold BnHeapA.ACEIL in *; lia | lia | unfold BnHeapA.ACEIL in *; lia
            | exact (conj SHX1 SHX2) | exact ACCN7 | exact ALN | exact ACCC7 | exact AL
            | unfold SHHI, BnHeapA.ACEIL in *; lia | unfold SHLO, SHHI; lia | unfold SHLO, SHHI; lia | unfold BnHeapA.ACEIL in *; lia ]. }
        intros ms' PO. unfold get_tail_postA in PO.
        destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & mF & -> & MUt & WMt & MIt & STt & BNt & CXt).
        subst QQ. apply evt_done. cbn [tbind fst snd]. apply implA_ret.
        set (c2 := mkGx (gx_items c ++ [pn]) (Some (length (gx_items c))) (S (gx_pused c)) (gx_indexes c) (gx_frames c) (gx_ssize c) (S (gx_used c)) 0%nat false).
        set (stF := mkST (st_bns ls ++ repeat (bn_nil 0) BN_CTX_POOL_SIZE) c2 (st_ri ls) (st_n0 ls) (st_rbits ls) (st_rshift ls)).
        lazymatch goal with |- context [(RPool (gx_pused c), ?stM)] =>
          assert (ESTF : stM = stF);
          [| rewrite ESTF] end.
        { subst stF c2. unfold set_ctx, setbn, set_bns, getbn. cbn [st_bns st_ctx st_ri st_n0 st_rbits st_rshift gx_items gx_current gx_pused gx_indexes gx_frames gx_ssize gx_used].
          f_equal.
          set (L := st_bns ls ++ repeat (bn_nil 0) BN_CTX_POOL_SIZE).
          assert (EN : nth (RPool (gx_pused c)) L (bn_nil 0) = bn_nil 0).
          { subst L. rewrite app_nth2 by (rewrite EL, IP; subst psize; unfold RPool; lia). apply nth_repeat. }
          transitivity (list_set L (RPool (gx_pused c)) (nth (RPool (gx_pused c)) L (bn_nil 0))); [| apply list_set_nth_id].
          f_equal. rewrite EN. reflexivity. }
        assert (MUcF : munch [(bv_unsigned sp - 128, bv_unsigned sp); (An, An + 24); (ac, ac + 72)]%Z mX mF).
        { eapply munch_trans; [exact MUc|]. first [exact MUt | eapply munch_weaken; [|exact MUt]; intros xx Hx; cbn [outside] in *; clear - Hx; intuition lia]. }
        assert (WMcF : wmono bgbsegs mX mF) by (eapply wmono_trans; eassumption).
        assert (MUF : munch WX m5 mF).
        { unfold id in MUX. eapply munch_trans; [exact MUX|]. eapply munch_weaken; [exact SUB| exact MUcF]. }
        assert (WMF : wmono bgbsegs m5 mF) by (eapply wmono_trans; eassumption).
        assert (HinN : In (pn, An, 400) OW1) by (left; reflexivity).
        assert (BC1 : In (qc, ac, 72) OW1) by (right; exact BC).
        assert (LSF : lib_state stF mF OW1 PL EA).
        { unfold lib_state. eapply (lib_state_cx_close_newitem [] ls stF mF OW1 PL EA Hs IX pn An ac qc);
            [| exact ND1| exact EC| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| | exact FRESHA| exact HinN| |].
          - eapply (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP); [exact HEAP5| exact LSC5| exact MUF| exact WMF| exact FROK| exact HWOK].
          - unfold st_wf. subst stF c2. cbn [st_bns st_ctx gx_items]. split; [|split; [|split]].
            + rewrite !length_app, repeat_length, EL. cbn [length]. lia.
            + intros r Hr NE1. unfold getbn. cbn [st_bns]. rewrite length_app, repeat_length in Hr.
              destruct (Nat.lt_ge_cases r (length (st_bns ls))) as [LT|GE].
              * rewrite app_nth1 by exact LT. apply BOK; [exact LT| exact NE1].
              * rewrite app_nth2 by exact GE. rewrite nth_repeat. apply bg_ok_nil. left. reflexivity.
            + unfold getbn. cbn [st_bns]. rewrite app_nth1 by (rewrite EL; unfold ROne, NFIX; lia). exact EONE.
            + unfold ctx_wf. cbn [gx_items gx_current gx_pused gx_indexes gx_frames gx_ssize gx_used gx_err_stack gx_too_many].
              split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
              split; [rewrite length_app; cbn [length]; subst psize; unfold BN_CTX_POOL_SIZE in *; lia|].
              split; [rewrite length_app; cbn [length]; lia|].
              split. { cbn [Nat.eqb]. f_equal. rewrite <- IU, IP. subst psize. unfold BN_CTX_POOL_SIZE. rewrite Nat.sub_succ, Nat.sub_0_r. symmetry. apply div16_mul. }
              split; [eapply nondecr_last_incr; [exact CE7| lia]| exact CE8].
          -
            assert (JOIN : rw_cells bgbsegs mF An (bn_cells 0 (bn_zero_pure (bn_nil 0)) ++ [CB 360 (repeat (Z_to_bv 8 0) 360)])).
            { apply bk_rw_cells_app. split; [exact BNt|]. cbn [bn_cells cells_size csize Nat.add]. change (Z.of_nat 24) with 24.
              eapply rw_cells_transport; [exact ZRX| exact MUt| exact WMt|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SEPc BAC CEIL LO SPR. unfold BnHeapA.ACEIL in *. lia. }
            eapply bk_rw_cells_recast; [exact JOIN| cbn [cells_wf cell_wf]; rewrite repeat_length; tauto| vm_compute; reflexivity| reflexivity].
          - apply (cx_view_some _ _ _ _ _ _ _ _ EC). subst stF. cbn [st_ctx]. split; [exact BC1|].
            split; [subst c2; cbn [gx_items]; rewrite !length_app; cbn [length]; lia|].
            split; [|split; [|split]].
            + unfold ctx_cells, cur_addr. subst c2. cbn [gx_items gx_current gx_pused gx_frames gx_ssize gx_used gx_err_stack gx_too_many Z.b2z].
              rewrite length_app. cbn [length]. rewrite <- LHs, nth_middle, last_last. unfold MallocRep.wz.
              rewrite !Nat2Z.inj_succ. unfold Z.succ.
              replace (Z.of_nat (BN_CTX_POOL_SIZE * (length Hs + 1))) with (Z.of_nat psize + 16) by (subst psize; rewrite LHs; unfold BN_CTX_POOL_SIZE; lia).
              exact CXt.
            + apply (stack_rep_same mF OW1 IX c c2); [reflexivity| reflexivity| reflexivity|].
              eapply (stack_rep_keep Σ1 OW1 LB m5 mF ls PL EA ac qc IX WX); [exact HEAP5| exact PARTS1| exact EC| exact STK5| exact MUF| exact WMF| exact HWST].
            + intros k q Hk. subst c2. cbn [gx_items] in Hk.
              destruct (Nat.lt_ge_cases k (length (gx_items c))) as [LT|GE].
              * rewrite nth_error_app1 in Hk by exact LT. rewrite app_nth1 by (rewrite LHs; exact LT). right. exact (HItems k q Hk).
              * rewrite nth_error_app2 in Hk by exact GE.
                destruct (k - length (gx_items c))%nat as [|kk] eqn:EKK; [|destruct kk; discriminate Hk].
                cbn [nth_error] in Hk. injection Hk as <-. assert (k = length Hs) as -> by lia. rewrite nth_middle. exact HinN.
            + apply links_snoc.
              * intros k H Hk HSk. eapply rw_cells_transport; [exact (PM5 k H Hk)| exact MUF| exact WMF| cbn [cells_size csize Nat.add]; exact (HWLK k H Hk HSk)].
              * intros k H Hk HSk. destruct (HR k H Hk) as (F0 & FC & _ & FX & FN & _).
                eapply rw_cells_transport; [exact (LTX k H Hk HSk)| exact MUcF| exact WMcF|]. cbn [disjoint_from cells_size csize Nat.add]. clear - F0 FC FX FN CEIL LO SPR. unfold BnHeapA.ACEIL in *. lia.
              * eapply rw_cells_transport; [exact LNX| exact MUt| exact WMt|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SEPc BAC CEIL LO SPR. unfold BnHeapA.ACEIL in *. lia. }
        unfold bn_postA. do 17 eexists. exists mF, OW1, PL. split; [reflexivity|]. cbn [fst snd].
        split; [exact (seg_heap Σ1 ls OW1 LB PL EA _ m5 mF _ lo _ HEAP5 PARTS1 FROK MUF WMF HWLX CEIL ltac:(unfold USTACK_TOP; lia))|]. split; [exact LSF|].
        split; [exact STt|]. split; [exact MIt|].
        split. { eapply ax_pres_trans; [exact AXP5|]. exact (seg_ax_pres' Σ1 ls OW1 LB PL EA _ m5 mF _ lo _ HEAP5 PARTS1 FROK MUF HWLX CEIL ltac:(lia)). }
        split; [exact CR3|].
        split. { unfold cnt_eq, cnt_bal, blocks_of. subst stF c2. cbn [st_bns st_ctx gx_items gx_indexes]. fold c.
                 rewrite map_app, concat_app, (map_app _ (gx_items c) [pn]), !length_app.
                 change (length (bn_blocks (bn_nil 0 : bignum bptr))) with 0%nat.
                 unfold OW1. cbn [map length]. lia. }
        split. { eapply (refs_stable_intro _ _ _ _ [pn]); [subst stF c2; reflexivity|]. intros q H0 _ Hq. right. exact Hq. }
        split; [reflexivity|]. split; [eexists; reflexivity|]. split; [|intros q0 A0 n0 Hq0; right; exact Hq0].
        exists An. split; [|reflexivity].
        apply ref_at_pool. exists pn, An. subst stF c2. cbn [st_ctx gx_items].
        split. { rewrite IP. subst psize. unfold BN_CTX_POOL_SIZE. rewrite div16_mul. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
        split; [exact HinN|]. rewrite IP. subst psize. unfold BN_CTX_POOL_SIZE. rewrite mod16_mul. lia. }

      pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp); (ac, ac + 72); (An, An + 400)]%Z m5) as MU5.
      pose proof (wmono_refl bgbsegs m5) as WMr5.
      assert (OFF5 : offshW [(bv_unsigned sp + -128, bv_unsigned sp); (ac, ac + 72); (An, An + 400)]).
      { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
      do 3 (ub; step). ub; shl. ub; chk0.
      do 3 (ub; step). rewrite ?(unsigned_lit (An + 384)) by (unfold BnHeapA.ACEIL in *; lia).
      ub; shl. ub; chk0.
      ub; step.
      do 2 (ub; step). rewrite ?(unsigned_lit (An + 392)) by (unfold BnHeapA.ACEIL in *; lia).
      ub; step.
      ub; step. ub; shl. ub; chk0.
      ub; step.
      do 2 (ub; step). ub; shl. ub; chk0.
      ub; step.
      ub; step. if_cases KH; zify_cond KH.
      *
        assert (EHS : Hs = []).
        { destruct Hs as [|h0 Hs']; [reflexivity| exfalso]. destruct (HR 0%nat h0 eq_refl) as (F0 & FC & _). cbn [hd] in KH.
          change 18446744073709551615 with (Z.ones 64) in KH. rewrite Z.land_ones, Z.mod_small in KH by (unfold BnHeapA.ACEIL in *; lia). lia. }
        ub; shl. ub; chk0. ub; step.
        do 3 (ub; step). ub; shl. ub; chk0. ub; step.
        ub; shl. ub; chk0. ub; step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply (CONTB [(bv_unsigned sp + -128, bv_unsigned sp); (ac, ac + 72); (An, An + 400)]%Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx);
            [ | | | | | exact MU5| exact WMr5| eassumption| | exact FR| exact ST5| exact (conj SHB51 SHB52)| | | exact BN0| exact ZR| | ] end.
        -- intros xx Hx. cbn [outside] in *. clear - Hx. intuition lia.
        -- constructor; [left; cbn; lia|]. constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith|].
           constructor; [right; left; exists (pn, An, 400); cbn; auto with zarith| constructor].
        -- constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
           constructor; [apply w_cx; [reflexivity| intros x' Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]|].
           constructor; [|constructor].
           eapply (w_foreign OW1 LB ls PL EA (bv_unsigned sp) true [] _ pn An 400); [first [eassumption | left; reflexivity | right; eassumption] | exact FRESHA| cbn; lia| cbn; lia].
        -- constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia|]. constructor; [|constructor].
           right; right. exists pn, An, 400. split; [exact INN1|]. cbn [fst snd]. split; [lia|]. split; [lia|].
           intros E. apply FRESHA. unfold all_ids. apply in_or_app; right; apply in_or_app; right. apply idx_in_m. symmetry. exact E.
        -- intros k H Hk HSk. rewrite EHS in HSk. cbn in HSk. lia.
        -- try rewrite EHS in CX. rewrite ?EHS. cbn [hd app last] in CX |- *. exact CX.
        -- eapply (acc_munch bgbsegs _ m5 _ _ _ ACC5 MU5 OFF5); unfold BnHeapA.ACEIL in *; lia.
        -- eapply (acc_munch bgbsegs _ m5 _ _ _ (acc_sub bgbsegs m5 An 400 An 24 ACCN5 ltac:(lia) ltac:(lia)) MU5 OFF5); unfold BnHeapA.ACEIL in *; lia.
        -- first [exact B2 | rewrite EHS in B2 |- *; cbn [last] in B2 |- *; exact B2].
        -- intros k H Hk HSk. rewrite EHS in Hk. destruct k; discriminate Hk.
      *
        assert (NHS : Hs <> []) by (intros E; rewrite E in KH; cbn [hd] in KH; rewrite Z.land_0_l in KH; lia).
        destruct (nth_error Hs (length Hs - 1)) as [T|] eqn:ET; [|exfalso; apply nth_error_None in ET; destruct Hs; [congruence| cbn in ET; lia]].
        assert (ELT : last Hs 0 = T) by (rewrite last_nth by exact NHS; exact (nth_error_nth _ _ _ ET)).
        destruct (HR _ _ ET) as (T0 & TC & TM & TX & TN & TAL & (qT & EqT & HinT0) & TK).
        assert (HinT : In (qT, T, 400) OW1) by (right; exact HinT0).
        assert (INT1 : In (qT, T, 400) (OW1 ++ LB)) by (apply in_or_app; left; exact HinT).
        pose proof (AH_acc_in _ _ _ _ (qT, T, 400) T 400 HEAP5 INT1 ltac:(cbn; lia) ltac:(cbn; lia)) as ACCT5.
        pose proof (AH_offsh _ _ _ _ (qT, T, 400) HEAP5 INT1) as OT. cbn [blk_addr blk_size fst snd] in OT. unfold SHLO, SHHI in OT.
        assert (LNKT : rw_cells bgbsegs m5 (T + 384) [C8 (Z_to_bv 64 (match (length Hs - 1)%nat with O => 0 | S k' => nth k' Hs 0 end)); C8 (Z_to_bv 64 0)]).
        { pose proof (PM5 _ _ ET) as L. rewrite (nth_overflow Hs (n := S (length Hs - 1)) 0) in L by (clear; lia). exact L. }
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          lazymatch type of MU5 with munch ?W0 _ _ =>
            apply (rw_cells_transport bgbsegs W0 m5 mx (T + 384)) in LNKT; [| exact MU5| exact WMr5| cbn [disjoint_from cells_size csize Nat.add]; clear - T0 TC TX TN CEIL LO SPR; unfold BnHeapA.ACEIL in *; lia] end end.
        apply (munch_weaken _ [(bv_unsigned sp + -128, bv_unsigned sp); (ac, ac + 72); (An, An + 400); (T + 384, T + 400)]%Z) in MU5;
          [| intros xx Hx; cbn [outside] in Hx |- *; clear - Hx; tauto].
        assert (OFF5T : offshW [(bv_unsigned sp + -128, bv_unsigned sp); (ac, ac + 72); (An, An + 400); (T + 384, T + 400)]).
        { cbn [offshW] in OFF5 |- *. destruct OFF5 as (O1 & O2 & O3 & _). split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [|exact I]. unfold SHLO, SHHI. clear - OT. lia. }
        rewrite ELT.
        ub; step. do 2 (ub; step). ub; shl_with ACCT5 TAL. ub; chk0. ub; step.
        ub; shl_with ACC5 AL. ub; chk0. ub; step.
        do 3 (ub; step). ub; shl_with ACC5 AL. ub; chk0. ub; step.
        ub; step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply (CONTB [(bv_unsigned sp + -128, bv_unsigned sp); (ac, ac + 72); (An, An + 400); (T + 384, T + 400)]%Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx);
            [ | | | | | exact MU5| exact WMr5| eassumption| | exact FR| exact ST5| exact (conj SHB51 SHB52)| | | exact BN0| exact ZR| | ] end.
        -- intros xx Hx. cbn [outside] in *. clear - Hx. intuition lia.
        -- constructor; [left; cbn; lia|]. constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith|].
           constructor; [right; left; exists (pn, An, 400); cbn; auto with zarith|].
           constructor; [right; left; exists (qT, T, 400); cbn; split; [exact HinT| lia]| constructor].
        -- constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
           constructor; [apply w_cx; [reflexivity| intros x' Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]|].
           constructor; [eapply (w_foreign OW1 LB ls PL EA (bv_unsigned sp) true [] _ pn An 400); [first [eassumption | left; reflexivity | right; eassumption] | exact FRESHA| cbn; lia| cbn; lia]|].
           constructor; [|constructor].
           apply w_cx; [reflexivity|]. intros x' Hx. right; left. exists qT, T. cbn in Hx. split; [eapply nth_error_In; exact EqT|]. split; [exact HinT|]. lia.
        -- constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia|].
           constructor. { right; right. exists pn, An, 400. split; [exact INN1|]. cbn [fst snd]. split; [lia|]. split; [lia|].
                          intros E. apply FRESHA. unfold all_ids. apply in_or_app; right; apply in_or_app; right. apply idx_in_m. symmetry. exact E. }
           constructor; [|constructor].
           right; right. exists qT, T, 400. split; [exact INT1|]. cbn [fst snd]. split; [lia|]. split; [lia|].
           fold c. intros E. eapply (ids_item_idx_neq ls qT qT); [eapply ids_m_nodup; exact IDS| eapply nth_error_In; exact EqT| symmetry; exact E| reflexivity].
        -- intros k H Hk HSk. cbn [disjoint_from]. destruct (HR k H Hk) as (F0 & FC & _ & FX & FN & _ & _ & FK).
           specialize (FK _ _ ET ltac:(lia)). clear - F0 FC FX FN FK CEIL LO SPR. unfold BnHeapA.ACEIL in *. lia.
        -- replace (hd 0 (Hs ++ [An])) with (hd 0 Hs) by (destruct Hs; [congruence| reflexivity]). first [exact CX | rewrite <- ELT; exact CX | rewrite ELT in CX |- *; exact CX].
        -- eapply (acc_munch bgbsegs _ m5 _ _ _ ACC5 MU5 OFF5T); unfold BnHeapA.ACEIL in *; lia.
        -- eapply (acc_munch bgbsegs _ m5 _ _ _ (acc_sub bgbsegs m5 An 400 An 24 ACCN5 ltac:(lia) ltac:(lia)) MU5 OFF5T); unfold BnHeapA.ACEIL in *; lia.
        -- first [exact B2 | rewrite <- ELT; exact B2 | rewrite ELT; exact B2].
        -- intros k H Hk HSk. replace k with (length Hs - 1)%nat in * by lia. rewrite ET in Hk. injection Hk as EKT. rewrite <- ?EKT. first [exact LNKT | rewrite ?EKT; exact LNKT].
Qed.

End WithRT.
