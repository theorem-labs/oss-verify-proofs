(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel AtpModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit F_memcpy Atp_h_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition push_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B : Z) (V : Z) (xd xl cap size : Z) (els : list (Z * Z)) (m : mem)
    (v' : @vec bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A' cap' : Z) (blk' : option bptr) (jr' : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ v' = (cap', size + 1, blk') /\ (cap' = (if size <? cap then cap else vcap_next cap size)) /\ blk' <> None
    /\ mem_inv psegs m' /\ stk psegs m' lo q /\ rw_cells psegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (vblocks blk' A' cap' ++ LB0) m'
    /\ vrep m' V A' v' (els ++ [(xd, xl)]) jr'
    /\ lx_pres LB0 q [(V, V + 24)] m m'.

Lemma signed_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite zb_signed. rewrite unsigned_lit by lia. replace (z <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma shiftr_16_4 : forall c, 0 <= c -> Z.shiftr (16 * c) 4 = c.
Proof. intros c Hc. rewrite Z.shiftr_div_pow2 by lia. replace (16 * c) with (c * 2^4) by lia. apply Z.div_mul. lia. Qed.
Lemma shiftr_16_3 : forall c, 0 <= c -> Z.shiftr (16 * c) 3 = 2 * c.
Proof. intros c Hc. rewrite Z.shiftr_div_pow2 by lia. replace (16 * c) with (2 * c * 2^3) by lia. apply Z.div_mul. lia. Qed.
Lemma land_ones64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. rewrite <- unsigned_lit_land. apply unsigned_lit. lia. Qed.
Lemma shiftr_small0 : forall x n, 0 <= x < 2^n -> 0 <= n -> Z.shiftr x n = 0.
Proof. intros x n Hx Hn. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Definition alloc_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (p : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) A junk,
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo q
    /\ rw_cells psegs m' LX_ERRNO [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB q m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ rblock_range A (16 * n)
    /\ RHEAP s' ((p, A, 16 * n) :: LB) m'
    /\ rw_cells psegs m' A [CB (Z.to_nat (16 * n)) junk].

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma allocate_spec : forall (ra gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q n lo B : Z) (errv : word),
    RHEAP s LB m -> rauxv_ok m B -> q <= B ->
    stk psegs m lo q -> alloc_ceiling <= lo -> lo <= q - (32 + RMALLOC_STACK) ->
    rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m -> 0 <= q < 2^64 -> 1 <= n -> 16 * n < 2^32 ->
    implM psegs (newnt lops (16 * n)) s
          (alloc_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ATP_ALLOCATE) fc None m (seg_rom psegs)).
  Proof.
    intros until errv. intros HEAP AUX QB ST CEIL LO ERR MI Hq N1 N2.
    unfold ATP_ALLOCATE, RMALLOC_STACK in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 931300) by reflexivity. rewrite ELX in ERR.
    pose proof (munch_refl [(q - 16, q)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM. iprefix.
    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB psegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    step. step. zstep. rewrite (shiftr_small0 n 60) by lia. zstep. if_false. zstep. zstep.
    replace (Z.shiftl n 4) with (16 * n) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr LB q a -> outside [(q - 16, q)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in B3'. lia. }
    assert (HEAP1 : RHEAP s LB m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    ihere. to_implM.
    eapply implM_post_evt.
    { eapply (opnew_body HM) with (B := B) (lo := lo);
        [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| assumption| lia| lia]. }
    cbv beta. intros p s' ms' PO. unfold opnew_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW & jnew
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA2 & SO2 & BRN & HEAP2 & BLKN).
    replace (ret_pc (Z_to_bv 64 251000)) with (Z_to_bv 64 251000) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    rewrite ELX in ERR2.
    rename MU into MU1. rename WM into WM1. pose proof (munch_refl [(q - 16, q)]%Z m2) as MU. pose proof (wmono_refl psegs m2) as WM.

    step. step. step. step. release_frame FR ST2 q. step.
    apply evt_done. unfold alloc_post. do 13 eexists. exists m2, errv2, NEW, jnew.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|].
    split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU1| exact WM1| apply CLI]|].
             eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    split; [exact FA2|]. split; [exact SO2|]. split; [exact BRN|]. split; [exact HEAP2| exact BLKN].
  Qed.

  Lemma push1_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
      (V X A cap size : Z) (blk : option bptr) (els : list (Z * Z)) (jr : list byte) (xd xl : Z),
    RHEAP s (vblocks blk A cap ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk psegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (112 + RMALLOC_STACK) ->
    rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m ->
    q <= V -> V + 24 <= B -> q <= X -> X + 16 <= B -> (V + 24 <= X \/ X + 16 <= V) ->
    vrep m V A (cap, size, blk) els jr -> cap < 2^26 -> 0 <= xd < 2^64 -> 0 <= xl < 2^64 ->
    rw_cells psegs m X [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)] ->
    implM psegs (vpush lops (cap, size, blk)) s
          (push_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B V xd xl cap size els m)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 X) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ATP_PUSH1) fc None m (seg_rom psegs)).
  Proof.
    intros until xl. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QV VB QX XB VX VR CAPB XD XL XC.
    unfold ATP_PUSH1, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    destruct VR as (ELS & SZ & SV & BLK).
    assert (ELX : LX_ERRNO = 931300) by reflexivity. rewrite ELX in ERR.
    remember (A + 16 * size) as VE eqn:EVE. remember (A + 16 * cap) as VC eqn:EVC.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    unfold vpush. cbn [bind ret lops Target.ops].
    destruct (Z.ltb_spec size cap) as [LT|GE].
    -
      unfold vblk in BLK. rewrite <- EVE in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia].
      destruct BLK as (BE & BJ & BR & C1). pose proof BR as (A0 & A16 & _ & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC.
      hide BE. hide BJ.
      pose proof (munch_refl [(q - 80, q)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
      apply implM_ret. unfold push_post.
      step. carve_frame 80%nat ST.
      apply (rw_cells_split_CB psegs _ _ [] 80 junk [] [8;8;8;8;8; 8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

      do 5 step. step. step. step. step. step.
      if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.

      pose proof (agree_on_of_munch _ _ _ MU WM) as AG0.
      unhide BJ. apply (rw_cells_agree _ _ _ _ _ AG0) in BJ.
      2:{ intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. repeat split; clear - Ha EVE EVC AC CEIL LO SZ LT QV; lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
      cbn [app] in HEAP.
      assert (HEAP0 : RHEAP s ((b, A, 16 * cap) :: LB0) m0).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX0 : rauxv_ok m0 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES0 : lx_pres LB0 q [(V, V + 24)] m m0).
      { eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      clear MU WM. pose proof (munch_refl [(q - 80, q); (VE, VE + 16); (V, V + 24)]%Z m0) as MU. pose proof (wmono_refl psegs m0) as WM.
      remember (Z.to_nat (16 * (cap - size - 1))) as r eqn:Hr.
      replace (Z.to_nat (16 * (cap - size))) with (8 + (8 + r))%nat in BJ by lia.
      apply (rw_cells_split_CB psegs _ _ [] _ jr [] [8; 8; r]%nat) in BJ; [| cbn; lia]. cbn [mk_CB_cells app] in BJ.

      step. step. step. step. step. step. step.

      do 6 step. release_frame FR ST q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
      unhide BE. apply (rw_cells_agree _ _ _ _ _ AG0) in BE; [| intros a Ha; rewrite velts_size in Ha; cbn [outside]; repeat split; clear - Ha ELS EVE AC CEIL LO SZ LT; unfold zlength in ELS; lia].
      apply (rw_cells_agree _ _ _ _ _ AG1) in BE; [| intros a Ha; rewrite velts_size in Ha; cbn [outside]; repeat split; clear - Ha ELS EVE AC CEIL LO SZ LT QV; unfold zlength in ELS; lia].
      pose proof (LH_head_disj _ _ _ _ _ _ HEAP0) as DJB.
      assert (HEAP9 : RHEAP s ((b, A, 16 * cap) :: LB0) m9).
      { eapply LH_frame; [exact HEAP0| exact MU| exact WM|].
        constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor; [apply W_ok_stack; cbn; lia| constructor]].
        eapply (W_ok_block _ (b, A, 16 * cap)); [left; reflexivity| cbn; lia| cbn; lia]. }
      assert (AUX9 : rauxv_ok m9 B).
      { eapply rauxv_ok_frame; [exact AUX0| exact MU| exact WM|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; clear - EVE AC AS CEIL LO SZ LT A0 QB; lia|].
        constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES9 : lx_pres LB0 q [(V, V + 24)] m m9).
      { eapply lx_pres_trans; [exact PRES0|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [| split; [clear - HX; lia| exact I]]].
        + destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
        + destruct HC as [HC|[HC|HC]]; [clear - HC EVE AC CEIL LO SZ LT; lia| | clear - HC EVE AS A0 SZ LT CAPB; lia].
          intros Hs. apply (DJB a HC). clear - Hs EVE SZ LT. lia. }
      destruct (Sj_stage1_kit.rw_cells_app psegs m9 VE [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)] [CB r (take r (drop 8 (drop 8 jr)))]) as [SPL _].
      destruct (SPL BJ) as [SLOT TAIL]. clear SPL BJ. cbn [cells_size csize Nat.add] in TAIL.
      apply evt_done. do 15 eexists. exists m9, errv, A, cap, (Some b), (take r (drop 8 (drop 8 jr))).
      split; [cbv delta [mkR]; reflexivity|].
      split; [reflexivity|]. split; [replace (size <? cap) with true by (symmetry; apply Z.ltb_lt; exact LT); reflexivity|]. split; [discriminate|].
      split; [assumption|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX9|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact HEAP9|]. split; [| exact PRES9].

      split; [unfold zlength in *; rewrite length_app; cbn [length]; lia|]. split; [lia|]. split.
      { replace (A + 16 * (size + 1)) with (VE + 16) by lia. rewrite <- EVC. exact SV. }
      split. { rewrite velts_app. cbn [velts fst snd]. eapply rw_cells_join; [exact BE| exact SLOT| rewrite velts_size; unfold zlength in ELS; lia]. }
      split. { replace (A + 16 * (size + 1)) with (VE + Z.of_nat 16) by lia. replace (Z.to_nat (16 * (cap - (size + 1)))) with r by lia. exact TAIL. }
      split; [exact BR| exact C1].
    -
      assert (SC : size = cap) by lia. rewrite SC in *. clear SC GE.
      assert (AR : 0 <= A /\ A + 16 * cap <= alloc_ceiling /\ (A + 16 * cap <= 0x10000 \/ 0x105000 <= A)).
      { unfold vblk in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia]. destruct BLK as (_ & _ & (A0 & _ & _ & AC & AS) & _).
        unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC. lia. }
      destruct AR as (A0 & AC & AS).
      hide BLK.

      assert (OLDIN : forall b, blk = Some b -> In (b, A, 16 * cap) (vblocks blk A cap ++ LB0)) by (intros b ->; left; reflexivity).
      pose proof (munch_refl [(q - 80, q)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
      unfold implM. iprefix.
      step. carve_frame 80%nat ST.
      apply (rw_cells_split_CB psegs _ _ [] 80 junk [] [8;8;8;8;8; 8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

      do 5 step. step. step. step. step. step.
      replace VE with VC in * by lia. if_true.

      zstep. zstep. replace (VC + - A) with (16 * cap) by lia.
      zstep. rewrite (signed_small (16 * cap)) by lia. rewrite (shiftr_16_4 cap) by lia.
      zstep. zstep. rewrite (shiftr_small0 (cap + 1) 60) by lia.
      zstep. if_false.

      zstep. replace (VC + - A) with (16 * cap) by lia.
      zstep. rewrite (signed_small (16 * cap)) by lia. rewrite (shiftr_16_3 cap) by lia.
      zstep.
      lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mx _) =>
        assert (REST : forall xa2 : word,
          evt psegs QQ (MS (mkR ra (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 X)
                               (Z_to_bv 64 (16 * cap)) (Z_to_bv 64 (vcap_next cap cap)) xa2 (Z_to_bv 64 0) a4 a5 a6 a7
                               (Z_to_bv 64 (16 * cap)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x3d22c) fc None mx (seg_rom psegs))) end.
      2:{ if_cases K; zify_cond K.
          - replace (Z_to_bv 64 (2 * cap)) with (Z_to_bv 64 (vcap_next cap cap)) by (f_equal; unfold vcap_next; lia). apply REST.
          - zstep. replace (Z_to_bv 64 (cap + 1)) with (Z_to_bv 64 (vcap_next cap cap)) by (f_equal; unfold vcap_next; lia). apply REST. }
      intros xa2.
      assert (CAP' : cap + 1 <= vcap_next cap cap <= 2 * cap + 1) by (unfold vcap_next; lia).
      set (cap' := vcap_next cap cap) in *.

      zstep. zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; clear - K CAPB SZ; lia].
      step. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
      step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HEAP1 : RHEAP s (vblocks blk A cap ++ LB0) m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES1 : lx_pres LB0 q [(V, V + 24)] m m1).
      { eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      unhide BLK. apply (vblk_agree _ _ _ _ _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO; lia| exact ELS| exact SZ].
      clear MU WM.
      ihere. to_implM. change VELT with 16.
      eapply implM_bind.
      { eapply allocate_spec with (B := B) (lo := lo);
          [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| assumption| lia| lia| lia]. }
      cbv beta. intros pn s2' ms2 PO. unfold alloc_post in PO.
      destruct PO as (r5 & r6 & r7 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW & jnew
                      & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA2 & SO2 & BRN & HEAP2 & BLKN).
      replace (ret_pc (Z_to_bv 64 250448)) with (Z_to_bv 64 250448) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR2.
      pose proof BRN as (N0 & N16 & _ & NC & NS). unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in NC.
      pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
      apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in SV; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in XC; [| intros a Ha; left; cbn in Ha; lia].
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG) in BLK;
        [| intros a Hb Ha; destruct blk as [b|]; [| congruence]; right; right; exists (b, A, 16 * cap); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]
         | exact ELS| exact SZ].
      assert (PRES2 : lx_pres LB0 q [(V, V + 24)] m m2).
      { eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; apply in_or_app; right; exact Hb]. }

      assert (SEPN : forall b, blk = Some b -> NEW + 16 * cap' <= A \/ A + 16 * cap <= NEW).
      { intros b Hb. exact (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP2 (OLDIN b Hb)). }
      clear AG PRES1 HEAP1 AUX1.

      remember (NEW + 16 * cap) as NE eqn:ENE. remember (Z.to_nat (16 * (cap' - cap - 1))) as r eqn:Hr.
      replace (Z.to_nat (16 * cap')) with (Z.to_nat (16 * cap) + (16 + r))%nat in BLKN by lia.
      apply rw_cells_CB_split2 in BLKN. destruct BLKN as [NPRE NREST]. rewrite Z2Nat.id in NREST by lia. rewrite <- ENE in NREST.
      apply (rw_cells_split_CB psegs _ _ [] _ _ [] [8; 8; r]%nat) in NREST; [| cbn; lia]. cbn [mk_CB_cells app] in NREST.
      remember (Z.to_nat (16 * cap)) as ncp eqn:Hncp. hide BLK.
      pose proof (munch_refl [(q - 80, q); (NEW, NE + 16); (V, V + 24)]%Z m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      unfold implM. iprefix.

      step. step. zstep. rewrite <- ENE. step. step. step.

      step. step. zstep. replace (Z.shiftl cap' 4) with (16 * cap') by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      zstep. zstep. zstep. replace (VC + - A) with (16 * cap) by lia. zstep. replace (NE + - (16 * cap)) with NEW by lia.
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.

      pose proof (agree_on_of_munch _ _ _ MU WM) as AG23.
      unhide BLK. apply (vblk_agree _ _ _ _ _ _ _ _ _ AG23) in BLK;
        [| intros a Hb Ha; destruct blk as [b|]; [| congruence]; specialize (SEPN b eq_refl); cbn [outside]; repeat split; clear - Ha SEPN ENE AC CEIL LO CAP' QV SZ; lia
         | exact ELS| exact SZ].
      assert (SRCB : bytes_at psegs m3 A (cells_bytes (velts els))).
      { unfold vblk in BLK. destruct blk as [b|].
        - destruct BLK as ([[_ HB] _] & _). exact HB.
        - destruct BLK as [AZ C0]. assert (els = []) as -> by (destruct els; [reflexivity| unfold zlength in ELS; cbn in ELS; lia]).
          rewrite AZ. unfold bytes_at. rewrite velts_bytes_length. cbn [length Nat.mul Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
      subst ncp.
      eapply evt_cut.
      { eapply (memcpy_callZ) with (Dst := NEW) (Src := A) (N := 16 * cap) (src := cells_bytes (velts els)) (junk := take (Z.to_nat (16 * cap)) jnew);
          [exact SRCB| rewrite velts_bytes_length; unfold zlength in ELS; lia| exact NPRE| | lia| lia| lia| assumption].
        destruct blk as [b|]; [specialize (SEPN b eq_refl); clear - SEPN CAP' SZ; lia|].
        unfold vblk in BLK. destruct BLK as [_ C0]. clear - C0. lia. }
      intros ms' PO. unfold memcpy_postZ in PO.
      destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & NPRE4 & SRC4).
      replace (ret_pc (Z_to_bv 64 250516)) with (Z_to_bv 64 250516) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear SRCB SRC4 NPRE. hide BLK.
      transport_after_call psegs m3 m4 MU4 WM4.
      clear MU4 WM4 AG23.

      step. step. step. step. step. step. step. step. step. step. step.

      step. step. step. if_true. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      assert (HEAP5 : RHEAP s2' ((pn, NEW, 16 * cap') :: vblocks blk A cap ++ LB0) m5).
      { eapply LH_frame; [exact HEAP2| exact MU| exact WM|].
        constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor; [apply W_ok_stack; cbn; lia| constructor]].
        eapply (W_ok_block _ (pn, NEW, 16 * cap')); [left; reflexivity| cbn; lia| cbn; lia]. }
      assert (AUX5 : rauxv_ok m5 B).
      { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; clear - ENE NC NS N0 CEIL LO SZ CAP' QB; lia|].
        constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES5 : lx_pres LB0 q [(V, V + 24)] m m5).
      { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
        pose proof (LH_head_disj _ _ _ _ _ _ HEAP2) as DJN.
        intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [| split; [clear - HX; lia| exact I]]].
        + destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
        + destruct HC as [HC|[HC|HC]]; [clear - HC ENE NC CEIL LO SZ CAP'; lia| | clear - HC ENE NS N0 SZ CAP' CAPB; lia].
          intros Hs. apply (DJN a); [| clear - Hs ENE SZ CAP'; lia]. eapply in_block_incl; [| exact HC]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }

      assert (FIN : forall m6 st6 (errv6 : word) yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6,
        RHEAP st6 ((pn, NEW, 16 * cap') :: LB0) m6 -> rauxv_ok m6 B -> mem_inv psegs m6 -> stk psegs m6 lo (q + -80) ->
        rw_cells psegs m6 931300 [C4 errv6] -> ps_fa st6 = ps_fa s -> ps_so st6 = ps_so s -> lx_pres LB0 q [(V, V + 24)] m m6 ->
        rw_cells psegs m6 V [C8 (Z_to_bv 64 NEW); C8 (Z_to_bv 64 (NE + 16)); C8 (Z_to_bv 64 (NEW + 16 * cap'))] ->
        rw_cells psegs m6 NE [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl); CB r (take r (drop 8 (drop 8 (drop (Z.to_nat (16 * cap)) jnew))))] ->
        rw_cells psegs m6 NEW [CB (Z.to_nat (16 * cap)) (cells_bytes (velts els))] ->
        (exists c0 c8 c16 c24 c32, rw_cells psegs m6 (q + -80) [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
        evt psegs (fun ms' => impl psegs (at_node psegs) (mret (cap', cap + 1, Some pn) st6)
                                   (epost (fun p => push_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B V xd xl cap cap els m (fst p) (snd p))) ms')
            (MS (mkR yra (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) yt0 yt1 yt2 (Z_to_bv 64 V) (Z_to_bv 64 NEW) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                     (Z_to_bv 64 (NE + 16)) (Z_to_bv 64 (NEW + 16 * cap')) s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
                F (Z_to_bv 64 0x3d2c0) fc None m6 (seg_rom psegs))).
      { intros m6 st6 errv6 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HEAP6 AUX6 MI6 ST6 ERR6 FA6 SO6 PRES6 SV6 NREST6 NPRE6 (c0 & c8 & c16 & c24 & c32 & FR6).
        clear MU WM. pose proof (munch_refl [(q - 80, q); (V, V + 24)]%Z m6) as MU. pose proof (wmono_refl psegs m6) as WM.

        step. do 6 step. release_frame FR6 ST6 q. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        destruct (Sj_stage1_kit.rw_cells_app psegs m9 NE [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)] [CB r (take r (drop 8 (drop 8 (drop (Z.to_nat (16 * cap)) jnew))))]) as [SPL _].
        destruct (SPL NREST6) as [SLOT TAIL]. clear SPL NREST6. cbn [cells_size csize Nat.add] in TAIL.
        ihere. to_implM. apply implM_ret. apply evt_done. unfold push_post.
        do 15 eexists. exists m9, errv6, NEW, cap', (Some pn), (take r (drop 8 (drop 8 (drop (Z.to_nat (16 * cap)) jnew)))).
        split; [cbv delta [mkR]; reflexivity|].
        split; [reflexivity|]. split; [rewrite Z.ltb_irrefl; reflexivity|]. split; [discriminate|].
        split; [assumption|]. split; [exact ST6|]. split; [exact ERR6|].
        split. { eapply rauxv_ok_frame; [exact AUX6| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
        split; [exact FA6|]. split; [exact SO6|].
        split. { cbn [vblocks app]. eapply LH_frame; [exact HEAP6| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
        split.
        2:{ eapply lx_pres_trans; [exact PRES6|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
            intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
            destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
        split; [unfold zlength in *; rewrite length_app; cbn [length]; lia|]. split; [lia|]. split.
        { replace (NEW + 16 * (cap + 1)) with (NE + 16) by lia. exact SV6. }
        unfold vblk. split. { rewrite velts_app. cbn [velts fst snd]. eapply rw_cells_join; [| exact SLOT| rewrite velts_size; unfold zlength in ELS; lia].
          eapply rw_cells_recast; [exact NPRE6| apply velts_wf| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| rewrite velts_size; cbn [cells_size csize]; unfold zlength in ELS; lia]. }
        split. { replace (NEW + 16 * (cap + 1)) with (NE + Z.of_nat 16) by lia. replace (Z.to_nat (16 * (cap' - (cap + 1)))) with r by lia. exact TAIL. }
        split; [exact BRN| lia]. }
      unhide BLK. unfold vblk in BLK. destruct blk as [b|].
      +
        destruct BLK as (_ & _ & (AP & _) & C1).
        if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].

        zstep. zstep. step. step.
        cbn [vblocks app] in HEAP5.
        pose proof (RHEAP_pull _ [(pn, NEW, 16 * cap')] (b, A, 16 * cap) LB0 _ HEAP5) as HEAP5'. cbn [app] in HEAP5'.
        assert (ND : List.NoDup (map blk_id ((b, A, 16 * cap) :: (pn, NEW, 16 * cap') :: LB0))) by (eapply LH_nodup; exact HEAP5').
        ihere. to_implM. eapply implM_bind.
        { eapply (opdel_sized_proof HF) with (B := B) (lo := lo) (A := A) (n := 16 * cap);
            [exact HEAP5'| left; reflexivity| exact AUX5| lia| exact ST2| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR2| exact MI4| lia]. }
        cbv beta. intros [] s6' ms6 PO. unfold free_postZ in PO.
        destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m6
                        & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
        rewrite (lb_remove_hd _ _ _ _ ND) in HP6, HEAP6. rewrite ELX in ERR6.
        replace (ret_pc (Z_to_bv 64 0x3d2c0)) with (Z_to_bv 64 0x3d2c0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_of_heap_pres _ _ _ _ HP6) as AG6.
        unfold implM. iprefix.
        apply FIN with (errv6 := errv2); try assumption.
        * congruence.
        * congruence.
        * eapply lx_pres_trans; [exact PRES5|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP6| lia| intros b0 Hb0; right; exact Hb0].
        * eapply rw_cells_agree; [exact AG6| eassumption| intros a Ha; left; cbn in Ha; lia].
        * eapply rw_cells_agree; [exact AG6| eassumption|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right.
          exists (pn, NEW, 16 * cap'). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        * eapply rw_cells_agree; [exact AG6| eassumption|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right.
          exists (pn, NEW, 16 * cap'). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        * do 5 eexists. eapply rw_cells_agree; [exact AG6| exact FR| intros a Ha; left; cbn in Ha; lia].
      +
        destruct BLK as [AZ C0]. rewrite AZ. if_true. step.
        replace (ret_pc (Z_to_bv 64 0x3d2c0)) with (Z_to_bv 64 0x3d2c0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        ihere. to_implM. apply implM_retb. unfold implM. iprefix. cbn [vblocks app] in HEAP5.
        apply FIN with (errv6 := errv2); try assumption; try reflexivity.
        do 5 eexists. rewrite AZ in FR. exact FR.
  Qed.

  Lemma push2_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
      (V X A cap size : Z) (blk : option bptr) (els : list (Z * Z)) (jr : list byte) (xd xl : Z),
    RHEAP s (vblocks blk A cap ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk psegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (112 + RMALLOC_STACK) ->
    rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m ->
    q <= V -> V + 24 <= B -> q <= X -> X + 16 <= B -> (V + 24 <= X \/ X + 16 <= V) ->
    vrep m V A (cap, size, blk) els jr -> cap < 2^26 -> 0 <= xd < 2^64 -> 0 <= xl < 2^64 ->
    rw_cells psegs m X [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)] ->
    implM psegs (vpush lops (cap, size, blk)) s
          (push_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B V xd xl cap size els m)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 X) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ATP_PUSH2) fc None m (seg_rom psegs)).
  Proof.
    intros until xl. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QV VB QX XB VX VR CAPB XD XL XC.
    unfold ATP_PUSH2, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    destruct VR as (ELS & SZ & SV & BLK).
    assert (ELX : LX_ERRNO = 931300) by reflexivity. rewrite ELX in ERR.
    remember (A + 16 * size) as VE eqn:EVE. remember (A + 16 * cap) as VC eqn:EVC.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    unfold vpush. cbn [bind ret lops Target.ops].
    destruct (Z.ltb_spec size cap) as [LT|GE].
    -
      unfold vblk in BLK. rewrite <- EVE in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia].
      destruct BLK as (BE & BJ & BR & C1). pose proof BR as (A0 & A16 & _ & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC.
      hide BE. hide BJ.
      pose proof (munch_refl [(q - 80, q)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
      apply implM_ret. unfold push_post.
      step. carve_frame 80%nat ST.
      apply (rw_cells_split_CB psegs _ _ [] 80 junk [] [8;8;8;8;8; 8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

      do 5 step. step. step. step. step. step.
      if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.

      pose proof (agree_on_of_munch _ _ _ MU WM) as AG0.
      unhide BJ. apply (rw_cells_agree _ _ _ _ _ AG0) in BJ.
      2:{ intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. repeat split; clear - Ha EVE EVC AC CEIL LO SZ LT QV; lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
      cbn [app] in HEAP.
      assert (HEAP0 : RHEAP s ((b, A, 16 * cap) :: LB0) m0).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX0 : rauxv_ok m0 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES0 : lx_pres LB0 q [(V, V + 24)] m m0).
      { eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      clear MU WM. pose proof (munch_refl [(q - 80, q); (VE, VE + 16); (V, V + 24)]%Z m0) as MU. pose proof (wmono_refl psegs m0) as WM.
      remember (Z.to_nat (16 * (cap - size - 1))) as r eqn:Hr.
      replace (Z.to_nat (16 * (cap - size))) with (8 + (8 + r))%nat in BJ by lia.
      apply (rw_cells_split_CB psegs _ _ [] _ jr [] [8; 8; r]%nat) in BJ; [| cbn; lia]. cbn [mk_CB_cells app] in BJ.

      step. step. step. step. step. step. step.

      do 6 step. release_frame FR ST q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
      unhide BE. apply (rw_cells_agree _ _ _ _ _ AG0) in BE; [| intros a Ha; rewrite velts_size in Ha; cbn [outside]; repeat split; clear - Ha ELS EVE AC CEIL LO SZ LT; unfold zlength in ELS; lia].
      apply (rw_cells_agree _ _ _ _ _ AG1) in BE; [| intros a Ha; rewrite velts_size in Ha; cbn [outside]; repeat split; clear - Ha ELS EVE AC CEIL LO SZ LT QV; unfold zlength in ELS; lia].
      pose proof (LH_head_disj _ _ _ _ _ _ HEAP0) as DJB.
      assert (HEAP9 : RHEAP s ((b, A, 16 * cap) :: LB0) m9).
      { eapply LH_frame; [exact HEAP0| exact MU| exact WM|].
        constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor; [apply W_ok_stack; cbn; lia| constructor]].
        eapply (W_ok_block _ (b, A, 16 * cap)); [left; reflexivity| cbn; lia| cbn; lia]. }
      assert (AUX9 : rauxv_ok m9 B).
      { eapply rauxv_ok_frame; [exact AUX0| exact MU| exact WM|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; clear - EVE AC AS CEIL LO SZ LT A0 QB; lia|].
        constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES9 : lx_pres LB0 q [(V, V + 24)] m m9).
      { eapply lx_pres_trans; [exact PRES0|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [| split; [clear - HX; lia| exact I]]].
        + destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
        + destruct HC as [HC|[HC|HC]]; [clear - HC EVE AC CEIL LO SZ LT; lia| | clear - HC EVE AS A0 SZ LT CAPB; lia].
          intros Hs. apply (DJB a HC). clear - Hs EVE SZ LT. lia. }
      destruct (Sj_stage1_kit.rw_cells_app psegs m9 VE [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)] [CB r (take r (drop 8 (drop 8 jr)))]) as [SPL _].
      destruct (SPL BJ) as [SLOT TAIL]. clear SPL BJ. cbn [cells_size csize Nat.add] in TAIL.
      apply evt_done. do 15 eexists. exists m9, errv, A, cap, (Some b), (take r (drop 8 (drop 8 jr))).
      split; [cbv delta [mkR]; reflexivity|].
      split; [reflexivity|]. split; [replace (size <? cap) with true by (symmetry; apply Z.ltb_lt; exact LT); reflexivity|]. split; [discriminate|].
      split; [assumption|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX9|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact HEAP9|]. split; [| exact PRES9].

      split; [unfold zlength in *; rewrite length_app; cbn [length]; lia|]. split; [lia|]. split.
      { replace (A + 16 * (size + 1)) with (VE + 16) by lia. rewrite <- EVC. exact SV. }
      split. { rewrite velts_app. cbn [velts fst snd]. eapply rw_cells_join; [exact BE| exact SLOT| rewrite velts_size; unfold zlength in ELS; lia]. }
      split. { replace (A + 16 * (size + 1)) with (VE + Z.of_nat 16) by lia. replace (Z.to_nat (16 * (cap - (size + 1)))) with r by lia. exact TAIL. }
      split; [exact BR| exact C1].
    -
      assert (SC : size = cap) by lia. rewrite SC in *. clear SC GE.
      assert (AR : 0 <= A /\ A + 16 * cap <= alloc_ceiling /\ (A + 16 * cap <= 0x10000 \/ 0x105000 <= A)).
      { unfold vblk in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia]. destruct BLK as (_ & _ & (A0 & _ & _ & AC & AS) & _).
        unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC. lia. }
      destruct AR as (A0 & AC & AS).
      hide BLK.

      assert (OLDIN : forall b, blk = Some b -> In (b, A, 16 * cap) (vblocks blk A cap ++ LB0)) by (intros b ->; left; reflexivity).
      pose proof (munch_refl [(q - 80, q)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
      unfold implM. iprefix.
      step. carve_frame 80%nat ST.
      apply (rw_cells_split_CB psegs _ _ [] 80 junk [] [8;8;8;8;8; 8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

      do 5 step. step. step. step. step. step.
      replace VE with VC in * by lia. if_true.

      zstep. zstep. replace (VC + - A) with (16 * cap) by lia.
      zstep. rewrite (signed_small (16 * cap)) by lia. rewrite (shiftr_16_4 cap) by lia.
      zstep. zstep. rewrite (shiftr_small0 (cap + 1) 60) by lia.
      zstep. if_false.

      zstep. replace (VC + - A) with (16 * cap) by lia.
      zstep. rewrite (signed_small (16 * cap)) by lia. rewrite (shiftr_16_3 cap) by lia.
      zstep.
      lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mx _) =>
        assert (REST : forall xa2 : word,
          evt psegs QQ (MS (mkR ra (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 X)
                               (Z_to_bv 64 (16 * cap)) (Z_to_bv 64 (vcap_next cap cap)) xa2 (Z_to_bv 64 0) a4 a5 a6 a7
                               (Z_to_bv 64 (16 * cap)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x3d350) fc None mx (seg_rom psegs))) end.
      2:{ if_cases K; zify_cond K.
          - replace (Z_to_bv 64 (2 * cap)) with (Z_to_bv 64 (vcap_next cap cap)) by (f_equal; unfold vcap_next; lia). apply REST.
          - zstep. replace (Z_to_bv 64 (cap + 1)) with (Z_to_bv 64 (vcap_next cap cap)) by (f_equal; unfold vcap_next; lia). apply REST. }
      intros xa2.
      assert (CAP' : cap + 1 <= vcap_next cap cap <= 2 * cap + 1) by (unfold vcap_next; lia).
      set (cap' := vcap_next cap cap) in *.

      zstep. zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; clear - K CAPB SZ; lia].
      step. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
      step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HEAP1 : RHEAP s (vblocks blk A cap ++ LB0) m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES1 : lx_pres LB0 q [(V, V + 24)] m m1).
      { eapply lx_pres_of_munch; [exact MU| exact WM|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      unhide BLK. apply (vblk_agree _ _ _ _ _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO; lia| exact ELS| exact SZ].
      clear MU WM.
      ihere. to_implM. change VELT with 16.
      eapply implM_bind.
      { eapply allocate_spec with (B := B) (lo := lo);
          [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| assumption| lia| lia| lia]. }
      cbv beta. intros pn s2' ms2 PO. unfold alloc_post in PO.
      destruct PO as (r5 & r6 & r7 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW & jnew
                      & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA2 & SO2 & BRN & HEAP2 & BLKN).
      replace (ret_pc (Z_to_bv 64 250740)) with (Z_to_bv 64 250740) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR2.
      pose proof BRN as (N0 & N16 & _ & NC & NS). unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in NC.
      pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
      apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in SV; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in XC; [| intros a Ha; left; cbn in Ha; lia].
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG) in BLK;
        [| intros a Hb Ha; destruct blk as [b|]; [| congruence]; right; right; exists (b, A, 16 * cap); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]
         | exact ELS| exact SZ].
      assert (PRES2 : lx_pres LB0 q [(V, V + 24)] m m2).
      { eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; apply in_or_app; right; exact Hb]. }

      assert (SEPN : forall b, blk = Some b -> NEW + 16 * cap' <= A \/ A + 16 * cap <= NEW).
      { intros b Hb. exact (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP2 (OLDIN b Hb)). }
      clear AG PRES1 HEAP1 AUX1.

      remember (NEW + 16 * cap) as NE eqn:ENE. remember (Z.to_nat (16 * (cap' - cap - 1))) as r eqn:Hr.
      replace (Z.to_nat (16 * cap')) with (Z.to_nat (16 * cap) + (16 + r))%nat in BLKN by lia.
      apply rw_cells_CB_split2 in BLKN. destruct BLKN as [NPRE NREST]. rewrite Z2Nat.id in NREST by lia. rewrite <- ENE in NREST.
      apply (rw_cells_split_CB psegs _ _ [] _ _ [] [8; 8; r]%nat) in NREST; [| cbn; lia]. cbn [mk_CB_cells app] in NREST.
      remember (Z.to_nat (16 * cap)) as ncp eqn:Hncp. hide BLK.
      pose proof (munch_refl [(q - 80, q); (NEW, NE + 16); (V, V + 24)]%Z m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      unfold implM. iprefix.

      step. step. zstep. rewrite <- ENE. step. step. step.

      step. step. zstep. replace (Z.shiftl cap' 4) with (16 * cap') by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      zstep. zstep. zstep. replace (VC + - A) with (16 * cap) by lia. zstep. replace (NE + - (16 * cap)) with NEW by lia.
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.

      pose proof (agree_on_of_munch _ _ _ MU WM) as AG23.
      unhide BLK. apply (vblk_agree _ _ _ _ _ _ _ _ _ AG23) in BLK;
        [| intros a Hb Ha; destruct blk as [b|]; [| congruence]; specialize (SEPN b eq_refl); cbn [outside]; repeat split; clear - Ha SEPN ENE AC CEIL LO CAP' QV SZ; lia
         | exact ELS| exact SZ].
      assert (SRCB : bytes_at psegs m3 A (cells_bytes (velts els))).
      { unfold vblk in BLK. destruct blk as [b|].
        - destruct BLK as ([[_ HB] _] & _). exact HB.
        - destruct BLK as [AZ C0]. assert (els = []) as -> by (destruct els; [reflexivity| unfold zlength in ELS; cbn in ELS; lia]).
          rewrite AZ. unfold bytes_at. rewrite velts_bytes_length. cbn [length Nat.mul Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
      subst ncp.
      eapply evt_cut.
      { eapply (memcpy_callZ) with (Dst := NEW) (Src := A) (N := 16 * cap) (src := cells_bytes (velts els)) (junk := take (Z.to_nat (16 * cap)) jnew);
          [exact SRCB| rewrite velts_bytes_length; unfold zlength in ELS; lia| exact NPRE| | lia| lia| lia| assumption].
        destruct blk as [b|]; [specialize (SEPN b eq_refl); clear - SEPN CAP' SZ; lia|].
        unfold vblk in BLK. destruct BLK as [_ C0]. clear - C0. lia. }
      intros ms' PO. unfold memcpy_postZ in PO.
      destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & NPRE4 & SRC4).
      replace (ret_pc (Z_to_bv 64 250808)) with (Z_to_bv 64 250808) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear SRCB SRC4 NPRE. hide BLK.
      transport_after_call psegs m3 m4 MU4 WM4.
      clear MU4 WM4 AG23.

      step. step. step. step. step. step. step. step. step. step. step.

      step. step. step. if_true. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      assert (HEAP5 : RHEAP s2' ((pn, NEW, 16 * cap') :: vblocks blk A cap ++ LB0) m5).
      { eapply LH_frame; [exact HEAP2| exact MU| exact WM|].
        constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor; [apply W_ok_stack; cbn; lia| constructor]].
        eapply (W_ok_block _ (pn, NEW, 16 * cap')); [left; reflexivity| cbn; lia| cbn; lia]. }
      assert (AUX5 : rauxv_ok m5 B).
      { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; clear - ENE NC NS N0 CEIL LO SZ CAP' QB; lia|].
        constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES5 : lx_pres LB0 q [(V, V + 24)] m m5).
      { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
        pose proof (LH_head_disj _ _ _ _ _ _ HEAP2) as DJN.
        intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [| split; [clear - HX; lia| exact I]]].
        + destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
        + destruct HC as [HC|[HC|HC]]; [clear - HC ENE NC CEIL LO SZ CAP'; lia| | clear - HC ENE NS N0 SZ CAP' CAPB; lia].
          intros Hs. apply (DJN a); [| clear - Hs ENE SZ CAP'; lia]. eapply in_block_incl; [| exact HC]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }

      assert (FIN : forall m6 st6 (errv6 : word) yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6,
        RHEAP st6 ((pn, NEW, 16 * cap') :: LB0) m6 -> rauxv_ok m6 B -> mem_inv psegs m6 -> stk psegs m6 lo (q + -80) ->
        rw_cells psegs m6 931300 [C4 errv6] -> ps_fa st6 = ps_fa s -> ps_so st6 = ps_so s -> lx_pres LB0 q [(V, V + 24)] m m6 ->
        rw_cells psegs m6 V [C8 (Z_to_bv 64 NEW); C8 (Z_to_bv 64 (NE + 16)); C8 (Z_to_bv 64 (NEW + 16 * cap'))] ->
        rw_cells psegs m6 NE [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl); CB r (take r (drop 8 (drop 8 (drop (Z.to_nat (16 * cap)) jnew))))] ->
        rw_cells psegs m6 NEW [CB (Z.to_nat (16 * cap)) (cells_bytes (velts els))] ->
        (exists c0 c8 c16 c24 c32, rw_cells psegs m6 (q + -80) [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
        evt psegs (fun ms' => impl psegs (at_node psegs) (mret (cap', cap + 1, Some pn) st6)
                                   (epost (fun p => push_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B V xd xl cap cap els m (fst p) (snd p))) ms')
            (MS (mkR yra (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) yt0 yt1 yt2 (Z_to_bv 64 V) (Z_to_bv 64 NEW) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                     (Z_to_bv 64 (NE + 16)) (Z_to_bv 64 (NEW + 16 * cap')) s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
                F (Z_to_bv 64 0x3d3e4) fc None m6 (seg_rom psegs))).
      { intros m6 st6 errv6 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HEAP6 AUX6 MI6 ST6 ERR6 FA6 SO6 PRES6 SV6 NREST6 NPRE6 (c0 & c8 & c16 & c24 & c32 & FR6).
        clear MU WM. pose proof (munch_refl [(q - 80, q); (V, V + 24)]%Z m6) as MU. pose proof (wmono_refl psegs m6) as WM.

        step. do 6 step. release_frame FR6 ST6 q. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        destruct (Sj_stage1_kit.rw_cells_app psegs m9 NE [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)] [CB r (take r (drop 8 (drop 8 (drop (Z.to_nat (16 * cap)) jnew))))]) as [SPL _].
        destruct (SPL NREST6) as [SLOT TAIL]. clear SPL NREST6. cbn [cells_size csize Nat.add] in TAIL.
        ihere. to_implM. apply implM_ret. apply evt_done. unfold push_post.
        do 15 eexists. exists m9, errv6, NEW, cap', (Some pn), (take r (drop 8 (drop 8 (drop (Z.to_nat (16 * cap)) jnew)))).
        split; [cbv delta [mkR]; reflexivity|].
        split; [reflexivity|]. split; [rewrite Z.ltb_irrefl; reflexivity|]. split; [discriminate|].
        split; [assumption|]. split; [exact ST6|]. split; [exact ERR6|].
        split. { eapply rauxv_ok_frame; [exact AUX6| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
        split; [exact FA6|]. split; [exact SO6|].
        split. { cbn [vblocks app]. eapply LH_frame; [exact HEAP6| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
        split.
        2:{ eapply lx_pres_trans; [exact PRES6|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
            intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
            destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
        split; [unfold zlength in *; rewrite length_app; cbn [length]; lia|]. split; [lia|]. split.
        { replace (NEW + 16 * (cap + 1)) with (NE + 16) by lia. exact SV6. }
        unfold vblk. split. { rewrite velts_app. cbn [velts fst snd]. eapply rw_cells_join; [| exact SLOT| rewrite velts_size; unfold zlength in ELS; lia].
          eapply rw_cells_recast; [exact NPRE6| apply velts_wf| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| rewrite velts_size; cbn [cells_size csize]; unfold zlength in ELS; lia]. }
        split. { replace (NEW + 16 * (cap + 1)) with (NE + Z.of_nat 16) by lia. replace (Z.to_nat (16 * (cap' - (cap + 1)))) with r by lia. exact TAIL. }
        split; [exact BRN| lia]. }
      unhide BLK. unfold vblk in BLK. destruct blk as [b|].
      +
        destruct BLK as (_ & _ & (AP & _) & C1).
        if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].

        zstep. zstep. step. step.
        cbn [vblocks app] in HEAP5.
        pose proof (RHEAP_pull _ [(pn, NEW, 16 * cap')] (b, A, 16 * cap) LB0 _ HEAP5) as HEAP5'. cbn [app] in HEAP5'.
        assert (ND : List.NoDup (map blk_id ((b, A, 16 * cap) :: (pn, NEW, 16 * cap') :: LB0))) by (eapply LH_nodup; exact HEAP5').
        ihere. to_implM. eapply implM_bind.
        { eapply (opdel_sized_proof HF) with (B := B) (lo := lo) (A := A) (n := 16 * cap);
            [exact HEAP5'| left; reflexivity| exact AUX5| lia| exact ST2| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR2| exact MI4| lia]. }
        cbv beta. intros [] s6' ms6 PO. unfold free_postZ in PO.
        destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m6
                        & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
        rewrite (lb_remove_hd _ _ _ _ ND) in HP6, HEAP6. rewrite ELX in ERR6.
        replace (ret_pc (Z_to_bv 64 0x3d3e4)) with (Z_to_bv 64 0x3d3e4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_of_heap_pres _ _ _ _ HP6) as AG6.
        unfold implM. iprefix.
        apply FIN with (errv6 := errv2); try assumption.
        * congruence.
        * congruence.
        * eapply lx_pres_trans; [exact PRES5|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP6| lia| intros b0 Hb0; right; exact Hb0].
        * eapply rw_cells_agree; [exact AG6| eassumption| intros a Ha; left; cbn in Ha; lia].
        * eapply rw_cells_agree; [exact AG6| eassumption|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right.
          exists (pn, NEW, 16 * cap'). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        * eapply rw_cells_agree; [exact AG6| eassumption|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right.
          exists (pn, NEW, 16 * cap'). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        * do 5 eexists. eapply rw_cells_agree; [exact AG6| exact FR| intros a Ha; left; cbn in Ha; lia].
      +
        destruct BLK as [AZ C0]. rewrite AZ. if_true. step.
        replace (ret_pc (Z_to_bv 64 0x3d3e4)) with (Z_to_bv 64 0x3d3e4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        ihere. to_implM. apply implM_retb. unfold implM. iprefix. cbn [vblocks app] in HEAP5.
        apply FIN with (errv6 := errv2); try assumption; try reflexivity.
        do 5 eexists. rewrite AZ in FR. exact FR.
  Qed.
End Proofs.
End WithCeiling0.
