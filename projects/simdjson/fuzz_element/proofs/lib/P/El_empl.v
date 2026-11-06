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
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit F_memcpy Atp_h_defs Atp_h_push.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Sj_stage1_kit.
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

Definition empl_post (sp0 : Z) (gp s1 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B : Z) (els : list (Z * Z)) (P : nat) (m : mem)
    (v' : @vec bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 m' (errv' : word) (A' cap' : Z) (b' : bptr) (jr' : list byte)
                    (c48 c56 c64 c72 c80 : list byte),
    ms' = MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s8 s0 (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s7 s6 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3bcf0) fc None m' (seg_rom psegs)
    /\ v' = (cap', Z.of_nat P, Some b') /\ cap' < 2^26
    /\ mem_inv psegs m' /\ stk psegs m' lo sp0 /\ rw_cells psegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((b', A', 16 * cap') :: LB0) m'
    /\ vrep m' (sp0 + 392) A' v' (els ++ repeat (0, 0) (P - length els)) jr'
    /\ rw_cells psegs m' (sp0 + 8) [CB 8 c48; CB 8 c56; CB 8 c64; CB 8 c72; CB 8 c80]
    /\ lx_pres LB0 sp0 [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] m m'.

Definition EM_S3 : Z := 1152921504606846975.
Definition EM_S4 : Z := 9223372036854775792.

Definition emp_post (sp0 : Z) (gp s1 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B : Z) (els : list (Z * Z)) (size : Z) (m : mem)
    (v' : @vec bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 m' (errv' : word) (A' cap' : Z) (b' : bptr) (jr' : list byte)
                    (e1 : word) (c48 c56 c64 c72 c80 : list byte),
    ms' = MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s8 s0 a0 a1 a2 a3 a4 a5 a6 a7 s1 (Z_to_bv 64 2) (Z_to_bv 64 EM_S3) (Z_to_bv 64 EM_S4) (Z_to_bv 64 (A' + 16 * (size + 1))) s7 s6 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3bcdc) fc None m' (seg_rom psegs)
    /\ v' = (cap', size + 1, Some b') /\ size + 1 <= cap' <= Z.max 2 (2 * (size + 1))
    /\ mem_inv psegs m' /\ stk psegs m' lo sp0 /\ rw_cells psegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((b', A', 16 * cap') :: LB0) m'
    /\ rw_cells psegs m' (sp0 + 392) [C8 (Z_to_bv 64 A'); C8 e1; C8 (Z_to_bv 64 (A' + 16 * cap'))]
    /\ vblk m' A' cap' (size + 1) (Some b') (els ++ [(0, 0)]) jr'
    /\ rw_cells psegs m' (sp0 + 8) [CB 8 c48; CB 8 c56; CB 8 c64; CB 8 c72; CB 8 c80]
    /\ lx_pres LB0 sp0 [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] m m'.

Lemma scratch_junk5 : forall m A (c1 c2 c3 c4 c5 : cell), rw_cells psegs m A [c1; c2; c3; c4; c5] ->
  csize c1 = 8%nat -> csize c2 = 8%nat -> csize c3 = 8%nat -> csize c4 = 8%nat -> csize c5 = 8%nat ->
  rw_cells psegs m A [CB 8 (cbytes c1); CB 8 (cbytes c2); CB 8 (cbytes c3); CB 8 (cbytes c4); CB 8 (cbytes c5)].
Proof.
  intros m A c1 c2 c3 c4 c5 H E1 E2 E3 E4 E5. pose proof H as H0. destruct H0 as [[Hwf _] _]. cbn [cells_wf] in Hwf. destruct Hwf as (W1 & W2 & W3 & W4 & W5 & _).
  eapply rw_cells_recast; [exact H| | |].
  - cbn [cells_wf cell_wf]. rewrite !cbytes_length by assumption. repeat split; congruence.
  - reflexivity.
  - cbn [cells_size csize]. rewrite E1, E2, E3, E4, E5. reflexivity.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma empl_push : forall (x1 gp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (sp0 lo B : Z) (errv : word)
      (A cap size : Z) (blk : option bptr) (els : list (Z * Z)) (jr : list byte) (c48 c56 c64 c72 c80 : list byte) (vs0 : Z),
    RHEAP s (vblocks blk A cap ++ LB0) m -> rauxv_ok m B -> sp0 + 528 <= B -> B < 2^63 ->
    stk psegs m lo sp0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 - (32 + RMALLOC_STACK) ->
    rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m -> sp0 mod 16 = 0 ->
    vrep m (sp0 + 392) A (cap, size, blk) els jr -> cap <= Z.max 2 (2 * size) -> 0 <= size < 2 -> (blk = None <-> els = []) ->
    s1 = Z_to_bv 64 (sp0 + 392) -> vs0 = 16 * size ->
    rw_cells psegs m (sp0 + 8) [CB 8 c48; CB 8 c56; CB 8 c64; CB 8 c72; CB 8 c80] ->
    implM psegs (vpush lops (cap, size, blk)) s (emp_post sp0 gp s1 s7 s8 s9 s10 s11 F fc s LB0 lo B els size m)
      (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s8 (Z_to_bv 64 vs0) (Z_to_bv 64 A) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s1 (Z_to_bv 64 2) (Z_to_bv 64 EM_S3) (Z_to_bv 64 EM_S4) (Z_to_bv 64 (A + 16 * size)) s7 s6 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3bc3c) fc None m (seg_rom psegs)).
  Proof.
    intros until vs0. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI AL16 VR CAPB SZB BN -> -> SCR.
    unfold RMALLOC_STACK, GLOBALS_TOP, EM_S3, EM_S4 in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 931300) by reflexivity. rewrite ELX in ERR.
    destruct VR as (ELS & SZ & SV & BLK).
    remember (A + 16 * size) as VE eqn:EVE. remember (A + 16 * cap) as VC eqn:EVC.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB0 sp0 [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] a ->
                outside [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. clear - HX. lia. }
    unfold vpush. cbn [bind ret lops Target.ops].
    destruct (Z.ltb_spec size cap) as [LT|GE].
    -
      unfold vblk in BLK. rewrite <- EVE in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia].
      destruct BLK as (BE & BJ & BR & C1). pose proof BR as (A0 & A16 & _ & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC.
      hide BE.
      remember (Z.to_nat (16 * (cap - size - 1))) as r eqn:Hr.
      replace (Z.to_nat (16 * (cap - size))) with (8 + (8 + r))%nat in BJ by lia.
      apply (rw_cells_split_CB psegs _ _ [] _ jr [] [8; 8; r]%nat) in BJ; [| cbn; lia]. cbn [mk_CB_cells app] in BJ.
      pose proof (munch_refl [(VE, VE + 16)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
      apply implM_ret.

      step. step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
      hstep. hstep. zstep. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
      unhide BE. apply (rw_cells_agree _ _ _ _ _ AG1) in BE; [| intros a Ha; rewrite velts_size in Ha; cbn [outside]; repeat split; clear - Ha ELS EVE AC CEIL LO SZ LT; unfold zlength in ELS; lia].
      cbn [vblocks app] in HEAP. pose proof (LH_head_disj _ _ _ _ _ _ HEAP) as DJB.
      destruct (Sj_stage1_kit.rw_cells_app psegs m9 VE [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB r (take r (drop 8 (drop 8 jr)))]) as [SPL _].
      destruct (SPL BJ) as [SLOT TAIL]. clear SPL BJ. cbn [cells_size csize Nat.add] in TAIL.
      apply evt_done. unfold emp_post. do 18 eexists. exists m9, errv, A, cap, b, (take r (drop 8 (drop 8 jr))), (Z_to_bv 64 VE). do 5 eexists.
      split; [replace (A + 16 * (size + 1)) with (VE + 16) by lia; cbv delta [mkR]; reflexivity|].
      split; [reflexivity|]. split; [clear - CAPB LT SZB; lia|].
      split; [assumption|]. split; [exact ST|]. split; [exact ERR|].
      split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; clear - EVE AC AS CEIL LO SZ LT A0 QB; lia| constructor]. }
      split; [reflexivity|]. split; [reflexivity|].
      split. { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [| constructor].
               eapply (W_ok_block _ (b, A, 16 * cap)); [left; reflexivity| cbn; lia| cbn; lia]. }
      split. { rewrite <- EVC. exact SV. }
      split. { unfold vblk. split. { rewrite velts_app. cbn [velts fst snd]. eapply rw_cells_join; [exact BE| exact SLOT| rewrite velts_size; unfold zlength in ELS; lia]. }
               split. { replace (A + 16 * (size + 1)) with (VE + Z.of_nat 16) by lia. replace (Z.to_nat (16 * (cap - (size + 1)))) with r by lia. exact TAIL. }
               split; [exact BR| exact C1]. }
      split; [exact SCR|].
      eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| exact I].
      destruct HC as [HC|[HC|HC]]; [clear - HC EVE AC CEIL LO SZ LT; lia| | clear - HC EVE AS A0 SZ LT CAPB; lia].
      intros Hs. apply (DJB a HC). clear - Hs EVE SZ LT. lia.
    -
      assert (SC : size = cap) by lia. rewrite SC in *. clear SC GE.
      assert (AR : 0 <= A /\ A + 16 * cap <= alloc_ceiling /\ (A + 16 * cap <= 0x10000 \/ 0x105000 <= A)).
      { unfold vblk in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia]. destruct BLK as (_ & _ & (A0 & _ & _ & AC & AS) & _).
        unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC. lia. }
      destruct AR as (A0 & AC & AS).
      assert (CAP1 : 0 <= cap <= 1) by lia.
      assert (CN : vcap_next cap cap = cap + 1) by (unfold vcap_next; lia).
      hide BLK.
      assert (OLDIN : forall b, blk = Some b -> In (b, A, 16 * cap) (vblocks blk A cap ++ LB0)) by (intros b ->; left; reflexivity).
      pose proof (munch_refl [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
      unfold implM. iprefix.

      step. replace VE with VC in * by lia. step. if_true.

      zstep. zstep. replace (VC + - A) with (16 * cap) by lia.
      zstep. rewrite (signed_small (16 * cap)) by lia. rewrite (shiftr_16_3 cap) by lia.
      step. if_cases K; zify_cond K; [exfalso; clear - K CAP1; lia|]. clear K. zstep.

      step. if_cases K; zify_cond K; [clear K| exfalso; clear - K CAP1; lia].
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HEAP1 : RHEAP s (vblocks blk A cap ++ LB0) m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES1 : lx_pres LB0 sp0 [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
      unhide BLK. apply (vblk_agree _ _ _ _ _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO; lia| exact ELS| exact SZ].
      clear MU WM.
      ihere. to_implM. change VELT with 16. rewrite CN.
      eapply implM_bind.
      { eapply (allocate_spec HM) with (B := B) (lo := lo);
          [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| rewrite ELX; eassumption| assumption| lia| lia| lia]. }
      cbv beta. intros pn s2' ms2 PO. unfold alloc_post in PO.
      destruct PO as (r5 & r6 & r7 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW & jnew
                      & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA2 & SO2 & BRN & HEAP2 & BLKN).
      replace (ret_pc (Z_to_bv 64 0x3bc7c)) with (Z_to_bv 64 0x3bc7c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR2.
      pose proof BRN as (N0 & N16 & _ & NC & NS). unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in NC.
      pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
      lazymatch goal with H : rw_cells psegs m1 (sp0 + 8) _ |- _ => apply (rw_cells_agree _ _ _ _ _ AG) in H; [rename H into SCR1| intros a Ha; left; cbn in Ha; lia] end.
      apply (rw_cells_agree _ _ _ _ _ AG) in SV; [| intros a Ha; left; cbn in Ha; lia].
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG) in BLK;
        [| intros a Hb Ha; destruct blk as [b|]; [| congruence]; right; right; exists (b, A, 16 * cap); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]
         | exact ELS| exact SZ].
      assert (PRES2 : lx_pres LB0 sp0 [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] m m2).
      { eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; apply in_or_app; right; exact Hb]. }
      assert (SEPN : forall b, blk = Some b -> NEW + 16 * (cap + 1) <= A \/ A + 16 * cap <= NEW).
      { intros b Hb. exact (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP2 (OLDIN b Hb)). }
      clear AG PRES1 HEAP1 AUX1.

      remember (NEW + 16 * cap) as NE eqn:ENE.
      replace (Z.to_nat (16 * (cap + 1))) with (Z.to_nat (16 * cap) + (8 + 8))%nat in BLKN by lia.
      apply rw_cells_CB_split2 in BLKN. destruct BLKN as [NPRE NREST]. rewrite Z2Nat.id in NREST by lia. rewrite <- ENE in NREST.
      apply (rw_cells_split_CB psegs _ _ [] _ _ [] [8; 8]%nat) in NREST; [| cbn; lia]. cbn [mk_CB_cells app] in NREST.
      hide BLK.
      pose proof (munch_refl [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416); (NEW, NE + 16)]%Z m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      unfold implM. iprefix.

      zstep. rewrite <- ENE. hstep. hstep.

      step. step. zstep. replace (Z.shiftl (cap + 1) 4) with (16 * (cap + 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      zstep. zstep. zstep. replace (VC + - A) with (16 * cap) by lia. zstep. replace (NE + - (16 * cap)) with NEW by lia.
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG23.
      unhide BLK. apply (vblk_agree _ _ _ _ _ _ _ _ _ AG23) in BLK;
        [| intros a Hb Ha; destruct blk as [b|]; [| congruence]; specialize (SEPN b eq_refl); cbn [outside]; repeat split; clear - Ha SEPN ENE AC CEIL LO CAP1 SZ; lia
         | exact ELS| exact SZ].
      assert (SRCB : bytes_at psegs m3 A (cells_bytes (velts els))).
      { unfold vblk in BLK. destruct blk as [b|].
        - destruct BLK as ([[_ HB] _] & _). exact HB.
        - destruct BLK as [AZ C0]. assert (els = []) as -> by (apply BN; reflexivity).
          rewrite AZ. unfold bytes_at. rewrite velts_bytes_length. cbn [length Nat.mul Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
      eapply evt_cut.
      { eapply (memcpy_callZ) with (Dst := NEW) (Src := A) (N := 16 * cap) (src := cells_bytes (velts els)) (junk := take (Z.to_nat (16 * cap)) jnew);
          [exact SRCB| rewrite velts_bytes_length; unfold zlength in ELS; lia| exact NPRE| | lia| lia| lia| assumption].
        destruct blk as [b|]; [specialize (SEPN b eq_refl); clear - SEPN CAP1 SZ; lia|].
        unfold vblk in BLK. destruct BLK as [_ C0]. clear - C0. lia. }
      intros ms' PO. unfold memcpy_postZ in PO.
      destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & NPRE4 & SRC4).
      replace (ret_pc (Z_to_bv 64 0x3bcb0)) with (Z_to_bv 64 0x3bcb0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear SRCB SRC4 NPRE. hide BLK.
      transport_after_call psegs m3 m4 MU4 WM4.
      clear MU4 WM4 AG23.

      step. step. step. step. step. step. step. step. step. step. step.

      step. step. step. if_true. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      assert (HEAP5 : RHEAP s2' ((pn, NEW, 16 * (cap + 1)) :: vblocks blk A cap ++ LB0) m5).
      { eapply LH_frame; [exact HEAP2| exact MU| exact WM|].
        constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
        eapply (W_ok_block _ (pn, NEW, 16 * (cap + 1))); [left; reflexivity| cbn; lia| cbn; lia]. }
      assert (AUX5 : rauxv_ok m5 B).
      { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
        constructor; [cbn; unfold RAUXV_CELL; clear - ENE NC NS N0 CEIL LO SZ CAP1 QB; lia| constructor]. }
      assert (PRES5 : lx_pres LB0 sp0 [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] m m5).
      { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
        pose proof (LH_head_disj _ _ _ _ _ _ HEAP2) as DJN.
        intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [clear - HX; lia| split; [clear - HX; lia| split; [| exact I]]].
        destruct HC as [HC|[HC|HC]]; [clear - HC ENE NC CEIL LO SZ CAP1; lia| | clear - HC ENE NS N0 SZ CAP1; lia].
        intros Hs. apply (DJN a); [| clear - Hs ENE SZ CAP1; lia]. eapply in_block_incl; [| exact HC]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }

      assert (FIN : forall m6 st6 (errv6 : word) yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6,
        RHEAP st6 ((pn, NEW, 16 * (cap + 1)) :: LB0) m6 -> rauxv_ok m6 B -> mem_inv psegs m6 -> stk psegs m6 lo sp0 ->
        rw_cells psegs m6 931300 [C4 errv6] -> ps_fa st6 = ps_fa s -> ps_so st6 = ps_so s -> lx_pres LB0 sp0 [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] m m6 ->
        rw_cells psegs m6 (sp0 + 392) [C8 (Z_to_bv 64 NEW); C8 (Z_to_bv 64 (NE + 16)); C8 (Z_to_bv 64 (NEW + 16 * (cap + 1)))] ->
        rw_cells psegs m6 NE [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
        rw_cells psegs m6 NEW [CB (Z.to_nat (16 * cap)) (cells_bytes (velts els))] ->
        rw_cells psegs m6 (sp0 + 8) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 VC); C8 (Z_to_bv 64 (sp0 + 392))] ->
        evt psegs (fun ms' => impl psegs (at_node psegs) (mret (cap + 1, cap + 1, Some pn) st6)
                                   (epost (fun p => emp_post sp0 gp (Z_to_bv 64 (sp0 + 392)) s7 s8 s9 s10 s11 F fc s LB0 lo B els cap m (fst p) (snd p))) ms')
            (MS (mkR yra (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) yt0 yt1 yt2 s8 (Z_to_bv 64 NEW) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (sp0 + 392)) (Z_to_bv 64 2) (Z_to_bv 64 1152921504606846975) (Z_to_bv 64 9223372036854775792) (Z_to_bv 64 (NE + 16)) s7 (Z_to_bv 64 (NEW + 16 * (cap + 1))) s9 s10 s11 yt3 yt4 yt5 yt6)
                F (Z_to_bv 64 0x3bcdc) fc None m6 (seg_rom psegs))).
      { intros m6 st6 errv6 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HEAP6 AUX6 MI6 ST6 ERR6 FA6 SO6 PRES6 SV6 SLOT6 NPRE6 SCR6.
        ihere. to_implM. apply implM_ret. apply evt_done. unfold emp_post.
        do 18 eexists. exists m6, errv6, NEW, (cap + 1), pn, (@nil byte), (Z_to_bv 64 (NE + 16)).
        exists (cbytes (C8 (Z_to_bv 64 A))), (cbytes (C8 (Z_to_bv 64 A))), (cbytes (C8 (Z_to_bv 64 A))), (cbytes (C8 (Z_to_bv 64 VC))), (cbytes (C8 (Z_to_bv 64 (sp0 + 392)))).
        split; [replace (NE + 16) with (NEW + 16 * (cap + 1)) by lia; unfold EM_S3, EM_S4; cbv delta [mkR]; reflexivity|].
        split; [reflexivity|]. split; [clear - CAP1; lia|].
        split; [exact MI6|]. split; [exact ST6|]. split; [exact ERR6|]. split; [exact AUX6|]. split; [exact FA6|]. split; [exact SO6|].
        split; [exact HEAP6|]. split; [exact SV6|].
        split. { unfold vblk. split. { rewrite velts_app. cbn [velts fst snd]. eapply rw_cells_join; [| exact SLOT6| rewrite velts_size; unfold zlength in ELS; lia].
                   eapply rw_cells_recast; [exact NPRE6| apply velts_wf| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| rewrite velts_size; cbn [cells_size csize]; unfold zlength in ELS; lia]. }
                 split. { replace (NEW + 16 * (cap + 1)) with (NE + 16) by lia. replace (Z.to_nat (16 * (cap + 1 - (cap + 1)))) with 0%nat by lia.
                          destruct SLOT6 as [[_ _] [W0 [W1 W2]]]. split; [split; [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; apply bytes_at_nil; lia]|].
                          cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
                 split; [exact BRN| lia]. }
        split; [| exact PRES6]. apply (scratch_junk5 _ _ _ _ _ _ _ SCR6); reflexivity. }
      unhide BLK. unfold vblk in BLK. destruct blk as [b|].
      +
        destruct BLK as (_ & _ & (AP & _) & C1).
        if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].

        zstep. zstep. step. step.
        cbn [vblocks app] in HEAP5.
        pose proof (RHEAP_pull _ [(pn, NEW, 16 * (cap + 1))] (b, A, 16 * cap) LB0 _ HEAP5) as HEAP5'. cbn [app] in HEAP5'.
        assert (ND : List.NoDup (map blk_id ((b, A, 16 * cap) :: (pn, NEW, 16 * (cap + 1)) :: LB0))) by (eapply LH_nodup; exact HEAP5').
        ihere. to_implM. eapply implM_bind.
        { eapply (opdel_sized_proof HF) with (B := B) (lo := lo) (A := A) (n := 16 * cap);
            [exact HEAP5'| left; reflexivity| exact AUX5| lia| eassumption| exact CEIL'| unfold RFREE_STACK; lia| eassumption| assumption| lia]. }
        cbv beta. intros [] s6' ms6 PO. unfold free_postZ in PO.
        destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m6
                        & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
        rewrite (lb_remove_hd _ _ _ _ ND) in HP6, HEAP6.
        replace (ret_pc (Z_to_bv 64 0x3bcdc)) with (Z_to_bv 64 0x3bcdc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_of_heap_pres _ _ _ _ HP6) as AG6.
        unfold implM. iprefix.
        apply FIN with (errv6 := errv2); try assumption.
        * congruence.
        * congruence.
        * eapply lx_pres_trans; [exact PRES5|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP6| lia| intros b0 Hb0; right; exact Hb0].
        * eapply rw_cells_agree; [exact AG6| eassumption| intros a Ha; left; cbn in Ha; lia].
        * eapply rw_cells_agree; [exact AG6| eassumption|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right.
          exists (pn, NEW, 16 * (cap + 1)). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        * eapply rw_cells_agree; [exact AG6| eassumption|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right.
          exists (pn, NEW, 16 * (cap + 1)). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        * eapply rw_cells_agree; [exact AG6| eassumption| intros a Ha; left; cbn in Ha; lia].
      +
        destruct BLK as [AZ C0]. rewrite AZ. if_true. step.
        replace (ret_pc (Z_to_bv 64 0x3bcdc)) with (Z_to_bv 64 0x3bcdc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        ihere. to_implM. apply implM_retb. unfold implM. iprefix. cbn [vblocks app] in HEAP5.
        apply FIN with (errv6 := errv2); try assumption; try reflexivity; rewrite AZ in *; assumption.
  Qed.

  Lemma empl_loop : forall (cnt : nat) {R} (k : vec -> M PState R) (Q : R -> PState -> machine_state -> Prop)
      (x1 gp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 mc : mem) (s0st sc : PState) (LB0 : list block) (sp0 lo B : Z) (errv : word)
      (A cap size : Z) (blk : option bptr) (els0 elsc : list (Z * Z)) (P : nat) (jr : list byte) (c48 c56 c64 c72 c80 : list byte) (vs0 : Z),
    (0 < cnt)%nat -> P = 2%nat -> Z.of_nat P = size + Z.of_nat cnt -> elsc ++ repeat (0, 0) cnt = els0 ++ repeat (0, 0) (P - length els0) ->
    RHEAP sc (vblocks blk A cap ++ LB0) mc -> rauxv_ok mc B -> sp0 + 528 <= B -> B < 2^63 ->
    stk psegs mc lo sp0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 - (32 + RMALLOC_STACK) ->
    rw_cells psegs mc LX_ERRNO [C4 errv] -> mem_inv psegs mc -> sp0 mod 16 = 0 ->
    vrep mc (sp0 + 392) A (cap, size, blk) elsc jr -> cap <= Z.max 2 (2 * size) -> 0 <= size < 2 -> (blk = None <-> elsc = []) ->
    s1 = Z_to_bv 64 (sp0 + 392) -> vs0 = 16 * size ->
    rw_cells psegs mc (sp0 + 8) [CB 8 c48; CB 8 c56; CB 8 c64; CB 8 c72; CB 8 c80] ->
    ps_fa sc = ps_fa s0st -> ps_so sc = ps_so s0st -> lx_pres LB0 sp0 [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] m0 mc ->
    (forall v' s' ms', empl_post sp0 gp s1 s7 s8 s9 s10 s11 F fc s0st LB0 lo B els0 P m0 v' s' ms' -> implM psegs (k v') s' Q ms') ->
    implM psegs (mbind (vpushes lops cnt (cap, size, blk)) k) sc Q
      (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s8 (Z_to_bv 64 vs0) (Z_to_bv 64 A) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s1 (Z_to_bv 64 2) (Z_to_bv 64 EM_S3) (Z_to_bv 64 EM_S4) (Z_to_bv 64 (A + 16 * size)) s7 s6 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3bc3c) fc None mc (seg_rom psegs)).
  Proof.
    induction cnt as [|cnt IH]; intros until vs0; intros CNT P2 HP HE HEAP AUX QB B63 ST CEIL GLO LO ERR MI AL16 VR CAPB SZB BN Hs1 Hvs0 SCR FA SO PRES HK; [lia|].
    unfold RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 931300) by reflexivity. rewrite ELX in ERR.
    assert (ELS : size = zlength elsc) by (destruct VR as (E & _); exact E).
    rewrite vpushes_S. apply implM_bind_assoc.
    eapply implM_bind.
    { eapply (empl_push) with (B := B) (lo := lo); try eassumption; try lia; rewrite ELX; exact ERR. }
    cbv beta. intros v1 st1 ms1 PO. unfold emp_post in PO.
    destruct PO as (y1 & y5 & y6 & y7 & y8 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y22 & y28 & y29 & y30 & y31 & m1 & errv1 & A1 & cap1 & b1 & jr1 & e1
                    & d48 & d56 & d64 & d72 & d80 & -> & Ev1 & CAP1 & MI1 & ST1 & ERR1 & AUX1 & FA1 & SO1 & HEAP1 & SV1 & BLK1 & SCR1 & PRES1).
    subst v1. rewrite ELX in ERR1.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP1 ltac:(right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (ELS1 : size + 1 = zlength (elsc ++ [(0, 0)])) by (unfold zlength in *; rewrite length_app; cbn [length]; lia).
    pose proof BLK1 as BLK1'. unfold vblk in BLK1'. destruct BLK1' as (_ & _ & (A10 & _ & _ & A1C & _) & C11). unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in A1C.
    hide BLK1.
    pose proof (munch_refl [(sp0 + 392, sp0 + 416)]%Z m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    unfold implM. iprefix.

    step. zstep. replace (A1 + 16 * (size + 1) + - A1) with (16 * (size + 1)) by lia.
    zstep. rewrite (signed_small (16 * (size + 1))) by lia. rewrite (shiftr_16_4 (size + 1)) by lia.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HEAP2 : RHEAP st1 ((b1, A1, 16 * cap1) :: LB0) m2).
    { eapply LH_frame; [exact HEAP1| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX2 : rauxv_ok m2 B).
    { eapply rauxv_ok_frame; [exact AUX1| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES2 : lx_pres LB0 sp0 [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] m0 m2).
    { eapply lx_pres_trans; [exact PRES| eapply lx_pres_trans; [exact PRES1|]]. eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. clear - HX. lia. }
    unhide BLK1. apply (vblk_agree _ _ _ _ _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in BLK1; [| intros a _ Ha; cbn [outside]; clear - Ha A1C CEIL LO; lia| exact ELS1| clear - CAP1 SZB; lia].
    assert (VR2 : vrep m2 (sp0 + 392) A1 (cap1, size + 1, Some b1) (elsc ++ [(0, 0)]) jr1).
    { split; [exact ELS1|]. split; [lia|]. split; [| exact BLK1]. lazymatch goal with H : rw_cells psegs m2 (sp0 + 392) _ |- _ => exact H end. }
    clear MU WM.
    if_cases K; zify_cond K.
    -
      ihere. to_implM.
      eapply (IH _ k Q) with (B := B) (lo := lo) (els0 := els0) (P := P) (m0 := m0) (s0st := s0st) (sc := st1);
        try eassumption; try lia; try congruence.
      + rewrite <- HE, <- app_assoc. reflexivity.
      + cbn [vblocks app]. exact HEAP2.
      + split; [discriminate| intros E; exfalso; destruct elsc; discriminate].
    -
      assert (cnt = 0%nat) as -> by lia. rewrite vpushes_O.
      ihere. to_implM. apply implM_ret_bind. apply HK. unfold empl_post.
      do 21 eexists. exists m2, errv1, A1, cap1, b1, jr1. do 5 eexists.
      split; [unfold EM_S3, EM_S4; cbv delta [mkR]; reflexivity|].
      split; [f_equal; f_equal; lia|]. split; [clear - CAP1 SZB K; lia|].
      split; [exact MI1|]. split; [assumption|]. split; [eassumption|]. split; [exact AUX2|]. split; [congruence|]. split; [congruence|].
      split; [exact HEAP2|].
      split. { rewrite <- HE. cbn [repeat]. replace (Z.of_nat P) with (size + 1) by lia. exact VR2. }
      split; [| exact PRES2]. lazymatch goal with H : rw_cells psegs m2 (sp0 + 8) _ |- _ => exact H end.
  Qed.

  Lemma empl_cps : forall {R} (k : vec -> M PState R) (Q : R -> PState -> machine_state -> Prop)
      (x1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (sp0 lo B : Z) (errv : word)
      (A cap : Z) (blk : option bptr) (els : list (Z * Z)) (jr : list byte) (c48 c56 c64 c72 c80 : list byte),
    RHEAP s (vblocks blk A cap ++ LB0) m -> rauxv_ok m B -> sp0 + 528 <= B -> B < 2^63 ->
    stk psegs m lo sp0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 - (32 + RMALLOC_STACK) ->
    rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m -> sp0 mod 16 = 0 ->
    vrep m (sp0 + 392) A (cap, zlength els, blk) els jr -> cap <= 2 * zlength els -> zlength els < 2^24 + 2 -> (blk = None <-> els = []) ->
    s1 = Z_to_bv 64 (sp0 + 392) ->
    rw_cells psegs m (sp0 + 8) [CB 8 c48; CB 8 c56; CB 8 c64; CB 8 c72; CB 8 c80] ->
    (forall v' s' ms', empl_post sp0 gp s1 s7 s8 s9 s10 s11 F fc s LB0 lo B els (Nat.max (length els) 2) m v' s' ms' -> implM psegs (k v') s' Q ms') ->
    implM psegs (mbind (vpushes lops (Nat.max (length els) 2 - length els) (cap, zlength els, blk)) k) s Q
      (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s8 s0 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s7 s6 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3bc10) fc None m (seg_rom psegs)).
  Proof.
    intros until c80; intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI AL16 VR CAPB ELB BN Hs1 SCR HK.
    unfold RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 931300) by reflexivity. rewrite ELX in ERR.
    pose proof VR as VR'. destruct VR' as (ELS & SZ & SV & BLK).
    assert (EL0 : 0 <= zlength els) by (unfold zlength; lia).
    assert (AR : 0 <= A /\ A + 16 * cap <= alloc_ceiling).
    { unfold vblk in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia]. destruct BLK as (_ & _ & (A0 & _ & _ & AC & _) & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC. lia. }
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM. iprefix.

    step. step. zstep. replace (A + 16 * zlength els + - A) with (16 * zlength els) by lia.
    zstep. rewrite (signed_small (16 * zlength els)) by lia. rewrite (shiftr_16_4 (zlength els)) by lia.
    step. step. if_cases K; zify_cond K.
    -
      replace (Nat.max (length els) 2 - length els)%nat with 0%nat by (unfold zlength in K; lia). rewrite vpushes_O.
      ihere. to_implM. apply implM_ret_bind. apply HK. unfold empl_post.
      do 21 eexists. exists m, errv, A, cap. unfold vblk in BLK. destruct blk as [b|]; [| exfalso; destruct BLK as [_ C0]; clear - K SZ C0; lia].
      exists b, jr. do 5 eexists.
      split; [cbv delta [mkR]; reflexivity|].
      split; [f_equal; f_equal; unfold zlength in *; lia|]. split; [unfold zlength in *; lia|].
      split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX|]. split; [reflexivity|]. split; [reflexivity|].
      split; [cbn [vblocks app] in HEAP; exact HEAP|].
      split. { replace (Nat.max (length els) 2 - length els)%nat with 0%nat by (unfold zlength in K; lia). cbn [repeat]. rewrite app_nil_r.
               replace (Z.of_nat (Nat.max (length els) 2)) with (zlength els) by (unfold zlength in *; lia). exact VR. }
      split; [exact SCR| apply lx_pres_refl].
    -
      step. step. step. zstep. zstep.
      ihere. to_implM.
      eapply (empl_loop (Nat.max (length els) 2 - length els) k Q) with (B := B) (lo := lo) (els0 := els) (elsc := els) (m0 := m) (P := Nat.max (length els) 2);
        try eassumption; try reflexivity; try (clear - K ELS SZ CAPB; unfold zlength in *; lia).
      apply lx_pres_refl.
  Qed.
End Proofs.
End WithCeiling0.
