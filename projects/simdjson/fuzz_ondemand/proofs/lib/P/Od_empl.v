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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel AtpModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit F_memcpy Atp_h_defs Atp_h_push.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Sj_stage1_kit.
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

Definition odempl_post (sp0 : Z) (gp s1 s3 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B : Z) (els : list (Z * Z)) (P : nat) (m : mem)
    (v' : @vec bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 t3 t4 t5 t6 m' (errv' : word) (A' cap' : Z) (b' : bptr) (jr' : list byte)
                    (c240 c248 c256 c264 c272 : list byte),
    ms' = MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x27268) fc None m' (seg_rom psegs)
    /\ v' = (cap', Z.of_nat P, Some b') /\ cap' < 2^26
    /\ mem_inv psegs m' /\ stk psegs m' lo sp0 /\ rw_cells psegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((b', A', 16 * cap') :: LB0) m'
    /\ vrep m' (sp0 + 360) A' v' (els ++ repeat (0, 0) (P - length els)) jr'
    /\ rw_cells psegs m' (sp0 + 240) [CB 8 c240; CB 8 c248; CB 8 c256; CB 8 c264; CB 8 c272]
    /\ lx_pres LB0 sp0 [(sp0 + 240, sp0 + 280); (sp0 + 360, sp0 + 384)] m m'.

Lemma od_scratch_junk5 : forall m A (c1 c2 c3 c4 c5 : cell), rw_cells psegs m A [c1; c2; c3; c4; c5] ->
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

  Lemma od_empl_cps : forall {R} (k : vec -> M PState R) (Q : R -> PState -> machine_state -> Prop)
      (x1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (sp0 lo B : Z) (errv : word)
      (A cap : Z) (blk : option bptr) (els : list (Z * Z)) (jr : list byte) (c240 c248 c256 c264 c272 : list byte),
    RHEAP s (vblocks blk A cap ++ LB0) m -> rauxv_ok m B -> sp0 + 512 <= B -> B < 2^63 ->
    stk psegs m lo sp0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 - (32 + RMALLOC_STACK) ->
    rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m -> sp0 mod 16 = 0 ->
    vrep m (sp0 + 360) A (cap, zlength els, blk) els jr -> cap <= 2 * zlength els -> zlength els < 2^25 -> (blk = None <-> els = []) ->
    s1 = Z_to_bv 64 (sp0 + 360) ->
    rw_cells psegs m (sp0 + 240) [CB 8 c240; CB 8 c248; CB 8 c256; CB 8 c264; CB 8 c272] ->
    (forall v' s' ms', odempl_post sp0 gp s1 s3 s7 s8 s9 s10 s11 F fc s LB0 lo B els (Nat.max (length els) 1) m v' s' ms' -> implM psegs (k v') s' Q ms') ->
    implM psegs (mbind (vpushes lops (Nat.max (length els) 1 - length els) (cap, zlength els, blk)) k) s Q
      (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x271a0) fc None m (seg_rom psegs)).
  Proof.
    intros until c272; intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI AL16 VR CAPB ELB BN Hs1 SCR HK.
    unfold RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 562956) by reflexivity. rewrite ELX in ERR.
    pose proof VR as VR'. destruct VR' as (ELS & SZ & SV & BLK).
    assert (EL0 : 0 <= zlength els) by (unfold zlength; lia).
    assert (AR : 0 <= A /\ A + 16 * cap <= alloc_ceiling).
    { unfold vblk in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia]. destruct BLK as (_ & _ & (A0 & _ & _ & AC & _) & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in AC. lia. }
    change (2^25) with 33554432 in ELB.
    subst s1.
    unfold implM. iprefix.

    step. step. step. if_cases K; zify_cond K.
    -
      rewrite ?unsigned_lit in K by lia.
      assert (NE : 1 <= zlength els) by lia.
      replace (Nat.max (length els) 1 - length els)%nat with 0%nat by (unfold zlength in NE; lia). rewrite vpushes_O.
      ihere. to_implM. apply implM_ret_bind. apply HK. unfold odempl_post.
      do 20 eexists. exists m, errv, A, cap. unfold vblk in BLK. destruct blk as [b|]; [| exfalso; destruct BLK as [_ C0]; clear - NE SZ C0; lia].
      exists b, jr. do 5 eexists.
      split; [cbv delta [mkR]; reflexivity|].
      split; [f_equal; f_equal; unfold zlength in *; lia|]. split; [unfold zlength in *; change (2^26) with 67108864; lia|].
      split; [exact MI|]. split; [exact ST|]. split; [rewrite ELX; exact ERR|]. split; [exact AUX|]. split; [reflexivity|]. split; [reflexivity|].
      split; [cbn [vblocks app] in HEAP; exact HEAP|].
      split. { replace (Nat.max (length els) 1 - length els)%nat with 0%nat by (unfold zlength in NE; lia). cbn [repeat]. rewrite app_nil_r.
               replace (Z.of_nat (Nat.max (length els) 1)) with (zlength els) by (unfold zlength in *; lia). exact VR. }
      split; [exact SCR| apply lx_pres_refl].
    -
      rewrite ?unsigned_lit in K by lia.
      assert (E0 : zlength els = 0) by lia.
      assert (ENIL : els = []) by (destruct els; [reflexivity| unfold zlength in E0; cbn [length] in E0; lia]).
      subst els. assert (BN' : blk = None) by (apply BN; reflexivity). subst blk.
      unfold vblk in BLK. destruct BLK as [AZ CZ].
      cbn [length] in *. change (Nat.max 0 1 - 0)%nat with 1%nat. change (zlength (@nil (Z * Z))) with 0 in *.
      cbn [vblocks app] in HEAP.
      remember (A + 16 * 0) as VE eqn:EVE. remember (A + 16 * cap) as VC eqn:EVC.
      assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
      { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
        unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. lia. }
      assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB0 sp0 [(sp0 + 240, sp0 + 280); (sp0 + 360, sp0 + 384)] a ->
                  outside [(sp0 + 240, sp0 + 280); (sp0 + 360, sp0 + 384)] a).
      { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. clear - HX. lia. }
      pose proof (munch_refl [(sp0 + 240, sp0 + 280); (sp0 + 360, sp0 + 384)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.

      step. step. zstep. zstep. step.

      step. step. if_cases K1; zify_cond K1; [clear K1| exfalso; rewrite ?unsigned_lit in K1 by lia; lia].

      zstep. replace (VC + - VE) with 0 by lia.
      step. if_cases K2; zify_cond K2; [clear K2| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].
      zstep. zstep. zstep.

      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HEAP1 : RHEAP s LB0 m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES1 : lx_pres LB0 sp0 [(sp0 + 240, sp0 + 280); (sp0 + 360, sp0 + 384)] m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
      clear MU WM.
      ihere. to_implM. rewrite vpushes_S. apply implM_bind_assoc.
      unfold vpush. cbn [bind ret lops Target.ops]. replace (0 <? cap) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      change VELT with 16. replace (vcap_next cap 0) with 1 by (unfold vcap_next; lia).
      apply implM_bind_assoc.
      eapply implM_bind.
      { eapply (allocate_spec HM) with (B := B) (lo := lo) (n := 1);
          [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| rewrite ELX; eassumption| assumption| lia| lia| lia]. }
      cbv beta. intros pn s2' ms2 PO. unfold alloc_post in PO.
      destruct PO as (r5 & r6 & r7 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW & jnew
                      & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA2 & SO2 & BRN & HEAP2 & BLKN).
      replace (ret_pc (Z_to_bv 64 0x27200)) with (Z_to_bv 64 0x27200) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR2.
      pose proof BRN as (N0 & N16 & _ & NC & NS). unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in NC.
      pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
      lazymatch goal with H : rw_cells psegs m1 (sp0 + 240) _ |- _ => apply (rw_cells_agree _ _ _ _ _ AG) in H; [rename H into SCR1| intros a Ha; left; cbn in Ha; lia] end.
      lazymatch goal with H : rw_cells psegs m1 (sp0 + 360) _ |- _ => apply (rw_cells_agree _ _ _ _ _ AG) in H; [rename H into SV1| intros a Ha; left; cbn in Ha; lia] end.
      assert (PRES2 : lx_pres LB0 sp0 [(sp0 + 240, sp0 + 280); (sp0 + 360, sp0 + 384)] m m2).
      { eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; exact Hb]. }
      clear AG PRES1 HEAP1 AUX1.
      change (Z.to_nat (16 * 1)) with 16%nat in BLKN.
      apply (rw_cells_split_CB psegs _ _ [] _ _ [] [8; 8]%nat) in BLKN; [| cbn; lia]. cbn [mk_CB_cells app] in BLKN.
      pose proof (munch_refl [(sp0 + 240, sp0 + 280); (sp0 + 360, sp0 + 384); (NEW, NEW + 16)]%Z m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      unfold implM. iprefix.

      hstep. hstep.

      step. step. zstep. change (Z.shiftl 1 4) with 16. zstep. zstep. zstep. replace (VE + - A) with 0 by lia. zstep. replace (NEW + - 0) with NEW by lia. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      eapply evt_cut.
      { eapply (memcpy_callZ) with (Dst := NEW) (Src := A) (N := 0) (src := []) (junk := []);
          [apply bytes_at_nil; lia| reflexivity| | lia| lia| lia| lia| assumption].
        split; [split; [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; apply bytes_at_nil; lia]|].
        cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
      intros ms' PO. unfold memcpy_postZ in PO.
      destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & NPRE4 & SRC4).
      replace (ret_pc (Z_to_bv 64 0x27230)) with (Z_to_bv 64 0x27230) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear SRC4 NPRE4.
      transport_after_call psegs m3 m4 MU4 WM4.
      clear MU4 WM4.

      step. step. step. step. step. step. step. step. step. step. step.

      step. step. step. if_true. step. step. if_cases K4; zify_cond K4; [clear K4| exfalso; rewrite ?unsigned_lit in K4 by lia; lia]. step.
      replace (ret_pc (Z_to_bv 64 0x2725c)) with (Z_to_bv 64 0x2725c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      step. step. step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia| clear K3].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      assert (HEAP5 : RHEAP s2' ((pn, NEW, 16 * 1) :: LB0) m5).
      { eapply LH_frame; [exact HEAP2| exact MU| exact WM|].
        constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
        eapply (W_ok_block _ (pn, NEW, 16 * 1)); [left; reflexivity| cbn; lia| cbn; lia]. }
      assert (AUX5 : rauxv_ok m5 B).
      { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
        constructor; [cbn; unfold RAUXV_CELL; clear - NC NS N0 CEIL LO QB; lia| constructor]. }
      assert (PRES5 : lx_pres LB0 sp0 [(sp0 + 240, sp0 + 280); (sp0 + 360, sp0 + 384)] m m5).
      { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
        pose proof (LH_head_disj _ _ _ _ _ _ HEAP2) as DJN.
        intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [clear - HX; lia| split; [clear - HX; lia| split; [| exact I]]].
        destruct HC as [HC|[HC|HC]]; [clear - HC NC CEIL LO; lia| | clear - HC NS N0; lia].
        intros Hs. apply (DJN a); [exact HC| clear - Hs; lia]. }
      ihere. to_implM. apply implM_bind_assoc. apply implM_retb. apply implM_retb. rewrite vpushes_O. apply implM_retb.
      apply HK. unfold odempl_post.
      do 20 eexists. exists m5, errv2, NEW, 1, pn, (@nil byte).
      exists (cbytes (C8 (Z_to_bv 64 A))), (cbytes (C8 (Z_to_bv 64 A))), (cbytes (C8 (Z_to_bv 64 A))), (cbytes (C8 (Z_to_bv 64 VC))), (cbytes (C8 (Z_to_bv 64 (sp0 + 360)))).
      split; [cbv delta [mkR]; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [rewrite ELX; eassumption|]. split; [exact AUX5|]. split; [congruence|]. split; [congruence|].
      split; [exact HEAP5|].
      split.
      { cbn [app repeat Nat.sub]. split; [reflexivity|]. split; [lia|].
        split. { lazymatch goal with H : rw_cells psegs m5 (sp0 + 360) _ |- _ => replace (NEW + 16 * 1) with (NEW + 16) by lia; exact H end. }
        unfold vblk. split. { cbn [velts fst snd]. lazymatch goal with H : rw_cells psegs m5 NEW _ |- _ => exact H end. }
        split. { replace (Z.to_nat (16 * (1 - 1))) with 0%nat by lia.
                 split; [split; [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; apply bytes_at_nil; lia]|].
                 cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
        split; [exact BRN| lia]. }
      split; [| exact PRES5].
      lazymatch goal with H : rw_cells psegs m5 (sp0 + 240) _ |- _ => apply (od_scratch_junk5 _ _ _ _ _ _ _ H); reflexivity end.
  Qed.
End Proofs.
End WithCeiling0.
