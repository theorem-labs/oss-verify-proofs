(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel AtpModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit F_memcpy Atp_defs Atp_kitu Atp_h_defs Atp_h_push.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition EMPL_PC : Z := 0x3c124.
Definition EMPL_RET : Z := 0x3c144.

Definition empl_post (sp0 : Z) (gp s6 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B : Z) (els : list (Z * Z)) (P : nat) (m : mem)
    (v' : @vec bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 t3 t4 t5 t6 m' (errv' : word) (A' cap' : Z) (b' : bptr) (jr' : list byte)
                    (c48 c56 c64 c72 c80 : list byte),
    ms' = MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 EMPL_RET) fc None m' (seg_rom usegs)
    /\ v' = (cap', Z.of_nat P, Some b') /\ cap' < 2^26
    /\ mem_inv usegs m' /\ stk usegs m' lo sp0 /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((b', A', 16 * cap') :: LB0) m'
    /\ vrep m' (sp0 + 392) A' v' (els ++ repeat (0, 0) (P - length els)) jr'
    /\ rw_cells usegs m' (sp0 + 8) [CB 8 c48; CB 8 c56; CB 8 c64; CB 8 c72; CB 8 c80]
    /\ lx_pres LB0 sp0 [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] m m'.

Ltac br_no := first [if_false | if_lia].
Ltac b2z_false := match goal with |- context [Z.b2z (?a <? ?b)] => replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) end.
Ltac b2z_true := match goal with |- context [Z.b2z (?a <? ?b)] => replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) end.
Ltac b2z_lit := repeat match goal with |- context [Z.b2z ?c] => let v := eval vm_compute in (Z.b2z c) in change (Z.b2z c) with v end.
Ltac land7 := match goal with |- context [Z.land ?x 7] => rewrite (land7_mod8 x) by lia end.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma empl_spec : forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
      (V A cap size : Z) (blk : option bptr) (els : list (Z * Z)) (jr : list byte),
    RHEAP s (vblocks blk A cap ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (128 + RMALLOC_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m ->
    q <= V -> V + 24 <= B ->
    vrep m V A (cap, size, blk) els jr -> cap < 2^26 ->
    implM usegs (vpush lops (cap, size, blk)) s
          (push_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B V 0 0 cap size els m)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ATP_EMPL) fc None m (seg_rom usegs)).
  Proof.
    intros until jr. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QV VB VR CAPB.
    unfold ATP_EMPL, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    destruct VR as (ELS & SZ & SV & BLK).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    remember (A + 16 * size) as VE eqn:EVE. remember (A + 16 * cap) as VC eqn:EVC.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    unfold vpush. cbn [bind ret lops Target.ops].
    destruct (Z.ltb_spec size cap) as [LT|GE].
    -
      unfold vblk in BLK. rewrite <- EVE in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia].
      destruct BLK as (BE & BJ & BR & C1). pose proof BR as (A0 & A16 & _ & AC & AS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC.
      hide BE. hide BJ.
      pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
      apply implM_ret. unfold push_post.
      step. carve_frame 64%nat ST.
      apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8;8;8;8;8; 8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

      step. step. step. step. step. step. step.
      if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.

      step. br_no. zstep. step. br_no. zstep. land7. step. br_no.

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
      clear MU WM. pose proof (munch_refl [(q - 64, q); (VE, VE + 16); (V, V + 24)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.
      remember (Z.to_nat (16 * (cap - size - 1))) as r eqn:Hr.
      replace (Z.to_nat (16 * (cap - size))) with (8 + (8 + r))%nat in BJ by lia.
      apply (rw_cells_split_CB usegs _ _ [] _ jr [] [8; 8; r]%nat) in BJ; [| cbn; lia]. cbn [mk_CB_cells app] in BJ.

      hstep. hstep. zstep. step. step.

      zstep. step. step. br_no. step. br_no. zstep. zstep. land7. step. br_no.

      step. step. step. step. release_frame FR ST q. step.
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
      lazymatch goal with H : rw_cells usegs m9 VE _ |- _ => rename H into BJ9 end.
      destruct (Sj_stage1_kit.rw_cells_app usegs m9 VE [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB r (take r (drop 8 (drop 8 jr)))]) as [SPL _].
      destruct (SPL BJ9) as [SLOT TAIL]. clear SPL BJ9. cbn [cells_size csize Nat.add] in TAIL.
      lazymatch goal with H : rw_cells usegs m9 V _ |- _ => rename H into SV9 end.
      apply evt_done. do 15 eexists. exists m9, errv, A, cap, (Some b), (take r (drop 8 (drop 8 jr))).
      split; [atp_st_eq_goal|].
      split; [reflexivity|]. split; [replace (size <? cap) with true by (symmetry; apply Z.ltb_lt; exact LT); reflexivity|]. split; [discriminate|].
      split; [assumption|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX9|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact HEAP9|]. split; [| exact PRES9].

      split; [unfold zlength in *; rewrite length_app; cbn [length]; lia|]. split; [lia|]. split.
      { lazymatch type of SV9 with rw_cells _ _ _ [_; C8 (Z_to_bv 64 ?e); _] => replace e with (A + 16 * (size + 1)) in SV9 by lia end. rewrite EVC in SV9. exact SV9. }
      split. { rewrite velts_app. cbn [velts fst snd]. eapply rw_cells_join; [exact BE| exact SLOT| rewrite velts_size; unfold zlength in ELS; lia]. }
      split. { replace (A + 16 * (size + 1)) with (VE + Z.of_nat 16) by lia. replace (Z.to_nat (16 * (cap - (size + 1)))) with r by lia. exact TAIL. }
      split; [exact BR| exact C1].
    -
      assert (SC : size = cap) by lia. rewrite SC in *. clear SC GE.
      assert (AR : 0 <= A /\ A + 16 * cap <= alloc_ceiling /\ (A = 0 \/ A mod 16 = 0) /\ (A + 16 * cap <= 0x10000 \/ 0x111000 <= A)).
      { unfold vblk in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia]. destruct BLK as (_ & _ & (A0 & A16 & _ & AC & AS) & _).
        unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC. lia. }
      destruct AR as (A0 & AC & A16 & AS).
      hide BLK.
      assert (OLDIN : forall b, blk = Some b -> In (b, A, 16 * cap) (vblocks blk A cap ++ LB0)) by (intros b ->; left; reflexivity).
      pose proof (munch_refl [(q - 96, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
      unfold implM. iprefix.
      step. carve_frame 64%nat ST.
      apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8;8;8;8;8; 8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

      step. step. step. step. step. step. step.
      replace VE with VC in * by lia. if_true.

      step. zstep. replace (VC + - A) with (16 * cap) by lia.
      zstep. rewrite (signed_small (16 * cap)) by lia. rewrite (shiftr_16_4 cap) by lia.
      zstep. zstep. rewrite (shiftr_small0 (cap + 1) 60) by lia.
      step. if_false.

      zstep. replace (VC + - A) with (16 * cap) by lia.
      zstep. rewrite (shiftr_16_3 cap) by lia.
      lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mx _) =>
        assert (REST : evt usegs QQ (MS (mkR ra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 V) s1
                               (Z_to_bv 64 (16 * cap)) (Z_to_bv 64 (vcap_next cap cap)) (Z_to_bv 64 cap) (Z_to_bv 64 (cap + 1)) (Z_to_bv 64 A) a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x3c698) fc None mx (seg_rom usegs))) end.
      2:{ step. if_cases K; zify_cond K.
          - eapply evt_eq; [| exact REST]. unfold vcap_next. atp_st_eq.
          - zstep. eapply evt_eq; [| exact REST]. unfold vcap_next. atp_st_eq. }
      assert (CAP' : cap + 1 <= vcap_next cap cap <= 2 * cap + 1) by (unfold vcap_next; lia).
      set (cap' := vcap_next cap cap) in *.

      zstep. zstep. step. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K CAPB SZ; lia].
      step. step. step.
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
      apply (proj1 (Sj_stage1_kit.rw_cells_app usegs _ _ [_; _; _; _; _] _)) in FR. destruct FR as [SBC FRH]. cbn [cells_size csize Nat.add] in FRH.
      replace (q - Z.of_nat 64 + Z.of_nat 40) with (q + -24) in FRH by lia.
      replace (q - Z.of_nat 64) with (q + -64) in SBC by lia.
      ihere. to_implM. change VELT with 16.
      eapply implM_bind.
      { eapply (grow_spec HM) with (B := B) (lo := lo);
          [exact HEAP1| exact AUX1| lia| exact B63| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| assumption| lia
          | lia| lia| lia| lia| lia| exact SBC| lia| lia]. }
      cbv beta. intros pn s2' ms2 PO. unfold grow_post in PO.
      destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW & jnew
                      & -> & MI2 & ST2 & ERR2 & AUX2 & PRESG & FA2 & SO2 & BRN & HEAP2 & BLKN & SBC2).
      replace (ret_pc (Z_to_bv 64 0x3c6b8)) with (Z_to_bv 64 0x3c6b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR2.
      pose proof BRN as (N0 & N16 & _ & NC & NS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in NC.
      pose proof (agree_of_lx_pres _ _ _ _ _ PRESG) as AG.
      apply (rw_cells_agree _ _ _ _ _ AG) in FRH; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in SV; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG) in BLK;
        [| intros a Hb Ha; destruct blk as [b|]; [| congruence]; split; [cbn [rin_ivs fst snd]; clear - Ha AC CEIL LO; lia| right; left; exists (b, A, 16 * cap); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]]
         | exact ELS| exact SZ].
      assert (PRES2 : lx_pres LB0 q [(V, V + 24)] m m2).
      { eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_sub; [exact PRESG| lia| intros b Hb; apply in_or_app; right; exact Hb|].
        intros a Ha Hna. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros Hb; pose proof (BLB a Hb); lia| unfold GLOBALS_TOP in *; lia]. }

      assert (SEPN : forall b, blk = Some b -> NEW + 16 * cap' <= A \/ A + 16 * cap <= NEW).
      { intros b Hb. exact (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP2 (OLDIN b Hb)). }
      clear AG PRES1 HEAP1 AUX1 PRESG.

      remember (NEW + 16 * cap) as NE eqn:ENE. remember (Z.to_nat (16 * (cap' - cap - 1))) as r eqn:Hr.
      replace (Z.to_nat (16 * cap')) with (Z.to_nat (16 * cap) + (16 + r))%nat in BLKN by lia.
      apply rw_cells_CB_split2 in BLKN. destruct BLKN as [NPRE NREST]. rewrite Z2Nat.id in NREST by lia. rewrite <- ENE in NREST.
      apply (rw_cells_split_CB usegs _ _ [] _ _ [] [8; 8; r]%nat) in NREST; [| cbn; lia]. cbn [mk_CB_cells app] in NREST.
      hide BLK.
      pose proof (munch_refl [(q - 96, q); (V, V + 24); (NEW, NE + 16)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      unfold implM. iprefix.

      step. try rewrite <- ENE. step. br_no. zstep. land7. step. br_no. hstep. hstep.

      step. step. br_no. zstep. step. br_no. zstep. step.

      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      lazymatch goal with H : rw_cells usegs m3 (q + -64) _ |- _ => rename H into SBC3 end.
      lazymatch goal with H : rw_cells usegs m3 V _ |- _ => rename H into SV3 end.
      lazymatch goal with H : mem_inv usegs m3 |- _ => rename H into MI3 end.
      lazymatch goal with H : stk usegs m3 _ _ |- _ => rename H into ST3 end.

      pose proof (agree_on_of_munch _ _ _ MU WM) as AG23.
      unhide BLK. apply (vblk_agree _ _ _ _ _ _ _ _ _ AG23) in BLK;
        [| intros a Hb Ha; destruct blk as [b|]; [| congruence]; specialize (SEPN b eq_refl); cbn [outside]; repeat split; clear - Ha SEPN ENE AC CEIL LO CAP' QV SZ; lia
         | exact ELS| exact SZ].
      assert (SRCB : bytes_at usegs m3 A (cells_bytes (velts els))).
      { unfold vblk in BLK. destruct blk as [b|].
        - destruct BLK as ([[_ HB] _] & _). exact HB.
        - destruct BLK as [AZ C0]. assert (els = []) as -> by (destruct els; [reflexivity| unfold zlength in ELS; cbn in ELS; lia]).
          rewrite AZ. unfold bytes_at. rewrite velts_bytes_length. cbn [length Nat.mul Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
      assert (SEP : A + 16 * cap <= NEW \/ NEW + 16 * cap <= A).
      { destruct blk as [b|]; [specialize (SEPN b eq_refl); clear - SEPN CAP' SZ; lia|]. unfold vblk in BLK. destruct BLK as [-> C0]. clear - C0 N0. lia. }
      rewrite EVC in SV3.
      lazymatch goal with H : rw_cells usegs m3 NEW _ |- _ => rename H into NPRE3 end.
      lazymatch type of SBC3 with rw_cells _ _ _ [_; _; C8 (Z_to_bv 64 ?e); _; _] => replace e with (NEW + 16 * cap + 16) in SBC3 by lia end.
      rewrite ENE in SBC3.
      eapply evt_cut.
      { eapply reloc_spec with (lo := lo) (els := els);
          [exact ST3| lia| lia| lia| exact MI3| exact SV3| lia| lia| exact SBC3| lia| lia| lia| exact SRCB| symmetry; exact ELS| lia| clear - A16; lia| lia| lia| lia
          | exact NPRE3| lia| lia| lia| lia| exact SEP]. }
      intros ms' PO. unfold reloc_post in PO.
      destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & ST4 & SV4 & SBC4 & NPRE4).
      replace (ret_pc (Z_to_bv 64 0x3c6f4)) with (Z_to_bv 64 0x3c6f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear SRCB SV3 SBC3 NPRE3 MI3 ST3. hide BLK.
      transport_after_call usegs m3 m4 MU4 WM4.
      clear MU4 WM4 AG23.
      rewrite <- ?ENE in SV4. rewrite <- ?ENE in NPRE4.

      step. step. step.
      assert (HEAP4 : RHEAP s2' ((pn, NEW, 16 * cap') :: vblocks blk A cap ++ LB0) m4).
      { eapply LH_frame; [exact HEAP2| exact MU| exact WM|].
        constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
        eapply (W_ok_block _ (pn, NEW, 16 * cap')); [left; reflexivity| cbn; lia| cbn; lia]. }
      assert (AUX4 : rauxv_ok m4 B).
      { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|].
        constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
        constructor; [cbn; unfold RAUXV_CELL; clear - ENE NC NS N0 CEIL LO SZ CAP' QB; lia| constructor]. }
      assert (PRES4 : lx_pres LB0 q [(V, V + 24)] m m4).
      { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
        pose proof (LH_head_disj _ _ _ _ _ _ HEAP2) as DJN.
        intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| split; [| exact I]]].
        + destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
        + destruct HC as [HC|[HC|HC]]; [clear - HC ENE NC CEIL LO SZ CAP'; lia| | clear - HC ENE NS N0 SZ CAP' CAPB; lia].
          intros Hs. apply (DJN a); [| clear - Hs ENE SZ CAP'; lia]. eapply in_block_incl; [| exact HC]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
      ihere. to_implM.
      eapply implM_bind.
      { eapply (sbdtor_spec HF) with (LB := (pn, NEW, 16 * cap') :: LB0) (blk := blk) (A := A) (cap := cap) (B := B) (lo := lo) (ALLOC := V);
          [ destruct blk as [b|]; [cbn [vblocks app]; apply (RHEAP_pull _ [(pn, NEW, 16 * cap')] (b, A, 16 * cap) LB0); cbn [app]; cbn [vblocks app] in HEAP4; exact HEAP4
                                 | cbn [vblocks app] in HEAP4 |- *; exact HEAP4]
          | intros Hn; unhide BLK; rewrite Hn in BLK; unfold vblk in BLK; destruct BLK as [AZ _]; exact AZ
          | intros Hn; destruct blk as [b|]; [| congruence]; unhide BLK; unfold vblk in BLK; destruct BLK as (_ & _ & (AP & _) & _); exact AP
          | reflexivity| lia| lia| exact AUX4| lia| exact ST4| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR2| exact MI4| lia| lia| exact SBC4| lia| lia]. }
      cbv beta. intros [] st5 ms5 PO. unfold sbdtor_post in PO.
      destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m5 & errv5
                      & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & HEAP5).
      replace (ret_pc (Z_to_bv 64 0x3c700)) with (Z_to_bv 64 0x3c700) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR5.
      pose proof (agree_of_heap_pres _ _ _ _ HP5) as AG5.
      apply (rw_cells_agree _ _ _ _ _ AG5) in FRH; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in SBC4; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in SV4; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG5) in NPRE4; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; right; right; exists (pn, NEW, 16 * cap'); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]].
      lazymatch goal with H : rw_cells usegs m4 NE _ |- _ => rename H into NREST4 end.
      apply (rw_cells_agree _ _ _ _ _ AG5) in NREST4; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; right; right; exists (pn, NEW, 16 * cap'); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]].
      assert (PRES5 : lx_pres LB0 q [(V, V + 24)] m m5).
      { eapply lx_pres_trans; [exact PRES4|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP5| lia| intros b0 Hb0; right; exact Hb0]. }
      clear AG5 HP5 MU WM.
      pose proof (munch_refl [(q - 64, q); (V, V + 24)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
      unfold implM. iprefix.

      zstep. step. step. br_no. step. br_no. zstep. zstep. land7. step. br_no.
      destruct (rw_cells_forget _ _ _ _ SBC4) as [jsb SBF]. cbn [cells_size csize Nat.add] in SBF.
      pose proof (rw_cells_join _ _ _ _ _ SBF FRH ltac:(cbn [cells_size csize Nat.add]; lia)) as FR. cbn [app] in FR.
      step. step. step. step. release_frame FR ST5 q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      lazymatch goal with H : rw_cells usegs m9 V _ |- _ => rename H into SV9 end.
      destruct (Sj_stage1_kit.rw_cells_app usegs m9 NE [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB r (take r (drop 8 (drop 8 (drop (Z.to_nat (16 * cap)) jnew))))]) as [SPL _].
      destruct (SPL NREST4) as [SLOT TAIL]. clear SPL NREST4. cbn [cells_size csize Nat.add] in TAIL.
      ihere. to_implM. apply implM_ret. apply evt_done. unfold push_post.
      do 15 eexists. exists m9, errv5, NEW, cap', (Some pn), (take r (drop 8 (drop 8 (drop (Z.to_nat (16 * cap)) jnew)))).
      split; [atp_st_eq_goal|].
      split; [reflexivity|]. split; [rewrite Z.ltb_irrefl; reflexivity|]. split; [discriminate|].
      split; [assumption|]. split; [assumption|]. split; [exact ERR5|].
      split. { eapply rauxv_ok_frame; [exact AUX5| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      split; [rewrite FA5; exact FA2|]. split; [rewrite SO5; exact SO2|].
      split. { cbn [vblocks app]. eapply LH_frame; [exact HEAP5| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      split.
      2:{ eapply lx_pres_trans; [exact PRES5|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
          intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
          destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      split; [unfold zlength in *; rewrite length_app; cbn [length]; lia|]. split; [lia|]. split.
      { lazymatch type of SV9 with rw_cells _ _ _ [_; C8 (Z_to_bv 64 ?e); _] => replace e with (NEW + 16 * (cap + 1)) in SV9 by lia end. exact SV9. }
      unfold vblk. split. { rewrite velts_app. cbn [velts fst snd]. eapply rw_cells_join; [| exact SLOT| rewrite velts_size; unfold zlength in ELS; lia].
        eapply rw_cells_recast; [exact NPRE4| apply velts_wf| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| rewrite velts_size; cbn [cells_size csize]; unfold zlength in ELS; lia]. }
      split. { replace (NEW + 16 * (cap + 1)) with (NE + Z.of_nat 16) by lia. replace (Z.to_nat (16 * (cap' - (cap + 1)))) with r by lia. exact TAIL. }
      split; [exact BRN| lia].
  Qed.

  Lemma empl_loop : forall (cnt : nat) {R} (k : vec -> M PState R) (Q : R -> PState -> machine_state -> Prop)
      (x1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 mc : mem) (s0st sc : PState) (LB0 : list block) (sp0 lo B : Z) (errv : word)
      (A cap size : Z) (blk : option bptr) (els0 elsc : list (Z * Z)) (P : nat) (jr : list byte) (c48 c56 c64 c72 c80 : list byte),
    (2 <= P)%nat -> ((0 < cnt)%nat -> P = 2%nat) -> Z.of_nat P = size + Z.of_nat cnt -> Z.of_nat P < 2^25 ->
    elsc ++ repeat (0, 0) cnt = els0 ++ repeat (0, 0) (P - length els0) ->
    RHEAP sc (vblocks blk A cap ++ LB0) mc -> rauxv_ok mc B -> sp0 + 528 <= B -> B < 2^63 ->
    stk usegs mc lo sp0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 - (128 + RMALLOC_STACK) ->
    rw_cells usegs mc LX_ERRNO [C4 errv] -> mem_inv usegs mc ->
    vrep mc (sp0 + 392) A (cap, size, blk) elsc jr -> cap <= Z.max 2 (2 * size) ->
    rw_cells usegs mc (sp0 + 8) [CB 8 c48; CB 8 c56; CB 8 c64; CB 8 c72; CB 8 c80] ->
    ps_fa sc = ps_fa s0st -> ps_so sc = ps_so s0st -> lx_pres LB0 sp0 [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] m0 mc ->
    (forall v' s' ms', empl_post sp0 gp s6 s9 s10 s11 F fc s0st LB0 lo B els0 P m0 v' s' ms' -> implM usegs (k v') s' Q ms') ->
    implM usegs (mbind (vpushes lops cnt (cap, size, blk)) k) sc Q
      (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 (Z_to_bv 64 16) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3c128) fc None mc (seg_rom usegs)).
  Proof.
    induction cnt as [|c IH]; intros until c80; intros HP2 HPc HP PB HE HEAP AUX QB B63 ST CEIL GLO LO ERR MI VR CAPB SCR FA SO PRES HK.
    -
      pose proof VR as VR'. destruct VR' as (ELS & SZ & SV & BLK).
      assert (AR : 0 <= A /\ A + 16 * cap <= alloc_ceiling).
      { unfold vblk in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia]. destruct BLK as (_ & _ & (A0 & _ & _ & AC & _) & _).
        unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC. lia. }
      assert (SZP : size = Z.of_nat P) by lia.
      rewrite vpushes_O.
      unfold implM. iprefix.

      step. step. zstep. try (replace (A + 16 * size + - A) with (16 * size) by lia).
      step. if_cases K; zify_cond K; rewrite (land_ones64 A) in K by lia; replace (A + 16 * size + - A) with (16 * size) in K by lia; rewrite (land_ones64 (16 * size)) in K by lia; [clear K| exfalso; lia].
      ihere. to_implM. apply implM_ret_bind. apply HK. unfold empl_post.
      unfold vblk in BLK. destruct blk as [b|]; [| exfalso; destruct BLK as [_ C0]; lia].
      do 23 eexists. exists mc, errv, A, cap, b, jr. do 5 eexists.
      split; [unfold EMPL_RET; cbv delta [mkR]; reflexivity|].
      split; [f_equal; f_equal; lia|]. split; [lia|].
      split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX|]. split; [exact FA|]. split; [exact SO|].
      split; [cbn [vblocks app] in HEAP; exact HEAP|].
      split. { rewrite <- HE. cbn [repeat]. rewrite app_nil_r. exact VR. }
      split; [exact SCR| exact PRES].
    -
      pose proof VR as VR'. destruct VR' as (ELS & SZ & SV & BLK).
      assert (AR : 0 <= A /\ A + 16 * cap <= alloc_ceiling).
      { unfold vblk in BLK. destruct blk as [b|]; [| destruct BLK as [-> ->]; lia]. destruct BLK as (_ & _ & (A0 & _ & _ & AC & _) & _).
        unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC. lia. }
      assert (P2 : P = 2%nat) by (apply HPc; lia).
      assert (SZ1 : size <= 1) by lia.
      rewrite vpushes_S. apply implM_bind_assoc.
      unfold implM. iprefix.

      step. step. zstep. try (replace (A + 16 * size + - A) with (16 * size) by lia).
      step. if_cases K; zify_cond K; rewrite (land_ones64 A) in K by lia; replace (A + 16 * size + - A) with (16 * size) in K by lia; rewrite (land_ones64 (16 * size)) in K by lia; [exfalso; lia| clear K].
      zstep. step.
      ihere. to_implM. eapply implM_bind.
      { eapply empl_spec with (B := B) (lo := lo) (V := sp0 + 392);
          [exact HEAP| exact AUX| lia| exact B63| exact ST| exact CEIL| exact GLO| exact LO| exact ERR| exact MI| lia| lia| exact VR| lia]. }
      cbv beta. intros v1 st1 ms1 PO. unfold push_post in PO.
      destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & errv1 & A1 & cap1 & blk1 & jr1
                      & -> & Ev1 & Ecap1 & BNN & MI1 & ST1 & ERR1 & AUX1 & FA1 & SO1 & HEAP1 & VR1 & PRES1).
      subst v1.
      lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?x)] =>
        replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
      assert (SCR1 : rw_cells usegs m1 (sp0 + 8) [CB 8 c48; CB 8 c56; CB 8 c64; CB 8 c72; CB 8 c80]).
      { eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES1)| exact SCR|].
        intros a Ha. cbn in Ha. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
      assert (PRES2 : lx_pres LB0 sp0 [(sp0 + 8, sp0 + 48); (sp0 + 392, sp0 + 416)] m0 m1).
      { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_weaken; [exact PRES1| lia| intros b0 Hb0; exact Hb0|].
        intros a Ha. cbn [rin_ivs fst snd] in Ha |- *. lia. }
      assert (CAP1 : cap1 <= Z.max 2 (2 * (size + 1))).
      { rewrite Ecap1. destruct (Z.ltb_spec size cap) as [Hl|Hl]; cbv iota; try unfold vcap_next; lia. }
      unfold implM. iprefix.

      step.
      ihere. to_implM.
      eapply (IH _ k Q) with (els0 := els0) (P := P) (m0 := m0) (s0st := s0st) (elsc := elsc ++ [(0, 0)]) (A := A1) (cap := cap1) (size := size + 1) (blk := blk1) (jr := jr1) (B := B) (lo := lo);
        [exact HP2| intros _; exact P2| lia| exact PB| rewrite <- HE, <- app_assoc; reflexivity
        | exact HEAP1| exact AUX1| exact QB| exact B63| exact ST1| exact CEIL| exact GLO| exact LO| exact ERR1| exact MI1| exact VR1| exact CAP1
        | exact SCR1| congruence| congruence| exact PRES2| exact HK].
  Qed.

  Lemma empl_cps : forall {R} (k : vec -> M PState R) (Q : R -> PState -> machine_state -> Prop)
      (x1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (sp0 lo B : Z) (errv : word)
      (A cap : Z) (blk : option bptr) (els : list (Z * Z)) (jr : list byte) (c48 c56 c64 c72 c80 : list byte),
    RHEAP s (vblocks blk A cap ++ LB0) m -> rauxv_ok m B -> sp0 + 528 <= B -> B < 2^63 ->
    stk usegs m lo sp0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 + 528 - LX_FUZZ_STACK ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> sp0 mod 16 = 0 ->
    vrep m (sp0 + 392) A (cap, zlength els, blk) els jr -> cap <= 2 * zlength els -> zlength els < 2^24 + 2 -> (blk = None <-> els = []) ->
    rw_cells usegs m (sp0 + 8) [CB 8 c48; CB 8 c56; CB 8 c64; CB 8 c72; CB 8 c80] ->
    (forall v' s' ms', empl_post sp0 gp s6 s9 s10 s11 F fc s LB0 lo B els (Nat.max (length els) 2) m v' s' ms' -> implM usegs (k v') s' Q ms') ->
    implM usegs (mbind (vpushes lops (Nat.max (length els) 2 - length els) (cap, zlength els, blk)) k) s Q
      (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EMPL_PC) fc None m (seg_rom usegs)).
  Proof.
    intros until c80; intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI AL16 VR CAPB ELB BN SCR HK.
    unfold EMPL_PC. unfold implM. iprefix.

    zstep.
    ihere. to_implM.
    eapply (empl_loop (Nat.max (length els) 2 - length els) k Q) with (els0 := els) (elsc := els) (m0 := m) (s0st := s) (P := Nat.max (length els) 2);
      [lia| intros Hc; lia| unfold zlength; lia| unfold zlength in ELB; lia| reflexivity
      | exact HEAP| exact AUX| exact QB| exact B63| exact ST| exact CEIL| exact GLO
      | unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES in LO; lia| exact ERR| exact MI| exact VR| lia
      | exact SCR| reflexivity| reflexivity| apply lx_pres_refl| exact HK].
  Qed.
End Proofs.
End WithCeiling0.
