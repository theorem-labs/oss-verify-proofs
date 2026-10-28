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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit F_memcpy Atp_defs Atp_kitu Atp_h_defs Atp_h_push Atp_h_find Atp_h_split.
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
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition splitinto_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B : Z) (RV FD D : Z) (d : list Z) (m : mem)
    (v' : @vec bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A' cap' : Z) (blk' : option bptr) (jr' : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ v' = (cap', zlength (poffs d), blk') /\ (d = [] <-> blk' = None) /\ cap' <= 2 * zlength (poffs d)
    /\ mem_inv usegs m' /\ stk usegs m' lo q /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (vblocks blk' A' cap' ++ LB0) m'
    /\ vrep m' RV A' v' (map (pview D) (poffs d)) jr'
    /\ rw_cells usegs m' FD [C8 (Z_to_bv 64 (D + zlength d)); C8 (Z_to_bv 64 0)]
    /\ lx_pres LB0 q [(RV, RV + 24); (FD, FD + 16)] m m'.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma splitinto_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B RV FD D : Z) (d : list Z) (errv : word)
      (v0 v8 v16 : list byte),
    RHEAP s LB0 m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (64 + 80 + 128 + RMALLOC_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m ->
    q <= RV -> RV + 24 <= FD -> FD + 16 <= B -> q mod 16 = 0 ->
    payload_ok m LB0 D d ->
    rw_cells usegs m RV [CB 8 v0; CB 8 v8; CB 8 v16] ->
    rw_cells usegs m FD [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (zlength d))] ->
    implM usegs (vpushes lops (length (atp_parts d)) vec0) s
          (splitinto_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B RV FD D d m)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 RV) (Z_to_bv 64 FD) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ATP_SPLITINTO) fc None m (seg_rom usegs)).
  Proof.
    intros until v16; intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QRV RVFD FDB Q16 PL XRV XFD.
    unfold RMALLOC_STACK, GLOBALS_TOP, ATP_SPLITINTO in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof PL as (PB & DBYT & D0 & DN & DLEN & DIN).
    assert (ZD : zlength d = Z.of_nat (length d)) by reflexivity. change (2^26) with 67108864 in DLEN.
    assert (LBL : length (to_bytes d) = length d) by apply to_bytes_length.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b0 & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    pose proof (munch_refl [(q - 80, q); (RV, RV + 24); (FD, FD + 16)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB0 q [(RV, RV + 24); (FD, FD + 16)] a -> outside [(q - 80, q); (RV, RV + 24); (FD, FD + 16)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| split; [clear -HX; lia| exact I]]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    hide PB.
    unfold implM. iprefix.

    step. carve_frame 64%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. step. step. if_lia. step. step. step. hstep. hstep. hstep. step.
    destruct d as [|c0 d'] eqn:Ed.
    -
      if_cases K; zify_cond K; [| exfalso; unfold zlength in K; cbn [length Z.of_nat] in K; lia]. clear K.

      step. step. step. step. step. release_frame FR ST q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      ihere. to_implM. cbn [atp_parts length]. rewrite vpushes_O. apply implM_ret.
      apply evt_done. unfold splitinto_post. do 15 eexists. exists m1, errv, 0, 0, (@None bptr), (@nil byte).
      split; [cbv delta [mkR]; reflexivity|].
      split; [reflexivity|]. split; [tauto|]. split; [unfold zlength; cbn [poffs length Z.of_nat]; lia|].
      split; [assumption|]. split; [assumption|]. split; [exact ERR|].
      split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
               constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      split; [reflexivity|]. split; [reflexivity|].
      split. { cbn [vblocks app]. eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|].
               constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      split. { unfold vrep, vblk. cbn [map poffs zlength length Z.of_nat]. split; [reflexivity|]. split; [lia|]. split; [| split; reflexivity].
               lazymatch goal with H : rw_cells usegs m1 RV _ |- _ => exact H end. }
      split. { replace (D + zlength []) with D by (unfold zlength; cbn; lia). lazymatch goal with H : rw_cells usegs m1 FD _ |- _ => exact H end. }
      eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI].
    -
      rewrite <- Ed in *. assert (DNE : d <> []) by (rewrite Ed; discriminate). clear Ed c0 d'.
      assert (ZNZ : zlength d <> 0) by (destruct d; [congruence| unfold zlength; cbn [length]; lia]).
      assert (DR : D + zlength d <= alloc_ceiling).
      { destruct DIN as [E0|(b0 & Hb & Hb1 & Hb2)]; [congruence|]. pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & R4 & _).
        unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in R4. lia. }
      if_cases K; zify_cond K; [exfalso; lia|]. clear K.

      step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HEAP1 : RHEAP s LB0 m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|].
        constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
        constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES1 : lx_pres LB0 q [(RV, RV + 24); (FD, FD + 16)] m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).

      destruct (rw_cells_split_at _ _ _ 3%nat FR) as [TMP FRB]. cbn [firstn skipn cells_size csize Nat.add] in TMP, FRB.
      destruct (rw_cells_split_at _ _ _ 1%nat FRB) as [HLD SAV]. cbn [firstn skipn cells_size csize Nat.add] in HLD, SAV. clear FR FRB.
      replace (q + -64 + Z.of_nat 24) with (q + -40) in HLD by lia. replace (q + -64 + Z.of_nat 24 + Z.of_nat 8) with (q + -32) in SAV by lia.
      lazymatch goal with H : rw_cells usegs m1 RV _ |- _ => rename H into XRV1 end.
      lazymatch goal with H : rw_cells usegs m1 FD _ |- _ => rename H into XFD1 end.
      unhide PB.
      assert (PB1 : bytes_at usegs m1 D (to_bytes d)).
      { eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact PB|]. rewrite LBL. intros a Ha.
        destruct DIN as [E0|(b0 & Hb & Hb1 & Hb2)]; [congruence|]. pose proof (BLB a ltac:(exists b0; split; [exact Hb| unfold zlength in Hb2; lia])). cbn [outside].
        repeat split; try exact I; lia. }
      clear PB. hide MU. hide WM.
      ihere. to_implM.
      replace (atp_parts d) with (parts_of d) by (rewrite atp_parts_eq; destruct d; [congruence| reflexivity]).
      eapply implM_post_evt.
      { eapply (split_spec_s HM HF) with (B := B) (lo := lo) (V := q + -64);
          [exact DNE| exact DBYT| lia| | lia| lia| exact B63| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RMALLOC_STACK; lia| lia| lia
          | exact HEAP1| exact AUX1| assumption| exact ST| rewrite ELX; eassumption| exact PB1| exact TMP].
        destruct DIN as [E0|DIN']; [congruence| exact DIN']. }
      cbv beta. intros v' st' ms' PO. unfold split_post in PO.
      destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & A2 & cap2 & blk2 & jr2
                      & -> & Ev' & BNN & Ecap2 & MI2 & ST2 & ERR2 & AUX2 & FA2 & SO2 & HEAP2 & VR2 & PRES2).
      replace (ret_pc (Z_to_bv 64 0x3c594)) with (Z_to_bv 64 0x3c594) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR2. subst v'.

      pose proof (agree_of_lx_pres _ _ _ _ _ PRES2) as AG2.
      assert (CL : forall a, q + -40 <= a < B -> lx_client LB0 (q + -64) [(q + -64, q + -64 + 24)] a).
      { intros a Ha. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
      apply (rw_cells_agree _ _ _ _ _ AG2) in HLD; [| intros a Ha; cbn in Ha; apply CL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in SAV; [| intros a Ha; cbn in Ha; apply CL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in XRV1; [| intros a Ha; cbn in Ha; apply CL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in XFD1; [| intros a Ha; cbn in Ha; apply CL; lia].
      assert (BLB2 : forall a, in_block LB0 a -> a < alloc_ceiling).
      { intros a (b0 & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
        unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
      assert (PRES2' : lx_pres LB0 q [(RV, RV + 24); (FD, FD + 16)] m m2).
      { eapply lx_pres_trans; [exact PRES1|]. eapply (lx_pres_sub LB0 q _ _ _ _ _ _ PRES2); [lia| intros b0 Hb0; exact Hb0|].
        intros a Ha NX. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; specialize (BLB2 a IB); lia| lia]. }
      destruct VR2 as (ELS2 & SZ2 & SV2 & BLK2). hide BLK2.
      unhide MU. unhide WM. clear MU WM AG2 PRES1 HEAP1 AUX1.
      pose proof (munch_refl [(q - 80, q); (RV, RV + 24); (FD, FD + 16)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.

      step. step.
      step. carve_frame 16%nat ST2.
      apply (rw_cells_split_CB usegs _ _ [] 16 junk0 [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
      clear TMP ST PB1 MI.
      hstep. step. step. step. step. if_true.
      step. step. step. release_frame FR ST2 (q + -64). step.

      step. step. step. hstep. hstep. hstep. step. step. step.

      step. astep. step. step. step. if_lia. astep. rewrite (land7_mod8 (q + -64)) by lia. step. if_false. step. step. if_true. step.

      step. step. zstep. step. if_lia. astep. astep.
      replace (0 <? D) with true by (symmetry; apply Z.ltb_lt; lia).
      first [ replace (zlength d + D <? 1) with false by (symmetry; apply Z.ltb_ge; lia) | idtac ].
      first [ replace (D + zlength d <? 1) with false by (symmetry; apply Z.ltb_ge; lia) | idtac ].
      cbn [Z.b2z Z.lxor Pos.lxor]. astep. step. if_false. step. hstep.

      lazymatch goal with H : rw_cells usegs _ (q + -64) _ |- _ => rename H into TMP end.
      lazymatch goal with H : rw_cells usegs _ (q + -40) _ |- _ => rename H into HLD2 end.
      pose proof (rw_cells_join _ _ _ _ _ TMP HLD2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
      pose proof (rw_cells_join _ _ _ _ _ J1 SAV ltac:(cbn [cells_size csize Nat.add]; lia)) as FR. cbn [app] in FR. clear TMP HLD2 SAV J1.
      step. step. step. step. step. release_frame FR ST2 q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG3.
      unhide BLK2.
      assert (BKR : forall a, blk2 <> None -> A2 <= a < A2 + 16 * cap2 -> a < alloc_ceiling).
      { intros a Hb Ha. destruct blk2 as [b0|]; [| congruence]. unfold vblk in BLK2. destruct BLK2 as (_ & _ & (A00 & _ & _ & A0C & _) & _).
        unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in A0C. lia. }
      apply evt_done. unfold splitinto_post. do 15 eexists. exists m3, errv2, A2, cap2, blk2, jr2.
      split; [atp_st_eq_goal|].
      split; [reflexivity|]. split; [split; [intros E; exfalso; exact (DNE E)| intros E; exfalso; exact (BNN E)]|]. split; [exact Ecap2|].
      split; [assumption|]. split; [assumption|]. split; [eassumption|].
      split. { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
               constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      split; [exact FA2|]. split; [exact SO2|].
      split. { eapply LH_frame; [exact HEAP2| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|].
               constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      split. { split; [exact ELS2|]. split; [exact SZ2|]. split; [lazymatch goal with H : rw_cells usegs m3 RV _ |- _ => exact H end|].
               eapply vblk_agree; [exact AG3| | exact ELS2| exact SZ2| exact BLK2]. intros a Hb Ha. specialize (BKR a Hb Ha). cbn [outside]. lia. }
      split. { lazymatch goal with H : rw_cells usegs m3 FD _ |- _ =>
                 lazymatch type of H with rw_cells _ _ _ [C8 (Z_to_bv 64 ?e); _] => replace e with (D + zlength d) in H by lia end; exact H end. }
      eapply lx_pres_trans; [exact PRES2'|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| split; [clear -HX; lia| exact I]]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB2 a HC); lia| lia].
  Qed.
End Proofs.
End WithCeiling0.
