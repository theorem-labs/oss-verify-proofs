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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Sj_h_pdtor.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Atp_h_defs El_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Atp_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
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

Ltac readdr H e := lazymatch type of H with rw_cells _ _ ?a _ => replace a with e in H by lia end.

Lemma vdtor_loop : forall Q (x1 sp gp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (k : nat),
  16 <= A -> A + 16 * Z.of_nat k < 2^63 -> (1 <= k)%nat ->
  evt usegs Q (MS (mkR x1 sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 A) a2 (Z_to_bv 64 16) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x40d88) fc None m (seg_rom usegs)) ->
  evt usegs Q (MS (mkR x1 sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 (A + 16 * Z.of_nat k)) a2 (Z_to_bv 64 16) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x40d78) fc None m (seg_rom usegs)).
Proof.
  intros until k. intros A16 AK K1 HK.
  revert AK K1. induction k as [|k IH]; intros AK K1; [lia|].
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

  step. if_lia. step. if_lia. zstep.
  replace (A + 16 * Z.of_nat (S k) + -16) with (A + 16 * Z.of_nat k) by lia.
  step. if_cases K; zify_cond K.
  -
    apply IH; lia.
  -
    eapply evt_eq; [| exact HK]. atp_st_eq.
Qed.

Section Proofs.
  Hypothesis HF : rfree_stmt.

  Lemma vexit_cps : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (x1 t0 t1 t2 y8 y9 ya0 a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 t3 t4 t5 t6 : word)
      (m0 m : mem) (s00 st : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary errv : word) (init : bool)
      (bv : bptr) (A cap : Z) (P : nat) (jlow jmid : list byte),
    RHEAP s00 LB m0 -> lx_statics m0 -> stderr_wfile m0 -> ssp_cells m0 canary ->
    bv_unsigned sp <= B -> B < 2^62 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK -> bv_unsigned sp mod 16 = 0 ->
    RHEAP st ((bv, A, 16 * cap) :: LB) m -> rauxv_ok m B -> mem_inv usegs m -> stk usegs m lo (bv_unsigned sp - 528) -> rw_cells usegs m LX_ERRNO [C4 errv] ->
    ps_fa st = ps_fa s00 -> ps_so st = ps_so s00 -> frm0 fc ->
    lx_pres LB (bv_unsigned sp) [LXW_SJ; LXW_UNW; LXW_TP] m0 m -> rw_cells usegs m EL_TPLOC [C8 (wz EL_GLOC)] -> sj_statics m init -> payload_ok m LB D d ->
    rw_cells usegs m (bv_unsigned sp - 528) [CB 392 jlow] ->
    rw_cells usegs m (bv_unsigned sp - 528 + 392) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * Z.of_nat P)); C8 (Z_to_bv 64 (A + 16 * cap))] ->
    Z.of_nat P <= cap ->
    rw_cells usegs m (bv_unsigned sp - 528 + 416) [CB 32 jmid] ->
    rw_cells usegs m (bv_unsigned sp - 528 + 448) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    implM usegs (mbind (vfree lops (cap, Z.of_nat P, Some bv)) (fun _ => mret 0)) st
          (rfuzz_one_post ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s00 LB D d lo B canary m0)
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 528)) gp (Z_to_bv 64 RATP) t0 t1 t2 y8 y9 ya0 a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 EL_EXIT2) fc None m (seg_rom usegs)).
  Proof.
    intros until jmid. intros HEAP00 LXS0 SEW0 SSP0 SPB B63 CEIL GLO LO AL16 HEAP3 AUX3 MI3 ST3 ERR3 FA3 SO3 FRM PRES3 TPC3 SJS3 PL3 LOW SV PCAP MID SAVE.
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP, EL_EXIT2 in *. unfold MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (ESP : sp = Z_to_bv 64 (bv_unsigned sp)) by (symmetry; apply Z_to_bv_bv_unsigned).
    remember (bv_unsigned sp) as usp eqn:Eusp.
    remember (usp - 528) as sp0 eqn:Esp0.
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (LO0 : 0 <= lo) by (destruct ST3 as [? _]; assumption).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR3.
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    pose proof (LH_block_range _ _ _ _ HEAP3 ltac:(left; reflexivity)) as (A0 & A16 & _ & AC & AS).
    cbn [blk_addr blk_size fst snd] in A0, A16, AC, AS. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC.
    assert (SP8 : (sp0 + 392) mod 8 = 0).
    { clear - AL16 Esp0. pose proof (Z.mod_divide usp 16 ltac:(lia)) as [H _]. destruct (H AL16) as [q Hq]. replace (sp0 + 392) with ((2 * q - 17) * 8) by lia. apply Z.mod_mul. lia. }
    assert (L7 : Z.land (sp0 + 392) 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact SP8).
    pose proof (munch_refl [(sp0, sp0 + 528)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ND : List.NoDup (map blk_id ((bv, A, 16 * cap) :: LB))) by (eapply LH_nodup; exact HEAP3).
    unfold implM. iprefix.
    repeat (first [hstep | if_lia]).
    lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mc _) =>
    assert (VT : forall r5 r6 r7 r8 r9 r11 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r28 r29 r30 r31,
               evt usegs QQ (MS (mkR (Z_to_bv 64 0x3c288) (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) r5 r6 r7 r8 r9 (Z_to_bv 64 A) r11 (Z_to_bv 64 (sp0 + 392)) r13 r14 r15 r16 r17
                                     r18 r19 r20 r21 r22 r23 r24 s9 s10 s11 r28 r29 r30 r31)
                                F (Z_to_bv 64 0x40d88) fc None mc (seg_rom usegs))) end.
    2:{ if_cases KE; zify_cond KE.
        -   apply VT.
        -
          rewrite ?unsigned_lit in KE by lia.
          step.
          eapply (vdtor_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A P);
            [clear - A0 A16; pose proof (Z.mod_divide A 16 ltac:(lia)) as [H _]; destruct (H A16) as [q Hq]; lia| lia| lia|].
          apply VT. }
    intros r5 r6 r7 r8 r9 r11 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r28 r29 r30 r31.

    step. zstep. replace (A + 16 * cap + - A) with (16 * cap) by lia. hstep. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HEAP4 : RHEAP st ((bv, A, 16 * cap) :: LB) m4).
    { eapply LH_frame; [exact HEAP3| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [exact AUX3| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES4 : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW; LXW_TP] m0 m4).
    { rewrite Esp0. replace (usp - 528 + 528) with usp by lia. eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    assert (SJS4 : sj_statics m4 init).
    { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS3]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1.
      cbn [outside]. split; [lia| exact I]. }
    rename TPC3 into TPC4.
    assert (PL4 : payload_ok m4 LB D d).
    { eapply payload_ok_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact PL3|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I]. }
    clear MU WM.
    ihere. to_implM. cbn [vfree]. eapply implM_bind.
    { eapply (opdel_sized_proof HF) with (B := B) (lo := lo) (A := A) (n := 16 * cap);
        [exact HEAP4| left; reflexivity| exact AUX4| lia| eassumption| exact CEIL'| unfold RFREE_STACK; lia| eassumption| assumption| lia]. }
    cbv beta. intros [] st5 ms5 PO. unfold free_postZ in PO.
    destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m5
                    & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & HEAP5).
    rewrite (lb_remove_hd _ _ _ _ ND) in HP5, HEAP5.
    replace (ret_pc (Z_to_bv 64 0x3c288)) with (Z_to_bv 64 0x3c288) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_heap_pres _ _ _ _ HP5) as AG5.
    assert (FRH : forall a, sp0 <= a < sp0 + 528 -> rclient_addr LB sp0 a) by (intros a Ha; left; lia).
    lazymatch goal with H : rw_cells usegs m4 (sp0 + 392) _ |- _ => apply (rw_cells_agree _ _ _ _ _ AG5) in H; [rename H into SV5| intros a Ha; cbn in Ha; apply FRH; lia] end.
    apply (rw_cells_agree _ _ _ _ _ AG5) in LOW; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5) in MID; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5) in SAVE; [| intros a Ha; cbn in Ha; apply FRH; lia].
    pose proof (statics_heap _ _ _ _ HP5 ltac:(unfold GLOBALS_TOP; lia)) as (_ & SJSf & _). pose proof (SJSf _ SJS4) as SJS5. clear SJSf.
    assert (TPC5 : rw_cells usegs m5 EL_TPLOC [C8 (Z_to_bv 64 EL_GLOC)]).
    { eapply rw_cells_agree; [exact AG5| exact TPC4|]. intros a Ha. cbn in Ha. right; left. split; [lia|].
      unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (PL5 : payload_ok m5 LB D d).
    { eapply payload_ok_agree; [exact AG5| exact PL4|]. intros b a Hb Ha. right; right. exists b. split; [exact Hb| exact Ha]. }
    assert (PRES5 : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW; LXW_TP] m0 m5).
    { eapply lx_pres_trans; [exact PRES4|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP5| lia| intros b Hb; exact Hb]. }
    clear AG5 HP5 HEAP4 AUX4 PRES4 SJS4 PL4 TPC4 HEAP3 AUX3 PRES3 SJS3 PL3.

    pose proof (rw_cells_forget_C8 usegs m5 (sp0 + 392) [] _ _ SV5) as J0'. cbn [app] in J0'.
    pose proof (rw_cells_forget_C8 usegs m5 (sp0 + 392) [CB 8 (le8 (Z_to_bv 64 A))] _ _ J0') as J0''. cbn [app] in J0''.
    pose proof (rw_cells_forget_C8 usegs m5 (sp0 + 392) [CB 8 (le8 (Z_to_bv 64 A)); CB 8 (le8 (Z_to_bv 64 A))] _ _ J0'') as SVJ. cbn [app] in SVJ. clear J0' J0'' SV5.
    pose proof (rw_cells_join _ _ _ _ _ LOW SVJ ltac:(cbn [cells_size csize Nat.add]; lia)) as J1.
    pose proof (rw_cells_join _ _ _ _ _ J1 MID ltac:(cbn [app cells_size csize Nat.add]; lia)) as J2.
    pose proof (rw_cells_join _ _ _ _ _ J2 SAVE ltac:(cbn [app cells_size csize Nat.add]; lia)) as FR. cbn [app] in FR.
    clear J1 J2 LOW SVJ MID SAVE.
    pose proof (munch_refl [(sp0, sp0 + 528)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    apply implM_ret.

    step. do 10 step. step. release_frame FR ST5 (sp0 + 528). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB (sp0 + 528) [LXW_SJ; LXW_UNW; LXW_TP] a -> outside [(sp0, sp0 + 528)] a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    assert (PRESF : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW; LXW_TP] m0 mF).
    { eapply lx_pres_trans; [exact PRES5|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    pose proof (agree_of_lx_pres _ _ _ _ _ PRESF) as AGF.
    assert (TPCF : rw_cells usegs mF EL_TPLOC [C8 (Z_to_bv 64 EL_GLOC)])
      by (eapply rw_cells_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact TPC5|]; intros a Ha; cbn in Ha; cbn [outside]; lia).
    rewrite Esp0. replace (usp - 528 + 528) with usp by lia. rewrite <- ESP. rewrite Esp0 in PRESF. replace (usp - 528 + 528) with usp in PRESF by lia.
    assert (SJSF : sj_statics mF init).
    { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS5]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1.
      cbn [outside]. split; [lia| exact I]. }
    apply evt_done. unfold rfuzz_one_post, lx_post_env, lx_env. cbn [app]. rewrite <- Eusp. do 15 eexists. exists F, fc, mF.
    split; [cbv delta [mkR]; reflexivity|].
    split.
    { split; [| split; [exact FRM| split; [exact PRESF| split; congruence]]].
      exists errv.
      split. { eapply LH_frame; [exact HEAP5| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      split. { eapply lx_statics_pres_tp; [exact PRESF| exact TPCF| exact LXS0]. }
      split. { exists init. exact SJSF. }
      split. { eapply stderr_wfile_agree; [exact AGF| | exact SEW0]. intros a Ha. apply stderr_addr_client; [exact Ha|].
               unfold stderr_addr in Ha. unfold LXW_SJ, LXW_UNW, LXW_TP, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
      split. { pose proof (ssp_canary_0 _ _ _ _ HEAP00 SSP0) as EC. rewrite EC. eapply RHEAP_ssp.
               eapply LH_frame; [exact HEAP5| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      split. { eapply rauxv_ok_frame; [exact AUX5| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      split; [lia|]. split; [(clear - B63; lia)|]. split; [rewrite Esp0 in ST5; replace (usp - 528 + 528) with usp in ST5 by lia; exact ST5|]. split; [exact CEIL'|]. split; [unfold GLOBALS_TOP; lia|].
      split. { unfold errno_addr, RATP. rewrite unsigned_lit by lia. rewrite ELX in ERR5. exact ERR5. }
      split; [reflexivity| assumption]. }
    split. { exists init. exact SJSF. }
    split; [reflexivity|]. split; [reflexivity|].
    eapply payload_ok_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact PL5|]. intros b a Hb Ha.
    pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I].
  Qed.

  Lemma exit_cps : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (x1 t0 t1 t2 y8 y9 y10 a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 t3 t4 t5 t6 : word)
      (m0 m : mem) (s00 st : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary errv : word) (init : bool)
      (bv : bptr) (A cap : Z) (P : nat) (psb ptp pim pix poc pia : bptr) (IMPL IDX OC IA TAPE SBUF nix ntp nsb : Z) (capw : word)
      (nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 j313 j329 j361 jlo jmid : list byte),
    RHEAP s00 LB m0 -> lx_statics m0 -> stderr_wfile m0 -> ssp_cells m0 canary ->
    bv_unsigned sp <= B -> B < 2^62 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK -> bv_unsigned sp mod 16 = 0 ->
    RHEAP st ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: (ptp, TAPE, ntp) :: (psb, SBUF, nsb) :: (bv, A, 16 * cap) :: LB) m ->
    rauxv_ok m B -> mem_inv usegs m -> stk usegs m lo (bv_unsigned sp - 528) -> rw_cells usegs m LX_ERRNO [C4 errv] ->
    ps_fa st = ps_fa s00 -> ps_so st = ps_so s00 -> frm0 fc ->
    lx_pres LB (bv_unsigned sp) [LXW_SJ; LXW_UNW; LXW_TP] m0 m -> rw_cells usegs m EL_TPLOC [C8 (wz EL_GLOC)] -> sj_statics m init -> payload_ok m LB D d -> 0 < A ->
    rw_cells usegs m (bv_unsigned sp - 528) [CB 312 jlo] ->
    rw_cells usegs m (bv_unsigned sp - 528 + 312) [C1 (Z_to_bv 8 0); CB 7 j313] ->
    rw_cells usegs m (bv_unsigned sp - 528 + 320) [C8 (Z_to_bv 64 IMPL)] ->
    rw_cells usegs m (bv_unsigned sp - 528 + 328) [C1 (Z_to_bv 8 0); CB 3 j329; C4 (Z_to_bv 64 12)] ->
    rw_cells usegs m (bv_unsigned sp - 528 + 336) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 capw] ->
    rw_cells usegs m (bv_unsigned sp - 528 + 360) (p48_cells (Z_to_bv 8 0) j361 (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
    rw_cells usegs m IMPL (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) ->
    rw_cells usegs m (bv_unsigned sp - 528 + 392) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * Z.of_nat P)); C8 (Z_to_bv 64 (A + 16 * cap))] ->
    Z.of_nat P <= cap ->
    rw_cells usegs m (bv_unsigned sp - 528 + 416) [CB 32 jmid] ->
    rw_cells usegs m (bv_unsigned sp - 528 + 448) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    implM usegs (mbind (del lops psb) (fun _ => mbind (del lops ptp) (fun _ => mbind (del lops pia) (fun _ => mbind (del lops poc) (fun _ =>
                 mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ => mbind (vfree lops (cap, Z.of_nat P, Some bv)) (fun _ => mret 0)))))))) st
          (rfuzz_one_post ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s00 LB D d lo B canary m0)
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 528)) gp (Z_to_bv 64 RATP) t0 t1 t2 y8 y9 y10 a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 EL_EXIT) fc None m (seg_rom usegs)).
  Proof.
    intros until jmid. intros HEAP00 LXS0 SEW0 SSP0 SPB B63 CEIL GLO LO AL16 HEAP2 AUX2 MI2 ST2 ERR2 FA2 SO2 FRM PRES2 TPC2 SJS2 PL2 A0 LOW PA0 PIMPL PA16 DOCC P48 THIS SV PCAP MID SAVE.
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP, EL_EXIT in *. unfold MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    remember (bv_unsigned sp) as usp eqn:Eusp.
    remember (usp - 528) as sp0 eqn:Esp0.
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (LO0 : 0 <= lo) by (destruct ST2 as [? _]; assumption).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR2.
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(do 6 right; left; reflexivity)) as (_ & _ & CAP0 & AC & AS).
    cbn [blk_addr blk_size fst snd] in CAP0, AC, AS. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in AC.
    assert (LXS2 : lx_statics m) by (eapply lx_statics_pres_tp; [exact PRES2| exact TPC2| exact LXS0]).
    pose proof LXS2 as (_ & _ & _ & _ & VTD2 & _ & _). unfold MallocRep.wz in VTD2.
    readdr PIMPL (sp0 + 312 + 8). readdr DOCC (sp0 + 312 + 24). readdr P48 (sp0 + 312 + 48).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.

    step. step.
    ihere. to_implM.
    eapply (pdtor_cps HF) with (B := B) (lo := lo) (ocp := None) (PARSER := sp0 + 312) (IMPL := IMPL) (IDX := IDX) (OC := OC) (IA := IA) (TAPE := TAPE) (SBUF := SBUF)
                                (psb := psb) (ptp := ptp) (pim := pim) (pix := pix) (poc := poc) (pia := pia);
      [exact HEAP2| exact AUX2| lia| exact ST2| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RFREE_STACK; lia| rewrite ELX; exact ERR2| exact MI2| lia| lia| lia
      | exact VTD2| exact PIMPL| exact DOCC| exact P48| exact THIS|].
    intros st3 ms3 PO. unfold hpost in PO.
    destruct PO as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m3
                    & -> & MI3 & ST3 & (errv3 & ERR3) & AUX3 & FA3 & SO3 & RR).
    unfold pdtor_R in RR. destruct RR as (HEAP3 & PRES23 & PIMPL3 & DOCC3 & P483). unfold p48_cells in P483.
    replace (ret_pc (Z_to_bv 64 0x3bdec)) with (Z_to_bv 64 0x3bdec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ELX in ERR3.

    pose proof (agree_of_lx_pres _ _ _ _ _ PRES23) as AG23.
    assert (FRCL : forall a, sp0 <= a < sp0 + 528 -> ~ (sp0 + 320 <= a < sp0 + 328) -> ~ (sp0 + 336 <= a < sp0 + 352) -> ~ (sp0 + 376 <= a < sp0 + 384) ->
              lx_client ((bv, A, 16 * cap) :: LB) sp0 (pdtor_X (sp0 + 312)) a).
    { intros a Ha N1 N2 N3. split; [| left; lia]. unfold pdtor_X. cbn [rin_ivs fst snd]. clear - Ha N1 N2 N3. lia. }
    apply (rw_cells_agree _ _ _ _ _ AG23) in SV; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG23) in LOW; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG23) in PA0; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG23) in PA16; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG23) in MID; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG23) in SAVE; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    assert (TPC3 : rw_cells usegs m3 EL_TPLOC [C8 (Z_to_bv 64 EL_GLOC)]).
    { eapply rw_cells_agree; [exact AG23| exact TPC2|]. intros a Ha. cbn in Ha. split; [unfold pdtor_X; cbn [rin_ivs fst snd]; clear - Ha GLO LO Esp0; lia| right; right].
      split; [clear - Ha; lia|]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. clear - Ha. lia. }
    assert (PL3 : payload_ok m3 LB D d).
    { eapply payload_ok_agree; [exact AG23| exact PL2|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. split; [unfold pdtor_X; cbn [rin_ivs fst snd]; clear - Ha BC CEIL LO Esp0; lia| right; left; exists b; split; [right; exact Hb| exact Ha]]. }
    assert (SJS3 : sj_statics m3 init).
    { eapply sj_statics_agree; [exact AG23| | exact SJS2]. intros a Ha. apply sjs_addr_client; [exact Ha|]. pose proof (sjs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1.
      unfold pdtor_X. cbn [rin_ivs fst snd]. clear - R1 GLO LO Esp0. lia. }
    assert (PRES3 : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW; LXW_TP] m0 m3).
    { rewrite Esp0. replace (usp - 528 + 528) with usp by lia. eapply lx_pres_trans; [exact PRES2|]. eapply (lx_pres_sub LB usp _ _ _ _ _ _ PRES23); [lia| intros b0 Hb0; right; exact Hb0|].
      intros a Ha NX. unfold pdtor_X in Ha. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; specialize (BLB a IB); lia| lia]. }
    clear AG23 PRES23 HEAP2 AUX2 PRES2 SJS2 PL2 TPC2 MU WM FRCL.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.

    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

    readdr PIMPL3 (sp0 + 320). readdr DOCC3 (sp0 + 336). readdr P483 (sp0 + 360).
    pose proof (rw_cells_join _ _ _ _ _ LOW PA0 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1.
    pose proof (rw_cells_join _ _ _ _ _ J1 PIMPL3 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J2.
    pose proof (rw_cells_join _ _ _ _ _ J2 PA16 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J3.
    pose proof (rw_cells_join _ _ _ _ _ J3 DOCC3 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J4.
    pose proof (rw_cells_join _ _ _ _ _ J4 P483 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J5. cbn [app] in J5.
    destruct (rw_cells_forget _ _ _ _ J5) as [jlow LOW']. cbn [cells_size csize Nat.add] in LOW'.
    clear J1 J2 J3 J4 J5 LOW PA0 PIMPL3 PA16 DOCC3 P483 MU WM.
    subst sp0 usp.
    eapply vexit_cps; try eassumption; [congruence| congruence| replace (bv_unsigned sp) with (bv_unsigned sp - 528 + 528) by lia; exact PRES3].
  Qed.
End Proofs.
End WithCeiling0.
