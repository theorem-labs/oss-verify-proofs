(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Drv_facts.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnMem BnTac.
From OSSVerify.Proofs.openssl.bndiv.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep BnIface BnUAlign BnUKit W_crypto W_ctx.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_CTX_END : Z := 0x115380.
Definition BN_CTX_END_STACK : Z := 16.

(* [comment removed for export] *)
Lemma end_loop : forall (k : nat) (POST : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (off j : Z),
  Z.of_nat k < j -> Z.of_nat k <= off -> off <= 15 -> j <= 16 ->
  evt usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (- (j - Z.of_nat k))) (Z_to_bv 64 (off - Z.of_nat k)) a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x115414) fc None m (seg_rom usegs)) ->
  evt usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (- j)) (Z_to_bv 64 off) a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x115414) fc None m (seg_rom usegs)).
Proof.
  induction k as [|k IH]; intros until j; intros HJ HO HO15 HJ16 K.
  - change (Z.of_nat 0) with 0 in K. rewrite !Z.sub_0_r in K. exact K.
  - rewrite Nat2Z.inj_succ in *.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. step. step.
    rewrite (swrap32_wrap64 (- j) 1) by lia. rewrite (swrap32_wrap64 off (-1)) by lia.
    step. if_cases K1; zify_cond K1.
    + eapply evt_eq; [| eapply (IH POST ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (off + -1) (j - 1));
                        [lia| lia| lia| lia|] ].
      * replace (- j + 1) with (- (j - 1)) by lia. reflexivity.
      * replace (j - 1 - Z.of_nat k) with (j - Z.succ (Z.of_nat k)) by lia.
        replace (off + -1 - Z.of_nat k) with (off - Z.succ (Z.of_nat k)) by lia. exact K.
    + exfalso. change 18446744073709551615 with (Z.ones 64) in K1. rewrite Z.land_ones in K1 by lia.
      clear - K1 HJ HJ16. change (2 ^ 64) with 18446744073709551616 in K1. Z.div_mod_to_equations. lia.
Qed.

  Lemma BN_CTX_end_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_CTX_END_STACK -> tp = wz RATP -> a0 = wz (ad_ctx AD) ->
    implM usegs (interp (embed (BN_CTX_end (tree_ops bptr) ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (fun _ _ OW' _ => OW' = OW))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_END) fc None m (seg_rom usegs)).
  Proof.
    intros until errv. intros (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI) -> ->.
    unfold BN_CTX_END_STACK, BN_CTX_END, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    pose proof SOK as (_ & _ & _ & _ & _ & POK & (CK1 & CK2 & CK3 & CK4 & CK5 & CK6 & CK7)).
    destruct (lib_state_cx_open [] ls m OW AD EA LS) as (H & Cu & IX & CX & STK & PM & HH & LSC).
    pose proof ADB as (_ & _ & _ & _ & _ & BC). pose proof (RH_range _ _ _ _ _ _ _ HEAP BC) as (CA0 & CA16 & _ & CAC & CAI).
    set (c := ls_ctx ls) in *.
    unfold ctx_cells in CX. rewrite CK7 in CX. change (Z.of_nat 0) with 0 in CX.
    unfold LX_ERRNO, RATP in ERR. change (3353240 - 164) with 3353076 in ERR.
    unfold BN_CTX_end, bbind, bgetctx, bret, bunr, bsetctx.
    cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd]. fold c.
    rewrite CK7. cbn [Nat.eqb negb].
    destruct (rev (cx_frames c)) as [|fp rest] eqn:EREV.
    { cbn [embed interp]. apply implM_interp_unr. }
    unfold implM. iprefix.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (CA8 : ad_ctx AD mod 8 = 0) by (clear - CA16; Z.div_mod_to_equations; lia).
    carve_frame 16%nat ST. do 4 step.
    step. if_cases KN; zify_cond KN; [exfalso; rewrite ?unsigned_lit in KN by lia; lia|]. clear KN.
    step. rewrite (land7_wrap _ CA8).
    chk ltac:(fun C => clear - C; lia).
    step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
    step. if_true.
    assert (EFR : cx_frames c = rev rest ++ [fp]).
    { rewrite <- (rev_involutive (cx_frames c)), EREV. reflexivity. }
    assert (DEPp : length (cx_frames c) = S (length rest)) by (rewrite EFR, length_app, length_rev; cbn; lia).
    assert (SSZ : cx_ssize c = 0%nat \/ cx_ssize c = 32%nat).
    { unfold stack_rep in STK. destruct (cx_indexes c); [right; exact (proj1 (proj2 STK))| left; exact (proj1 (proj2 STK))]. }
    assert (FPU : (fp <= cx_used c)%nat).
    { rewrite EFR in CK4. rewrite <- app_assoc in CK4. cbn [app] in CK4. eapply nondecr_last_le; exact CK4. }
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (length (cx_frames c)))) by lia.
    step.
    step. replace (Z.of_nat (length (cx_frames c)) + -1) with (Z.of_nat (length rest)) by lia.
    do 3 step.
    rewrite (unsigned_lit (Z.of_nat (length rest))) by lia. rewrite shl32_shr30 by lia.
    step.
    (* [comment removed for export] *)
    unfold stack_rep in STK. destruct (cx_indexes c) as [q|] eqn:EI; [|exfalso; destruct STK as (_ & _ & E2); rewrite E2 in DEPp; cbn in DEPp; lia].
    destruct STK as (HinI & SZ32 & stale & LEN & ARR).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP HinI) as (IA0 & IA16 & _ & IAC & IAI).
    assert (NEI : ad_pc AD <> q) by (eapply ids_ad_m; [exact IDS| unfold ad_ids; cbn; tauto| apply idx_in_m; exact EI]).
    pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HinI NEI) as CXI.
    remember (map (fun k : nat => wz (Z.of_nat k)) (cx_frames c) ++ stale) as ws eqn:Ews.
    assert (LWS : length ws = 32%nat) by (subst ws; rewrite length_app, length_map; exact LEN).
    assert (NTH : nth_error ws (Z.to_nat (Z.of_nat (length rest))) = Some (wz (Z.of_nat fp))).
    { rewrite Nat2Z.id, Ews, EFR, map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
      rewrite nth_error_app2 by (rewrite length_map, length_rev; lia). rewrite length_map, length_rev, Nat.sub_diag. reflexivity. }
    chkw ltac:(fun C => clear - C IA0 IAC DEPp LEN; lia).
    step. rewrite (snez_pos_wz IX) by (clear - IA0 IAC; lia).
    step. rewrite (seqz_pos (IX + 4 * Z.of_nat (length rest))) by (clear - IA0 IAC DEPp LEN; lia).
    step.
    chk ltac:(fun C => clear - C; lia).
    chkw ltac:(fun C => clear - C IA0 IAC; lia).
    step. rewrite (land3_wrap (IX + 4 * Z.of_nat (length rest))) by (clear - IA16; Z.div_mod_to_equations; lia).
    chk ltac:(fun C => clear - C; lia).
    pose proof ARR as ARR0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of MU with munch ?W0 _ _ =>
        apply (u32arr_transport usegs W0 m mx IX ws) in ARR; [| exact MU| exact WM| cbn [disjoint_from]; rewrite LWS; lia] end end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let a := cur_mem_addr in
      pose proof (u32arr_read usegs mx IX ws (Z.of_nat (length rest)) (wz (Z.of_nat fp)) a ARR NTH ltac:(lia) ltac:(addr_tac)) as RD end.
    step. clear RD. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat fp)) by lia.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (cx_used c))) by lia.
    set (pu' := if (fp <? cx_used c)%nat then (cx_pused c - (cx_used c - fp))%nat else cx_pused c).
    set (cur' := if (fp <? cx_used c)%nat && (pu' =? 0)%nat then None else cx_current c).
    lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mx _) => rename mx into m1;
      assert (FIN : forall (x12 x13 x14 : word) (mX : mem) (CuX : Z),
        rw_cells usegs mX (ad_ctx AD)
          [C8 (wz H); C8 (wz CuX); C8 (wz H); C4 (wz (Z.of_nat pu')); C4 (wz (Z.of_nat (cx_psize c))); C8 (wz IX);
           C4 (wz (Z.of_nat (length rest))); C4 (wz (Z.of_nat (cx_ssize c))); C4 (wz (Z.of_nat (cx_used c)));
           C4 (wz 0); C4 (wz (Z.b2z (cx_too_many c))); C4 (wz 0); C8 (wz 0)] ->
        rw_cells usegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
        stk usegs mX lo (bv_unsigned sp + -16) ->
        munch [(bv_unsigned sp + -16, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]%Z m mX -> wmono usegs m mX -> mem_inv usegs mX ->
        rw_cells usegs mX 3353076 [C4 errv] ->
        ((cur' = None /\ CuX = 0) \/ (cur' = cx_head c /\ cur' <> None /\ CuX = H)) ->
        evt usegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RATP) t0 t1 t2 sp s1 (Z_to_bv 64 (ad_ctx AD))
                             (Z_to_bv 64 (Z.of_nat fp)) x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 1135684) fc None mX (seg_rom usegs))) end.
    { intros x12 x13 x14 mX CuX CXX FRX STX MUX WMX MIX ERRX HCUR.
      clear MU WM MI ERR ST FR CX ARR.
      unfold MallocRep.wz in *.
      step. step. step. step. step. release_frame FRX STX (bv_unsigned sp). step.
      ihere. to_implM. cbn [embed interp]. apply implM_ret. apply evt_done.
      lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      lazymatch goal with |- context [set_ctx ?cc ls] => set (c' := cc) end.
      assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -16, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]).
      { constructor; [left; cbn; lia|]. constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith| constructor]. }
      assert (EPU : pu' = fp).
      { subst pu'. destruct (fp <? cx_used c)%nat eqn:EL; [lia|]. apply Nat.ltb_ge in EL. lia. }
      assert (LSF : lib_state (set_ctx c' ls) mF OW AD EA).
      { unfold lib_state. eapply (lib_state_cx_close [] ls mF OW AD EA c' H CuX IX); [| exact ND| reflexivity| reflexivity| exact HH| | | | |].
        - eapply (lib_state_frame s LB); [exact HEAP| exact LSC| exact MUX| exact WMX|].
          constructor; [apply w_stack; cbn; lia|].
          constructor; [apply w_cx; [reflexivity| intros x Hx; left; cbn in Hx; lia]| constructor].
        - unfold ctx_cells, c'. cbn [cx_pused cx_psize cx_frames cx_ssize cx_used cx_err_stack cx_too_many Z.b2z].
          rewrite length_rev. fold pu'. rewrite EPU in *. exact CXX.
        - unfold stack_rep, c'. cbn [cx_indexes cx_ssize cx_frames]. split; [exact HinI|]. split; [exact SZ32|].
          exists (wz (Z.of_nat fp) :: stale). split; [rewrite length_rev; cbn [length]; rewrite DEPp in LEN; lia|].
          lazymatch type of MUX with munch ?W0 _ _ =>
            apply (u32arr_transport usegs W0 m mF IX ws) in ARR0; [| exact MUX| exact WMX| cbn [disjoint_from]; rewrite LWS; lia] end.
          rewrite Ews, EFR, map_app in ARR0. cbn [map] in ARR0. rewrite <- app_assoc in ARR0. cbn [app] in ARR0. exact ARR0.
        - assert (PMF : pool_mem mF H Cu c).
          { eapply (pool_mem_keep s OW LB m mF ls AD EA H Cu); [exact HEAP| exact IDS| exact ADB| exact HH| exact PM| exact MUX| exact WMX|].
            constructor; [left; cbn; lia|]. constructor; [right; left; cbn; lia| constructor]. }
          unfold pool_mem in *. subst c'. cbn [cx_head cx_current]. fold pu'. fold cur'.
          destruct (cx_head c) as [ph|] eqn:Eh.
          + split; [exact (proj1 PMF)|]. destruct HCUR as [[E1 E2]|(E1 & E2 & E3)]; [left; auto| right; auto].
          + destruct HCUR as [[E1 E2]|(E1 & E2 & E3)]; [auto| congruence].
        - unfold ctx_okm, c'. cbn [cx_pused cx_used cx_psize cx_vals cx_frames cx_ssize cx_current cx_head cx_err_stack]. fold pu'. fold cur'.
          split; [exact EPU|]. split; [lia|]. split; [exact CK3|].
          split. { rewrite EFR in CK4. rewrite <- app_assoc in CK4. cbn [app] in CK4. eapply nondecr_drop_last; exact CK4. }
          split; [rewrite length_rev; lia|]. split; [|reflexivity].
          intros HP. subst cur'. replace (pu' =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact HP). rewrite andb_false_r.
          apply CK6. lia.
        - apply ids_ok_set_ctx_same; [exact IDS| reflexivity| symmetry; exact EI| reflexivity]. }
      unfold bn_post. do 15 eexists. exists mF, OW, errv. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MUX WMX HWL CEIL)|]. split; [exact LSF|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MUX WMX HWL SPB); unfold GLOBALS_TOP; lia|]. split; [exact STX|].
      split; [unfold LX_ERRNO, RATP; exact ERRX|]. split; [exact MIX|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MUX WMX HWL CEIL); unfold GLOBALS_TOP; lia|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [intros r' a' HA'; exact HA'| reflexivity]. }
    assert (HCUR0 : (cx_current c = None /\ Cu = 0) \/ (cx_current c = cx_head c /\ cx_current c <> None /\ Cu = H)).
    { unfold pool_mem in PM. destruct (cx_head c) as [ph|] eqn:Eh.
      - destruct PM as [_ [[E1 E2]|[E1 E2]]]; [left; auto| right; rewrite E1; repeat split; [discriminate| exact E2]].
      - destruct PM as [E1 E2]. left. auto. }
    step. if_cases KR; zify_cond KR; rewrite ?unsigned_lit in KR by lia.
    - (* [comment removed for export] *)
      assert (ELT : (fp <? cx_used c)%nat = false) by (apply Nat.ltb_ge; lia).
      eapply FIN; [| exact FR| exact ST| exact MU| exact WM| exact MI| exact ERR|].
      + subst pu'. rewrite ELT. exact CX.
      + subst cur'. rewrite ELT. cbn [andb]. exact HCUR0.
    - (* [comment removed for export] *)
      assert (ELT : (fp <? cx_used c)%nat = true) by (apply Nat.ltb_lt; lia).
      step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (cx_pused c))) by lia.
      step. step. step.
      rewrite !(unsigned_lit (Z.of_nat fp)), !(unsigned_lit (Z.of_nat (cx_used c))) by lia.
      rewrite !(bk_swrap32_small (Z.of_nat fp - Z.of_nat (cx_used c))) by lia.
      replace (Z.of_nat (cx_pused c) + (Z.of_nat fp - Z.of_nat (cx_used c))) with (Z.of_nat pu') by (subst pu'; rewrite ELT; lia).
      step. step.
      rewrite (unsigned_lit (Z.of_nat (cx_pused c) + -1)) by lia.
      replace (Z.land (Z.of_nat (cx_pused c) + -1) 15) with (Z.of_nat (cx_pused c) + -1)
        by (change 15 with (Z.ones 4); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
      replace (Z.of_nat fp - Z.of_nat (cx_used c)) with (- (Z.of_nat (cx_used c) - Z.of_nat fp)) by lia.
      eapply evt_eq; [| eapply (end_loop (cx_used c - fp - 1)) with (off := Z.of_nat (cx_pused c) + -1) (j := Z.of_nat (cx_used c) - Z.of_nat fp);
                        [lia| lia| lia| lia|] ]; [reflexivity|].
      replace (Z.of_nat (cx_used c) - Z.of_nat fp - Z.of_nat (cx_used c - fp - 1)) with 1 by lia.
      replace (Z.of_nat (cx_pused c) + -1 - Z.of_nat (cx_used c - fp - 1)) with (Z.of_nat pu') by (subst pu'; rewrite ELT; lia).
      assert (PUR : (pu' <= 16)%nat) by (subst pu'; rewrite ELT; lia).
      step. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia.
      + (* [comment removed for export] *)
        assert (EP0 : pu' = 0%nat) by lia.
        assert (PNZ : cx_pused c <> 0%nat) by lia.
        pose proof (CK6 PNZ) as ECUR.
        destruct HCUR0 as [[E1 E2]|(E1 & E2 & E3)].
        { (* [comment removed for export] *)
          exfalso. rewrite ECUR in E1. destruct POK as [EV|[EV _]]; [rewrite EV in CK3; cbn in CK3; lia|].
          clear - LSC E1 EV. destruct LSC as (_ & _ & _ & (_ & _ & (_ & _ & _ & _ & _ & _ & _ & (H' & Cu' & I' & _ & HPool & _)))).
          fold c in HPool. rewrite E1 in HPool. destruct HPool as [_ EV0]. rewrite EV0 in EV. discriminate. }
        subst Cu.
        destruct (cx_head c) as [ph|] eqn:Eh; [|congruence].
        unfold pool_mem in PM. rewrite Eh in PM. destruct PM as [PN _].
        pose proof (RH_range _ _ _ _ _ _ _ HEAP HH) as (HA0 & HA16 & _ & HAC & HAI).
        assert (NEH : ad_pc AD <> ph) by (eapply ids_ad_m; [exact IDS| unfold ad_ids; cbn; tauto| apply head_in_m; exact Eh]).
        pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HH NEH) as CXH.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          lazymatch type of MU with munch ?W0 _ _ =>
            apply (rw_cells_transport usegs W0 m mx (H + 384)) in PN; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end end.
        unfold MallocRep.wz in CX.
        assert (HA8 : H mod 8 = 0) by (clear - HA16; Z.div_mod_to_equations; lia).
        step.
        chk ltac:(fun C => clear - C HA0 HAC; lia).
        step. rewrite (land7_wrap _ HA8).
        chk ltac:(fun C => clear - C; lia).
        step. step. step. step.
        rewrite (swrap32_wrap64 (- (1)) 1) by lia. change (- (1) + 1) with 0.
        step. if_false.
        eapply FIN; [| exact FR| exact ST| exact MU| exact WM| exact MI| exact ERR|].
        * exact CX.
        * left. subst cur'. rewrite ELT. replace (pu' =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; exact EP0). cbn. auto.
      + (* [comment removed for export] *)
        step. step. step.
        rewrite (swrap32_wrap64 (- (1)) 1) by lia. change (- (1) + 1) with 0.
        step. if_false.
        eapply FIN; [| exact FR| exact ST| exact MU| exact WM| exact MI| exact ERR|].
        * exact CX.
        * subst cur'. replace (pu' =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia). rewrite andb_false_r. exact HCUR0.
  Qed.
End WithCeiling0.
