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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgWords BgArith BgMont BgExp.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_expandAF W_callsAF AFrameKit ExpKitAF W_small3A W_calls3AF AFrameEnv ExpStmtF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_MOD_EXP : Z := 0x2ae9cc.
Definition BN_MOD_EXP_RECP : Z := 0x2afa78.
Definition BN_MOD_EXP_MONT : Z := 0x2af070.
Definition BN_MOD_EXP_MONT_WORD : Z := 0x2aeb98.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Proofs.

  Variables (EXP_STACK EXP_COST : Z) (EXP_DEPTH : nat).
  Hypothesis EXP_STACK16 : 16 <= EXP_STACK.
  Definition BN_MOD_EXP_STACK : Z := 64 + EXP_STACK.

  Hypothesis BN_mod_exp_recp_walkA : exp_stmtAn_f BN_MOD_EXP_RECP EXP_STACK EXP_COST EXP_DEPTH (BN_mod_exp_recp (tree_ops bptr)) None.
  Hypothesis BN_mod_exp_mont_walkA : exp_stmtAn_f BN_MOD_EXP_MONT EXP_STACK EXP_COST EXP_DEPTH (BN_mod_exp_mont (tree_ops bptr)) (Some (wz 0)).

  Hypothesis BN_mod_exp_mont_word_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rp rm : bnref) (A : Z) (arr arp arm ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo EXP_STACK EXP_COST ->
    fr_room EXP_DEPTH ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MOD_EXP_MONT_WORD (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr arr -> ref_at ls OW PL rp arp -> ref_at ls OW PL rm arm ->
    hpl PL rr -> rp <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) -> pl_fresh PL -> 0 <= A < BW ->
    a0 = wz arr -> a1 = wz A -> a2 = wz arp -> a3 = wz arm -> a4 = wz ac -> a5 = wz 0 ->
    implA (BN_mod_exp_mont_word (tree_ops bptr) rr A rp rm ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA EXP_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_EXP_MONT_WORD) fc None m (seg_rom bgasegs)).

  Ltac strip2 l := lazymatch l with
    | cons _ (cons _ nil) => constr:(@nil cell)
    | cons ?x ?t => let r := strip2 t in constr:(cons x r)
    end.

  Lemma BN_mod_exp_walkA : exp_stmtAn_f BN_MOD_EXP BN_MOD_EXP_STACK EXP_COST EXP_DEPTH (BN_mod_exp (tree_ops bptr)) None.
  Proof.
    unfold exp_stmtAn_f. intros until qc. intros PRE ROOM UW CTX -> HAr HAa HAp HAm HPr NROa NROp NROm NBa HPC HFR -> -> -> -> -> _.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold BN_MOD_EXP_STACK in LO'.
    unfold BN_MOD_EXP, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.

    set (ba := getbn ra_ ls). set (bp := getbn rp ls). set (bm := getbn rm ls).
    pose proof (st_wf_ok _ _ (proj1 PARTS) (ref_at_valid _ _ _ _ _ _ _ _ LS HAa) NROa) as (OKa1 & OKa2 & OKa3 & OKa4). fold ba in OKa1, OKa2, OKa3, OKa4.
    pose proof (st_wf_ok _ _ (proj1 PARTS) (ref_at_valid _ _ _ _ _ _ _ _ LS HAp) NROp) as (_ & _ & _ & OKp4). fold bp in OKp4.
    pose proof (st_wf_ok _ _ (proj1 PARTS) (ref_at_valid _ _ _ _ _ _ _ _ LS HAm) NROm) as (_ & _ & _ & OKm4). fold bm in OKm4.
    unfold BG_DMAX in OKa3.
    assert (CTa : Z.land (bn_flags ba) 4 = 0) by (destruct OKa4 as [E|E]; rewrite E; reflexivity).
    assert (CTp : Z.land (bn_flags bp) 4 = 0) by (destruct OKp4 as [E|E]; rewrite E; reflexivity).
    assert (CTm : Z.land (bn_flags bm) 4 = 0) by (destruct OKm4 as [E|E]; rewrite E; reflexivity).
    clear OKa4 OKp4 OKm4.

    unfold BN_mod_exp, any_consttime, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd fold_right]. cbv beta.
    fold ba bp bm.
    apply implA_from_evt.

    carve_frame 64%nat ST. do 10 step. do 4 step. do 3 step. do 2 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mP OW PL EA _ HEAP LS MU WM FROK WOK) as LS0.
    lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
      assert (EV0 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) EXP_COST Σ ls OW m p 0 Σ ls mP OW) end.
    { unfold cenvA, cenv_ok.
      split; [split; [exact CEIL|]; split; [lia|]; split; [lia|]; split; [unfold USTACK_TOP; lia|]; split; [exact SP16|];
              split; [clear - SP16; Z.div_mod_to_equations; lia|]; split; [exact CNT|]; split; [exact CRED|]; split; [exact FROK|]; split; [exact FAL| exact NOFR]|].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
      split; [exact ST|]. split; [exact MI|].
      split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))|].
      split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
      split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
      eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
    pose proof EV0 as (OK & _).
    pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & FROKK & _ & _).
    clear HEAP LS ST MI MU WM HWL WOK FR PRE PARTS.
    assert (LOFB16 : lo <= bv_unsigned sp + -64 - 16) by (clear - LO' EXP_STACK16; lia).

    eapply (is_odd_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) EXP_COST Σ ls OW m LOFB16); [exact EV0 | exact LS0 | exact HAm | exact NROm |].
    intros mA y0A y1A y2A y4A y5A y6A y7A y8A y9A y10A y11A y12A y13A y14A EVA LSA.
    rewrite (ret_pc_even 2812444) by (clear; lia).
    fold bm.
    destruct (is_odd_pure bm) eqn:Eodd; cbn [Z.b2z].
    2:{
      step. if_true. do 5 step.
      pose proof EVA as (_ & _ & STT & _ & _ & _ & _ & _ & FRT & _ & _). cbn [app] in FRT.
      do 8 step. release_frame FRT STT (bv_unsigned sp). step. step.
      apply evt_done.
      destruct (cenv_tailA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) EXP_COST Σ ls OW m _ _ _ _ _ _ EXP_STACK EXP_COST ras
                  ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = wz 1)
                  EVA LSA STT ltac:(clear - LO'; lia) ltac:(clear; lia) eq_refl) as (PREX & UWX & POSTX).
      rewrite Z_to_bv_bv_unsigned in PREX, POSTX.
      eapply implA_mono.
      { eapply (BN_mod_exp_recp_walkA ra sp) with (lo := lo) (ras := ras) (rr := rr) (ra_ := ra_) (rp := rp) (rm := rm) (arr := arr) (ara := ara) (arp := arp) (arm := arm) (ac := ac) (qc := qc) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
          [exact PREX | exact ROOM | exact UWX | exact (uk_ctx_tail _ _ _ E_BN_mod_exp_2ae920 CTX) | reflexivity | exact HAr | exact HAa | exact HAp | exact HAm | exact HPr | exact NROa | exact NROp | exact NROm | exact NBa | exact HPC | exact HFR | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | intros w Hw; discriminate Hw]. }
      cbv beta. intros r Σ' ms' PO. apply POSTX. exact PO.
    }

    step. if_false.
    pose proof (proj1 (proj2 EVA)) as HEAPA.
    destruct (open_for_call LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) EXP_COST Σ ls OW m LOFB16 _ _ _ _ _ _ _ _ EVA LSA HAa NROa)
      as (Da & BNa & _ & _ & _ & _ & SEPa & _ & ACCa & ALa & _ & _ & Aa0).
    fold ba in BNa. unfold BnRepDefs.bn_cells in BNa.
    pose proof (munch_refl (@nil (Z * Z)) mA) as MUA.
    do 3 step. shl_with ACCa ALa. chk0.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top ba))) by (clear - OKa2 OKa3; unfold bn_dmax in *; lia).
    step.
    step. if_cases KT; zify_cond KT; rewrite ?unsigned_lit in KT by (clear - OKa2 OKa3; unfold bn_dmax in *; lia).
    {
      replace ((bn_top ba =? 1)%nat) with false by (symmetry; apply Nat.eqb_neq; clear - KT; lia). cbn [andb].
      do 6 step.
      pose proof EVA as (_ & _ & STT & _ & _ & _ & _ & _ & FRT & _ & _). cbn [app] in FRT.
      do 8 step. release_frame FRT STT (bv_unsigned sp). step. step.
      apply evt_done.
      destruct (cenv_tailA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) EXP_COST Σ ls OW m _ _ _ _ _ _ EXP_STACK EXP_COST ras
                  ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = wz 1)
                  EVA LSA STT ltac:(clear - LO'; lia) ltac:(clear; lia) eq_refl) as (PREX & UWX & POSTX).
      rewrite Z_to_bv_bv_unsigned in PREX, POSTX.
      eapply implA_mono.
      { eapply (BN_mod_exp_mont_walkA ra sp) with (lo := lo) (ras := ras) (rr := rr) (ra_ := ra_) (rp := rp) (rm := rm) (arr := arr) (ara := ara) (arp := arp) (arm := arm) (ac := ac) (qc := qc) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
          [exact PREX | exact ROOM | exact UWX | exact (uk_ctx_tail _ _ _ E_BN_mod_exp_2ae8e4 CTX) | reflexivity | exact HAr | exact HAa | exact HAp | exact HAm | exact HPr | exact NROa | exact NROp | exact NROm | exact NBa | exact HPC | exact HFR | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | intros w Hw; injection Hw; intros <-; reflexivity]. }
      cbv beta. intros r Σ' ms' PO. apply POSTX. exact PO.
    }
    replace ((bn_top ba =? 1)%nat) with true by (symmetry; apply Nat.eqb_eq; clear - KT; lia). cbn [andb].

    assert (NGa : 0 <= Z.b2z (bn_neg ba) <= 1) by (destruct (bn_neg ba); cbn; lia).
    do 3 step. shl_with ACCa ALa. chk0.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.b2z (bn_neg ba))) by (clear - NGa; lia).
    step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by (clear - NGa; lia).
    {
      replace (bn_neg ba) with true by (destruct (bn_neg ba); [reflexivity| cbn in KN; lia]). cbn [negb andb].
      do 6 step.
      pose proof EVA as (_ & _ & STT & _ & _ & _ & _ & _ & FRT & _ & _). cbn [app] in FRT.
      do 8 step. release_frame FRT STT (bv_unsigned sp). step. step.
      apply evt_done.
      destruct (cenv_tailA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) EXP_COST Σ ls OW m _ _ _ _ _ _ EXP_STACK EXP_COST ras
                  ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = wz 1)
                  EVA LSA STT ltac:(clear - LO'; lia) ltac:(clear; lia) eq_refl) as (PREX & UWX & POSTX).
      rewrite Z_to_bv_bv_unsigned in PREX, POSTX.
      eapply implA_mono.
      { eapply (BN_mod_exp_mont_walkA ra sp) with (lo := lo) (ras := ras) (rr := rr) (ra_ := ra_) (rp := rp) (rm := rm) (arr := arr) (ara := ara) (arp := arp) (arm := arm) (ac := ac) (qc := qc) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
          [exact PREX | exact ROOM | exact UWX | exact (uk_ctx_tail _ _ _ E_BN_mod_exp_2ae8e4 CTX) | reflexivity | exact HAr | exact HAa | exact HAp | exact HAm | exact HPr | exact NROa | exact NROp | exact NROm | exact NBa | exact HPC | exact HFR | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | intros w Hw; injection Hw; intros <-; reflexivity]. }
      cbv beta. intros r Σ' ms' PO. apply POSTX. exact PO.
    }
    replace (bn_neg ba) with false by (destruct (bn_neg ba); [cbn in KN; lia| reflexivity]). cbn [negb andb].

    unfold has_flag, BN_FLG_CONSTTIME. rewrite CTa, CTp, CTm. cbn [Z.eqb negb orb andb].
    clear BNa ACCa MUA.

    step. step. step.
    eapply (get_flags_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) EXP_COST Σ ls OW m LOFB16); [exact EVA | exact LSA | exact HAp | exact NROp |].
    intros mB y0B y1B y2B y4B y5B y6B y7B y8B y9B y10B y11B y12B y13B y14B EVB LSB.
    rewrite (ret_pc_even 2812520) by (clear; lia).
    fold bp. rewrite (unsigned_lit 4) by (clear; lia). rewrite CTp.
    step. if_false.

    step. step. step.
    eapply (get_flags_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) EXP_COST Σ ls OW m LOFB16); [exact EVB | exact LSB | exact HAa | exact NROa |].
    intros mC y0C y1C y2C y4C y5C y6C y7C y8C y9C y10C y11C y12C y13C y14C EVC LSC.
    rewrite (ret_pc_even 2812536) by (clear; lia).
    fold ba. rewrite (unsigned_lit 4) by (clear; lia). rewrite CTa.
    step. if_false.

    step. step. step.
    eapply (get_flags_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) EXP_COST Σ ls OW m LOFB16); [exact EVC | exact LSC | exact HAm | exact NROm |].
    intros mD y0D y1D y2D y4D y5D y6D y7D y8D y9D y10D y11D y12D y13D y14D EVD LSD.
    rewrite (ret_pc_even 2812552) by (clear; lia).
    fold bm. rewrite (unsigned_lit 4) by (clear; lia). rewrite CTm.
    step. if_true.

    destruct (open_for_read LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) EXP_COST Σ ls OW m _ _ _ _ _ _ _ _ 16 EVD LSD HAa NROa ltac:(clear; lia) LOFB16)
      as (Da2 & BNa2 & _ & Ua & _ & _ & _ & _ & _ & _ & ACCa2 & ALa2 & ACCDa & ALDa & BDa & _ & _).
    fold ba in BNa2, Ua, ACCDa, BDa. unfold BnRepDefs.bn_cells in BNa2.
    pose proof (munch_refl (@nil (Z * Z)) mD) as MUD.
    destruct (bn_buf ba) as [|w0 l0] eqn:Ebuf; [exfalso; unfold bn_dmax in OKa2; rewrite Ebuf in OKa2; cbn [length] in OKa2; clear - OKa2 KT; lia|].
    pose proof (limbs_nth (w0 :: l0) 0 OKa1) as LN. cbn [nth] in LN.
    do 2 step. shl_with ACCa2 ALa2. chk0.
    step. unfold MallocRep.wz at 1.
    do 2 step. shl_limb ACCDa ALDa BDa 0. chk0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let a := cur_mem_addr in pose proof (u64arr_read_0 mx Da2 w0 l0 a Ua ltac:(addr_tac)) as RD end.
    step. clear RD.
    cbn [nth].
    do 5 step.
    pose proof EVD as (_ & _ & STT & _ & _ & _ & _ & _ & FRT & _ & _). cbn [app] in FRT.
    do 8 step. release_frame FRT STT (bv_unsigned sp). step. step.
    apply evt_done.
    destruct (cenv_tailA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) EXP_COST Σ ls OW m _ _ _ _ _ _ EXP_STACK EXP_COST ras
                ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = wz 1)
                EVD LSD STT ltac:(clear - LO'; lia) ltac:(clear; lia) eq_refl) as (PREX & UWX & POSTX).
    rewrite Z_to_bv_bv_unsigned in PREX, POSTX.
    eapply implA_mono.
    { eapply (BN_mod_exp_mont_word_walkA ra sp) with (lo := lo) (ras := ras) (rr := rr) (rp := rp) (rm := rm) (A := w0) (arr := arr) (arp := arp) (arm := arm) (ac := ac) (qc := qc) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [exact PREX | exact ROOM | exact UWX | exact (uk_ctx_tail _ _ _ E_BN_mod_exp_2ae984 CTX) | reflexivity | exact HAr | exact HAp | exact HAm | exact HPr | exact NROp | exact NROm | exact HPC | exact HFR | exact LN | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity]. }
    cbv beta. intros r Σ' ms' PO. apply POSTX. exact PO.
  Qed.
End Proofs.

End WithRT.
