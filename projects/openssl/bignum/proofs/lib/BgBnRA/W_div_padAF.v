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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BnDivSpec BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require Import BnCalls.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require Import DivModel.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require W_div_pad.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_expandAF W_lshiftAF W_div_tailAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation pad_model := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_div_pad.pad_model.

Definition div_pre9 (j0 : list byte) (asnum sh arm : Z) (j1 : list byte) (c11 : word) (j2 : list byte) (atmp : Z) (j3 : list byte) (asdiv : Z) (dn : nat) (j4 : list byte)
    (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 : word) : list cell :=
  [CB 32 j0; C8 (Z_to_bv 64 ((asnum + 8) ≫ 3 + SHB)); C8 (Z_to_bv 64 sh); C8 (Z_to_bv 64 arm);
   CB 32 j1; C8 c11; CB 16 j2; C8 (Z_to_bv 64 asnum); C8 (Z_to_bv 64 atmp); CB 8 j3;
   C8 (Z_to_bv 64 (asdiv ≫ 3 + SHB)); C8 (Z_to_bv 64 asdiv); C8 (Z_to_bv 64 (Z.of_nat dn)); CB 8 j4;
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_dv_wexp1 := (E_bn_div_fixed_top_2335d8 : uk_call BN_DIV_FIXED_TOP 0x2337c0 BN_WEXPAND).

Section EnvI.
  Variables (LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (rasO : option (list Z)) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem).

  Lemma cenv_icallA : forall pre used Σ ls m m' OW d n b,
    cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
    In b OW -> blk_addr b <= d -> d + n <= blk_addr b + blk_size b ->
    AHEAP Σ OW LB m' -> stk bgasegs m' lo FB -> mem_inv bgasegs m' ->
    agree_on (fun a => aclient_addr (OW ++ LB) FB a /\ ~ (d <= a < d + n)) m m' ->
    cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m' OW.
  Proof.
    intros pre used Σ ls m m' OW d n b (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) Hb H1 H2 HEAP' ST' MI' AG.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & _).
    pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & BC & _).
    assert (AG' : agree_on (fun a => FB <= a < USTACK_TOP) m m').
    { eapply agree_on_mono; [exact AG|]. intros a Ha. cbv beta in Ha. split; [left; exact Ha|]. unfold BnHeapA.ACEIL in *. lia. }
    unfold cenvA. split; [exact OK|]. split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|].
    split. { eapply ax_pres_trans; [exact AXP|]. eapply ax_pres_weaken; [eapply (ax_pres_of_icall Σ OW LB m m' FB (XW PL) d n b HEAP Hb H1 H2 ltac:(lia) AG) | clear - FBSP; lia]. }
    split; [exact CR|]. split; [exact CNT|]. split; [exact RS|].
    split. { eapply rw_cells_agree; [exact AG' | exact FR |]. intros a Ha. rewrite cells_size_app in Ha. cbn [cells_size csize Nat.add] in Ha.
             unfold USTACK_TOP in *. lia. }
    split; [exact FSZ|].
    unfold uw_opt in *. destruct rasO as [ras|]; [|exact I].
    apply (uw_chain_agree m m' ras SPv (bv_unsigned s0w) UW). eapply agree_on_mono; [exact AG'|]. intros a Ha. cbv beta in *. lia.
  Qed.

  Lemma cenv_silentA_p : forall pre pre' used Σ ls m m' OW W,
    cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW -> lib_parts ls OW PL EA -> munch W m m' -> wmono bgasegs m m' ->
    Forall (w_lib ls OW PL lo SPv) W -> stk bgasegs m' lo FB -> mem_inv bgasegs m' ->
    rw_cells bgasegs m' FB (pre' ++ [C8 s0w; C8 raw]) -> Z.of_nat (cells_size pre') = SPv - FB - 16 ->
    cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre' used Σ ls m' OW.
  Proof.
    intros pre pre' used Σ ls m m' OW W (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) PARTS MU WM HW ST' MI' FR' FSZ'.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _).
    unfold cenvA. split; [exact OK|]. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HW CEIL ltac:(lia))|].
    split; [exact ST'|]. split; [exact MI'|].
    split. { eapply ax_pres_trans; [exact AXP|]. exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HW CEIL ltac:(lia)). }
    split; [exact CR|]. split; [exact CNT|]. split; [exact RS|]. split; [exact FR'|]. split; [exact FSZ'|].
    unfold uw_opt in *. destruct rasO as [ras|]; [|exact I].
    eapply uw_chain_munch_nw; [exact UW | exact MU |].
    eapply Forall_impl; [|exact HW]. intros [x y] [[H1 H2]|[(b & Hb & H1 & H2)|(r & a & HA & NRO & H1 & H2)]]; cbn [fst snd] in *; [exact H2| |].
    - pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & BC & _). lia.
    - pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NOFR).
      destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HA NRO) as (q & Aa & n & Hin & R1 & R2).
      pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & BC & _). lia.
  Qed.
End EnvI.

Lemma div_padA : forall {Y : Type} (REST : unit -> bstate bptr -> btree bptr (Y * bstate bptr)) (Q : Y * bstate bptr -> rts RT -> machine_state -> Prop)
    (ra sp gp s0 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo : Z) (ras : list Z) (TOTAL used : Z)
    (snum : bnref) (asnum : Z)
    (j0 : list byte) (sh arm : Z) (j1 : list byte) (c11 : word) (j2 : list byte) (atmp : Z) (j3 : list byte) (asdiv : Z) (j4 : list byte)
    (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 : word)
    (Σ8 : rts RT) (ls8 : bstate bptr) (m8 : mem) (OW8 : list block) (dn tnp : nat)
    (x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x18 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= bv_unsigned sp - BN_DIV_FT_STACK ->
  cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -272) s0 ra (Some ras) TOTAL Σ ls OW m
        (div_pre9 j0 asnum sh arm j1 c11 j2 atmp j3 asdiv dn j4 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ8 ls8 m8 OW8 ->
  used + MC <= TOTAL ->
  uk_ctx BN_DIV_FIXED_TOP (bv_unsigned ra :: ras) ->
  lib_state ls8 m8 OW8 PL EA ->
  ref_at ls8 OW8 PL snum asnum -> hpl PL snum ->
  bn_top (getbn snum ls8) = tnp -> (tnp <= dn)%nat -> Z.of_nat dn + 1 < 2147483648 ->
  (forall ΣP lsP mP OWP (F' : bvmap 5 word) (fc' : bv 32) y1 y5 y6 y7 y10 y11 y14 y15 y16 y17 y25 y28 y29 y30 y31,
     cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -272) s0 ra (Some ras) TOTAL Σ ls OW m
        (div_pre9 j0 asnum sh arm j1 c11 j2 atmp j3 asdiv dn j4 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC) ΣP lsP mP OWP ->
     lib_state lsP mP OWP PL EA -> refs_stable ls8 OW8 lsP OWP ->
     (forall r, r <> snum -> getbn r lsP = getbn r ls8) ->
     bn_top (getbn snum lsP) = (dn + 1)%nat -> bn_neg (getbn snum lsP) = bn_neg (getbn snum ls8) ->
     firstn (dn + 1) (bn_buf (getbn snum lsP)) = firstn tnp (bn_buf (getbn snum ls8)) ++ repeat 0 (dn + 1 - tnp) ->
     st_ctx lsP = st_ctx ls8 ->
     implA (REST tt lsP) ΣP Q
       (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -272)) gp (Z_to_bv 64 TP_A) y5 y6 y7 sp (Z_to_bv 64 (asnum ≫ 3))
                y10 y11 (Z_to_bv 64 (asnum + 8)) (Z_to_bv 64 (Z.of_nat dn)) y14 y15 y16 y17 x18 (Z_to_bv 64 (Z.of_nat (dn + 1))) (Z_to_bv 64 SHB)
                (Z_to_bv 64 (Z.of_nat tnp)) (Z_to_bv 64 asnum) x23 x24 y25 x26 x27 y28 y29 y30 y31)
           F' (Z_to_bv 64 0x233808) fc' None mP (seg_rom bgasegs))) ->
  implA (bbind (tree_ops bptr) (pad_model snum dn tnp) REST ls8) Σ8 Q
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -272)) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 (asnum ≫ 3))
             x10 x11 (Z_to_bv 64 (asnum + 8)) (Z_to_bv 64 (Z.of_nat dn)) x14 x15 x16 x17 x18 (Z_to_bv 64 (Z.of_nat tnp)) (Z_to_bv 64 SHB)
             (Z_to_bv 64 (Z.of_nat tnp)) (Z_to_bv 64 asnum) x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x2337ac) fc None m8 (seg_rom bgasegs)).
Proof.
  intros until x31. intros LO ENV8 USED CTX LS8 HAsn HPs Etop HPAD HDN K.
  pose proof (proj1 HPs : not_one snum) as NROs.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold BN_DIV_FT_STACK, BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO.
  pose proof ENV8 as (OK & HEAP8 & ST8 & MI8 & _).
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
  pose proof (AH_ceil _ _ _ _ HEAP8) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -272)) = bv_unsigned sp + -272) by (apply unsigned_lit; lia).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS8 HAsn) as HVsn.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS8) as PARTS8; pose proof PARTS8 as (WFS8 & PWF8 & IDS8 & PLB8 & ERRB8).
  pose proof (st_wf_ok snum ls8 WFS8 HVsn NROs) as (OK1 & OK2 & OK3 & OK4).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP8 PARTS8 NOFR HAsn NROs) as (qs0 & As0 & ns0 & Hins0 & Rs01 & Rs02).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP8 Hins0) as (SA00 & _ & _ & SAC0 & _).
  assert (ASN : 0 < asnum /\ asnum + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - SA00 Rs01 Rs02 SAC0 CEIL LO SPR SPT; lia).
  clear qs0 As0 ns0 Hins0 Rs01 Rs02 SA00 SAC0.
  apply implA_from_evt.
  zstep.
  zstep. rewrite (bk_swrap32_small (Z.of_nat dn + 1)) by (clear - HDN; lia).
  do 3 zstep.
  apply evt_done. unfold pad_model. unfold bbind at 1 2. cbn [bind tree_ops].
  apply implA_assoc.
  eapply implA_bind.
  { eapply implA_leaves; [apply (bn_wexpand_leaves2 snum (dn + 1) ls8 HVsn OK2)|].
    eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := snum) (a := asnum) (OW := OW8) (LB := LB) (PL := PL) (EA := EA);
      [| | | reflexivity | exact HAsn | exact (hpl_wref PL snum HPs) | reflexivity | f_equal; f_equal; clear; lia | clear - HDN; lia].
    - eapply cenv_preA; [exact ENV8 | exact LS8 | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV8).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_wexp1 CTX). }
  cbv beta. intros [u9 ls9] Σ9 ms9 [PO LEAF9].
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -272) TOTAL Σ ls OW) in PO; [| exact OK | exact HEAP8].
  cbn [fst snd] in *.
  destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & F9 & fc9 & m9 & OW9 & PL9 & -> & CP9 & (EPL9 & -> & HDM9 & _ & _)).
  subst PL9. specialize (CP9 eq_refl).
  assert (E9 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -272) s0 ra (Some ras) TOTAL Σ ls OW m
                 (div_pre9 j0 asnum sh arm j1 c11 j2 atmp j3 asdiv dn j4 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC) Σ9 ls9 m9 OW9
               /\ lib_state ls9 m9 OW9 PL EA) by (eapply cenv_postA; [exact ENV8 | exact CP9]).
  destruct E9 as (ENV9 & LS9).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP9) as RS9.
  rewrite (ret_pc_even 0x2337c0) by lia. unfold MallocRep.wz.
  clear CP9.
  destruct LEAF9 as (W1 & W2 & W3 & W4 & W5 & _ & WC & _). cbn [snd] in *. rewrite Etop in W2, W5.

  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
  set (b9 := getbn snum ls9) in *.
  set (k := (dn - tnp + 1)%nat).

  pose proof (ref_at_stable _ _ _ _ _ _ _ RS9 HAsn) as HAsn9.
  pose proof ENV9 as (_ & HEAP9 & ST9 & MI9 & _ & _ & _ & _ & FR9 & _ & _). unfold div_pre9 in FR9. cbn [app] in FR9.
  pose proof (AH_nodup_l _ _ _ _ HEAP9) as ND9.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS9) as PARTS9; pose proof PARTS9 as (WFS9 & PWF9 & IDS9 & PLB9 & ERRB9).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS9 HAsn9) as HVsn9.
  destruct (lib_state_open [] ls9 m9 OW9 PL EA snum asnum LS9 ND9 HAsn9 ltac:(intros []) NROs) as ((D9 & BN9 & ARR9) & (OKa & OKb & OKc & OKd) & LSH9).
  fold b9 in BN9, ARR9, OKa, OKb, OKc, OKd.
  destruct (bn_arr_facts_w ls9 OW9 PL EA (bv_unsigned sp) USTACK_TOP Σ9 LB m9 snum D9 HEAP9 PARTS9 FROK HVsn9 (hpl_wref PL snum HPs) ARR9) as (U9 & _ & D90 & D9C & D9I & SEP9).
  fold b9 in U9, D9C, D9I, SEP9.
  pose proof (SEP9 snum asnum HAsn9) as SEPs. clear SEP9.
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP9 PARTS9 NOFR HAsn9 NROs) as (qs & As & ns & Hins & Rs1 & Rs2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP9 Hins) as (SA0 & _ & _ & SAC & SAI).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP9 LS9 NOFR HAsn9 NROs) as (ACSA & ALSA & OFSA).
  destruct (arr_shA _ _ _ _ _ _ HEAP9 (bn_arr_nofr PL snum m9 OW9 _ _ PWF9 NOFR NROs ARR9 ltac:(solve_nbuf))) as (ACS & ALS & OFS). fold b9 in ACS, OFS.
  assert (HD9 : exists p9, bn_d b9 = Some p9 /\ In (p9, D9, 8 * Z.of_nat (bn_dmax b9)) OW9).
  { destruct (bn_d b9) as [p9|] eqn:Ed90; [exists p9; split; [reflexivity|]; unfold bn_arr in ARR9; rewrite Ed90 in ARR9; exact (proj1 ARR9)|].
    exfalso. destruct (bn_arr_null PL snum m9 OW9 D9 b9 PWF9 (hpl_wref PL snum HPs) Ed90 ARR9) as [_ E]. unfold bn_dmax in HDM9. rewrite E in HDM9. cbn in HDM9. lia. }
  destruct HD9 as (p9 & Ed9 & Hinp9).
  unfold bn_cells in BN9. unfold MallocRep.wz in *. unfold BG_DMAX in OKc.
  assert (Lb9 : length (bn_buf b9) = bn_dmax b9) by reflexivity.
  assert (Kk : (tnp + k <= bn_dmax b9)%nat) by (unfold k; clear - HDM9 HPAD; lia).
  assert (Ek : Z.of_nat k = Z.of_nat dn + 1 - Z.of_nat tnp) by (unfold k; clear - HPAD; lia).

  destruct (proj1 (limbarr_split bgasegs m9 D9 (bn_buf b9) tnp ltac:(rewrite Lb9; clear - Kk; lia)) U9) as (Ulo & Urest).
  destruct (proj1 (limbarr_split bgasegs m9 (D9 + 8 * Z.of_nat tnp) (skipn tnp (bn_buf b9)) k ltac:(rewrite length_skipn, Lb9; clear - Kk; lia)) Urest) as (_ & Uhi).
  clear Urest U9.
  pose proof (munch_refl [(bv_unsigned sp + -272, bv_unsigned sp); (asnum, asnum + 24); (D9, D9 + 8 * Z.of_nat (bn_dmax b9))]%Z m9) as MU9.
  pose proof (wmono_refl bgasegs m9) as WM9.
  assert (OFF9 : offshW [(bv_unsigned sp + -272, bv_unsigned sp); (asnum, asnum + 24); (D9, D9 + 8 * Z.of_nat (bn_dmax b9))]).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFSA OFS C2 CEIL LO. lia. }
  assert (OFFa : offshW [(asnum, asnum + 24)]) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFSA; lia).
  repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
  apply implA_from_evt.
  zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ ASN; lia. }
  clear KZ.
  zstep.
  shl_with ACSA ALSA. chk0.
  step.
  step.
  do 2 zstep.
  rewrite (bk_swrap32_small (Z.of_nat dn + 1 - Z.of_nat tnp)) by (clear - HDN HPAD; lia).
  do 3 zstep.

  replace (D9 + Z.of_nat tnp ≪ 3) with (D9 + 8 * Z.of_nat tnp) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace ((Z.of_nat dn + 1 - Z.of_nat tnp) ≪ 3) with (8 * Z.of_nat k) by (rewrite Z.shiftl_mul_pow2 by lia; clear - Ek; lia).
  step.
  assert (INP9 : In (p9, D9, 8 * Z.of_nat (bn_dmax b9)) (OW9 ++ LB)) by (apply in_or_app; left; exact Hinp9).
  apply evt_done.
  eapply implA_step_same.
  { eapply (asan_memset_cpsA) with (d := D9 + 8 * Z.of_nat tnp) (n := 8 * Z.of_nat k) (c := Z_to_bv 8 0) (bd := (p9, D9, 8 * Z.of_nat (bn_dmax b9)))
                                   (lo := lo) (OW := OW9) (LB := LB); try reflexivity.
    - exact HEAP9.
    - rewrite ESP. exact ST9.
    - exact CEIL.
    - rewrite ESP. unfold RT_STACK. clear - LO; lia.
    - rewrite ESP. unfold USTACK_TOP. clear - SPT; lia.
    - rewrite ESP. exact FB16.
    - exact MI9.
    - exact INP9.
    - cbn [blk_addr blk_size fst snd]. clear; lia.
    - cbn [blk_addr blk_size fst snd]. clear - Kk; lia.
    - clear - Kk OKc Lb9; lia. }
  intros ms10 PO. unfold icall_post in PO. rewrite ?ESP in PO.
  destruct PO as (v0 & v1 & v2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & F10 & fc10 & m10 & -> & MI10 & ST10 & HEAP10 & WM10 & AG10 & BZ & WR10).
  rewrite (ret_pc_even 0x2337f0) by lia. unfold MallocRep.wz.
  apply hide_elim in SEPs. apply hide_elim in SAI.

  pose proof (cenv_icallA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -272) s0 ra (Some ras) TOTAL Σ ls OW m _ _ _ _ _ _ _ (D9 + 8 * Z.of_nat tnp) (8 * Z.of_nat k) _
                ENV9 Hinp9 ltac:(cbn [blk_addr blk_size fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear - Kk; lia) HEAP10 ST10 MI10 AG10) as ENV10.
  assert (LSH10 : lib_state_h [snum] ls9 m10 OW9 PL EA).
  { eapply (lib_state_h_icall Σ9 LB [snum] ls9 m9 m10 OW9 PL EA (bv_unsigned sp + -272) (bv_unsigned sp) (D9 + 8 * Z.of_nat tnp) (8 * Z.of_nat k) HEAP9 LSH9 FROK ltac:(clear; lia) AG10).
    eapply (w_limbs OW9 LB ls9 PL EA (bv_unsigned sp) false [snum] _ snum p9 D9); [left; reflexivity| exact HVsn9| exact Ed9| exact Hinp9| cbn [fst snd]; clear; lia| cbn [fst snd]; fold b9; clear - Kk; lia]. }
  eapply (rw_cells_agree _ _ _ _ _ AG10) in FR9; [| intros x Hx; cbn in Hx; split; [left; unfold USTACK_TOP; clear - Hx SPT; lia | unfold BnHeapA.ACEIL in *; clear - Hx D9C CEIL LO Kk; lia]].
  eapply (rw_cells_agree _ _ _ _ _ AG10) in BN9; [| intros x Hx; cbn in Hx; split;
     [right; right; exists (qs, As, ns); split; [exact Hins | cbn; clear - Hx Rs1 Rs2; lia] | clear - Hx SEPs Kk; lia]].
  eapply (u64arr_agree _ _ _ _ _ AG10) in Ulo; [| intros x Hx; rewrite wlimbs_len, firstn_length_le in Hx by (rewrite Lb9; clear - Kk; lia); split;
     [right; right; exists (p9, D9, 8 * Z.of_nat (bn_dmax b9)); split; [exact INP9 | cbn [blk_addr blk_size fst snd]; clear - Hx Kk; lia] | clear - Hx; lia]].
  eapply (u64arr_agree _ _ _ _ _ AG10) in Uhi; [| intros x Hx; rewrite wlimbs_len, !length_skipn, Lb9 in Hx; split;
     [right; right; exists (p9, D9, 8 * Z.of_nat (bn_dmax b9)); split; [exact INP9 | cbn [blk_addr blk_size fst snd]; clear - Hx Kk; lia] | clear - Hx Kk; lia]].

  assert (POST : u64arr bgasegs m10 (D9 + 8 * Z.of_nat tnp) (wlimbs (repeat 0 k))).
  { apply limbarr_limbs_at. rewrite repeat_length. split; [|exact WR10].
    unfold limbs_at. rewrite BnCalls.lbytes_repeat0. replace (8 * k)%nat with (Z.to_nat (8 * Z.of_nat k)) by (clear; lia). exact BZ. }
  assert (U10 : u64arr bgasegs m10 D9 (wlimbs (splice (bn_buf b9) tnp (repeat 0 k)))).
  { unfold splice. rewrite repeat_length.
    apply limbarr_app. split; [exact Ulo|]. rewrite firstn_length_le by (rewrite Lb9; clear - Kk; lia).
    apply limbarr_app. split; [exact POST|]. rewrite repeat_length.
    replace (skipn (tnp + k) (bn_buf b9)) with (skipn k (skipn tnp (bn_buf b9))) by (rewrite skipn_skipn; f_equal; clear; lia).
    exact Uhi. }
  clear Ulo Uhi POST BZ WR10.
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP10 LSH10 NOFR HAsn9 NROs) as (ACSA10 & _ & _).

  apply hide_intro in SEPs. apply hide_intro in SAI. apply hide_intro in U10.
  pose proof (munch_refl [(asnum, asnum + 24)]%Z m10) as MUa. pose proof (wmono_refl bgasegs m10) as WMa.
  clear MU9 WM9 ACSA ACS HEAP9 ST9 MI9 LSH9.
  apply implA_from_evt.
  step.
  shl_with ACSA10 ALSA.
  zstep.
  chk0.
  zstep.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m11 end.
  apply hide_elim in U10. apply hide_elim in SEPs.
  eapply (u64arr_transport bgasegs _ m10 m11) in U10; [| exact MUa | match goal with WMx : wmono _ m10 m11 |- _ => exact WMx end |
    cbn [disjoint_from]; rewrite wlimbs_len, splice_length by (rewrite repeat_length, Lb9; exact Kk); rewrite Lb9; split; [clear - SEPs; lia | exact I] ].

  set (SN := mkBN (bn_d b9) (splice (bn_buf b9) tnp (repeat 0 k)) (dn + 1) (bn_neg b9) (bn_flags b9)).
  assert (Lspl : length (splice (bn_buf b9) tnp (repeat 0 k)) = bn_dmax b9) by (rewrite splice_length by (rewrite repeat_length, Lb9; exact Kk); exact Lb9).
  assert (WOK : Forall (w_ok OW9 LB ls9 PL EA (bv_unsigned sp) [snum]) [(asnum, asnum + 24)]).
  { constructor; [eapply (w_struct OW9 LB ls9 PL EA (bv_unsigned sp) false [snum] _ snum asnum); [left; reflexivity| exact HAsn9| exact NROs| cbn; clear; lia| cbn; clear; lia]| constructor]. }
  assert (HWL : Forall (w_lib ls9 OW9 PL lo (bv_unsigned sp)) [(asnum, asnum + 24)]).
  { constructor; [w_lib_ref HAsn9 NROs| constructor]. }
  match goal with MUx : munch _ m10 m11, WMx : wmono _ m10 m11, STx : stk _ m11 _ _, MIx : mem_inv _ m11, FRx : rw_cells _ m11 (bv_unsigned sp + -272) _ |- _ =>
    rename MUx into MUaF; rename WMx into WMaF; rename STx into ST11; rename MIx into MI11; rename FRx into FR11 end.
  assert (LSP : lib_state (setbn snum SN ls9) m11 OW9 PL EA).
  { unfold lib_state. eapply (lib_state_close [] ls9 m11 OW9 PL EA snum asnum); [| exact ND9 | exact HAsn9 | exact NROs | | |].
    - exact (lib_state_frame Σ9 LB (bv_unsigned sp) USTACK_TOP [snum] ls9 m10 m11 OW9 PL EA _ HEAP10 LSH10 MUaF WMaF FROK WOK).
    - exists D9. split.
      + unfold bn_cells, SN, bn_dmax, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lspl.
        replace (Z.of_nat (dn + 1)) with (Z.of_nat dn + 1) by (clear; lia). exact BN9.
      + unfold bn_arr, SN, bn_dmax. cbn [bn_d bn_buf]. rewrite Ed9, Lspl. split; [exact Hinp9 | exact U10].
    - apply hide_elim in OKd. unfold bg_ok, SN, bn_dmax, BG_DMAX. cbn [bn_top bn_buf bn_flags]. rewrite Lspl.
      split; [apply splice_limbs; [exact OKa | apply limbs_repeat; exact limb_0]|]. split; [exact HDM9|]. split; [exact OKc| exact OKd].
    - apply ids_ok_setbn_same; [exact IDS9 | exact HVsn9 |]. fold b9. unfold bn_blocks, SN, bn_dmax. cbn [bn_d bn_buf]. rewrite Lspl. reflexivity. }
  assert (ENVP : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -272) s0 ra (Some ras) TOTAL Σ ls OW m
                   (div_pre9 j0 asnum sh arm j1 c11 j2 atmp j3 asdiv dn j4 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC) Σ9 (setbn snum SN ls9) m11 OW9).
  { apply cenv_setbnA; [| exact HVsn9 | fold b9; unfold bn_blocks, SN; cbn [bn_d bn_buf bn_dmax bn_top]; rewrite ?Ed9; reflexivity].
    eapply (cenv_silentA_p LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -272) s0 ra (Some ras) TOTAL Σ ls OW m);
      [exact ENV10 | exact PARTS9 | exact MUaF | exact WMaF | exact HWL | exact ST11 | exact MI11 | unfold div_pre9; cbn [app]; exact FR11 | cbn; lia]. }
  apply evt_done.
  replace (Z.of_nat dn + 1) with (Z.of_nat (dn + 1)) by (clear; lia).
  eapply K; [exact ENVP | exact LSP | | | | | |].
  - eapply refs_stable_trans; [exact RS9| apply refs_stable_setbn].
  - intros r0 Hr0. rewrite getbn_setbn_other by (apply not_eq_sym; exact Hr0). apply W1. apply not_eq_sym. exact Hr0.
  - rewrite getbn_setbn_same by exact HVsn9. reflexivity.
  - rewrite getbn_setbn_same by exact HVsn9. cbn [SN bn_neg]. exact W3.
  - rewrite getbn_setbn_same by exact HVsn9. cbn [SN bn_buf].
    replace (dn + 1)%nat with (tnp + k)%nat by (unfold k; clear - HPAD; lia).
    rewrite firstn_pad_zeros by (rewrite Lb9; exact Kk). rewrite W5.
    replace (tnp + k - tnp)%nat with k by (clear; lia). reflexivity.
  - rewrite st_ctx_setbn. exact WC.
Qed.

End WithRT.
