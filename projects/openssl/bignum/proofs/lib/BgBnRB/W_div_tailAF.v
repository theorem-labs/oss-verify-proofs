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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnDivWords BnDivLoop BnSpecs2 BnDivSpec.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure DivLoopPure DivTop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require DivLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2 AW_div_body AW_div_loop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require W_div_tail.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_expandAF ShiftKitAF W_lshiftAF W_rshiftAF W_ctxAF W_ctx_endAF.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import UbStruct.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_DIV_FIXED_TOP : Z := 0x234b80.

Definition BN_DIV_FT_STACK : Z := 304 + BN_LSHIFT_STACK.

Definition oref_at (bs : bstate bptr) (OW : list block) (PL : placement) (o : option bnref) (a : Z) : Prop :=
  match o with Some r => ref_at bs OW PL r a | None => a = 0 end.

Lemma oref_at_stable : forall st OW st' OW' PL o a, refs_stable st OW st' OW' -> oref_at st OW PL o a -> oref_at st' OW' PL o a.
Proof. intros st OW st' OW' PL [r|] a RS H; [exact (ref_at_stable _ _ _ _ _ _ _ RS H)| exact H]. Qed.

Lemma oref_at_setbn : forall st OW PL r b o a, oref_at st OW PL o a -> oref_at (setbn r b st) OW PL o a.
Proof. intros st OW PL r b [r'|] a H; [apply ref_at_setbn; exact H| exact H]. Qed.

Lemma vref_setbn : forall r r' b (bs : bstate bptr), vref r bs -> vref r (setbn r' b bs).
Proof. intros r r' b bs H. unfold vref in *. rewrite length_setbn. exact H. Qed.

Notation div_tail_model := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_div_tail.div_tail_model.
Notation bbind_get := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_div_tail.bbind_get.
Notation bbind_set := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_div_tail.bbind_set.
Notation bbind_ret := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_div_tail.bbind_ret.

Definition div_pre (c0 : list byte) (negn : bool) (asnum sh actx arm d1 : Z) (dn : nat) (loop : nat) (asdiv : Z) (wt iw wn : Z)
    (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 : word) : list cell :=
  [CB 8 c0; C8 (Z_to_bv 64 (Z.b2z negn)); C8 (Z_to_bv 64 (shad (asnum + 8))); C8 (Z_to_bv 64 (asnum + 8)); C8 (Z_to_bv 64 sh); C8 (Z_to_bv 64 actx); C8 (Z_to_bv 64 arm);
   C8 (Z_to_bv 64 (d1 mod 4294967296)); C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 (Z.shiftr d1 32));
   C8 (Z_to_bv 64 (Z.of_nat dn + 1)); C8 (Z_to_bv 64 d1);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (8 * Z.of_nat dn)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 asnum); C8 (Z_to_bv 64 (Z.of_nat loop)); C8 (Z_to_bv 64 (shad asdiv));
   C8 (Z_to_bv 64 wt); C8 (Z_to_bv 64 asdiv); C8 (Z_to_bv 64 iw); C8 (Z_to_bv 64 (Z.of_nat dn)); C8 (Z_to_bv 64 wn);
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].

Definition div_pre9 (j0 : list byte) (asnum sh actx arm : Z) (j1 j2 : list byte) (asdiv : Z) (j3 : list byte) (anum : Z) (dn : nat) (j4 : list byte)
    (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 : word) : list cell :=
  [CB 16 j0; C8 (Z_to_bv 64 ((asnum + 8) ≫ 3 + SHB)); C8 (Z_to_bv 64 (asnum + 8)); C8 (Z_to_bv 64 sh); C8 (Z_to_bv 64 actx); C8 (Z_to_bv 64 arm);
   CB 80 j1; C8 (Z_to_bv 64 asnum); CB 8 j2; C8 (Z_to_bv 64 (asdiv ≫ 3 + SHB)); CB 8 j3; C8 (Z_to_bv 64 asdiv); C8 (Z_to_bv 64 anum); C8 (Z_to_bv 64 (Z.of_nat dn)); CB 8 j4;
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].

Ltac drop2 l :=
  lazymatch l with
  | [_; _] => constr:(@nil cell)
  | ?x :: ?t => let t' := drop2 t in constr:(x :: t')
  end.

Ltac env_openA ENV :=
  let E := fresh "ENVo" in
  let HEAPe := fresh "HEAPe" in let STe := fresh "STe" in let MIe := fresh "MIe" in let FRe := fresh "FRe" in let FSZe := fresh "FSZe" in
  let MUe := fresh "MUe" in let WMe := fresh "WMe" in
  pose proof ENV as E;
  destruct E as (_ & HEAPe & STe & MIe & _ & _ & _ & _ & FRe & FSZe & _);
  try unfold div_pre in FRe; try unfold div_pre9 in FRe; cbn [app] in FRe;
  lazymatch type of MIe with mem_inv _ ?mm =>
    lazymatch type of STe with stk _ _ _ ?fb =>
      lazymatch type of FSZe with _ = ?spv - _ - 16 =>
        pose proof (munch_refl [(fb, spv)]%Z mm) as MUe; pose proof (wmono_refl bgbsegs mm) as WMe
      end
    end
  end;
  clear FSZe.

Ltac env_closeA HWLs WOKs ENV LS ENVn LSn :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of LS with lib_state ?lsx ?m0x ?OWx ?PLx ?EAx =>
      lazymatch type of ENV with cenvA ?LB ?PL ?lo ?SPv ?FB ?s0w ?raw ?rasO ?TOT ?Sg0 ?ls0 ?OW0 ?m00 ?pre ?used ?Sgx _ _ _ =>
        match goal with
        | FRx : rw_cells _ mx FB ?fr', STx : stk _ mx _ FB, MIx : mem_inv _ mx, MUx : munch _ m0x mx, WMx : wmono _ m0x mx,
          HEAPx : @BnHeapA.AHEAP _ Sgx OWx LB m0x, FROKx : frames_ok LB PLx SPv USTACK_TOP |- _ =>
            let pre' := drop2 fr' in
            assert (ENVn : cenvA LB PL lo SPv FB s0w raw rasO TOT Sg0 ls0 OW0 m00 pre' used Sgx lsx mx OWx)
              by (eapply (cenv_silentA LB PL EAx lo SPv FB s0w raw rasO TOT Sg0 ls0 OW0 m00 pre pre');
                    [exact ENV | exact LS | exact MUx | exact WMx | apply HWLs | exact STx | exact MIx | cbn [app]; exact FRx | cbn; lia]);
            pose proof (lib_state_frame Sgx LB SPv USTACK_TOP [] lsx m0x mx OWx PLx EAx _ HEAPx LS MUx WMx FROKx (WOKs _ _) : lib_state lsx mx OWx PLx EAx) as LSn;
            clear FRx STx MIx MUx WMx HEAPx
        end
      end
    end
  end.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_dv_rshift := (E_bn_div_fixed_top_2352c8 : uk_call BN_DIV_FIXED_TOP 0x2354b0 BN_RSHIFT).

Lemma implA_post_evt : forall {A} (t : btree bptr A) Σ (Q1 Q : A -> rts RT -> machine_state -> Prop) ms,
  implA t Σ Q1 ms -> (forall a Σ' ms', Q1 a Σ' ms' -> evt bgbsegs (Q a Σ') ms') -> implA t Σ Q ms.
Proof.
  intros A t Σ Q1 Q ms H HK X Φ S T c Hc Hk.
  apply (H X Φ S T c Hc).
  intros c' (a & X' & Σ' & HΦ & Hc').
  apply (asta_evtA Σ' (Q1 a Σ') (Q a Σ') (HK a Σ') T c' Hc').
  intros c'' Hc''. apply Hk. exists a, X', Σ'. split; [exact HΦ | exact Hc''].
Qed.

Lemma div_tailA : forall
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo : Z) (ras : list Z) (TOTAL used : Z) (c0 : list byte)
    (res tmp snum sdiv : bnref) (rm : option bnref) (adv arm atmp asnum asdiv ac : Z) (qc : bptr)
    (ΣU : rts RT) (lsU : bstate bptr) (mL : mem) (OWU : list block)
    (sdbuf : list Z) (dn loop nP : nat) (d0 d1 sh : Z) (negn : bool) (psn pv : bptr) (DsnP Ddv : Z)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word),
  lo <= bv_unsigned sp - BN_DIV_FT_STACK -> pl_ctx PL = Some (ac, qc) ->
  cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) TOTAL Σ ls OW m
        (div_pre c0 negn asnum sh ac arm d1 dn loop asdiv (DsnP + 8 * Z.of_nat nP - 8) 0 (DsnP + 8 * Z.of_nat loop) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1)
        used ΣU lsU mL OWU ->
  used + MC <= TOTAL ->
  uk_ctx BN_DIV_FIXED_TOP (bv_unsigned ra :: ras) ->
  lib_state lsU mL OWU PL EA ->
  ref_at lsU OWU PL res adv -> oref_at lsU OWU PL rm arm -> ref_at lsU OWU PL tmp atmp -> ref_at lsU OWU PL snum asnum -> ref_at lsU OWU PL sdiv asdiv ->
  wref PL res -> (forall r, rm = Some r -> hpl PL r) -> hpl PL tmp -> hpl PL snum -> hpl PL sdiv ->
  tmp <> snum -> tmp <> sdiv -> snum <> sdiv -> res <> tmp -> res <> snum -> res <> sdiv ->

  bn_buf (getbn sdiv lsU) = sdbuf -> bn_top (getbn sdiv lsU) = dn -> (1 <= dn)%nat ->
  d0 = nth (dn - 1) sdbuf 0 -> d1 = (if (dn =? 1)%nat then 0 else nth (dn - 2) sdbuf 0) -> 9223372036854775808 <= d0 ->

  bn_top (getbn snum lsU) = nP -> nP = (loop + dn)%nat -> (1 <= loop)%nat ->
  bn_d (getbn snum lsU) = Some psn -> In (psn, DsnP, 8 * Z.of_nat (bn_dmax (getbn snum lsU))) OWU ->
  lval (slice (bn_buf (getbn snum lsU)) loop dn) < lval (firstn dn sdbuf) ->

  bn_d (getbn res lsU) = Some pv -> In (pv, Ddv, 8 * Z.of_nat (bn_dmax (getbn res lsU))) OWU ->
  bn_top (getbn res lsU) = loop -> (loop <= bn_dmax (getbn res lsU))%nat ->
  (dn + 1 <= bn_dmax (getbn tmp lsU))%nat ->
  0 <= sh < 64 ->
  implA (div_tail_model tmp snum res rm sdbuf dn loop nP d0 d1 negn sh lsU) ΣU
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA TOTAL (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp x9
             x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 d0) (Z_to_bv 64 (Ddv + 8 * Z.of_nat loop)) (Z_to_bv 64 atmp) (Z_to_bv 64 (shad atmp))
             (Z_to_bv 64 (Z.of_nat dn + 1)) x23 (Z_to_bv 64 SHB) (Z_to_bv 64 (8 * Z.of_nat dn)) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x235130) fc None mL (seg_rom bgbsegs)).
Proof.
  intros until x31.
  intros LO EC ENVU USED CTX LSU HAdv HArm HAtmp HAsnum HAsdiv WRFv HPrm HPt HPs HPd NEts NEtd NEsd NEvt NEvs NEvd
         Esdb Etopd HDN Hd0 Hd1 Hnorm Etopn HnP LOOP1 Edsn Hinsn HTOPC Edv Hinpv Etopv HLr HLt Hsh.
  pose proof (proj1 WRFv : not_one res) as NROv. pose proof (proj1 HPt : not_one tmp) as NROt. pose proof (proj1 HPs : not_one snum) as NROs. pose proof (proj1 HPd : not_one sdiv) as NROd.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold BN_DIV_FT_STACK, BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO.
  pose proof ENVU as (OK & HEAPU & STU & MIU & AXPU & CRU & CNTU & RSU & FRU & FSZU & UWU).
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
  pose proof (AH_ceil _ _ _ _ HEAPU) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -304)) = bv_unsigned sp + -304) by (apply unsigned_lit; lia).
  assert (HWLs : forall lsx OWx, Forall (w_lib lsx OWx PL lo (bv_unsigned sp)) [(bv_unsigned sp + -304, bv_unsigned sp)]) by (intros lsx OWx; constructor; [left; cbn; lia| constructor]).
  assert (WOKs : forall OWx lsx, Forall (w_ok OWx LB lsx PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -304, bv_unsigned sp)]).
  { intros OWx lsx; constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }

  assert (FIN : forall ΣS lsS mS OWS usedS FS fcS y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31,
             cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) TOTAL Σ ls OW m
               (div_pre c0 negn asnum sh ac arm d1 dn loop asdiv (DsnP + 8 * Z.of_nat (nP - 1 - loop)) (Z.of_nat loop) (DsnP + 8 * Z.of_nat (loop - loop)) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) usedS ΣS lsS mS OWS ->
             lib_state lsS mS OWS PL EA -> usedS <= TOTAL ->
             implA (BN_CTX_end (tree_ops bptr) lsS) ΣS
               (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA TOTAL (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
               (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp (Z_to_bv 64 TP_A) y5 y6 y7 sp (Z_to_bv 64 1) y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 (Z_to_bv 64 ac) y28 y29 y30 y31)
                   FS (Z_to_bv 64 0x2354b8) fcS None mS (seg_rom bgbsegs))).
  { intros ΣS lsS mS OWS usedS FS fcS y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31 ENVS LSS US.
    clear ENVU LSU HAdv HArm HAtmp HAsnum HAsdiv Esdb Etopd Etopn Edsn Hinsn HTOPC Edv Hinpv Etopv HLr HLt HEAPU STU MIU AXPU CRU CNTU RSU FRU FSZU UWU.
    apply implA_from_evt.
    zstep. step.
    apply evt_done.
    eapply implA_post_evt.
    { eapply BN_CTX_end_walkA with (lo := lo) (OW := OWS) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc); [ | reflexivity | exact EC | reflexivity].
      eapply cenv_preA; [exact ENVS | exact LSS | unfold BN_CTX_END_STACK; clear - LO; lia | clear - US; lia]. }
    cbv beta. intros [uE lsE] ΣE msE PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) TOTAL Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENVS))].
    cbn [fst snd] in *.
    destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & F3 & fc3 & mE & OWE & PLE & -> & CPE & (EPLE & _)).
    subst PLE. specialize (CPE eq_refl).
    destruct (cenv_postA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ENVS CPE) as (ENVE & LSE).
    rewrite (ret_pc_even 0x2354c0) by lia. unfold MallocRep.wz.
    clear CPE.
    pose proof (cenv_finalA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ENVE LSE ltac:(clear - US; lia))
      as (F1 & F2' & F3' & F4 & F5 & F6 & F7).
    env_openA ENVE.
    zstep. do 13 step.
    release_frame FRe STe (bv_unsigned sp). step. step.
    apply evt_done.
    unfold bn_postA. do 17 eexists. exists mE, OWE, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact F2'|]. split; [exact STe|]. split; [exact F3'|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; reflexivity. }

  pose proof (AH_nodup_l _ _ _ _ HEAPU) as ND.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LSU) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSU HAsnum) as HVsn. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSU HAdv) as HVdv.
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSU HAtmp) as HVtm. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSU HAsdiv) as HVsd.
  destruct (lib_state_open [] lsU mL OWU PL EA sdiv asdiv LSU ND HAsdiv ltac:(intros []) NROd) as ((Dsd & BNsd & ARRsd) & (OKd1 & OKd2 & OKd3 & OKd4) & _).
  destruct (lib_state_open [] lsU mL OWU PL EA snum asnum LSU ND HAsnum ltac:(intros []) NROs) as ((Dsn & BNsn & ARRsn) & (OKn1 & OKn2 & OKn3 & OKn4) & LSH1).
  destruct (lib_state_open [snum] lsU mL OWU PL EA res adv LSH1 ND HAdv ltac:(intros [E|[]]; apply NEvs; symmetry; exact E) NROv) as ((Dv & BNdv & ARRdv) & (OKv1 & OKv2 & OKv3 & OKv4) & LSH2).
  destruct (lib_state_open [res; snum] lsU mL OWU PL EA tmp atmp LSH2 ND HAtmp ltac:(intros [E|[E|[]]]; [apply NEvt; exact E| apply NEts; symmetry; exact E]) NROt)
    as ((Dt & BNt & ARRt) & (OKt1 & OKt2 & OKt3 & OKt4) & LSH3).
  set (bsn := getbn snum lsU) in *. set (bvv := getbn res lsU) in *. set (btm := getbn tmp lsU) in *. set (bsd := getbn sdiv lsU) in *.

  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAPU LSU NOFR HAtmp NROt) as (ACTA & ALTA & OFTA).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAPU LSU NOFR HAsdiv NROd) as (ACVA & ALVA & OFVA).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAPU LSU NOFR HAsnum NROs) as (ACSA & ALSA & OFSA).
  destruct (arr_shA _ _ _ _ _ _ HEAPU (bn_arr_nofr PL snum mL OWU _ _ PWF NOFR NROs ARRsn ltac:(solve_nbuf))) as (ACS & ALS & OFS). fold bsn in ACS, OFS.
  destruct (arr_shA _ _ _ _ _ _ HEAPU (bn_arr_nofr PL tmp mL OWU _ _ PWF NOFR NROt ARRt ltac:(solve_nbuf))) as (ACT & ALT & OFT). fold btm in ACT, OFT.
  destruct (arr_shA _ _ _ _ _ _ HEAPU (bn_arr_nofr PL res mL OWU _ _ PWF NOFR NROv ARRdv ltac:(solve_nbuf))) as (ACR & ALR & OFR). fold bvv in ACR, OFR.
  destruct (arr_shA _ _ _ _ _ _ HEAPU (bn_arr_nofr PL sdiv mL OWU _ _ PWF NOFR NROd ARRsd ltac:(solve_nbuf))) as (ACV & ALV & OFV). fold bsd in ACV, OFV.
  pose proof (AH_shb _ _ _ _ HEAPU) as SHB0.

  assert (EDsn : Dsn = DsnP).
  { unfold bn_arr in ARRsn. rewrite Edsn in ARRsn. exact (proj1 (AH_addr_unique OWU psn Dsn _ DsnP _ ND (proj1 ARRsn) Hinsn)). }
  subst Dsn.
  assert (EDv : Dv = Ddv).
  { unfold bn_arr in ARRdv. rewrite Edv in ARRdv. exact (proj1 (AH_addr_unique OWU pv Dv _ Ddv _ ND (proj1 ARRdv) Hinpv)). }
  subst Dv.
  assert (HDT : exists pt, bn_d btm = Some pt /\ In (pt, Dt, 8 * Z.of_nat (bn_dmax btm)) OWU).
  { destruct (bn_d btm) as [pt|] eqn:Edt0; [exists pt; split; [reflexivity|]; unfold bn_arr in ARRt; rewrite Edt0 in ARRt; exact (proj1 ARRt)|].
    exfalso. destruct (bn_arr_null PL tmp mL OWU Dt btm PWF (hpl_wref PL tmp HPt) Edt0 ARRt) as [_ E]. unfold bn_dmax in HLt. rewrite E in HLt. cbn in HLt. lia. }
  destruct HDT as (pt & Edt & Hinpt).
  assert (HDS : exists psd, bn_d bsd = Some psd /\ In (psd, Dsd, 8 * Z.of_nat (bn_dmax bsd)) OWU).
  { destruct (bn_d bsd) as [psd|] eqn:Edsd0; [exists psd; split; [reflexivity|]; unfold bn_arr in ARRsd; rewrite Edsd0 in ARRsd; exact (proj1 ARRsd)|].
    exfalso. destruct (bn_arr_null PL sdiv mL OWU Dsd bsd PWF (hpl_wref PL sdiv HPd) Edsd0 ARRsd) as [_ E]. unfold bn_dmax in OKd2. rewrite E in OKd2. cbn in OKd2. lia. }
  destruct HDS as (psd & Edsd & Hinpsd).
  destruct (bn_arr_facts_w lsU OWU PL EA (bv_unsigned sp) USTACK_TOP ΣU LB mL snum DsnP HEAPU PARTS FROK HVsn (hpl_wref PL snum HPs) ARRsn) as (Usn & _ & Sn0 & SnC & SnI & SEPsn). fold bsn in Usn, SnC, SnI, SEPsn.
  destruct (bn_arr_facts_w lsU OWU PL EA (bv_unsigned sp) USTACK_TOP ΣU LB mL res Ddv HEAPU PARTS FROK HVdv WRFv ARRdv) as (Uv & _ & V0 & VC & VI & SEPv). fold bvv in Uv, VC, VI, SEPv.
  destruct (bn_arr_facts_w lsU OWU PL EA (bv_unsigned sp) USTACK_TOP ΣU LB mL tmp Dt HEAPU PARTS FROK HVtm (hpl_wref PL tmp HPt) ARRt) as (Ut & _ & T0 & TC & TI & SEPt). fold btm in Ut, TC, TI, SEPt.
  destruct (bn_arr_facts_w lsU OWU PL EA (bv_unsigned sp) USTACK_TOP ΣU LB mL sdiv Dsd HEAPU PARTS FROK HVsd (hpl_wref PL sdiv HPd) ARRsd) as (Usd & _ & D0 & DC & _ & SEPd). fold bsd in Usd, DC, SEPd.
  pose proof (limbs_limbs_disj ΣU OWU LB mL HEAPU lsU PL EA PARTS snum tmp _ _ _ _ _ _ (not_eq_sym NEts) HVsn HVtm Edsn Edt Hinsn Hinpt) as DJst.
  pose proof (limbs_limbs_disj ΣU OWU LB mL HEAPU lsU PL EA PARTS snum sdiv _ _ _ _ _ _ NEsd HVsn HVsd Edsn Edsd Hinsn Hinpsd) as DJsd.
  pose proof (limbs_limbs_disj ΣU OWU LB mL HEAPU lsU PL EA PARTS snum res _ _ _ _ _ _ (not_eq_sym NEvs) HVsn HVdv Edsn Edv Hinsn Hinpv) as DJsv.
  pose proof (limbs_limbs_disj ΣU OWU LB mL HEAPU lsU PL EA PARTS tmp sdiv _ _ _ _ _ _ NEtd HVtm HVsd Edt Edsd Hinpt Hinpsd) as DJtd.
  pose proof (limbs_limbs_disj ΣU OWU LB mL HEAPU lsU PL EA PARTS tmp res _ _ _ _ _ _ (not_eq_sym NEvt) HVtm HVdv Edt Edv Hinpt Hinpv) as DJtv.
  pose proof (limbs_limbs_disj ΣU OWU LB mL HEAPU lsU PL EA PARTS res sdiv _ _ _ _ _ _ NEvd HVdv HVsd Edv Edsd Hinpv Hinpsd) as DJvd.
  pose proof (SEPsn tmp atmp HAtmp) as DJs_ta. pose proof (SEPsn sdiv asdiv HAsdiv) as DJs_va. pose proof (SEPsn snum asnum HAsnum) as DJs_sa.
  pose proof (SEPt tmp atmp HAtmp) as DJt_ta. pose proof (SEPt sdiv asdiv HAsdiv) as DJt_va. pose proof (SEPt snum asnum HAsnum) as DJt_sa.
  pose proof (SEPv tmp atmp HAtmp) as DJv_ta. pose proof (SEPv sdiv asdiv HAsdiv) as DJv_va. pose proof (SEPv snum asnum HAsnum) as DJv_sa.
  pose proof (SEPsn res adv HAdv) as DJs_da. pose proof (SEPt res adv HAdv) as DJt_da. pose proof (SEPv res adv HAdv) as DJv_da.
  pose proof (struct_disj ΣU OWU LB mL HEAPU lsU PL EA (bv_unsigned sp) USTACK_TOP PARTS FROK tmp snum atmp asnum NEts HAtmp HAsnum) as DJ_ta_sa.
  pose proof (struct_disj ΣU OWU LB mL HEAPU lsU PL EA (bv_unsigned sp) USTACK_TOP PARTS FROK res snum adv asnum NEvs HAdv HAsnum) as DJ_da_sa.
  pose proof (struct_disj ΣU OWU LB mL HEAPU lsU PL EA (bv_unsigned sp) USTACK_TOP PARTS FROK sdiv snum asdiv asnum (not_eq_sym NEsd) HAsdiv HAsnum) as DJ_va_sa.
  clear SEPsn SEPt SEPv SEPd.
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAPU PARTS NOFR HAtmp NROt) as (qt & At & nt & Hint & Rt1 & Rt2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAPU Hint) as (TA0 & _ & _ & TAC & _).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAPU PARTS NOFR HAsdiv NROd) as (qd & Ad & nd & Hind & Rd1 & Rd2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAPU Hind) as (VA0 & _ & _ & VAC & _).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAPU PARTS NOFR HAsnum NROs) as (qs & As & ns & Hins & Rs1 & Rs2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAPU Hins) as (SA0 & _ & _ & SAC & SAI).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAPU PARTS NOFR HAdv NROv) as (qv & Av & nv & Hinv & Rv1 & Rv2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAPU Hinv) as (DA0 & _ & _ & DAC & DAI).

  cbn [app] in FRU. unfold div_pre in FRU.
  unfold BG_DMAX in OKn3, OKv3, OKt3, OKd3.
  destruct (proj1 (limbarr_limbs_at bgbsegs mL DsnP (bn_buf bsn)) Usn) as (LAsn & WRsn).
  destruct (proj1 (limbarr_limbs_at bgbsegs mL Dt (bn_buf btm)) Ut) as (LAt & WRt).
  destruct (proj1 (limbarr_limbs_at bgbsegs mL Ddv (bn_buf bvv)) Uv) as (LAv & WRv).
  destruct (proj1 (limbarr_limbs_at bgbsegs mL Dsd (bn_buf bsd)) Usd) as (LAsd & _).
  rewrite Esdb in LAsd, OKd1.
  assert (Lsdb : length sdbuf = bn_dmax bsd) by (rewrite <- Esdb; reflexivity).
  assert (DLB : dl_bndA DsnP Dt Dsd Ddv atmp asdiv lo (bv_unsigned sp) (bn_dmax bsn) (bn_dmax btm) (length sdbuf) (bn_dmax bvv)).
  { unfold dl_bndA. rewrite Lsdb. unfold BnHeapA.ACEIL in *. clear - Sn0 SnC T0 TC D0 DC V0 VC TA0 TAC Rt1 Rt2 VA0 VAC Rd1 Rd2 CEIL LO SPR SPT. lia. }
  assert (DLP : DivLoop.dl_pair DsnP Dt Dsd Ddv atmp asdiv (bn_dmax bsn) (bn_dmax btm) (length sdbuf) (bn_dmax bvv)).
  { unfold DivLoop.dl_pair, DivLoop.dj. rewrite Lsdb.
    split; [clear - DJst; lia|]. split; [clear - DJsd; lia|]. split; [clear - DJsv; lia|]. split; [clear - DJs_ta; lia|]. split; [clear - DJs_va; lia|].
    split; [clear - DJtd; lia|]. split; [clear - DJtv; lia|]. split; [clear - DJt_ta; lia|]. split; [clear - DJt_va; lia|].
    split; [clear - DJvd; lia|]. split; [clear - DJv_ta; lia|]. clear - DJv_va; lia. }
  assert (DAL : db_al DsnP Dt Dsd Ddv atmp asdiv).
  { unfold db_al. split; [exact ALS|]. split; [exact ALT|]. split; [exact ALV|]. split; [exact ALR|]. split; [exact ALTA| exact ALVA]. }
  assert (OFFWL : offshW [(DsnP, DsnP + 8 * Z.of_nat (bn_dmax bsn)); (Dt, Dt + 8 * Z.of_nat (bn_dmax btm)); (Ddv, Ddv + 8 * Z.of_nat (bn_dmax bvv));
                          (bv_unsigned sp - 416, bv_unsigned sp)]%Z).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFS OFT OFR C2 CEIL LO. lia. }
  assert (DG1 : disjoint_from [(DsnP, DsnP + 8 * Z.of_nat (bn_dmax bsn)); (Dt, Dt + 8 * Z.of_nat (bn_dmax btm)); (Ddv, Ddv + 8 * Z.of_nat (bn_dmax bvv));
                               (bv_unsigned sp - 416, bv_unsigned sp)]%Z g_GOT_shadow_offset_cell 8).
  { cbn [disjoint_from]. unfold g_GOT_shadow_offset_cell, BnHeapA.ACEIL in *. clear - SnI TI VI C1 CEIL LO Sn0 T0 V0 OKn2 Etopn HnP LOOP1 HLt HLr HDN. lia. }
  assert (DG2 : disjoint_from [(DsnP, DsnP + 8 * Z.of_nat (bn_dmax bsn)); (Dt, Dt + 8 * Z.of_nat (bn_dmax btm)); (Ddv, Ddv + 8 * Z.of_nat (bn_dmax bvv));
                               (bv_unsigned sp - 416, bv_unsigned sp)]%Z g_shadow_memory_dynamic_address 8).
  { cbn [disjoint_from]. unfold g_shadow_memory_dynamic_address, BnHeapA.ACEIL in *. clear - SnI TI VI C1 CEIL LO Sn0 T0 V0 OKn2 Etopn HnP LOOP1 HLt HLr HDN. lia. }
  unfold bn_cells in BNt, BNsd, BNsn. unfold MallocRep.wz in BNt, BNsd, BNsn.
  pose proof (AH_range _ _ _ _ _ _ _ HEAPU Hinsn) as (PS0 & _). pose proof (AH_range _ _ _ _ _ _ _ HEAPU Hinpt) as (PT0 & _).
  pose proof (AH_range _ _ _ _ _ _ _ HEAPU Hinpsd) as (PD0 & _). pose proof (AH_range _ _ _ _ _ _ _ HEAPU Hinpv) as (PV0 & _).
  assert (DNZ : 0 < DsnP /\ 0 < Dt /\ 0 < Dsd /\ 0 < Ddv) by (clear - PS0 PT0 PD0 PV0; lia).
  assert (L0 : LINV sp d1 sdbuf dn loop nP DsnP Dt Dsd Ddv atmp asdiv lo (bn_dmax bsn) (bn_dmax btm) (bn_dmax bvv)
                 c0 (Z_to_bv 64 (Z.b2z negn)) (Z_to_bv 64 (shad (asnum + 8))) (Z_to_bv 64 (asnum + 8)) (Z_to_bv 64 sh) (Z_to_bv 64 ac) (Z_to_bv 64 arm)
                 (Z_to_bv 64 asnum) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra
                 (Z_to_bv 64 (Z.of_nat (bn_top btm))) (Z_to_bv 64 (Z.of_nat (bn_dmax btm))) (Z_to_bv 64 (Z.b2z (bn_neg btm))) (Z_to_bv 64 (bn_flags btm))
                 (Z_to_bv 64 (Z.of_nat (bn_top bsd))) (Z_to_bv 64 (Z.of_nat (bn_dmax bsd))) (Z_to_bv 64 (Z.b2z (bn_neg bsd))) (Z_to_bv 64 (bn_flags bsd))
                 mL 0%nat mL (bn_buf bsn) (bn_buf btm) (bn_buf bvv)).
  { unfold LINV, LINVf. rewrite !Nat.sub_0_r. replace (DsnP + 8 * Z.of_nat (nP - 1)) with (DsnP + 8 * Z.of_nat nP - 8) by (clear - HnP LOOP1; lia).
    split; [exact LAsn|]. split; [exact LAt|]. split; [exact LAv|]. split; [exact LAsd|].
    split; [exact WRsn|]. split; [exact WRt|]. split; [exact WRv|]. split; [exact BNt|]. split; [exact BNsd|].
    split; [exact FRU|]. split; [exact STU|]. split; [exact MIU|]. split; [apply munch_refl| apply wmono_refl]. }
  assert (DI0 : div_inv sdbuf dn loop nP (lval (firstn nP (bn_buf bsn))) (bn_dmax bsn) (bn_dmax btm) (bn_dmax bvv) 0 (bn_buf bsn, bn_buf btm, bn_buf bvv)).
  { unfold div_inv. rewrite !Nat.sub_0_r. split; [exact OKn1|]. split; [reflexivity|]. split; [exact OKt1|]. split; [reflexivity|].
    split; [exact OKv1|]. split; [reflexivity|]. split; [exact HTOPC|]. unfold slice at 1. rewrite firstn_O. cbn [lval]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity. }

  unfold div_tail_model. rewrite !bbind_get. fold bsn btm bvv.
  destruct (div_loop sdbuf dn loop nP d0 d1 loop 0 (bn_buf bsn, bn_buf btm, bn_buf bvv)) as [[snb tmb] rb] eqn:EDL0.
  apply implA_from_evt.
  eapply evt_eq; [| eapply (dl_loop sp gp (Z_to_bv 64 TP_A) F fc _ d0 d1 sdbuf dn loop nP DsnP Dt Dsd Ddv atmp asdiv lo
                                (bn_dmax bsn) (bn_dmax btm) (bn_dmax bvv) (lval (firstn nP (bn_buf bsn)))
                                c0 (Z_to_bv 64 (Z.b2z negn)) (Z_to_bv 64 (shad (asnum + 8))) (Z_to_bv 64 (asnum + 8)) (Z_to_bv 64 sh) (Z_to_bv 64 ac) (Z_to_bv 64 arm)
                                (Z_to_bv 64 asnum) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra _ _ _ _ _ _ _ _ mL
                                OKd1 HDN ltac:(rewrite Lsdb, <- Etopd; exact OKd2) HnP Hd0 Hd1 Hnorm
                                ltac:(rewrite <- Etopn; exact OKn2) HLt HLr ltac:(clear - OKn2 OKn3 Etopn; lia) DLB DLP DAL
                                ACS ACT ltac:(rewrite Lsdb; exact ACV) ACR ACTA ACVA SHB0 OFFWL DG1 DG2 ltac:(unfold SHHI, BnHeapA.ACEIL in *; clear - C2 CEIL; lia) DNZ
                                loop 0%nat mL (bn_buf bsn) (bn_buf btm) (bn_buf bvv)
                                x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 ltac:(clear; lia) L0 DI0) ].
  { rewrite !Nat.sub_0_r. reflexivity. }
  intros mm' snb' tmb' rb' y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y19 y23 y26 y27 y28 y29 y30 y31 EDL L1 DI1.
  rewrite EDL0 in EDL. injection EDL as Esnb Etmb Erb. subst snb' tmb' rb'.

  destruct L1 as (LAsn1 & LAt1 & LAv1 & _ & WRsn1 & WRt1 & WRv1 & TAc1 & _ & FR1 & ST1 & MI1 & MU1 & WM1).
  pose proof DI1 as (Hsnb & Lsnb & Htmb & Ltmb & Hrb & Lrb & _ & _).
  assert (DJW : forall A k, (A + k <= DsnP \/ DsnP + 8 * Z.of_nat (bn_dmax bsn) <= A) -> (A + k <= Dt \/ Dt + 8 * Z.of_nat (bn_dmax btm) <= A) ->
                  (A + k <= Ddv \/ Ddv + 8 * Z.of_nat (bn_dmax bvv) <= A) -> A + k <= bv_unsigned sp - 416 ->
                  disjoint_from [(DsnP, DsnP + 8 * Z.of_nat (bn_dmax bsn)); (Dt, Dt + 8 * Z.of_nat (bn_dmax btm)); (Ddv, Ddv + 8 * Z.of_nat (bn_dmax bvv));
                                 (bv_unsigned sp - 416, bv_unsigned sp)] A k).
  { intros A k H1 H2 H3 H4. cbn [disjoint_from]. clear - H1 H2 H3 H4. lia. }
  eapply (rw_cells_transport bgbsegs _ mL mm') in BNsn; [| exact MU1 | exact WM1 | apply DJW; cbn [cells_size csize Nat.add];
    [clear - DJs_sa; lia | clear - DJt_sa; lia | clear - DJv_sa; lia | unfold BnHeapA.ACEIL in *; clear - Rs2 SAC CEIL LO; lia] ].
  unfold bn_cells in BNdv. unfold MallocRep.wz in BNdv.
  eapply (rw_cells_transport bgbsegs _ mL mm') in BNdv; [| exact MU1 | exact WM1 | apply DJW; cbn [cells_size csize Nat.add];
    [clear - DJs_da; lia | clear - DJt_da; lia | clear - DJv_da; lia | unfold BnHeapA.ACEIL in *; clear - Rv2 DAC CEIL LO; lia] ].

  assert (MU2 : munch [(asnum, asnum + 24); (DsnP, DsnP + 8 * Z.of_nat (bn_dmax bsn)); (Dt, Dt + 8 * Z.of_nat (bn_dmax btm)); (Ddv, Ddv + 8 * Z.of_nat (bn_dmax bvv));
                       (bv_unsigned sp - 416, bv_unsigned sp)] mL mm').
  { eapply munch_weaken; [|exact MU1]. unfold sub_fp. intros xx Hxx. cbn [outside] in Hxx |- *. exact (proj2 Hxx). }
  assert (OFF2 : offshW [(asnum, asnum + 24); (DsnP, DsnP + 8 * Z.of_nat (bn_dmax bsn)); (Dt, Dt + 8 * Z.of_nat (bn_dmax btm)); (Ddv, Ddv + 8 * Z.of_nat (bn_dmax bvv));
                       (bv_unsigned sp - 416, bv_unsigned sp)]).
  { cbn [offshW]. cbn [offshW] in OFFWL. unfold SHLO, SHHI in *. clear - OFSA OFFWL. lia. }
  clear MU1 DJW.
  pose proof (munch_refl [(asnum, asnum + 24)]%Z mm') as MUa. pose proof (wmono_refl bgbsegs mm') as WMa.
  clear DLB DLP DAL L0 DI0 DI1 LAsn LAt LAv LAsd WRsn WRt WRv Usn Ut Uv Usd BNt BNsd FRU STU MIU HTOPC OFFWL DG1 DG2.
  clear DJst DJsd DJsv DJtd DJtv DJvd DJs_ta DJs_va DJt_ta DJt_va DJv_ta DJv_va DJs_da DJt_da DJv_da.
  assert (ASN : 0 < asnum /\ asnum + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - SA0 Rs1 Rs2 SAC CEIL LO SPR SPT; lia).

  apply hide_intro in OFSA.
  repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
  repeat match goal with H : _ <> _ |- _ => apply hide_intro in H end.
  apply hide_intro in TAc1. apply hide_intro in BNdv.
  step.
  do 3 zstep.
  shl_with ACSA ALSA.
  chk0.
  step.
  zstep.
  step.
  shl_with ACSA ALSA.
  step. step. step.
  chk0.
  step.
  zstep.
  zstep.
  step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
  apply hide_elim in TAc1. apply hide_elim in BNdv.
  apply hide_elim in DJ_ta_sa. apply hide_elim in DJ_da_sa. apply hide_elim in SAI.
  apply hide_elim in DJs_sa. apply hide_elim in DJt_sa. apply hide_elim in DJv_sa.
  eapply (rw_cells_transport bgbsegs _ mm' mF) in TAc1; [| exact MUa | exact WMa | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - DJ_ta_sa; lia| exact I]].
  eapply (rw_cells_transport bgbsegs _ mm' mF) in BNdv; [| exact MUa | exact WMa | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - DJ_da_sa; lia| exact I]].
  assert (Usn' : u64arr bgbsegs mF DsnP (wlimbs snb)).
  { apply limbarr_limbs_at. split.
    - eapply limbs_at_transport; [exact LAsn1 | exact MUa |]. cbn [disjoint_from]. rewrite Lsnb. split; [clear - DJs_sa; lia | exact I].
    - rewrite Lsnb. exact WRsn1. }
  assert (Ut' : u64arr bgbsegs mF Dt (wlimbs tmb)).
  { apply limbarr_limbs_at. split.
    - eapply limbs_at_transport; [exact LAt1 | exact MUa |]. cbn [disjoint_from]. rewrite Ltmb. split; [clear - DJt_sa; lia | exact I].
    - rewrite Ltmb. exact WRt1. }
  assert (Uv' : u64arr bgbsegs mF Ddv (wlimbs rb)).
  { apply limbarr_limbs_at. split.
    - eapply limbs_at_transport; [exact LAv1 | exact MUa |]. cbn [disjoint_from]. rewrite Lrb. split; [clear - DJv_sa; lia | exact I].
    - rewrite Lrb. exact WRv1. }
  match goal with FRx : rw_cells _ mF (bv_unsigned sp + -304) _, STx : stk _ mF _ _, MIx : mem_inv _ mF |- _ =>
    rename FRx into FRF; rename STx into STF; rename MIx into MIF end.
  clear LAsn1 LAt1 LAv1 WRsn1 WRt1 WRv1 MUa WMa DJ_ta_sa DJ_da_sa SAI DJs_sa DJt_sa DJv_sa.
  apply evt_done. cbv beta. rewrite !bbind_set.
  set (TM := bn_with_buf btm tmb). set (DVV := bn_with_buf bvv rb). set (SN := mkBN (bn_d bsn) snb dn negn (bn_flags bsn)).
  assert (WOK : Forall (w_ok OWU LB lsU PL EA (bv_unsigned sp) [tmp; res; snum])
                  [(asnum, asnum + 24); (DsnP, DsnP + 8 * Z.of_nat (bn_dmax bsn)); (Dt, Dt + 8 * Z.of_nat (bn_dmax btm)); (Ddv, Ddv + 8 * Z.of_nat (bn_dmax bvv));
                   (bv_unsigned sp - 416, bv_unsigned sp)]).
  { constructor; [eapply (w_struct OWU LB lsU PL EA (bv_unsigned sp) false [tmp; res; snum] _ snum asnum); [right; right; left; reflexivity| exact HAsnum| exact NROs| cbn; clear; lia| cbn; clear; lia]|].
    constructor; [eapply (w_limbs OWU LB lsU PL EA (bv_unsigned sp) false [tmp; res; snum] _ snum psn DsnP); [right; right; left; reflexivity| exact HVsn| exact Edsn| exact Hinsn| cbn [fst snd]; lia| cbn [fst snd]; fold bsn; lia]|].
    constructor; [eapply (w_limbs OWU LB lsU PL EA (bv_unsigned sp) false [tmp; res; snum] _ tmp pt Dt); [left; reflexivity| exact HVtm| exact Edt| exact Hinpt| cbn [fst snd]; lia| cbn [fst snd]; fold btm; lia]|].
    constructor; [eapply (w_limbs OWU LB lsU PL EA (bv_unsigned sp) false [tmp; res; snum] _ res pv Ddv); [right; left; reflexivity| exact HVdv| exact Edv| exact Hinpv| cbn [fst snd]; lia| cbn [fst snd]; fold bvv; lia]|].
    constructor; [apply w_stack; cbn [fst snd]; unfold BnHeapA.ACEIL in *; clear - CEIL LO; lia| constructor]. }
  assert (HWL : Forall (w_lib lsU OWU PL lo (bv_unsigned sp))
                  [(asnum, asnum + 24); (DsnP, DsnP + 8 * Z.of_nat (bn_dmax bsn)); (Dt, Dt + 8 * Z.of_nat (bn_dmax btm)); (Ddv, Ddv + 8 * Z.of_nat (bn_dmax bvv));
                   (bv_unsigned sp - 416, bv_unsigned sp)]).
  { constructor; [w_lib_ref HAsnum NROs|].
    constructor; [right; left; exists (psn, DsnP, 8 * Z.of_nat (bn_dmax bsn)); cbn; split; [exact Hinsn| lia]|].
    constructor; [right; left; exists (pt, Dt, 8 * Z.of_nat (bn_dmax btm)); cbn; split; [exact Hinpt| lia]|].
    constructor; [right; left; exists (pv, Ddv, 8 * Z.of_nat (bn_dmax bvv)); cbn; split; [exact Hinpv| lia]|].
    constructor; [left; cbn [fst snd]; clear - LO; lia| constructor]. }
  match goal with MUx : munch _ mL mF, WMx : wmono _ mL mF |- _ => rename MUx into MU2F; rename WMx into WM2F end.
  pose proof (lib_state_frame ΣU LB (bv_unsigned sp) USTACK_TOP [tmp; res; snum] lsU mL mF OWU PL EA _ HEAPU LSH3 MU2F WM2F FROK WOK) as LSF.
  assert (LSc1 : lib_state_h [res; snum] (setbn tmp TM lsU) mF OWU PL EA).
  { eapply (lib_state_close [res; snum] lsU mF OWU PL EA tmp atmp); [exact LSF | exact ND | exact HAtmp | exact NROt | | | ].
    - exists Dt. split.
      + unfold bn_cells, TM, bn_dmax, MallocRep.wz. cbn [bn_with_buf bn_top bn_buf bn_neg bn_flags]. rewrite Ltmb. exact TAc1.
      + unfold bn_arr, TM, bn_dmax. cbn [bn_with_buf bn_d bn_buf]. rewrite Edt, Ltmb. split; [exact Hinpt | exact Ut'].
    - apply hide_elim in OKt4. unfold bg_ok, TM, bn_dmax, BG_DMAX. cbn [bn_with_buf bn_top bn_buf bn_flags]. rewrite Ltmb.
      split; [exact Htmb|]. split; [exact OKt2|]. split; [exact OKt3| exact OKt4].
    - apply ids_ok_setbn_same; [exact IDS | exact HVtm |]. unfold bn_blocks, TM, bn_dmax. cbn [bn_with_buf bn_d bn_buf]. rewrite Ltmb. reflexivity. }
  set (lsa := setbn tmp TM lsU) in *.
  assert (HAdv_a : ref_at lsa OWU PL res adv) by (apply ref_at_setbn; exact HAdv).
  assert (HVdv_a : vref res lsa) by (apply vref_setbn; exact HVdv).
  assert (Gdv_a : getbn res lsa = bvv) by (unfold lsa; apply getbn_setbn_other; apply not_eq_sym; exact NEvt).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LSc1) as (_ & _ & IDSa & _).
  assert (LSc2 : lib_state_h [snum] (setbn res DVV lsa) mF OWU PL EA).
  { eapply (lib_state_close [snum] lsa mF OWU PL EA res adv); [exact LSc1 | exact ND | exact HAdv_a | exact NROv | | | ].
    - exists Ddv. split.
      + unfold bn_cells, DVV, bn_dmax, MallocRep.wz. cbn [bn_with_buf bn_top bn_buf bn_neg bn_flags]. rewrite Lrb. exact BNdv.
      + unfold bn_arr, DVV, bn_dmax. cbn [bn_with_buf bn_d bn_buf]. rewrite Edv, Lrb. split; [exact Hinpv | exact Uv'].
    - apply hide_elim in OKv4. unfold bg_ok, DVV, bn_dmax, BG_DMAX. cbn [bn_with_buf bn_top bn_buf bn_flags]. rewrite Lrb.
      split; [exact Hrb|]. split; [exact OKv2|]. split; [exact OKv3| exact OKv4].
    - apply ids_ok_setbn_same; [exact IDSa | exact HVdv_a |]. rewrite Gdv_a. unfold bn_blocks, DVV, bn_dmax. cbn [bn_with_buf bn_d bn_buf]. rewrite Lrb. reflexivity. }
  set (lsb := setbn res DVV lsa) in *.
  assert (HAsn_b : ref_at lsb OWU PL snum asnum) by (apply ref_at_setbn; apply ref_at_setbn; exact HAsnum).
  assert (HVsn_b : vref snum lsb) by (apply vref_setbn; apply vref_setbn; exact HVsn).
  assert (Gsn_b : getbn snum lsb = bsn).
  { unfold lsb. rewrite getbn_setbn_other by exact NEvs. unfold lsa. apply getbn_setbn_other. exact NEts. }
  pose proof (lib_state_h_parts _ _ _ _ _ _ LSc2) as (_ & _ & IDSb & _).
  assert (LSc3 : lib_state (setbn snum SN lsb) mF OWU PL EA).
  { unfold lib_state. eapply (lib_state_close [] lsb mF OWU PL EA snum asnum); [exact LSc2 | exact ND | exact HAsn_b | exact NROs | | | ].
    - exists DsnP. split.
      + unfold bn_cells, SN, bn_dmax, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lsnb. exact BNsn.
      + unfold bn_arr, SN, bn_dmax. cbn [bn_d bn_buf]. rewrite Edsn, Lsnb. split; [exact Hinsn | exact Usn'].
    - apply hide_elim in OKn4. unfold bg_ok, SN, bn_dmax, BG_DMAX. cbn [bn_top bn_buf bn_flags]. rewrite Lsnb.
      split; [exact Hsnb|]. split; [clear - OKn2 Etopn HnP; lia|]. split; [exact OKn3| exact OKn4].
    - apply ids_ok_setbn_same; [exact IDSb | exact HVsn_b |]. rewrite Gsn_b. unfold bn_blocks, SN, bn_dmax. cbn [bn_d bn_buf]. rewrite Lsnb. reflexivity. }
  set (lsc := setbn snum SN lsb) in *.
  assert (ENVc : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) TOTAL Σ ls OW m
                   (div_pre c0 negn asnum sh ac arm d1 dn loop asdiv (DsnP + 8 * Z.of_nat (nP - 1 - loop)) (Z.of_nat loop) (DsnP + 8 * Z.of_nat (loop - loop)) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used ΣU lsc mF OWU).
  { unfold lsc. apply cenv_setbnA; [| exact HVsn_b | rewrite Gsn_b; unfold bn_blocks, SN; cbn [bn_d bn_buf bn_dmax bn_top]; rewrite ?Edsn; reflexivity].
    unfold lsb. apply cenv_setbnA; [| exact HVdv_a | rewrite Gdv_a; unfold bn_blocks, DVV; cbn [bn_with_buf bn_d bn_buf bn_dmax bn_top]; rewrite ?Edv; reflexivity].
    unfold lsa. apply cenv_setbnA; [| exact HVtm | fold btm; unfold bn_blocks, TM; cbn [bn_with_buf bn_d bn_buf bn_dmax bn_top]; rewrite ?Edt; reflexivity].
    eapply (cenv_silentA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) TOTAL Σ ls OW m);
      [exact ENVU | exact LSU | exact MU2F | exact WM2F | exact HWL | exact STF | exact MIF | unfold div_pre; cbn [app]; exact FRF | cbn; lia]. }
  assert (HArm_c : oref_at lsc OWU PL rm arm) by (do 3 apply oref_at_setbn; exact HArm).
  assert (HAsn_c : ref_at lsc OWU PL snum asnum) by (apply ref_at_setbn; exact HAsn_b).
  clear LSF LSc1 LSc2 LSH1 LSH2 LSH3 WOK HWL TAc1 BNdv BNsn Usn' Ut' Uv'.
  destruct rm as [r|].
  -
    cbn [oref_at] in HArm_c. pose proof (HPrm r eq_refl) as HPr.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LSc3) as PARTSc.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVc)) PARTSc HArm_c HPr) as (RA0 & RAC & _ & _).
    assert (ARM : 0 < arm < 18446744073709551616) by (unfold BnHeapA.ACEIL in *; clear - RA0 RAC CEIL LO SPR; lia).
    apply implA_from_evt.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (clear - ARM; lia). clear - KZ ARM. lia. }
    clear KZ.
    step.
    apply evt_done.
    unfold bbind at 1. cbn [bind tree_ops].
    eapply implA_bind.
    { eapply (bn_rshift_fixed_top_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OWU) (LB := LB) (PL := PL) (EA := EA) (rr := r) (rx := snum) (ar := arm) (ax := asnum) (n := sh);
        [ | | | reflexivity | exact HArm_c | exact HPr | exact HAsn_c | exact NROs | solve_nbuf | reflexivity | reflexivity | reflexivity | clear - Hsh; lia].
      - eapply cenv_preA; [exact ENVc | exact LSc3 | unfold BN_RSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - USED; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENVc).
      - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_rshift CTX). }
    cbv beta. intros [uS lsS] ΣS msS PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) TOTAL Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENVc))].
    cbn [fst snd] in *.
    destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & F2 & fc2 & mS & OWS & PLS & -> & CPS & (EPLS & -> & _)).
    subst PLS. specialize (CPS eq_refl).
    destruct (cenv_postA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ENVc CPS) as (ENVS & LSS).
    rewrite (ret_pc_even 0x2354b0) by lia. unfold MallocRep.wz.
    clear CPS.
    apply implA_from_evt.
    zstep. if_cases KZ; zify_cond KZ. 2:{ exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ. lia. }
    clear KZ.
    apply evt_done.
    eapply FIN; [exact ENVS | exact LSS | clear - USED; lia].
  -
    cbn [oref_at] in HArm_c. subst arm.
    rewrite bbind_ret.
    apply implA_from_evt.
    zstep. if_cases KZ; zify_cond KZ. 2:{ exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ. lia. }
    clear KZ.
    apply evt_done.
    eapply FIN; [exact ENVc | exact LSc3 | clear - USED; unfold MC in *; lia].
Qed.

End WithRT.
