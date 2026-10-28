(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnDivWords BnDivLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_num_bits_word.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr DivLoopPure.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnP Require Import DivLA DivBody DivLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap DivLA DivBody DivLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves W_expand W_ctx BnCall BnRKit W_lshift W_rshift W_ctx_end.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnR Require Import DivModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition oref_at (bs : bstate bptr) (OW : list block) (PL : placement) (o : option bnref) (a : Z) : Prop :=
  match o with Some r => ref_at bs OW PL r a | None => a = 0 end.

Lemma oref_at_stable : forall st OW st' OW' PL o a, refs_stable st OW st' OW' -> oref_at st OW PL o a -> oref_at st' OW' PL o a.
Proof. intros st OW st' OW' PL [r|] a RS H; [exact (ref_at_stable _ _ _ _ _ _ _ RS H)| exact H]. Qed.

Lemma oref_at_setbn : forall st OW PL r b o a, oref_at st OW PL o a -> oref_at (setbn r b st) OW PL o a.
Proof. intros st OW PL r b [r'|] a H; [apply ref_at_setbn; exact H| exact H]. Qed.

Definition div_tail_model (tmp snum res : bnref) (rm : option bnref) (sdbuf : list Z) (dn loop nP : nat) (d0 d1 : Z) (negn : bool) (sh : Z)
    : bstate bptr -> btree bptr (unit * bstate bptr) :=
  bbind (tree_ops bptr) (bget (tree_ops bptr) snum) (fun sn =>
  bbind (tree_ops bptr) (bget (tree_ops bptr) tmp) (fun tm =>
  bbind (tree_ops bptr) (bget (tree_ops bptr) res) (fun r =>
    let '(snb, tmb, rb) := div_loop sdbuf dn loop nP d0 d1 loop 0 (bn_buf sn, bn_buf tm, bn_buf r) in
    bbind (tree_ops bptr) (bset (tree_ops bptr) tmp (bn_with_buf tm tmb)) (fun _ =>
    bbind (tree_ops bptr) (bset (tree_ops bptr) res (bn_with_buf r rb)) (fun _ =>
    bbind (tree_ops bptr) (bset (tree_ops bptr) snum (mkBN (bn_d sn) snb dn negn (bn_flags sn))) (fun _ =>
    bbind (tree_ops bptr) (match rm with Some r => bn_rshift_fixed_top (tree_ops bptr) r snum sh | None => bret (tree_ops bptr) tt end) (fun _ =>
    BN_CTX_end (tree_ops bptr)))))))).

Lemma bbind_get : forall {B} r (f : bignum bptr -> BM (M := btree bptr) B) (bs : bstate bptr),
  bbind (tree_ops bptr) (bget (tree_ops bptr) r) f bs = f (getbn r bs) bs.
Proof. reflexivity. Qed.

Lemma bbind_set : forall {B} r b (f : unit -> BM (M := btree bptr) B) (bs : bstate bptr),
  bbind (tree_ops bptr) (bset (tree_ops bptr) r b) f bs = f tt (setbn r b bs).
Proof. reflexivity. Qed.

Lemma bbind_ret : forall {A B} (a : A) (f : A -> BM (M := btree bptr) B) (bs : bstate bptr),
  bbind (tree_ops bptr) (bret (tree_ops bptr) a) f bs = f a bs.
Proof. reflexivity. Qed.

Lemma vref_setbn : forall r r' b (bs : bstate bptr), vref r bs -> vref r (setbn r' b bs).
Proof. intros r r' b bs H. unfold vref in *. rewrite length_setbn. exact H. Qed.

Ltac env_open ENV :=
  let E := fresh "ENVo" in
  let HEAPe := fresh "HEAPe" in let STe := fresh "STe" in let errve := fresh "errve" in let ERRe := fresh "ERRe" in
  let MIe := fresh "MIe" in let FRe := fresh "FRe" in let FSZe := fresh "FSZe" in let MUe := fresh "MUe" in let WMe := fresh "WMe" in
  pose proof ENV as E;
  destruct E as (HEAPe & _ & STe & (errve & ERRe) & MIe & _ & _ & _ & _ & FRe & FSZe);
  unfold LX_ERRNO, RATP in ERRe; change (3346328 - 164) with 3346164 in ERRe;
  lazymatch type of MIe with mem_inv _ ?mm =>
    lazymatch type of STe with stk _ _ _ ?fb =>
      lazymatch type of FSZe with _ = (?spv - _) =>
        pose proof (munch_refl [(fb, spv)]%Z mm) as MUe; pose proof (wmono_refl bgusegs mm) as WMe
      end
    end
  end;
  clear FSZe.

Ltac env_close CSIL HWLs WOKs ENV LS ENVn LSn :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of LS with lib_state ?lsx ?m0x ?OWx ?ADx ?EAx =>
      match goal with
      | FRx : rw_cells _ mx ?fb ?fr', STx : stk _ mx _ ?fb, MIx : mem_inv _ mx, MUx : munch _ m0x mx, WMx : wmono _ m0x mx,
        ERRx : rw_cells _ mx 3346164 _, HEAPx : RHEAP ?stx _ m0x |- _ =>
          assert (ENVn : cenv _ ADx _ _ _ _ _ _ _ _ fr' stx lsx mx OWx)
            by (eapply (CSIL _ fr'); [exact ENV | exact LS | exact MUx | exact WMx | apply HWLs | exact STx | unfold LX_ERRNO, RATP; exact ERRx | exact MIx | exact FRx | cbn; lia]);
          pose proof (lib_state_frame stx _ _ _ [] lsx m0x mx OWx ADx EAx _ HEAPx LS MUx WMx ltac:(eassumption) (WOKs _ _) : lib_state lsx mx OWx ADx EAx) as LSn;
          clear FRx STx MIx MUx WMx ERRx HEAPx
      end
    end
  end.

Definition TFRAME (jb0 : list byte) (negn : bool) (sh arm d1 actx : Z) (dn : nat) (asnum : Z) (loop : nat) (asdiv wt : Z)
    (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 jb0; C8 (Z_to_bv 64 (Z.b2z negn)); C8 (Z_to_bv 64 sh); C8 (Z_to_bv 64 arm);
   C8 (Z_to_bv 64 (d1 mod 4294967296)); C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 (Z.shiftr d1 32));
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 actx); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (8 * Z.of_nat dn)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 (Z.of_nat dn + 1)); C8 (Z_to_bv 64 asnum); C8 (Z_to_bv 64 (Z.of_nat loop)); C8 (Z_to_bv 64 asdiv); C8 (Z_to_bv 64 wt);
   C8 (Z_to_bv 64 (Z.of_nat dn));
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma div_tail : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (res tmp snum sdiv : bnref) (rm : option bnref) (adv arm atmp asnum asdiv ac : Z) (qc : bptr)
      (stU : PState) (lsU : bstate bptr) (mL : mem) (OWU : list block)
      (sdbuf : list Z) (dn loop nP : nat) (d0 d1 sh : Z) (negn : bool) (psn pv : bptr) (DsnP Ddv : Z) (jb0 : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x27 x28 x29 x30 x31 : word),
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp + -256 - 16384 -> bv_unsigned sp <= B ->
    frames_ok PL (bv_unsigned sp) B -> pl_ctx PL = Some (ac, qc) ->
    cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m
      (TFRAME jb0 negn sh arm d1 ac dn asnum loop asdiv (DsnP + 8 * Z.of_nat (nP - 1)) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      stU lsU mL OWU ->
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
    implM bgusegs (interp (embed (div_tail_model tmp snum res rm sdbuf dn loop nP d0 d1 negn sh lsU))) stU
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 (Ddv + 8 * Z.of_nat loop))
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 d1) x19 (Z_to_bv 64 atmp) (Z_to_bv 64 0) (Z_to_bv 64 0) x23
               (Z_to_bv 64 (8 * Z.of_nat dn)) (Z_to_bv 64 (DsnP + 8 * Z.of_nat loop)) (Z_to_bv 64 d0) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x109c0c) fc None mL (seg_rom bgusegs)).
  Proof.
    intros until x31.
    intros CEIL GLO' LO SPB FROK EC ENVU LSU HAdv HArm HAtmp HAsnum HAsdiv WRFv HPrm HPt HPs HPd NEts NEtd NEsd NEvt NEvs NEvd
           Esdb Etopd HDN Hd0 Hd1 Hnorm Etopn HnP LOOP1 Edsn Hinsn HTOPC Edv Hinpv Etopv HLr HLt Hsh.
    pose proof (proj1 WRFv) as NROv. pose proof (proj1 HPt) as NROt. pose proof (proj1 HPs) as NROs. pose proof (proj1 HPd) as NROd.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -256) by lia.
    assert (FBsp : bv_unsigned sp + -256 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m CEIL GLO' FBlo FBsp SPB SPR2 FROK) as CPRE.
    pose proof (cenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m CEIL GLO' FBlo FBsp FROK) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) CEIL FBlo FBsp SPR2 A) as BPC.
    pose proof (cenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m CEIL GLO' FBlo FBsp SPB FROK) as CSIL.
    assert (HWLs : forall bsx OWx, Forall (w_lib bsx OWx PL lo (bv_unsigned sp)) [(bv_unsigned sp + -256, bv_unsigned sp)]) by (intros bsx OWx; constructor; [left; cbn; lia| constructor]).
    assert (WOKs : forall OWx lsx, Forall (w_ok OWx LB lsx PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -256, bv_unsigned sp)]) by (intros OWx lsx; constructor; [apply w_stack; cbn; lia| constructor]).

    assert (FIN : forall stS lsS mS OWS y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31,
               cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m
                 (TFRAME jb0 negn sh arm d1 ac dn asnum loop asdiv (DsnP + 8 * Z.of_nat (nP - 1 - loop)) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) stS lsS mS OWS ->
               lib_state lsS mS OWS PL EA ->
               implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr) lsS))) stS
                 (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
                 (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp (Z_to_bv 64 RATP) y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
                          (Z_to_bv 64 1) y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                     F (Z_to_bv 64 1089184) fc None mS (seg_rom bgusegs))).
    { intros stS lsS mS OWS y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 ENVS LSS.
      clear ENVU LSU HAdv HArm HAtmp HAsnum HAsdiv Esdb Etopd Etopn Edsn Hinsn HTOPC Edv Hinpv Etopv HLr HLt.
      env_open ENVS. unfold TFRAME in FRe. unfold MallocRep.wz. unfold implM. iprefix.
      step. zstep.
      env_close CSIL HWLs WOKs ENVS LSS ENVS' LSS'.
      destruct (CPRE _ _ _ _ _ BN_CTX_END_STACK ENVS' LSS' ltac:(unfold BN_CTX_END_STACK; clear - LO; lia)) as (errvE & PREE).
      ihere. to_implM.
      eapply implM_post_evt.
      { eapply BN_CTX_end_walk with (lo := lo) (B := B) (errv := errvE) (OW := OWS) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc);
          [exact PREE | reflexivity | exact EC | reflexivity]. }
      cbv beta. intros [uE lsE] stE msE PO. apply BPC in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mE & OWE & PLE & -> & CPE & (EPLE & _)).
      subst PLE. specialize (CPE eq_refl).
      destruct (CPOST _ _ _ _ _ _ _ _ _ ENVS' CPE) as (ENVE & LSE).
      cbn [fst snd] in *.
      replace (ret_pc (Z_to_bv 64 1089192)) with (Z_to_bv 64 1089192) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear PREE CPE.
      pose proof (cenv_final LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m _ _ _ _ _ ENVE LSE)
        as (F1 & F2 & F3 & (errvF & F4) & F5 & F6 & F7 & F8 & F9).
      env_open ENVE. unfold TFRAME in FRe. unfold MallocRep.wz.
      zstep. do 13 step.
      release_frame FRe STe (bv_unsigned sp). step. step.
      apply evt_done. unfold bn_post. do 15 eexists. exists mE, OWE, PL, errvF. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact STe|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity. }

    pose proof (RH_nodup_l _ _ _ _ (proj1 ENVU)) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LSU) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSU HAsnum) as HVsn. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSU HAdv) as HVdv.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSU HAtmp) as HVtm. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSU HAsdiv) as HVsd.
    destruct (lib_state_open [] lsU mL OWU PL EA sdiv asdiv LSU ND HAsdiv ltac:(intros []) NROd) as ((Dsd & BNsd & ARRsd) & (OKd1 & OKd2 & OKd3 & OKd4) & _).
    destruct (lib_state_open [] lsU mL OWU PL EA snum asnum LSU ND HAsnum ltac:(intros []) NROs) as ((Dsn & BNsn & ARRsn) & (OKn1 & OKn2 & OKn3 & OKn4) & LSH1).
    destruct (lib_state_open [snum] lsU mL OWU PL EA res adv LSH1 ND HAdv ltac:(intros [E|[]]; apply NEvs; symmetry; exact E) NROv) as ((Dv & BNdv & ARRdv) & (OKv1 & OKv2 & OKv3 & OKv4) & LSH2).
    destruct (lib_state_open [res; snum] lsU mL OWU PL EA tmp atmp LSH2 ND HAtmp ltac:(intros [E|[E|[]]]; [apply NEvt; exact E| apply NEts; symmetry; exact E]) NROt)
      as ((Dt & BNt & ARRt) & (OKt1 & OKt2 & OKt3 & OKt4) & LSH3).
    set (bsn := getbn snum lsU) in *. set (bvv := getbn res lsU) in *. set (btm := getbn tmp lsU) in *. set (bsd := getbn sdiv lsU) in *.

    assert (EDsn : Dsn = DsnP).
    { unfold bn_arr in ARRsn. rewrite Edsn in ARRsn. exact (proj1 (RH_addr_unique OWU psn Dsn _ DsnP _ ND (proj1 ARRsn) Hinsn)). }
    subst Dsn.
    assert (EDv : Dv = Ddv).
    { unfold bn_arr in ARRdv. rewrite Edv in ARRdv. exact (proj1 (RH_addr_unique OWU pv Dv _ Ddv _ ND (proj1 ARRdv) Hinpv)). }
    subst Dv.
    assert (HDT : exists pt, bn_d btm = Some pt /\ In (pt, Dt, 8 * Z.of_nat (bn_dmax btm)) OWU).
    { destruct (bn_d btm) as [pt|] eqn:Edt0; [exists pt; split; [reflexivity|]; unfold bn_arr in ARRt; rewrite Edt0 in ARRt; exact (proj1 ARRt)|].
      exfalso. destruct (bn_arr_null PL tmp mL OWU Dt btm PWF (hpl_wref PL tmp HPt) Edt0 ARRt) as [_ E]. unfold bn_dmax in HLt. rewrite E in HLt. cbn in HLt. lia. }
    destruct HDT as (pt & Edt & Hinpt).
    assert (HDS : exists psd, bn_d bsd = Some psd /\ In (psd, Dsd, 8 * Z.of_nat (bn_dmax bsd)) OWU).
    { destruct (bn_d bsd) as [psd|] eqn:Edsd0; [exists psd; split; [reflexivity|]; unfold bn_arr in ARRsd; rewrite Edsd0 in ARRsd; exact (proj1 ARRsd)|].
      exfalso. destruct (bn_arr_null PL sdiv mL OWU Dsd bsd PWF (hpl_wref PL sdiv HPd) Edsd0 ARRsd) as [_ E]. unfold bn_dmax in OKd2. rewrite E in OKd2. cbn in OKd2. lia. }
    destruct HDS as (psd & Edsd & Hinpsd).
    destruct (bn_arr_facts_w lsU OWU PL EA (bv_unsigned sp) B stU LB mL snum DsnP (proj1 ENVU) PARTS FROK HVsn (hpl_wref PL snum HPs) ARRsn) as (Usn & _ & Sn0 & SnC & SnI & SEPsn). fold bsn in Usn, SnC, SnI, SEPsn.
    destruct (bn_arr_facts_w lsU OWU PL EA (bv_unsigned sp) B stU LB mL res Ddv (proj1 ENVU) PARTS FROK HVdv WRFv ARRdv) as (Uv & _ & V0 & VC & VI & SEPv). fold bvv in Uv, VC, VI, SEPv.
    destruct (bn_arr_facts_w lsU OWU PL EA (bv_unsigned sp) B stU LB mL tmp Dt (proj1 ENVU) PARTS FROK HVtm (hpl_wref PL tmp HPt) ARRt) as (Ut & _ & T0 & TC & TI & SEPt). fold btm in Ut, TC, TI, SEPt.
    destruct (bn_arr_facts_w lsU OWU PL EA (bv_unsigned sp) B stU LB mL sdiv Dsd (proj1 ENVU) PARTS FROK HVsd (hpl_wref PL sdiv HPd) ARRsd) as (Usd & _ & D0 & DC & _ & SEPd). fold bsd in Usd, DC, SEPd.
    pose proof (limbs_limbs_disj stU OWU LB mL (proj1 ENVU) lsU PL EA PARTS snum tmp _ _ _ _ _ _ (not_eq_sym NEts) HVsn HVtm Edsn Edt Hinsn Hinpt) as DJst.
    pose proof (limbs_limbs_disj stU OWU LB mL (proj1 ENVU) lsU PL EA PARTS snum sdiv _ _ _ _ _ _ NEsd HVsn HVsd Edsn Edsd Hinsn Hinpsd) as DJsd.
    pose proof (limbs_limbs_disj stU OWU LB mL (proj1 ENVU) lsU PL EA PARTS snum res _ _ _ _ _ _ (not_eq_sym NEvs) HVsn HVdv Edsn Edv Hinsn Hinpv) as DJsv.
    pose proof (limbs_limbs_disj stU OWU LB mL (proj1 ENVU) lsU PL EA PARTS tmp sdiv _ _ _ _ _ _ NEtd HVtm HVsd Edt Edsd Hinpt Hinpsd) as DJtd.
    pose proof (limbs_limbs_disj stU OWU LB mL (proj1 ENVU) lsU PL EA PARTS tmp res _ _ _ _ _ _ (not_eq_sym NEvt) HVtm HVdv Edt Edv Hinpt Hinpv) as DJtv.
    pose proof (limbs_limbs_disj stU OWU LB mL (proj1 ENVU) lsU PL EA PARTS res sdiv _ _ _ _ _ _ NEvd HVdv HVsd Edv Edsd Hinpv Hinpsd) as DJvd.
    pose proof (SEPsn tmp atmp HAtmp) as DJs_ta. pose proof (SEPsn sdiv asdiv HAsdiv) as DJs_va. pose proof (SEPsn snum asnum HAsnum) as DJs_sa.
    pose proof (SEPt tmp atmp HAtmp) as DJt_ta. pose proof (SEPt sdiv asdiv HAsdiv) as DJt_va. pose proof (SEPt snum asnum HAsnum) as DJt_sa.
    pose proof (SEPv tmp atmp HAtmp) as DJv_ta. pose proof (SEPv sdiv asdiv HAsdiv) as DJv_va. pose proof (SEPv snum asnum HAsnum) as DJv_sa.
    pose proof (SEPsn res adv HAdv) as DJs_da. pose proof (SEPt res adv HAdv) as DJt_da. pose proof (SEPv res adv HAdv) as DJv_da.
    pose proof (struct_disj stU OWU LB mL (proj1 ENVU) lsU PL EA (bv_unsigned sp) B PARTS FROK tmp snum atmp asnum NEts HAtmp HAsnum) as DJ_ta_sa.
    pose proof (struct_disj stU OWU LB mL (proj1 ENVU) lsU PL EA (bv_unsigned sp) B PARTS FROK res snum adv asnum NEvs HAdv HAsnum) as DJ_da_sa.
    clear SEPsn SEPt SEPv SEPd.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENVU) PARTS HAtmp HPt) as (TA0 & TAC & _ & (qt & At & nt & Hint & Rt1 & Rt2)).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENVU) PARTS HAsdiv HPd) as (VA0 & VAC & _ & (qd & Ad & nd & Hind & Rd1 & Rd2)).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENVU) PARTS HAsnum HPs) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Rs1 & Rs2)).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ (proj1 ENVU) PARTS FROK HAdv NROv) as (DA0 & DAC & DAI).

    destruct ENVU as (HEAPU & AUXU & STU & (errvU & ERRU) & MIU & LXPU & FAU & SOU & RSU & FRU & FSZU).
    assert (ENVU : cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m
      (TFRAME jb0 negn sh arm d1 ac dn asnum loop asdiv (DsnP + 8 * Z.of_nat (nP - 1)) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) stU lsU mL OWU).
    { unfold cenv. repeat (split; [first [assumption | exists errvU; assumption]|]). assumption. }
    unfold BG_DMAX in OKn3, OKv3, OKt3, OKd3.
    destruct (proj1 (limbarr_limbs_at bgusegs mL DsnP (bn_buf bsn)) Usn) as (LAsn & WRsn).
    destruct (proj1 (limbarr_limbs_at bgusegs mL Dt (bn_buf btm)) Ut) as (LAt & WRt).
    destruct (proj1 (limbarr_limbs_at bgusegs mL Ddv (bn_buf bvv)) Uv) as (LAv & WRv).
    destruct (proj1 (limbarr_limbs_at bgusegs mL Dsd (bn_buf bsd)) Usd) as (LAsd & _).
    rewrite Esdb in LAsd, OKd1.
    assert (Lsdb : length sdbuf = bn_dmax bsd) by (rewrite <- Esdb; reflexivity).
    assert (DLB : udl_bnd DsnP Dt Dsd Ddv atmp asdiv lo (bv_unsigned sp) (bn_dmax bsn) (bn_dmax btm) (length sdbuf) (bn_dmax bvv)).
    { unfold udl_bnd. rewrite Lsdb. clear - Sn0 SnC T0 TC D0 DC V0 VC TA0 TAC VA0 VAC CEIL LO SPR. lia. }
    assert (DLP : dl_pair DsnP Dt Dsd Ddv atmp asdiv (bn_dmax bsn) (bn_dmax btm) (length sdbuf) (bn_dmax bvv)).
    { unfold dl_pair, dj. rewrite Lsdb.
      split; [clear - DJst; lia|]. split; [clear - DJsd; lia|]. split; [clear - DJsv; lia|]. split; [clear - DJs_ta; lia|]. split; [clear - DJs_va; lia|].
      split; [clear - DJtd; lia|]. split; [clear - DJtv; lia|]. split; [clear - DJt_ta; lia|]. split; [clear - DJt_va; lia|].
      split; [clear - DJvd; lia|]. split; [clear - DJv_ta; lia|]. clear - DJv_va; lia. }
    assert (UAL : ualign DsnP Dt Dsd Ddv atmp).
    { pose proof (block_ualign _ _ _ _ _ _ _ HEAPU Hinsn) as (P1 & Q1). pose proof (block_ualign _ _ _ _ _ _ _ HEAPU Hinpt) as (P2 & Q2).
      pose proof (block_ualign _ _ _ _ _ _ _ HEAPU Hinpsd) as (P3 & Q3). pose proof (block_ualign _ _ _ _ _ _ _ HEAPU Hinpv) as (P4 & Q4).
      pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAPU PARTS HAtmp NROt) as (P5 & Q5). unfold ualign. clear - P1 P2 P3 P4 P5 Q1 Q2 Q3 Q4 Q5. tauto. }
    unfold bn_cells in BNt, BNsd, BNsn. unfold MallocRep.wz in BNt, BNsd, BNsn.
    assert (L0 : ULINV sp d1 sdbuf dn loop DsnP Dt Dsd Ddv atmp asdiv lo (bn_dmax bsn) (bn_dmax btm) (bn_dmax bvv)
                   jb0 (Z_to_bv 64 (Z.b2z negn)) (Z_to_bv 64 sh) (Z_to_bv 64 arm) (Z_to_bv 64 ac) (Z_to_bv 64 asnum)
                   s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra
                   (Z_to_bv 64 (Z.of_nat (bn_top btm))) (Z_to_bv 64 (Z.of_nat (bn_dmax btm))) (Z_to_bv 64 (Z.b2z (bn_neg btm))) (Z_to_bv 64 (bn_flags btm))
                   (Z_to_bv 64 (Z.of_nat (bn_top bsd))) (Z_to_bv 64 (Z.of_nat (bn_dmax bsd))) (Z_to_bv 64 (Z.b2z (bn_neg bsd))) (Z_to_bv 64 (bn_flags bsd))
                   mL (DsnP + 8 * Z.of_nat (nP - 1 - 0)) mL (bn_buf bsn) (bn_buf btm) (bn_buf bvv)).
    { unfold ULINV. split; [exact LAsn|]. split; [exact LAt|]. split; [exact LAv|]. split; [exact LAsd|].
      split; [exact WRsn|]. split; [exact WRt|]. split; [exact WRv|]. split; [exact BNt|]. split; [exact BNsd|].
      split; [rewrite Nat.sub_0_r; exact FRU|]. split; [exact STU|]. split; [exact MIU|]. split; [apply munch_refl| apply wmono_refl]. }
    assert (DI0 : div_inv sdbuf dn loop nP (lval (firstn nP (bn_buf bsn))) (bn_dmax bsn) (bn_dmax btm) (bn_dmax bvv) 0 (bn_buf bsn, bn_buf btm, bn_buf bvv)).
    { unfold div_inv. rewrite !Nat.sub_0_r. split; [exact OKn1|]. split; [reflexivity|]. split; [exact OKt1|]. split; [reflexivity|].
      split; [exact OKv1|]. split; [reflexivity|]. split; [exact HTOPC|]. unfold slice at 1. rewrite firstn_O. cbn [lval]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity. }

    unfold div_tail_model. rewrite !bbind_get. fold bsn btm bvv.
    unfold implM. iprefix.
    eapply evt_eq; [| eapply (udl_loop sp gp (Z_to_bv 64 RATP) F fc _ d0 d1 sdbuf dn loop nP DsnP Dt Dsd Ddv atmp asdiv lo
                                  (bn_dmax bsn) (bn_dmax btm) (bn_dmax bvv) (lval (firstn nP (bn_buf bsn)))
                                  jb0 (Z_to_bv 64 (Z.b2z negn)) (Z_to_bv 64 sh) (Z_to_bv 64 arm) (Z_to_bv 64 ac) (Z_to_bv 64 asnum)
                                  s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra _ _ _ _ _ _ _ _ mL
                                  OKd1 HDN ltac:(rewrite Lsdb, <- Etopd; exact OKd2) HnP Hd0 Hd1 Hnorm
                                  ltac:(rewrite <- Etopn; exact OKn2) HLt HLr ltac:(clear - OKn2 OKn3 Etopn; lia) DLB DLP UAL
                                  loop 0%nat mL (bn_buf bsn) (bn_buf btm) (bn_buf bvv)
                                  x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x27 x28 x29 x30 x31 ltac:(clear; lia) L0 DI0) ].
    { rewrite !Nat.sub_0_r. reflexivity. }
    intros mm' snb tmb rb y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y23 y25 y27 y28 y29 y30 y31 EDL L1 DI1.
    rewrite <- EDL.

    destruct L1 as (LAsn1 & LAt1 & LAv1 & _ & WRsn1 & WRt1 & WRv1 & TAc1 & _ & FR1 & ST1 & MI1 & MU1 & WM1).
    pose proof DI1 as (Hsnb & Lsnb & Htmb & Ltmb & Hrb & Lrb & _ & _).
    assert (DJW : forall A k, (A + k <= DsnP \/ DsnP + 8 * Z.of_nat (bn_dmax bsn) <= A) -> (A + k <= Dt \/ Dt + 8 * Z.of_nat (bn_dmax btm) <= A) ->
                    (A + k <= Ddv \/ Ddv + 8 * Z.of_nat (bn_dmax bvv) <= A) -> (A + k <= bv_unsigned sp - 352 \/ bv_unsigned sp <= A) ->
                    disjoint_from [(DsnP, DsnP + 8 * Z.of_nat (bn_dmax bsn)); (Dt, Dt + 8 * Z.of_nat (bn_dmax btm)); (Ddv, Ddv + 8 * Z.of_nat (bn_dmax bvv));
                                   (bv_unsigned sp - 352, bv_unsigned sp)] A k).
    { intros A k H1 H2 H3 H4. cbn [disjoint_from]. clear - H1 H2 H3 H4. lia. }
    eapply (rw_cells_transport bgusegs _ mL mm') in BNsn; [| exact MU1 | exact WM1 | apply DJW; cbn [cells_size csize Nat.add];
      [clear - DJs_sa; lia | clear - DJt_sa; lia | clear - DJv_sa; lia | clear - Rs2 SAC CEIL LO; lia] ].
    unfold bn_cells in BNdv. unfold MallocRep.wz in BNdv.
    eapply (rw_cells_transport bgusegs _ mL mm') in BNdv; [| exact MU1 | exact WM1 | apply DJW; cbn [cells_size csize Nat.add];
      [clear - DJs_da; lia | clear - DJt_da; lia | clear - DJv_da; lia | clear - DAC CEIL LO; lia] ].
    unfold LX_ERRNO, RATP in ERRU. change (3346328 - 164) with 3346164 in ERRU.
    eapply (rw_cells_transport bgusegs _ mL mm') in ERRU; [| exact MU1 | exact WM1 | apply DJW; cbn [cells_size csize Nat.add];
      [clear - SnI OKn2 Etopn HnP LOOP1; lia | clear - TI HLt; lia | clear - VI HLr LOOP1; lia | clear - GLO' LO; unfold GLOBALS_TOP in GLO'; lia] ].
    assert (MU2 : munch [(asnum, asnum + 24); (DsnP, DsnP + 8 * Z.of_nat (bn_dmax bsn)); (Dt, Dt + 8 * Z.of_nat (bn_dmax btm)); (Ddv, Ddv + 8 * Z.of_nat (bn_dmax bvv));
                         (bv_unsigned sp - 352, bv_unsigned sp)] mL mm').
    { eapply munch_weaken; [|exact MU1]. unfold sub_fp. intros xx Hxx. cbn [outside] in Hxx |- *. exact (proj2 Hxx). }
    clear MU1 DJW.
    pose proof (munch_refl [(asnum, asnum + 24)]%Z mm') as MUa. pose proof (wmono_refl bgusegs mm') as WMa.
    clear DLB DLP L0 DI0 DI1 LAsn LAt LAv LAsd WRsn WRt WRv Usn Ut Uv Usd BNt BNsd FRU STU MIU HTOPC EDL.
    clear DJst DJsd DJsv DJtd DJtv DJvd DJs_ta DJs_va DJt_ta DJt_va DJv_ta DJv_va DJs_da DJt_da DJv_da.

    repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
    apply hide_intro in TAc1. apply hide_intro in BNdv. apply hide_intro in ERRU.
    do 5 step. zstep. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    apply hide_elim in TAc1. apply hide_elim in BNdv. apply hide_elim in ERRU.
    apply hide_elim in DJ_ta_sa. apply hide_elim in DJ_da_sa. apply hide_elim in SAI.
    apply hide_elim in DJs_sa. apply hide_elim in DJt_sa. apply hide_elim in DJv_sa.
    eapply (rw_cells_transport bgusegs _ mm' mF) in TAc1; [| exact MUa | exact WMa | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - DJ_ta_sa; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ mm' mF) in BNdv; [| exact MUa | exact WMa | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - DJ_da_sa; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ mm' mF) in ERRU; [| exact MUa | exact WMa | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - SAI Rs1 Rs2; lia| exact I]].
    assert (Usn' : u64arr bgusegs mF DsnP (wlimbs snb)).
    { apply limbarr_limbs_at. split.
      - eapply limbs_at_transport; [exact LAsn1 | exact MUa |]. cbn [disjoint_from]. rewrite Lsnb. split; [clear - DJs_sa; lia | exact I].
      - rewrite Lsnb. exact WRsn1. }
    assert (Ut' : u64arr bgusegs mF Dt (wlimbs tmb)).
    { apply limbarr_limbs_at. split.
      - eapply limbs_at_transport; [exact LAt1 | exact MUa |]. cbn [disjoint_from]. rewrite Ltmb. split; [clear - DJt_sa; lia | exact I].
      - rewrite Ltmb. exact WRt1. }
    assert (Uv' : u64arr bgusegs mF Ddv (wlimbs rb)).
    { apply limbarr_limbs_at. split.
      - eapply limbs_at_transport; [exact LAv1 | exact MUa |]. cbn [disjoint_from]. rewrite Lrb. split; [clear - DJv_sa; lia | exact I].
      - rewrite Lrb. exact WRv1. }
    clear LAsn1 LAt1 LAv1 WRsn1 WRt1 WRv1 MUa WMa DJ_ta_sa DJ_da_sa SAI DJs_sa DJt_sa DJv_sa.
    ihere. to_implM. rewrite !bbind_set.
    set (TM := bn_with_buf btm tmb). set (DVV := bn_with_buf bvv rb). set (SN := mkBN (bn_d bsn) snb dn negn (bn_flags bsn)).
    assert (WOK : Forall (w_ok OWU LB lsU PL EA (bv_unsigned sp) [tmp; res; snum])
                    [(asnum, asnum + 24); (DsnP, DsnP + 8 * Z.of_nat (bn_dmax bsn)); (Dt, Dt + 8 * Z.of_nat (bn_dmax btm)); (Ddv, Ddv + 8 * Z.of_nat (bn_dmax bvv));
                     (bv_unsigned sp - 352, bv_unsigned sp)]).
    { constructor; [eapply (w_struct OWU LB lsU PL EA (bv_unsigned sp) false [tmp; res; snum] _ snum asnum); [right; right; left; reflexivity| exact HAsnum| exact NROs| cbn; lia| cbn; lia]|].
      constructor; [eapply (w_limbs OWU LB lsU PL EA (bv_unsigned sp) false [tmp; res; snum] _ snum psn DsnP); [right; right; left; reflexivity| exact HVsn| exact Edsn| exact Hinsn| cbn [fst snd]; lia| cbn [fst snd]; fold bsn; lia]|].
      constructor; [eapply (w_limbs OWU LB lsU PL EA (bv_unsigned sp) false [tmp; res; snum] _ tmp pt Dt); [left; reflexivity| exact HVtm| exact Edt| exact Hinpt| cbn [fst snd]; lia| cbn [fst snd]; fold btm; lia]|].
      constructor; [eapply (w_limbs OWU LB lsU PL EA (bv_unsigned sp) false [tmp; res; snum] _ res pv Ddv); [right; left; reflexivity| exact HVdv| exact Edv| exact Hinpv| cbn [fst snd]; lia| cbn [fst snd]; fold bvv; lia]|].
      constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LO; lia| constructor]. }
    assert (HWL : Forall (w_lib lsU OWU PL lo (bv_unsigned sp))
                    [(asnum, asnum + 24); (DsnP, DsnP + 8 * Z.of_nat (bn_dmax bsn)); (Dt, Dt + 8 * Z.of_nat (bn_dmax btm)); (Ddv, Ddv + 8 * Z.of_nat (bn_dmax bvv));
                     (bv_unsigned sp - 352, bv_unsigned sp)]).
    { constructor; [right; left; exists (qs, As, ns); cbn; auto|].
      constructor; [right; left; exists (psn, DsnP, 8 * Z.of_nat (bn_dmax bsn)); cbn; split; [exact Hinsn| lia]|].
      constructor; [right; left; exists (pt, Dt, 8 * Z.of_nat (bn_dmax btm)); cbn; split; [exact Hinpt| lia]|].
      constructor; [right; left; exists (pv, Ddv, 8 * Z.of_nat (bn_dmax bvv)); cbn; split; [exact Hinpv| lia]|].
      constructor; [left; cbn [fst snd]; clear - LO; lia| constructor]. }
    pose proof (lib_state_frame stU LB _ _ [tmp; res; snum] lsU mL mF OWU PL EA _ HEAPU LSH3 MU2 WM1 FROK WOK) as LSF.
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
    assert (ENVc : cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m
      (TFRAME jb0 negn sh arm d1 ac dn asnum loop asdiv (DsnP + 8 * Z.of_nat (nP - 1 - loop)) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) stU lsc mF OWU).
    { unfold lsc, lsb, lsa. do 3 apply cenv_setbn.
      eapply (CSIL _ _); [exact ENVU | exact LSU | exact MU2 | exact WM1 | exact HWL | exact ST1 | unfold LX_ERRNO, RATP; exact ERRU | exact MI1 | exact FR1 | cbn; lia]. }
    assert (HArm_c : oref_at lsc OWU PL rm arm) by (do 3 apply oref_at_setbn; exact HArm).
    assert (HAsn_c : ref_at lsc OWU PL snum asnum) by (apply ref_at_setbn; exact HAsn_b).
    clear LSF LSc1 LSc2 LSH1 LSH2 LSH3 WOK HWL MU2 WM1 TAc1 BNdv BNsn Usn' Ut' Uv' ERRU FR1 ST1 MI1 HEAPU.
    destruct rm as [r|].
    -
      cbn [oref_at] in HArm_c. pose proof (HPrm r eq_refl) as HPr.
      pose proof (lib_state_h_parts _ _ _ _ _ _ LSc3) as PARTSc.
      pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENVc) PARTSc HArm_c HPr) as (RA0 & RAC & _ & _).
      assert (ARM : 0 < arm < 18446744073709551616) by (clear - RA0 RAC CEIL LO SPR; lia).
      unfold implM. iprefix.
      zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. lia. }
      clear KZ.
      env_open ENVc. unfold TFRAME in FRe. unfold MallocRep.wz.
      step. zstep.
      clear HEAPe STe errve ERRe MIe FRe MUe WMe.
      destruct (CPRE _ _ _ _ _ BN_RSHIFT_STACK ENVc LSc3 ltac:(unfold BN_RSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK; clear - LO; lia)) as (errvR & PRER).
      ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
      eapply implM_embed_bind.
      { eapply (bn_rshift_fixed_top_walk HM HF) with (lo := lo) (B := B) (errv := errvR) (OW := OWU) (LB := LB) (PL := PL) (EA := EA) (rr := r) (rx := snum) (R := arm) (X := asnum) (n := sh);
          [exact PRER | reflexivity | exact HArm_c | exact HPr | exact HAsn_c | exact NROs | reflexivity | reflexivity | reflexivity | clear - Hsh; lia]. }
      cbv beta. intros [uS lsS] stS msS PO. apply BPC in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mS & OWS & PLS & -> & CPS & (EPLS & -> & _)).
      subst PLS. specialize (CPS eq_refl).
      destruct (CPOST _ _ _ _ _ _ _ _ _ ENVc CPS) as (ENVS & LSS).
      cbn [fst snd] in *.
      replace (ret_pc (Z_to_bv 64 1089176)) with (Z_to_bv 64 1089176) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear PRER CPS.
      env_open ENVS. unfold TFRAME in FRe. unfold MallocRep.wz. unfold implM. iprefix.
      zstep. if_cases KZ; zify_cond KZ. 2:{ exfalso. rewrite ?unsigned_lit in KZ by lia. lia. }
      clear KZ.
      env_close CSIL HWLs WOKs ENVS LSS ENVS' LSS'.
      ihere. to_implM. eapply FIN; [exact ENVS'| exact LSS'].
    -
      cbn [oref_at] in HArm_c. subst arm.
      rewrite bbind_ret.
      env_open ENVc. unfold TFRAME in FRe. unfold MallocRep.wz. unfold implM. iprefix.
      zstep. if_cases KZ; zify_cond KZ. 2:{ exfalso. rewrite ?unsigned_lit in KZ by lia. lia. }
      clear KZ.
      env_close CSIL HWLs WOKs ENVc LSc3 ENVS' LSS'.
      ihere. to_implM. eapply FIN; [exact ENVS'| exact LSS'].
  Qed.
End Proofs.
End WithCeiling0.
