(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnDivWords BnModel BnTree BnInv BnBridge BgState BgWords BgInv BgLib BgArith BgMont BgExp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top BnUKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit ValArr W_mod_exp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac the_mi := lazymatch goal with H : mem_inv bgusegs _ |- _ => exact H end.
Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_RECP_CTX_SET : Z := 0x151d44.
Definition BN_RECIPROCAL : Z := 0x152170.
Definition BN_COPY : Z := 0xfe304.
Definition BN_DIV : Z := 0x10966c.
Definition BN_SET_BIT : Z := 0xff0e8.
Definition BN_CTX_START : Z := 0x100c14.
Definition BN_CTX_GET : Z := 0x100e84.
Definition BN_CTX_END : Z := 0x100da4.

Lemma nbits_range : forall b : bignum bptr, limbs (bn_buf b) -> 0 <= num_bits_pure b <= 64 * Z.of_nat (bn_top b).
Proof.
  intros b HL. unfold num_bits_pure. destruct (Nat.eqb_spec (bn_top b) 0) as [E|NE]; [lia|].
  pose proof (limbs_nth (bn_buf b) (bn_top b - 1) HL) as LN. unfold limb, BW in LN.
  pose proof (num_bits_word_le (nth (bn_top b - 1) (bn_buf b) 0) 64 ltac:(lia) LN). lia.
Qed.

Section Proofs.
  Variable CS : Z.
  Hypothesis CS96 : 128 <= CS.
  Definition BN_RECP_CTX_SET_STACK : Z := 32 + CS.

  Hypothesis BN_copy_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rx ry : bnref) (ax ay : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rx ax -> ref_at bs OW PL ry ay -> wref PL rx -> ry <> ROne -> a0 = wz ax -> a1 = wz ay ->
    implM bgusegs (interp (embed (BN_copy (tree_ops bptr) rx ry bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz ax /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_COPY) fc None m (seg_rom bgusegs)).

  Hypothesis BN_CTX_start_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_start (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' _ => PL' = PL /\ forall q A n, In (q, A, n) OW -> In (q, A, n) OW'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_START) fc None m (seg_rom bgusegs)).

  Hypothesis BN_CTX_get_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_get (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun r bs' OW' PL' a0' => PL' = PL /\ (exists i, r = RPool i) /\ (exists a, ref_at bs' OW' PL r a /\ a0' = wz a) /\ forall q A n, In (q, A, n) OW -> In (q, A, n) OW'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_GET) fc None m (seg_rom bgusegs)).

  Hypothesis BN_CTX_end_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ OW' PL' _ => PL' = PL /\ OW' = OW))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_END) fc None m (seg_rom bgusegs)).

  Hypothesis BN_set_bit_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rx : bnref) (ax n : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = Z_to_bv 64 n -> -2^31 <= n < 2^31 ->
    implM bgusegs (interp (embed (BN_set_bit (tree_ops bptr) rx n bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_SET_BIT) fc None m (seg_rom bgusegs)).

  Hypothesis BN_div_q_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx rm : bnref) (ar ax am ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL rm am -> wref PL rr -> rx <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz 0 -> a2 = wz ax -> a3 = wz am -> a4 = wz ac ->
    implM bgusegs (interp (embed (BN_div (tree_ops bptr) (Some rr) None rx rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_DIV) fc None m (seg_rom bgusegs)).

  Lemma BN_RECP_CTX_set_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rd : bnref) (ad an : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_RECP_CTX_SET_STACK -> tp = wz RATP ->
    ref_at bs OW PL rd ad -> rd <> ROne -> recp_at PL an -> a0 = wz an -> a1 = wz ad ->
    implM bgusegs (interp (embed (BN_RECP_CTX_set (tree_ops bptr) rd bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RECP_CTX_SET) fc None m (seg_rom bgusegs)).
  Proof.
    intros until an. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HAd NROd HRC -> ->.
    unfold BN_RECP_CTX_SET_STACK, BN_RECP_CTX_SET, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (recp_at_refN bs OW PL an HRC) as HAN. pose proof (recp_at_refNr bs OW PL an HRC) as HANr.
    pose proof (recp_at_wrefN PL an HRC) as WRN. pose proof (recp_at_wrefNr PL an HRC) as WRNr. pose proof (recp_at_recp PL an HRC) as HRc.
    assert (AnR : 0 < an /\ an + 60 < 2^63).
    { pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAN (proj1 WRN)) as (X & _ & _).
      pose proof (recp_facts _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HRc) as (_ & _ & Y & Z_ & _). unfold RECP_SC_SZ in Y. clear - X Y Z_. lia. }
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAN (proj1 WRN)) as (_ & AN8).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAd NROd) as ALd.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.

    unfold BN_RECP_CTX_set, BN_num_bits, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd].
    unfold implM. iprefix.

    carve_frame 32%nat ST. do 6 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m fr s bs m1 OW)
    end.
    { unfold kenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -32) by lia.
    assert (FBsp : bv_unsigned sp + -32 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) CEIL FBlo FBsp SPR2 A) as BPK.
    pose proof (kenv_open LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL FROK) as KOPEN.
    pose proof (kenv_open_u LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL FROK) as KOPENU.
    pose proof (kenv_below LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KBELOW.
    assert (LOF : lo <= bv_unsigned sp + -32 - CS) by lia.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    clear HEAP AUX ST ERR MI MU WM HWL WOK FR LS.

    destruct (KOPEN _ _ _ _ _ rd ad ENV LS1 HAd NROd) as (Dd & BNd & Ud & (OKd1 & OKd2 & OKd3 & OKd4) & _ & SEPd & SEPDd & _).
    pose proof ENV as (_ & _ & ST1 & _ & MI1 & _).
    step. step. step. step.
    eapply evt_cut.
    { eapply (BN_is_zero_spec _ (Z_to_bv 64 (bv_unsigned sp + -32))) with (lo := lo) (A := ad) (D := Dd) (b := getbn rd bs);
        [exact BNd | exact ALd | clear - OKd2 OKd3; unfold BG_DMAX in OKd3; lia | rewrite ESP; exact ST1 | rewrite ESP; clear - LOF CS96; lia | exact MI1
        | rewrite ESP; clear - SEPd FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST1 MI1.
    intros ms2 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *.
    destruct (KBELOW _ _ _ _ m2 _ 16 ENV LS1 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV2 & LS2). clear ENV LS1 MUc WMc MIc STc BNd Ud.
    replace (ret_pc (Z_to_bv 64 0x151d6c)) with (Z_to_bv 64 0x151d6c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold is_zero_pure. destruct (Nat.eqb_spec (bn_top (getbn rd bs)) 0) as [TZ|TNZ]; cbn [Z.b2z].
    {
      step. if_false. ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
    step. if_true.

    chkw ltac:(fun C => clear - C AnR; lia).
    step. rewrite ?(land7_wrap _ AN8), ?(land7_wz _ AN8).
    chkw ltac:(fun C => clear - C; lia).
    step. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV2 LS2 LOF) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_copy_walk; [exact PRE1| reflexivity| exact HAN| exact HAd| exact WRN| exact NROd| reflexivity| reflexivity]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & OW3 & -> & KP & (_ & -> & _)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV2 KP) as (ENV3 & LS3). pose proof KP as RS3; apply kpost_refs in RS3.
    cbn [fst snd] in *. clear PRE1 KP ENV2 LS2.
    replace (ret_pc (Z_to_bv 64 0x151d90)) with (Z_to_bv 64 0x151d90) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold implM. iprefix.
    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AnR; lia); zify_cond KZ; [exfalso; clear - KZ AnR; lia| clear KZ].

    unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
    step. step.
    eapply (zero_call LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) with (r := RRecpNr) (ar := an + 24);
      [clear - LOF CS96; lia | reflexivity | exact ENV3 | exact LS3 | exact (recp_at_refNr _ _ _ _ HRC) | exact WRNr |].
    intros m4 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV4 LS4.
    replace (ret_pc (Z_to_bv 64 0x151d9c)) with (Z_to_bv 64 0x151d9c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    set (bs4 := setbn RRecpNr (bn_zero_pure (getbn RRecpNr bs1)) bs1) in *.

    assert (HAd4 : ref_at bs4 OW3 PL rd ad) by (apply ref_at_setbn; exact (ref_at_stable _ _ _ _ PL _ _ RS3 HAd)).
    destruct (KOPENU _ _ _ _ _ rd ad ENV4 LS4 HAd4 NROd) as (Dd4 & BNd & Ud & (OKd1' & OKd2' & OKd3' & OKd4') & _ & SEPd4 & SEPDd4 & _ & ALd4 & UPd4).
    set (bd := getbn rd bs4) in *.
    assert (FLd : 0 <= bn_flags bd <= 1) by (destruct OKd4' as [E|E]; rewrite E; lia).
    assert (CTd : Z.land (bn_flags bd) 4 = 0) by (destruct OKd4' as [E|E]; rewrite E; reflexivity).
    pose proof ENV4 as (_ & _ & ST4 & _ & MI4 & _). unfold BG_DMAX in OKd3'.
    step. step.
    eapply evt_cut.
    { eapply (BN_num_bits_spec _ (Z_to_bv 64 (bv_unsigned sp + -32))) with (lo := lo) (A := ad) (D := Dd4) (b := bd);
        [exact BNd | exact ALd4 | exact UPd4 | exact Ud | exact OKd1' | exact OKd2' | clear - OKd3'; lia | clear - FLd; lia | exact CTd
        | rewrite ESP; exact ST4 | rewrite ESP; clear - LOF CS96; lia | exact MI4
        | rewrite ESP; clear - SEPd4 FBlo FBsp CS96 LOF; lia | rewrite ESP; clear - SEPDd4 FBlo FBsp CS96 LOF; lia | reflexivity]. }
    clear ST4 MI4.
    intros ms5 PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *.
    destruct (KBELOW _ _ _ _ m5 _ 128 ENV4 LS4 ltac:(lia) ltac:(clear - LOF CS96; lia) MUc WMc STc MIc) as (ENV5 & LS5). clear ENV4 LS4 MUc WMc MIc STc BNd Ud.
    replace (ret_pc (Z_to_bv 64 0x151da4)) with (Z_to_bv 64 0x151da4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (nbits_range bd OKd1') as BITS.
    unfold has_flag, BN_FLG_CONSTTIME. fold bd. rewrite CTd. cbn [Z.eqb negb tbind]. cbv beta.
    set (nb := num_bits_pure bd) in *.

    pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LS5 HRc) as RC. unfold recp_cells in RC.
    pose proof ENV5 as (HEAP5 & _ & ST5 & (errv5 & ERR5) & MI5 & _ & _ & _ & _ & FR5 & _).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS5) as PARTS5.
    pose proof (recp_facts _ _ _ _ _ _ _ _ _ _ HEAP5 PARTS5 FROK HRc) as (RC0 & RCS & RCB & _ & _ & _). unfold RECP_SC_SZ in RCB.
    unfold LX_ERRNO, RATP in ERR5. change (3346328 - 164) with 3346164 in ERR5.
    pose proof (munch_refl [(an + 48, an + 48 + RECP_SC_SZ)]%Z m5) as MU. pose proof (wmono_refl bgusegs m5) as WM. unfold RECP_SC_SZ in MU.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    assert (LS6 : lib_state (set_recp nb 0 bs4) m6 OW3 PL EA).
    { eapply (lib_state_set_recp _ LB (bv_unsigned sp) B false [] bs4 m5 m6 OW3 PL EA (an + 48) nb 0);
        [exact HEAP5| exact LS5| exact FROK| exact HRc| exact MU| exact WM| exact RC]. }
    assert (ENV6 : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m [C8 s2; C8 s1; C8 s0; C8 ra] st1 (set_recp nb 0 bs4) m6 OW3).
    { apply kenv_set_recp.
      eapply kenv_xw with (m := m5) (W := [(an + 48, an + 48 + 12)]) (errv' := errv5);
        [exact CEIL| exact GLO'| exact FBlo| exact FBsp| exact SPB| exact FROK| exact ENV5| exact MU| exact WM| | exact ST5| unfold LX_ERRNO, RATP; exact ERR5| exact MI5| exact FR5].
      constructor; [|constructor]. exists (an + 48, an + 48 + RECP_SC_SZ). split; [apply pl_frames_recp; exact HRc|]. unfold RECP_SC_SZ. cbn [fst snd]. clear. lia. }
    clear RC MU WM ST5 FR5 ERR5 MI5 HEAP5 ENV5 LS5.

    ihere. to_implM. unfold bsetrecp. cbn [ret tree_ops embed interp]. apply implM_interp_ret.
    pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -32) s bs OW m _ _ _ _ _ ENV6) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
    step. do 4 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_post. do 15 eexists. exists m6, OW3, PL, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact LS6|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity.
  Qed.

  Definition BN_RECIPROCAL_STACK : Z := 64 + CS.

  Lemma BN_reciprocal_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rm : bnref) (arr arm len ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_RECIPROCAL_STACK -> tp = wz RATP ->
    ref_at bs OW PL rr arr -> ref_at bs OW PL rm arm -> wref PL rr -> rm <> ROne -> pl_ctx PL = Some (ac, qc) -> 0 <= len < 2^31 ->
    a0 = wz arr -> a1 = wz arm -> a2 = wz len -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_reciprocal (tree_ops bptr) rr rm len bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun r _ _ PL' a0' => PL' = PL /\ r = len /\ a0' = wz len))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RECIPROCAL) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HAr HAm WRr NROm HPC LEN -> -> -> ->.
    unfold BN_RECIPROCAL_STACK, BN_RECIPROCAL, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.

    unfold BN_reciprocal, bbind, bret. cbn [bind ret tree_ops tbind fst snd].
    unfold implM. iprefix.

    carve_frame 64%nat ST. do 15 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m fr s bs m1 OW)
    end.
    { unfold kenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -64) by lia.
    assert (FBsp : bv_unsigned sp + -64 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) CEIL FBlo FBsp SPR2 A) as BPK.
    assert (LOF : lo <= bv_unsigned sp + -64 - CS) by lia.
    clear HEAP AUX ST ERR MI MU WM HWL WOK FR.

    destruct (KPRE _ _ _ _ _ CS ENV LS1 LOF) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_start_walk; [exact PRE1| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & INCL2)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP) as (ENV2 & LS2). pose proof KP as RS2; apply kpost_refs in RS2.
    cbn [fst snd] in *. clear PRE1 KP ENV LS1.
    replace (ret_pc (Z_to_bv 64 0x1521b0)) with (Z_to_bv 64 0x1521b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV2 LS2 LOF) as (errv2 & PRE2).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_get_walk; [exact PRE2| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [t bs2] st2 ms2 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & OW3 & -> & KP & (_ & (ti & Et) & (at_ & HAt & ->) & INCL3)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV2 KP) as (ENV3 & LS3). pose proof KP as RS3; apply kpost_refs in RS3.
    cbn [fst snd] in *. clear PRE2 KP ENV2 LS2.
    replace (ret_pc (Z_to_bv 64 0x1521b8)) with (Z_to_bv 64 0x1521b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (refs_stable_trans _ _ _ _ _ _ RS2 RS3) as RS13.
    pose proof ENV3 as (HEAP3 & _). pose proof (lib_state_h_parts _ _ _ _ _ _ LS3) as PARTS3.
    assert (FROK3 : frames_ok PL (bv_unsigned sp + -64) B) by (eapply frames_ok_call; [exact FROK| exact CEIL| exact FBlo| exact FBsp]).
    assert (NROt : t <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP3 PARTS3 FROK3 HAt NROt) as (At0 & AtC & _).
    assert (AtR : 0 < at_ < 2^64) by (clear - At0 AtC SPR; lia). clear AtC HEAP3 PARTS3.
    unfold implM. iprefix. step.
    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].

    step. step. step.
    destruct (KPRE _ _ _ _ _ CS ENV3 LS3 LOF) as (errv3 & PRE3).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_set_bit_walk; [exact PRE3| reflexivity| exact HAt| rewrite Et; apply wref_pool| reflexivity| reflexivity| clear - LEN; lia]. }
    cbv beta. intros [u4 bs4] st4 ms4 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & OW4 & -> & KP & (_ & -> & _)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV3 KP) as (ENV4 & LS4). pose proof KP as RS4; apply kpost_refs in RS4.
    cbn [fst snd] in *. clear PRE3 KP ENV3 LS3.
    replace (ret_pc (Z_to_bv 64 0x1521cc)) with (Z_to_bv 64 0x1521cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (refs_stable_trans _ _ _ _ _ _ RS13 RS4) as RS14.
    unfold implM. iprefix. step. if_false.

    do 5 step. step.
    destruct (KPRE _ _ _ _ _ CS ENV4 LS4 LOF) as (errv5 & PRE5).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_div_q_walk; [exact PRE5| reflexivity| exact (ref_at_stable _ _ _ _ PL _ _ RS14 HAr)| exact (ref_at_stable _ _ _ _ PL _ _ RS4 HAt)
        | exact (ref_at_stable _ _ _ _ PL _ _ RS14 HAm)| exact WRr| exact NROt| exact NROm| exact HPC| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros [u6 bs6] st6 ms6 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & OW6 & -> & KP & (_ & ->)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV4 KP) as (ENV6 & LS6). pose proof KP as RS6; apply kpost_refs in RS6.
    cbn [fst snd] in *. clear PRE5 KP ENV4 LS4.
    replace (ret_pc (Z_to_bv 64 0x1521e8)) with (Z_to_bv 64 0x1521e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    unfold implM. iprefix. step. step. step.
    assert (ESL : bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 1)) + -1))) = 0) by (vm_compute; reflexivity).
    rewrite ESL. rewrite (unsigned_lit len) by (clear - LEN; lia). rewrite Z.lor_0_l. clear ESL.
    step. step.
    destruct (KPRE _ _ _ _ _ CS ENV6 LS6 LOF) as (errv7 & PRE7).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply BN_CTX_end_walk; [exact PRE7| reflexivity| exact HPC| reflexivity]. }
    cbv beta. intros [u8 bs8] st8 ms8 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & OW8 & -> & KP & (_ & EOW8)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENV6 KP) as (ENV8 & LS8). pose proof KP as RS8; apply kpost_refs in RS8.
    cbn [fst snd] in *. clear PRE7 KP ENV6 LS6.
    replace (ret_pc (Z_to_bv 64 0x1521fc)) with (Z_to_bv 64 0x1521fc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [embed interp]. apply implM_interp_ret.
    pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m _ _ _ _ _ ENV8) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
    step. do 8 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_post. do 15 eexists. exists m8, OW8, PL, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact LS8|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; [reflexivity|]. split; reflexivity.
  Qed.
End Proofs.
End WithCeiling0.
