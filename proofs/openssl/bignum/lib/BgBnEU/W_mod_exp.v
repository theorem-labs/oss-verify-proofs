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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgArith BgMont BgExp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small BnUKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
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

Definition BN_MOD_EXP : Z := 0x14fae0.
Definition BN_MOD_EXP_RECP : Z := 0x150724.
Definition BN_MOD_EXP_MONT : Z := 0x1500dc.
Definition BN_MOD_EXP_MONT_WORD : Z := 0x14fc38.

Section Proofs.

  Variable EXP_STACK : Z.
  Hypothesis EXP_STACK16 : 16 <= EXP_STACK.
  Definition BN_MOD_EXP_STACK : Z := 64 + EXP_STACK.

  Definition pl_fresh (PL : placement) : Prop :=
    pl_bn PL RRecpN = None /\ pl_bn PL RRecpNr = None /\ pl_recp PL = None /\ pl_mont PL = None /\ pl_bn PL RTmod = None.

  Definition exp_stmt (ENTRY STACK : Z) (one : bnref -> bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit)
      (sixth : option word) : Prop := forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr ra_ rp rm : bnref) (arr ara arp arm ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr arr -> ref_at bs OW PL ra_ ara -> ref_at bs OW PL rp arp -> ref_at bs OW PL rm arm ->
    hpl PL rr -> ra_ <> ROne -> rp <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz arr -> a1 = wz ara -> a2 = wz arp -> a3 = wz arm -> a4 = wz ac -> (forall w, sixth = Some w -> a5 = w) ->
    implM bgusegs (interp (embed (one rr ra_ rp rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ bs' OW' PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ENTRY) fc None m (seg_rom bgusegs)).

  Definition exp_stmt_f (ENTRY STACK : Z) (one : bnref -> bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit)
      (sixth : option word) : Prop := forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr ra_ rp rm : bnref) (arr ara arp arm ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr arr -> ref_at bs OW PL ra_ ara -> ref_at bs OW PL rp arp -> ref_at bs OW PL rm arm ->
    hpl PL rr -> ra_ <> ROne -> rp <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) -> pl_fresh PL ->
    a0 = wz arr -> a1 = wz ara -> a2 = wz arp -> a3 = wz arm -> a4 = wz ac -> (forall w, sixth = Some w -> a5 = w) ->
    implM bgusegs (interp (embed (one rr ra_ rp rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ bs' OW' PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ENTRY) fc None m (seg_rom bgusegs)).

  Hypothesis BN_mod_exp_recp_walk : exp_stmt_f BN_MOD_EXP_RECP EXP_STACK (BN_mod_exp_recp (tree_ops bptr)) None.
  Hypothesis BN_mod_exp_mont_walk : exp_stmt_f BN_MOD_EXP_MONT EXP_STACK (BN_mod_exp_mont (tree_ops bptr)) (Some (wz 0)).

  Hypothesis BN_mod_exp_mont_word_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rp rm : bnref) (A : Z) (arr arp arm ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv EXP_STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rr arr -> ref_at bs OW PL rp arp -> ref_at bs OW PL rm arm ->
    hpl PL rr -> rp <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) -> pl_fresh PL -> 0 <= A < BW ->
    a0 = wz arr -> a1 = wz A -> a2 = wz arp -> a3 = wz arm -> a4 = wz ac -> a5 = wz 0 ->
    implM bgusegs (interp (embed (BN_mod_exp_mont_word (tree_ops bptr) rr A rp rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ bs' OW' PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_EXP_MONT_WORD) fc None m (seg_rom bgusegs)).

  Lemma BN_mod_exp_walk : exp_stmt_f BN_MOD_EXP BN_MOD_EXP_STACK (BN_mod_exp (tree_ops bptr)) None.
  Proof.
    unfold exp_stmt_f. intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> SP16 HAr HAa HAp HAm WRr NROa NROp NROm HPC HFR -> -> -> -> -> _.
    unfold BN_MOD_EXP_STACK, BN_MOD_EXP, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.

    unfold BN_mod_exp, any_consttime, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd fold_right]. cbv beta.
    unfold implM. iprefix.

    carve_frame 64%nat ST. do 15 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -80, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL) as HEAP1.

    destruct (lib_state_open [] bs m1 OW PL EA ra_ ara LS1 ND HAa ltac:(intros []) NROa) as ((Da & BNa & ARRa) & (OKa1 & OKa2 & OKa3 & OKa4) & _).
    destruct (lib_state_open [] bs m1 OW PL EA rp arp LS1 ND HAp ltac:(intros []) NROp) as ((Dp & BNp & ARRp) & (OKp1 & OKp2 & OKp3 & OKp4) & _).
    destruct (lib_state_open [] bs m1 OW PL EA rm arm LS1 ND HAm ltac:(intros []) NROm) as ((Dm & BNm & ARRm) & (OKm1 & OKm2 & OKm3 & OKm4) & _).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAa) as HVa. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAm) as HVm.
    destruct (bn_arr_facts s OW LB m1 HEAP1 bs PL EA _ _ PARTS FROK ra_ Da HVa NROa ARRa) as (Ua & LENa & Da0 & DaC & _ & _).
    destruct (bn_arr_facts s OW LB m1 HEAP1 bs PL EA _ _ PARTS FROK rm Dm HVm NROm ARRm) as (Um & LENm & Dm0 & DmC & _ & _).
    set (ba := getbn ra_ bs) in *. set (bp := getbn rp bs) in *. set (bm := getbn rm bs) in *.
    unfold bn_cells in BNa, BNp, BNm. unfold BG_DMAX in OKa3, OKp3, OKm3.
    assert (FLa : 0 <= bn_flags ba <= 1) by (destruct OKa4 as [E|E]; rewrite E; lia).
    assert (FLp : 0 <= bn_flags bp <= 1) by (destruct OKp4 as [E|E]; rewrite E; lia).
    assert (FLm : 0 <= bn_flags bm <= 1) by (destruct OKm4 as [E|E]; rewrite E; lia).
    assert (CTa : Z.land (bn_flags ba) 4 = 0) by (destruct OKa4 as [E|E]; rewrite E; reflexivity).
    assert (CTp : Z.land (bn_flags bp) 4 = 0) by (destruct OKp4 as [E|E]; rewrite E; reflexivity).
    assert (CTm : Z.land (bn_flags bm) 4 = 0) by (destruct OKm4 as [E|E]; rewrite E; reflexivity).
    clear OKa4 OKp4 OKm4.

    assert (SEPa : ara + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= ara).
    { pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAa NROa) as (_ & SAC & _). clear - SAC CEIL LO EXP_STACK16. lia. }
    assert (SEPp : arp + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= arp).
    { pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAp NROp) as (_ & SAC & _). clear - SAC CEIL LO EXP_STACK16. lia. }
    assert (SEPm : arm + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= arm).
    { pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAm NROm) as (_ & SAC & _). clear - SAC CEIL LO EXP_STACK16. lia. }
    assert (SEPDa : Da + 8 * Z.of_nat (bn_dmax ba) <= bv_unsigned sp - 80 \/ bv_unsigned sp <= Da) by (clear - DaC CEIL LO EXP_STACK16; lia).
    assert (SEPDm : Dm + 8 * Z.of_nat (bn_dmax bm) <= bv_unsigned sp - 80 \/ bv_unsigned sp <= Dm) by (clear - DmC CEIL LO EXP_STACK16; lia).
    assert (DaR : Da < 2^63) by (clear - DaC CEIL; lia).
    clear DaC DmC.
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAa NROa) as (AaP & AA8).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAp NROp) as ALp.
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAm NROm) as ALm.
    assert (UPm : ub_ptr_ok (Z.of_nat (bn_top bm)) Dm).
    { intros T0. apply (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP1 PARTS ARRm). clear - T0 OKm2. lia. }
    assert (AaR : ara < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAa NROa) as (_ & Y & _); clear - Y SPR; lia).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (BN_is_odd_spec _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (lo := lo) (A := arm) (D := Dm) (b := bm);
        [exact BNm | exact ALm | exact UPm | exact Um | exact OKm1 | exact OKm2 | clear - OKm3; lia | rewrite ESP; exact ST | rewrite ESP; clear - LO EXP_STACK16 SPR; lia | exact MI
        | rewrite ESP; clear - SEPm SPR; lia | rewrite ESP; clear - SEPDm SPR; lia | reflexivity]. }
    post_call bgusegs m1. rename x14 into m2. rename PC into ST. rewrite ESP in ST. lazymatch type of POST with ?x = _ => subst x end.

    assert (TAIL : forall mX (QX : unit * bstate bptr -> PState -> machine_state -> Prop),
      munch [(bv_unsigned sp - 80, bv_unsigned sp)] m mX -> wmono bgusegs m mX -> mem_inv bgusegs mX -> rw_cells bgusegs mX 3346164 [C4 errv] ->
      stk bgusegs mX lo (bv_unsigned sp) ->
      (forall r st' ms', bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B mX PL EA
                            (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = Z_to_bv 64 1) r st' ms' -> QX r st' ms') ->
      bn_pre s bs mX OW LB PL EA sp lo B errv EXP_STACK /\
      (forall r st' ms', bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B mX PL EA
                            (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = Z_to_bv 64 1) r st' ms' -> QX r st' ms')).
    { intros mX QX MUX WMX MIX ERRX STX HQ. split; [|exact HQ]. unfold bn_pre.
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUX WMX HWL CEIL)|].
      split; [exact (lib_state_frame s LB _ _ [] bs m mX OW PL EA _ HEAP LS MUX WMX FROK WOK)|].
      split; [exact FROK|]. split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MUX WMX HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|].
      split; [exact SPB|]. split; [exact B63|]. split; [exact STX|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [lia|].
      split; [unfold LX_ERRNO, RATP; exact ERRX| exact MIX]. }

    assert (POSTX : forall mX r st' ms', munch [(bv_unsigned sp - 80, bv_unsigned sp)] m mX -> wmono bgusegs m mX ->
      bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B mX PL EA
        (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = Z_to_bv 64 1) r st' ms' ->
      bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
        (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = Z_to_bv 64 1) r st' ms').
    { intros mX r st' ms' MUX WMX PO. unfold bn_post in *.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m9 & OW9 & PL9 & errv9 & -> & HEAP9 & LS9 & AUX9 & ST9 & ERR9
                      & MI9 & LXP9 & FA9 & SO9 & RST9 & RES9).
      do 15 eexists. exists m9, OW9, PL9, errv9. split; [reflexivity|]. repeat (split; [assumption|]).
      split; [|repeat (split; [assumption|]); exact RES9].
      eapply lx_pres_trans; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUX WMX HWL CEIL); unfold GLOBALS_TOP; lia| exact LXP9]. }
    destruct (is_odd_pure bm) eqn:Eodd; cbn [Z.b2z].
    2:{
      step. if_true. do 13 step. release_frame FR ST (bv_unsigned sp). step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mX end.
      ihere. to_implM.
      destruct (TAIL mX _ MU WM ltac:(the_mi) ERR ST (fun r st' ms' H => H)) as [PREX _].
      eapply implM_mono; [eapply BN_mod_exp_recp_walk; [exact PREX| reflexivity| exact SP16| exact HAr| exact HAa| exact HAp| exact HAm| exact WRr| exact NROa| exact NROp| exact NROm| exact HPC| exact HFR
        | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| intros w Hw; discriminate Hw]|].
      cbv beta. intros r st' ms' PO. exact (POSTX mX r st' ms' MU WM PO). }

    step. if_false.
    chkw ltac:(fun C => clear - C AaP AaR; lia).
    step. rewrite ?(land7_wrap _ AA8), ?(land7_wz _ AA8).
    chkw ltac:(fun C => clear - C; lia).
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top ba))) by (clear - OKa2 OKa3; lia).
    step. step. if_cases KT; zify_cond KT; rewrite ?unsigned_lit in KT by (clear - OKa2 OKa3; lia).
    {
      replace ((bn_top ba =? 1)%nat) with false by (symmetry; apply Nat.eqb_neq; clear - KT; lia). cbn [andb].
      do 14 step. release_frame FR ST (bv_unsigned sp). step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mX end.
      ihere. to_implM.
      destruct (TAIL mX _ MU WM ltac:(the_mi) ERR ST (fun r st' ms' H => H)) as [PREX _].
      eapply implM_mono; [eapply BN_mod_exp_mont_walk; [exact PREX| reflexivity| exact SP16| exact HAr| exact HAa| exact HAp| exact HAm| exact WRr| exact NROa| exact NROp| exact NROm| exact HPC| exact HFR
        | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| intros w Hw; injection Hw; intros <-; reflexivity]|].
      cbv beta. intros r st' ms' PO. exact (POSTX mX r st' ms' MU WM PO). }
    replace ((bn_top ba =? 1)%nat) with true by (symmetry; apply Nat.eqb_eq; clear - KT; lia). cbn [andb].

    assert (NGa : 0 <= Z.b2z (bn_neg ba) <= 1) by (destruct (bn_neg ba); cbn; lia).
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.b2z (bn_neg ba))) by (clear - NGa; lia).
    step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by (clear - NGa; lia).
    {
      replace (bn_neg ba) with true by (destruct (bn_neg ba); [reflexivity| cbn in KN; lia]). cbn [negb andb].
      do 14 step. release_frame FR ST (bv_unsigned sp). step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mX end.
      ihere. to_implM.
      destruct (TAIL mX _ MU WM ltac:(the_mi) ERR ST (fun r st' ms' H => H)) as [PREX _].
      eapply implM_mono; [eapply BN_mod_exp_mont_walk; [exact PREX| reflexivity| exact SP16| exact HAr| exact HAa| exact HAp| exact HAm| exact WRr| exact NROa| exact NROp| exact NROm| exact HPC| exact HFR
        | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| intros w Hw; injection Hw; intros <-; reflexivity]|].
      cbv beta. intros r st' ms' PO. exact (POSTX mX r st' ms' MU WM PO). }
    replace (bn_neg ba) with false by (destruct (bn_neg ba); [cbn in KN; lia| reflexivity]). cbn [negb andb].

    unfold has_flag, BN_FLG_CONSTTIME. rewrite CTa, CTp, CTm. cbn [Z.eqb negb orb andb].

    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    eapply evt_cut.
    { eapply (BN_get_flags_spec _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (lo := lo) (A := arp) (D := Dp) (b := bp);
        [exact BNp | exact ALp | clear - FLp; lia | rewrite ESP; exact ST | rewrite ESP; clear - LO EXP_STACK16 SPR; lia | the_mi | rewrite ESP; clear - SEPp SPR; lia | reflexivity]. }
    post_call bgusegs m3. rename PC into ST. rewrite ESP in ST. lazymatch type of POST with ?x = _ => subst x end.
    rewrite (unsigned_lit 4) by lia. rewrite CTp.
    step. if_false.

    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    eapply evt_cut.
    { eapply (BN_get_flags_spec _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (lo := lo) (A := ara) (D := Da) (b := ba);
        [exact BNa | split; [exact AaP| exact AA8] | clear - FLa; lia | rewrite ESP; exact ST | rewrite ESP; clear - LO EXP_STACK16 SPR; lia | the_mi | rewrite ESP; clear - SEPa SPR; lia | reflexivity]. }
    post_call bgusegs m4. rename PC into ST. rewrite ESP in ST. lazymatch type of POST with ?x = _ => subst x end.
    rewrite (unsigned_lit 4) by lia. rewrite CTa.
    step. if_false.

    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    eapply evt_cut.
    { eapply (BN_get_flags_spec _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (lo := lo) (A := arm) (D := Dm) (b := bm);
        [exact BNm | exact ALm | clear - FLm; lia | rewrite ESP; exact ST | rewrite ESP; clear - LO EXP_STACK16 SPR; lia | the_mi | rewrite ESP; clear - SEPm SPR; lia | reflexivity]. }
    post_call bgusegs m5. rename PC into ST. rewrite ESP in ST. lazymatch type of POST with ?x = _ => subst x end.
    rewrite (unsigned_lit 4) by lia. rewrite CTm.
    step. if_true.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    step.
    destruct (bn_buf ba) as [|w0 l0] eqn:Ebuf; [exfalso; unfold bn_dmax in OKa2; rewrite Ebuf in OKa2; cbn [length] in OKa2; clear - OKa2 KT; lia|].
    pose proof (limbs_nth (w0 :: l0) 0 OKa1) as LN. cbn [nth] in LN.
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP1 PARTS ARRa ltac:(unfold bn_dmax; rewrite Ebuf; cbn; lia)) as (DaP & DA8).
    chkw ltac:(fun C => clear - C DaP DaR; lia).
    step. rewrite ?(land7_wrap _ DA8), ?(land7_wz _ DA8).
    chkw ltac:(fun C => clear - C; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let a := cur_mem_addr in pose proof (u64arr_read_0 mx Da w0 l0 a Ua ltac:(addr_tac)) as RD end.
    step. clear RD.
    do 13 step. release_frame FR ST (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mX end.
    ihere. to_implM. fold ba. rewrite Ebuf. cbn [nth].
    destruct (TAIL mX _ MU WM ltac:(the_mi) ERR ST (fun r st' ms' H => H)) as [PREX _].
    eapply implM_mono; [eapply BN_mod_exp_mont_word_walk; [exact PREX| reflexivity| exact SP16| exact HAr| exact HAp| exact HAm| exact WRr| exact NROp| exact NROm| exact HPC| exact HFR| exact LN
      | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]|].
    cbv beta. intros r st' ms' PO. exact (POSTX mX r st' ms' MU WM PO).
  Qed.
End Proofs.
End WithCeiling0.
