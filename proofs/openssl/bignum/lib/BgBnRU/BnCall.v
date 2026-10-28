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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Env.

  Variables (LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B SPv FB : Z).
  Variables (s0 : PState) (bs0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LOFB : lo <= FB.
  Hypothesis FBSP : FB <= SPv.
  Hypothesis SPB : SPv <= B.
  Hypothesis SPR : SPv < 2^64.
  Hypothesis FROK : frames_ok PL SPv B.

  Lemma FROK_FB : frames_ok PL FB B.
  Proof using CEIL LOFB FBSP FROK. eapply frames_ok_mono; [exact FROK| lia]. Qed.

  Definition cenv (fr : list cell) (st : PState) (bs : bstate bptr) (m : mem) (OW : list block) : Prop :=
    RHEAP st (OW ++ LB) m /\ rauxv_ok m B /\ stk bgusegs m lo FB /\ (exists errv : word, rw_cells bgusegs m LX_ERRNO [C4 errv]) /\ mem_inv bgusegs m
    /\ lx_pres LB SPv (XW PL) m0 m /\ ps_fa st = ps_fa s0 /\ ps_so st = ps_so s0 /\ refs_stable bs0 OW0 bs OW
    /\ rw_cells bgusegs m FB fr /\ Z.of_nat (cells_size fr) = SPv - FB.

  Lemma ESPv : bv_unsigned (Z_to_bv 64 FB) = FB.
  Proof using CEIL LOFB FBSP SPR. apply unsigned_lit. lia. Qed.

  Lemma cenv_pre : forall fr st bs m OW K,
    cenv fr st bs m OW -> lib_state bs m OW PL EA -> lo <= FB - K ->
    exists errv, bn_pre st bs m OW LB PL EA (Z_to_bv 64 FB) lo B errv K.
  Proof using CEIL GLO LOFB FBSP SPB SPR FROK.
    intros fr st bs m OW K (HEAP & AUX & ST & (errv & ERR) & MI & _) LS HK. exists errv. pose proof FROK_FB as FF. pose proof FROK as (_ & _ & B63).
    unfold bn_pre. rewrite ESPv. repeat (split; [first [assumption | lia]|]). assumption.
  Qed.

  Definition cpost (st : PState) (bs : bstate bptr) (m : mem) (OW : list block) (st' : PState) (bs' : bstate bptr) (m' : mem) (OW' : list block) : Prop :=
    RHEAP st' (OW' ++ LB) m' /\ lib_state bs' m' OW' PL EA /\ rauxv_ok m' B /\ stk bgusegs m' lo FB
    /\ (exists errv' : word, rw_cells bgusegs m' LX_ERRNO [C4 errv']) /\ mem_inv bgusegs m'
    /\ lx_pres LB FB (XW PL) m m' /\ ps_fa st' = ps_fa st /\ ps_so st' = ps_so st /\ refs_stable bs OW bs' OW'.

  Lemma cpost_refs : forall st bs m OW st' bs' m' OW', cpost st bs m OW st' bs' m' OW' -> refs_stable bs OW bs' OW'.
  Proof. intros st bs m OW st' bs' m' OW' (_ & _ & _ & _ & _ & _ & _ & _ & _ & RS). exact RS. Qed.

  Lemma cenv_post : forall fr st bs m OW st' bs' m' OW',
    cenv fr st bs m OW -> cpost st bs m OW st' bs' m' OW' -> cenv fr st' bs' m' OW' /\ lib_state bs' m' OW' PL EA.
  Proof using CEIL GLO LOFB FBSP FROK.
    intros fr st bs m OW st' bs' m' OW' (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ)
           (HEAP' & LS' & AUX' & ST' & ERR' & MI' & LXP' & FA' & SO' & RS').
    split; [|exact LS'].
    unfold cenv. split; [exact HEAP'|]. split; [exact AUX'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact MI'|].
    split. { eapply lx_pres_trans; [exact LXP|]. eapply lx_pres_weaken; [exact LXP'| exact FBSP| auto| auto]. }
    split; [congruence|]. split; [congruence|].
    split; [eapply refs_stable_trans; eauto|].
    split; [|exact FSZ].
    eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP' | exact FR |].
    intros a Ha. eapply xw_client; [exact (proj1 FROK)| lia|].
    unfold LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. unfold GLOBALS_TOP in GLO. lia.
  Qed.

  Lemma bn_post_cpost : forall {A : Type} (ra gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      st bs OW m (RES : A -> bstate bptr -> list block -> placement -> word -> Prop) (r : A * bstate bptr) st' ms',
    bn_post ra (Z_to_bv 64 FB) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc st bs OW LB lo B m PL EA RES r st' ms' ->
    exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' OW' PL',
      ms' = MS (mkR ra (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bgusegs)
      /\ (PL' = PL -> cpost st bs m OW st' (snd r) m' OW') /\ RES (fst r) (snd r) OW' PL' a0.
  Proof using CEIL LOFB FBSP SPR.
    intros A ra gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc st bs OW m RES r st' ms' PO. unfold bn_post in PO.
    destruct PO as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & OW' & PL' & errv' & E & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11).
    rewrite ESPv in *.
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', OW', PL'. split; [exact E|]. split; [|exact P11].
    intros ->. unfold cpost. repeat (split; [first [assumption | exists errv'; assumption]|]). assumption.
  Qed.

  Lemma cenv_silent : forall fr fr' st bs m m' OW W (errv' : word),
    cenv fr st bs m OW -> lib_state bs m OW PL EA -> munch W m m' -> wmono bgusegs m m' -> Forall (w_lib bs OW PL lo SPv) W ->
    stk bgusegs m' lo FB -> rw_cells bgusegs m' LX_ERRNO [C4 errv'] -> mem_inv bgusegs m' ->
    rw_cells bgusegs m' FB fr' -> Z.of_nat (cells_size fr') = SPv - FB ->
    cenv fr' st bs m' OW.
  Proof using CEIL GLO LOFB FBSP SPB FROK.
    intros fr fr' st bs m m' OW W errv' (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ) LS MU WM HW ST' ERR' MI' FR' FSZ'.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    unfold cenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HW CEIL)|].
    split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HW SPB ltac:(lia)); exact GLO|].
    split; [exact ST'|]. split; [exists errv'; exact ERR'|]. split; [exact MI'|].
    split. { eapply lx_pres_trans; [exact LXP|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HW CEIL); [exact GLO| lia]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact RS|]. split; [exact FR'| exact FSZ'].
  Qed.

  Lemma cenv_setbn : forall fr st bs m OW r b, cenv fr st bs m OW -> cenv fr st (setbn r b bs) m OW.
  Proof.
    intros fr st bs m OW r b (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ).
    unfold cenv. split; [exact HEAP|]. split; [exact AUX|]. split; [exact ST|]. split; [exact ERR|]. split; [exact MI|]. split; [exact LXP|].
    split; [exact FA|]. split; [exact SO|]. split; [eapply refs_stable_trans; [exact RS| apply refs_stable_setbn]|]. split; [exact FR| exact FSZ].
  Qed.

  Lemma cenv_final : forall fr st bs m OW,
    cenv fr st bs m OW -> lib_state bs m OW PL EA ->
    RHEAP st (OW ++ LB) m /\ lib_state bs m OW PL EA /\ rauxv_ok m B /\ (exists errv : word, rw_cells bgusegs m LX_ERRNO [C4 errv]) /\ mem_inv bgusegs m
    /\ lx_pres LB SPv (XW PL) m0 m /\ ps_fa st = ps_fa s0 /\ ps_so st = ps_so s0 /\ refs_stable bs0 OW0 bs OW.
  Proof. intros fr st bs m OW (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & _) LS. repeat (split; [assumption|]). assumption. Qed.

End Env.
End WithCeiling0.
