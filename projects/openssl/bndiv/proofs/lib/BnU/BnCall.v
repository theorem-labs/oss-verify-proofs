(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnArr.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep BnIface.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Env.
  (* [comment removed for export] *)
  Variables (LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B SPv FB : Z).
  Variables (s0 : PState) (ls0 : lstate bptr) (OW0 : list block) (m0 : mem).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LOFB : lo <= FB.
  Hypothesis FBSP : FB <= SPv.
  Hypothesis SPB : SPv <= B.
  Hypothesis SPR : SPv < 2^64.

  Definition cenv (fr : list cell) (st : PState) (ls : lstate bptr) (m : mem) (OW : list block) : Prop :=
    RHEAP st (OW ++ LB) m /\ rauxv_ok m B /\ stk usegs m lo FB /\ (exists errv : word, rw_cells usegs m LX_ERRNO [C4 errv]) /\ mem_inv usegs m
    /\ lx_pres LB SPv LIBW_bn m0 m /\ ps_fa st = ps_fa s0 /\ ps_so st = ps_so s0 /\ refs_stable ls0 OW0 ls OW AD
    /\ rw_cells usegs m FB fr /\ Z.of_nat (cells_size fr) = SPv - FB.

  Lemma ESPv : bv_unsigned (Z_to_bv 64 FB) = FB.
  Proof using CEIL LOFB FBSP SPR. apply unsigned_lit. lia. Qed.

  (* [comment removed for export] *)
  Lemma cenv_pre : forall fr st ls m OW K,
    cenv fr st ls m OW -> lib_state ls m OW AD EA -> lo <= FB - K ->
    exists errv, bn_pre st ls m OW LB AD EA (Z_to_bv 64 FB) lo B errv K.
  Proof using CEIL GLO LOFB FBSP SPB SPR.
    intros fr st ls m OW K (HEAP & AUX & ST & (errv & ERR) & MI & _) LS HK. exists errv.
    unfold bn_pre. rewrite ESPv. repeat (split; [first [assumption | lia]|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Definition cpost (st : PState) (ls : lstate bptr) (m : mem) (OW : list block) (st' : PState) (ls' : lstate bptr) (m' : mem) (OW' : list block) : Prop :=
    RHEAP st' (OW' ++ LB) m' /\ lib_state ls' m' OW' AD EA /\ rauxv_ok m' B /\ stk usegs m' lo FB
    /\ (exists errv' : word, rw_cells usegs m' LX_ERRNO [C4 errv']) /\ mem_inv usegs m'
    /\ lx_pres LB FB LIBW_bn m m' /\ ps_fa st' = ps_fa st /\ ps_so st' = ps_so st /\ refs_stable ls OW ls' OW' AD.

  Lemma cpost_refs : forall st ls m OW st' ls' m' OW', cpost st ls m OW st' ls' m' OW' -> refs_stable ls OW ls' OW' AD.
  Proof. intros st ls m OW st' ls' m' OW' (_ & _ & _ & _ & _ & _ & _ & _ & _ & RS). exact RS. Qed.

  Lemma cenv_post : forall fr st ls m OW st' ls' m' OW',
    cenv fr st ls m OW -> cpost st ls m OW st' ls' m' OW' -> cenv fr st' ls' m' OW' /\ lib_state ls' m' OW' AD EA.
  Proof using CEIL GLO LOFB FBSP.
    intros fr st ls m OW st' ls' m' OW' (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ)
           (HEAP' & LS' & AUX' & ST' & ERR' & MI' & LXP' & FA' & SO' & RS').
    split; [|exact LS'].
    unfold cenv. split; [exact HEAP'|]. split; [exact AUX'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact MI'|].
    split. { eapply lx_pres_trans; [exact LXP|]. eapply lx_pres_weaken; [exact LXP'| exact FBSP| auto| auto]. }
    split; [congruence|]. split; [congruence|].
    split; [eapply refs_stable_trans; eauto|].
    split; [|exact FSZ].
    eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP' | exact FR |].
    intros a Ha. split; [|left; lia]. unfold LIBW_bn. cbn [rin_ivs fst snd]. unfold GLOBALS_TOP in GLO. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bn_post_cpost : forall {A : Type} (ra gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      st ls OW m (RES : A -> lstate bptr -> list block -> word -> Prop) (r : A * lstate bptr) st' ms',
    bn_post ra (Z_to_bv 64 FB) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc st ls OW LB lo B m AD EA RES r st' ms' ->
    exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' OW',
      ms' = MS (mkR ra (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ cpost st ls m OW st' (snd r) m' OW' /\ RES (fst r) (snd r) OW' a0.
  Proof using CEIL LOFB FBSP SPR.
    intros A ra gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc st ls OW m RES r st' ms' PO. unfold bn_post in PO.
    destruct PO as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & OW' & errv' & E & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11).
    rewrite ESPv in *.
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', OW'. split; [exact E|]. split; [|exact P11].
    unfold cpost. repeat (split; [first [assumption | exists errv'; assumption]|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma cenv_silent : forall fr fr' st ls m m' OW W (errv' : word),
    cenv fr st ls m OW -> munch W m m' -> wmono usegs m m' -> Forall (w_lib OW lo SPv) W ->
    stk usegs m' lo FB -> rw_cells usegs m' LX_ERRNO [C4 errv'] -> mem_inv usegs m' ->
    rw_cells usegs m' FB fr' -> Z.of_nat (cells_size fr') = SPv - FB ->
    cenv fr' st ls m' OW.
  Proof using CEIL GLO LOFB FBSP SPB.
    intros fr fr' st ls m m' OW W errv' (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ) MU WM HW ST' ERR' MI' FR' FSZ'.
    unfold cenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HW CEIL)|].
    split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HW SPB); exact GLO|].
    split; [exact ST'|]. split; [exists errv'; exact ERR'|]. split; [exact MI'|].
    split. { eapply lx_pres_trans; [exact LXP|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HW CEIL); [exact GLO| lia]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact RS|]. split; [exact FR'| exact FSZ'].
  Qed.

  (* [comment removed for export] *)
  Lemma cenv_setbn : forall fr st ls m OW r b, cenv fr st ls m OW -> cenv fr st (setbn r b ls) m OW.
  Proof.
    intros fr st ls m OW r b (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ).
    unfold cenv. repeat (split; [assumption|]). split; [|split; assumption].
    intros r0 a0 H0. apply ref_at_setbn. apply RS. exact H0.
  Qed.

  (* [comment removed for export] *)
  Lemma cenv_final : forall fr st ls m OW,
    cenv fr st ls m OW -> lib_state ls m OW AD EA ->
    RHEAP st (OW ++ LB) m /\ lib_state ls m OW AD EA /\ rauxv_ok m B /\ (exists errv : word, rw_cells usegs m LX_ERRNO [C4 errv]) /\ mem_inv usegs m
    /\ lx_pres LB SPv LIBW_bn m0 m /\ ps_fa st = ps_fa s0 /\ ps_so st = ps_so s0 /\ refs_stable ls0 OW0 ls OW AD.
  Proof. intros fr st ls m OW (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & _) LS. repeat (split; [assumption|]). assumption. Qed.

End Env.
End WithCeiling0.
