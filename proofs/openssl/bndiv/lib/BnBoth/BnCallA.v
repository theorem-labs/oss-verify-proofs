(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA UnwindA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma ax_pres_of_icall : forall Σ OW LB m m' SP X d n b,
  AHEAP Σ OW LB m -> In b OW -> blk_addr b <= d -> d + n <= blk_addr b + blk_size b -> ACEIL <= SP ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ ~ (d <= a < d + n)) m m' ->
  ax_pres LB SP X m m'.
Proof.
  intros Σ OW LB m m' SP X d n b HEAP Hb H1 H2 HSP AG. eapply agree_on_mono; [exact AG|]. intros x [_ Hc]. split.
  - destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]]; [left; exact Hc | right; left; exact Hc | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]].
  - intros HAr. destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]].
    + pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & BC & _). lia.
    + eapply (blk_not_static Σ OW LB m b x HEAP Hb); [lia | exact Hc].
    + assert (NE : blk_id b0 <> blk_id b).
      { intros E. pose proof (AH_nodup _ _ _ _ HEAP) as NDA. rewrite map_app in NDA.
        eapply (nodup_app_disj _ _ (blk_id b) NDA); [apply in_map; exact Hb | rewrite <- E; apply in_map; exact Hb0]. }
      pose proof (AH_disjoint_gen _ _ _ _ b0 b HEAP (in_or_app _ _ _ (or_intror Hb0)) (in_or_app _ _ _ (or_introl Hb)) NE) as DJ. lia.
Qed.

Section Env.
  (* [comment removed for export] *)
  Variables (LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo SPv FB : Z) (s0w raw : word) (rasO : option (list Z)) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : lstate bptr) (OW0 : list block) (m0 : mem).
  (* [comment removed for export] *)
  Definition cenv_ok : Prop :=
    ACEIL <= lo /\ lo <= FB /\ FB + 16 <= SPv /\ SPv + 16 <= USTACK_TOP /\ SPv mod 16 = 0 /\ FB mod 16 = 0
    /\ cnt_ok ls0 OW0 LB /\ TOTAL <= rt_credit RT Σ0.

  (* [comment removed for export] *)
  Definition uw_opt (m : mem) : Prop :=
    match rasO with Some ras => uw_chain USTACK_TOP m SPv (bv_unsigned s0w) ras | None => True end.

  Definition cenvA (pre : list cell) (used : Z) (Σ : rts RT) (ls : lstate bptr) (m : mem) (OW : list block) : Prop :=
    cenv_ok /\ AHEAP Σ OW LB m /\ stk bsegs m lo FB /\ mem_inv bsegs m
    /\ ax_pres LB SPv LIBW_A m0 m
    /\ rt_credit RT Σ0 - used <= rt_credit RT Σ
    /\ cnt_eq ls0 OW0 ls OW /\ refs_stable ls0 OW0 ls OW AD
    /\ rw_cells bsegs m FB (pre ++ [C8 s0w; C8 raw]) /\ Z.of_nat (cells_size pre) = SPv - FB - 16
    /\ uw_opt m.

  Lemma ESPvA : forall Σ OW m, cenv_ok -> AHEAP Σ OW LB m -> bv_unsigned (Z_to_bv 64 FB) = FB.
  Proof.
    intros Σ OW m (CEIL & LOFB & FBSP & SPT & _) H. pose proof (AH_ceil _ _ _ _ H) as (C1 & _). unfold SEGTOP_A, USTACK_TOP in *. apply unsigned_lit. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cenv_preA : forall pre used Σ ls m OW K C,
    cenvA pre used Σ ls m OW -> lib_state ls m OW AD EA -> lo <= FB - K -> used + C <= TOTAL ->
    bn_preA Σ ls m OW LB AD EA (Z_to_bv 64 FB) lo K C.
  Proof.
    intros pre used Σ ls m OW K C (OK & HEAP & ST & MI & _ & CR & CNT & _) LS HK HC.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0).
    unfold bn_preA. rewrite (ESPvA _ _ _ OK HEAP).
    split; [exact HEAP|]. split; [exact LS|]. split; [exact ST|]. split; [exact CEIL|]. split; [exact HK|].
    split; [lia|]. split; [exact FB16|]. split; [exact MI|]. split; [exact (cnt_ok_eq _ _ _ _ _ CNT0 CNT)| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma cenv_uwA : forall pre used Σ ls m OW ras, rasO = Some ras ->
    cenvA pre used Σ ls m OW -> uw_chain USTACK_TOP m FB SPv (bv_unsigned raw :: ras).
  Proof.
    intros pre used Σ ls m OW ras ER ((CEIL & LOFB & FBSP & SPT & SP16 & _) & _ & _ & _ & _ & _ & _ & _ & FR & FSZ & UW).
    unfold uw_opt in UW. rewrite ER in UW.
    apply (uw_push_frame m FB SPv (SPv - FB) pre (bv_unsigned raw) (bv_unsigned s0w) ras);
      [lia | lia | clear - SP16; Z.div_mod_to_equations; lia | lia | apply bv_unsigned_in_range | | exact UW].
    rewrite !Z_to_bv_bv_unsigned. replace (SPv + - (SPv - FB)) with FB by lia. exact FR.
  Qed.

  (* [comment removed for export] *)
  Definition cpostA (Σ : rts RT) (ls : lstate bptr) (m : mem) (OW : list block) (cost : Z)
      (Σ' : rts RT) (ls' : lstate bptr) (m' : mem) (OW' : list block) : Prop :=
    AHEAP Σ' OW' LB m' /\ lib_state ls' m' OW' AD EA /\ stk bsegs m' lo FB /\ mem_inv bsegs m'
    /\ ax_pres LB FB LIBW_A m m' /\ rt_credit RT Σ - cost <= rt_credit RT Σ'
    /\ cnt_eq ls OW ls' OW' /\ refs_stable ls OW ls' OW' AD.

  Lemma cpost_refsA : forall Σ ls m OW cost Σ' ls' m' OW', cpostA Σ ls m OW cost Σ' ls' m' OW' -> refs_stable ls OW ls' OW' AD.
  Proof. intros Σ ls m OW cost Σ' ls' m' OW' (_ & _ & _ & _ & _ & _ & _ & RS). exact RS. Qed.

  Lemma cenv_postA : forall pre used Σ ls m OW cost Σ' ls' m' OW',
    cenvA pre used Σ ls m OW -> cpostA Σ ls m OW cost Σ' ls' m' OW' -> cenvA pre (used + cost) Σ' ls' m' OW' /\ lib_state ls' m' OW' AD EA.
  Proof.
    intros pre used Σ ls m OW cost Σ' ls' m' OW' (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW)
           (HEAP' & LS' & ST' & MI' & AXP' & CR' & CNT' & RS').
    pose proof OK as (CEIL & LOFB & FBSP & SPT & _).
    split; [|exact LS'].
    assert (AG : agree_on (fun a => FB <= a < USTACK_TOP) m m').
    { eapply agree_on_mono; [exact AXP'|]. intros a Ha. cbv beta in Ha. split; [|left; lia].
      pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1.
      unfold LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
    unfold cenvA. split; [exact OK|]. split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|].
    split. { eapply ax_pres_trans; [exact AXP|]. eapply ax_pres_weaken; [exact AXP'| lia]. }
    split; [lia|].
    split; [eapply cnt_eq_trans; eauto|].
    split; [eapply refs_stable_trans; eauto|].
    split. { eapply rw_cells_agree; [exact AG | exact FR |]. intros a Ha. rewrite cells_size_app in Ha. cbn [cells_size csize Nat.add] in Ha.
             unfold USTACK_TOP in *. lia. }
    split; [exact FSZ|].
    unfold uw_opt in *. destruct rasO as [ras|]; [|exact I].
    apply (uw_chain_agree m m' ras SPv (bv_unsigned s0w) UW). eapply agree_on_mono; [exact AG|]. intros a Ha. cbv beta in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bn_postA_cpost : forall {A : Type} (ra gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
      Σ ls OW m cost (RES : A -> lstate bptr -> list block -> word -> Prop) (r : A * lstate bptr) Σ' ms',
    cenv_ok -> AHEAP Σ OW LB m ->
    bn_postA ra (Z_to_bv 64 FB) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Σ ls OW LB lo m AD EA cost RES r Σ' ms' ->
    exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' OW',
      ms' = MS (mkR ra (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ cpostA Σ ls m OW cost Σ' (snd r) m' OW' /\ RES (fst r) (snd r) OW' a0.
  Proof.
    intros A ra gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Σ ls OW m cost RES r Σ' ms' OK HEAP PO. unfold bn_postA in PO.
    destruct PO as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & fc' & m' & OW' & E & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    rewrite (ESPvA _ _ _ OK HEAP) in *.
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F', fc', m', OW'. split; [exact E|]. split; [|exact P9].
    unfold cpostA. repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma cenv_silentA : forall pre pre' used Σ ls m m' OW W,
    cenvA pre used Σ ls m OW -> munch W m m' -> wmono bsegs m m' -> Forall (w_lib OW lo SPv) W ->
    stk bsegs m' lo FB -> mem_inv bsegs m' ->
    rw_cells bsegs m' FB (pre' ++ [C8 s0w; C8 raw]) -> Z.of_nat (cells_size pre') = SPv - FB - 16 ->
    cenvA pre' used Σ ls m' OW.
  Proof.
    intros pre pre' used Σ ls m m' OW W (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) MU WM HW ST' MI' FR' FSZ'.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & _).
    unfold cenvA. split; [exact OK|]. split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HW CEIL ltac:(lia))|].
    split; [exact ST'|]. split; [exact MI'|].
    split. { eapply ax_pres_trans; [exact AXP|]. exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HW CEIL ltac:(lia)). }
    split; [exact CR|]. split; [exact CNT|]. split; [exact RS|]. split; [exact FR'|]. split; [exact FSZ'|].
    unfold uw_opt in *. destruct rasO as [ras|]; [|exact I].
    eapply uw_chain_munch_nw; [exact UW | exact MU |].
    eapply Forall_impl; [|exact HW]. intros [x y] [[H1 H2]|(b & Hb & H1 & H2)]; cbn [fst snd] in *; [exact H2|].
    pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & BC & _). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cenv_setbnA : forall pre used Σ ls m OW r b, cenvA pre used Σ ls m OW -> valid_refm r ls ->
    length (bn_blocks b) = length (bn_blocks (getbn r ls)) -> cenvA pre used Σ (setbn r b ls) m OW.
  Proof.
    intros pre used Σ ls m OW r b (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) HV HB.
    unfold cenvA. repeat (split; [assumption|]).
    split. { unfold cnt_eq in *. rewrite (cnt_bal_setbn r b ls OW OW HV), CNT, HB. lia. }
    split; [|repeat (split; [assumption|]); assumption].
    intros r0 a0 H0. apply ref_at_setbn. apply RS. exact H0.
  Qed.

  (* [comment removed for export] *)
  Lemma cenv_finalA : forall pre used Σ ls m OW,
    cenvA pre used Σ ls m OW -> lib_state ls m OW AD EA -> used <= TOTAL ->
    AHEAP Σ OW LB m /\ lib_state ls m OW AD EA /\ mem_inv bsegs m
    /\ ax_pres LB SPv LIBW_A m0 m /\ rt_credit RT Σ0 - TOTAL <= rt_credit RT Σ
    /\ cnt_eq ls0 OW0 ls OW /\ refs_stable ls0 OW0 ls OW AD.
  Proof.
    intros pre used Σ ls m OW (OK & HEAP & ST & MI & AXP & CR & CNT & RS & _) LS HU.
    split; [exact HEAP|]. split; [exact LS|]. split; [exact MI|]. split; [exact AXP|]. split; [lia|]. split; [exact CNT| exact RS].
  Qed.

End Env.
End WithRT.
