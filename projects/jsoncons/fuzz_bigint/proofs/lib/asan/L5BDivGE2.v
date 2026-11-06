(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5Cmp L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5BDivH L5BDivT L5BDivD L5BDivPH L5BDivPL L5BDivE L5BDivEA L5BDivHC L5BDivHD L5BDivHA L5BRed L5BDivHL L5BDivHL2 L5BDivHN L5BDivHO L5BDivGE L5DivSpecsAB0 L5DivInnerSpecsAB0 L5OpmodSpecsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGE2.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA. Import L5ADIVPH. Import L5ADIVPL. Import L5ADVHL. Import L5ADVHN. Import L5ADVHO. Import L5ADVHL2. Import L5ADVGE.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac algn := lazymatch goal with |- ?h _ (Zpos _) => is_const h; lazymatch h with Z.le => fail | Z.lt => fail | Z.ge => fail | Z.gt => fail | _ => assumption end end.
Local Ltac sc := first [ asm | rk | gmem | algn | (arith_goal; first [asm | blia]) | assumption ].

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Section DIV.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (E SCRD F fl ro r : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 384).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : aligned E 32.
Hypothesis HK : K [].
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 384 + 4784 <= SCRD.
Hypothesis FFR1 : ffrk 1 FF LK 4.
Hypothesis FFRS : ffrs FF E.
Hypothesis Hrsz : resize_spec L ar HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis Hasg : assign_spec L ar HI.
Variable cr0 : credit.
Hypothesis HH0 : ri_inv HI LB FF LK cr0 A M (vml_of model).
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 E.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation SH := (F / 8 + 2147450880).

Local Ltac open_ctx BI :=
  let PF := fresh "PF" in
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as PF;
  destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.




(* [comment removed for export] *)
Lemma gen_entry_ht (fx9 : FPState) g1 g2 R9 M9 model9 cr9 LK9 A9 c to qo qn bits rd bn bd wn wd bt wt bq wq d0 d1 :
  at20 L ar HI R M model LB FF LK A E SCRD F ro g1 g2 R9 M9 model9 cr9 LK9 A9 c to qo qn bits rd bn bd wn wd -> 0 <= c <= 1 ->
  L5ADVEA.tob LB M to bt wt -> aobj FF to 32 -> L5ADVEA.tob LB M qo bq wq -> aobj FF qo 32 -> L5.bo_dyn bn = L5.bo_dyn bt -> (L5.bo_dyn bq = true -> L5.bo_dyn bn = true) ->
  L5.bo_len bd = 1%nat -> (2 <= L5.bo_len bn)%nat -> L5.bo_st bd = L5.BInl d0 d1 -> 4294967296 <= d0 ->
  (forall (fx1 : FPState) R1 M1 model1, atG L ar HI R M model LB FF LK A E SCRD F ro g1 g2 R1 M1 model1 cr9 LK9 A9 to qo qn bits rd bn bd wn wd -> srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x930a8 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx9) R9 0x92c94 M9 model9) K.
Proof.
  intros A20 CR TT AOT TQ AOQ DYE DYQ LD1 LN2 STD D0R KF.
  eapply (L5ADVGE.atG_of_p4 L ar C HI LY HIok) with (toHT := true) (bt := bt) (wt := wt) (bq := bq) (wq := wq);
    try first [exact G | exact ER | exact EA | exact HSCR | exact HH0 | exact A20 | exact CR | exact TT | exact AOT | exact TQ | exact AOQ | exact DYE | exact DYQ | exact (conj LD1 LN2)].
  intros fx1 R1 M1 model1 (BI1 & RI1 & Y18 & Y21 & Y22 & Y25 & Y26 & Y27 & QNR & BITS & TN1 & TD1 & ON1 & OD1 & SGN & SGD & SP1 & DSH1 & HDR1) p11 TT1 TQ1 VW1. cbn iota.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr0 A M model qo 32 E SCRD HH0 AOQ ltac:(clear; lia) ltac:(reflexivity)) as ((QLO & QCE & QHI & Q8 & _) & QBIG & _).
  pose proof (proj1 TD1) as (_ & _ & _ & ST). rewrite STD in ST. destruct ST as (_ & D16 & _ & _ & D0H & _).
  pose proof (proj1 TT1) as (_ & _ & TL8 & TST).
  assert (LTR : 0 <= Z.of_nat (L5.bo_len bt) < 2 ^ 64). { destruct (L5.bo_st bt) as [v0 v1|cap q]. destruct TST as (_ & _ & _ & L2 & _). clear - L2; lia. destruct TST as (_ & _ & _ & LC & CRR & _). clear - LC CRR; lia. }
  assert (S264 : L5.u64_at RSEGS M1 (E - 120) (F + 48)).
  { pose proof (VW1 (E - 120) _ ltac:(left; reflexivity)) as X. unfold L5.bo_data in X. rewrite STD in X. replace (F + 48) with (F + 32 + 16) by (clear; lia). exact (proj1 X). }
  eapply (L5ADVHL2.ht L ar C HI LY HIok) with (toG := true) (qo := qo) (d0 := d0) (lent := Z.of_nat (L5.bo_len bt)); try first [exact G | exact ER | exact EA];
    [exact BI1 | exact RI1 | exact Y18 | exact p11 | exact S264 | exact (proj1 (SP1 _ _ ltac:(do 2 right; left; reflexivity))) | exact (proj1 (proj2 DSH1))
     | replace (F + 48) with (F + 32 + 16) by (clear; lia); exact D16 | clear - D0R D0H; lia | exact LTR | clear - QLO QHI; lia | ].
  intros fx2 R2 model2' BI2 KS2 q20 _. cbn iota in KS2 |- *.
  apply (KF fx2 R2 M1 model2').
  split. exact BI2. split. { apply (rinvD_ks R E R1 R2 KS_v5HTg RI1 KS2). vm_compute; reflexivity. }
  split. rewrite (KS2 18%nat) by inl. exact Y18. split. rewrite (KS2 21%nat) by inl. exact Y21. split. rewrite (KS2 22%nat) by inl. exact Y22. split. rewrite (KS2 25%nat) by inl. exact Y25.
  split. rewrite (KS2 26%nat) by inl. exact Y26. split. rewrite (KS2 27%nat) by inl. exact Y27.
  split. exact QNR. split. exact BITS. split. exact TN1. split. exact TD1. split. exact ON1. split. exact OD1. split. exact SGN. split. exact SGD. split. exact SP1. split. exact DSH1. exact HDR1.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGE2.
