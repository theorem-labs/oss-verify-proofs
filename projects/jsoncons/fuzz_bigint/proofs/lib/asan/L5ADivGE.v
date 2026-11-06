(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5Cmp L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5AFrameK L5DivKitA L5ADivH L5ADivT L5ADivD L5ADivPH L5ADivPL L5ADivE L5ADivEA L5ADivHC L5ADivHD L5ADivHA L5ARed L5ADivHL L5ADivHN L5ADivHO L5DivSpecsA L5DivInnerSpecsA L5OpmodSpecsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGE.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA. Import L5ADIVPH. Import L5ADIVPL. Import L5ADVHL. Import L5ADVHN. Import L5ADVHO.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Section DIV.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (E SCRD F fl ro r : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 352).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : aligned E 32.
Hypothesis HK : K [].
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 352 + 4656 <= SCRD.
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
  destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.




(* [comment removed for export] *)
Definition atG (g1 g2 : growth) (Rc : bvmap 5 word) (Mc : word -> option byte) (modelc : Model) (crc : credit) (LKc : list fframe) (Ac : list (Z * Z))
           (to qo qn bits rd : Z) (bn bd : L5.bigobj) (wn wd : list Z) : Prop :=
  binv [] (bx12 g1 g2) Mc modelc LKc crc Ac /\ rinvD R E Rc
  /\ getr Rc (reg 18) = Z_to_bv 64 SH /\ getr Rc (reg 22) = Z_to_bv 64 qo /\ getr Rc (reg 24) = Z_to_bv 64 to /\ getr Rc (reg 25) = getr R (reg 25)
  /\ getr Rc (reg 26) = Z_to_bv 64 (L5.bo_data (F + 32) bd)
  /\ 0 <= qn <= 1 /\ (bits = 0 \/ bits = 2)
  /\ L5ADVEA.tob (bx12 g1 g2 ++ LB) Mc (F + 96) bn wn /\ L5ADVEA.tob (bx12 g1 g2 ++ LB) Mc (F + 32) bd wd
  /\ obj_at Mc (F + 96) bn (on_of g2) /\ obj_at Mc (F + 32) bd (on_of g1)
  /\ Z.testbit (L5.bo_fb bn) 1 = false /\ Z.testbit (L5.bo_fb bd) 1 = false
  /\ spl E Mc [(E - 264, F + 32); (E - 304, rd); (E - 248, qo); (E - 208, to); (E - 288, bits); (E - 272, F + 96); (E - 312, qn); (E - 296, F)]
  /\ dsh Mc F 0 248 248 248 248 /\ L5.u64_at RSEGS Mc F 1102416563.

(* [comment removed for export] *)
Lemma atG_of_p4 (fx9 : FPState) g1 g2 R9 M9 model9 cr9 LK9 A9 c to qo qn bits rd bn bd wn wd bt wt (toHT : bool) :
  at20 L ar HI R M model LB FF LK A E SCRD F ro g1 g2 R9 M9 model9 cr9 LK9 A9 c to qo qn bits rd bn bd wn wd -> 0 <= c <= 1 ->
  L5ADVEA.tob LB M to bt wt -> aobj FF to 32 -> aobj FF qo 32 -> L5.bo_dyn bn = L5.bo_dyn bt ->
  (if toHT then L5.bo_len bd = 1%nat /\ (2 <= L5.bo_len bn)%nat else (2 <= L5.bo_len bd)%nat) ->
  (forall (fx1 : FPState) R1 M1 model1,
      atG g1 g2 R1 M1 model1 cr9 LK9 A9 to qo qn bits rd bn bd wn wd ->
      getr R1 (reg 10) = Z_to_bv 64 (to + 8) -> L5ADVEA.tob (bx12 g1 g2 ++ LB) M1 to bt wt ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 (if toHT then 0x9267c else 0x926d8) M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx9) R9 0x92374 M9 model9) K.
Proof.
  intros (BI9 & RIH9 & c10 & c19 & c20 & c22 & c24 & c26 & QNR & BITS & TN9 & TD9 & ON9 & OD9 & SGN & SGD & S88 & S48 & S104 & S144 & S64 & DSH9 & HDR9) CR TT AOT AOQ DYE DISP KF.
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHQ : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (hnf in ALF; clear - FRP ALF; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof RIH9 as (RI9 & X18 & X23 & X27 & X25).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr0 A M model qo 32 E SCRD HH0 AOQ ltac:(clear; lia) ltac:(reflexivity)) as ((QLO & QCE & QHI & Q8 & _) & QBIG & _).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (TT9 : L5ADVEA.tob (bx12 g1 g2 ++ LB) M9 to bt wt). { eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI9 | exact AOT | exact TT | ]. intros a _ rr []. }
  pose proof (proj1 TD9) as (_ & _ & _ & STD9).
  assert (LDR : 0 <= Z.of_nat (L5.bo_len bd) < 2 ^ 64). { destruct (L5.bo_st bd) as [v0 v1|cap q]. destruct STD9 as (_ & _ & _ & L2 & _). clear - L2; lia. destruct STD9 as (_ & _ & _ & LC & CRR & _). clear - LC CRR; lia. }
  eapply L5ADVHN.p4n with (toHT := toHT) (bn := bn) (bt := bt) (lend := Z.of_nat (L5.bo_len bd)) (qo := qo) (qn := qn) (c := c) (to := to); try first [exact LY | exact HIok | exact G | exact ER | exact EA];
    [exact BI9 | exact RI9 | exact X27 | exact c10 | exact CR | exact c19 | exact c20 | exact c22 | exact QNR | exact c24 | exact S104 | exact S144 | clear - QLO QHI; lia
     | exact (proj1 TN9) | exact (proj1 TT9) | exact AOT | exact (proj1 (proj2 (proj2 TT9))) | exact DYE | | ].
  { destruct toHT. destruct DISP as (L1 & L2). split. rewrite L1; reflexivity. exact L2. clear - DISP LDR. lia. }
  intros fx1 R1 M1 model1 BI1 KS1 p10 p11 p21 p22 p24 p27 AG1 S80_1 S40_1 S56_1.
  set (X1 := fun a => (E - 272 <= a < E - 264) \/ (E - 312 <= a < E - 304) \/ (E - 296 <= a < E - 288)).
  assert (OFF1 : L5ADVEA.offx L ar FF E F (bx12 g1 g2 ++ LB) 0 X1 M9 M1).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG1. exact Ha. all: intros Q; apply NX; subst X1; cbn beta; clear - Q; lia. }
  assert (KPS : forall a v, E - 352 <= a -> a + 8 <= E -> (a = E - 264 \/ a = E - 304 \/ a = E - 248 \/ a = E - 208 \/ a = E - 288) -> L5.u64_at RSEGS M9 a v -> L5.u64_at RSEGS M1 a v).
  { intros a v H1 H2 H3 Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - H1 ER; lia. 2: clear - H2 ER; lia. intros i Hi. apply AG1. clear - Hi H1 H2 ER; lia. all: clear - Hi H3; lia. }
  pose proof BI9 as (B1_9 & _).
  assert (TKP : forall o b ws, aobj FF' o 32 -> L5ADVEA.tob (bx12 g1 g2 ++ LB) M9 o b ws -> L5ADVEA.tob (bx12 g1 g2 ++ LB) M1 o b ws).
  { intros o b ws AOB TO. eapply L5ADVEA.tob_keep'; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact B1_9 | exact AOB | exact TO | exact OFF1 | intros cap q Eq; split; apply (proj2 (proj2 (proj2 TO)) cap q Eq) | ].
    intros a OR. pose proof (oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] _ M9 model9 LK9 cr9 A9 o b ws a BI9 AOB TO OR) as N1.
    subst X1; cbn beta. clear - N1 HSCR. lia. }
  assert (KPF : forall i, F <= i < F + 512 -> M1 (Z_to_bv 64 i) = M9 (Z_to_bv 64 i)). { intros i Hi. apply AG1. clear - Hi FRP; lia. all: clear - Hi SFB; lia. }
  apply (KF fx1 R1 M1 model1).
  - split. exact BI1. split. { apply (rinvD_ks R E R9 R1 KSP4 RI9 KS1). vm_compute; reflexivity. }
    split. rewrite (KS1 18%nat) by inl. exact X18. split. exact p22. split. exact p24. split. rewrite (KS1 25%nat) by inl. exact X25. split. rewrite (KS1 26%nat) by inl. exact c26.
    split. exact QNR. split. exact BITS. split. exact (TKP _ _ _ AON' TN9). split. exact (TKP _ _ _ AOD' TD9).
    split. { apply (obj_at_agree M9 M1 _ _ _ ON9 ltac:(clear - FRP; lia) ltac:(clear - FRP; lia)). intros i Hi. apply KPF. clear - Hi; lia. }
    split. { apply (obj_at_agree M9 M1 _ _ _ OD9 ltac:(clear - FRP; lia) ltac:(clear - FRP; lia)). intros i Hi. apply KPF. clear - Hi; lia. }
    split. exact SGN. split. exact SGD.
    split. { intros a v Hin. cbn [In] in Hin. destruct Hin as [Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[]]]]]]]]]; injection Eq as <- <-; (split; [|clear; lia]).
             apply KPS; [clear; lia | clear; lia | clear; lia | exact S88]. apply KPS; [clear; lia | clear; lia | clear; lia | exact S48].
             apply KPS; [clear; lia | clear; lia | clear; lia | exact S104]. apply KPS; [clear; lia | clear; lia | clear; lia | exact S144].
             apply KPS; [clear; lia | clear; lia | clear; lia | exact S64]. exact S80_1. exact S40_1. exact S56_1. }
    split. { eapply dsh_keep; [exact G | exact ER | exact DSH9 | exact OFF1 | ]. intros j Hj. subst X1; cbn beta. clear - Hj SHQ ER. lia. }
    eapply hdr_keep; [exact G | exact HDR9 | exact OFF1 | ]. intros i Hi. subst X1; cbn beta. clear - Hi ER SFB. lia.
  - exact p10.
  - eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI1 | exact AOT | exact TT | ]. intros a _ rr [].
Qed.

(* [comment removed for export] *)
Lemma gen_entry_p4 (fx9 : FPState) g1 g2 R9 M9 model9 cr9 LK9 A9 c to qo qn bits rd bn bd wn wd bt wt :
  at20 L ar HI R M model LB FF LK A E SCRD F ro g1 g2 R9 M9 model9 cr9 LK9 A9 c to qo qn bits rd bn bd wn wd -> 0 <= c <= 1 ->
  L5ADVEA.tob LB M to bt wt -> aobj FF to 32 -> aobj FF qo 32 -> L5.bo_dyn bn = L5.bo_dyn bt -> (2 <= L5.bo_len bd)%nat ->
  (forall (fx1 : FPState) R1 M1 model1, atG g1 g2 R1 M1 model1 cr9 LK9 A9 to qo qn bits rd bn bd wn wd -> srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x926d8 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx9) R9 0x92374 M9 model9) K.
Proof.
  intros A20 CR TT AOT AOQ DYE LD KF.
  apply (atG_of_p4 fx9 g1 g2 R9 M9 model9 cr9 LK9 A9 c to qo qn bits rd bn bd wn wd bt wt false A20 CR TT AOT AOQ DYE LD).
  intros fx1 R1 M1 model1 AG _ _. exact (KF fx1 R1 M1 model1 AG).
Qed.

(* [comment removed for export] *)
Lemma gen_entry_ht (fx9 : FPState) g1 g2 R9 M9 model9 cr9 LK9 A9 c to qo qn bits rd bn bd wn wd bt wt d0 d1 :
  at20 L ar HI R M model LB FF LK A E SCRD F ro g1 g2 R9 M9 model9 cr9 LK9 A9 c to qo qn bits rd bn bd wn wd -> 0 <= c <= 1 ->
  L5ADVEA.tob LB M to bt wt -> aobj FF to 32 -> aobj FF qo 32 -> L5.bo_dyn bn = L5.bo_dyn bt ->
  L5.bo_len bd = 1%nat -> (2 <= L5.bo_len bn)%nat -> L5.bo_st bd = L5.BInl d0 d1 -> 4294967296 <= d0 ->
  (forall (fx1 : FPState) R1 M1 model1, atG g1 g2 R1 M1 model1 cr9 LK9 A9 to qo qn bits rd bn bd wn wd -> srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x926d8 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx9) R9 0x92374 M9 model9) K.
Proof.
  intros A20 CR TT AOT AOQ DYE LD1 LN2 STD D0R KF.
  apply (atG_of_p4 fx9 g1 g2 R9 M9 model9 cr9 LK9 A9 c to qo qn bits rd bn bd wn wd bt wt true A20 CR TT AOT AOQ DYE (conj LD1 LN2)).
  intros fx1 R1 M1 model1 (BI1 & RI1 & Y18 & Y22 & Y24 & Y25 & Y26 & QNR & BITS & TN1 & TD1 & ON1 & OD1 & SGN & SGD & SP1 & DSH1 & HDR1) p10 TT1.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr0 A M model qo 32 E SCRD HH0 AOQ ltac:(clear; lia) ltac:(reflexivity)) as ((QLO & QCE & QHI & Q8 & _) & QBIG & _).
  pose proof (proj1 TD1) as (_ & _ & _ & ST). rewrite STD in ST. destruct ST as (_ & D16 & _ & _ & D0H & _).
  pose proof (proj1 TT1) as (_ & _ & TL8 & TST).
  assert (LTR : 0 <= Z.of_nat (L5.bo_len bt) < 2 ^ 64). { destruct (L5.bo_st bt) as [v0 v1|cap q]. destruct TST as (_ & _ & _ & L2 & _). clear - L2; lia. destruct TST as (_ & _ & _ & LC & CRR & _). clear - LC CRR; lia. }
  eapply L5ADVHL.ht with (toG := true) (to := to) (qo := qo) (d0 := d0) (lent := Z.of_nat (L5.bo_len bt)); try first [exact LY | exact HIok | exact G | exact ER | exact EA];
    [exact BI1 | exact RI1 | exact p10 | exact Y22 | rewrite Y26; unfold L5.bo_data; rewrite STD; f_equal; clear; lia | exact (proj1 (SP1 _ _ ltac:(do 7 right; left; reflexivity)))
     | exact (proj1 (proj2 DSH1)) | replace (F + 48) with (F + 32 + 16) by (clear; lia); exact D16 | clear - D0R D0H; lia | exact AOT | exact (proj1 (proj2 (proj2 TT1))) | exact TL8 | exact LTR | clear - QLO QHI; lia | ].
  intros fx2 R2 model2' BI2 KS2 q23 _. cbn iota in KS2 |- *.
  apply (KF fx2 R2 M1 model2').
  split. exact BI2. split. { apply (rinvD_ks R E R1 R2 KS_v5HTg RI1 KS2). vm_compute; reflexivity. }
  split. rewrite (KS2 18%nat) by inl. exact Y18. split. rewrite (KS2 22%nat) by inl. exact Y22. split. rewrite (KS2 24%nat) by inl. exact Y24. split. rewrite (KS2 25%nat) by inl. exact Y25.
  split. rewrite (KS2 26%nat) by inl. exact Y26.
  split. exact QNR. split. exact BITS. split. exact TN1. split. exact TD1. split. exact ON1. split. exact OD1. split. exact SGN. split. exact SGD. split. exact SP1. split. exact DSH1. exact HDR1.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGE.
