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
     L5Cmp L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5BDivH L5BDivT L5BDivD L5BDivPH L5BDivE L5BDivEA L5BDivHC L5BDivHD L5BDivHA L5BRed.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVHL.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA. Import L5ADIVPH.
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
Lemma word_of_defined (Mk : word -> option byte) a : L5.defined Mk a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> exists w, L5.u64_at RSEGS Mk a w /\ 0 <= w < 2 ^ 64.
Proof.
  intros D Ha Hb. destruct (L5SA.limbs_of_defined Mk a 1 ltac:(exact D) Ha ltac:(clear - Hb; lia)) as (ws & Lw & Rw & LA).
  destruct ws as [|w [|]]; cbn in Lw; try (exfalso; clear - Lw; lia). exists w. split. pose proof (LA 0%nat ltac:(cbn; clear; lia)) as X. rewrite Z.mul_0_r, Z.add_0_r in X. exact X.
  inversion Rw. assumption.
Qed.
(* [comment removed for export] *)
Lemma arg_shz cr0 W BX Mc modelc LKc crc Ac o : ri_inv HI LB FF LK cr0 A M (vml_of model) ->
  binv W BX Mc modelc LKc crc Ac -> aobj FF o 32 -> shadow_zero M o 4 -> (forall j, 0 <= j < 4 -> L5.outside W (o / 8 + SB + j)) -> shadow_zero Mc o 4.
Proof.
  intros HH0 (_ & _ & _ & _ & _ & _ & EK & _) AOB SZ NW.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr0 A M model o 32 E SCRD HH0 AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OCLSH.
  intros j Hj. unfold byte_at. rewrite EK. apply SZ. exact Hj. split.
  unfold S, SB. clear - Hj OR OBIG. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  split. unfold S. apply OCLSH. exact Hj. unfold S. apply NW. exact Hj.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Definition spl (Mk : word -> option byte) (cells : list (Z * Z)) : Prop := forall a v, In (a, v) cells -> L5.u64_at RSEGS Mk a v /\ SPA <= a /\ a + 8 <= E.
Lemma spl_keep LBx scr (X : Z -> Prop) Mc M1 cells : spl Mc cells -> L5ADVEA.offx L ar FF E F LBx scr X Mc M1 -> (forall i, SPA <= i < E -> ~ X i) -> spl M1 cells.
Proof.
  intros SP OFF NX a v Hin. destruct (SP a v Hin) as (Hc & H1 & H2). split. 2: split; assumption.
  eapply L5ADVEA.spill_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact Hc | exact H1 | exact H2 | exact OFF | ]. intros i Hi. apply NX. clear - Hi H1 H2. lia.
Qed.
Lemma spl_vis W BX Mc modelc LKc crc Ac cells a v : binv W BX Mc modelc LKc crc Ac -> spl Mc cells -> In (a, v) cells -> L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) a v.
Proof.
  intros BI SP Hin. destruct (SP a v Hin) as (Hc & H1 & H2). open_ctx BI.
  apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact SV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 ER; lia) ltac:(clear - H2 ER; lia))). exact Hc.
Qed.
(* [comment removed for export] *)
Lemma shz_vis W BX Mc modelc LKc crc Ac off n k : binv W BX Mc modelc LKc crc Ac -> shr8 Mc F off n 0 -> 0 <= off -> off + n <= 64 -> k = 2147450880 + off ->
  L5KA.zeros_at (mrestrict (ahid Ac modelc) Mc) (F / 8 + k) n.
Proof.
  intros BI SHR O1 O2 -> i Hi. open_ctx BI.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SQ : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (hnf in ALF; clear - FRP ALF; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply byte_of_u8. 2: right; clear - SQ O1 Hi; lia. 2: clear - SQ O1 O2 Hi; lia.
  apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F / 8 + (2147450880 + off) + i) 0 ltac:(eapply avis_sub; [exact SHV | unfold SB; clear - O1 Hi; lia | unfold SB; clear - O1 O2 Hi; lia]) ltac:(clear - SQ O1 Hi; lia) ltac:(clear - SQ O1 O2 Hi; lia))).
  pose proof (SHR i Hi) as U8. unfold SB in U8. replace (F / 8 + (2147450880 + off) + i) with (F / 8 + 2147450880 + off + i) by (clear; lia). exact U8.
Qed.

End DIV.
End WithIface.
End SCFG_1.
End L5ADVHL.
