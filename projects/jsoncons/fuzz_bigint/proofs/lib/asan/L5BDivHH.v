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
     L5Cmp L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5BDivH L5BDivT L5BDivD L5BDivPH L5BDivE L5BDivEA L5BDivHC L5BDivHD L5BDivHA L5BDivHN.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVHH.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA. Import L5ADIVPH. Import L5ADVHN.
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
Lemma resize_stage (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac o pcn (n : nat) b ws :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 10) = Z_to_bv 64 o -> getr Rc (reg 11) = Z_to_bv 64 (Z.of_nat n) -> getr Rc (reg 1) = Z_to_bv 64 pcn -> L5.ra_ok pcn ->
  L5.big_at RSEGS Mc o b -> L5C.obj_limbs RSEGS Mc b ws -> aobj FF o 32 -> shadow_zero Mc o 4 ->
  Z.of_nat n <= 2 ^ 23 ->
  (L5.bo_dyn b = true -> Z.of_nat n <= L5.bo_cap b) ->
  ((3 <= n)%nat -> L5.bo_dyn b = false -> acredit_ok L crc (8 * round_up (Z.of_nat n))) ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(o, 32); (L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b), 8 * Z.max 0 (Z.of_nat n - Z.of_nat (L5.bo_len b)))] a) ->
  (forall (fx' : FPState) R' M' model' (g : growth) LBn cr' LK' A',
      resize_post L ar (BX ++ LB) FF' LK' crc Mc M' Rc R' o SPA n b ws g LBn cr' ->
      binv W1 (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' pcn M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc RESIZE Mc modelc) K.
Proof.
  intros BI RI X10 X11 X1 RAn OB OL AOB SZ LEN CAPOK CROK INB WSUB KF.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  edestruct L5ADVEA.callee_pre with (SCRc := RESIZE_SCR) as (STKc & ROOMc & RSc & A32c); [exact HIok | exact EA | exact FFR1 | exact FFRS | exact BI | vm_compute; discriminate | clear - HSCR; change RESIZE_SCR with 4496; lia | ].
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac o BI AOB SZ)
    as ((ORP & ORG & O8) & OBIG & _ & _ & OFR & OF & OSH & _).
  pose proof RI as (Z2 & _ & _ & _ & Z4 & _).
  assert (OCR : forall a, docell E a -> SPA <= a < E). { destruct G as [_ _ _ _ _ OCR0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. exact OCR0. }
  apply (Hrsz fx Rc Mc modelc K (BX ++ LB) FF' LKc crc Ac o SPA pcn n b ws B1 B2 HK).
  - rewrite r10. exact X10.
  - rewrite r11. exact X11.
  - exact LEN.
  - exact CAPOK.
  - exact CROK.
  - rewrite r1. exact X1.
  - exact RAn.
  - rewrite r2. exact Z2.
  - exact A32c.
  - rewrite r4, Z4. rewrite <- G4. reflexivity.
  - exact STKc.
  - apply (ffrk_le 1 FF' LKc 4 4 ROOMc). clear; lia.
  - exact RSc.
  - exact OB.
  - exact OL.
  - apply aobj_cons. exact AOB.
  - exact SZ.
  - exact INB.
  - intros fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST RT3 IA3 AM3 ILK3 HH3.
    assert (BI3 : binv W1 (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M3 model3 LK3 cr3 A3).
    { pose proof POST as (_ & PG).
      destruct g as [|qn capn].
      - destruct PG as (DY & ELB & _ & _ & AH3). subst LBn.
        apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
                 W W1 BX BX BX Mc modelc LKc crc Ac M3 model3 LK3 cr3 A3 RESIZE_SCR _ BI AH3 HH3 AM3 RT3 IA3 ILK3).
        + vm_compute; discriminate.
        + clear - HSCR; change RESIZE_SCR with 4496; lia.
        + intros rr a [Hr|[Hr|[]]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR.
          * split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR. lia. }
            change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH. lia.
          * destruct b as [fb len sto]. destruct sto as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_st L5.bo_len] in IR.
            -- assert (LE2 : (n <= 2)%nat).
               { destruct DY as [DY|DY]. 2: exact DY. exfalso. destruct OB as (_ & _ & _ & (BT & _)). unfold L5.bo_dyn in DY. cbn [L5.bo_fb] in DY, BT. rewrite BT in DY. discriminate DY. }
               split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR LE2. lia. }
               change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH LE2. lia.
            -- assert (CAPB : Z.of_nat n <= cap).
               { apply CAPOK. destruct OB as (_ & _ & _ & (BT & _)). unfold L5.bo_dyn. cbn [L5.bo_fb]. exact BT. }
               edestruct L5ADVEA.blk_avoid with (a := a) as (Y1 & Y2 & _); try first [exact LY | exact HIok | exact G | exact HSCR]; [exact BI | exact (INB cap q eq_refl) | clear - IR CAPB; lia | ].
               split. exact Y1. exact Y2.
        + intros a _ X. exact (proj2 (WSUB a X)).
        + intros a X. exact (proj1 (WSUB a X)).
      - destruct PG as (_ & _ & _ & ELB & _ & _ & _ & _ & AH3). subst LBn.
        apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
                 W W1 BX BX ((qn, 8 * capn) :: BX) Mc modelc LKc crc Ac M3 model3 LK3 cr3 A3 RESIZE_SCR _ BI AH3 HH3 AM3 RT3 IA3 ILK3).
        + vm_compute; discriminate.
        + clear - HSCR; change RESIZE_SCR with 4496; lia.
        + intros rr a [Hr|[]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR.
          split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR. lia. }
          change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH. lia.
        + intros a _ X rr [Hr|[]]. subst rr. apply (proj2 (WSUB a X) (o, 32)). left; reflexivity.
        + intros a X. exact (proj1 (WSUB a X)). }
    apply (KF fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST BI3 IA3 ILK3).
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVHH.
