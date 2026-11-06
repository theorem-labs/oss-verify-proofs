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
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BCopy L5BDetailG L5BDetailK L5BFrameK L5DivKitAB0 L5BDivH L5BDivT L5BDivD L5BDivPE L5BDivE.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVEA.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADIVPE.
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
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis Hasg : assign_spec L ar HI.

Section DIV.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (E SCRD F fl ro r : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 384).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : aligned E 32.
Hypothesis HK : K [].
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 E.
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 384 + 4784 <= SCRD.
Hypothesis FFR1 : ffrk 1 FF LK 4.
Hypothesis FFRS : ffrs FF E.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation Gx := (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G).
Local Notation SH := (F / 8 + 2147450880).

(* [comment removed for export] *)
Lemma callee_pre W BX Mc modelc LKc crc Ac SCRc : binv W BX Mc modelc LKc crc Ac -> 0 <= SCRc -> SCRc + 384 <= SCRD ->
  astk ar Mc SPA SCRc /\ ffrk 1 FF' LKc 4 /\ ffrs FF' SPA /\ SPA mod 32 = 0.
Proof.
  intros (B1 & B2 & B3 & B4 & B5 & B6 & _) HS0 HS.
  assert (SA : (E - 384) mod 16 = 0 /\ (E - 384) mod 32 = 0). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF.
  assert (ND : NoDup (map ff_addr (FF' ++ LKc))). { clear - WF. decompose [and] WF. assumption. }
  split. { apply (astk_sub ar Mc Mc E SCRD 384 SCRc B6 (mem_grows_refl Mc)). clear; lia. exact HS0. clear - HS; lia. exact (proj1 SA). }
  split. { apply (ffrk_push_other 1 FF LK LKc (F, 3, SPA + 32) 4). cbn [ff_class fst snd]. clear; lia. exact FFR1. exact B5. exact ND. }
  split. { apply (ffrs_push FF E). exact FFRS. clear; lia. clear; lia. }
  exact (proj2 SA).
Qed.

(* [comment removed for export] *)
Lemma blk_avoid W BX Mc modelc LKc crc Ac q n a : binv W BX Mc modelc LKc crc Ac -> In (q, n) (BX ++ LB) -> q <= a < q + n ->
  ~ docell E a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 3 / 8) /\ ~ (SPA <= a < E).
Proof.
  intros (B1 & _) IN Ha. change (ff_bytes 3 / 8) with 64.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
  pose proof (proj1 (WB _ IN)) as (X1 & _ & _ & X4 & X5 & (X6 & X7 & X8)). cbn [fst snd] in *.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  assert (NS : ~ (SPA <= a < E)) by (clear - Ha X5 SLO HSCR; lia).
  split. { intros D. apply NS. unfold docell in D. clear - D. lia. }
  split. 2: exact NS.
  unfold SB, BIGSHADOW_LO, BIGSHADOW_HI in *. change (ff_bytes 3) with 512 in *.
  assert (Q : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416).
  { clear - FR F8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  clear - Ha X7 Q. lia.
Qed.

(* [comment removed for export] *)
Lemma loc_aobj k : 32 <= k -> k + 32 <= 504 -> k mod 8 = 0 -> aobj FF' (F + k) 32.
Proof.
  intros K1 K2 K8. exists (F, 3, SPA + 32). split. left; reflexivity. cbn [ff_addr ff_class fst snd]. change (ff_bytes 3) with 512.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  split. clear - K1; lia. split. clear - K2; lia.
  clear - F32 K8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma assign_stage (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac o k pcn b b' ws' :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 10) = Z_to_bv 64 o -> getr Rc (reg 11) = Z_to_bv 64 (F + k) -> getr Rc (reg 1) = Z_to_bv 64 pcn -> L5.ra_ok pcn ->
  32 <= k -> k + 32 <= 504 -> k mod 8 = 0 ->
  L5.big_at RSEGS Mc o b -> aobj FF o 32 -> shadow_zero Mc o 4 ->
  L5.big_at RSEGS Mc (F + k) b' -> L5C.obj_limbs RSEGS Mc b' ws' -> shadow_zero Mc (F + k) 4 ->
  Z.of_nat (L5.bo_len b') <= 2 ^ 23 ->
  (L5.bo_dyn b = true -> Z.of_nat (L5.bo_len b') <= L5.bo_cap b) ->
  ((3 <= L5.bo_len b')%nat -> L5.bo_dyn b = false -> acredit_ok L crc (8 * round_up (Z.of_nat (L5.bo_len b')))) ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) ->
  (forall cap q, L5.bo_st b' = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) ->
  (forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st b' = L5.BDyn c' q' -> q + 8 * c <= q' \/ q' + 8 * c' <= q) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(o, 32); (L5.bo_data o b, 8 * Z.of_nat (L5.bo_len b'))] a) ->
  (forall (fx' : FPState) R' M' model' (g : growth) LBn cr' LK' A',
      assign_post L ar (BX ++ LB) FF' LK' crc Mc M' Rc R' o (F + k) SPA b b' ws' g LBn cr' ->
      binv W1 (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' pcn M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc ASSIGN Mc modelc) K.
Proof.
  intros BI RI X10 X11 X1 RAn K1 K2 K8 OB AOB SZ OB' OL' SZ' LEN CAPOK CROK INB INB' NOAL WSUB KF.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  pose proof (callee_pre W BX Mc modelc LKc crc Ac ASSIGN_SCR BI ltac:(vm_compute; discriminate) ltac:(clear - HSCR; change ASSIGN_SCR with 4560; lia)) as (STKc & ROOMc & RSc & A32c).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac o BI AOB SZ)
    as ((ORP & ORG & O8) & OBIG & _ & _ & OFR & OF & OSH & _).
  pose proof RI as (Z2 & _ & _ & _ & Z4 & _).
  assert (OCR : forall a, docell E a -> SPA <= a < E). { destruct G as [_ _ _ _ _ OCR0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. exact OCR0. }
  apply (Hasg fx Rc Mc modelc K (BX ++ LB) FF' LKc crc Ac o (F + k) SPA pcn b b' ws' B1 B2 HK).
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
  - apply aobj_cons. exact AOB.
  - exact SZ.
  - exact OB'.
  - exact OL'.
  - apply loc_aobj; assumption.
  - exact SZ'.
  - exact INB.
  - exact INB'.
  - clear - OF K1 K2. lia.
  - exact NOAL.
  - intros fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST RT3 IA3 AM3 ILK3 HH3.
    assert (BI3 : binv W1 (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M3 model3 LK3 cr3 A3).
    { pose proof POST as (_ & _ & PG).
      destruct g as [|qn capn].
      - destruct PG as (DY & ELB & _ & _ & AH3). subst LBn.
        apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
                 W W1 BX BX BX Mc modelc LKc crc Ac M3 model3 LK3 cr3 A3 ASSIGN_SCR _ BI AH3 HH3 AM3 RT3 IA3 ILK3).
        + vm_compute; discriminate.
        + clear - HSCR; change ASSIGN_SCR with 4560; lia.
        + intros rr a [Hr|[Hr|[]]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR.
          * split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR. lia. }
            change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH. lia.
          * destruct b as [fb len sto]. destruct sto as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_st] in IR.
            -- assert (LE2 : (L5.bo_len b' <= 2)%nat).
               { destruct DY as [DY|DY]. 2: exact DY. exfalso. destruct OB as (_ & _ & _ & (BT & _)). unfold L5.bo_dyn in DY. cbn [L5.bo_fb] in DY, BT. rewrite BT in DY. discriminate DY. }
               split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR LE2. lia. }
               change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH LE2. lia.
            -- assert (CAPB : Z.of_nat (L5.bo_len b') <= cap).
               { apply CAPOK. destruct OB as (_ & _ & _ & (BT & _)). unfold L5.bo_dyn. cbn [L5.bo_fb]. exact BT. }
               destruct (blk_avoid W BX Mc modelc LKc crc Ac q (8 * cap) a BI (INB cap q eq_refl) ltac:(clear - IR CAPB; lia)) as (Y1 & Y2 & _).
               split. exact Y1. exact Y2.
        + intros a _ X. exact (proj2 (WSUB a X)).
        + intros a X. exact (proj1 (WSUB a X)).
      - destruct PG as (_ & _ & _ & ELB & _ & _ & _ & _ & AH3). subst LBn.
        apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
                 W W1 BX BX ((qn, 8 * capn) :: BX) Mc modelc LKc crc Ac M3 model3 LK3 cr3 A3 ASSIGN_SCR _ BI AH3 HH3 AM3 RT3 IA3 ILK3).
        + vm_compute; discriminate.
        + clear - HSCR; change ASSIGN_SCR with 4560; lia.
        + intros rr a [Hr|[]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR.
          split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR. lia. }
          change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH. lia.
        + intros a _ X rr [Hr|[]]. subst rr. apply (proj2 (WSUB a X) (o, 32)). left; reflexivity.
        + intros a X. exact (proj1 (WSUB a X)). }
    apply (KF fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST BI3 IA3 ILK3).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tob (LBx : list (Z * Z)) (Mk : word -> option byte) (o : Z) (b : L5.bigobj) (ws : list Z) : Prop :=
  L5.big_at RSEGS Mk o b /\ L5C.obj_limbs RSEGS Mk b ws /\ shadow_zero Mk o 4 /\ (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LBx).
Definition offx (LBx : list (Z * Z)) (scr : Z) (X : Z -> Prop) (Mc M1 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBx FF' SPA scr a -> ~ X a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a).
Definition inW (Wc : list L5.range) (a : Z) : Prop := exists rr, In rr Wc /\ L5.in_rng rr a.

Lemma offx_of_ahpres LBx scr Wc Mc M1 : ahpres L ar LBx FF' SPA scr Wc Mc M1 -> offx LBx scr (inW Wc) Mc M1.
Proof. intros (AG & _) a Ha Hc NX. apply AG. split. exact Ha. split. exact Hc. intros rr Hr IR. apply NX. exists rr. split; assumption. Qed.
Lemma offx_of_frame LBx scr (X : Z -> Prop) Mc M1 : (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> offx LBx scr X Mc M1.
Proof. intros FRM a Ha _ NX. apply FRM; assumption. Qed.
Lemma offx_refl LBx scr X Mc : offx LBx scr X Mc Mc. Proof. intros a _ _ _. reflexivity. Qed.

Lemma tob_keep LBo LBx LBy LKx crx Ax modelx scr (X : Z -> Prop) Mc M1 o b ws :
  ri_inv HI LBx FF' LKx crx Ax Mc (vml_of modelx) -> aobj FF' o 32 -> tob LBx Mc o b ws -> offx LBo scr X Mc M1 ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LBo /\ In (q, 8 * cap) LBy) ->
  (forall a, o <= a < o + 32 -> ~ X a) -> (forall j, 0 <= j < 4 -> ~ X (o / 8 + SB + j)) ->
  (forall cap q a, L5.bo_st b = L5.BDyn cap q -> q <= a < q + 8 * Z.of_nat (L5.bo_len b) -> ~ X a) ->
  tob LBy M1 o b ws.
Proof.
  intros HH AOB (OB & OL & SZ & INB) OFF INO NXO NXS NXD.
  pose proof (aobj_facts L ar C HI LY HIok LBx FF' LKx crx Ax Mc modelx o 32 SPA scr HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & _ & _).
  assert (AGO : forall i, o <= i < o + 32 -> M1 (Z_to_bv 64 i) = Mc (Z_to_bv 64 i)).
  { intros i Hi. apply OFF. clear - Hi OR; lia. apply (obj_client L ar LBo FF' SPA scr o 32 i AOB Hi). apply NXO. exact Hi. }
  split. { eapply L5C.big_at_agree. 4: exact OB. exact AGO. clear - OR; lia. clear - OR; lia. }
  split. { destruct OL as (OL1 & OL2 & OL3). split. exact OL1. split. exact OL2.
           destruct b as [fb len sto]. cbn [L5.bo_st L5.bo_len] in *. destruct sto as [v0 v1|cap q]. exact OL3.
           destruct OB as (_ & _ & _ & (_ & _ & _ & LC & CR & Q8 & Q4096 & Q47 & _)). cbn [L5.bo_len] in LC.
           eapply L5C.limbs_at_agree. 4: exact OL3. 2: clear - Q4096; lia. 2: rewrite OL1; clear - Q47 LC CR; lia.
           intros i Hi. rewrite OL1 in Hi. apply OFF. clear - Hi Q4096 Q47 LC CR; lia.
           apply (block_client L ar LBo FF' SPA scr q (8 * cap) i (proj1 (INO cap q eq_refl))). clear - Hi LC; lia.
           apply (NXD cap q i eq_refl). exact Hi. }
  split. { intros j Hj. unfold byte_at. rewrite OFF. apply SZ. exact Hj.
           unfold S, SB. clear - Hj OR OBIG. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
           destruct AOB as (f & Hf & X1 & X2 & X8). destruct f as [[Ff kf] rsf]. cbn [ff_addr ff_class fst snd] in X1, X2.
           apply (fframe_shadow_client L ar LBo FF' SPA scr Ff kf rsf). exact Hf. unfold in_shadow_of, S.
           assert (KB : 64 <= ff_bytes kf) by (clear - X1 X2; lia). clear - Hj X1 X2 X8 KB. lia.
           unfold S. apply NXS. exact Hj. }
  intros cap q Eq. exact (proj2 (INO cap q Eq)).
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma spill_keep LBx scr (X : Z -> Prop) Mc M1 a v : L5.u64_at RSEGS Mc a v -> SPA <= a -> a + 8 <= E -> offx LBx scr X Mc M1 ->
  (forall i, a <= i < a + 8 -> ~ X i) -> L5.u64_at RSEGS M1 a v.
Proof.
  intros Hc H1 H2 OFF NX. destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - H1 ER; lia. 2: clear - H2 ER; lia.
  intros i Hi. apply OFF. clear - Hi H1 H2 ER; lia. apply stack_client. clear - Hi H1 H2 SLO SHI SPT HSCR; lia. clear - Hi H1; lia. apply NX. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma shz_keep LBo LBx LKx crx Ax modelx scr (X : Z -> Prop) Mc M1 o :
  ri_inv HI LBx FF' LKx crx Ax Mc (vml_of modelx) -> aobj FF' o 32 -> shadow_zero Mc o 4 -> offx LBo scr X Mc M1 ->
  (forall j, 0 <= j < 4 -> ~ X (o / 8 + SB + j)) -> shadow_zero M1 o 4.
Proof.
  intros HH AOB SZ OFF NXS.
  pose proof (aobj_facts L ar C HI LY HIok LBx FF' LKx crx Ax Mc modelx o 32 SPA scr HH AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & _).
  intros j Hj. unfold byte_at. rewrite OFF. apply SZ. exact Hj.
  unfold S, SB. clear - Hj OR OBIG. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  destruct AOB as (f & Hf & X1 & X2 & X8). destruct f as [[Ff kf] rsf]. cbn [ff_addr ff_class fst snd] in X1, X2.
  apply (fframe_shadow_client L ar LBo FF' SPA scr Ff kf rsf). exact Hf. unfold in_shadow_of, S.
  assert (KB : 64 <= ff_bytes kf) by (clear - X1 X2; lia). clear - Hj X1 X2 X8 KB. lia.
  unfold S. apply NXS. exact Hj.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma limbs_keep LBo scr (X : Z -> Prop) Mc M1 o b fb' ws :
  L5.big_at RSEGS Mc o b -> L5C.obj_limbs RSEGS Mc b ws -> offx LBo scr X Mc M1 ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LBo) ->
  (forall cap q a, L5.bo_st b = L5.BDyn cap q -> q <= a < q + 8 * Z.of_nat (L5.bo_len b) -> ~ X a) ->
  L5C.obj_limbs RSEGS M1 (L5.BO fb' (L5.bo_len b) (L5.bo_st b)) ws.
Proof.
  intros OB (OL1 & OL2 & OL3) OFF INO NXD. split. exact OL1. split. exact OL2.
  destruct b as [fb len sto]. cbn [L5.bo_st L5.bo_len] in *. destruct sto as [v0 v1|cap q]. exact OL3.
  destruct OB as (_ & _ & _ & (_ & _ & _ & LC & CR & Q8 & Q4096 & Q47 & _)). cbn [L5.bo_len] in LC.
  eapply L5C.limbs_at_agree. 4: exact OL3. 2: clear - Q4096; lia. 2: rewrite OL1; clear - Q47 LC CR; lia.
  intros i Hi. rewrite OL1 in Hi. apply OFF. clear - Hi Q4096 Q47 LC CR; lia.
  apply (block_client L ar LBo FF' SPA scr q (8 * cap) i (INO cap q eq_refl)). clear - Hi LC; lia.
  apply (NXD cap q i eq_refl). exact Hi.
Qed.
(* [comment removed for export] *)
Lemma loc_keep LBo scr (X : Z -> Prop) Mc M1 k b blk : obj_at Mc (F + k) b blk -> 32 <= k -> k + 32 <= 504 -> offx LBo scr X Mc M1 ->
  (forall i, F + k <= i < F + k + 32 -> ~ X i) -> obj_at M1 (F + k) b blk.
Proof.
  intros OA K1 K2 OFF NX. destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 3) with 512 in *.
  apply (obj_at_agree Mc M1 _ _ _ OA ltac:(clear - FR K1; lia) ltac:(clear - FR K2; lia)). intros i Hi. apply OFF. clear - Hi FR K1 K2; lia.
  apply (fframe_client L ar _ _ _ _ F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Hi K1 K2; lia. apply NX. exact Hi.
Qed.
(* [comment removed for export] *)
Lemma fb_sgn fb s : 0 <= fb < 256 -> (s = 0 \/ s = 2) -> 0 <= Z.lor (Z.land fb 253) s < 256 /\ Z.testbit (Z.lor (Z.land fb 253) s) 0 = Z.testbit fb 0.
Proof.
  intros Hfb Hs.
  assert (H := L5ACPY.byte_enum2 (fun x y => ((0 <=? Z.lor (Z.land x 253) 0) && (Z.lor (Z.land x 253) 0 <? 256) && Bool.eqb (Z.testbit (Z.lor (Z.land x 253) 0) 0) (Z.testbit x 0)
                                         && (0 <=? Z.lor (Z.land x 253) 2) && (Z.lor (Z.land x 253) 2 <? 256) && Bool.eqb (Z.testbit (Z.lor (Z.land x 253) 2) 0) (Z.testbit x 0))%bool)
                ltac:(vm_compute; reflexivity) fb 0 Hfb ltac:(lia)).
  cbv beta in H. repeat (apply andb_prop in H; destruct H as [H ?]).
  repeat match goal with X : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in X end.
  destruct Hs; subst s; (split; [lia | assumption]).
Qed.

(* [comment removed for export] *)
Definition oreg (o : Z) (b : L5.bigobj) (a : Z) : Prop :=
  o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4 \/ (exists cap q, L5.bo_st b = L5.BDyn cap q /\ q <= a < q + 8 * cap).
Lemma tob_keep' LBo LBx LBy LKx crx Ax modelx scr (X : Z -> Prop) Mc M1 o b ws :
  ri_inv HI LBx FF' LKx crx Ax Mc (vml_of modelx) -> aobj FF' o 32 -> tob LBx Mc o b ws -> offx LBo scr X Mc M1 ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LBo /\ In (q, 8 * cap) LBy) ->
  (forall a, oreg o b a -> ~ X a) -> tob LBy M1 o b ws.
Proof.
  intros HH AOB TO OFF INO NX. apply (tob_keep LBo LBx LBy LKx crx Ax modelx scr X Mc M1 o b ws HH AOB TO OFF INO).
  - intros a Ha. apply NX. left. exact Ha.
  - intros j Hj. apply NX. right; left. clear - Hj; lia.
  - intros cap q a Eq Ha. apply NX. right; right. exists cap, q. split. exact Eq.
    destruct TO as (OB & _). destruct b as [fb len sto]. cbn [L5.bo_st L5.bo_len] in *. subst sto. destruct OB as (_ & _ & _ & (_ & _ & _ & LC & _)). cbn [L5.bo_len] in LC. clear - Ha LC; lia.
Qed.

(* [comment removed for export] *)
Lemma blk_frame W BX Mc modelc LKc crc Ac q n o : binv W BX Mc modelc LKc crc Ac -> In (q, n) (BX ++ LB) ->
  (q + n <= F \/ F + 512 <= q) /\ (aobj FF' o 32 -> q + n <= o \/ o + 32 <= q) /\ ~ (q <= fl < q + n).
Proof.
  intros BI IN. pose proof BI as (B1 & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
  pose proof (WB _ IN) as (_ & _ & _ & _ & _ & FA & FSA). cbn [fst snd] in *.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 3) with 512 in *.
  split. { pose proof (FA (F, 3, SPA + 32) ltac:(apply in_or_app; left; left; reflexivity)) as X. cbn [ff_addr ff_class fst snd] in X. change (ff_bytes 3) with 512 in X. exact X. }
  split. { intros (f & Hf & X1 & X2 & _). pose proof (FA f ltac:(apply in_or_app; left; exact Hf)) as X. clear - X X1 X2. lia. }
  clear - FSA FLP. lia.
Qed.

(* [comment removed for export] *)
Lemma arg_off W BX Mc modelc LKc crc Ac o b ws a : binv W BX Mc modelc LKc crc Ac -> aobj FF o 32 -> tob (BX ++ LB) Mc o b ws -> oreg o b a ->
  ~ (F <= a < F + 512) /\ ~ (SH <= a < SH + 64) /\ ~ (SPA <= a < E) /\ a <> fl.
Proof.
  intros BI AOB (OB & _ & SZ & INB) OR.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac o BI AOB SZ)
    as ((ORP & ORG & O8) & OBIG & _ & _ & OFR & OF & OSH & SOF & SOSH & SOFR & _ & _ & OCL).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  destruct OR as [OR|[OR|(cap & q & Eq & OR)]].
  - split. clear - OR OF; lia. split. clear - OR OSH; lia. split. clear - OR OFR; lia. exact (proj1 (proj2 (proj2 (OCL a OR)))).
  - unfold SB in OR. split. clear - OR SOF; lia. split. clear - OR SOSH; lia. split. clear - OR SOFR; lia.
    intros ->. clear - OR FLBIG ORP. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - pose proof (blk_avoid W BX Mc modelc LKc crc Ac q (8 * cap) a BI (INB cap q Eq) OR) as (_ & Y2 & Y3). change (ff_bytes 3 / 8) with 64 in Y2. unfold SB in Y2.
    pose proof (blk_frame W BX Mc modelc LKc crc Ac q (8 * cap) o BI (INB cap q Eq)) as (Y4 & _ & Y5).
    split. clear - OR Y4; lia. split. exact Y2. split. exact Y3. intros ->. apply Y5. exact OR.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Lemma big_at_fb Mc M1 o b fb' : L5.big_at RSEGS Mc o b -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  (forall i, o + 1 <= i < o + 32 -> M1 (Z_to_bv 64 i) = Mc (Z_to_bv 64 i)) -> L5.u8_at RSEGS M1 o fb' -> 0 <= fb' < 256 ->
  Z.testbit fb' 0 = Z.testbit (L5.bo_fb b) 0 -> L5.big_at RSEGS M1 o (L5.BO fb' (L5.bo_len b) (L5.bo_st b)).
Proof.
  intros (O0 & FBR & O8 & OST) H0 H1 AG U8 FR' BT. unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
  assert (X : forall a v, o + 8 <= a -> a + 8 <= o + 32 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS M1 a v).
  { intros a v A1 A2 Hc. eapply L5C.u64_at_agree. 4: exact Hc. intros i Hi. apply AG. clear - Hi A1 A2; lia. clear - A1 H0; lia. clear - A2 H1; lia. }
  split. exact U8. split. exact FR'. split. apply X. clear; lia. clear; lia. exact O8.
  destruct (L5.bo_st b) as [v0 v1|cap q].
  - destruct OST as (T0 & C16 & C24 & REST). split. rewrite BT. exact T0. split. apply X. clear; lia. clear; lia. exact C16. split. apply X. clear; lia. clear; lia. exact C24. exact REST.
  - destruct OST as (T0 & C16 & C24 & REST). split. rewrite BT. exact T0. split. apply X. clear; lia. clear; lia. exact C16. split. apply X. clear; lia. clear; lia. exact C24. exact REST.
Qed.

(* [comment removed for export] *)
Lemma tob_keep_fb LBo LBx LBy LKx crx Ax modelx scr (X : Z -> Prop) Mc M1 o b ws fb' :
  ri_inv HI LBx FF' LKx crx Ax Mc (vml_of modelx) -> aobj FF' o 32 -> tob LBx Mc o b ws -> offx LBo scr X Mc M1 ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LBo /\ In (q, 8 * cap) LBy) ->
  (forall a, o + 1 <= a < o + 32 -> ~ X a) -> (forall j, 0 <= j < 4 -> ~ X (o / 8 + SB + j)) ->
  (forall cap q a, L5.bo_st b = L5.BDyn cap q -> q <= a < q + 8 * Z.of_nat (L5.bo_len b) -> ~ X a) ->
  L5.u8_at RSEGS M1 o fb' -> 0 <= fb' < 256 -> Z.testbit fb' 0 = Z.testbit (L5.bo_fb b) 0 ->
  tob LBy M1 o (L5.BO fb' (L5.bo_len b) (L5.bo_st b)) ws.
Proof.
  intros HH AOB (OB & OL & SZ & INB) OFF INO NXO NXS NXD U8 FBR BT.
  pose proof (aobj_facts L ar C HI LY HIok LBx FF' LKx crx Ax Mc modelx o 32 SPA scr HH AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & _).
  split. { apply (big_at_fb Mc M1 o b fb' OB ltac:(clear - OR; lia) ltac:(clear - OR; lia)). 2: exact U8. 2: exact FBR. 2: exact BT.
           intros i Hi. apply OFF. clear - Hi OR; lia. apply (obj_client L ar LBo FF' SPA scr o 32 i AOB). clear - Hi; lia. apply NXO. exact Hi. }
  split. { apply (limbs_keep LBo scr X Mc M1 o b fb' ws OB OL OFF). intros cap q Eq. exact (proj1 (INO cap q Eq)). exact NXD. }
  split. { apply (shz_keep LBo LBx LKx crx Ax modelx scr X Mc M1 o HH AOB SZ OFF NXS). }
  cbn [L5.bo_st]. intros cap q Eq. exact (proj2 (INO cap q Eq)).
Qed.

(* [comment removed for export] *)
Lemma obj_rng W BX Mc modelc LKc crc Ac o : binv W BX Mc modelc LKc crc Ac -> aobj FF' o 32 ->
  (4096 <= o /\ o + 32 <= 2 ^ 47 /\ o mod 8 = 0) /\ (2147446784 + 17592186048512 <= o \/ o + 32 <= 2147446784).
Proof.
  intros (B1 & _) AOB.
  pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc o 32 0 0 B1 AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & _).
  split. clear - OR; lia. exact OBIG.
Qed.
Lemma blk_rng W BX Mc modelc LKc crc Ac q n : binv W BX Mc modelc LKc crc Ac -> In (q, n) (BX ++ LB) ->
  0 <= q /\ 0 < n /\ (q + n <= 2147446784 \/ 2147446784 + 17592186048512 <= q).
Proof.
  intros (B1 & _) IN. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
  pose proof (proj1 (WB _ IN)) as (X1 & _ & _ & X4 & _ & (X6 & X7 & _)). cbn [fst snd] in *. unfold BIGSHADOW_LO, BIGSHADOW_HI in X7. split. exact X6. split. exact X4. clear - X7; lia.
Qed.

(* [comment removed for export] *)
Lemma oreg_hdr W BX Mc modelc LKc crc Ac o b ws o2 a : binv W BX Mc modelc LKc crc Ac -> aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> aobj FF' o2 32 ->
  (o + 32 <= o2 \/ o2 + 32 <= o) -> oreg o b a -> ~ (o2 <= a < o2 + 32).
Proof.
  intros BI AOB (_ & _ & _ & INB) AOB2 AP OR.
  pose proof (obj_rng W BX Mc modelc LKc crc Ac o BI AOB) as (R1 & _). pose proof (obj_rng W BX Mc modelc LKc crc Ac o2 BI AOB2) as (R2 & BIG2).
  destruct OR as [OR|[OR|(cap & q & Eq & OR)]].
  - clear - OR AP; lia.
  - unfold SB in OR. clear - OR R1 BIG2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - pose proof (blk_frame W BX Mc modelc LKc crc Ac q (8 * cap) o2 BI (INB cap q Eq)) as (_ & Y & _). specialize (Y AOB2). clear - Y OR; lia.
Qed.
Lemma oreg_shd W BX Mc modelc LKc crc Ac o b ws o2 a : binv W BX Mc modelc LKc crc Ac -> aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> aobj FF' o2 32 ->
  (o + 32 <= o2 \/ o2 + 32 <= o) -> oreg o b a -> ~ (o2 / 8 + SB <= a < o2 / 8 + SB + 4).
Proof.
  intros BI AOB (_ & _ & _ & INB) AOB2 AP OR.
  pose proof (obj_rng W BX Mc modelc LKc crc Ac o BI AOB) as (R1 & BIG1). pose proof (obj_rng W BX Mc modelc LKc crc Ac o2 BI AOB2) as (R2 & _).
  destruct OR as [OR|[OR|(cap & q & Eq & OR)]]; unfold SB in *.
  - clear - OR R2 BIG1. lia.
  - clear - OR R1 R2 AP. lia.
  - pose proof (blk_rng W BX Mc modelc LKc crc Ac q (8 * cap) BI (INB cap q Eq)) as (_ & _ & Y). clear - Y OR R2. lia.
Qed.
Lemma oreg_blk W BX Mc modelc LKc crc Ac o b ws q2 n2 a : binv W BX Mc modelc LKc crc Ac -> aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> In (q2, n2) (BX ++ LB) ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> q + 8 * cap <= q2 \/ q2 + n2 <= q) -> oreg o b a -> ~ (q2 <= a < q2 + n2).
Proof.
  intros BI AOB (_ & _ & _ & INB) IN2 AP OR.
  pose proof (obj_rng W BX Mc modelc LKc crc Ac o BI AOB) as (R1 & _).
  pose proof (blk_rng W BX Mc modelc LKc crc Ac q2 n2 BI IN2) as (Y0 & Y1 & Y).
  destruct OR as [OR|[OR|(cap & q & Eq & OR)]]; unfold SB in *.
  - pose proof (blk_frame W BX Mc modelc LKc crc Ac q2 n2 o BI IN2) as (_ & Z & _). specialize (Z AOB). clear - Z OR; lia.
  - clear - OR R1 Y. lia.
  - specialize (AP cap q Eq). clear - AP OR; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ea4 (fx : FPState) Rc Mc modelc W BX LKc crc Ac qo qn fq :
  binv W BX Mc modelc LKc crc Ac -> (forall a, qo <= a < qo + 1 -> ~ L5.outside W a) ->
  rinvD R E Rc -> getr Rc (reg 18) = Z_to_bv 64 SH -> getr Rc (reg 25) = Z_to_bv 64 (F + 96) -> getr Rc (reg 26) = Z_to_bv 64 qo ->
  aobj FF qo 32 -> shadow_zero Mc qo 4 -> L5.u8_at RSEGS Mc qo fq -> 0 <= fq < 256 -> 0 <= qn <= 1 ->
  L5.u64_at RSEGS Mc (E - 288) ro -> L5.u64_at RSEGS Mc (E - 312) qn -> 0 <= ro < 2 ^ 64 ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W BX M1 model1 LKc crc Ac ->
      (forall x, In x KS_v5EA4 -> getr R1 (reg x) = getr Rc (reg x)) ->
      getr R1 (reg 1) = Z_to_bv 64 0x92d68 -> getr R1 (reg 10) = Z_to_bv 64 ro -> getr R1 (reg 11) = Z_to_bv 64 (F + 96) ->
      getr R1 (reg 19) = Z_to_bv 64 ro ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (SH + 20 <= a < SH + 24) -> ~ (qo <= a < qo + 1) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.u8_at RSEGS M1 qo (Z.lor (Z.land fq 253) (2 * qn)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 ASSIGN M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92d1c Mc modelc) K.
Proof.
  intros BI WQO RI X18 X25 X26 AOQ SZQ QFB FQR QNR SP96 SP72 ROR KF.
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac BI) as PF.
  destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac qo BI AOQ SZQ)
    as ((ORP & ORG & O8) & OBIG & OZv & OWv & OFR & OF & OSH & SOF & SOSH & SOFR & XB & XC & OCL).
  destruct (Gx W _ Mc modelc LKc crc Ac BI) as (_ & OWNv & _ & (_ & _ & _ & SV & _)).
  pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ALO : aligned qo 8) by exact O8.
  assert (SP96v : L5.u64_at RSEGS MV (E - 288) ro).
  { apply (proj2 (u64_at_vis _ Mc (E - 288) _ ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). exact SP96. }
  assert (SP72v : L5.u64_at RSEGS MV (E - 312) qn).
  { apply (proj2 (u64_at_vis _ Mc (E - 312) _ ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - ER; lia) ltac:(clear - ER; lia))). exact SP72. }
  assert (HVQ : 0 <= qn <= 1 /\ 0 <= qn < 2 ^ 64) by (clear - QNR; lia). destruct HVQ as [HVQ HVQ'].
  assert (HVF : 0 <= fq <= 255 /\ 0 <= fq < 2 ^ 64) by (clear - FQR; lia). destruct HVF as [HVF HVF'].
  assert (HVR : 0 <= ro <= 18446744073709551615) by (clear - ROR; lia).
  pose proof (v5EA4_conc fx Rc MV (fun j => match j with 2%nat => E | 35%nat => qo | 36%nat => ro | 40%nat => F | 41%nat => fl | 57%nat => qn | 58%nat => U Rc 1 | 60%nat => fq | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (apply XB; sc) ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & pR19 & pFB & _)).
  set (Wp := fun a => SH + 20 <= a < SH + 24 \/ qo <= a < qo + 1).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x92d1c R1 ASSIGN M1v Wp K BI pMS MG1).
  { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
  { intros a Ha [Wa|Wa].
    - apply (L5DKA.wp_shadow L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). unfold SB. change (ff_bytes 3 / 8) with 64. clear - Wa. lia.
    - destruct (OCL a ltac:(clear - Wa; lia)) as (C1 & C2 & C3 & C4). split. exact C4. split. split. exact C1. exact C2. intros _. apply WQO. exact Wa. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  apply (KF fx1 R1 M1 model1 BI1 pKS).
  - exact pR1.
  - exact pR10.
  - exact pR11.
  - exact pR19.
  - intros a Ha N1 N2. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2. lia.
  - assert (OVIS : avis (ahid Ac modelc) qo 32).
    { pose proof BI as (B1 & _). assert (AOB' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ).
      exact (proj1 (proj2 (proj2 (proj2 (aobj_facts L ar C HI LY HIok _ FF' LKc crc Ac Mc modelc qo 32 0 0 B1 AOB' ltac:(clear; lia) ltac:(reflexivity)))))). }
    replace (2 * qn) with ((2 * qn) mod 2 ^ 64) by (apply Z.mod_small; clear - QNR; lia).
    apply (proj1 (u8_at_vis (ahid Ac modelc) M1 qo _ ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - ORP; lia) ltac:(clear - ORP; lia))). rewrite VIS1. exact pFB.
Qed.

(* [comment removed for export] *)
Lemma ea3 (fx : FPState) Rc Mc modelc W BX LKc crc Ac f0 :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 18) = Z_to_bv 64 SH -> getr Rc (reg 19) = Z_to_bv 64 (F + 160) -> getr Rc (reg 20) = Z_to_bv 64 (F + 176) ->
  L5.u8_at RSEGS Mc (F + 160) f0 -> 0 <= f0 < 256 -> Z.testbit f0 0 = false ->
  (forall (fx1 : FPState) R1 model1,
      binv W BX Mc model1 LKc crc Ac ->
      (forall x, In x KS_v5EA3i -> getr R1 (reg x) = getr Rc (reg x)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x92d1c Mc model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92cfc Mc modelc) K.
Proof.
  intros BI RI X18 X19 X20 T0F F0R BT0 KF.
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac BI) as PF.
  destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  destruct (Gx W _ Mc modelc LKc crc Ac BI) as (_ & OWNv & _ & (_ & _ & FV & SV & _)). change (ff_bytes 3) with 512 in FV.
  pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB). pose proof BI as (B1 & B2 & _).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (T0Fv : L5.u8_at RSEGS MV (F + 160) f0).
  { apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F + 160) f0 ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). exact T0F. }
  assert (HVF : 0 <= f0 <= 255 /\ 0 <= f0 < 2 ^ 64) by (clear - F0R; lia). destruct HVF as [HVF HVF'].
  pose proof (v5EA3i_conc fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => f0 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & _)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x92cfc R1 0x92d1c K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  apply (KF fx1 R1 model1 BI1 pKS).
Qed.

(* [comment removed for export] *)
Lemma ea1 (fx : FPState) Rc Mc modelc W BX LKc crc Ac qo :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 18) = Z_to_bv 64 SH -> getr Rc (reg 22) = Z_to_bv 64 F -> getr Rc (reg 26) = Z_to_bv 64 qo -> 0 <= qo < 2 ^ 64 ->
  (forall (fx6 : FPState) R1 R6 R7 M6 model6,
      binv W BX M6 model6 LKc crc Ac ->
      (forall x, In x KS_v5EA1 -> getr R1 (reg x) = getr Rc (reg x)) -> regs_preserved R1 R6 -> (forall x, In x KS_v5EA2 -> getr R7 (reg x) = getr R6 (reg x)) ->
      getr R1 (reg 19) = Z_to_bv 64 (F + 160) -> getr R1 (reg 20) = Z_to_bv 64 (F + 176) ->
      getr R7 (reg 1) = Z_to_bv 64 0x92cfc -> getr R7 (reg 10) = Z_to_bv 64 qo -> getr R7 (reg 11) = Z_to_bv 64 (F + 160) ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BX ++ LB) FF' SPA MEM_SCR a -> ~ (SH + 20 <= a < SH + 24) -> ~ (F + 160 <= a < F + 192) ->
                 M6 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      L5.big_at RSEGS M6 (F + 160) (L5.BO 0 0 (L5.BInl 0 0)) -> shadow_zero M6 (F + 160) 4 ->
      srealizes RSEGS SCFG (cfg (fx:=fx6) R7 ASSIGN M6 model6) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92cb8 Mc modelc) K.
Proof.
  intros BI RI X18 X22 X26 QOR KF.
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac BI) as PF.
  destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  destruct (Gx W _ Mc modelc LKc crc Ac BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV)). change (ff_bytes 3) with 512 in FV. change (ff_bytes 3 / 8) with 64 in SHV.
  pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 3) with 512 in *.
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  pose proof (v5EA1_conc fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & pR12 & pR19 & pR20 & pT0 & pS3 & pS2 & pS1 & pS0 & _)).
  set (Wp := fun a => SH + 20 <= a < SH + 24 \/ F + 160 <= a < F + 161).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ Mc modelc LKc crc Ac fx fx1 Rc 0x92cb8 R1 0x5e7f0 M1v Wp K BI pMS MG1).
  { intros a Ha Hn. apply pFZ. exact Ha. all: subst Wp; cbn beta in Hn; clear - Hn; lia. }
  { intros a Ha [Wa|Wa].
    - apply (L5DKA.wp_shadow L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). unfold SB. change (ff_bytes 3 / 8) with 64. clear - Wa. lia.
    - apply (L5DKA.wp_fake L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). change (ff_bytes 3) with 512. clear - Wa; lia. clear - Wa; lia. }
  intros M1 model1 BI1 AH1 VIS1 MGM1 FRM1.
  pose proof BI1 as (C1 & C2 & _ & _ & _ & C6 & _).
  assert (T0F1 : L5.u8_at RSEGS M1 (F + 160) 0).
  { apply (proj1 (u8_at_vis (ahid Ac modelc) M1 (F + 160) 0 ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). rewrite VIS1. exact pT0. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FSH20 : (F + 160) / 8 = F / 8 + 20 /\ (F + 160) mod 8 = 0 /\ 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (clear - F8 FR; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (VZ1 : shadow_zero M1 (F + 160) 4).
  { intros j Hj. unfold byte_at, S. rewrite (proj1 FSH20).
    assert (X : L5.u8_at RSEGS M1v (F / 8 + 20 + SB + j) 0).
    { assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia). unfold SB. destruct J as [J|[J|[J|J]]]; subst j; gmem. }
    apply (byte_of_u8 M1 _ 0). 2: right; clear - Hj FSH20; unfold SB; lia. 2: clear - Hj FSH20; unfold SB; lia.
    apply (proj1 (u8_at_vis (ahid Ac modelc) M1 (F / 8 + 20 + SB + j) 0 ltac:(eapply avis_sub; [exact SHV | unfold SB; clear - Hj; lia | unfold SB; clear - Hj; lia]) ltac:(clear - Hj FSH20; unfold SB; lia) ltac:(clear - Hj FSH20; unfold SB; lia))).
    rewrite VIS1. exact X. }
  (* [comment removed for export] *)
  pose proof (aio_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
  rewrite (aly_segs L C LY), (aly_memset L C LY), (aly_scr_mem L C LY) in MS.
  assert (RI1 : rinvD R E R1). { apply (rinvD_ks R E Rc R1 KS_v5EA1 RI pKS). vm_compute; reflexivity. }
  pose proof RI1 as (Y2 & Y8 & Y9 & Y3 & Y4 & YSB).
  assert (U25 : bv_unsigned (getr R1 2%bv) = SPA). { rewrite r2, Y2. apply L5.unsigned_lit. clear - ER; lia. }
  assert (SA16 : (E - 384) mod 16 = 0). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  eapply (MS fx1 R1 M1 model1 (BX ++ LB) FF' LKc crc Ac (F + 168) 0 16 K); clear MS.
  { split. exact C1. split. exact (proj1 C2). split. exact (proj2 C2).
    split. rewrite r10. exact pR10. split. rewrite r12. exact pR12. split. clear; lia.
    split. rewrite r4, Y4. exact G4. split. rewrite r1, pR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
    split. { rewrite U25. apply (astack_ok_of_astk L ar C LY M1 M1 E SCRD 384 2560 C6 (mem_grows_refl M1)). clear; lia. clear; lia. clear - HSCR; lia. exact SA16. }
    split. { eapply aacc_of_zero. exact VZ1. exact (proj1 (proj2 FSH20)). clear - FR; lia. clear; lia. clear; lia. }
    split. { intros i Hi. rewrite U25. apply (fframe_client L ar _ _ _ _ F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Hi; lia. }
    split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS M1 (F + 168) 16). 2: clear - FR; lia. 2: clear - FR; lia. 2: exact Hi. 2: exact Hm.
             pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ C1) as (_ & WF1 & _).
             pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (WF1 _ (or_introl eq_refl))))))) as FD. cbn [ff_addr ff_class fst snd] in FD. change (ff_bytes 3) with 512 in FD.
             intros j Hj. replace (F + 168 + j) with (F + (168 + j)) by (clear; lia). apply FD. clear - Hj; lia. }
    split. exact HK. apply (app_rng_fs L ar C HI HIok _ _ _ _ _ _ _ (F + 168) 16 C1). clear - FS1; lia. clear - FS2; lia. }
  { rewrite r11. exact pR11. }
  intros R6 M6 model6 mR10 RP6 ZB PRES6 SDEF6 RT6 MI6 HH6. rewrite U25 in PRES6, SDEF6. rewrite r1, pR1.
  assert (Hh6 : m_halted model6 = None). { rewrite (L5LZ.model_rt_halted _ _ RT6). exact (proj1 C2). }
  assert (BI6 : binv W BX M6 model6 LKc crc Ac).
  { apply (L5AFK.binv_mem L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
             W BX M1 model1 LKc crc Ac M6 model6 (fun a => F + 168 <= a < F + 168 + 16) 2560 BI1 HH6 (conj Hh6 MI6) RT6 PRES6).
    - intros a Ha. apply SDEF6. clear - Ha; lia.
    - intros a Da. destruct (ZB (a - (F + 168)) ltac:(clear - Da; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (F + 168 + (a - (F + 168))) with a in Bv by (clear; lia). rewrite Bv. discriminate.
    - intros a. destruct (rng_dec a (F + 168) (F + 168 + 16)); [left|right]; assumption.
    - intros a Da. change (ff_bytes 3) with 512. clear - Da; lia.
    - clear - HSCR; lia.
    - clear; lia. }
  assert (FCL6 : forall a, F + 32 <= a < F + 504 -> aclient L ar (BX ++ LB) FF' SPA 2560 a).
  { intros a Ha. apply (fframe_client L ar _ _ _ _ F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Ha; lia. }
  assert (VU6 : L5.u8_at RSEGS M6 (F + 160) 0).
  { eapply L5C.u8_at_agree. 4: exact T0F1. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. apply PRES6. clear - Hi FR; lia. apply FCL6. clear - Hi; lia. clear - Hi; lia. }
  assert (Z6 : L5KA.zeros_at M6 (F + 168) 16). { intros i Hi. destruct (ZB i Hi) as (v & Ev & Bv). subst v. exact Bv. }
  assert (VZ6 : shadow_zero M6 (F + 160) 4).
  { intros j Hj. unfold byte_at. rewrite PRES6. apply VZ1. exact Hj. unfold S, SB. rewrite (proj1 FSH20). clear - Hj FSH20; lia.
    apply (fframe_shadow_client L ar _ _ _ _ F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. unfold in_shadow_of, S. rewrite (proj1 FSH20).
    clear - Hj F8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    unfold S. rewrite (proj1 FSH20). clear - Hj FSH20 FBIG; unfold SB; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  assert (RI6 : rinvD R E R6) by (apply (rinvD_pres R E R1 R6 RI1 RP6)).
  pose proof RI6 as (Z2 & Z8 & Z9 & Z3 & Z4 & ZSB).
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W _ M6 model6 LKc crc Ac BI6) as PF6.
  destruct PF6 as (W384' & IMGC' & CSB' & CUAR' & FDEFv' & FWv' & FSHWv' & FLCv' & FLWv').
  destruct (Gx W _ M6 model6 LKc crc Ac BI6) as (_ & _ & _ & (_ & _ & FV6 & _ & _)). change (ff_bytes 3) with 512 in FV6.
  set (MV6 := mrestrict (ahid Ac model6) M6) in *.
  assert (HVQO : 0 <= qo <= 18446744073709551615) by (clear - QOR; lia).
  assert (X18_6 : getr R6 (reg 18) = Z_to_bv 64 SH) by rk.
  assert (X19_6 : getr R6 (reg 19) = Z_to_bv 64 (F + 160)) by rk.
  assert (X20_6 : getr R6 (reg 20) = Z_to_bv 64 (F + 176)) by rk.
  assert (X26_6 : getr R6 (reg 26) = Z_to_bv 64 qo) by rk.
  pose proof (v5EA2_conc fx1 R6 MV6 (fun j => match j with 2%nat => E | 35%nat => qo | 40%nat => F | 41%nat => fl | 58%nat => U R6 1 | _ => 0 end)) as P2. cbn beta iota in P2.
  feed P2 ltac:(first [apply UR | apply U_to | sc ]).
  destruct P2 as (fx7 & R7 & M7v & MG7 & qFR & qFZ & (qMS & qKS & qR1 & qR10 & qR11 & qT24 & _)).
  set (Wq := fun a => F + 184 <= a < F + 192).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ M6 model6 LKc crc Ac fx1 fx7 R6 0x92ce4 R7 ASSIGN M7v Wq K BI6 qMS MG7).
  { intros a Ha Hn. apply qFZ. exact Ha. subst Wq; cbn beta in Hn; clear - Hn; lia. }
  { intros a Ha Wa. subst Wq; cbn beta in Wa.
    apply (L5DKA.wp_fake L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). change (ff_bytes 3) with 512. clear - Wa; lia. clear - Wa; lia. }
  intros M7 model7 BI7 AH7 VIS7 MGM7 FRM7.
  assert (VU7 : L5.u8_at RSEGS M7 (F + 160) 0).
  { eapply L5C.u8_at_agree. 4: exact VU6. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. apply FRM7. clear - Hi FR; lia. subst Wq; cbn beta. clear - Hi; lia. }
  assert (Z7 : L5KA.zeros_at M7 (F + 168) 16).
  { intros i Hi. rewrite FRM7. exact (Z6 i Hi). clear - Hi FR; lia. subst Wq; cbn beta. clear - Hi; lia. }
  assert (T24_7 : L5.u64_at RSEGS M7 (F + 184) 0).
  { apply (proj1 (u64_at_vis (ahid Ac model6) M7 (F + 184) 0 ltac:(eapply avis_sub; [exact FV6 | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). rewrite VIS7. exact qT24. }
  assert (VBIG7 : L5.big_at RSEGS M7 (F + 160) (L5.BO 0 0 (L5.BInl 0 0))).
  { apply L5ADK.big_at_zero. exact VU7.
    - replace (F + 160 + 8) with (F + 168) by (clear; lia). apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z7. clear; lia. clear; lia. clear - FR; lia. clear - FR; lia.
    - replace (F + 160 + 16) with (F + 176) by (clear; lia). apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z7. clear; lia. clear; lia. clear - FR; lia. clear - FR; lia.
    - replace (F + 160 + 24) with (F + 184) by (clear; lia). exact T24_7. }
  assert (VZ7 : shadow_zero M7 (F + 160) 4).
  { intros j Hj. unfold byte_at. rewrite FRM7. apply VZ6. exact Hj. unfold S, SB. rewrite (proj1 FSH20). clear - Hj FSH20; lia.
    subst Wq; cbn beta. unfold S, SB. rewrite (proj1 FSH20). clear - Hj FSH20 FBIG FRP. lia. }
  apply (KF fx7 R1 R6 R7 M7 model7 BI7 pKS RP6 qKS pR19 pR20 qR1 qR10 qR11).
  - intros a Ha Hc N1 N2. rewrite FRM7. rewrite PRES6. apply FRM1. exact Ha. subst Wp; cbn beta. clear - N1 N2; lia. exact Ha. exact Hc. clear - N2; lia. exact Ha. subst Wq; cbn beta. clear - N2; lia.
  - exact VBIG7.
  - exact VZ7.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition same_store (b : L5.bigobj) (st' : L5.bstore) : Prop :=
  match L5.bo_st b, st' with L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q | L5.BInl _ _, L5.BInl _ _ => True | _, _ => False end.
Lemma ra_lit pc : 0 <= pc < 2 ^ 47 -> pc mod 2 = 0 -> L5.ra_ok pc. Proof. intros; split; assumption. Qed.
Lemma inW2 o d n a : inW [(o, 32); (d, n)] a -> o <= a < o + 32 \/ d <= a < d + n.
Proof. intros (rr & [E1|[E1|[]]] & IR); subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR; [left|right]; exact IR. Qed.
Lemma outside_cons2 (W0 : list L5.range) r1 r2 a : L5.outside (r1 :: r2 :: W0) a -> L5.outside W0 a /\ L5.outside [r1; r2] a.
Proof. intros O. split; intros rr Hr; apply O; cbn [In] in *; tauto. Qed.

Lemma early_path (fx : FPState) Rc Mc modelc W BXf LKc crc Ac qo qn bits bq wq br wr bn wn on bd od :
  binv W (ostr on ++ ostr od ++ BXf) Mc modelc LKc crc Ac ->
  rinvD R E Rc -> getr Rc (reg 18) = Z_to_bv 64 SH -> getr Rc (reg 22) = Z_to_bv 64 F -> getr Rc (reg 24) = Z_to_bv 64 (F + 32) -> getr Rc (reg 25) = Z_to_bv 64 (F + 96) ->
  getr Rc (reg 26) = Z_to_bv 64 qo -> getr Rc (reg 27) = Z_to_bv 64 F -> 0 <= qn <= 1 ->
  L5.u64_at RSEGS Mc (E - 312) qn -> L5.u64_at RSEGS Mc (E - 288) ro -> L5.u64_at RSEGS Mc (E - 328) bits -> (bits = 0 \/ bits = 2) ->
  tob ((ostr on ++ ostr od ++ BXf) ++ LB) Mc qo bq wq -> aobj FF qo 32 ->
  tob ((ostr on ++ ostr od ++ BXf) ++ LB) Mc ro br wr -> aobj FF ro 32 -> (qo + 32 <= ro \/ ro + 32 <= qo) ->
  tob ((ostr on ++ ostr od ++ BXf) ++ LB) Mc (F + 96) bn wn -> obj_at Mc (F + 96) bn on -> obj_at Mc (F + 32) bd od ->
  Z.of_nat (L5.bo_len bn) <= 2 ^ 23 -> (L5.bo_dyn br = true -> Z.of_nat (L5.bo_len bn) <= L5.bo_cap br) -> ((3 <= L5.bo_len bn)%nat -> L5.bo_dyn br = true) ->
  (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bn = L5.BDyn c' q' -> q + 8 * c <= q' \/ q' + 8 * c' <= q) ->
  (forall c q c' q', L5.bo_st bq = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q + 8 * c <= q' \/ q' + 8 * c' <= q) ->
  (forall cap q, L5.bo_st bq = L5.BDyn cap q -> In (q, 8 * cap) (BXf ++ LB)) -> (forall cap q, L5.bo_st br = L5.BDyn cap q -> In (q, 8 * cap) (BXf ++ LB)) ->
  (forall (fxf : FPState) Rf Mf modelf Af LKf,
      regs_preserved R Rf -> incl Ac Af -> incl LKf LKc ->
      ahpres L ar LB FF E SCRD ((ro, 32) :: (L5.bo_data ro br, 8 * Z.of_nat (L5.bo_len bn)) :: (qo, 32) :: (L5.bo_data qo bq, 8 * Z.of_nat 0) :: W) M Mf ->
      (exists stq, tob (BXf ++ LB) Mf qo (L5.BO (Z.lor (Z.land (L5.bo_fb bq) 253) (2 * qn)) 0 stq) [] /\ same_store bq stq) ->
      (exists str, tob (BXf ++ LB) Mf ro (L5.BO (Z.lor (Z.land (assign_fb (L5.bo_fb br) (L5.bo_fb bn) (L5.bo_len bn) false) 253) bits) (L5.bo_len bn) str) wn /\ same_store br str) ->
      model_rt model modelf -> amodel_ok Af modelf -> ri_inv HI (BXf ++ LB) FF LKf crc Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92cb8 Mc modelc) K.
Proof.
  set (BX := ostr on ++ ostr od ++ BXf).
  intros BI RI X18 X22 X24 X25 X26 X27 QNR SP72 SP96 SP64 BITS TQ AOQ TR AOR QRA TN ON OD LEN CAPOK NOGROW NOAL NOALQ INQ INR KF.
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  assert (AON' : aobj FF' (F + 96) 32) by (apply loc_aobj; [clear; lia | clear; lia | reflexivity]).
  assert (AOT' : aobj FF' (F + 160) 32) by (apply loc_aobj; [clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (apply loc_aobj; [clear; lia | clear; lia | reflexivity]).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHQ : (F + 160) / 8 = F / 8 + 20 /\ (F + 96) / 8 = F / 8 + 12 /\ 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (clear - FRP ALF; unfold aligned in ALF; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (obj_rng W BX Mc modelc LKc crc Ac qo BI AOQ') as (QRG & QBIG). pose proof (obj_rng W BX Mc modelc LKc crc Ac ro BI AOR') as (RRG & RBIG).
  (* [comment removed for export] *)
  assert (QOF : forall a, oreg qo bq a -> ~ (F <= a < F + 512) /\ ~ (SH <= a < SH + 64) /\ ~ (SPA <= a < E) /\ a <> fl) by (intros a; apply (arg_off W BX Mc modelc LKc crc Ac qo bq wq a BI AOQ TQ)).
  assert (ROF : forall a, oreg ro br a -> ~ (F <= a < F + 512) /\ ~ (SH <= a < SH + 64) /\ ~ (SPA <= a < E) /\ a <> fl) by (intros a; apply (arg_off W BX Mc modelc LKc crc Ac ro br wr a BI AOR TR)).
  (* [comment removed for export] *)
  apply (ea1 fx Rc Mc modelc W BX LKc crc Ac qo BI RI X18 X22 X26 ltac:(clear - QRG; lia)).
  intros fx7 R1 R6 R7 M6 model7 BI7 KS1 RP6 KS7 p19 p20 q1 q10 q11 AG6 T0B6 T0Z6.
  set (X6 := fun a => SH + 20 <= a < SH + 24 \/ F + 160 <= a < F + 192).
  assert (OFF6 : offx (BX ++ LB) MEM_SCR X6 Mc M6). { intros a Ha Hc NX. apply AG6. exact Ha. exact Hc. subst X6; cbn beta in NX; clear - NX; lia. subst X6; cbn beta in NX; clear - NX; lia. }
  pose proof BI as (B1 & _).
  assert (SPX6 : forall i, SPA <= i < E -> ~ X6 i). { intros i Hi. subst X6; cbn beta. clear - Hi SFB SHQ ER. lia. }
  assert (SP72_6 : L5.u64_at RSEGS M6 (E - 312) qn). { apply (spill_keep (BX ++ LB) MEM_SCR X6 Mc M6 _ _ SP72 ltac:(clear; lia) ltac:(clear; lia) OFF6). intros i Hi. apply SPX6. clear - Hi; lia. }
  assert (SP96_6 : L5.u64_at RSEGS M6 (E - 288) ro). { apply (spill_keep (BX ++ LB) MEM_SCR X6 Mc M6 _ _ SP96 ltac:(clear; lia) ltac:(clear; lia) OFF6). intros i Hi. apply SPX6. clear - Hi; lia. }
  assert (SP64_6 : L5.u64_at RSEGS M6 (E - 328) bits). { apply (spill_keep (BX ++ LB) MEM_SCR X6 Mc M6 _ _ SP64 ltac:(clear; lia) ltac:(clear; lia) OFF6). intros i Hi. apply SPX6. clear - Hi; lia. }
  assert (TQ6 : tob (BX ++ LB) M6 qo bq wq).
  { apply (tob_keep' (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc MEM_SCR X6 Mc M6 qo bq wq B1 AOQ' TQ OFF6). intros cap q Eq. split; apply (proj2 (proj2 (proj2 TQ)) cap q Eq).
    intros a OR. destruct (QOF a OR) as (N1 & N2 & _). subst X6; cbn beta. clear - N1 N2. lia. }
  assert (TR6 : tob (BX ++ LB) M6 ro br wr).
  { apply (tob_keep' (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc MEM_SCR X6 Mc M6 ro br wr B1 AOR' TR OFF6). intros cap q Eq. split; apply (proj2 (proj2 (proj2 TR)) cap q Eq).
    intros a OR. destruct (ROF a OR) as (N1 & N2 & _). subst X6; cbn beta. clear - N1 N2. lia. }
  assert (TN6 : tob (BX ++ LB) M6 (F + 96) bn wn).
  { apply (tob_keep' (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc MEM_SCR X6 Mc M6 (F + 96) bn wn B1 AON' TN OFF6). intros cap q Eq. split; apply (proj2 (proj2 (proj2 TN)) cap q Eq).
    intros a OR. pose proof (oreg_hdr W BX Mc modelc LKc crc Ac (F + 96) bn wn (F + 160) a BI AON' TN AOT' ltac:(left; clear; lia) OR) as N1.
    pose proof (oreg_shd W BX Mc modelc LKc crc Ac (F + 96) bn wn (F + 160) a BI AON' TN AOT' ltac:(left; clear; lia) OR) as N2.
    subst X6; cbn beta. rewrite (proj1 SHQ) in N2. unfold SB in N2. clear - N1 N2. lia. }
  assert (X6F : forall k i, 32 <= k -> k + 32 <= 160 -> F + k <= i < F + k + 32 -> ~ X6 i). { intros k i K1 K2 Hi. subst X6; cbn beta. clear - K1 K2 Hi SHQ FBIG FRP. lia. }
  assert (OD6 : obj_at M6 (F + 32) bd od) by (apply (loc_keep (BX ++ LB) MEM_SCR X6 Mc M6 32 bd od OD ltac:(clear; lia) ltac:(clear; lia) OFF6); intros i Hi; apply (X6F 32 i); [clear; lia | clear; lia | exact Hi]).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac qo BI AOQ (proj1 (proj2 (proj2 TQ)))) as (_ & _ & _ & _ & _ & QAF & _).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro BI AOR (proj1 (proj2 (proj2 TR)))) as (_ & _ & _ & _ & _ & RAF & _).
  (* [comment removed for export] *)
  assert (RI7 : rinvD R E R7).
  { apply (rinvD_ks R E R6 R7 KS_v5EA2 (rinvD_pres R E R1 R6 (rinvD_ks R E Rc R1 KS_v5EA1 RI KS1 ltac:(vm_compute; reflexivity)) RP6) KS7). vm_compute; reflexivity. }
  set (W1 := (qo, 32) :: (L5.bo_data qo bq, 8 * Z.of_nat 0) :: W).
  pose proof BI7 as (B1_7 & _).
  apply (assign_stage fx7 R7 M6 model7 W W1 BX LKc crc Ac qo 160 0x92cfc bq (L5.BO 0 0 (L5.BInl 0 0)) [] BI7 RI7 q10 q11 q1).
  { apply ra_lit. clear; lia. reflexivity. }
  { clear; lia. } { clear; lia. } { reflexivity. }
  { exact (proj1 TQ6). } { exact AOQ. } { exact (proj1 (proj2 (proj2 TQ6))). }
  { exact T0B6. } { split. reflexivity. split. constructor. reflexivity. } { exact T0Z6. }
  { cbn [L5.bo_len]. clear; lia. }
  { intros _. cbn [L5.bo_len]. pose proof (proj1 TQ6) as (_ & _ & _ & ST). unfold L5.bo_cap. destruct (L5.bo_st bq). clear; lia. destruct ST as (_ & _ & _ & _ & CR & _). clear - CR; lia. }
  { intros H3. exfalso. cbn [L5.bo_len] in H3. clear - H3; lia. }
  { exact (proj2 (proj2 (proj2 TQ6))). }
  { intros cap q Eq. discriminate Eq. }
  { intros c q c' q' _ Eq. discriminate Eq. }
  { intros a O. apply outside_cons2. exact O. }
  intros fx8 R8 M8 model8 g LBn cr8 LK8 A8 POST8 BI8 IA8 ILK8.
  destruct POST8 as (RP8 & a0_8 & PG8). cbn [L5.bo_len L5.bo_fb] in PG8.
  destruct g as [|qg capg]. 2:{ exfalso. destruct PG8 as (_ & H3 & _). clear - H3; lia. }
  destruct PG8 as (DY8 & ELB8 & ECR8 & (st8 & QB8 & QL8 & SS8) & AH8). subst LBn cr8.
  change (assign_fb (L5.bo_fb bq) 0 0 false) with (L5.bo_fb bq) in QB8, QL8.
  pose proof (offx_of_ahpres (BX ++ LB) ASSIGN_SCR _ M6 M8 AH8) as OFF8.
  assert (NX8 : forall a, ~ (qo <= a < qo + 32) -> ~ inW [(qo, 32); (L5.bo_data qo bq, 8 * Z.of_nat 0)] a).
  { intros a N IW. apply inW2 in IW. destruct IW as [IW|IW]. exact (N IW). clear - IW; lia. }
  assert (SP72_8 : L5.u64_at RSEGS M8 (E - 312) qn).
  { apply (spill_keep (BX ++ LB) ASSIGN_SCR _ M6 M8 _ _ SP72_6 ltac:(clear; lia) ltac:(clear; lia) OFF8). intros i Hi. apply NX8. intros Q. destruct (QOF i (or_introl Q)) as (_ & _ & N3 & _). apply N3. clear - Hi; lia. }
  assert (SP96_8 : L5.u64_at RSEGS M8 (E - 288) ro).
  { apply (spill_keep (BX ++ LB) ASSIGN_SCR _ M6 M8 _ _ SP96_6 ltac:(clear; lia) ltac:(clear; lia) OFF8). intros i Hi. apply NX8. intros Q. destruct (QOF i (or_introl Q)) as (_ & _ & N3 & _). apply N3. clear - Hi; lia. }
  assert (SP64_8 : L5.u64_at RSEGS M8 (E - 328) bits).
  { apply (spill_keep (BX ++ LB) ASSIGN_SCR _ M6 M8 _ _ SP64_6 ltac:(clear; lia) ltac:(clear; lia) OFF8). intros i Hi. apply NX8. intros Q. destruct (QOF i (or_introl Q)) as (_ & _ & N3 & _). apply N3. clear - Hi; lia. }
  assert (TR8 : tob (BX ++ LB) M8 ro br wr).
  { apply (tob_keep' (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac model7 ASSIGN_SCR _ M6 M8 ro br wr B1_7 AOR' TR6 OFF8). intros cap q Eq. split; apply (proj2 (proj2 (proj2 TR6)) cap q Eq).
    intros a OR. apply NX8. apply (oreg_hdr W BX M6 model7 LKc crc Ac ro br wr qo a BI7 AOR' TR6 AOQ' ltac:(clear - QRA; lia) OR). }
  assert (TN8 : tob (BX ++ LB) M8 (F + 96) bn wn).
  { apply (tob_keep' (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac model7 ASSIGN_SCR _ M6 M8 (F + 96) bn wn B1_7 AON' TN6 OFF8). intros cap q Eq. split; apply (proj2 (proj2 (proj2 TN6)) cap q Eq).
    intros a OR. apply NX8. apply (oreg_hdr W BX M6 model7 LKc crc Ac (F + 96) bn wn qo a BI7 AON' TN6 AOQ' ltac:(clear - QAF; lia) OR). }
  assert (QHF : forall i, F <= i < F + 512 -> ~ inW [(qo, 32); (L5.bo_data qo bq, 8 * Z.of_nat 0)] i). { intros i Hi. apply NX8. clear - Hi QAF. lia. }
  assert (OD8 : obj_at M8 (F + 32) bd od) by (apply (loc_keep (BX ++ LB) ASSIGN_SCR _ M6 M8 32 bd od OD6 ltac:(clear; lia) ltac:(clear; lia) OFF8); intros i Hi; apply QHF; clear - Hi; lia).
  assert (T0_8 : obj_at M8 (F + 160) (L5.BO 0 0 (L5.BInl 0 0)) None).
  { apply (loc_keep (BX ++ LB) ASSIGN_SCR _ M6 M8 160 _ None (conj T0B6 eq_refl) ltac:(clear; lia) ltac:(clear; lia) OFF8). intros i Hi. apply QHF. clear - Hi; lia. }
  assert (SZQ8 : shadow_zero M8 qo 4).
  { apply (shz_keep (BX ++ LB) (BX ++ LB) LKc crc Ac model7 ASSIGN_SCR _ M6 M8 qo B1_7 AOQ' (proj1 (proj2 (proj2 TQ6))) OFF8). intros j Hj. apply NX8. unfold SB. clear - Hj QRG QBIG.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (INQ8 : forall cap q, st8 = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB) /\ L5.bo_st bq = L5.BDyn cap q).
  { intros cap q Eq. subst st8. destruct (L5.bo_st bq) as [v0 v1|c0 q0] eqn:EB. destruct SS8. destruct SS8 as (-> & ->). split. apply (proj2 (proj2 (proj2 TQ6)) c0 q0). exact EB. reflexivity. }
  (* [comment removed for export] *)
  assert (RI8 : rinvD R E R8) by (apply (rinvD_pres R E R7 R8 RI7 RP8)).
  assert (X18_8 : getr R8 (reg 18) = Z_to_bv 64 SH) by rk.
  assert (X19_8 : getr R8 (reg 19) = Z_to_bv 64 (F + 160)) by rk.
  assert (X20_8 : getr R8 (reg 20) = Z_to_bv 64 (F + 176)) by rk.
  apply (ea3 fx8 R8 M8 model8 W1 BX LK8 crc A8 0 BI8 RI8 X18_8 X19_8 X20_8 (proj1 (proj1 T0_8)) ltac:(clear; lia) ltac:(reflexivity)).
  intros fx9 R9 model9 BI9 KS9.
  (* [comment removed for export] *)
  assert (RI9 : rinvD R E R9). { apply (rinvD_ks R E R8 R9 KS_v5EA3i RI8 KS9). vm_compute; reflexivity. }
  assert (X18_9 : getr R9 (reg 18) = Z_to_bv 64 SH) by rk.
  assert (X25_9 : getr R9 (reg 25) = Z_to_bv 64 (F + 96)) by rk.
  assert (X26_9 : getr R9 (reg 26) = Z_to_bv 64 qo) by rk.
  assert (WQO : forall a, qo <= a < qo + 1 -> ~ L5.outside W1 a). { intros a Ha O. apply (O (qo, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - Ha; lia. }
  pose proof QB8 as (QFB8 & FQR & _). cbn [L5.bo_fb] in QFB8, FQR.
  apply (ea4 fx9 R9 M8 model9 W1 BX LK8 crc A8 qo qn (L5.bo_fb bq) BI9 WQO RI9 X18_9 X25_9 X26_9 AOQ SZQ8 QFB8 FQR QNR SP96_8 SP72_8 ltac:(clear - RRG; lia)).
  intros fx10 R10 M10 model10 BI10 KS10 t1 t10 t11 t19 AG10 QFB10.
  set (X10 := fun a => SH + 20 <= a < SH + 24 \/ qo <= a < qo + 1).
  assert (OFF10 : offx (BX ++ LB) 0 X10 M8 M10). { apply offx_of_frame. intros a Ha NX. apply AG10. exact Ha. subst X10; cbn beta in NX; clear - NX; lia. subst X10; cbn beta in NX; clear - NX; lia. }
  pose proof BI9 as (B1_9 & _).
  assert (SP64_10 : L5.u64_at RSEGS M10 (E - 328) bits).
  { apply (spill_keep (BX ++ LB) 0 X10 M8 M10 _ _ SP64_8 ltac:(clear; lia) ltac:(clear; lia) OFF10). intros i Hi. subst X10; cbn beta. intros [Q|Q].
    clear - Q Hi SHQ ER; lia. assert (OQ : oreg qo bq i) by (left; clear - Q; lia). destruct (QOF i OQ) as (_ & _ & N3 & _). apply N3. clear - Hi; lia. }
  assert (TR10 : tob (BX ++ LB) M10 ro br wr).
  { apply (tob_keep' (BX ++ LB) (BX ++ LB) (BX ++ LB) LK8 crc A8 model9 0 X10 M8 M10 ro br wr B1_9 AOR' TR8 OFF10). intros cap q Eq. split; apply (proj2 (proj2 (proj2 TR8)) cap q Eq).
    intros a OR. subst X10; cbn beta. intros [Q|Q]. destruct (ROF a OR) as (_ & N2 & _). apply N2. clear - Q; lia.
    apply (oreg_hdr W1 BX M8 model9 LK8 crc A8 ro br wr qo a BI9 AOR' TR8 AOQ' ltac:(clear - QRA; lia) OR). clear - Q; lia. }
  assert (TN10 : tob (BX ++ LB) M10 (F + 96) bn wn).
  { apply (tob_keep' (BX ++ LB) (BX ++ LB) (BX ++ LB) LK8 crc A8 model9 0 X10 M8 M10 (F + 96) bn wn B1_9 AON' TN8 OFF10). intros cap q Eq. split; apply (proj2 (proj2 (proj2 TN8)) cap q Eq).
    intros a OR. subst X10; cbn beta. intros [Q|Q].
    pose proof (oreg_shd W1 BX M8 model9 LK8 crc A8 (F + 96) bn wn (F + 160) a BI9 AON' TN8 AOT' ltac:(left; clear; lia) OR) as N2. rewrite (proj1 SHQ) in N2. unfold SB in N2. clear - N2 Q; lia.
    apply (oreg_hdr W1 BX M8 model9 LK8 crc A8 (F + 96) bn wn qo a BI9 AON' TN8 AOQ' ltac:(clear - QAF; lia) OR). clear - Q; lia. }
  assert (OD10 : obj_at M10 (F + 32) bd od).
  { apply (loc_keep (BX ++ LB) 0 X10 M8 M10 32 bd od OD8 ltac:(clear; lia) ltac:(clear; lia) OFF10). intros i Hi. subst X10; cbn beta. clear - Hi QAF SHQ FBIG FRP. lia. }
  pose proof (fb_sgn (L5.bo_fb bq) (2 * qn) FQR ltac:(clear - QNR; lia)) as (FQR' & FQT).
  assert (TQ10 : tob (BX ++ LB) M10 qo (L5.BO (Z.lor (Z.land (L5.bo_fb bq) 253) (2 * qn)) 0 st8) []).
  { apply (tob_keep_fb (BX ++ LB) (BX ++ LB) (BX ++ LB) LK8 crc A8 model9 0 X10 M8 M10 qo (L5.BO (L5.bo_fb bq) 0 st8) [] _ B1_9 AOQ').
    - split. exact QB8. split. exact QL8. split. exact SZQ8. intros cap q Eq. exact (proj1 (INQ8 cap q Eq)).
    - exact OFF10.
    - cbn [L5.bo_st]. intros cap q Eq. split; exact (proj1 (INQ8 cap q Eq)).
    - intros a Ha. subst X10; cbn beta. intros [Q|Q]. assert (OQ : oreg qo bq a) by (left; clear - Ha; lia). destruct (QOF a OQ) as (_ & N2 & _). apply N2. clear - Q; lia. clear - Q Ha; lia.
    - intros j Hj. subst X10; cbn beta. intros [Q|Q]. assert (OQ : oreg qo bq (qo / 8 + SB + j)) by (right; left; clear - Hj; lia). destruct (QOF _ OQ) as (_ & N2 & _). apply N2. clear - Q; lia.
      unfold SB in Q. clear - Q Hj QRG QBIG. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    - cbn [L5.bo_len]. intros cap q a _ Ha. exfalso. clear - Ha; lia.
    - exact QFB10.
    - exact FQR'.
    - exact FQT. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  assert (RI10 : rinvD R E R10). { apply (rinvD_ks R E R9 R10 KS_v5EA4 RI9 KS10). vm_compute; reflexivity. }
  set (W2 := (ro, 32) :: (L5.bo_data ro br, 8 * Z.of_nat (L5.bo_len bn)) :: W1).
  pose proof BI10 as (B1_10 & _).
  apply (assign_stage fx10 R10 M10 model10 W1 W2 BX LK8 crc A8 ro 96 0x92d68 br bn wn BI10 RI10 t10 t11 t1).
  { apply ra_lit. clear; lia. reflexivity. }
  { clear; lia. } { clear; lia. } { reflexivity. }
  { exact (proj1 TR10). } { exact AOR. } { exact (proj1 (proj2 (proj2 TR10))). }
  { exact (proj1 TN10). } { exact (proj1 (proj2 TN10)). } { exact (proj1 (proj2 (proj2 TN10))). }
  { exact LEN. } { exact CAPOK. }
  { intros H3 DF. exfalso. rewrite (NOGROW H3) in DF. discriminate DF. }
  { exact (proj2 (proj2 (proj2 TR10))). } { exact (proj2 (proj2 (proj2 TN10))). } { exact NOAL. }
  { intros a O. apply outside_cons2. exact O. }
  intros fx11 R11 M11 model11 g LBn cr11 LK11 A11 POST11 BI11 IA11 ILK11.
  destruct POST11 as (RP11 & a0_11 & PG11).
  destruct g as [|qg capg]. 2:{ exfalso. destruct PG11 as (DF & H3 & _). rewrite (NOGROW H3) in DF. discriminate DF. }
  destruct PG11 as (DY11 & ELB11 & ECR11 & (st11 & RB11 & RL11 & SS11) & AH11). subst LBn cr11.
  pose proof (offx_of_ahpres (BX ++ LB) ASSIGN_SCR _ M10 M11 AH11) as OFF11.
  assert (INW11 : forall a, inW [(ro, 32); (L5.bo_data ro br, 8 * Z.of_nat (L5.bo_len bn))] a -> ro <= a < ro + 32 \/ (exists c q, L5.bo_st br = L5.BDyn c q /\ q <= a < q + 8 * c)).
  { intros a IW. apply inW2 in IW. destruct IW as [IW|IW]. left; exact IW.
    pose proof (proj1 TR10) as (_ & _ & _ & ST). destruct br as [fbr lenr sto]. destruct sto as [v0 v1|c q]; cbn [L5.bo_data L5.bo_st L5.bo_dyn L5.bo_fb L5.bo_cap] in *.
    - left. destruct DY11 as [DY|DY]. exfalso. destruct ST as (BT & _). unfold L5.bo_dyn in DY. cbn [L5.bo_fb] in DY. rewrite BT in DY. discriminate DY. clear - IW DY; lia.
    - right. exists c, q. split. reflexivity. assert (CB : Z.of_nat (L5.bo_len bn) <= c). { apply CAPOK. destruct ST as (BT & _). unfold L5.bo_dyn. cbn [L5.bo_fb]. exact BT. } clear - IW CB; lia. }
  assert (NX11 : forall a, ~ oreg ro br a -> ~ inW [(ro, 32); (L5.bo_data ro br, 8 * Z.of_nat (L5.bo_len bn))] a).
  { intros a N IW. apply N. destruct (INW11 a IW) as [Q|Q]. left; exact Q. right; right. exact Q. }
  assert (SP64_11 : L5.u64_at RSEGS M11 (E - 328) bits).
  { apply (spill_keep (BX ++ LB) ASSIGN_SCR _ M10 M11 _ _ SP64_10 ltac:(clear; lia) ltac:(clear; lia) OFF11). intros i Hi. apply NX11. intros OR. destruct (ROF i OR) as (_ & _ & N3 & _). apply N3. clear - Hi; lia. }
  assert (TQ11 : tob (BX ++ LB) M11 qo (L5.BO (Z.lor (Z.land (L5.bo_fb bq) 253) (2 * qn)) 0 st8) []).
  { apply (tob_keep' (BX ++ LB) (BX ++ LB) (BX ++ LB) LK8 crc A8 model10 ASSIGN_SCR _ M10 M11 qo _ [] B1_10 AOQ' TQ10 OFF11). cbn [L5.bo_st]. intros cap q Eq. split; exact (proj1 (INQ8 cap q Eq)).
    intros a OR. apply NX11. intros [Q|[Q|(c & q & Eq & Q)]].
    - apply (oreg_hdr W1 BX M10 model10 LK8 crc A8 qo _ [] ro a BI10 AOQ' TQ10 AOR' QRA OR). exact Q.
    - apply (oreg_shd W1 BX M10 model10 LK8 crc A8 qo _ [] ro a BI10 AOQ' TQ10 AOR' QRA OR). exact Q.
    - apply (oreg_blk W1 BX M10 model10 LK8 crc A8 qo _ [] q (8 * c) a BI10 AOQ' TQ10 (proj2 (proj2 (proj2 TR10)) c q Eq)). 2: exact OR. 2: exact Q.
      cbn [L5.bo_st]. intros cap0 q0 E0. destruct (INQ8 cap0 q0 E0) as (_ & EB). exact (NOALQ cap0 q0 c q EB Eq). }
  assert (TN11 : tob (BX ++ LB) M11 (F + 96) bn wn).
  { apply (tob_keep' (BX ++ LB) (BX ++ LB) (BX ++ LB) LK8 crc A8 model10 ASSIGN_SCR _ M10 M11 (F + 96) bn wn B1_10 AON' TN10 OFF11). intros cap q Eq. split; apply (proj2 (proj2 (proj2 TN10)) cap q Eq).
    intros a OR. apply NX11. intros [Q|[Q|(c & q & Eq & Q)]].
    - apply (oreg_hdr W1 BX M10 model10 LK8 crc A8 (F + 96) bn wn ro a BI10 AON' TN10 AOR' ltac:(clear - RAF; lia) OR). exact Q.
    - apply (oreg_shd W1 BX M10 model10 LK8 crc A8 (F + 96) bn wn ro a BI10 AON' TN10 AOR' ltac:(clear - RAF; lia) OR). exact Q.
    - apply (oreg_blk W1 BX M10 model10 LK8 crc A8 (F + 96) bn wn q (8 * c) a BI10 AON' TN10 (proj2 (proj2 (proj2 TR10)) c q Eq)). 2: exact OR. 2: exact Q.
      intros cap0 q0 E0. pose proof (NOAL c q cap0 q0 Eq E0) as X. clear - X; lia. }
  assert (OD11 : obj_at M11 (F + 32) bd od).
  { apply (loc_keep (BX ++ LB) ASSIGN_SCR _ M10 M11 32 bd od OD10 ltac:(clear; lia) ltac:(clear; lia) OFF11). intros i Hi. apply NX11. intros OR. destruct (ROF i OR) as (N1 & _). apply N1. clear - Hi; lia. }
  assert (SZR11 : shadow_zero M11 ro 4).
  { apply (shz_keep (BX ++ LB) (BX ++ LB) LK8 crc A8 model10 ASSIGN_SCR _ M10 M11 ro B1_10 AOR' (proj1 (proj2 (proj2 TR10))) OFF11). intros j Hj IW. destruct (INW11 _ IW) as [Q|(c & q & Eq & Q)].
    - unfold SB in Q. clear - Q Hj RRG RBIG. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    - pose proof (blk_rng W1 BX M10 model10 LK8 crc A8 q (8 * c) BI10 (proj2 (proj2 (proj2 TR10)) c q Eq)) as (_ & _ & Y). unfold SB in Q. clear - Q Y Hj RRG. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  assert (RI11 : rinvD R E R11) by (apply (rinvD_pres R E R10 R11 RI10 RP11)).
  assert (RITL : rinvTL R E F R11). { unfold rinvTL. split. exact RI11. repeat split; rk. }
  assert (X19_11 : getr R11 (reg 19) = Z_to_bv 64 ro) by rk.
  assert (WRO : forall a, ro <= a < ro + 1 -> ~ L5.outside W2 a). { intros a Ha O. apply (O (ro, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - Ha; lia. }
  pose proof RB11 as (RFB11 & FRR & _). cbn [L5.bo_fb] in RFB11, FRR.
  set (fr11 := assign_fb (L5.bo_fb br) (L5.bo_fb bn) (L5.bo_len bn) false) in *.
  pose proof (fb_sgn fr11 bits FRR BITS) as (FRR' & FRT).
  assert (INR11 : forall cap q, st11 = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB) /\ L5.bo_st br = L5.BDyn cap q).
  { intros cap q Eq. subst st11. destruct (L5.bo_st br) as [v0 v1|c0 q0] eqn:EB. destruct SS11. destruct SS11 as (-> & ->). split. apply (proj2 (proj2 (proj2 TR10)) c0 q0). exact EB. reflexivity. }
  assert (TRn : tob (BX ++ LB) M11 ro (L5.BO fr11 (L5.bo_len bn) st11) wn).
  { split. exact RB11. split. exact RL11. split. exact SZR11. intros cap q Eq. exact (proj1 (INR11 cap q Eq)). }
  apply (ea5 L ar C HI LY HIok Hdel R M model K LB FF LK A E SCRD F fl ro r LK2 M2 model2 cr2 G ER EA HK RA UR1 G2 G4 ltac:(clear - HSCR; lia)
           fx11 R11 M11 model11 W2 BXf LK11 crc A11 bn on bd od fr11 bits BI11 WRO RITL X19_11 (conj (proj1 TN11) (proj2 ON)) OD11 AOR SZR11 SP64_11 ltac:(clear - BITS; lia) RFB11 FRR).
  intros fxf Rf Mf modelf Af RPf IAf AHf AGf FBf RTf AMf HHf.
  pose proof BI11 as (B1_11 & _).
  set (Xf := fun a => L5AFK.Wret F fl 3 a \/ F / 8 + SB + 12 <= a < F / 8 + SB + 16 \/ ro <= a < ro + 1).
  assert (OFFf : offx (BXf ++ LB) OPDEL_SCR Xf M11 Mf). { intros a Ha Hc NX. apply AGf; [exact Ha | exact Hc | intros Q; apply NX; left; exact Q | intros Q; apply NX; right; left; exact Q | intros Q; apply NX; right; right; exact Q]. }
  assert (XfF : forall a, ~ (F <= a < F + 512) -> ~ (SH <= a < SH + 64) -> a <> fl -> ~ (ro <= a < ro + 1) -> ~ Xf a).
  { intros a N1 N2 N3 N4. subst Xf; cbn beta. unfold L5AFK.Wret, SB. change (ff_bytes 3 / 8) with 64. clear - N1 N2 N3 N4. lia. }
  apply (KF fxf Rf Mf modelf Af LK11 RPf).
  - intros x Hx. apply IAf. apply IA11. apply IA8. exact Hx.
  - intros x Hx. apply ILK8. apply ILK11. exact Hx.
  - exact AHf.
  - exists st8. split.
    + apply (tob_keep' (BXf ++ LB) (BX ++ LB) (BXf ++ LB) LK11 crc A11 model11 OPDEL_SCR Xf M11 Mf qo _ [] B1_11 AOQ' TQ11 OFFf).
      * cbn [L5.bo_st]. intros cap q Eq. destruct (INQ8 cap q Eq) as (_ & EB). split; exact (INQ cap q EB).
      * intros a OR. assert (OQ : oreg qo bq a).
        { destruct OR as [OR|[OR|(c & q & Eq & OR)]]. left; exact OR. right; left; exact OR. cbn [L5.bo_st] in Eq. right; right. exists c, q. split. exact (proj2 (INQ8 c q Eq)). exact OR. }
        destruct (QOF a OQ) as (N1 & N2 & _ & N4). apply (XfF a N1 N2 N4).
        intros Q. apply (oreg_hdr W1 BX M10 model10 LK8 crc A8 qo _ [] ro a BI10 AOQ' TQ10 AOR' QRA OR). clear - Q; lia.
    + unfold same_store. destruct (L5.bo_st bq) as [v0 v1|c0 qq0]; destruct st8 as [v0' v1'|c1 qq1]; exact SS8.
  - exists st11. split.
    + apply (tob_keep_fb (BXf ++ LB) (BX ++ LB) (BXf ++ LB) LK11 crc A11 model11 OPDEL_SCR Xf M11 Mf ro (L5.BO fr11 (L5.bo_len bn) st11) wn _ B1_11 AOR' TRn OFFf).
      * cbn [L5.bo_st]. intros cap q Eq. destruct (INR11 cap q Eq) as (_ & EB). split; exact (INR cap q EB).
      * intros a Ha. assert (OQ : oreg ro br a) by (left; clear - Ha; lia). destruct (ROF a OQ) as (N1 & N2 & _ & N4). apply (XfF a N1 N2 N4). clear - Ha; lia.
      * intros j Hj. assert (OQ : oreg ro br (ro / 8 + SB + j)) by (right; left; clear - Hj; lia). destruct (ROF _ OQ) as (N1 & N2 & _ & N4). apply (XfF _ N1 N2 N4).
        unfold SB. clear - Hj RRG RBIG. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      * cbn [L5.bo_st L5.bo_len]. intros cap q a Eq Ha. destruct (INR11 cap q Eq) as (INb & EB).
        assert (LC : Z.of_nat (L5.bo_len bn) <= cap). { destruct RB11 as (_ & _ & _ & ST). cbn [L5.bo_st L5.bo_len] in ST. rewrite Eq in ST. exact (proj1 (proj2 (proj2 (proj2 ST)))). }
        assert (OQ : oreg ro br a). { right; right. exists cap, q. split. exact EB. clear - Ha LC; lia. }
        destruct (ROF a OQ) as (N1 & N2 & _ & N4). apply (XfF a N1 N2 N4).
        pose proof (blk_frame W1 BX M10 model10 LK8 crc A8 q (8 * cap) ro BI10 INb) as (_ & Y & _). specialize (Y AOR'). clear - Y Ha LC. lia.
      * exact FBf.
      * exact FRR'.
      * exact FRT.
    + unfold same_store. destruct (L5.bo_st br) as [v0 v1|c0 qq0]; destruct st11 as [v0' v1'|c1 qq1]; exact SS11.
  - exact RTf.
  - exact AMf.
  - exact HHf.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End DIV.
End WithIface.
End SCFG_1.
End L5ADVEA.
