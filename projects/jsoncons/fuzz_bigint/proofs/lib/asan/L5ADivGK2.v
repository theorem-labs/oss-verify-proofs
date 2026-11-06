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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5ACmp L5CoreB L5ADetailH L5AFrameK L5DivKitA L5DivSpecsA L5OpmodSpecsA L5DivLeafSpecsA L5DivInnerSpecsA L5ACopyAS L5ADivH L5ADivT L5ADivD L5ADivE L5ADivEA L5ADivHC L5ADivHA L5ADivHO L5ADivHL L5ADivHM L5ADivPG1 L5ADivPG2 L5ADivGL L5ADivGA L5ADivGB L5ADivGC L5ADivGD L5ADivGU L5ARed L5ADivHH L5ADivHS L5ADivGE L5ADivN L5ADivO1 L5ANorm L5ADivGN L5ADivGK L5ARzHuge.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require As0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGK2.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB. Import L5ADVGC. Import L5ADVGD. Import L5ADVGU. Import L5ADVHL. Import L5ADVGE. Import L5ADVGN. Import L5ADVGK.
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
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis Hasg : assign_spec L ar HI.
Hypothesis Hcps : L5ACPAS.copya_stk_spec L ar HI.
Hypothesis Hnorm : L5DLA.norm_specA L ar HI.
Hypothesis Hrsz : resize_spec L ar HI.
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 E.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation SH := (F / 8 + 2147450880).
Local Notation offx := (L5ADVEA.offx L ar FF E F).
Local Notation tob := (L5ADVEA.tob).

Local Ltac open_ctx BI :=
  let PF := fresh "PF" in
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as PF;
  destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Notation G1 := (L5ADVGA.g1 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps).
Local Notation G2s := (L5ADVGA.g2 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps).
Local Notation G3 := (L5ADVGA.g3 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hnorm).
Local Notation G4s := (L5ADVGA.g4 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G5 := (L5ADVGA.g5 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR).
Local Notation G6 := (L5ADVGB.g6 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hasg).
Local Notation G7 := (L5ADVGC.g7 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR).
Local Notation G7b := (L5ADVGC.g7b L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G8 := (L5ADVGC.g8 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G8b := (L5ADVGC.g8b L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G9 := (L5ADVGC.g9 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR).
Local Notation RSZ := (L5ADVHH.resize_stage L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G EA HK G4 HSCR FFR1 FFRS Hrsz).
Local Notation ARG_AFTER := (L5ADVGN.arg_after L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G).
Local Notation OREG_DISJ := (L5ADVGN.oreg_disj L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G).
Local Notation GN_FRONT := (L5ADVGN.gn_front L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps Hnorm).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arg_data_upd W BX Mc modelc LKc crc Ac M' scr o b ws :
  binv W BX Mc modelc LKc crc Ac -> aobj FF o 32 -> tob (BX ++ LB) Mc o b ws ->
  L5ADVEA.offx L ar FF E F (BX ++ LB) scr (fun a => L5.bo_data o b <= a < L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b)) Mc M' ->
  L5.defined M' (L5.bo_data o b) (8 * Z.of_nat (L5.bo_len b)) ->
  exists b' ws', tob (BX ++ LB) M' o b' ws' /\ L5.bo_fb b' = L5.bo_fb b /\ L5.bo_len b' = L5.bo_len b /\ L5ADVEA.same_store b (L5.bo_st b') /\ L5.bo_data o b' = L5.bo_data o b.
Proof.
  intros BI AOB TO OFF DEF. pose proof BI as (B1 & _). assert (AOB' : aobj FF' o 32) by (apply aobj_cons; exact AOB).
  edestruct L5ADVEA.obj_rng with (o := o) as ((O1 & O2 & O8) & OBIG); try first [exact LY | exact HIok | exact BI | exact AOB'].
  pose proof (len_le_cap Mc o b (proj1 TO)) as LC.
  apply (L5ADVGN.tob_data_upd (BX ++ LB) Mc M' o b ws TO O1 O2).
  - intros a Ha ND. apply OFF. clear - Ha O1 O2; lia. apply (obj_client L ar (BX ++ LB) FF' SPA scr o 32 a AOB' Ha). exact ND.
  - intros j Hj. apply OFF.
    + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold SB. clear - Hj O1 O2. lia.
    + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      destruct AOB' as (f & Hf & X1 & X2 & X8). destruct f as [[Ff kf] rsf]. cbn [ff_addr ff_class fst snd] in X1, X2.
      apply (fframe_shadow_client L ar (BX ++ LB) FF' SPA scr Ff kf rsf). exact Hf. unfold in_shadow_of, S.
      assert (KB : 64 <= ff_bytes kf) by (clear - X1 X2; lia).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold SB. clear - Hj X1 X2 X8 KB. lia.
    + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      destruct (L5ADVGN.shz_off_self L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac o b ws j BI (aobj_cons _ _ _ _ AOB) TO Hj) as (N1 & N2).
      intros Y. destruct b as [fb len sto]. unfold L5.bo_data in Y. cbn [L5.bo_st L5.bo_len] in *. destruct sto as [v0 v1|cap q].
      * apply N1. clear - Y LC. lia.
      * apply (N2 cap q eq_refl). clear - Y LC. lia.
  - exact DEF.
  - intros cap q Eq. destruct (L5ADVEA.blk_frame L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac q (8 * cap) o BI (proj2 (proj2 (proj2 TO)) cap q Eq)) as (_ & Y & _).
    specialize (Y (aobj_cons _ _ _ _ AOB)). clear - Y; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma g5_arg (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac qo (bq : L5.bigobj) wq :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> getr Rc (reg 21) = Z_to_bv 64 2147450880 -> getr Rc (reg 22) = Z_to_bv 64 qo ->
  aobj FF qo 32 -> tob (BX ++ LB) Mc qo bq wq -> Z.of_nat (L5.bo_len bq) <= 2 ^ 24 ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(L5.bo_data qo bq, 8 * Z.of_nat (L5.bo_len bq))] a) ->
  (forall (fx' : FPState) R' M' model' bq' wq',
      binv W1 BX M' model' LKc crc Ac -> rinvD R E R' ->
      (forall x, In x [3; 4; 19; 20; 21; 22; 23; 26; 27]%nat -> getr R' (reg x) = getr Rc (reg x)) ->
      getr R' (reg 18) = Z_to_bv 64 (qo / 8 + 2147450880) -> getr R' (reg 24) = Z_to_bv 64 (L5.bo_data qo bq) -> getr R' (reg 25) = Z_to_bv 64 (Z.of_nat (L5.bo_len bq)) ->
      tob (BX ++ LB) M' qo bq' wq' -> L5.bo_fb bq' = L5.bo_fb bq -> L5.bo_len bq' = L5.bo_len bq -> L5ADVEA.same_store bq (L5.bo_st bq') -> L5.bo_data qo bq' = L5.bo_data qo bq ->
      L5ADVEA.offx L ar FF E F (BX ++ LB) MEM_SCR (fun a => L5.bo_data qo bq <= a < L5.bo_data qo bq + 8 * Z.of_nat (L5.bo_len bq)) Mc M' ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x927c0 M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92758 Mc modelc) K.
Proof.
  intros BI RI X21 X22 AOQ TQ LEN WSUB KF. pose proof TQ as (OBQ & OLQ & SZQ & INQ).
  apply (G5 fx Rc Mc modelc W W1 BX LKc crc Ac qo bq BI RI X21 X22 AOQ SZQ OBQ LEN INQ WSUB).
  intros fx' R' M' model' BI' RI' KS p18 p24 p25 AG ZR.
  assert (OFF : L5ADVEA.offx L ar FF E F (BX ++ LB) MEM_SCR (fun a => L5.bo_data qo bq <= a < L5.bo_data qo bq + 8 * Z.of_nat (L5.bo_len bq)) Mc M').
  { intros a Ha Hc NX. apply AG. exact Ha. exact Hc. exact NX. }
  assert (DEF : L5.defined M' (L5.bo_data qo bq) (8 * Z.of_nat (L5.bo_len bq))). { intros i Hi. rewrite (ZR i Hi). discriminate. }
  destruct (arg_data_upd W BX Mc modelc LKc crc Ac M' MEM_SCR qo bq wq BI AOQ TQ OFF DEF) as (bq' & wq' & TQ' & F1 & L1 & S1 & D1).
  apply (KF fx' R' M' model' bq' wq' BI' RI' KS p18 p24 p25 TQ' F1 L1 S1 D1 OFF).
Qed.

(* [comment removed for export] *)
Lemma arg_data_updX W BX Mc modelc LKc crc Ac M' scr (X : Z -> Prop) o b ws :
  binv W BX Mc modelc LKc crc Ac -> aobj FF o 32 -> tob (BX ++ LB) Mc o b ws ->
  L5ADVEA.offx L ar FF E F (BX ++ LB) scr X Mc M' ->
  (forall a, (o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4) -> X a -> L5.bo_data o b <= a < L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b)) ->
  L5.defined M' (L5.bo_data o b) (8 * Z.of_nat (L5.bo_len b)) ->
  exists b' ws', tob (BX ++ LB) M' o b' ws' /\ L5.bo_fb b' = L5.bo_fb b /\ L5.bo_len b' = L5.bo_len b /\ L5ADVEA.same_store b (L5.bo_st b') /\ L5.bo_data o b' = L5.bo_data o b.
Proof.
  intros BI AOB TO OFF XD DEF. pose proof BI as (B1 & _). assert (AOB' : aobj FF' o 32) by (apply aobj_cons; exact AOB).
  edestruct L5ADVEA.obj_rng with (o := o) as ((O1 & O2 & O8) & OBIG); try first [exact LY | exact HIok | exact BI | exact AOB'].
  pose proof (len_le_cap Mc o b (proj1 TO)) as LC.
  apply (L5ADVGN.tob_data_upd (BX ++ LB) Mc M' o b ws TO O1 O2).
  - intros a Ha ND. apply OFF. clear - Ha O1 O2; lia. apply (obj_client L ar (BX ++ LB) FF' SPA scr o 32 a AOB' Ha). intros Y. apply ND. exact (XD a (or_introl Ha) Y).
  - intros j Hj. apply OFF.
    + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold SB. clear - Hj O1 O2. lia.
    + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      destruct AOB' as (f & Hf & X1 & X2 & X8). destruct f as [[Ff kf] rsf]. cbn [ff_addr ff_class fst snd] in X1, X2.
      apply (fframe_shadow_client L ar (BX ++ LB) FF' SPA scr Ff kf rsf). exact Hf. unfold in_shadow_of, S.
      assert (KB : 64 <= ff_bytes kf) by (clear - X1 X2; lia).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold SB. clear - Hj X1 X2 X8 KB. lia.
    + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      destruct (L5ADVGN.shz_off_self L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac o b ws j BI (aobj_cons _ _ _ _ AOB) TO Hj) as (N1 & N2).
      intros Y0. assert (RS : o / 8 + SB <= o / 8 + SB + j < o / 8 + SB + 4) by (clear - Hj; Lia.lia). pose proof (XD (o / 8 + SB + j) (or_intror RS) Y0) as Y.
      destruct b as [fb len sto]. unfold L5.bo_data in Y. cbn [L5.bo_st L5.bo_len] in *. destruct sto as [v0 v1|cap q].
      * apply N1. clear - Y LC. lia.
      * apply (N2 cap q eq_refl). clear - Y LC. lia.
  - exact DEF.
  - intros cap q Eq. destruct (L5ADVEA.blk_frame L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac q (8 * cap) o BI (proj2 (proj2 (proj2 TO)) cap q Eq)) as (_ & Y & _).
    specialize (Y (aobj_cons _ _ _ _ AOB)). clear - Y; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma arg_data_def W BX Mc modelc LKc crc Ac (Mk : word -> option byte) o b : binv W BX Mc modelc LKc crc Ac -> aobj FF o 32 -> L5.big_at RSEGS Mk o b ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) -> L5.defined Mc (L5.bo_data o b) (8 * Z.of_nat (L5.bo_len b)).
Proof.
  intros BI AOB OB INB. pose proof BI as (B1 & _). assert (AOB' : aobj FF' o 32) by (apply aobj_cons; exact AOB).
  pose proof (len_le_cap Mk o b OB) as LC.
  destruct b as [fb len sto]. unfold L5.bo_data. cbn [L5.bo_st L5.bo_len] in *. destruct sto as [v0 v1|cap q].
  - pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc o 32 0 0 B1 AOB' ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & ODEF & _).
    intros i Hi. replace (o + 16 + i) with (o + (16 + i)) by (clear; lia). apply ODEF. clear - Hi LC; lia.
  - pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _). pose proof (WB (q, 8 * cap) (INB cap q eq_refl)) as (_ & BDEF & _). cbn [fst snd] in BDEF.
    intros i Hi. apply BDEF. clear - Hi LC; lia.
Qed.

(* [comment removed for export] *)
Lemma g9_arg (fx : FPState) Rc Mc modelc W BX LKc crc Ac to qo (br bq bd : L5.bigobj) wr wq wd (n l : Z) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 19) = Z_to_bv 64 (L5.bo_data ro br) -> getr Rc (reg 20) = Z_to_bv 64 (L5.bo_data qo bq) ->
  getr Rc (reg 21) = Z_to_bv 64 ((L5.bo_data (F + 32) bd + 8 * l) / 8 + 2147450880) -> getr Rc (reg 22) = Z_to_bv 64 n ->
  getr Rc (reg 24) = Z_to_bv 64 (L5.bo_data (F + 32) bd + 8 * l) ->
  aobj FF ro 32 -> aobj FF qo 32 -> tob (BX ++ LB) Mc ro br wr -> tob (BX ++ LB) Mc qo bq wq -> tob (BX ++ LB) Mc (F + 32) bd wd ->
  Z.of_nat (L5.bo_len br) = n + 1 -> Z.of_nat (L5.bo_len bq) = n - l -> Z.of_nat (L5.bo_len bd) = l + 1 -> l <= n <= 299 -> 0 <= l <= 298 ->
  2 ^ 63 <= nth_w wd (Z.to_nat l) ->
  L5.u64_at RSEGS Mc (E - 232) l -> L5.u64_at RSEGS Mc (E - 224) (L5.bo_data (F + 32) bd) -> L5.u64_at RSEGS Mc (E - 216) (l + 1) ->
  L5.u64_at RSEGS Mc (E - 200) 2147450880 -> L5.u64_at RSEGS Mc (E - 208) to -> 0 <= to < 2 ^ 64 ->
  shadow_zero Mc (E - 184) 1 ->
  (let Dr := L5.bo_data ro br in let Dq := L5.bo_data qo bq in let Dd := L5.bo_data (F + 32) bd in
   (Dr + 8 * (n + 1) <= Dq \/ Dq + 8 * (n - l) <= Dr) /\ (Dr + 8 * (n + 1) <= Dd \/ Dd + 8 * (l + 1) <= Dr) /\ (Dq + 8 * (n - l) <= Dd \/ Dd + 8 * (l + 1) <= Dq)) ->
  (forall a, L5.bo_data ro br <= a < L5.bo_data ro br + 8 * (n + 1) -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a) ->
  (forall a, L5.bo_data qo bq <= a < L5.bo_data qo bq + 8 * (n - l) -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a) ->
  (qo + 32 <= ro \/ ro + 32 <= qo) -> (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall (fx1 : FPState) R1 M1 model1 br' wr' bq' wq',
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 ->
      tob (BX ++ LB) M1 ro br' wr' -> L5.bo_fb br' = L5.bo_fb br -> L5.bo_len br' = L5.bo_len br -> L5ADVEA.same_store br (L5.bo_st br') -> L5.bo_data ro br' = L5.bo_data ro br ->
      tob (BX ++ LB) M1 qo bq' wq' -> L5.bo_fb bq' = L5.bo_fb bq -> L5.bo_len bq' = L5.bo_len bq -> L5ADVEA.same_store bq (L5.bo_st bq') -> L5.bo_data qo bq' = L5.bo_data qo bq ->
      L5ADVEA.offx L ar FF E F (BX ++ LB) 0 (L5ADVGL.FP E (L5.bo_data ro br) (L5.bo_data qo bq) n l) Mc M1 ->
      L5.u64_at RSEGS M1 (E - 328) (U Rc 18) -> L5.u64_at RSEGS M1 (E - 320) (U Rc 26) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x929e8 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x9290c Mc modelc) K.
Proof.
  intros BI RI X19 X20 X21 X22 X24 AOR AOQ TR TQ TD LENR LENQ LEND NR LR DTOP S120 S128 S136 S152 S144 TOR QCZ APART WDR WDQ APO NQB KF.
  apply (G9 fx Rc Mc modelc W BX LKc crc Ac to qo br bq bd wr wq wd n l BI RI X19 X20 X21 X22 X24 AOR AOQ TR TQ TD LENR LENQ LEND NR LR DTOP S120 S128 S136 S152 S144 TOR QCZ APART WDR WDQ).
  intros fx1 R1 M1 model1 BI1 RI1 AG S24 S32.
  set (Dr := L5.bo_data ro br) in *. set (Dq := L5.bo_data qo bq) in *.
  assert (OFF : L5ADVEA.offx L ar FF E F (BX ++ LB) 0 (L5ADVGL.FP E Dr Dq n l) Mc M1) by (apply L5ADVEA.offx_of_frame; exact AG).
  assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR). assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ).
  pose proof (len_le_cap Mc ro br (proj1 TR)) as LCR. pose proof (len_le_cap Mc qo bq (proj1 TQ)) as LCQ.
  (* [comment removed for export] *)
  assert (HSO : forall o b a, (o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4) -> L5ADVEA.oreg o b a) by (intros o b a [Y|Y]; [left; exact Y | right; left; exact Y]).
  assert (DQO : forall a, Dq <= a < Dq + 8 * (n - l) -> L5ADVEA.oreg qo bq a).
  { intros a Ha. subst Dq. destruct bq as [fb len sto]. unfold L5.bo_data in *. cbn [L5.bo_st L5.bo_len] in *. destruct sto as [v0 v1|cap q].
    left. clear - Ha LCQ LENQ; lia. right; right. exists cap, q. split. reflexivity. clear - Ha LCQ LENQ; lia. }
  assert (DRO : forall a, Dr <= a < Dr + 8 * (n + 1) -> L5ADVEA.oreg ro br a).
  { intros a Ha. subst Dr. destruct br as [fb len sto]. unfold L5.bo_data in *. cbn [L5.bo_st L5.bo_len] in *. destruct sto as [v0 v1|cap q].
    left. clear - Ha LCR LENR; lia. right; right. exists cap, q. split. reflexivity. clear - Ha LCR LENR; lia. }
  assert (NFR : forall o b ws a, aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> L5ADVEA.oreg o b a -> ~ (SPA - 80 <= a < E)).
  { intros o b ws a AO TO OR X0. apply (L5ADVHA.oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac o b ws a BI AO TO OR). clear - X0 HSCR; lia. }
  assert (XDR : forall a, (ro <= a < ro + 32 \/ ro / 8 + SB <= a < ro / 8 + SB + 4) -> L5ADVGL.FP E Dr Dq n l a -> Dr <= a < Dr + 8 * Z.of_nat (L5.bo_len br)).
  { intros a HS [Y|[Y|[Y|[Y|Y]]]]; try (exfalso; apply (NFR ro br wr a AOR' TR (HSO _ _ _ HS)); clear - Y; lia).
    rewrite LENR. exact Y. exfalso. exact (OREG_DISJ W BX Mc modelc LKc crc Ac ro br wr qo bq wq a BI AOR' TR AOQ' TQ ltac:(clear - APO; lia) NQB (HSO _ _ _ HS) (DQO a Y)). }
  assert (XDQ : forall a, (qo <= a < qo + 32 \/ qo / 8 + SB <= a < qo / 8 + SB + 4) -> L5ADVGL.FP E Dr Dq n l a -> Dq <= a < Dq + 8 * Z.of_nat (L5.bo_len bq)).
  { intros a HS [Y|[Y|[Y|[Y|Y]]]]; try (exfalso; apply (NFR qo bq wq a AOQ' TQ (HSO _ _ _ HS)); clear - Y; lia).
    exfalso. exact (OREG_DISJ W BX Mc modelc LKc crc Ac qo bq wq ro br wr a BI AOQ' TQ AOR' TR APO ltac:(intros c q c' q' E1 E2 X0; exact (NQB c' q' c q E2 E1 (eq_sym X0))) (HSO _ _ _ HS) (DRO a Y)).
    rewrite LENQ. exact Y. }
  destruct (arg_data_updX W BX Mc modelc LKc crc Ac M1 0 _ ro br wr BI AOR TR OFF XDR (arg_data_def W BX M1 model1 LKc crc Ac Mc ro br BI1 AOR (proj1 TR) (proj2 (proj2 (proj2 TR)))))
    as (br' & wr' & TR' & F1 & L1 & S1 & D1).
  destruct (arg_data_updX W BX Mc modelc LKc crc Ac M1 0 _ qo bq wq BI AOQ TQ OFF XDQ (arg_data_def W BX M1 model1 LKc crc Ac Mc qo bq BI1 AOQ (proj1 TQ) (proj2 (proj2 (proj2 TQ)))))
    as (bq' & wq' & TQ' & F2 & L2 & S2 & D2).
  apply (KF fx1 R1 M1 model1 br' wr' bq' wq' BI1 RI1 TR' F1 L1 S1 D1 TQ' F2 L2 S2 D2 OFF S24 S32).
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGK2.
