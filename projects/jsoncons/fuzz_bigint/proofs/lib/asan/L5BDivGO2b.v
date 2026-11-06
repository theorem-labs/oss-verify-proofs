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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BCmp L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivLeafSpecsAB0 L5DivInnerSpecsAB0 L5BCopyAS L5BDivH L5BDivT L5BDivD L5BDivE L5BDivEA L5BDivHC L5BDivHA L5BDivHO L5BDivHL L5BDivHM L5BDivPG1 L5BDivPG2 L5BDivGL L5BDivGA L5BDivGB L5BDivGC L5BDivGD L5BDivGU L5BRed L5BDivHH L5BDivHS L5BDivGE L5BDivN L5BDivO1 L5BDivGN L5BDivGK L5BRzHuge L5BDivGK2 L5BDivGK3 L5BDivO2 L5BDivGO2 BigModel BigFactsBase BigFactsOps L5WordsB L5ParseSpecsAB0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Bo0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGO2B.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB. Import L5ADVGC. Import L5ADVGD. Import L5ADVGU. Import L5ADVHL. Import L5ADVGE. Import L5ADVGN. Import L5ADVGK. Import L5ADVGK2. Import L5ADVGK3. Import L5ADVGO2. Import L5ADVGK.
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
Hypothesis HSSH : L5OMA.stksh ar M (E - SCRD).
Hypothesis HSC8 : SCRD mod 8 = 0.
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
Local Notation HSCR0 := (L5ADVGA.HSCR0 SCRD HSCR).

Local Ltac open_ctx BI :=
  let PF := fresh "PF" in
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as PF;
  destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Notation G1 := (L5ADVGA.g1 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps).
Local Notation G2s := (L5ADVGA.g2 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps).
Local Notation G3 := (L5ADVGA.g3 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR HSSH HSC8 FFR1 FFRS Hnorm).
Local Notation G4s := (L5ADVGA.g4 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G5 := (L5ADVGA.g5 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR HSSH HSC8).
Local Notation G6 := (L5ADVGB.g6 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hasg).
Local Notation G7 := (L5ADVGC.g7 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR HSSH HSC8).
Local Notation G7b := (L5ADVGC.g7b L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G8 := (L5ADVGC.g8 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G8b := (L5ADVGC.g8b L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA).
Local Notation G9 := (L5ADVGC.g9 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR HSSH HSC8).
Local Notation RSZ := (L5ADVHH.resize_stage L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G EA HK G4 HSCR0 FFR1 FFRS Hrsz).
Local Notation ARG_AFTER := (L5ADVGN.arg_after L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G).
Local Notation OREG_DISJ := (L5ADVGN.oreg_disj L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G).
Local Notation GN_FRONT := (L5ADVGN.gn_front L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR HSSH HSC8 FFR1 FFRS Hcps Hnorm).
Local Notation G12C := (L5ADVGN.g12_copies L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hcps).
Local Notation NORM_TOBS := (L5ADVGN.norm_tobs L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR).
Local Notation STK_DEST := (L5ADVGN.stk_dest L ar C HI HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR).
Local Notation ARSZ2 := (L5ADVGK3.arg_resize2 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G EA HK G4 HSCR FFR1 FFRS Hrsz).
Local Notation G6A2 := (L5ADVGK3.g6_arg2 L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HK G4 HSCR FFR1 FFRS Hasg).
Local Notation G5A := (L5ADVGK2.g5_arg L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR HSSH HSC8).
Local Notation G9A := (L5ADVGK2.g9_arg L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER EA HSCR HSSH HSC8).
Local Notation ARG_AT := (L5ADVHA.arg_at L ar C HI LY HIok R M model LB FF LK A).
Local Notation trk := (L5ADVGO2.trk LB E F).
Local Notation TRK_KEEP := (L5ADVGO2.trk_keep L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR).
Local Notation TRK_KEEP_ARG := (L5ADVGO2.trk_keep_arg L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR).
Local Notation INV_HEAD := (L5ADVGO2.inv_head_fresh L ar C HI HIok).
Local Notation INV_APART := (L5ADVGO2.inv_blk_apart L ar C HI HIok).
Local Notation OFFX_WEAKEN := (L5ADVGO2.offx_weaken L ar FF E F).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g7_trk (qo : Z) (fx7 : FPState) R7 M7 model7 W7 BX7 LK7 cr7 A7 (bq br bn bd bn0 bd0 : L5.bigobj) wq wr wn wd on0 cells x (n l sd : Z) :
  binv W7 BX7 M7 model7 LK7 cr7 A7 -> rinvD R E R7 -> aobj FF qo 32 -> aobj FF ro 32 ->
  getr R7 (reg 20) = Z_to_bv 64 (n + 1) -> getr R7 (reg 22) = Z_to_bv 64 ro -> getr R7 (reg 24) = Z_to_bv 64 sd -> 0 <= sd < 2 ^ 64 ->
  tob (BX7 ++ LB) M7 qo bq wq -> tob (BX7 ++ LB) M7 ro br wr -> trk BX7 M7 bn bd bn0 bd0 wn wd on0 cells x ->
  Z.of_nat (L5.bo_len br) = n + 1 -> Z.of_nat (L5.bo_len bd) = l + 1 -> 0 <= n <= 299 -> 0 <= l <= 298 ->
  In (E - 272, l + 1) cells -> In (E - 120, L5.bo_data (F + 32) bd) cells ->
  (forall c v, In (c, v) cells -> (c + 8 <= E - 376 \/ E - 360 <= c) /\ (c + 8 <= E - 240 \/ E - 224 <= c)) ->
  (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W7 a) ->
  (forall (fx1 : FPState) R1 M1 model1,
      binv W7 BX7 M1 model1 LK7 cr7 A7 -> rinvD R E R1 ->
      (forall k, In k [3; 4; 18; 20; 25; 26]%nat -> getr R1 (reg k) = getr R7 (reg k)) ->
      getr R1 (reg 19) = Z_to_bv 64 n -> getr R1 (reg 21) = Z_to_bv 64 ((ro + 8) / 8 + 2147450880) -> getr R1 (reg 22) = Z_to_bv 64 (ro + 8) -> getr R1 (reg 27) = Z_to_bv 64 l ->
      tob (BX7 ++ LB) M1 qo bq wq -> tob (BX7 ++ LB) M1 ro br wr -> trk BX7 M1 bn bd bn0 bd0 wn wd on0 cells x ->
      L5.u64_at RSEGS M1 (E - 232) (Z.of_nat (L5.bo_len br)) -> L5.u64_at RSEGS M1 (E - 240) (L5.bo_data ro br) ->
      L5.u64_at RSEGS M1 (E - 376) sd -> L5.u64_at RSEGS M1 (E - 368) (ro / 8 + 2147450880) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 (if nth_w wr (Z.to_nat n) <? nth_w wd (Z.to_nat l) then 0x93350 else 0x93288) M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx7) R7 0x931d4 M7 model7) K.
Proof.
  intros BI7 RI7 AOQ AOR X20 X22 X24 SDR TQ7 TR7 TRK7 LENR LEND NR LR IN272 IN120 CELLS WSH KF.
  pose proof TRK7 as (_ & TD7 & _ & _ & SPL7 & _).
  apply (G7 fx7 R7 M7 model7 W7 BX7 LK7 cr7 A7 sd br bd wr wd n l BI7 RI7 X20 X22 X24 SDR AOR TR7 TD7 LENR LEND NR LR (proj1 (SPL7 _ _ IN272)) (proj1 (SPL7 _ _ IN120)) WSH).
  intros fx1 R1 M1 model1 BI1 RI1 KS1 p19 p21 p22 p27 AG1 S232 S240 S376 S368.
  set (X7 := fun a => E - 376 <= a < E - 360 \/ E - 240 <= a < E - 224 \/ E - 392 <= a < E - 384).
  assert (OFF1 : offx (BX7 ++ LB) 0 X7 M7 M1).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG1. exact Ha. intros Y; apply NX; left; exact Y. intros Y; apply NX; right; left; exact Y. intros Y; apply NX; right; right; exact Y. }
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  assert (NOFR : forall o b ws a, aobj FF' o 32 -> tob (BX7 ++ LB) M7 o b ws -> L5ADVEA.oreg o b a -> ~ X7 a).
  { intros o b ws a AO TO OR X0. apply (L5ADVHA.oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W7 BX7 M7 model7 LK7 cr7 A7 o b ws a BI7 AO TO OR). subst X7; cbn beta in X0. clear - X0 HSCR; lia. }
  pose proof BI7 as (B7 & _).
  assert (KEEP : forall o b ws, aobj FF' o 32 -> tob (BX7 ++ LB) M7 o b ws -> tob (BX7 ++ LB) M1 o b ws).
  { intros o b ws AO TO. apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX7 ++ LB) (BX7 ++ LB) (BX7 ++ LB) LK7 cr7 A7 model7 0 _ M7 M1 o b ws B7 AO TO OFF1).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TO)) cap q Eq) as X0. split; exact X0. intros a OR. exact (NOFR _ _ _ a AO TO OR). }
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SFB).
  assert (TRK1 : trk BX7 M1 bn bd bn0 bd0 wn wd on0 cells x).
  { apply (TRK_KEEP W7 BX7 BX7 M7 M1 model7 LK7 cr7 A7 0 _ bn bd bn0 bd0 wn wd on0 cells x BI7 OFF1 ltac:(intros b0 Hb; exact Hb) TRK7).
    - intros a OR. exact (NOFR _ _ _ a AON' (proj1 TRK7) OR).
    - intros a OR. exact (NOFR _ _ _ a AOD' TD7 OR).
    - intros i Hi X0. subst X7; cbn beta in X0. clear - Hi X0. lia.
    - intros c v Hin i Hi X0. subst X7; cbn beta in X0. destruct (CELLS c v Hin) as (Y1 & Y2). destruct (SPL7 c v Hin) as (_ & H1 & _). clear - Hi X0 Y1 Y2 H1; lia.
    - intros i Hi X0. subst X7; cbn beta in X0. clear - Hi X0 SFB. lia.
    - intros j Hj X0. subst X7; cbn beta in X0. pose proof (L5ADVGO2.sh_rng L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER j Hj) as Y. clear - Y X0 ER. lia. }
  apply (KF fx1 R1 M1 model1 BI1 RI1 KS1 p19 p21 p22 p27 (KEEP _ _ _ AOQ' TQ7) (KEEP _ _ _ AOR' TR7) TRK1 S232 S240 S376 S368).
Qed.

(* [comment removed for export] *)
Lemma frame_step W BX Mc M1 modelc LKc crc Ac (XS : Z -> Prop) :
  binv W BX Mc modelc LKc crc Ac -> (forall a, 0 <= a < 2 ^ 64 -> ~ XS a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall i, XS i -> SPA - 96 <= i < E /\ ~ (E - 220 <= i < E - 152)) ->
  (forall o b ws, aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> tob (BX ++ LB) M1 o b ws)
  /\ (forall bn bd bn0 bd0 wn wd on0 cells x, trk BX Mc bn bd bn0 bd0 wn wd on0 cells x -> (forall c v, In (c, v) cells -> forall i, c <= i < c + 8 -> ~ XS i) -> trk BX M1 bn bd bn0 bd0 wn wd on0 cells x)
  /\ (forall c v, L5.u64_at RSEGS Mc c v -> SPA <= c -> c + 8 <= E -> (forall i, c <= i < c + 8 -> ~ XS i) -> L5.u64_at RSEGS M1 c v).
Proof.
  intros BI AG XSR.
  assert (OFF1 : offx (BX ++ LB) 0 XS Mc M1). { apply L5ADVEA.offx_of_frame. exact AG. }
  assert (NOFR : forall o b ws a, aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> L5ADVEA.oreg o b a -> ~ XS a).
  { intros o b ws a AO TO OR X0. apply (L5ADVHA.oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac o b ws a BI AO TO OR). destruct (XSR a X0) as (Y & _). clear - Y HSCR; lia. }
  pose proof BI as (B7 & _).
  split; [|split].
  - intros o b ws AO TO. apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BX ++ LB) LKc crc Ac modelc 0 _ Mc M1 o b ws B7 AO TO OFF1).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TO)) cap q Eq) as X0. split; exact X0. intros a OR. exact (NOFR _ _ _ a AO TO OR).
  - intros bn bd bn0 bd0 wn wd on0 cells x TRK NXC. pose proof TRK as (TN & TD & _).
    assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
    assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
    pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SFB).
    apply (TRK_KEEP W BX BX Mc M1 modelc LKc crc Ac 0 _ bn bd bn0 bd0 wn wd on0 cells x BI OFF1 ltac:(intros b0 Hb; exact Hb) TRK).
    + intros a OR. exact (NOFR _ _ _ a AON' TN OR).
    + intros a OR. exact (NOFR _ _ _ a AOD' TD OR).
    + intros i Hi X0. exact (proj2 (XSR i X0) Hi).
    + exact NXC.
    + intros i Hi X0. destruct (XSR i X0) as (Y & _). clear - Hi Y SFB. lia.
    + intros j Hj X0. destruct (XSR j X0) as (Y & _). pose proof (L5ADVGO2.sh_rng L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER j Hj) as Y'. clear - Y Y' ER. lia.
  - intros c v Hc H1 H2 NX. exact (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BX ++ LB) 0 _ Mc M1 c v Hc H1 H2 OFF1 NX).
Qed.

(* [comment removed for export] *)
Lemma data_apart W BX Mc modelc LKc crc Ac o1 b1 ws1 o2 b2 ws2 (n1 n2 : Z) :
  binv W BX Mc modelc LKc crc Ac -> aobj FF' o1 32 -> tob (BX ++ LB) Mc o1 b1 ws1 -> aobj FF' o2 32 -> tob (BX ++ LB) Mc o2 b2 ws2 ->
  (o1 + 32 <= o2 \/ o2 + 32 <= o1) -> (forall c q c' q', L5.bo_st b1 = L5.BDyn c q -> L5.bo_st b2 = L5.BDyn c' q' -> q <> q') ->
  0 <= n1 <= Z.of_nat (L5.bo_len b1) -> 0 <= n2 <= Z.of_nat (L5.bo_len b2) ->
  L5.bo_data o1 b1 + 8 * n1 <= L5.bo_data o2 b2 \/ L5.bo_data o2 b2 + 8 * n2 <= L5.bo_data o1 b1.
Proof.
  intros BI AO1 T1 AO2 T2 AP NQ N1 N2. pose proof BI as (B1 & _).
  pose proof (len_le_cap Mc o1 b1 (proj1 T1)) as L1. pose proof (len_le_cap Mc o2 b2 (proj1 T2)) as L2.
  pose proof (proj2 (proj2 (proj2 T1))) as IN1. pose proof (proj2 (proj2 (proj2 T2))) as IN2.
  unfold L5.bo_data. destruct (L5.bo_st b1) as [u0 u1|c1 q1] eqn:E1; destruct (L5.bo_st b2) as [v0 v1|c2 q2] eqn:E2.
  - clear - AP N1 N2 L1 L2. lia.
  - edestruct L5ADVEA.blk_frame with (q := q2) (n := 8 * c2) (o := o1) as (_ & Y & _); try first [exact LY | exact HIok | exact G | exact HSCR | exact BI]. exact (IN2 c2 q2 eq_refl).
    specialize (Y AO1). clear - Y N1 N2 L1 L2. lia.
  - edestruct L5ADVEA.blk_frame with (q := q1) (n := 8 * c1) (o := o2) as (_ & Y & _); try first [exact LY | exact HIok | exact G | exact HSCR | exact BI]. exact (IN1 c1 q1 eq_refl).
    specialize (Y AO2). clear - Y N1 N2 L1 L2. lia.
  - pose proof (INV_APART (BX ++ LB) _ _ _ _ _ _ q1 (8 * c1) q2 (8 * c2) B1 (IN1 c1 q1 eq_refl) (IN2 c2 q2 eq_refl) (NQ c1 q1 c2 q2 eq_refl eq_refl)) as Y.
    clear - Y N1 N2 L1 L2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma g9_trk (fx : FPState) Rc Mc modelc W BX LKc crc Ac to qo (br bq bn bd bn0 bd0 : L5.bigobj) wr wq wn wd on0 cells x (n l : Z) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 19) = Z_to_bv 64 n -> getr Rc (reg 27) = Z_to_bv 64 l ->
  aobj FF ro 32 -> aobj FF qo 32 -> tob (BX ++ LB) Mc ro br wr -> tob (BX ++ LB) Mc qo bq wq -> trk BX Mc bn bd bn0 bd0 wn wd on0 cells x ->
  Z.of_nat (L5.bo_len br) = n + 1 -> Z.of_nat (L5.bo_len bq) = n - l -> Z.of_nat (L5.bo_len bd) = l + 1 -> l <= n <= 299 -> 0 <= l <= 298 ->
  2 ^ 63 <= nth_w wd (Z.to_nat l) ->
  In (E - 272, l + 1) cells -> In (E - 264, to) cells -> 0 <= to < 2 ^ 64 ->
  In (E - 240, L5.bo_data ro br) cells -> In (E - 136, L5.bo_data qo bq) cells -> In (E - 120, L5.bo_data (F + 32) bd) cells ->
  (forall c v, In (c, v) cells -> c + 8 <= E - 248 \/ E - 240 <= c) ->
  (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) ->
  (forall a, L5.bo_data ro br <= a < L5.bo_data ro br + 8 * (n + 1) -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a) ->
  (forall a, L5.bo_data qo bq <= a < L5.bo_data qo bq + 8 * (n - l) -> aclient L ar LB FF E SCRD a -> ~ L5.outside W a) ->
  (qo + 32 <= ro \/ ro + 32 <= qo) ->
  (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') -> (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') -> (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall (fx1 : FPState) R1 M1 model1 br' wr' bq' wq',
      binv W BX M1 model1 LKc crc Ac -> rinvD R E R1 -> getr R1 (reg 18) = getr Rc (reg 18) ->
      tob (BX ++ LB) M1 ro br' wr' -> L5.bo_fb br' = L5.bo_fb br -> L5.bo_len br' = L5.bo_len br -> L5ADVEA.same_store br (L5.bo_st br') -> L5.bo_data ro br' = L5.bo_data ro br ->
      tob (BX ++ LB) M1 qo bq' wq' -> L5.bo_fb bq' = L5.bo_fb bq -> L5.bo_len bq' = L5.bo_len bq -> L5ADVEA.same_store bq (L5.bo_st bq') -> L5.bo_data qo bq' = L5.bo_data qo bq ->
      trk BX M1 bn bd bn0 bd0 wn wd on0 cells x ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 0x93458 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x93350 Mc modelc) K.
Proof.
  intros BI RI X19 X27 AOR AOQ TR TQ TRK LENR LENQ LEND NR LR DTOP IN272 IN264 TOR IN240 IN136 IN120 CELLS WSH WDR WDQ APO NQB NQNR NQNQ NQDR NQDQ KF.
  pose proof TRK as (TN & TD & _ & _ & SPL & _).
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  pose proof (len_le_cap Mc ro br (proj1 TR)) as LCR. pose proof (len_le_cap Mc qo bq (proj1 TQ)) as LCQ.
  assert (APART : let Dr := L5.bo_data ro br in let Dq := L5.bo_data qo bq in let Dd := L5.bo_data (F + 32) bd in
            (Dr + 8 * (n + 1) <= Dq \/ Dq + 8 * (n - l) <= Dr) /\ (Dr + 8 * (n + 1) <= Dd \/ Dd + 8 * (l + 1) <= Dr) /\ (Dq + 8 * (n - l) <= Dd \/ Dd + 8 * (l + 1) <= Dq)).
  { assert (OFFA : forall o b ws, aobj FF o 32 -> tob (BX ++ LB) Mc o b ws -> forall k, 0 <= k <= 480 -> F + k + 32 <= o \/ o + 32 <= F + k).
    { intros o b ws AO TO k Hk.
      edestruct L5ADVEA.arg_off with (o := o) (a := o) as (Y1 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AO | exact TO | left; clear; lia | ].
      edestruct L5ADVEA.arg_off with (o := o) (a := o + 31) as (Y2 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AO | exact TO | left; clear; lia | ].
      clear - Hk Y1 Y2. lia. }
    cbv zeta. split.
    - apply (data_apart W BX Mc modelc LKc crc Ac ro br wr qo bq wq (n + 1) (n - l) BI AOR' TR AOQ' TQ). clear - APO; lia. exact NQB. clear - LENR NR; lia. clear - LENQ NR LR; lia.
    - split.
      + apply (data_apart W BX Mc modelc LKc crc Ac ro br wr (F + 32) bd wd (n + 1) (l + 1) BI AOR' TR AOD' TD). destruct (OFFA ro br wr AOR TR 32 ltac:(clear; lia)) as [Y|Y]; clear - Y; lia.
        intros c q c' q' E1 E2 X0. exact (NQDR c' q' c q E2 E1 (eq_sym X0)). clear - LENR NR; lia. clear - LEND LR; lia.
      + apply (data_apart W BX Mc modelc LKc crc Ac qo bq wq (F + 32) bd wd (n - l) (l + 1) BI AOQ' TQ AOD' TD). destruct (OFFA qo bq wq AOQ TQ 32 ltac:(clear; lia)) as [Y|Y]; clear - Y; lia.
        intros c q c' q' E1 E2 X0. exact (NQDQ c' q' c q E2 E1 (eq_sym X0)). clear - LENQ NR LR; lia. clear - LEND LR; lia. }
  apply (G9A fx Rc Mc modelc W BX LKc crc Ac to qo br bq bd wr wq wd n l BI RI X19 X27 AOR AOQ TR TQ TD LENR LENQ LEND NR LR DTOP
           (proj1 (SPL _ _ IN272)) (proj1 (SPL _ _ IN264)) TOR (proj1 (SPL _ _ IN240)) (proj1 (SPL _ _ IN136)) (proj1 (SPL _ _ IN120)) WSH APART WDR WDQ APO NQB).
  intros fx1 R1 M1 model1 br' wr' bq' wq' BI1 RI1 K18 TR1 FR1 LR1 SR1 DR1 TQ1 FQ1 LQ1 SQ1 DQ1 OFF1.
  set (Dr := L5.bo_data ro br) in *. set (Dq := L5.bo_data qo bq) in *.
  assert (DSR : forall a, Dr <= a < Dr + 8 * (n + 1) -> L5ADVEA.oreg ro br a).
  { intros a Ha. subst Dr. unfold L5.bo_data in Ha. destruct (L5.bo_st br) as [v0 v1|cap q] eqn:EST.
    left. clear - Ha LCR LENR. lia. right; right. exists cap, q. split. exact EST. clear - Ha LCR LENR. lia. }
  assert (DSQ : forall a, Dq <= a < Dq + 8 * (n - l) -> L5ADVEA.oreg qo bq a).
  { intros a Ha. subst Dq. unfold L5.bo_data in Ha. destruct (L5.bo_st bq) as [v0 v1|cap q] eqn:EST.
    left. clear - Ha LCQ LENQ. lia. right; right. exists cap, q. split. exact EST. clear - Ha LCQ LENQ. lia. }
  assert (AOFF : forall o b ws a, aobj FF o 32 -> tob (BX ++ LB) Mc o b ws -> L5ADVEA.oreg o b a -> ~ (F <= a < F + 512) /\ ~ (SPA <= a < E)).
  { intros o b ws a AO TO OR. edestruct L5ADVEA.arg_off with (o := o) (a := a) as (Y1 & _ & Y3 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AO | exact TO | exact OR | ]. split; assumption. }
  assert (APF : forall o b ws, aobj FF o 32 -> tob (BX ++ LB) Mc o b ws -> forall k, 0 <= k <= 480 -> F + k + 32 <= o \/ o + 32 <= F + k).
  { intros o b ws AO TO k Hk. destruct (AOFF o b ws o AO TO ltac:(left; clear; lia)) as (Y1 & _). destruct (AOFF o b ws (o + 31) AO TO ltac:(left; clear; lia)) as (Y2 & _). clear - Hk Y1 Y2. lia. }
  assert (NOFR : forall o b ws a, aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> L5ADVEA.oreg o b a -> ~ (E - SCRD <= a < E)).
  { intros o b ws a AO TO OR. exact (L5ADVHA.oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac o b ws a BI AO TO OR). }
  assert (FSTK : F + 512 <= E - SCRD). { destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL _ _ _ _ _ _ _ _ _ _ _ _ _ _]. change (ff_bytes 3) with 512 in FCEIL. clear - SLO FCEIL. lia. }
  assert (TRK1 : trk BX M1 bn bd bn0 bd0 wn wd on0 cells x).
  { apply (TRK_KEEP W BX BX Mc M1 modelc LKc crc Ac 0 _ bn bd bn0 bd0 wn wd on0 cells x BI OFF1 ltac:(intros b0 Hb; exact Hb) TRK).
    - intros a ORn [X0|[X0|[X0|[X0|X0]]]].
      + apply (NOFR _ _ _ a AON' TN ORn). clear - X0 HSCR. lia.
      + apply (NOFR _ _ _ a AON' TN ORn). clear - X0 HSCR. lia.
      + apply (NOFR _ _ _ a AON' TN ORn). clear - X0 HSCR. lia.
      + exact (OREG_DISJ W BX Mc modelc LKc crc Ac (F + 96) bn wn ro br wr a BI AON' TN AOR' TR (APF ro br wr AOR TR 96 ltac:(clear; lia)) NQNR ORn (DSR a X0)).
      + exact (OREG_DISJ W BX Mc modelc LKc crc Ac (F + 96) bn wn qo bq wq a BI AON' TN AOQ' TQ (APF qo bq wq AOQ TQ 96 ltac:(clear; lia)) NQNQ ORn (DSQ a X0)).
    - intros a ORd [X0|[X0|[X0|[X0|X0]]]].
      + apply (NOFR _ _ _ a AOD' TD ORd). clear - X0 HSCR. lia.
      + apply (NOFR _ _ _ a AOD' TD ORd). clear - X0 HSCR. lia.
      + apply (NOFR _ _ _ a AOD' TD ORd). clear - X0 HSCR. lia.
      + exact (OREG_DISJ W BX Mc modelc LKc crc Ac (F + 32) bd wd ro br wr a BI AOD' TD AOR' TR (APF ro br wr AOR TR 32 ltac:(clear; lia)) NQDR ORd (DSR a X0)).
      + exact (OREG_DISJ W BX Mc modelc LKc crc Ac (F + 32) bd wd qo bq wq a BI AOD' TD AOQ' TQ (APF qo bq wq AOQ TQ 32 ltac:(clear; lia)) NQDQ ORd (DSQ a X0)).
    - intros i Hi [X0|[X0|[X0|[X0|X0]]]]; try (clear - Hi X0; lia).
      + apply (proj2 (AOFF ro br wr i AOR TR (DSR i X0))). clear - Hi; lia.
      + apply (proj2 (AOFF qo bq wq i AOQ TQ (DSQ i X0))). clear - Hi; lia.
    - intros c v Hin i Hi [X0|[X0|[X0|[X0|X0]]]]; destruct (SPL c v Hin) as (_ & H1 & H2); pose proof (CELLS c v Hin) as Y2.
      + clear - Hi X0 H1. lia.
      + destruct X0.
      + clear - Hi X0 Y2. lia.
      + apply (proj2 (AOFF ro br wr i AOR TR (DSR i X0))). clear - Hi H1 H2; lia.
      + apply (proj2 (AOFF qo bq wq i AOQ TQ (DSQ i X0))). clear - Hi H1 H2; lia.
    - intros i Hi [X0|[X0|[X0|[X0|X0]]]].
      + clear - Hi X0 FSTK HSCR. lia.
      + clear - Hi X0 FSTK HSCR. lia.
      + clear - Hi X0 FSTK HSCR. lia.
      + apply (proj1 (AOFF ro br wr i AOR TR (DSR i X0))). clear - Hi; lia.
      + apply (proj1 (AOFF qo bq wq i AOQ TQ (DSQ i X0))). clear - Hi; lia.
    - intros j Hj [X0|[X0|[X0|[X0|X0]]]]; try (pose proof (L5ADVGO2.sh_rng L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER j Hj) as Y; clear - Y X0 ER; lia).
      + edestruct L5ADVEA.arg_off with (o := ro) (a := j) as (_ & Y2 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AOR | exact TR | exact (DSR j X0) | ]. exact (Y2 Hj).
      + edestruct L5ADVEA.arg_off with (o := qo) (a := j) as (_ & Y2 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI | exact AOQ | exact TQ | exact (DSQ j X0) | ]. exact (Y2 Hj). }
  apply (KF fx1 R1 M1 model1 br' wr' bq' wq' BI1 RI1 K18 TR1 FR1 LR1 SR1 DR1 TQ1 FQ1 LQ1 SQ1 DQ1 TRK1).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gB_trk (fx : FPState) Rc Mc modelc W BX LKc crc Ac qo (br bq bn bd bn0 bd0 : L5.bigobj) wr wq wn wd on0 cells x (n lenq : nat) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc -> aobj FF ro 32 -> aobj FF qo 32 -> (qo + 32 <= ro \/ ro + 32 <= qo) -> 0 <= qo < 2 ^ 64 ->
  getr Rc (reg 20) = Z_to_bv 64 (Z.of_nat n + 1) -> getr Rc (reg 21) = Z_to_bv 64 ((ro + 8) / 8 + 2147450880) -> getr Rc (reg 22) = Z_to_bv 64 (ro + 8) ->
  getr Rc (reg 26) = Z_to_bv 64 (qo + 8) ->
  tob (BX ++ LB) Mc ro br wr -> L5.bo_len br = Datatypes.S n -> tob (BX ++ LB) Mc qo bq wq -> L5.bo_len bq = lenq -> trk BX Mc bn bd bn0 bd0 wn wd on0 cells x ->
  In (E - 296, qo) cells -> In (E - 288, ro) cells -> In (E - 320, qo / 8 + 2147450880) cells -> In (E - 352, (qo + 8) / 8 + 2147450880) cells -> In (E - 368, ro / 8 + 2147450880) cells ->
  L5.u64_at RSEGS Mc (E - 232) (Z.of_nat (Datatypes.S n)) -> L5.u64_at RSEGS Mc (E - 128) (Z.of_nat lenq) ->
  (forall c v, In (c, v) cells -> (c + 8 <= E - 240 \/ E - 224 <= c) /\ (c + 8 <= E - 136 \/ E - 120 <= c)) ->
  (n <= 298)%nat -> (lenq <= 298)%nat ->
  (L5.bo_dyn br = true -> Z.of_nat n + 2 <= L5.bo_cap br) -> (L5.bo_dyn bq = true -> Z.of_nat lenq + 1 <= L5.bo_cap bq) ->
  L5OMA.acredit_for L crc ((if L5.bo_dyn br then 0 else 1) + (if L5.bo_dyn bq then 0 else 1)) ((if L5.bo_dyn br then 0 else 8 * round_up (Z.of_nat n + 2)) + (if L5.bo_dyn bq then 0 else 8 * round_up (Z.of_nat lenq + 1))) ->
  (forall a, L5.outside W a -> L5.outside [(ro, 32)] a /\ L5.outside [(qo, 32)] a) ->
  ((L5.bo_dyn br = true \/ (Datatypes.S (Datatypes.S n) <= 2)%nat) -> forall a, aclient L ar LB FF E SCRD a -> L5.outside W a ->
      ~ L5.in_rng (L5.bo_data ro br + 8 * Z.of_nat (Datatypes.S n), 8 * Z.max 0 (Z.of_nat (Datatypes.S (Datatypes.S n)) - Z.of_nat (Datatypes.S n))) a) ->
  ((L5.bo_dyn bq = true \/ (Datatypes.S lenq <= 2)%nat) -> forall a, aclient L ar LB FF E SCRD a -> L5.outside W a ->
      ~ L5.in_rng (L5.bo_data qo bq + 8 * Z.of_nat lenq, 8 * Z.max 0 (Z.of_nat (Datatypes.S lenq) - Z.of_nat lenq)) a) ->
  (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') -> (forall c q c' q', L5.bo_st bn = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st br = L5.BDyn c' q' -> q <> q') -> (forall c q c' q', L5.bo_st bd = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q') ->
  (forall (fx9 : FPState) R9 M9 model9 (gr gq : growth) br9 bq9 cr9 LK9 A9,
      let BXr := match gr with Same => BX | Grown q cap => (q, 8 * cap) :: BX end in
      let BX9 := match gq with Same => BXr | Grown q cap => (q, 8 * cap) :: BXr end in
      binv W BX9 M9 model9 LK9 cr9 A9 -> rinvD R E R9 ->
      (forall k, In k [3; 4; 18; 20; 24; 25; 26; 27]%nat -> getr R9 (reg k) = getr Rc (reg k)) ->
      getr R9 (reg 19) = Z_to_bv 64 (Z.of_nat n + 1) ->
      tob (BX9 ++ LB) M9 ro br9 (resize_limbs wr (Datatypes.S (Datatypes.S n))) -> L5.bo_len br9 = Datatypes.S (Datatypes.S n) ->
      (match gr with Same => L5.bo_fb br9 = L5.bo_fb br /\ L5ADVEA.same_store br (L5.bo_st br9)
                   | Grown q cap => L5.bo_fb br9 = Z.lor (L5.bo_fb br) 1 /\ L5.bo_st br9 = L5.BDyn cap q /\ cap = round_up (Z.of_nat (Datatypes.S (Datatypes.S n))) /\ L5.bo_dyn br = false /\ (3 <= Datatypes.S (Datatypes.S n))%nat end) ->
      tob (BX9 ++ LB) M9 qo bq9 (resize_limbs wq (Datatypes.S lenq)) -> L5.bo_len bq9 = Datatypes.S lenq ->
      (match gq with Same => L5.bo_fb bq9 = L5.bo_fb bq /\ L5ADVEA.same_store bq (L5.bo_st bq9)
                   | Grown q cap => L5.bo_fb bq9 = Z.lor (L5.bo_fb bq) 1 /\ L5.bo_st bq9 = L5.BDyn cap q /\ cap = round_up (Z.of_nat (Datatypes.S lenq)) /\ L5.bo_dyn bq = false /\ (3 <= Datatypes.S lenq)%nat end) ->
      trk BX9 M9 bn bd bn0 bd0 wn wd on0 cells x ->
      L5.u64_at RSEGS M9 (E - 240) (L5.bo_data ro br9) -> L5.u64_at RSEGS M9 (E - 136) (L5.bo_data qo bq9) ->
      cr9 = L5DLA.adebl L (L5DLA.adebl L crc (L5DLA.blocks_of gr)) (L5DLA.blocks_of gq) -> incl Ac A9 -> incl LK9 LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx9) R9 0x93350 M9 model9) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x93288 Mc modelc) K.
Proof.
  intros BI RI AOR AOQ APO QOR X20 X21 X22 X26 TR LENR TQ LENQ TRK IN296 IN288 IN320 IN352 IN368 S232 S128 CELLS NB LQB CAPR CAPQ CRD WHDR WTR WTQ NQB NQNR NQNQ NQDR NQDQ KF.
  pose proof TRK as (TN & TD & _ & _ & SPL & _).
  assert (AOQ' : aobj FF' qo 32) by (apply aobj_cons; exact AOQ). assert (AOR' : aobj FF' ro 32) by (apply aobj_cons; exact AOR).
  assert (AOFF : forall W' BX' M' model' LK' cr' A' o b ws a, binv W' BX' M' model' LK' cr' A' -> aobj FF o 32 -> tob (BX' ++ LB) M' o b ws -> L5ADVEA.oreg o b a -> ~ (SPA <= a < E)).
  { intros W' BX' M' model' LK' cr' A' o b ws a BI' AO TO OR. edestruct L5ADVEA.arg_off with (o := o) (a := a) as (_ & _ & Y3 & _); try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI' | exact AO | exact TO | exact OR | ]. exact Y3. }
  assert (RUN : 8 <= round_up (Z.of_nat n + 2) /\ 8 <= round_up (Z.of_nat lenq + 1)).
  { unfold round_up. clear. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  apply (G7b fx Rc Mc modelc W BX LKc crc Ac br BI RI (proj1 (SPL _ _ IN288)) AOR (proj1 (proj2 (proj2 TR))) (proj1 TR) ltac:(rewrite LENR; exact S232)).
  intros fx1 R1 model1 BI1 RI1 KS1 p1 p10 p11 p19. rewrite LENR in p11.
  assert (P11 : getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat (Datatypes.S (Datatypes.S n)))). { rewrite p11. f_equal. clear. lia. }
  apply (ARSZ2 fx1 R1 Mc model1 W W BX LKc crc Ac ro 0x9329c (Datatypes.S (Datatypes.S n)) br wr BI1 RI1 p10 P11 p1 ltac:(split; [clear; lia | reflexivity]) AOR TR).
  { clear - NB. lia. }
  { intros DY. pose proof (CAPR DY) as X0. clear - X0. lia. }
  { intros _ DYF. replace (Z.of_nat (Datatypes.S (Datatypes.S n))) with (Z.of_nat n + 2) by (clear; lia). rewrite DYF in CRD. apply (cred_ok1 L C LY crc _ _ _ CRD). destruct (L5.bo_dyn bq); clear; lia. destruct (L5.bo_dyn bq); clear - RUN; lia. }
  { intros a OUT. split. exact OUT. exact (proj1 (WHDR a OUT)). }
  { rewrite LENR. exact WTR. }
  intros fx2 R2 M2' model2' gr br9 cr2' LK2' A2 RP2 BI2 TR2 LENR2 GRF OFF2 IA2 ILK2.
  set (BXr := match gr with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) in *.
  assert (SUBr : forall b0, In b0 (BX ++ LB) -> In b0 (BXr ++ LB)). { intros b0 Hb. subst BXr. destruct gr. exact Hb. right. exact Hb. }
  pose proof BI1 as (B1 & _).
  assert (TRK2 : trk BXr M2' bn bd bn0 bd0 wn wd on0 cells x).
  { exact (TRK_KEEP_ARG W BX BXr Mc M2' model1 LKc crc Ac RESIZE_SCR ro br wr bn bd bn0 bd0 wn wd on0 cells x BI1 AOR TR OFF2 SUBr TRK NQNR NQDR). }
  assert (TQ2 : tob (BXr ++ LB) M2' qo bq wq).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BX ++ LB) (BX ++ LB) (BXr ++ LB) LKc crc Ac model1 RESIZE_SCR _ Mc M2' qo bq wq B1 AOQ' TQ OFF2).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TQ)) cap q Eq) as X0. split. exact X0. apply SUBr. exact X0.
    intros a O1 O2. exact (OREG_DISJ W BX Mc model1 LKc crc Ac ro br wr qo bq wq a BI1 AOR' TR AOQ' TQ ltac:(clear - APO; lia) NQB O2 O1). }
  (* [comment removed for export] *)
  assert (RI2 : rinvD R E R2) by (apply (rinvD_pres R E R1 R2 RI1 RP2)).
  assert (KR2 : forall k, In k [3; 4; 18; 20; 21; 22; 24; 25; 26; 27]%nat -> getr R2 (reg k) = getr Rc (reg k)).
  { intros k Hk. rewrite (cs_of_preserved R1 R2 k RP2) by (revert Hk; apply (L5K.incl_b [3; 4; 18; 20; 21; 22; 24; 25; 26; 27]%nat); vm_compute; reflexivity).
    apply KS1. revert Hk. apply (L5K.incl_b [3; 4; 18; 20; 21; 22; 24; 25; 26; 27]%nat). vm_compute; reflexivity. }
  pose proof BI2 as (B2 & _).
  pose proof TRK2 as (_ & _ & _ & _ & SPL2 & _).
  assert (S128_2 : L5.u64_at RSEGS M2' (E - 128) (Z.of_nat lenq)).
  { apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BX ++ LB) RESIZE_SCR _ Mc M2' _ _ S128 ltac:(clear; lia) ltac:(clear; lia) OFF2).
    intros i Hi OR. apply (AOFF _ _ _ _ _ _ _ ro br wr i BI1 AOR TR OR). clear - Hi; lia. }
  apply (G8 fx2 R2 M2' model2' W BXr LK2' cr2' A2 qo (Z.of_nat lenq) br9 BI2 RI2 ltac:(rewrite (cs_of_preserved R1 R2 19 RP2) by inl; exact p19) ltac:(rewrite (KR2 21%nat) by inl; exact X21)
           ltac:(rewrite (KR2 22%nat) by inl; exact X22) QOR ltac:(clear - LQB; lia) AOR (proj1 (proj2 (proj2 TR2))) (proj1 TR2) (proj1 (SPL2 _ _ IN368)) (proj1 (SPL2 _ _ IN296)) S128_2).
  intros fx3 R3 M3 model3 BI3 RI3 KS3 q1 q10 q11 AG3 S240_3 S232_3.
  destruct (frame_step W BXr M2' M3 model2' LK2' cr2' A2 (fun a => E - 240 <= a < E - 224) BI2 AG3 ltac:(intros i Hi; cbv beta in Hi; split; clear - Hi; lia)) as (KEEP3 & TKEEP3 & _).
  assert (TRK3 : trk BXr M3 bn bd bn0 bd0 wn wd on0 cells x).
  { apply (TKEEP3 _ _ _ _ _ _ _ _ _ TRK2). intros c v Hin i Hi X0. destruct (CELLS c v Hin) as (Y1 & _). clear - Hi X0 Y1; lia. }
  pose proof (KEEP3 _ _ _ AOR' TR2) as TR3. pose proof (KEEP3 _ _ _ AOQ' TQ2) as TQ3.
  assert (Q11 : getr R3 (reg 11) = Z_to_bv 64 (Z.of_nat (Datatypes.S lenq))). { rewrite q11. f_equal. clear. lia. }
  assert (CR2 : (3 <= Datatypes.S lenq)%nat -> L5.bo_dyn bq = false -> acredit_ok L cr2' (8 * round_up (Z.of_nat (Datatypes.S lenq)))).
  { intros _ DQF. replace (Z.of_nat (Datatypes.S lenq)) with (Z.of_nat lenq + 1) by (clear; lia). rewrite DQF in CRD. destruct gr as [|qg capg].
    - destruct GRF as (_ & _ & ->). apply (cred_ok1 L C LY crc _ _ _ CRD). destruct (L5.bo_dyn br); clear; lia. destruct (L5.bo_dyn br); clear - RUN; lia.
    - destruct GRF as (_ & _ & EC & -> & DRF & _). rewrite DRF in CRD. change (1 + 1) with 2 in CRD. rewrite EC. replace (Z.of_nat (Datatypes.S (Datatypes.S n))) with (Z.of_nat n + 2) by (clear; lia).
      pose proof (cred_step L crc 2 _ (8 * round_up (Z.of_nat n + 2)) CRD ltac:(clear; lia) ltac:(clear - RUN; lia)) as X0.
      apply (cred_ok1 L C LY _ (2 - 1) _ (8 * round_up (Z.of_nat lenq + 1)) X0). clear; lia. clear - RUN; lia. }
  apply (ARSZ2 fx3 R3 M3 model3 W W BXr LK2' cr2' A2 qo 0x932f8 (Datatypes.S lenq) bq wq BI3 RI3 q10 Q11 q1 ltac:(split; [clear; lia | reflexivity]) AOQ TQ3).
  { clear - LQB. lia. }
  { intros DY. pose proof (CAPQ DY) as X0. clear - X0. lia. }
  { exact CR2. }
  { intros a OUT. split. exact OUT. exact (proj2 (WHDR a OUT)). }
  { rewrite LENQ. exact WTQ. }
  intros fx4 R4 M4 model4 gq bq9 cr4 LK4 A4 RP4 BI4 TQ4 LENQ4 GQF OFF4 IA4 ILK4.
  set (BX9 := match gq with Same => BXr | Grown q cap => (q, 8 * cap) :: BXr end) in *.
  assert (SUB9 : forall b0, In b0 (BXr ++ LB) -> In b0 (BX9 ++ LB)). { intros b0 Hb. subst BX9. destruct gq. exact Hb. right. exact Hb. }
  pose proof BI3 as (B3 & _).
  (* [comment removed for export] *)
  assert (NQB9 : forall c q c' q', L5.bo_st br9 = L5.BDyn c q -> L5.bo_st bq = L5.BDyn c' q' -> q <> q').
  { intros c q c' q' Eq Eq'. destruct gr as [|qg capg].
    - destruct GRF as (_ & SS & _). unfold L5ADVEA.same_store in SS. rewrite Eq in SS. destruct (L5.bo_st br) as [? ?|c0 q0] eqn:E0. destruct SS. destruct SS as (EC0 & EQ0).
      intros X0. apply (NQB c0 q0 c' q' eq_refl Eq'). clear - X0 EQ0. first [lia | congruence].
    - destruct GRF as (_ & ST & _). rewrite ST in Eq. injection Eq as <- <-. subst BXr. cbn [app] in B2.
      apply (INV_HEAD qg (8 * capg) (BX ++ LB) _ _ _ _ _ _ q' (8 * c') B2). exact (proj2 (proj2 (proj2 TQ)) c' q' Eq'). }
  assert (TRK4 : trk BX9 M4 bn bd bn0 bd0 wn wd on0 cells x).
  { exact (TRK_KEEP_ARG W BXr BX9 M3 M4 model3 LK2' cr2' A2 RESIZE_SCR qo bq wq bn bd bn0 bd0 wn wd on0 cells x BI3 AOQ TQ3 OFF4 SUB9 TRK3 NQNQ NQDQ). }
  assert (TR4 : tob (BX9 ++ LB) M4 ro br9 (resize_limbs wr (Datatypes.S (Datatypes.S n)))).
  { apply (L5ADVEA.tob_keep' L ar C HI LY HIok FF E F (BXr ++ LB) (BXr ++ LB) (BX9 ++ LB) LK2' cr2' A2 model3 RESIZE_SCR _ M3 M4 ro br9 _ B3 AOR' TR3 OFF4).
    intros cap q Eq. pose proof (proj2 (proj2 (proj2 TR3)) cap q Eq) as X0. split. exact X0. apply SUB9. exact X0.
    intros a O1 O2. exact (OREG_DISJ W BXr M3 model3 LK2' cr2' A2 ro br9 _ qo bq wq a BI3 AOR' TR3 AOQ' TQ3 ltac:(clear - APO; lia) NQB9 O1 O2). }
  assert (S240_4 : L5.u64_at RSEGS M4 (E - 240) (L5.bo_data ro br9)).
  { apply (L5ADVEA.spill_keep L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER HSCR0 (BXr ++ LB) RESIZE_SCR _ M3 M4 _ _ S240_3 ltac:(clear; lia) ltac:(clear; lia) OFF4).
    intros i Hi OR. apply (AOFF _ _ _ _ _ _ _ qo bq wq i BI3 AOQ TQ3 OR). clear - Hi; lia. }
  (* [comment removed for export] *)
  assert (RI4 : rinvD R E R4) by (apply (rinvD_pres R E R3 R4 RI3 RP4)).
  assert (KR4 : forall k, In k [3; 4; 18; 20; 21; 22; 24; 25; 26; 27]%nat -> getr R4 (reg k) = getr Rc (reg k)).
  { intros k Hk. rewrite (cs_of_preserved R3 R4 k RP4) by (revert Hk; apply (L5K.incl_b [3; 4; 18; 20; 21; 22; 24; 25; 26; 27]%nat); vm_compute; reflexivity).
    rewrite (KS3 k) by (revert Hk; apply (L5K.incl_b [3; 4; 18; 20; 21; 22; 24; 25; 26; 27]%nat); vm_compute; reflexivity). apply KR2. exact Hk. }
  pose proof TRK4 as (_ & _ & _ & _ & SPL4 & _).
  apply (G8b fx4 R4 M4 model4 W BX9 LK4 cr4 A4 qo (Z.of_nat n + 1) bq9 BI4 RI4 ltac:(rewrite (KR4 20%nat) by inl; exact X20) ltac:(rewrite (KR4 26%nat) by inl; exact X26)
           ltac:(clear - NB; lia) AOQ (proj1 (proj2 (proj2 TQ4))) (proj1 TQ4) (proj1 (SPL4 _ _ IN320)) (proj1 (SPL4 _ _ IN352)) (proj1 (SPL4 _ _ IN296))).
  intros fx5 R5 M5 model5 BI5 RI5 KS5 s19 AG5 S136_5 S128_5.
  destruct (frame_step W BX9 M4 M5 model4 LK4 cr4 A4 (fun a => E - 136 <= a < E - 120) BI4 AG5 ltac:(intros i Hi; cbv beta in Hi; split; clear - Hi; lia)) as (KEEP5 & TKEEP5 & CKEEP5).
  assert (TRK5 : trk BX9 M5 bn bd bn0 bd0 wn wd on0 cells x).
  { apply (TKEEP5 _ _ _ _ _ _ _ _ _ TRK4). intros c v Hin i Hi X0. destruct (CELLS c v Hin) as (_ & Y2). clear - Hi X0 Y2; lia. }
  apply (KF fx5 R5 M5 model5 gr gq br9 bq9 cr4 LK4 A4 BI5 RI5).
  - intros k Hk. rewrite (KS5 k) by (revert Hk; apply (L5K.incl_b [3; 4; 18; 20; 24; 25; 26; 27]%nat); vm_compute; reflexivity).
    apply KR4. revert Hk. apply (L5K.incl_b [3; 4; 18; 20; 24; 25; 26; 27]%nat). vm_compute; reflexivity.
  - exact s19.
  - exact (KEEP5 _ _ _ AOR' TR4).
  - exact LENR2.
  - destruct gr as [|qg capg]. exact (conj (proj1 GRF) (proj1 (proj2 GRF))). destruct GRF as (G1 & G2' & G3 & _ & G5'). split. exact G1. split. exact G2'. split. exact G3. exact G5'.
  - exact (KEEP5 _ _ _ AOQ' TQ4).
  - exact LENQ4.
  - destruct gq as [|qg capg]. exact (conj (proj1 GQF) (proj1 (proj2 GQF))). destruct GQF as (G1 & G2' & G3 & _ & G5'). split. exact G1. split. exact G2'. split. exact G3. exact G5'.
  - exact TRK5.
  - apply (CKEEP5 _ _ S240_4). clear; lia. clear; lia. intros i Hi X0. clear - Hi X0; lia.
  - exact S136_5.
  - destruct gq as [|qg capg]; destruct gr as [|qr capr]; cbn [L5DLA.blocks_of L5DLA.adebl].
    + rewrite (proj2 (proj2 GQF)). exact (proj2 (proj2 GRF)).
    + rewrite (proj2 (proj2 GQF)). destruct GRF as (_ & _ & _ & -> & _). reflexivity.
    + destruct GQF as (_ & _ & _ & -> & _). rewrite (proj2 (proj2 GRF)). reflexivity.
    + destruct GQF as (_ & _ & _ & -> & _). destruct GRF as (_ & _ & _ & -> & _). reflexivity.
  - intros a0 Ha0. apply IA4. apply IA2. exact Ha0.
  - intros f0 Hf0. apply ILK2. apply ILK4. exact Hf0.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGO2B.
