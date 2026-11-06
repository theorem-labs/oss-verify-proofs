(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5DivSpecsA L5OpmodSpecsA L5DivLeafSpecsA L5DivInnerSpecsA L5ParseSpecsA L5UnwindSpecsA L5ATopX L5ADivEA L5ADivO1 L5AOpModH L5AOpMod.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AOME3.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Lemma u64_eq M a a' v v' : L5.u64_at RSEGS M a v -> a = a' -> v = v' -> L5.u64_at RSEGS M a' v'.
Proof. intros H -> ->. exact H. Qed.
Lemma u32_eq M a a' v : L5.u32_at RSEGS M a v -> a = a' -> L5.u32_at RSEGS M a' v.
Proof. intros H ->. exact H. Qed.
Lemma big_eq M a a' b : L5.big_at RSEGS M a b -> a = a' -> L5.big_at RSEGS M a' b.
Proof. intros H ->. exact H. Qed.
Lemma in5 {T : Type} (a b c d e : T) l x : In x (a :: b :: c :: d :: e :: l) <-> In x ([a; b; d; e] ++ c :: l).
Proof. cbn. tauto. Qed.
Lemma in3 {T : Type} (a b c : T) l x : In x (a :: b :: c :: l) <-> In x (c :: a :: b :: l).
Proof. cbn. tauto. Qed.
Lemma nodup5 (a b c d e : Z * Z) l : NoDup (map fst (a :: b :: c :: d :: e :: l)) -> NoDup (map fst ([a; b; d; e] ++ c :: l)).
Proof.
  intros ND. apply base.NoDup_ListNoDup. apply base.NoDup_ListNoDup in ND. revert ND.
  apply Permutation_NoDup. apply Permutation_map. apply perm_skip. apply perm_skip. apply (Permutation_middle [d; e] l c).
Qed.
Lemma nodup3 (a b c : Z * Z) l : NoDup (map fst (a :: b :: c :: l)) -> NoDup (map fst (c :: a :: b :: l)).
Proof.
  intros ND. apply base.NoDup_ListNoDup. apply base.NoDup_ListNoDup in ND. revert ND.
  apply Permutation_NoDup. apply Permutation_map. symmetry. apply (Permutation_middle [a; b] l c).
Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

(* [comment removed for export] *)
Lemma aclient_lb_incl LB LB' FF sp scr a : (forall b, In b LB -> In b LB') -> aclient L ar LB FF sp scr a -> aclient L ar LB' FF sp scr a.
Proof.
  intros I X. unfold aclient, aclient_g in *. destruct X as [X|[X|[X|[X|[X|[X|X]]]]]].
  - left. destruct X as (b & Hb & Y). exists b. split. apply I; exact Hb. exact Y.
  - right; left; exact X.
  - right; right; left; exact X.
  - right; right; right; left; exact X.
  - right; right; right; right; left; exact X.
  - right; right; right; right; right; left; exact X.
  - right; right; right; right; right; right. destruct X as (b & Hb & Y). exists b. split. apply I; exact Hb. exact Y.
Qed.
(* [comment removed for export] *)
Lemma fr_live_re LB LB' FFb FFb' M k F fl rs rs' :
  L5DSA.fr_live L ar LB FFb M k F fl rs -> (forall b, In b LB' -> In b LB) -> FFb = FFb' -> rs = rs' -> L5DSA.fr_live L ar LB' FFb' M k F fl rs'.
Proof.
  intros [c f n a h] I <- <-. constructor; try assumption. intros X. apply n. revert X. apply aclient_lb_incl. exact I.
Qed.

Theorem om1_e3_arm_ok : L5USA.e3_chainA_spec_of L ar HI (L5DIA.assert_throw_atA L ar) -> L5USA.as0_unw_layout L -> L5AOPMOD.om1_e3_arm L ar HI.
Proof.
  intros He3 UNWL R M model K LB FF LK cr A xo bo E r fbx bb wb st F fl fx' Rt Mt modelt LBt crt LKt At F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx
         HH AM HK G1 RE G9 G2 A32 G4 STK G3 SSH FFRS XA AOX SZX BOK AOB SZB APXB CRF XSP E3A RTt IAt AMt ILKt HHt KE3.
  pose proof (as0_layout2_of L C LY) as LY2.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold L5AOPMOD.SCRo in SLO.
  assert (ER : 140735332487680 <= E <= 140737488355328 /\ 0 <= E < 2 ^ 64) by (clear - SLO SHI SPT; lia). destruct ER as (ER & ERG).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model xo 32 E L5AOPMOD.SCRo HH AOX ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & _ & _ & _ & OCL & _).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model bo 32 E L5AOPMOD.SCRo HH AOB ltac:(clear; lia) ltac:(reflexivity)) as (DR & DBIG & _).
  (* [comment removed for export] *)
  destruct E3A as (R1 & Mq & (U1_1 & U1_8 & U1_9 & U1_18 & U1_19 & U1_20 & U1_21 & U1_22 & U1_23 & U1_24 & U1_25 & U1_26 & U1_27) & G1_3 & G1_4 & DO1 & QOWN & SHOPa & LIVEa & AHPa).
  destruct DO1 as (RU & MU & d3 & d4 & lenX & LBm & crm & fbx' & fd0 & fn0 & fn & fden & v0 & v1 & v2 & v3 & nd0 & nn0 & nn & nd & bq
                   & UU1 & UU8 & UU9 & UU18 & UU19 & UU20 & UU21 & UU22 & UU23 & UU24 & UU27 & GU3 & GU4 & ELBm & UNE & DSAVa
                   & Oa336 & Oa296 & Oa280 & Oa272 & Oa264 & Oa256 & Oa248 & Oa240 & Oa208 & Oa200 & Oa192
                   & BDEN0a & BNUM0a & BNUMa & BDENa & SHDa & LIVE3a & BXO & BQO & BQDYN & AFRqx & CRLE & AHPo).
  destruct UNE as (RQ & MQ & UQ1 & UQ8 & UQ9 & UQk & GQ3 & GQ4 & DQE & Uc8 & Uc16 & Uc24 & MWu & AHPu).
  destruct DQE as (RN & MN & UN1 & UN8 & UN9 & UN18 & UN19 & UN20 & UN21 & UN22 & UN23 & UN24 & UN25 & UN26 & UN27 & GN3 & GN4 & DNE & OPFb & ZOb & SHOPb & LIVEb & AHPq).
  destruct DNE as (RZ & MZ & B0 & B1 & fd0N & fn0N & fnN & fdenN & w1 & UZ1 & UZ8 & UZ9 & UZ18 & UZ19 & UZ20 & UZ21 & UZ22 & UZ23 & UZ24 & UZ25 & UZ26 & GZ27 & GZ3 & GZ4 & RH & DSAVb
                   & Nb336 & Nb296 & Nb280 & Nb272 & Nb264 & Nb256 & Nb248 & Nb240 & Nb224 & Nb216 & Nb208 & Nb200 & Nb192 & Nb172
                   & BDEN0b & BNUM0b & BNUMb & SGNb & BDENb & SGDb & SHDb & LIVE3b & ELBp & ECRp & AHPn).
  destruct RH as (H2 & H3 & H4 & H10 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & RSAVz & Zc104
                  & Za136 & Za144 & Za152 & Za160 & Za168 & Za176 & Za184 & Za192 & Za200 & Za208 & Za216 & Za224 & Za232 & SHRZc & SHRZd & LIVEd & LIVEc & AHPz).
  destruct DSAVa as (Sa8 & Sa16 & Sa24 & Sa32 & Sa40 & Sa48 & Sa56 & Sa64 & Sa72 & Sa80 & Sa88 & Sa96 & Sa104).
  destruct DSAVb as (Sb8 & Sb16 & Sb24 & Sb32 & Sb40 & Sb48 & Sb56 & Sb64 & Sb72 & Sb80 & Sb88 & Sb96 & Sb104).
  destruct RSAVz as (Sz8 & Sz16 & Sz24 & Sz32 & Sz40 & Sz48 & Sz56 & Sz64 & Sz72 & Sz80 & Sz88 & Sz96).
  destruct OPFb as (Sq8 & Sq16 & Sq24 & Sq32 & Sq40 & Sq48 & Sq56 & Sq64 & Sq72 & Sq80 & Sq88).
  pose proof (UQk 18 ltac:(clear; lia)) as UQ18. pose proof (UQk 19 ltac:(clear; lia)) as UQ19. pose proof (UQk 20 ltac:(clear; lia)) as UQ20.
  pose proof (UQk 21 ltac:(clear; lia)) as UQ21. pose proof (UQk 22 ltac:(clear; lia)) as UQ22. pose proof (UQk 23 ltac:(clear; lia)) as UQ23.
  pose proof (UQk 24 ltac:(clear; lia)) as UQ24. pose proof (UQk 25 ltac:(clear; lia)) as UQ25. pose proof (UQk 26 ltac:(clear; lia)) as UQ26.
  pose proof (UQk 27 ltac:(clear; lia)) as UQ27. clear UQk.
  subst LBt LBm.
  (* [comment removed for export] *)
  set (LBT := [(B0, 64); (B1, 64); (d3, 64); (d4, 64)]). set (LB1 := (qx, 64) :: LB).
  set (FR := [(F, fl); (F3a, fl3a); (F1b, fl1b); (F3b, fl3b); (F1c, fl1c); (F1d, fl1d)]).
  unfold S in U1_22.
  Local Ltac veq := first [ reflexivity | assumption | ring | (match goal with |- ?l = _ => match goal with H : l = _ |- _ => rewrite H end end; veq) ].
  Local Ltac cl H := refine (u64_eq _ _ _ _ _ H _ _); [ ring | veq ].
  Local Ltac bg H := refine (big_eq _ _ _ _ H _); ring.
  assert (LIVEa' : L5DSA.fr_live L ar (LBT ++ LB1) FF Mt 1 F fl (E - 64)).
  { destruct LIVEa as [c f n a h]. constructor; try assumption.
    assert (HHp0 : forall b, In b ([(B0, 64); (B1, 64); (d3, 64); (d4, 64); (qx, 64)]) -> ablock_range L ar (fst b) (snd b) /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + FS_BYTES <= fst b)).
    { intros b Hb. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHt) as (WB & _). destruct (WB b) as (BR & _ & _ & _ & _ & _ & BFS). 2: split; [exact BR | exact BFS].
      cbn [In] in Hb |- *. clear - Hb. destruct Hb as [<-|[<-|[<-|[<-|[<-|[]]]]]]; auto 8. }
    change (LBT ++ LB1) with ([(B0, 64); (B1, 64); (d3, 64); (d4, 64); (qx, 64)] ++ LB).
    apply (not_client_bx L ar ((F, 1, E - 64) :: FF) fl _ LB HHp0 f). 2: exact n.
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & FSAPP & _). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. clear - f FSAPP. unfold FS_BYTES in *. Lia.lia. }
  assert (FLAT : L5DIA.assert_throw_atA L ar LBT LB1 FF R M Rt Mt E xo FR).
  { exists F, fl, F3a, fl3a, F1b, fl1b, F3b, fl3b, F1c, fl1c, F1d, fl1d, B0, B1, d3, d4, qx, bo, LB, lenX, (L5DSA.U RN 25), (L5DSA.U RN 26), (L5DSA.U RQ 9), fbx',
           fd0N, fn0N, fnN, fdenN, w1, fd0, fn0, fn, fden, v0, v1, v2, v3, nd0, nn0, nn, nd, bq.
    split. reflexivity. split. reflexivity. split. reflexivity.
    split. { unfold L5DSA.assert_throw_regs.
      split. rewrite H2. f_equal. ring. split. rewrite H3, GZ3, GN3, GQ3, GU3, G1_3. reflexivity. split. rewrite H4, GZ4, GN4, GQ4, GU4, G1_4. reflexivity.
      split. exact H10. split. rewrite H8. f_equal. ring. split. rewrite H9. f_equal. ring.
      split. exact H18. split. exact H19. split. exact H20. split. exact H21. split. exact H22. split. exact H23. split. exact H24. split. exact H25. split. exact H26.
      rewrite H27. exact GZ27. }
    split. cl Za136.
    split. cl Za144.
    split. cl Za152.
    split. cl Za160.
    split. cl Za168.
    split. cl Za176.
    split. cl Za184.
    split. cl Za192.
    split. cl Za200.
    split. cl Za208.
    split. cl Za216.
    split. cl Za224.
    split. cl Za232.
    split. cl Sz8.
    split. cl Sz16.
    split. cl Sz24.
    split. cl Sz32.
    split. cl Sz40.
    split. cl Sz48.
    split. cl Sz56.
    split. cl Sz64.
    split. cl Sz72.
    split. cl Sz80.
    split. cl Sz88.
    split. cl Sz96.
    split. cl Zc104.
    split. cl Sb8.
    split. cl Sb16.
    split. cl Sb24.
    split. cl Sb32.
    split. cl Sb40.
    split. cl Sb48.
    split. cl Sb56.
    split. cl Sb64.
    split. cl Sb72.
    split. cl Sb80.
    split. cl Sb88.
    split. cl Sb96.
    split. cl Sb104.
    split. cl Nb336.
    split. cl Nb296.
    split. cl Nb280.
    split. cl Nb272.
    split. cl Nb264.
    split. cl Nb256.
    split. cl Nb248.
    split. cl Nb240.
    split. cl Nb224.
    split. cl Nb216.
    split. cl Nb208.
    split. cl Nb200.
    split. cl Nb192.
    split. refine (u32_eq _ _ _ _ Nb172 _); ring.
    split. bg BDEN0b. split. bg BNUM0b. split. bg BNUMb. split. exact SGNb. split. bg BDENb. split. exact SGDb.
    split. cl Sq8.
    split. cl Sq16.
    split. cl Sq24.
    split. cl Sq32.
    split. cl Sq40.
    split. cl Sq48.
    split. cl Sq56.
    split. cl Sq64.
    split. cl Sq72.
    split. cl Sq80.
    split. cl Sq88.
    split. exact ZOb.
    split. cl Uc8.
    split. cl Uc16.
    split. cl Uc24.
    split. { destruct MWu as (MW1 & MW2). split. bg MW1. exact MW2. }
    split. { unfold L5DSA.divO_saves.
      split. cl Sa8.
      split. cl Sa16.
      split. cl Sa24.
      split. cl Sa32.
      split. cl Sa40.
      split. cl Sa48.
      split. cl Sa56.
      split. cl Sa64.
      split. cl Sa72.
      split. cl Sa80.
      split. cl Sa88.
      split. cl Sa96.
      cl Sa104. }
    split. cl Oa336.
    split. cl Oa296.
    split. cl Oa280.
    split. cl Oa272.
    split. cl Oa264.
    split. cl Oa256.
    split. cl Oa248.
    split. cl Oa240.
    split. cl Oa208.
    split. cl Oa200.
    split. cl Oa192.
    split. bg BDEN0a. split. bg BNUM0a. split. bg BNUMa. split. bg BDENa.
    split. exact QOWN. split. exact BQO. split. exact BQDYN. split. exact BXO.
    split. exact SHRZd. split. exact SHRZc. split. exact SHDb. split. exact SHOPb. split. exact SHDa. split. exact SHOPa.
    split. { refine (fr_live_re _ _ _ _ _ _ _ _ _ _ LIVEd (fun b => proj2 (in5 _ _ _ _ _ _ b)) _ _). repeat (f_equal; try ring). ring. }
    split. { refine (fr_live_re _ _ _ _ _ _ _ _ _ _ LIVEc (fun b => proj2 (in5 _ _ _ _ _ _ b)) _ _). repeat (f_equal; try ring). ring. }
    split. { refine (fr_live_re _ _ _ _ _ _ _ _ _ _ LIVE3b (fun b => proj2 (in5 _ _ _ _ _ _ b)) _ _). repeat (f_equal; try ring). ring. }
    split. { refine (fr_live_re _ _ _ _ _ _ _ _ _ _ LIVEb (fun b => proj2 (in5 _ _ _ _ _ _ b)) _ _). repeat (f_equal; try ring). ring. }
    split. { refine (fr_live_re _ _ _ _ _ _ _ _ _ _ LIVE3a (fun b => proj2 (in5 _ _ _ _ _ _ b)) _ _). repeat (f_equal; try ring). ring. }
    exact LIVEa'. }
  (* [comment removed for export] *)
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF0.
  assert (TOP : ar_stack_top ar <= 2 ^ 47). { clear - WF0. decompose [and] WF0. assumption. }
  assert (AGC : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF E L5AOPMOD.SCRo a -> ~ (xo <= a < xo + 32) -> Mt (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc Hn. apply (proj1 AHPa). split. exact Ha. split. exact Hc. intros rr [<-|[]] IR. apply Hn. exact IR. }
  assert (XSPt : L5USA.xs_pre ar st Mt).
  { eapply L5ATX.xs_pre_same; try first [exact LY | exact HIok | exact UNWL]. 2: exact XSP. intros a Hd.
    assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hd as [(X0 & _)|X0]; clear - X0 SPT; Lia.lia). apply AGC. exact Ha.
    destruct Hd as [(X0 & NS)|X0]. right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. exact X0. exact NS.
    right; left. split. clear - X0 SLO SHI; Lia.lia. clear - X0 SHI; Lia.lia.
    destruct Hd as [(X0 & _)|X0]. clear - X0 OR; Lia.lia. clear - X0 OR SLO SHI; Lia.lia. }
  assert (STKt : astk ar Mt E L5AOPMOD.SCRo).
  { apply (astk_after2 L ar C HI HIok _ _ _ _ _ _ _ LB FF M M Mt E L5AOPMOD.SCRo E L5AOPMOD.SCRo [(xo, 32)] HH STK (mem_grows_refl M) AHPa). clear; Lia.lia. clear; Lia.lia. vm_compute; discriminate. }
  assert (FCE : 4096 <= ahl_ceil ar). { clear - OR. Lia.lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHX : forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> ~ (xo <= a < xo + 32)).
  { intros a Hs. unfold in_shadow_of, S, SB in Hs. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) in Hs by (clear; Lia.lia). change ((2 ^ 47 - 1) / 8) with 17592186044415 in Hs.
    clear - Hs OBIG FCE. Lia.lia. }
  assert (SSHt : L5OMA.stksh ar Mt (E - L5AOPMOD.SCRo)).
  { eapply (L5AOPMOD.stksh_sub). exact SSH. clear; Lia.lia. 3: unfold L5AOPMOD.SCRo; clear - SLO; Lia.lia. 3: unfold L5AOPMOD.SCRo; clear - SLO FCE; Lia.lia. 3: exact TOP. 3: clear - SPT; Lia.lia.
    1,2: (unfold L5AOPMOD.SCRo; clear - A32; Lia.lia).
    intros a Ha Hs. apply AGC. exact Ha. right; right; right; right; left. exact Hs. apply SHX. exact Hs. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHt) as WFt.
  assert (NDt : NoDup (map fst ((B0, 64) :: (B1, 64) :: (qx, 64) :: (d3, 64) :: (d4, 64) :: LB))). { clear - WFt. decompose [and] WFt. assumption. }
  rewrite L5DIA.ff_o_e3 in HHt, WFt.
  assert (NDFt : NoDup (map ff_addr (L5DSA.ff_e3 FF E F F3a F1b F3b F1c F1d))).
  { assert (X : NoDup (map ff_addr (L5DSA.ff_e3 FF E F F3a F1b F3b F1c F1d ++ LKt))) by (clear - WFt; decompose [and] WFt; assumption).
    rewrite map_app in X. apply list_relations.list.NoDup_app in X. exact (proj1 X). }
  assert (HHp : ri_inv HI (LBT ++ LB1) (L5DSA.ff_e3 FF E F F3a F1b F3b F1c F1d) LKt crt At Mt (vml_of modelt)).
  { apply (aio_perm _ _ _ _ _ HIok _ _ _ _ _ _ _ _ _ HHt). intros b. apply in5. apply nodup5. exact NDt. intros f. reflexivity. exact NDFt. }
  assert (CAPB : 0 <= L5.bo_cap bb). { unfold L5.bo_cap. destruct BOK as (OBB & _). destruct OBB as (_ & _ & _ & ST). destruct (L5.bo_st bb). clear; Lia.lia. destruct ST as (_ & _ & _ & _ & CR0 & _). clear - CR0; Lia.lia. }
  assert (CRFt : L5OMA.acredit_for L crt 3 (L5USA.EXC23_SZ + L5USA.MSG3_SZ + L5USA.REF3_SZ)).
  { destruct (L5OMA.acredit_for_split L cr L5DIA.DIVO1_K (L5DIA.divO1_bytes (L5.bo_cap bb)) 5 320 LY2 CRF) as (_ & X). vm_compute; split; discriminate.
    unfold L5DIA.divO1_bytes. clear - CAPB; Lia.lia.
    apply (L5OMA.acredit_for_mono L _ crt) in X. 2: exact CRLE.
    apply (L5OMA.acredit_for_le L crt _ _ 3 (L5USA.EXC23_SZ + L5USA.MSG3_SZ + L5USA.REF3_SZ) LY2 X). vm_compute; discriminate.
    unfold L5DIA.divO1_bytes, L5USA.EXC23_SZ, L5USA.MSG3_SZ, L5USA.REF3_SZ. clear - CAPB. Lia.lia. }
  apply (He3 fx' R M Rt Mt modelt K LBT LB1 FF LK LKt crt At E L5AOPMOD.SCRo xo FR st FLAT eq_refl).
  - rewrite G1, RE. reflexivity.
  - exact G2.
  - exact G3.
  - exact G4.
  - exact G9.
  - exact A32.
  - exact XSPt.
  - exact HHp.
  - exact AMt.
  - exact HK.
  - exact ILKt.
  - exact STKt.
  - vm_compute; discriminate.
  - reflexivity.
  - exact SSHt.
  - exact CRFt.
  - (* [comment removed for export] *)
    intros fxl Rl Ml modell LBl crl LKl Al RPl LND AHPl RTl IAl AMl HHl.
    destruct AHPa as (EKa & DFa & DKa). destruct AHPl as (EKl & DFl & DKl). unfold LB1 in EKl, DKl.
    assert (AHL : ahpres L ar LB FF E L5AOPMOD.SCRo ((xo, 32) :: L5USA.xs_foot) M Ml).
    { split. { eapply ek_trans. eapply ek_W. exact EKa. intros a O rr [<-|[]]. apply O. left; reflexivity.
               eapply ek_W. apply (ek_tl L ar LB (qx, 64) FF E L5AOPMOD.SCRo _ Mt Ml EKl). intros a O rr Hr. apply O. right. exact Hr. }
      split. exact DFl. eapply dk_trans. exact DKa. apply (dk_tl L ar LB (qx, 64) FF E L5AOPMOD.SCRo Mt Ml DKl). }
    assert (FOOT : forall a, 0x633000 <= a \/ a < 0x10000 -> L5.outside L5USA.xs_foot a).
    { intros a Ha rr [<-|[<-|[]]] IR; unfold L5.in_rng, L5USA.EH_UNCAUGHT, L5USA.UW_FLAGS in IR; cbn [fst snd] in IR; clear - Ha IR; Lia.lia. }
    assert (OBXl : L5.big_at RSEGS Ml xo (L5.BO fbx' lenX (L5.BDyn 8 qx))).
    { eapply L5C.big_at_agree. 4: exact BXO. 2: clear - OR; Lia.lia. 2: clear - OR; Lia.lia. intros j Hj. apply EKl. split. clear - Hj OR; Lia.lia.
      split. apply (obj_client L ar _ FF _ _ xo 32 j AOX Hj). apply FOOT. left. clear - Hj OR; Lia.lia. }
    pose proof LND as ((obj & ref & _ & _ & _ & ELBl & _) & _). unfold LB1 in ELBl. subst LBl.
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHl) as WFl.
    assert (NDl : NoDup (map fst ((ref, L5USA.REF3_SZ) :: (obj - 128, L5USA.EXC23_SZ) :: (qx, 64) :: LB))). { clear - WFl. decompose [and] WFl. assumption. }
    assert (NDFl : NoDup (map ff_addr FF)).
    { assert (X : NoDup (map ff_addr (FF ++ LKl))) by (clear - WFl; decompose [and] WFl; assumption).
      rewrite map_app in X. apply list_relations.list.NoDup_app in X. exact (proj1 X). }
    assert (HHq : ri_inv HI ((qx, 64) :: (ref, L5USA.REF3_SZ) :: (obj - 128, L5USA.EXC23_SZ) :: LB) FF LKl crl Al Ml (vml_of modell)).
    { apply (aio_perm _ _ _ _ _ HIok _ _ _ _ _ _ _ _ _ HHl). intros b. apply in3. apply nodup3. exact NDl. intros f. reflexivity. exact NDFl. }
    pose proof (L5ADH.afresh_of_inv L ar C HI HIok qx 64 _ FF LKl crl Al Ml _ HHq) as (AF1 & AF2 & AF3 & AF4 & AF5).
    assert (AFRl : afresh L ar LB (FF ++ LKl) Ml qx 64).
    { split. exact AF1. split. intros b Hb. apply AF2. right; right; exact Hb. split. exact AF3. split. exact AF4. exact AF5. }
    assert (CRAl : L5OMA.acredit_after L cr L5DIA.DIVO1_K (L5DIA.divO1_bytes (L5.bo_cap bb)) crt).
    { pose proof (L5OMA.adebits_le L cr L5DIA.DIVO1_K (L5DIA.divO1_bytes (L5.bo_cap bb)) 5 320 LY2 ltac:(vm_compute; discriminate) ltac:(unfold L5DIA.divO1_bytes; clear - CAPB; Lia.lia)) as X.
      unfold L5OMA.acredit_after, credit_le in *. clear - X CRLE. Lia.lia. }
    (* [comment removed for export] *)
    pose proof BOK as (OBB & OLB & REDB & INB).
    assert (TBo : L5ADVEA.tob LB M bo bb wb). { split. exact OBB. split. exact OLB. split. exact SZB. intros cap q Eq. rewrite Eq in INB. exact INB. }
    assert (NWB : forall a, L5ADVEA.oreg bo bb a -> L5.outside ((xo, 32) :: L5USA.xs_foot) a).
    { intros a ORa rr [<-|Hr].
      - unfold L5.in_rng; cbn [fst snd]. destruct ORa as [ORa|[ORa|(cap & q & Eq & ORa)]].
        + clear - ORa APXB; Lia.lia.
        + unfold SB in ORa. clear - ORa DR OBIG. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
        + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
          destruct WF0 as (WB & WF & _). rewrite Eq in INB. destruct (WB _ INB) as (_ & _ & _ & _ & _ & _ & BFS). cbn [fst snd] in BFS.
          destruct AOX as (f & Hf & O1 & O2 & _). destruct (WF f Hf) as (Y1 & Y2 & _ & Y4 & _).
          assert (HB : 0 < ff_bytes (ff_class f)). { clear - Y4. destruct Y4 as [E0|[E0|[E0|[]]]]; rewrite <- E0; vm_compute; reflexivity. }
          clear - ORa BFS O1 O2 Y1 Y2 HB. Lia.lia.
      - revert rr Hr. apply FOOT.
        destruct ORa as [ORa|[ORa|(cap & q & Eq & ORa)]]. left; clear - ORa DR; Lia.lia. left. unfold SB in ORa. clear - ORa DR. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
        destruct WF0 as (WB & _). rewrite Eq in INB. destruct (WB _ INB) as ((Q0 & QIMG & _) & _). cbn [fst snd] in Q0, QIMG. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in QIMG. clear - ORa QIMG Q0. Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct (L5ADVO1.arg_kept L ar C HI LY HIok M Ml model LB FF LK cr A E L5AOPMOD.SCRo _ bo _ _ HH AHL AOB TBo NWB) as (OBBl & OLBl).
    apply (KE3 fxl Rl Ml modell _ crl LKl Al fbx' lenX qx crt RPl OBXl AFRl CRAl LND OBBl OLBl AHL).
    + eapply L5LZ.model_rt_trans. exact RTt. exact RTl.
    + intros x Hx. apply IAl. apply IAt. exact Hx.
    + exact AMl.
    + exact HHl.
Qed.

(* [comment removed for export] *)
Theorem opmod1A_ok' : opdel_sized_spec L ar HI -> L5DIA.divO1_specA L ar HI -> L5USA.e2_chainA_spec L ar HI -> L5USA.e3_chainA_spec_of L ar HI (L5DIA.assert_throw_atA L ar) ->
  L5USA.as0_unw_layout L ->
  L5OMA.opmod1A_spec L ar HI L5USA.XS (L5USA.xs_pre ar) L5USA.xs_foot (L5USA.e2_landed L) (L5USA.e3_landed L) L5AOPMOD.SCRo 6 0 4 L5DIA.DIVO1_K L5DIA.divO1_bytes.
Proof.
  intros Hdel HdivO1 He2 He3 UNWL. apply (L5AOPMOD.opmod1A_ok L ar C HI LY HIok Hdel HdivO1 He2 (om1_e3_arm_ok He3 UNWL) UNWL).
Qed.
End WithIface.
End SCFG_1.
End L5AOME3.
