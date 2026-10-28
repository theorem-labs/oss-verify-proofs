(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HCommon.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BsCXXHeap RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Call LbB_Conv LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwStm.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Bridge LbB_SR LbB_TablStmt LbB_HdrGet LbB_PmHTK LbB_PmHTS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHT1 LbB_PmHT2 LbB_PmHT3_5 LbB_PmHT3_6.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition HT_W (sf sp h : Z) : list (Z * Z) := HT_WIN sf ++ (sp - HG_STACK, sp) :: [(h, h + 32)].
Definition HT_KEEP : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition ht_hg0 (b code n e h : Z) (ws : list Z) (m : mem) (sp sf : Z) : Prop :=
  fld ASEGS m b 8 code /\ fld ASEGS m (b + 8) 8 n /\ b mod 8 = 0 /\ addressable m b 16
  /\ AIMG_TOP <= b /\ b + 16 <= 2 ^ 47 /\ (b + 16 <= sp - HG_STACK \/ sp <= b)
  /\ (e = 0 \/ e = 1)
  /\ h mod 8 = 0 /\ sh h = sf + 278 /\ wr_at asegs m h 32 /\ aconst_ok (h, h + 32)
  /\ (h + 32 <= sp - TL_STACK \/ sp <= h)
  /\ ((0x6e8000 <= h /\ h + 32 <= 0x7fff7000) \/ (0x10007fff8000 <= h /\ h + 32 <= 2 ^ 47))
  /\ (h + 32 <= b \/ b + 16 <= h)
  /\ AIMG_TOP <= code /\ code mod 4 = 0 /\ code + 20 <= 2 ^ 47 /\ (code + 20 <= sp - HG_STACK \/ sp <= code)
  /\ 5 <= n /\ Zlen ws = 5 /\ (forall i, 0 <= i < 5 -> fld ASEGS m (code + 4 * i) 4 (Znth i ws)) /\ addressable m code (4 * n)
  /\ disjoint_from (HT_WIN sf) b 16 /\ disjoint_from (HT_WIN sf) code 20
  /\ disjoint_from (HT_WIN sf) (sh b) (nsh 16) /\ disjoint_from (HT_WIN sf) (sh code) (nsh (4 * n))
  /\ h + 32 <= AAPP_HI
  /\ (h + 32 <= code \/ code + 20 <= h).

Lemma ht_mrd0 : forall m a, fldA m a 1 0 -> mrd asegs m (wa a) = Some (b8 0).
Proof.
  intros m a F. unfold fldA, fld in F. unfold mrd, wa.
  assert (WB : word_to_le_bytes 1 (Z_to_bv 64 0) = [b8 0]) by (vm_compute; reflexivity).
  rewrite WB in F. simpl in F.
  destruct (m (Z_to_bv 64 a)) as [x|].
  - injection F as F. subst x. reflexivity.
  - change (seg_rom asegs (Z_to_bv 64 a)) with (PropExec.seg_rom ASEGS (Z_to_bv 64 a)).
    destruct (PropExec.seg_rom ASEGS (Z_to_bv 64 a)) as [x|]; [injection F as F; subst x; reflexivity | discriminate F].
Qed.

Lemma ht_fld_munch : forall W m m' a k v, fld ASEGS m a k v -> munch W m m' -> disjoint_from W a (Z.of_nat k) ->
  0 <= a -> a + Z.of_nat k < 2 ^ 64 -> fld ASEGS m' a k v.
Proof.
  intros W m m' a k v F MU D H0 H1. eapply fld_agree; [exact H0 | exact H1 | exact F |].
  intros x Hx. unfold LibIface.zwin in Hx. apply MU. rewrite unsigned_lit by lia. eapply disjoint_outside; [exact D | lia].
Qed.

Lemma ht_disj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn; [auto|]. intros a n a' n' [D1 D2] L1 L2 L3. split; [lia | eapply IH; eauto].
Qed.

Lemma ht_disj_app : forall W1 W2 a n, disjoint_from (W1 ++ W2) a n -> disjoint_from W1 a n /\ disjoint_from W2 a n.
Proof.
  induction W1 as [|[lo hi] W1 IH]; cbn; intros W2 a n D; [split; [exact I | exact D]|].
  destruct D as [D1 D2]. destruct (IH W2 a n D2) as [E1 E2]. split; [split; [exact D1 | exact E1] | exact E2].
Qed.

Lemma ht_outside_app : forall W1 W2 x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; cbn; intros W2 x O; [split; [exact I | exact O]|].
  destruct O as [O1 O2]. destruct (IH W2 x O2) as [E1 E2]. split; [split; [exact O1 | exact E1] | exact E2].
Qed.

Lemma ht_munch_app : forall W1 W2 m m1 m2, munch W1 m m1 -> munch W2 m1 m2 -> munch (W1 ++ W2) m m2.
Proof.
  intros W1 W2 m m1 m2 M1 M2 x Hx. destruct (ht_outside_app W1 W2 _ Hx) as [O1 O2]. rewrite (M2 x O2). exact (M1 x O1).
Qed.

Lemma ht_wmono_trans : forall m m1 m2, wmono asegs m m1 -> wmono asegs m1 m2 -> wmono asegs m m2.
Proof. intros m m1 m2 W1 W2 x Hx. exact (W2 x (W1 x Hx)). Qed.

Lemma ht_hg_pre : forall b code n e h ws m M1 sp sf a3,
  ht_hg0 b code n e h ws m sp sf -> wr_at asegs m (sf + 278) 4 ->
  munch (HT_WIN sf) m M1 -> wmono asegs m M1 ->
  fldA M1 (sf + 278) 1 0 -> fldA M1 (sf + 279) 1 0 -> fldA M1 (sf + 280) 1 0 -> fldA M1 (sf + 281) 1 0 ->
  hg_pre (b, code, n, e, h, ws) M1 sp (wz b) (wz e) (wz h) a3.
Proof.
  intros b code n e h ws m M1 sp sf a3 G WR MU WM Z0 Z1 Z2 Z3.
  destruct G as (Fb & Fn & B8 & AB & B1 & B2 & B3 & HE & H8 & SHH & WH & ACH & H3 & H4 & HB & C1 & C2 & C3 & C4 & N5 & LW & FW
                 & AC & D1 & D2 & D3 & D4 & HAP & HCD).
  assert (AI : 0 <= AIMG_TOP) by (unfold AIMG_TOP; lia).
  pose proof WR as (WR0 & WR1 & _).
  assert (AH : addressable M1 h 32).
  { split; [lia|]. change (shadow_of 32) with [b8 0; b8 0; b8 0; b8 0].
    split; [lia|]. split; [exact H8|]. split.
    - split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. rewrite SHH.
      destruct i as [|[|[|[|i]]]]; cbn [nth_error].
      + replace (sf + 278 + Z.of_nat 0) with (sf + 278) by lia. exact (ht_mrd0 _ _ Z0).
      + replace (sf + 278 + Z.of_nat 1) with (sf + 279) by lia. exact (ht_mrd0 _ _ Z1).
      + replace (sf + 278 + Z.of_nat 2) with (sf + 280) by lia. exact (ht_mrd0 _ _ Z2).
      + replace (sf + 278 + Z.of_nat 3) with (sf + 281) by lia. exact (ht_mrd0 _ _ Z3).
      + cbn [length] in Hi. lia.
    - cbn [length]. change (Z.of_nat 4) with 4. rewrite SHH. exact (wr_at_transport asegs m M1 _ 4 WR WM). }
  cbv beta iota delta [hg_pre].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact (ht_fld_munch _ m M1 b 8 code Fb MU (ht_disj_sub _ b 16 b (Z.of_nat 8) D1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))|].
  split; [exact (ht_fld_munch _ m M1 (b + 8) 8 n Fn MU (ht_disj_sub _ b 16 (b + 8) (Z.of_nat 8) D1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))|].
  split; [exact B8|].
  split; [exact (addressable_transport _ m M1 b 16 AB MU WM D3)|].
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact HE|]. split; [exact H8|].
  split.
  { split; [exact (wr_at_transport asegs m M1 h 32 WH WM)|].
    split; [exact (addressable_accessible M1 h 32 h 32 AH ltac:(lia) ltac:(lia) HAP)|].
    split; [exact ACH|]. split; [exact H3 | exact H4]. }
  split; [exact AH|]. split; [exact HB|].
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact N5|]. split; [exact LW|].
  split.
  { intros i Hi. apply (ht_fld_munch _ m M1 _ 4 _ (FW i Hi) MU); [| lia | lia].
    apply (ht_disj_sub _ code 20); [exact D2 | lia | lia | lia]. }
  split; [exact (addressable_transport _ m M1 code (4 * n) AC MU WM D4) | exact HCD].
Qed.

Ltac htin := solve [cbn [In HT_SAVED HT_KEEP]; repeat (first [left; reflexivity | right])].

Section HTail.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma pm_htail : hdr_get_stmt ->
    forall (s : as_St H) (msF : machine_state) (mo : Model) (R F : bvmap 5 word) (fc : bv 32) (m : mem)
      (p sf fb b e h code n lo : Z) (ws : list Z) (Q : config -> Prop),
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 HT_START) fc None m (seg_rom asegs) -> rfull R ->
    mem_inv asegs m -> ACONST m -> ht_a_pre R m p sf fb b e h ->
    ht_hg0 b code n e h ws m (bv_unsigned (getr R 2)) sf ->
    stk asegs m lo (bv_unsigned (getr R 2)) -> aceil <= lo -> lo <= bv_unsigned (getr R 2) - HG_STACK ->
    bv_unsigned (getr R 2) mod 16 = 0 -> bv_unsigned (getr R 2) <= 2 ^ 47 ->
    Forall aconst_ok (HT_WIN sf) -> disjoint_from (HT_WIN sf) lo (bv_unsigned (getr R 2) - lo) ->
    disjoint_from ((bv_unsigned (getr R 2) - HG_STACK, bv_unsigned (getr R 2)) :: [(h, h + 32)]) (sf + 278) 4 ->
    fldA m (p + 24) 8 0 -> disjoint_from (HT_W sf (bv_unsigned (getr R 2)) h) (p + 24) 8 ->
    (forall msF1 mo1 R1 m1, as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 HT_LOOP) fc None m1 (seg_rom asegs) -> rfull R1 ->
       getr R1 1 = wz HT_RET -> getr R1 10 = wz 0 -> getr R1 17 = wz 0 ->
       (forall r, In r HT_KEEP -> getr R1 r = getr R r) ->
       munch (HT_W sf (bv_unsigned (getr R 2)) h) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       stk asegs m1 lo (bv_unsigned (getr R 2)) -> ACONST m1 ->
       fldA m1 (sf + 278) 1 0 -> fldA m1 (sf + 279) 1 0 -> fldA m1 (sf + 280) 1 0 -> fldA m1 (sf + 281) 1 0 ->
       hg_post (b, code, n, e, h, ws) m (wz 0) (getr R1 11) m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    (forall msF1 mo1 R1 m1, as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 HT_D4) fc None m1 (seg_rom asegs) -> rfull R1 ->
       getr R1 1 = wz HT_RET -> getr R1 10 = wz (-4) ->
       (forall r, In r HT_KEEP -> getr R1 r = getr R r) ->
       munch (HT_W sf (bv_unsigned (getr R 2)) h) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       stk asegs m1 lo (bv_unsigned (getr R 2)) -> ACONST m1 ->
       fldA m1 (sf + 278) 1 0 -> fldA m1 (sf + 279) 1 0 -> fldA m1 (sf + 280) 1 0 -> fldA m1 (sf + 281) 1 0 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros HG s msF mo R F fc m p sf fb b e h code n lo ws Q KR VIS RF MI AC PA G0 ST L1 L2 SA SH ACW DSTK DSH F24 D24 K0 KN.
    pose proof PA as PA'. unfold ht_a_pre in PA'.
    destruct PA' as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17).
    eapply (pm_ht1 H HH s msF mo R F fc m p sf fb b e h Q KR VIS RF MI PA).
    intros msF1 mo1 R1 M1 KR1 MP1 VIS1 RF1 MI1 MU1 WM1 Z0 Z1 Z2 Z3 G1 G9 G10 G11 G12 G18 G19 G25 KP1.
    assert (SP1 : getr R1 2 = getr R 2) by (apply KP1; htin).
    assert (AC1 : ACONST M1) by exact (ACONST_frame _ m M1 AC MU1 WM1 ACW).
    assert (ST1 : stk asegs M1 lo (bv_unsigned (getr R 2))).
    { eapply (stk_transport_disjoint asegs (HT_WIN sf) m M1); [exact ST | exact MU1 | exact WM1 | exact DSTK]. }
    eapply (pm_ht2 H HH HG (b, code, n, e, h, ws) s msF1 mo1 R1 F fc M1 lo Q KR1 VIS1 RF1 G1);
      rewrite ?SP1; [exact ST1 | exact L1 | exact L2 | exact SA | exact SH | exact MI1 | exact AC1 | |].
    { rewrite G10, G11, G12. exact (ht_hg_pre b code n e h ws m M1 _ sf _ G0 P8 MU1 WM1 Z0 Z1 Z2 Z3). }
    intros msF2 mo2 R2 m2 KR2 MP2 VIS2 RF2 KP2 MU2 WM2 MI2 ST2 AC2 HP.
    cbn [hg_win] in MU2.
    pose proof (ht_disj_app (HT_WIN sf) _ _ _ D24) as [D24a D24b].
    assert (MU : munch (HT_W sf (bv_unsigned (getr R 2)) h) m m2) by exact (ht_munch_app _ _ m M1 m2 MU1 MU2).
    assert (WM : wmono asegs m m2) by exact (ht_wmono_trans m M1 m2 WM1 WM2).
    assert (Y0 : fldA m2 (sf + 278) 1 0) by exact (ht_fld_munch _ M1 m2 _ 1 0 Z0 MU2 (ht_disj_sub _ (sf + 278) 4 (sf + 278) (Z.of_nat 1) DSH ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)).
    assert (Y1 : fldA m2 (sf + 279) 1 0) by exact (ht_fld_munch _ M1 m2 _ 1 0 Z1 MU2 (ht_disj_sub _ (sf + 278) 4 (sf + 279) (Z.of_nat 1) DSH ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)).
    assert (Y2 : fldA m2 (sf + 280) 1 0) by exact (ht_fld_munch _ M1 m2 _ 1 0 Z2 MU2 (ht_disj_sub _ (sf + 278) 4 (sf + 280) (Z.of_nat 1) DSH ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)).
    assert (Y3 : fldA m2 (sf + 281) 1 0) by exact (ht_fld_munch _ M1 m2 _ 1 0 Z3 MU2 (ht_disj_sub _ (sf + 278) 4 (sf + 281) (Z.of_nat 1) DSH ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)).
    assert (E18 : getr R2 18 = wz p) by (rewrite (KP2 18%bv ltac:(htin)); exact G18).
    assert (E1 : getr R2 1 = wz HT_RET) by (rewrite (KP2 1%bv ltac:(htin)); exact G1).
    assert (KP21 : forall r, In r HT_KEEP -> getr R2 r = getr R r).
    { intros r Hr.
      assert (IS : In r HT_SAVED) by (clear - Hr; unfold HT_KEEP in Hr; repeat (destruct Hr as [<- | Hr]; [htin |]); destruct Hr).
      rewrite (KP2 r IS). clear IS.
      unfold HT_KEEP in Hr. repeat (destruct Hr as [<- | Hr];
        [ first [ solve [apply KP1; htin] | rewrite G9; exact (eq_sym P0) | rewrite G18; exact (eq_sym P1)
                | rewrite G19; exact (eq_sym P2) | rewrite G25; exact (eq_sym P3) ] |]).
      destruct Hr. }
    pose proof HP as HP0. cbv beta iota delta [hg_post] in HP.
    destruct HP as [[R0 _] | R0].
    - eapply (pm_ht3_5 H HH s msF2 mo2 R2 F fc m2 p Q KR2 VIS2 RF2).
      { unfold ht_z_pre. split; [exact R0|]. split; [exact E18|]. split; [|split; lia].
        eapply (ht_fld_munch _ M1 m2 _ 8 0); [eapply (ht_fld_munch _ m M1 _ 8 0 F24 MU1); [exact D24a | lia | lia] | exact MU2 | exact D24b | lia | lia]. }
      intros msF3 mo3 R3 KR3 MP3 VIS3 RF3 H10 H17 H18 KP3.
      eapply (K0 msF3 mo3 R3 m2 KR3 (ah_mpres_trans H HH _ _ _ (ah_mpres_trans H HH _ _ _ MP1 MP2) MP3) VIS3 RF3); [rewrite (KP3 1%bv ltac:(htin)); exact E1 | exact H10 | exact H17 | | exact MU | exact WM
        | exact MI2 | exact ST2 | exact AC2 | exact Y0 | exact Y1 | exact Y2 | exact Y3 | ].
      + intros r Hr. rewrite <- (KP21 r Hr). unfold HT_KEEP in Hr.
        repeat (destruct Hr as [<- | Hr]; [ first [ solve [apply KP3; htin] | rewrite H18; exact (eq_sym E18) ] |]). destruct Hr.
      + rewrite (KP3 11%bv ltac:(htin)). rewrite R0 in HP0. exact HP0.
    - eapply (pm_ht3_6 H HH s msF2 mo2 R2 F fc m2 p Q KR2 VIS2 RF2).
      { unfold ht_n_pre. split; [rewrite R0; reflexivity|]. split; [exact E18|]. split; lia. }
      intros msF3 mo3 R3 KR3 MP3 VIS3 RF3 H10 H18 KP3.
      eapply (KN msF3 mo3 R3 m2 KR3 (ah_mpres_trans H HH _ _ _ (ah_mpres_trans H HH _ _ _ MP1 MP2) MP3) VIS3 RF3); [rewrite (KP3 1%bv ltac:(htin)); exact E1 | exact H10 | | exact MU | exact WM
        | exact MI2 | exact ST2 | exact AC2 | exact Y0 | exact Y1 | exact Y2 | exact Y3].
      intros r Hr. rewrite <- (KP21 r Hr). unfold HT_KEEP in Hr.
      repeat (destruct Hr as [<- | Hr]; [ first [ solve [apply KP3; htin] | rewrite H18; exact (eq_sym E18) ] |]). destruct Hr.
  Qed.
End HTail.
