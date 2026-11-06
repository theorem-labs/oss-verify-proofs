(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9L5DefsA PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AxSymExec3 AxSymExec3B AxSymExec3Sound.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmCurDefs PmCurSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutHeap2 CutL5 CutL5A CutHeapA CutBridgeA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import TopKitCB RdKitCb CurKitCB2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CTK.
Definition mem := (word -> option byte).

Section Agree.
Variable L : asan_layout.
Variable IC : PMLA.consts.
Variables (M M' : mem) (S : Z -> Prop).
Hypothesis AG : forall a, S a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Abbreviation segs := (hl_segs L).
Abbreviation out := (PTA.out S).

Lemma u64T : forall b n k v, out b n -> 0 <= k -> k + 8 <= n -> L5.u64_at segs M (b + k) v -> L5.u64_at segs M' (b + k) v.
Proof. intros b n k v O K0 K1 H. apply (PTA.u64_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ O); lia | exact H]. Qed.
Lemma u32T : forall b n k v, out b n -> 0 <= k -> k + 4 <= n -> L5.u32_at segs M (b + k) v -> L5.u32_at segs M' (b + k) v.
Proof. intros b n k v O K0 K1 H. apply (PTA.u32_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ O); lia | exact H]. Qed.
Lemma u8T : forall b n k v, out b n -> 0 <= k -> k + 1 <= n -> L5.u8_at segs M (b + k) v -> L5.u8_at segs M' (b + k) v.
Proof. intros b n k v O K0 K1 H. apply (PTA.u8_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ O); lia | exact H]. Qed.

Lemma src_atA_ag : forall Sx IS ch bof, out Sx 304 -> PMCSA.src_atA L IC M Sx IS ch bof -> PMCSA.src_atA L IC M' Sx IS ch bof.
Proof.
  intros Sx IS ch bof OS H. unfold PMCSA.src_atA, PMLA.u64, PMLA.u8, PMLA.u32 in *.
  destruct H as (Q240 & Q248 & Q264 & Q272 & (de & Q280 & DER) & Q288 & Q296 & (st0 & QIOSB) & Q32).
  split; [exact (u64T _ _ 240 _ OS ltac:(lia) ltac:(lia) Q240)|]. split; [exact (u64T _ _ 248 _ OS ltac:(lia) ltac:(lia) Q248)|].
  split; [exact (u64T _ _ 264 _ OS ltac:(lia) ltac:(lia) Q264)|]. split; [exact (u64T _ _ 272 _ OS ltac:(lia) ltac:(lia) Q272)|].
  split; [exists de; split; [exact (u64T _ _ 280 _ OS ltac:(lia) ltac:(lia) Q280) | exact DER]|].
  split; [exact (u64T _ _ 288 _ OS ltac:(lia) ltac:(lia) Q288)|]. split; [exact (u8T _ _ 296 _ OS ltac:(lia) ltac:(lia) Q296)|].
  split; [|exact (u64T _ _ 32 _ OS ltac:(lia) ltac:(lia) Q32)].
  destruct QIOSB as (K32 & K36 & K40 & K48 & KZ & KDEF). exists st0. unfold PMLA.iosb_at, PMLA.u64, PMLA.u32.
  split; [replace (Sx + 88 + 32) with (Sx + 120) in * by lia; exact (u32T _ _ 120 _ OS ltac:(lia) ltac:(lia) K32)|].
  split; [replace (Sx + 88 + 36) with (Sx + 124) in * by lia; exact (u32T _ _ 124 _ OS ltac:(lia) ltac:(lia) K36)|].
  split; [replace (Sx + 88 + 40) with (Sx + 128) in * by lia; exact (u64T _ _ 128 _ OS ltac:(lia) ltac:(lia) K40)|].
  split; [replace (Sx + 88 + 48) with (Sx + 136) in * by lia; exact (u64T _ _ 136 _ OS ltac:(lia) ltac:(lia) K48)|].
  split; [intros k Hk; replace (Sx + 88 + 56 + 8 * k) with (Sx + (144 + 8 * k)) by lia; apply (u64T _ _ (144 + 8 * k) _ OS); [lia | lia | replace (Sx + (144 + 8 * k)) with (Sx + 88 + 56 + 8 * k) by lia; exact (KZ k Hk)]|].
  apply (PTA.def_ag M M' S AG); [apply (PTA.out_sub _ _ _ _ _ OS); lia | exact KDEF].
Qed.

Lemma parser_at_ag : forall P ps, out P 272 -> out (PML.ps_bptr ps) (PML.ps_bcap ps) -> out (PML.ps_sb ps) (PML.ps_scap ps) ->
  PMLA.parser_at segs IC M P ps -> PMLA.parser_at segs IC M' P ps.
Proof.
  intros P ps OP OB OS H. destruct (RDKC.pax_of segs IC M P ps H) as [HX HW].
  pose proof H as H'. unfold PMLA.parser_at in H'. destruct H' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HD).
  assert (HX' : RDKC.pax segs IC M' P ps).
  { apply (RDKC.pax_ag segs IC M M' S AG P ps); [| exact OB | exact OS | | exact HX].
    - intros k n K0 K1 _. apply (PTA.out_sub _ _ _ _ _ OP); lia.
    - intros i Hi. destruct OP as (_ & _ & O3). rewrite (AG (P + i) (O3 (P + i) ltac:(lia))). exact (HD i ltac:(lia)). }
  assert (HW' : RDKC.win segs M' P (PML.ps_win ps)).
  { unfold RDKC.win in *. destruct (PML.ps_win ps) as [[p e]|].
    - destruct HW as (W1 & W2 & W3). unfold PMLA.u64 in *. split; [exact (u64T _ _ 200 _ OP ltac:(lia) ltac:(lia) W1)|]. split; [exact (u64T _ _ 192 _ OP ltac:(lia) ltac:(lia) W2) | exact W3].
    - destruct HW as (W1 & W2). unfold PMLA.u64 in *. split; [exact (u64T _ _ 192 _ OP ltac:(lia) ltac:(lia) W1) | exact (u64T _ _ 200 _ OP ltac:(lia) ltac:(lia) W2)]. }
  pose proof (RDKC.pax_to segs IC M' P ps (PML.ps_win ps) HX' HW') as R. rewrite RDKC.ps_set_win_id in R. exact R.
Qed.

Lemma cursor_atA_ag : forall C IS ch bof dn ps, out C 656 -> out (PML.ps_bptr ps) (PML.ps_bcap ps) -> out (PML.ps_sb ps) (PML.ps_scap ps) ->
  PMCSA.cursor_atA L IC M C IS ch bof dn ps -> PMCSA.cursor_atA L IC M' C IS ch bof dn ps.
Proof.
  intros C IS ch bof dn ps OC OB OS (H1 & H2 & H3 & H4 & H5). unfold PMCSA.cursor_atA.
  split; [apply src_atA_ag; [apply (PTA.out_sub _ _ _ _ _ OC); lia | exact H1]|].
  split; [apply parser_at_ag; [apply (PTA.out_sub _ _ _ _ _ OC); lia | exact OB | exact OS | exact H2]|].
  split.
  { destruct H3 as (V1 & V2). unfold PMLA.vis_at, PMLA.u64 in *. split; [exact (u64T _ _ 592 _ OC ltac:(lia) ltac:(lia) V1)|].
    intros i Hi. destruct OC as (_ & _ & O3). rewrite (AG (C + 592 + i) (O3 (C + 592 + i) ltac:(lia))). exact (V2 i Hi). }
  split; [unfold PMLA.u8 in *; exact (u8T _ _ 640 _ OC ltac:(lia) ltac:(lia) H4)|].
  exact (PTA.def_ag M M' S AG C 656 OC H5).
Qed.

Definition chunks_out (LBo : list (Z * Z)) : Prop :=
  forall b, In (b, 16384) LBo -> out b 16384 /\ (forall a, in_shadow_of b 16384 a -> S a) /\ b mod 8 = 0.
Lemma evcA_ag : forall V lv LBo ps', out V 48 -> chunks_out LBo -> PMCSA.evcA L M V lv LBo ps' -> PMCSA.evcA L M' V lv LBo ps'.
Proof.
  intros V lv LBo ps' OV OCH (w0 & HW & HE). exists w0. split.
  - destruct w0 as [[p0 e0]|]; [|exact I]. destruct HW as (b & Hin & B1 & B2 & BD & BS). exists b. split; [exact Hin|]. split; [exact B1|]. split; [exact B2|].
    destruct (OCH b Hin) as (OB & SB' & B8).
    split; [apply (PTA.def_ag M M' S AG); [apply (PTA.out_sub _ _ _ _ _ OB); lia | exact BD] | exact (PTA.shadow_blk_ag M M' S AG b 16384 ltac:(lia) SB' B8 BS)].
  - destruct OV as (O1 & O2 & O3). apply (CKA2.evp_ag segs M M' V lv w0 ps'); [lia | lia | intros a Ha; apply AG; apply O3; lia | exact HE].
Qed.

Lemma rn_relA_ag : forall ps ps' code dn' V LBo, out V 48 -> chunks_out LBo ->
  PMCSA.rn_relA L ps ps' code dn' M V LBo -> PMCSA.rn_relA L ps ps' code dn' M' V LBo.
Proof.
  intros ps ps' code dn' V LBo OV OCH (R1 & R2). split; [exact R1|]. intros Hc Hd. destruct (R2 Hc Hd) as (Q1 & [Q2|(Q3 & Q4)]); split; [exact Q1 | left; exact Q2 | exact Q1 |].
  right. split; [exact Q3 | exact (evcA_ag V _ LBo ps' OV OCH Q4)].
Qed.

Definition blocks_out (LBx : list (Z * Z)) : Prop :=
  forall b, In b LBx -> out (fst b) (snd b) /\ (forall a, in_shadow_of (fst b) (snd b) a -> S a) /\ fst b mod 8 = 0 /\ 0 <= snd b.
Lemma cctor_postA_ag : forall LB C IS E kx bx rep g LB' cr' LBk W,
  g <> PML.LS0 ->
  out C 656 -> out IS 272 -> out E 16 -> RDKC.text_out S IS rep ->
  (match rep with PML.SShort _ => True | PML.SLong cap p _ => 0 <= cap /\ p mod 8 = 0 /\ forall a, in_shadow_of p cap a -> S a end) ->
  (forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> 0 <= a < 2 ^ 63 /\ S a) ->
  (forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 1
             \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
             \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> PMLA.in_foot IC a) ->
  blocks_out LB' ->
  PMCSA.cctor_postA L IC LB C IS E kx bx rep g M LB' cr' LBk W -> PMCSA.cctor_postA L IC LB C IS E kx bx rep g M' LB' cr' LBk W.
Proof.
  intros LB C IS E kx bx rep g LB' cr' LBk W Hg0 OC OI OE OT OSH STS FOOTL OBL H.
  destruct H as (ch & ps' & code & gp' & rdst' & g' & bof' & dn' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19).
  assert (InB : In (PML.ps_bptr ps', PML.ps_bcap ps') LB') by (rewrite H10; left; reflexivity).
  assert (InS : In (PML.ps_sb ps', PML.ps_scap ps') LB') by (rewrite H10; right; left; reflexivity).
  assert (InC : In (ch, 16384) LB') by (rewrite H10; right; right; left; reflexivity).
  destruct (OBL _ InB) as (OB & SB' & B8 & B0). destruct (OBL _ InS) as (OS & SS' & S8 & S0). destruct (OBL _ InC) as (OCk & SC' & C8 & _). cbn [fst snd] in *.
  assert (CHO : chunks_out ((ch, 16384) :: LB)).
  { intros b Hb. assert (Hb' : In (b, 16384) LB') by (rewrite H10; right; right; exact Hb). destruct (OBL _ Hb') as (X1 & X2 & X3 & _). cbn [fst snd] in *. exact (conj X1 (conj X2 X3)). }
  assert (H18' : shadow_blk M' ch 16384) by exact (PTA.shadow_blk_ag M M' S AG ch 16384 ltac:(lia) SC' C8 H17).
  assert (H19' : L5.defined M' ch 16384) by exact (PTA.def_ag M M' S AG ch 16384 OCk H18).
  assert (OV : out (C + 592) 48) by (apply (PTA.out_sub _ _ _ _ _ OC); lia).
  exists ch, ps', code, gp', rdst', g', bof', dn'.
  split; [exact (cursor_atA_ag C IS ch bof' dn' ps' OC OB OS H1)|].
  split; [exact (RDKC.isrc_ag segs IC M M' S AG IS rep gp' rdst' OI OT ltac:(destruct H3 as (_ & X & _); exact X) H2)|].
  split; [exact H3|].
  split; [exact (PTA.ec_at_ag segs IC M M' S AG E code OE H4)|].
  assert (Hg' : g' <> PML.LS0) by (destruct H6 as [E6|E6]; rewrite E6; [exact Hg0 | destruct g; discriminate]).
  split; [apply (PTA.ls_ok_ag segs IC M M' S AG g'); [exact Hg' | exact STS | exact FOOTL | exact H5]|].
  split; [exact H6|]. split; [exact H7|].
  split.
  { apply (RDKC.win_okA_agx M M' ((ch, 16384) :: LB) ch ps'); [| | exact H18' | exact H19' | exact H8].
    - intros c a Hc Hne Ha. destruct (CHO c Hc) as ((_ & _ & O3) & SHc & _). destruct Ha as [Ha|Ha]; [exact (AG a (O3 a Ha)) | exact (AG a (SHc a Ha))].
    - intros c Hc. destruct (CHO c Hc) as ((O1 & O2 & _) & _ & C8'). split; [exact O1|]. split; [lia | exact C8']. }
  split; [unfold PMLA.u8 in *; apply (PTA.u8_ag segs M M' S AG); [split; [pose proof (STS (PMLA.SYSCAT_GUARD IC) ltac:(right; apply FOOTL; right; right; left; lia)) as (X & _); lia|]; split; [pose proof (STS (PMLA.SYSCAT_GUARD IC) ltac:(right; apply FOOTL; right; right; left; lia)) as (X & _); lia|]; intros i Hi; replace i with (PMLA.SYSCAT_GUARD IC) by lia; exact (proj2 (STS (PMLA.SYSCAT_GUARD IC) ltac:(right; apply FOOTL; right; right; left; lia))) | exact H9]|].
  split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact H13|].
  split.
  { intros Hc Hd. destruct (H14 Hc Hd) as (Q1 & [Q2|(Q3 & Q4)]); split; [exact Q1 | left; exact Q2 | exact Q1 |]. right. split; [exact Q3 | exact (evcA_ag (C + 592) 0 _ ps' OV CHO Q4)]. }
  split.
  { apply (PTA.parser_sh_ag M M' S AG ps'); [lia | | exact B8 | exact S8 | exact SB' | exact SS' | exact H15].
    destruct H1 as (_ & HP & _). unfold PMLA.parser_at in HP. split; [lia|]. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  split; [exact (RDKC.srep_sh_ag M M' S AG rep OSH H16)|].
  split; [exact H18'|]. split; [exact H19'|]. exact H19.
Qed.

Definition HFOOT2 : Prop := forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 2
             \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
             \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> PMLA.in_foot IC a.
Definition HSTAT : Prop := forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> 0 <= a < 2 ^ 63 /\ S a.
Definition sh_out (o g : Z) : Prop := forall j, 0 <= j < g -> S (HeapIfaceA.S o + j).
Lemma cctor_preA_ag : forall ar FF cr LB C IS E sp scr kx bx rep g,
  HSTAT -> HFOOT2 ->
  out C 656 -> out IS 272 -> out E 16 -> RDKC.text_out S IS rep ->
  (match rep with PML.SShort _ => True | PML.SLong cap p _ => 0 <= cap /\ p mod 8 = 0 /\ forall a, in_shadow_of p cap a -> S a end) ->
  sh_out C 82 -> sh_out IS 34 -> sh_out E 2 ->
  (forall a, HeapIfaceA.S (sp - scr) <= a < HeapIfaceA.S (sp - scr) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - scr)) / 8 -> S a) ->
  PMCSA.cctor_preA L ar IC M FF cr LB C IS E sp scr kx bx rep g -> PMCSA.cctor_preA L ar IC M' FF cr LB C IS E sp scr kx bx rep g.
Proof.
  intros ar FF cr LB C IS E sp scr kx bx rep g HS HF OC OI OE OT OSH SC SI SE SSTK H.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23).
  assert (HF1 : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 1
             \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
             \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> PMLA.in_foot IC a).
  { intros a Ha. apply HF. destruct Ha as [X|[X|[X|X]]]; [left; exact X | right; left; exact X | right; right; left; lia | right; right; right; exact X]. }
  assert (GS : forall k, 0 <= k < 2 -> S (PMLA.SYSCAT_GUARD IC + k) /\ 0 <= PMLA.SYSCAT_GUARD IC + k < 2 ^ 63).
  { intros k Hk. destruct (HS (PMLA.SYSCAT_GUARD IC + k) ltac:(right; apply HF; right; right; left; lia)) as (X & Y). exact (conj Y X). }
  assert (GO : forall k, 0 <= k < 2 -> out (PMLA.SYSCAT_GUARD IC + k) 1).
  { intros k Hk. destruct (GS k Hk) as (Y & X). split; [lia|]. split; [lia|]. intros i Hi. replace i with (PMLA.SYSCAT_GUARD IC + k) by lia. exact Y. }
  pose proof (GO 0 ltac:(lia)) as GO0. rewrite Z.add_0_r in GO0.
  assert (FOBJ : forall o n FF', sh_out o (n / 8) -> PMSA.fobj M FF' o n -> PMSA.fobj M' FF' o n).
  { intros o n FF' SO (F1 & F2 & F3). split; [exact F1|]. split; [exact F2|]. exact (PTA.shadow_zero_ag M M' S AG o (n / 8) SO F3). }
  unfold PMCSA.cctor_preA.
  split; [exact (RDKC.isrc_ag segs IC M M' S AG IS rep _ 0 OI OT H8 H1)|].
  split; [exact (PTA.ec_at_ag segs IC M M' S AG E 0 OE H2)|].
  split; [exact (TKA.img_ro_ag IC M M' S AG HS H3)|].
  split; [exact (TKA.gloc_done_ag L IC M M' S AG HS HF H4)|].
  split; [exact (PTA.ls_ok_ag segs IC M M' S AG g H6 HS HF1 H5)|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
  split; [exact (FOBJ C 656 FF SC H9)|]. split; [exact (FOBJ IS 272 FF SI H10)|]. split; [exact (FOBJ E 16 FF SE H11)|].
  split; [exact H12|]. split; [exact H13|]. split; [exact H14|].
  split; [exact (PTA.def_ag M M' S AG C 656 OC H15)|].
  split.
  { unfold PMLA.u8 in *. destruct H16 as [(X0 & X1)|X0]; [left; split | right].
    - exact (PTA.u8_ag segs M M' S AG _ _ GO0 X0).
    - exact (PTA.u8_ag segs M M' S AG _ _ (GO 1 ltac:(lia)) X1).
    - exact (PTA.u8_ag segs M M' S AG _ _ GO0 X0). }
  split; [exact H17|]. split; [exact H18|]. split; [exact H19|]. split; [exact H20|].
  split; [exact (RDKC.srep_sh_ag M M' S AG rep OSH H21)|]. split; [exact H22|].
  apply (PTA.stksh_ag ar M M' sp scr); [|exact H23]. intros a Ha. exact (AG a (SSTK a Ha)).
Qed.

End Agree.

Section Cells.
Variable segs : list Segment.
Lemma kword2_zero_u8 : forall E (M : mem) a A, kentry_ok segs E M (KWord a 2 (ELit 0)) -> estart E a = A ->
  L5.u8_at segs M A 0 /\ L5.u8_at segs M (A + 1) 0.
Proof.
  intros E M a A (_ & Hfl & Hr) Ha. rewrite (CL5.adenot_start E a _ Hfl), Ha in Hr. cbn [edenot] in Hr.
  unfold word_to_le_bytes in Hr. rewrite Z_to_bv_unsigned in Hr. cbn in Hr. unfold L5.u8_at.
  cbn [rdn] in Hr |- *. destruct (match M (Z_to_bv 64 A) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 A) end) as [b0|] eqn:E0; [|discriminate].
  destruct (match M (Z_to_bv 64 A + 1)%bv with Some b => Some b | None => seg_rom segs (Z_to_bv 64 A + 1)%bv end) as [b1|] eqn:E1; [|discriminate].
  injection Hr as H0 H1. subst b0 b1. split; [reflexivity|].
  assert (EQ : Z_to_bv 64 (A + 1) = (Z_to_bv 64 A + 1)%bv) by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned; unfold bv_wrap; rewrite Zplus_mod_idemp_l; change (bv_unsigned (1%bv : bv 64)) with 1; reflexivity).
  rewrite EQ, E1. reflexivity.
Qed.
End Cells.

Lemma cctor_postA_cr : forall L IC LB C IS E kx bx rep g (M : mem) LB' cr1 cr2 LBk W,
  PMCSA.cctor_postA L IC LB C IS E kx bx rep g M LB' cr1 LBk W ->
  (forall ps' ch, LB' = PML.ps_blocks ps' ++ (ch, 16384) :: LB -> PMLA.pcredit_xA L cr2 ps' kx bx) ->
  PMCSA.cctor_postA L IC LB C IS E kx bx rep g M LB' cr2 LBk W.
Proof.
  intros L IC LB C IS E kx bx rep g M LB' cr1 cr2 LBk W H HC.
  destruct H as (ch & ps' & code & gp' & rdst' & g' & bof' & dn' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19).
  exists ch, ps', code, gp', rdst', g', bof', dn'. repeat (split; [assumption|]). split; [exact (HC ps' ch H10)|]. repeat (split; [assumption|]). exact H19.
Qed.

End CTK.
