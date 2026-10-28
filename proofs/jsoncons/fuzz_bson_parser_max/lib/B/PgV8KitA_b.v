(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrcKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcKitA_b PgTxtKitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgV8A_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGV8KA.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation keepb := PGTKA.keepb.
Abbreviation keepb_true := PGTKA.keepb_true.
Abbreviation v8_atA := (PGV8.v8_at RSEGS PMSPA.accA PGV8A.annA).

(* [comment removed for export] *)
Lemma annA_agree (M M' : word -> option byte) b u c :
  0 <= u <= c -> b mod 8 = 0 -> PMFA.agsh M M' b c -> PGV8A.annA M b u c -> PGV8A.annA M' b u c.
Proof.
  intros Hu B8 SH (Z0 & P & T). unfold PGV8A.annA, HAJ.ann_shadow in *.
  pose proof (Z.div_mod (c + 7) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)) as D2.
  pose proof (Z.div_mod u 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound u 8 ltac:(lia)) as D4.
  pose proof (Z.div_mod b 8 ltac:(lia)) as D5.
  assert (SJ : forall j, 0 <= j < (c + 7) / 8 -> M' (Z_to_bv 64 (HeapIfaceA.S b + j)) = M (Z_to_bv 64 (HeapIfaceA.S b + j))).
  { intros j Hj. replace (HeapIfaceA.S b + j) with (HeapIfaceA.S (b + j * 8)).
    - apply SH. lia.
    - unfold HeapIfaceA.S. rewrite Z.div_add by lia. lia. }
  assert (U8 : 0 <= u / 8) by (apply Z.div_pos; lia).
  split; [|split].
  - intros j Hj. unfold byte_at. rewrite SJ; [exact (Z0 j Hj)| lia].
  - intros NZ. unfold byte_at. rewrite SJ; [exact (P NZ)| lia].
  - intros j Hj. unfold byte_at. rewrite SJ; [exact (T j Hj)|]. assert (0 <= (u + 7) / 8) by (apply Z.div_pos; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma v8_keepA (M M' : word -> option byte) o x :
  0 <= o -> o + 24 <= 2 ^ 64 -> PMFA.agA M M' o 24 ->
  (forall b n c, x = PGV8.V8Blk b n c -> PMFA.agA M M' b c) ->
  v8_atA M o x -> v8_atA M' o x.
Proof.
  intros Ho Ho' [AG SH] AGB (VD & VA & VR).
  split; [exact (L5C.defined_agree M M' o 24 AG VD)|]. split; [exact (PMFA.accA_agree M M' o 24 SH VA)|].
  destruct x as [|b n c].
  - destruct VR as (U0 & U1 & U2).
    split; [apply (L5C.u64_at_agree RSEGS M M' o); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| lia| lia| exact U0]|].
    split; [apply (L5C.u64_at_agree RSEGS M M' (o + 8)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| lia| lia| exact U1]|].
    apply (L5C.u64_at_agree RSEGS M M' (o + 16)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| lia| lia| exact U2].
  - destruct VR as (U0 & U1 & U2 & B1 & B2 & B3 & B4 & BD & BA & BN). destruct (AGB b n c eq_refl) as [AGb SHb].
    split; [apply (L5C.u64_at_agree RSEGS M M' o); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| lia| lia| exact U0]|].
    split; [apply (L5C.u64_at_agree RSEGS M M' (o + 8)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| lia| lia| exact U1]|].
    split; [apply (L5C.u64_at_agree RSEGS M M' (o + 16)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| lia| lia| exact U2]|].
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
    split; [exact (L5C.defined_agree M M' b c AGb BD)|].
    split; [apply (PMFA.accA_agree M M' b n); [eapply PMFA.agsh_sub; [exact SHb| lia| lia]| exact BA]|].
    apply (annA_agree M M' b n c); [exact B1| apply PMKA.mod16_8'; exact B4| exact SHb| exact BN].
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Theorem src_of_vw_okA (T : PGV8.vowner) (x : PGV8.v8) (g : Z) :
  PGV8A.vowner_ok RSEGS PMA.AD L ar HI T -> PGSA.owner_ok RSEGS PMA.AD L ar HI (PGV8A.src_of_vw T x g).
Proof.
  intros [TS TL TU].
  destruct TL as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15).
  constructor; cbn [PGS.ow_at PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi PGS.ow_win PGV8A.src_of_vw].
  - (* [comment removed for export] *) intros M src OB' (OB & -> & AT). destruct (TS M src x g OB AT) as (S1 & S2 & S3 & _ & _).
    split; [exact S1|]. split; [exact S2| exact S3].
  - (* [comment removed for export] *) set (xos := PGV8.vw_os T) in *. set (xois := PGV8.vw_ois T) in *. set (xotb := PGV8.vw_ov T) in *. set (xlo := PGV8.vw_lo T) in *. set (xhi := PGV8.vw_hi T) in *. repeat split; try lia.
  - (* [comment removed for export] *)
    intros LBX sp scr Wx M M' src src' OB' FF LK Aw cr VM OFR (OB & -> & AT) HH FA FB FC HP SF' QC.
    set (xos := PGV8.vw_os T) in *. set (xois := PGV8.vw_ois T) in *. set (xotb := PGV8.vw_ov T) in *. set (xlo := PGV8.vw_lo T) in *. set (xhi := PGV8.vw_hi T) in *.
    exists OB. split; [reflexivity|].
    destruct (TS M src x g OB AT) as (SF & NI & DEF & VS & TBOK).
    set (BIG := PM.src_own src ++ (PGV8.v8_own x ++ OB) ++ LBX) in *.
    assert (BIGE : BIG = (PM.src_own src ++ PGV8.v8_own x) ++ (OB ++ LBX)) by (unfold BIG; rewrite <- !app_assoc; reflexivity).
    assert (BIGE2 : BIG = PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) by (unfold BIG; rewrite <- !app_assoc; reflexivity).
    pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & _).
    assert (ND : NoDup (map fst BIG)) by exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
    assert (AOT : PMSPA.aobjA FF xotb 24) by (apply (PGSKA.aobjA_sub FF xlo xhi); [exact OFR| lia| lia]).
    assert (AOS : PMSPA.aobjA FF xos 296) by (apply (PGSKA.aobjA_sub FF xlo xhi); [exact OFR| lia| lia]).
    assert (AOI : PMSPA.aobjA FF xois 272) by (apply (PGSKA.aobjA_sub FF xlo xhi); [exact OFR| lia| lia]).
    set (Wx0 := List.filter (keepb xlo xhi OB) Wx).
    (* [comment removed for export] *)
    assert (REJ : forall r, In r Wx -> keepb xlo xhi OB r = false ->
              (exists b n c, x = PGV8.V8Blk b n c /\ b <= fst r /\ fst r + snd r <= b + n)).
    { intros r Hr KF. pose proof (proj1 (Forall_forall _ _) FC r Hr) as [(C1 & C2 & C3)|[_ W]]; [|exact W].
      exfalso. assert (KT : keepb xlo xhi OB r = true); [|rewrite KT in KF; discriminate KF].
      apply (proj2 (keepb_true xlo xhi OB r)). split; [exact C1|]. split; [|exact C3]. intros B m Hin. apply (C2 B m). apply in_or_app. right. exact Hin. }
    assert (OWNIN : forall B m, In (B, m) (PM.src_own src ++ PGV8.v8_own x) -> In (B, m) BIG) by (intros B m Hin; rewrite BIGE; apply in_or_app; left; exact Hin).
    assert (OWNF : forall B m, In (B, m) (PM.src_own src ++ PGV8.v8_own x) ->
              forall B' m', In (B', m') (OB ++ LBX) -> B + m <= B' \/ B' + m' <= B).
    { intros B m Hin B' m' Hin'. assert (HB' : In (B', m') BIG) by (rewrite BIGE; apply in_or_app; right; exact Hin').
      apply (PMASK.blk_apart L ar C HI HIok BIG FF LK cr Aw M VM B m B' m' HH (OWNIN B m Hin) HB').
      apply (PMASK.fst_neq_appA (PM.src_own src ++ PGV8.v8_own x) (OB ++ LBX) B m B' m'); [rewrite <- BIGE; exact ND| exact Hin| exact Hin']. }
    assert (HP2 : L5CA.ahpres L ar ((PM.src_own src ++ PGV8.v8_own x) ++ (OB ++ LBX)) ([] ++ FF) sp scr (PGS.W_srcG xos xois src ++ Wx) M M').
    { rewrite <- BIGE. exact HP. }
    (* [comment removed for export] *)
    assert (HW : forall a, aclient L ar (OB ++ LBX) FF sp scr a -> L5.outside (PGS.W_srcfG xos xois ++ [(xotb, 24)] ++ Wx0) a ->
                 L5.outside (PGS.W_srcG xos xois src ++ Wx) a).
    { intros a CA OW r Hr Hin. apply in_app_or in Hr. destruct Hr as [Hr|Hr].
      - unfold PGS.W_srcG in Hr. apply in_app_or in Hr. destruct Hr as [Hr|[<-|[]]].
        + apply (OW r); [apply in_or_app; left; exact Hr| exact Hin].
        + unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
          exact (PMARS1.own_not_aclient L ar C HI HIok (PM.src_own src ++ PGV8.v8_own x) (OB ++ LBX) FF LK cr Aw M VM (PM.sr_qc src) PM.CHUNK a sp scr
                   ltac:(rewrite <- BIGE; exact HH) ltac:(apply in_or_app; left; left; reflexivity) Hin CA).
      - destruct (keepb xlo xhi OB r) eqn:KB.
        + apply (OW r); [|exact Hin]. apply in_or_app. right. apply in_or_app. right. unfold Wx0. apply filter_In. split; [exact Hr| exact KB].
        + destruct (REJ r Hr KB) as (b & n & c & E & W1 & W2). unfold L5.in_rng in Hin.
          assert (NC : 0 <= n <= c) by (rewrite E in VS; destruct VS as (_ & _ & _ & _ & _ & NC & _); exact NC).
          exact (PMARS1.own_not_aclient L ar C HI HIok (PM.src_own src ++ PGV8.v8_own x) (OB ++ LBX) FF LK cr Aw M VM b c a sp scr
                   ltac:(rewrite <- BIGE; exact HH) ltac:(apply in_or_app; right; rewrite E; left; reflexivity) ltac:(clear - Hin W1 W2 NC; lia) CA). }
    assert (EK : L5SAR.ek L ar (OB ++ LBX) FF sp scr (PGS.W_srcfG xos xois ++ [(xotb, 24)] ++ Wx0) M M').
    { apply (L5SAR.ek_callee L ar (OB ++ LBX) (PM.src_own src ++ PGV8.v8_own x) FF [] sp scr sp scr _ _ M M' HP2); [lia| lia| exact HW]. }
    assert (DK : L5SAR.dk L ar (OB ++ LBX) FF sp scr M M').
    { apply (L5SAR.dk_callee L ar (OB ++ LBX) (PM.src_own src ++ PGV8.v8_own x) FF [] sp scr sp scr _ M M' HP2); lia. }
    (* [comment removed for export] *)
    assert (WAPP : PMKA.wapp (PGS.W_srcG xos xois src ++ Wx)).
    { intros r Hr. apply in_app_or in Hr.
      pose proof AOS as (f & Hf & X1 & X2). destruct (WF _ Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in FSAPP, Y2. destruct FSAPP as (FS0 & FSs & FS47).
      pose proof AOI as (f' & Hf' & X1' & X2'). destruct (WF _ Hf') as (Y1' & Y2' & _). unfold FS_BYTES in Y2'.
      destruct Hr as [Hr|Hr].
      - unfold PGS.W_srcG, PGS.W_srcfG in Hr. cbn [app] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
        + destruct FSs as [Z|Z]; [left|right]; clear - Z X1 X2 Y1 Y2; lia.
        + destruct FSs as [Z|Z]; [left|right]; clear - Z X1' X2' Y1' Y2'; lia.
        + destruct FSs as [Z|Z]; [left|right]; clear - Z X1' X2' Y1' Y2'; lia.
        + destruct (WB _ (OWNIN _ _ ltac:(apply in_or_app; left; left; reflexivity))) as ((_ & _ & _ & _ & _ & QAPP) & _). cbn [fst snd] in QAPP.
          unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QAPP. clear - QAPP. lia.
      - destruct (keepb xlo xhi OB r) eqn:KB.
        + apply (proj1 (keepb_true xlo xhi OB r)) in KB. destruct KB as (_ & _ & AM). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in AM |- *. clear - AM. lia.
        + destruct (REJ r Hr KB) as (b & n & c & E & W1 & W2).
          assert (NC : 0 <= n <= c) by (rewrite E in VS; destruct VS as (_ & _ & _ & _ & _ & NC & _); exact NC).
          destruct (WB _ (OWNIN _ _ ltac:(apply in_or_app; right; rewrite E; left; reflexivity))) as ((_ & _ & _ & _ & _ & QAPP) & _). cbn [fst snd] in QAPP.
          unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QAPP |- *. clear - QAPP W1 W2 NC. lia. }
    pose proof HP as (EKB & DSB & DKB0).
    assert (EKBIG : L5SAR.ek L ar BIG FF sp scr (PGS.W_srcG xos xois src ++ Wx) M M') by exact EKB.
    assert (DKBIG : L5SAR.dk L ar BIG FF sp scr M M') by exact DKB0.
    apply (TU LBX sp scr Wx0 M M' src src' x x g g OB FF LK Aw cr VM OFR AT).
    + (* [comment removed for export] *) rewrite <- BIGE2. exact HH.
    + (* [comment removed for export] *) apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) FA b). rewrite app_assoc. exact Hb.
    + (* [comment removed for export] *) intros b Hb. split.
      * apply FB. apply in_or_app. right. exact Hb.
      * intros B' m' Hin'. destruct b as [B m]. cbn [fst snd].
        destruct (OWNF B' m' ltac:(apply in_or_app; right; exact Hin') B m ltac:(apply in_or_app; left; exact Hb)); lia.
    + (* [comment removed for export] *) apply Forall_forall. intros r Hr. unfold Wx0 in Hr. apply filter_In in Hr. destruct Hr as [_ KB].
      exact (proj1 (keepb_true xlo xhi OB r) KB).
    + (* [comment removed for export] *) apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF sp scr _ M M' EK DSB DK).
    + exact SF'.
    + exact QC.
    + (* [comment removed for export] *)
      assert (OUTT : forall a, xotb <= a < xotb + 24 -> L5.outside (PGS.W_srcG xos xois src ++ Wx) a).
      { intros a Ha r Hr Hin. apply in_app_or in Hr. destruct Hr as [Hr|Hr].
        - unfold PGS.W_srcG, PGS.W_srcfG in Hr. cbn [app] in Hr. unfold L5.in_rng in Hin.
          destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; try (clear - Hin Ha L13 L14 L15; lia).
          destruct (PMASK.blk_obj_apart L ar C HI HIok BIG FF LK cr Aw M VM (PM.sr_qc src) PM.CHUNK xotb 24 HH (OWNIN _ _ ltac:(apply in_or_app; left; left; reflexivity)) AOT) as [Z|Z]; clear - Z Hin Ha; lia.
        - destruct (keepb xlo xhi OB r) eqn:KB.
          + apply (proj1 (keepb_true xlo xhi OB r)) in KB. destruct KB as [KB _]. unfold L5.in_rng in Hin. clear - KB Hin Ha L5' L6; lia.
          + destruct (REJ r Hr KB) as (b & n & c & E & W1 & W2). unfold L5.in_rng in Hin.
            assert (NC : 0 <= n <= c) by (rewrite E in VS; destruct VS as (_ & _ & _ & _ & _ & NC & _); exact NC).
            destruct (PMASK.blk_obj_apart L ar C HI HIok BIG FF LK cr Aw M VM b c xotb 24 HH (OWNIN _ _ ltac:(apply in_or_app; right; rewrite E; left; reflexivity)) AOT) as [Z|Z]; clear - Z Hin Ha W1 W2 NC; lia. }
      assert (KEPT : forall a, xotb <= a < xotb + 24 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. apply EKBIG. pose proof AOT as (f & Hf & X1 & X2). destruct (FRB f Hf) as (Y1 & Y2).
        split; [clear - Ha X1 X2 Y1 Y2; lia|]. split; [apply PMASR1.cl_of_bf; right; apply (PMASR1.in_fframe_of_aobjA FF xotb 24 a AOT Ha)| exact (OUTT a Ha)]. }
      destruct VS as (VD & VA & VR). pose proof AOT as (ft & Hft & Xt1 & Xt2). destruct (FRB ft Hft) as (Yt1 & Yt2).
      assert (AG : L5C.agree_on M M' xotb 24) by (intros i Hi; apply KEPT; exact Hi).
      split; [apply (PMASK.defined_dk L ar BIG FF sp scr M M' xotb 24 DKBIG); [intros i Hi; apply PMASR1.cl_of_bf; right; apply (PMASR1.in_fframe_of_aobjA FF xotb 24 i AOT Hi)| clear - Xt1 Yt1; lia| clear - Xt2 Yt2; lia| exact VD]|].
      split; [exact (PMKA.acc_keepA' L ar BIG FF sp scr _ M M' EKBIG WAPP FRB xotb 24 AOT VA)|].
      destruct x as [|b n c].
      * destruct VR as (U0 & U1 & U2).
        split; [apply (L5C.u64_at_agree RSEGS M M' xotb); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| clear - Xt1 Yt1; lia| clear - Xt2 Yt2; lia| exact U0]|].
        split; [apply (L5C.u64_at_agree RSEGS M M' (xotb + 8)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| clear - Xt1 Yt1; lia| clear - Xt2 Yt2; lia| exact U1]|].
        apply (L5C.u64_at_agree RSEGS M M' (xotb + 16)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| clear - Xt1 Yt1; lia| clear - Xt2 Yt2; lia| exact U2].
      * destruct VR as (U0 & U1 & U2 & B1 & B2 & B3 & B4 & BD & BA & BN).
        assert (HB : In (b, c) BIG) by (apply OWNIN; apply in_or_app; right; left; reflexivity).
        destruct (BRB _ HB) as (Z0 & Z4). cbn [fst snd] in Z0, Z4.
        assert (SHB : PMFA.agsh M M' b c) by (apply (PMASK.agsh_blk L ar BIG FF sp scr _ M M' b c EKBIG WAPP HB); [clear - Z0; lia| clear - Z4; lia]).
        split; [apply (L5C.u64_at_agree RSEGS M M' xotb); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| clear - Xt1 Yt1; lia| clear - Xt2 Yt2; lia| exact U0]|].
        split; [apply (L5C.u64_at_agree RSEGS M M' (xotb + 8)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| clear - Xt1 Yt1; lia| clear - Xt2 Yt2; lia| exact U1]|].
        split; [apply (L5C.u64_at_agree RSEGS M M' (xotb + 16)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| clear - Xt1 Yt1; lia| clear - Xt2 Yt2; lia| exact U2]|].
        split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split.
        -- apply (PMASK.defined_dk L ar BIG FF sp scr M M' b c DKBIG); [intros i Hi; apply (L5SAR.block_client L ar BIG FF sp scr b c i HB Hi)| clear - Z0; lia| clear - Z4; lia| exact BD].
        -- split; [apply (PMFA.accA_agree M M' b n); [eapply PMFA.agsh_sub; [exact SHB| lia| clear - B1; lia]| exact BA]|].
           apply (annA_agree M M' b n c); [exact B1| apply PMKA.mod16_8'; exact B4| exact SHB| exact BN].
    + exact TBOK.
  - (* [comment removed for export] *)
    intros M src OB' p k (OB & -> & AT) (Hk & WIN).
    set (xos := PGV8.vw_os T) in *. set (xois := PGV8.vw_ois T) in *. set (xotb := PGV8.vw_ov T) in *. set (xlo := PGV8.vw_lo T) in *. set (xhi := PGV8.vw_hi T) in *.
    destruct (TS M src x g OB AT) as (_ & _ & _ & (VD & VA & VR) & _).
    split; [exact Hk|]. destruct WIN as (b & n & c & -> & W1 & W2).
    destruct VR as (_ & _ & _ & B1 & _ & _ & _ & BD & BA & _).
    split; [intros i Hi; replace (p + i) with (b + (p - b + i)) by lia; apply BD; lia|].
    split; [left; exists b, c; split; [apply in_or_app; left; left; reflexivity| lia]|].
    intros i Hi. apply BA. lia.
Qed.

(* [comment removed for export] *)
Lemma v8_visG LB FF LK cr Aw M model otb x :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PMSPA.aobjA FF otb 24 -> otb mod 8 = 0 -> v8_atA M otb x ->
  let MV := mrestrict (ahid Aw model) M in
  (6905856 <= otb <= 140737488355304 /\ otb mod 8 = 0 /\ (2147446784 + 17592186048512 <= otb \/ otb + 24 <= 2147446784))
  /\ L5KA.zeros_at MV (otb / 8 + 2147450880) 3 /\ L5.writable RSEGS MV otb 24 /\ otb + 24 <= ahl_ceil ar
  /\ (forall a n, otb <= a -> a + n <= otb + 24 -> L5A.avis (ahid Aw model) a n)
  /\ PMSPA.aobjA FF otb 24 /\ ar_fs ar <= otb /\ otb + 24 <= ar_fs ar + FS_BYTES.
Proof.
  intros HH AO O8 VS MV.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model otb 24 0 0 HH (PMKA.aobj_of_aobjA FF otb 24 AO O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
  assert (ACC : PMSPA.accA M otb 24) by (destruct VS as (_ & TC & _); exact TC).
  split; [split; [lia| split; [exact O8| exact OBIG]]|].
  split.
  { change 3 with (24 / 8). apply (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model otb 24 HH AO O8 ltac:(lia) ltac:(reflexivity) ACC). }
  split.
  { apply (proj2 (L5A.writable_vis _ M otb 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]. }
  split; [lia|]. split; [intros a n Ha Hn; eapply L5A.avis_sub; [exact OVIS| lia| lia]|]. split; [exact AO|].
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & _).
  destruct AO as (f & Hf & W1 & W2). destruct (WF _ Hf) as (X1 & X2 & _). lia.
Qed.

End WithHeap.
End PGV8KA.
