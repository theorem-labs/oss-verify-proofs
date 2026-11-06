(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5WordsB L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5ARed L5AMul10K L5DivLeafSpecsA L5ANormP As0Clz L5AShrOk L5ACmp.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require As0_code_92368_93368 As0_code_93368_94368.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ANORM.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5AMULK. Import L5ANORMP. Import L5DLA. Import L5W.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | blia] ].

Lemma SCR_EQ : NORM_SCR = 4656. Proof. reflexivity. Qed.
Lemma SHLSCR_EQ : SHL_SCR + 16 = 4576. Proof. reflexivity. Qed.
Lemma MULMSCR_EQ : MULM_SCR + 16 = 4576. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma clz_of_spec w : 1 <= w < 2 ^ 64 -> 0 <= clz_of w <= 63 /\ 2 ^ 63 <= w * 2 ^ clz_of w < 2 ^ 64.
Proof.
  intros Hw. unfold clz_of. pose proof (Z.log2_spec w ltac:(lia)) as [A B]. pose proof (Z.log2_nonneg w) as C.
  assert (D: Z.log2 w <= 63).
  { destruct (Z_lt_le_dec 63 (Z.log2 w)) as [X|X]; [|exact X]. exfalso.
    assert (2 ^ 64 <= 2 ^ Z.log2 w) by (apply Z.pow_le_mono_r; lia). lia. }
  split. lia.
  replace (2 ^ 63) with (2 ^ Z.log2 w * 2 ^ (63 - Z.log2 w)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  replace (2 ^ 64) with (2 ^ Z.succ (Z.log2 w) * 2 ^ (63 - Z.log2 w)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  pose proof (Z.pow_pos_nonneg 2 (63 - Z.log2 w) ltac:(lia) ltac:(lia)). nia.
Qed.
Lemma clz_of_unique w c : 1 <= w -> 0 <= c -> 2 ^ 63 <= w * 2 ^ c < 2 ^ 64 -> c = clz_of w.
Proof.
  intros Hw Hc [A B]. unfold clz_of.
  assert (E: Z.log2 (w * 2 ^ c) = 63). { apply Z.log2_unique. lia. split. exact A. exact B. }
  rewrite Z.log2_mul_pow2 in E by lia. lia.
Qed.

Lemma u64_at_agree1 M M' a v : (forall i, a <= i < a + 8 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v.
Proof. intros HA Ha H8 Hu. eapply (L5C.u64_at_agree RSEGS M M'). intros i Hi. apply HA. exact Hi. lia. lia. exact Hu. Qed.
Lemma u32_at_agree1 M M' a v : (forall i, a <= i < a + 4 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.

Lemma adebl_app L cr0 l1 l2 : adebl L cr0 (l1 ++ l2) = adebl L (adebl L cr0 l2) l1.
Proof. induction l1 as [|[A0 n0] l1 IH]; cbn [app adebl]. reflexivity. rewrite IH. reflexivity. Qed.

Lemma outside2 (o1 n1 o2 n2 a : Z) : ~ (o1 <= a < o1 + n1) -> ~ (o2 <= a < o2 + n2) -> L5.outside [(o1, n1); (o2, n2)] a.
Proof. intros H1 H2 rr [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; assumption. Qed.

Lemma obj_limbs_prefix M fb m st rw n :
  L5C.obj_limbs RSEGS M (L5.BO fb m st) rw -> (n <= m)%nat -> (match st with L5.BInl _ _ => (m <= 2)%nat | _ => True end) ->
  L5C.obj_limbs RSEGS M (L5.BO fb n st) (firstn n rw).
Proof.
  intros (Lw & Rw & V) Hn Hst. unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st] in *. split. rewrite length_firstn. Lia.lia.
  split. apply (proj2 (words_ok_BF _)). apply (BigFactsBase.words_ok_firstn n rw). apply (proj1 (words_ok_BF rw)). exact Rw.
  destruct st as [v0 v1|cap q].
  - subst rw. rewrite L5C.firstn_firstn_le by Lia.lia. reflexivity.
  - apply L5C.limbs_at_firstn. exact V.
Qed.


(* [comment removed for export] *)
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis SHLok : shl_specA_at 16 L ar HI.
Hypothesis MULMok : mulm_specA_at 16 L ar HI.

Lemma ffr_lk FF LK LK' d : ffr FF LK d -> incl LK' LK -> NoDup (map ff_addr (FF ++ LK')) -> ffr FF LK' d.
Proof.
  unfold ffr. intros R I ND. rewrite ff_count_app in R |- *.
  pose proof (ff_count_incl 1 LK' LK I (nodup_of_map_app_r FF LK' ND)) as C2. Lia.lia.
Qed.

(* [comment removed for export] *)
Lemma obj_vis LB FF LK cr A M model o sp :
  ri_inv HI LB FF LK cr A M (vml_of model) -> aobj FF o 32 -> shadow_zero M o 4 -> ahl_ceil ar + 4096 <= sp -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 ->
  let H := ahid A model in let MV := mrestrict H M in
  (4096 <= o <= 140737488355296 /\ aligned o 8 /\ (2147446784 + 17592186048512 <= o \/ o + 32 <= 2147446784) /\ o + 32 <= sp - 4096 /\ 0x633000 <= o)
  /\ L5KA.zeros_at MV (o / 8 + SB) 4 /\ L5.writable RSEGS MV o 32 /\ avis H o 32
  /\ (forall a v, o <= a -> a + 8 <= o + 32 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v)
  /\ (forall v, L5.u8_at RSEGS M o v -> L5.u8_at RSEGS MV o v).
Proof.
  intros HH AOB SZ SLO SPT H MV.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp 4560 HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH. fold H in OVIS, OVSH.
  split. { unfold aligned. clear - OR OBIG SLO SPT. lia. }
  split. { apply (proj2 (zeros_at_vis H M _ 4 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  split. { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H M o 32 OVIS)). exact ODEF. clear - OR; lia. clear - OR; lia. }
  split. exact OVIS.
  split. { intros a v Ha Hb Hc. apply (proj2 (u64_at_vis H M a v ltac:(eapply avis_sub; [exact OVIS | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Hb OR; lia))). exact Hc. }
  intros v Hc. apply (proj2 (u8_at_vis H M o v ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). exact Hc.
Qed.

(* [comment removed for export] *)
Lemma stk_vis LB FF LK cr A M model sp :
  ri_inv HI LB FF LK cr A M (vml_of model) -> astk ar M sp NORM_SCR ->
  let H := ahid A model in let MV := mrestrict H M in
  (140735332491824 <= sp <= 140737488355328 /\ aligned sp 16)
  /\ L5.writable RSEGS MV (sp - 80) 80
  /\ (forall a v, sp - 80 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v)
  /\ (forall a v, sp - 80 <= a -> a + 8 <= sp -> L5.u64_at RSEGS MV a v -> L5.u64_at RSEGS M a v).
Proof.
  intros HH STK H MV. pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). rewrite SCR_EQ in SLO.
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & _). fold H in VIS.
  assert (SPR : 140735332491824 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  split. { split. exact SPR. exact A16. }
  split. { apply (proj2 (writable_vis H M (sp - 80) 80 (VIS (sp - 80) 80 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
           eapply (astk_writable ar M sp). exact STK. rewrite SCR_EQ; clear; lia. clear; lia. clear; lia. }
  split. { intros a v Ha Hb Hc. apply (proj2 (u64_at_vis H M a v (VIS a 8 ltac:(clear - SLO Ha; lia) ltac:(clear - SPR Hb; lia)) ltac:(clear - SPR Ha; lia) ltac:(clear - SPR Hb; lia))). exact Hc. }
  intros a v Ha Hb Hc. apply (proj1 (u64_at_vis H M a v (VIS a 8 ltac:(clear - SLO Ha; lia) ltac:(clear - SPR Hb; lia)) ltac:(clear - SPR Ha; lia) ltac:(clear - SPR Hb; lia))). exact Hc.
Qed.

(* [comment removed for export] *)
Lemma px_vis LB FF LK cr A M model px sp :
  ri_inv HI LB FF LK cr A M (vml_of model) -> astk ar M sp NORM_SCR -> px mod 4 = 0 -> sp <= px -> L5.defined M px 4 -> px + 4 <= ar_sptop ar -> shadow_zero M px 1 ->
  let H := ahid A model in let MV := mrestrict H M in
  (140735332487168 <= px <= 140737488355324 /\ aligned px 4 /\ (2147446784 + 17592186048512 <= px \/ px + 4 <= 2147446784))
  /\ L5.writable RSEGS MV px 4 /\ L5KA.zeros_at MV (px / 8 + SB) 1
  /\ (forall v, L5.u32_at RSEGS M px v -> L5.u32_at RSEGS MV px v)
  /\ (forall a, px <= a < px + 4 -> H (Z_to_bv 64 a) = false).
Proof.
  intros HH STK P4 SPX PTOP PSP SZ H MV. pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). rewrite SCR_EQ in SLO.
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & _ & _ & _ & _ & _ & VSTSH). fold H in VIS, VSTSH.
  assert (PR : 140735332487168 <= px <= 140737488355324) by (clear - SLO SHI SPT SPX PSP; lia).
  assert (PV : avis H px 4). { apply VIS. clear - SLO SPX; lia. clear - PR; lia. }
  split. { split. exact PR. split. exact P4. left. clear - PR; lia. }
  split. { apply (proj2 (writable_vis H M px 4 PV ltac:(clear - PR; lia) ltac:(clear - PR; lia))). apply (L5C.writable_of_defined RSEGS).
           exact PTOP. clear - PR; lia. clear - PR; lia. }
  split. { assert (SHV : forall i, 0 <= i < 1 -> in_shadow_of (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar) (px / 8 + SB + i)).
           { intros i Hi. unfold in_shadow_of, S.
             assert (E1 : (ahl_ceil ar) / 8 <= px / 8) by (apply Z.div_le_mono; [clear; lia | clear - SLO SPX; lia]).
             assert (E2 : px / 8 <= (ahl_ceil ar + (ar_sptop ar - ahl_ceil ar) - 1) / 8) by (apply Z.div_le_mono; [clear; lia | clear - PSP; lia]).
             clear - Hi E1 E2. lia. }
           apply (proj2 (zeros_at_vis H M _ 1 (VSTSH _ 1 SHV))).
           intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  split. { intros v Hc. apply (proj2 (u32_at_vis H M px v PV ltac:(clear - PR; lia) ltac:(clear - PR; lia))). exact Hc. }
  intros a Ha. replace a with (px + (a - px)) by (clear; lia). apply (PV (a - px)). clear - Ha; lia.
Qed.



(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition keptP (LBc : list (Z * Z)) (FF : list fframe) (M Mc : word -> option byte) (sp o d n : Z) : Prop :=
  (forall a, sp - 80 <= a < 2 ^ 47 -> Mc (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall o2, aobj FF o2 32 -> (o + 32 <= o2 \/ o2 + 32 <= o) -> forall a, o2 <= a < o2 + 32 -> Mc (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall o2, aobj FF o2 32 -> forall i, 0 <= i < 4 -> Mc (Z_to_bv 64 (o2 / 8 + SB + i)) = M (Z_to_bv 64 (o2 / 8 + SB + i)))
  /\ (forall p, sp <= p < ar_sptop ar -> Mc (Z_to_bv 64 (p / 8 + SB)) = M (Z_to_bv 64 (p / 8 + SB)))
  /\ (forall q2 n2, In (q2, n2) LBc -> (d + n <= q2 \/ q2 + n2 <= d) -> forall a, q2 <= a < q2 + n2 -> Mc (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall q2 n2, In (q2, n2) LBc -> forall a, in_shadow_of q2 n2 a -> Mc (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall q2 n2, In (q2, n2) LBc -> L5.defined M q2 n2 -> L5.defined Mc q2 n2).
Lemma callee_frame LBc FF LKc crc Ac M model Mc Wc sp o d n :
  ri_inv HI LBc FF LKc crc Ac M (vml_of model) -> astk ar M sp NORM_SCR ->
  ahpres L ar LBc FF (sp - 80) 4576 Wc M Mc -> (forall x, L5.outside [(o, 32); (d, n)] x -> L5.outside Wc x) ->
  aobj FF o 32 -> ((d = o + 16 /\ n <= 16) \/ (exists c, In (d, 8 * c) LBc /\ n <= 8 * c)) ->
  keptP LBc FF M Mc sp o d n /\ astk ar Mc sp NORM_SCR.
Proof.
  intros HH STK AHP WS AOB DLOC.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). rewrite SCR_EQ in SLO.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (aobj_facts L ar C HI LY HIok LBc FF LKc crc Ac M model o 32 (sp - 80) 4576 HH AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & _ & _ & _ & _ & _).
  (* [comment removed for export] *)
  assert (DF : 0 <= d /\ d + n <= ahl_ceil ar /\ (d + n <= 0x7fff7000 \/ 0x10007fff8000 <= d \/ n <= 0)
               /\ (forall o2, aobj FF o2 32 -> (o + 32 <= o2 \/ o2 + 32 <= o) -> d + n <= o2 \/ o2 + 32 <= d \/ n <= 0)).
  { destruct DLOC as [[-> Hn]|(c & INc & Hn)].
    - split. clear - OR; lia. split. clear - OR Hn; lia. split. clear - OBIG Hn; lia. intros o2 _ AP. clear - AP Hn; lia.
    - pose proof (WB _ INc) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _ & _ & _ & _ & QFF & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5, QFF.
      unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
      split. clear - Q0; lia. split. clear - Q4 Hn; lia. split. clear - Q5 Hn; lia.
      intros o2 (f & Hf & X1 & X2 & _) _. pose proof (QFF f ltac:(apply in_or_app; left; exact Hf)) as X. clear - X X1 X2 Hn. lia. }
  destruct DF as (D0 & DCEIL & DAPP & DOBJ).
  destruct AHP as (P & DEFc & DKc).
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBc FF (sp - 80) 4576 a -> ~ (o <= a < o + 32) -> ~ (d <= a < d + n) -> Mc (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. apply P. split. exact Ha. split. exact Hc. apply WS. apply outside2; assumption. }
  split. 2:{ apply (astk_after L ar C HI HIok LBc FF LKc crc Ac M M Mc _ sp _ (sp - 80) 4576 Wc HH STK (mem_grows_refl M)). split. exact P. split. exact DEFc. exact DKc.
             rewrite SCR_EQ; clear; lia. clear; lia. rewrite SCR_EQ; clear; lia. }
  unfold keptP.
  split. { intros a Ra. apply KEEP. clear - Ra SLO SPT; lia. apply stack_client. clear - Ra SLO; lia. clear - Ra; lia. clear - Ra OR SLO; lia. clear - Ra DCEIL SLO; lia. }
  split. { intros o2 AO2 AP a Ra. pose proof AO2 as (f2 & Hf2 & Y1 & Y2 & _). pose proof (WF f2 Hf2) as (Z1 & Z2 & _).
           apply KEEP. unfold FS_BYTES, app_mem in *. clear - Ra Y1 Y2 Z1 Z2 FSCEIL SPT FSAPP; lia. apply (obj_client L ar LBc FF (sp - 80) 4576 o2 32 a AO2 Ra).
           clear - Ra AP; lia. pose proof (DOBJ o2 AO2 AP) as X. clear - Ra X; lia. }
  split. { intros o2 AO2 i Hi.
           pose proof (aobj_facts L ar C HI LY HIok LBc FF LKc crc Ac M model o2 32 (sp - 80) 4576 HH AO2 ltac:(clear; lia) ltac:(reflexivity)) as (OR2 & _ & _ & _ & _ & _ & OCLSH2).
           change (32 / 8) with 4 in OCLSH2. apply KEEP. clear - Hi OR2; unfold SB; lia. apply OCLSH2. exact Hi.
           clear - Hi OR2 OBIG; unfold SB; lia. clear - Hi OR2 DAPP; unfold SB; lia. }
  split. { intros p Rp. apply KEEP. clear - Rp SLO SPT; unfold SB; lia.
           right; right; right; right; left. unfold in_shadow_of, S.
           assert (E1 : (ahl_ceil ar) / 8 <= p / 8) by (apply Z.div_le_mono; [clear; lia | clear - SLO Rp; lia]).
           assert (E2 : p / 8 <= (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) / 8) by (apply Z.div_le_mono; [clear; lia | clear - Rp SPT; lia]).
           clear - E1 E2; lia. clear - Rp SLO SPT OBIG; unfold SB; lia. clear - Rp SLO SPT DAPP; unfold SB; lia. }
  split. { intros q2 n2 IN2 AP a Ra. pose proof (WB _ IN2) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _ & _ & _ & _ & QFF & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5, QFF.
           apply KEEP. clear - Ra Q0 Q4 SPT; lia. apply (block_client L ar LBc FF (sp - 80) 4576 q2 n2 a IN2 Ra).
           destruct AOB as (f & Hf & X1 & X2 & _). pose proof (QFF f ltac:(apply in_or_app; left; exact Hf)) as X. clear - Ra X X1 X2; lia. clear - Ra AP; lia. }
  split. { intros q2 n2 IN2 a Sa. pose proof (WB _ IN2) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5.
           unfold in_shadow_of, S in Sa.
           assert (RA' : 0x7fff8000 <= a < 0x10007fff8000). { clear - Sa Q0 Q3 Q4 SPT. unfold SB in *. lia. }
           apply KEEP. clear - RA'; lia. do 6 right. exists (q2, n2). split. exact IN2. exact Sa. clear - RA' OBIG; lia. clear - RA' DAPP; lia. }
  intros q2 n2 IN2 DEF2 i Hi. pose proof (WB _ IN2) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q4.
  apply DKc. clear - Hi Q0 Q4 SPT; lia. apply (block_client L ar LBc FF (sp - 80) 4576 q2 n2 (q2 + i) IN2). clear - Hi; lia. apply DEF2. exact Hi.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Lemma big_at_kept LBc FF M Mc sp o d n o2 b2 :
  keptP LBc FF M Mc sp o d n -> aobj FF o2 32 -> (o + 32 <= o2 \/ o2 + 32 <= o) -> 0 <= o2 -> o2 + 32 <= 2 ^ 64 ->
  L5.big_at RSEGS M o2 b2 -> L5.big_at RSEGS Mc o2 b2.
Proof.
  intros (_ & K2 & _) AO2 AP H0 H1 OB. eapply L5C.big_at_agree. 4: exact OB. 2: exact H0. 2: exact H1. intros j Hj. apply (K2 o2 AO2 AP j Hj).
Qed.
Lemma limbs_kept LBc FF M Mc sp o d n fb2 (m2 : nat) st2 ws2 :
  keptP LBc FF M Mc sp o d n ->
  (match st2 with L5.BDyn cap2 q2 => In (q2, 8 * cap2) LBc /\ (d + n <= q2 \/ q2 + 8 * cap2 <= d) /\ Z.of_nat m2 <= cap2 /\ 0 <= q2 /\ q2 + 8 * cap2 <= 2 ^ 64 | L5.BInl _ _ => True end) ->
  L5C.obj_limbs RSEGS M (L5.BO fb2 m2 st2) ws2 -> L5C.obj_limbs RSEGS Mc (L5.BO fb2 m2 st2) ws2.
Proof.
  intros (_ & _ & _ & _ & K5 & _) ST (L1 & L2 & L3). cbn [L5.bo_len L5.bo_st] in *. split. exact L1. split. exact L2.
  destruct st2 as [v0 v1|cap2 q2]. exact L3. destruct ST as (IN2 & AP & Hm & Q0 & Q1).
  eapply (L5C.limbs_at_agree RSEGS M Mc). 4: exact L3. 2: exact Q0. 2:{ rewrite L1. clear - Hm Q1. lia. }
  intros j Hj. apply (K5 q2 (8 * cap2) IN2 AP j). rewrite L1 in Hj. clear - Hj Hm. lia.
Qed.
Lemma limbs_kept_b LBc FF M Mc sp o d n (b2 : L5.bigobj) ws2 :
  keptP LBc FF M Mc sp o d n ->
  (match L5.bo_st b2 with L5.BDyn cap2 q2 => In (q2, 8 * cap2) LBc /\ (d + n <= q2 \/ q2 + 8 * cap2 <= d) /\ Z.of_nat (L5.bo_len b2) <= cap2 /\ 0 <= q2 /\ q2 + 8 * cap2 <= 2 ^ 64 | L5.BInl _ _ => True end) ->
  L5C.obj_limbs RSEGS M b2 ws2 -> L5C.obj_limbs RSEGS Mc b2 ws2.
Proof. destruct b2 as [fb2 m2 st2]. apply limbs_kept. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma afresh_kept LBc FF M Mc sp o d n LBx FFx FFx' A0 cap0 :
  keptP LBc FF M Mc sp o d n -> In (A0, 8 * cap0) LBc -> incl FFx' FFx ->
  afresh L ar LBx FFx M A0 (8 * cap0) -> afresh L ar LBx FFx' Mc A0 (8 * cap0).
Proof.
  intros (_ & _ & _ & _ & _ & K6 & K7) IN0 IFF (BR & BA & FA & DEF0 & SH0 & SHP).
  split. exact BR. split. exact BA. split. { eapply fframes_apart_incl. exact FA. exact IFF. }
  split. { apply (K7 A0 (8 * cap0) IN0 DEF0). }
  destruct BR as (B0 & _ & B16 & Bn & _).
  assert (E8 : (8 * cap0) / 8 = cap0) by (clear; lia). assert (E0 : (8 * cap0) mod 8 = 0) by (clear; lia).
  split.
  - intros j Hj. unfold byte_at, S. rewrite E8 in Hj. rewrite (K6 A0 (8 * cap0) IN0). apply SH0. rewrite E8. exact Hj.
    unfold in_shadow_of, S. clear - Hj B0 B16 Bn. lia.
  - intros X. exfalso. apply X. exact E0.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma blk_obj_apart LB FF LK cr A M V q c o :
  ri_inv HI LB FF LK cr A M V -> In (q, 8 * c) LB -> aobj FF o 32 -> o + 32 <= q \/ q + 8 * c <= o.
Proof.
  intros HH INB (g0 & Hg & X1 & X2 & _). pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB _ INB)))))) g0 ltac:(apply in_or_app; left; exact Hg)) as X. cbn [fst snd] in X.
  pose proof (WF g0 Hg) as (_ & _ & _ & Y4 & _).
  assert (HB : 0 < ff_bytes (ff_class g0)). { clear - Y4. destruct Y4 as [E|[E|[E|[]]]]; rewrite <- E; [change (ff_bytes 1) with 128 | change (ff_bytes 2) with 256 | change (ff_bytes 3) with 512]; lia. }
  clear - X X1 X2 HB. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet)
          (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (od on px sp r : Z) (bd bn : L5.bigobj) (wd wn : list Z).
Hypothesis HH0 : ri_inv HI LB FF LK cr A M0 (vml_of model0).
Hypothesis AM0 : amodel_ok A model0.
Hypothesis HK0 : K [].
Hypothesis G11 : getr R0 11%bv = Z_to_bv 64 od.
Hypothesis G12 : getr R0 12%bv = Z_to_bv 64 on.
Hypothesis G13 : getr R0 13%bv = Z_to_bv 64 px.
Hypothesis G1 : getr R0 1%bv = Z_to_bv 64 r.
Hypothesis RA : L5.ra_ok r.
Hypothesis G2 : getr R0 2%bv = Z_to_bv 64 sp.
Hypothesis A32 : sp mod 32 = 0.
Hypothesis G4 : getr R0 4%bv = Z_to_bv 64 (hl_tp L).
Hypothesis STK : astk ar M0 sp NORM_SCR.
Hypothesis ROOM : ffr FF LK 4.
Hypothesis RS : ffrs FF sp.
Hypothesis OBd : L5.big_at RSEGS M0 od bd.
Hypothesis OLd : L5C.obj_limbs RSEGS M0 bd wd.
Hypothesis Hnd : (1 <= L5.bo_len bd <= 290)%nat.
Hypothesis TOPnz : nth_w wd (L5.bo_len bd - 1) <> 0.
Hypothesis TOPsm : (2 <= L5.bo_len bd)%nat -> nth_w wd (L5.bo_len bd - 1) < 2 ^ 63.
Hypothesis OBn : L5.big_at RSEGS M0 on bn.
Hypothesis OLn : L5C.obj_limbs RSEGS M0 bn wn.
Hypothesis Hnn : (1 <= L5.bo_len bn <= 290)%nat.
Hypothesis NN2 : (2 <= L5.bo_len bd)%nat -> (2 <= L5.bo_len bn)%nat /\ exists i, (i < L5.bo_len bn)%nat /\ nth_w wn i <> 0.
Hypothesis AOd : aobj FF od 32.
Hypothesis SZd0 : shadow_zero M0 od 4.
Hypothesis AOn : aobj FF on 32.
Hypothesis SZn0 : shadow_zero M0 on 4.
Hypothesis APdn : od + 32 <= on \/ on + 32 <= od.
Hypothesis P4 : px mod 4 = 0.
Hypothesis Spx : sp <= px.
Hypothesis Hpx : L5.defined M0 px 4.
Hypothesis Hpx2 : px + 4 <= ar_sptop ar.
Hypothesis SZp0 : shadow_zero M0 px 1.
Hypothesis BLKd : forall cap q, L5.bo_st bd = L5.BDyn cap q -> In (q, 8 * cap) LB /\ Z.of_nat (L5.bo_len bd) + 1 <= cap.
Hypothesis BLKn : forall cap q, L5.bo_st bn = L5.BDyn cap q -> In (q, 8 * cap) LB /\ Z.of_nat (L5.bo_len bn) + 1 <= cap.
Hypothesis SECcap : second (L5.bo_len bd) (shl_result wd (clz_of (nth_w wd (L5.bo_len bd - 1)))) = true ->
       (L5.bo_dyn bd = true -> Z.of_nat (L5.bo_len bd) + 2 <= L5.bo_cap bd) /\ (L5.bo_dyn bn = true -> Z.of_nat (L5.bo_len bn) + 2 <= L5.bo_cap bn).
Hypothesis APB : forall cd qd cn qn, L5.bo_st bd = L5.BDyn cd qd -> L5.bo_st bn = L5.BDyn cn qn -> qd + 8 * cd <= qn \/ qn + 8 * cn <= qd.
Hypothesis CR : acredits L cr (cnt bd + cnt bn).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (c : Z) (gd gn : growth) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        norm_postA L ar LB FF LK' cr M0 M' R0 R' od on px sp bd bn wd wn c gd gn LB' cr' ->
        model_rt model0 model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K.

(* [comment removed for export] *)
Let nd : nat := L5.bo_len bd.
Let nn : nat := L5.bo_len bn.
Let w0 : Z := nth_w wd (nd - 1).
Let C0 : Z := clz_of w0.
Let D : list Z := shl_result wd C0.
Let Dn : list Z := shl_result wn C0.
Let SEC : bool := second nd D.
Let W : list L5.range := norm_W od on px bd bn.

Lemma wd_len : length wd = nd. Proof. exact (proj1 OLd). Qed.
Lemma wn_len : length wn = nn. Proof. exact (proj1 OLn). Qed.
Lemma wd_ok : words_ok wd. Proof. exact (proj1 (proj2 OLd)). Qed.
Lemma wn_ok : words_ok wn. Proof. exact (proj1 (proj2 OLn)). Qed.
Lemma w0_rng : 1 <= w0 < 2 ^ 64.
Proof. pose proof (words_ok_nth wd (nd - 1) wd_ok) as X. subst w0. fold nd in TOPnz. unfold nth_w in *. lia. Qed.
Lemma C0_rng : 0 <= C0 <= 63 /\ 2 ^ 63 <= w0 * 2 ^ C0 < 2 ^ 64.
Proof. apply clz_of_spec. apply w0_rng. Qed.
Lemma D_len : length D = (if C0 =? 0 then nd else Datatypes.S nd).
Proof. subst D. unfold shl_result. destruct (Z.eqb_spec C0 0). apply wd_len. rewrite shl_words_length, wd_len. reflexivity. Qed.
Lemma Dn_len : length Dn = (if C0 =? 0 then nn else Datatypes.S nn).
Proof. subst Dn. unfold shl_result. destruct (Z.eqb_spec C0 0). apply wn_len. rewrite shl_words_length, wn_len. reflexivity. Qed.
Lemma D_ok : words_ok D.
Proof. subst D. unfold shl_result. destruct (Z.eqb_spec C0 0). apply wd_ok. apply shl_words_ok. pose proof C0_rng; lia. apply wd_ok. Qed.
Lemma Dn_ok : words_ok Dn.
Proof. subst Dn. unfold shl_result. destruct (Z.eqb_spec C0 0). apply wn_ok. apply shl_words_ok. pose proof C0_rng; lia. apply wn_ok. Qed.
Lemma val_shl_result ws : words_ok ws -> BigFactsBase.val (shl_result ws C0) = 2 ^ C0 * BigFactsBase.val ws.
Proof.
  intros Wo. unfold shl_result. destruct (Z.eqb_spec C0 0) as [E|NE]. rewrite E. lia.
  apply shl_words_val. pose proof C0_rng; lia. exact Wo.
Qed.
Lemma D_rlen_pos : (1 <= rlen D)%nat.
Proof.
  apply L5WB.rlen_pos_of_val. subst D. rewrite (val_shl_result wd wd_ok).
  pose proof (L5WB.val_pos_of_nonzero wd (nd - 1) wd_ok ltac:(rewrite wd_len; subst nd; Lia.lia) TOPnz). pose proof (Z.pow_pos_nonneg 2 C0 ltac:(lia) ltac:(pose proof C0_rng; lia)). nia.
Qed.
Lemma Dn_rlen_pos : (2 <= nd)%nat -> (1 <= rlen Dn)%nat.
Proof.
  intros H2. destruct (NN2 H2) as [_ (i & Hi & Hnz)]. apply L5WB.rlen_pos_of_val. subst Dn. rewrite (val_shl_result wn wn_ok).
  pose proof (L5WB.val_pos_of_nonzero wn i wn_ok ltac:(rewrite wn_len; exact Hi) Hnz). pose proof (Z.pow_pos_nonneg 2 C0 ltac:(lia) ltac:(pose proof C0_rng; lia)). nia.
Qed.
Lemma rlen_D_le : (rlen D <= Datatypes.S nd)%nat. Proof. pose proof (rlen_le D) as H. rewrite D_len in H. destruct (C0 =? 0); Lia.lia. Qed.
Lemma rlen_Dn_le : (rlen Dn <= Datatypes.S nn)%nat. Proof. pose proof (rlen_le Dn) as H. rewrite Dn_len in H. destruct (C0 =? 0); Lia.lia. Qed.

(* [comment removed for export] *)
Definition saved (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (U R0 1) /\ L5.u64_at RSEGS M (sp - 16) (U R0 8) /\ L5.u64_at RSEGS M (sp - 24) (U R0 9) /\ L5.u64_at RSEGS M (sp - 32) (U R0 18)
  /\ L5.u64_at RSEGS M (sp - 40) (U R0 19) /\ L5.u64_at RSEGS M (sp - 48) (U R0 20) /\ L5.u64_at RSEGS M (sp - 56) (U R0 21) /\ L5.u64_at RSEGS M (sp - 64) (U R0 22)
  /\ L5.u64_at RSEGS M (sp - 72) (U R0 23) /\ L5.u64_at RSEGS M (sp - 80) (U R0 24).
Definition regsN (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 80) /\ getr R (reg 8) = Z_to_bv 64 od /\ getr R (reg 9) = Z_to_bv 64 on /\ getr R (reg 18) = Z_to_bv 64 px
  /\ getr R (reg 19) = Z_to_bv 64 2147450880 /\ getr R (reg 21) = Z_to_bv 64 (od / 8 + 2147450880)
  /\ getr R (reg 22) = Z_to_bv 64 (8 * (Z.of_nat nd - 1)) /\ getr R (reg 23) = Z_to_bv 64 (Z.of_nat nd - 1) /\ getr R (reg 24) = Z_to_bv 64 (px / 8 + 2147450880)
  /\ (forall k, In k [3; 4; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k)).
(* [comment removed for export] *)
Definition ctx (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit) (LK3 : list fframe) (A3 : list (Z * Z)) : Prop :=
  ri_inv HI LB3 FF LK3 cr3 A3 M (vml_of model) /\ amodel_ok A3 model /\ model_rt model0 model /\ incl A A3 /\ incl LK3 LK
  /\ regsN R /\ saved M /\ astk ar M sp NORM_SCR /\ L5.u32_at RSEGS M px C0
  /\ shadow_zero M od 4 /\ shadow_zero M on 4 /\ shadow_zero M px 1
  /\ ek L ar LB FF sp NORM_SCR W M0 M /\ dk L ar LB FF sp NORM_SCR M0 M.



Lemma sp_rng : 140735332491824 <= sp <= 140737488355328 /\ ahl_ceil ar + 4096 + 4656 <= sp /\ sp <= ar_sptop ar /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47.
Proof. pose proof STK as (A16 & SLO & SHI & SPT & _). rewrite SCR_EQ in SLO. clear - SLO SHI SPT. lia. Qed.

(* [comment removed for export] *)
Lemma px_def (Mk : word -> option byte) : dk L ar LB FF sp NORM_SCR M0 Mk -> L5.defined Mk px 4.
Proof.
  intros DK i Hi. pose proof sp_rng as (SR & SLO & SHI & SPT).
  apply DK. clear - Hi Spx Hpx2 SR SPT; lia. apply stack_client. clear - Hi Spx Hpx2 SLO SPT; lia. clear - Hi Spx; lia. apply Hpx. exact Hi.
Qed.


(* [comment removed for export] *)
Lemma ctx_after (R R5 : bvmap 5 word) (M M5 : word -> option byte) (model model5 : Model) (LB3 LB5 : list (Z * Z)) (cr3 cr5 : credit) (LK3 LK5 : list fframe) (A3 A5 : list (Z * Z))
      (Wc : list L5.range) (o d n : Z) :
  ctx R M model LB3 cr3 LK3 A3 -> regs_preserved R R5 ->
  ri_inv HI LB5 FF LK5 cr5 A5 M5 (vml_of model5) -> amodel_ok A5 model5 -> model_rt model model5 -> incl A3 A5 -> incl LK5 LK3 ->
  ahpres L ar LB3 FF (sp - 80) 4576 Wc M M5 -> (forall x, L5.outside [(o, 32); (d, n)] x -> L5.outside Wc x) ->
  aobj FF o 32 -> In (o, 32) W -> ((d = o + 16 /\ n <= 16) \/ (exists c, In (d, 8 * c) LB3 /\ n <= 8 * c)) ->
  (exists BX, LB3 = BX ++ LB) ->
  (forall a, aclient L ar LB FF sp NORM_SCR a -> L5.outside W a -> ~ (d <= a < d + n)) ->
  ctx R5 M5 model5 LB5 cr5 LK5 A5 /\ keptP LB3 FF M M5 sp o d n.
Proof.
  intros CTX RP HH5 AM5 RT5 IA5 ILK5 AHP WS AOB OW DLOC (BX & ELB) DW.
  destruct CTX as (HH & AM & RT & IA & ILK & RG & SV & STK3 & PX & SZd & SZn & SZp & EK & DK).
  pose proof (callee_frame LB3 FF LK3 cr3 A3 M model M5 Wc sp o d n HH STK3 AHP WS AOB DLOC) as (KP & STK5).
  pose proof KP as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  pose proof sp_rng as (SPR & SLO & SHI & SPT).
  split; [|exact KP]. unfold ctx.
  split. exact HH5. split. exact AM5. split. { eapply L5LZ.model_rt_trans. exact RT. exact RT5. }
  split. { intros x Hx. apply IA5. apply IA. exact Hx. } split. { intros x Hx. apply ILK. apply ILK5. exact Hx. }
  split. { destruct RG as (g2 & g8 & g9 & g18 & g19 & g21 & g22 & g23 & g24 & gK). unfold regsN.
           repeat split; try (rewrite (cs_of_preserved R R5 _ RP) by inl; assumption).
           intros k Hk. rewrite (cs_of_preserved R R5 k RP). apply gK. exact Hk. revert Hk; apply (L5K.incl_b _ cs_all); vm_compute; reflexivity. }
  split. { destruct SV as (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24). unfold saved.
           repeat split; (eapply u64_at_agree1; [intros i Hi; apply K1; clear - Hi SPR; lia | clear - SPR; lia | clear - SPR; lia | assumption]). }
  split. exact STK5.
  split. { eapply u32_at_agree1. 4: exact PX. intros i Hi. apply K1. clear - Hi Spx Hpx2 SPT; lia. clear - Spx SPR; lia. clear - Hpx2 SPT; lia. }
  split. { intros j Hj. unfold byte_at, S. rewrite (K3 od AOd j Hj). apply SZd. exact Hj. }
  split. { intros j Hj. unfold byte_at, S. rewrite (K3 on AOn j Hj). apply SZn. exact Hj. }
  split. { intros j Hj. unfold byte_at, S. replace (px / 8 + SB + j) with (px / 8 + SB) by (clear - Hj; lia). rewrite (K4 px ltac:(clear - Spx Hpx2; lia)).
           specialize (SZp j Hj). unfold byte_at, S in SZp. replace (px / 8 + SB + j) with (px / 8 + SB) in SZp by (clear - Hj; lia). exact SZp. }
  subst LB3.
  split.
  - eapply ek_trans. exact EK. eapply (ek_callee L ar LB BX FF [] sp NORM_SCR (sp - 80) 4576 W Wc M M5). exact AHP. rewrite SCR_EQ; clear; lia. clear; lia.
    intros a Hc Ho. apply WS. apply outside2. { pose proof (Ho (o, 32) OW) as X. unfold L5.in_rng in X. cbn [fst snd] in X. exact X. } apply DW; assumption.
  - eapply dk_trans. exact DK. eapply (dk_callee L ar LB BX FF [] sp NORM_SCR (sp - 80) 4576 Wc M M5). exact AHP. rewrite SCR_EQ; clear; lia. clear; lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mulm_step (o : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit) (LK3 : list fframe) (A3 : list (Z * Z))
      (rr fb : Z) (n : nat) (cap q : Z) (rw : list Z) :
  ctx R M model LB3 cr3 LK3 A3 ->
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 MAXW -> getr R (reg 1) = Z_to_bv 64 rr -> L5.ra_ok rr ->
  aobj FF o 32 -> In (o, 32) W -> shadow_zero M o 4 ->
  L5.big_at RSEGS M o (L5.BO fb n (L5.BDyn cap q)) -> L5C.obj_limbs RSEGS M (L5.BO fb n (L5.BDyn cap q)) rw -> In (q, 8 * cap) LB3 ->
  (1 <= n <= 291)%nat -> Z.of_nat n + 1 <= cap ->
  (exists BX, LB3 = BX ++ LB) ->
  (forall a, aclient L ar LB FF sp NORM_SCR a -> L5.outside W a -> ~ (q <= a < q + 8 * cap)) ->
  (forall (fx5 : FPState) (R5 : bvmap 5 word) (M5 : word -> option byte) (model5 : Model) (LK5 : list fframe) (A5 : list (Z * Z)),
      ctx R5 M5 model5 LB3 cr3 LK5 A5 -> incl LK5 LK3 ->
      keptP LB3 FF M M5 sp o q (8 * (Z.of_nat n + 1)) ->
      (let rw' := mulw_words rw MAXW in let fb' := if Nat.eqb (rlen rw') 0 then Z.land fb 253 else fb in
       length rw' = Datatypes.S n /\ words_ok rw' /\ (rlen rw' <= Datatypes.S n)%nat /\
       L5.big_at RSEGS M5 o (L5.BO fb' (rlen rw') (L5.BDyn cap q)) /\ L5C.obj_limbs RSEGS M5 (L5.BO fb' (Datatypes.S n) (L5.BDyn cap q)) rw') ->
      srealizes RSEGS SCFG (cfg (fx:=fx5) R5 rr M5 model5) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R MULM M model) K.
Proof.
  intros CTX G10 G11' G1' RA' AOB OW SZo OB OL INq Hn Hcap LBX DW NEXT.
  pose proof CTX as (HH & AM & RT & IA & ILK & RG & SV & STK3 & PX & SZd & SZn & SZp & EK & DK).
  destruct RG as (g2 & g8 & g9 & g18 & g19 & g21 & g22 & g23 & g24 & gK).
  pose proof sp_rng as (SPR & SLO & SHI & SPT).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF3.
  assert (ND3 : NoDup (map ff_addr (FF ++ LK3))). { clear - WF3. decompose [and] WF3. assumption. } clear WF3.
  pose proof OB as (_ & _ & _ & B0 & _). cbn [L5.bo_fb L5.bo_st] in B0.
  apply (MULMok fx R M model K LB3 FF LK3 cr3 A3 o (sp - 80) rr MAXW (L5.BO fb n (L5.BDyn cap q)) rw HH AM HK0).
  - rewrite r10. exact G10.
  - rewrite r11. exact G11'.
  - unfold MAXW. clear; lia.
  - cbn [L5.bo_len]. clear - Hn; Lia.lia.
  - cbn [L5.bo_len]. clear - Hn; Lia.lia.
  - intros _. cbn [L5.bo_len L5.bo_cap L5.bo_st]. exact Hcap.
  - intros ND. exfalso. unfold L5.bo_dyn in ND. cbn [L5.bo_fb] in ND. rewrite B0 in ND. discriminate.
  - rewrite r1. exact G1'.
  - exact RA'.
  - rewrite r2. exact g2.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - A32. lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite r4, (gK 4%nat ltac:(cbn; tauto)), <- r4. exact G4.
  - rewrite MULMSCR_EQ. eapply astk_sub. exact STK3. apply mem_grows_refl. clear; lia. clear; lia. rewrite SCR_EQ; clear; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - A32. lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (ffr_lk FF LK LK3 4 ROOM ILK ND3).
  - eapply ffrs_le. exact RS. clear; lia.
  - exact OB.
  - exact OL.
  - exact AOB.
  - exact SZo.
  - intros cap' q' E. cbn [L5.bo_st] in E. inversion E; subst. exact INq.
  - intros fx5 R5 M5 model5 g5 LB5 cr5 LK5 A5 POST RT5 IA5 AM5 ILK5 HH5.
    unfold mulm_postA_at in POST. cbv zeta in POST. cbn [L5.bo_len L5.bo_fb L5.bo_st L5.bo_dyn L5.bo_data] in POST.
    destruct POST as (RP5 & B10 & LRW & WRW & NLE5 & st5 & OB5 & OL5 & GG).
    destruct g5 as [|A5' c5].
    2:{ exfalso. destruct GG as (ND & _). unfold L5.bo_dyn in ND. cbn [L5.bo_fb] in ND. rewrite B0 in ND. discriminate. }
    cbv iota in OB5, OL5.
    destruct GG as (_ & -> & -> & STM & AHP5). destruct st5 as [z0 z1|cap5 q5]; [contradiction|]. destruct STM as [-> ->].
    rewrite MULMSCR_EQ in AHP5.
    destruct (ctx_after R R5 M M5 model model5 LB3 LB3 cr3 cr3 LK3 LK5 A3 A5 _ o q (8 * (Z.of_nat n + 1)) CTX RP5 HH5 AM5 RT5 IA5 ILK5 AHP5) as (CTX5 & KP5).
    + intros x Hx. exact Hx.
    + exact AOB.
    + exact OW.
    + right. exists cap. split. exact INq. clear - Hcap; lia.
    + exact LBX.
    + intros a Hc Ho X. apply (DW a Hc Ho). clear - X Hcap; lia.
    + apply (NEXT fx5 R5 M5 model5 LK5 A5 CTX5 ILK5 KP5). cbv zeta. split. exact LRW. split. exact WRW. split. exact NLE5. split. exact OB5. exact OL5.
Qed.

Lemma UR1 : U R0 1 = r. Proof. apply (U_of R0 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fin (sec : bool) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit) (LK3 : list fframe) (A3 : list (Z * Z))
      (gd gn : growth) (std stn : L5.bstore) :
  ctx R M model LB3 cr3 LK3 A3 -> SEC = sec ->
  obj_after M od bd (norm_words wd C0 sec) gd std -> obj_after M on bn (norm_words wn C0 sec) gn stn ->
  LB3 = blocks_of gn ++ blocks_of gd ++ LB -> cr3 = adebl L cr (blocks_of gn ++ blocks_of gd) ->
  (match gd with Same => True | Grown A0 cap => afresh L ar LB (FF ++ LK3) M A0 (8 * cap) end) ->
  (match gn with Same => True | Grown A0 cap => afresh L ar (blocks_of gd ++ LB) (FF ++ LK3) M A0 (8 * cap) end) ->
  (match gd with Same => True | Grown _ _ => (3 <= length D)%nat \/ SEC = true end) ->
  (match gn with Same => True | Grown _ _ => (3 <= length Dn)%nat \/ SEC = true end) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R (if sec then 0x93438 else 0x93440) M model) K.
Proof.
  intros CTX HSEC OAd OAn ELB ECR FRd FRn GNd GNn.
  destruct CTX as (HH & AM & RT & IA & ILK & RG & SV & STK3 & PX & SZd & SZn & SZp & EK & DK).
  pose proof (stk_vis LB3 FF LK3 cr3 A3 M model sp HH STK3) as ((SPR & A16) & W80 & XF & XB).
  pose proof (L5ASHROK.statics_vis L ar C HI LY HIok LB3 FF LK3 cr3 A3 M model HH) as (IMGC & CSB & CUAR).
  destruct RG as (g2 & g8 & g9 & g18 & g19 & g21 & g22 & g23 & g24 & gK).
  destruct SV as (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24).
  set (H := ahid A3 model) in *. set (MV := mrestrict H M) in *.
  assert (RUN : exists fx3 R3 M3v, mem_grows MV M3v /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M3v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
            /\ msteps RSEGS (st fx R (if sec then 0x93438 else 0x93440) MV) (st fx3 R3 0x93470 M3v)
            /\ (forall x, In x [3; 4; 25; 26; 27]%nat -> getr R3 (reg x) = getr R (reg x))
            /\ getr R3 (reg 1) = Z_to_bv 64 (U R0 1) /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 (U R0 8) /\ getr R3 (reg 9) = Z_to_bv 64 (U R0 9)
            /\ getr R3 (reg 10) = Z_to_bv 64 (if sec then 1 else 0) /\ getr R3 (reg 18) = Z_to_bv 64 (U R0 18) /\ getr R3 (reg 19) = Z_to_bv 64 (U R0 19)
            /\ getr R3 (reg 20) = Z_to_bv 64 (U R0 20) /\ getr R3 (reg 21) = Z_to_bv 64 (U R0 21) /\ getr R3 (reg 22) = Z_to_bv 64 (U R0 22)
            /\ getr R3 (reg 23) = Z_to_bv 64 (U R0 23) /\ getr R3 (reg 24) = Z_to_bv 64 (U R0 24)).
  { destruct sec.
    - pose proof (vnzH_conc fx R MV (fun j => match j with 2%nat => sp | 42%nat => U R 1 | 48%nat => U R0 1 | 49%nat => U R0 8 | 50%nat => U R0 9 | 51%nat => U R0 18 | 52%nat => U R0 19
                    | 53%nat => U R0 20 | 54%nat => U R0 21 | 55%nat => U R0 22 | 56%nat => U R0 23 | 57%nat => U R0 24 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XF; [clear; lia | clear; lia | sc])]).
      destruct P as (fx3 & R3 & M3v & MG3 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24)).
      exists fx3, R3, M3v. split. exact MG3. split. exact eFZ. split. exact eMS.
      split. { intros x Hx. apply eKS. revert Hx; apply (L5K.incl_b _ KS_vnzH); vm_compute; reflexivity. }
      repeat split; assumption.
    - pose proof (vnzK_conc fx R MV (fun j => match j with 2%nat => sp | 42%nat => U R 1 | 48%nat => U R0 1 | 49%nat => U R0 8 | 50%nat => U R0 9 | 51%nat => U R0 18 | 52%nat => U R0 19
                    | 53%nat => U R0 20 | 54%nat => U R0 21 | 55%nat => U R0 22 | 56%nat => U R0 23 | 57%nat => U R0 24 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XF; [clear; lia | clear; lia | sc])]).
      destruct P as (fx3 & R3 & M3v & MG3 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24)).
      exists fx3, R3, M3v. split. exact MG3. split. exact eFZ. split. exact eMS.
      split. { intros x Hx. apply eKS. revert Hx; apply (L5K.incl_b _ KS_vnzK); vm_compute; reflexivity. }
      repeat split; assumption. }
  destruct RUN as (fx3 & R3 & M3v & MG3 & eFZ & eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24).
  rewrite UR1 in eR1.
  pose proof (ret_to fx3 R3 M3v 0x93470 As0_code_93368_94368.W_93470 r As0_code_93368_94368.F_93470 eq_refl As0_code_93368_94368.D_93470 eR1 (proj1 RA) (proj2 RA)) as RETs.
  apply (apiece_ro L ar C HI LY HIok LB3 FF LK3 cr3 A3 M model fx fx3 R _ R3 r M3v K HH AM (msteps_trans _ _ _ _ eMS RETs) MG3).
  { exact eFZ. }
  intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3.
  pose proof (mem_eq_of_agree M M3 FRM3) as EM. subst M3.
  apply (KONT fx3 R3 M model3 C0 gd gn LB3 cr3 LK3 A3).
  - unfold norm_postA. cbv zeta. fold nd. fold w0. fold C0. fold D. fold SEC. rewrite HSEC.
    split.
    { apply preserved_by_index. intros j Hj. cbn in Hj.
      assert (CH : forall j', In j' [3; 4; 25; 26; 27]%nat -> getr R3 (reg j') = getr R0 (reg j')). { intros j' Hj1. rewrite (eKS j' Hj1). apply gK. exact Hj1. }
      destruct Hj as [<-|Hj]. { rewrite eR2. rewrite <- r2, G2. reflexivity. }
      destruct Hj as [<-|Hj]. { apply CH; inl. }
      destruct Hj as [<-|Hj]. { apply CH; inl. }
      destruct Hj as [<-|Hj]. { rewrite eR8. symmetry. apply U_to. }
      destruct Hj as [<-|Hj]. { rewrite eR9. symmetry. apply U_to. }
      destruct Hj as [<-|Hj]. { rewrite eR18. symmetry. apply U_to. }
      destruct Hj as [<-|Hj]. { rewrite eR19. symmetry. apply U_to. }
      destruct Hj as [<-|Hj]. { rewrite eR20. symmetry. apply U_to. }
      destruct Hj as [<-|Hj]. { rewrite eR21. symmetry. apply U_to. }
      destruct Hj as [<-|Hj]. { rewrite eR22. symmetry. apply U_to. }
      destruct Hj as [<-|Hj]. { rewrite eR23. symmetry. apply U_to. }
      destruct Hj as [<-|Hj]. { rewrite eR24. symmetry. apply U_to. }
      destruct Hj as [<-|Hj]. { apply CH; inl. }
      destruct Hj as [<-|Hj]. { apply CH; inl. }
      destruct Hj as [<-|Hj]. { apply CH; inl. }
      destruct Hj. }
    split. reflexivity. split. { pose proof C0_rng as X. clear - X; lia. } split. { pose proof C0_rng as X. subst w0. clear - X; lia. }
    split. { rewrite r10. exact eR10. }
    split. exact PX.
    split. { exists std, stn. split. exact OAd. exact OAn. }
    split. exact ELB. split. exact ECR. split. exact FRd. split. exact FRn.
    split. { apply ahpres_of. exact EK. eapply astk_defined. exact STK3. clear; lia. clear; lia. exact DK. }
    split. { destruct gd. exact I. rewrite <- HSEC. exact GNd. } { destruct gn. exact I. rewrite <- HSEC. exact GNn. }
  - eapply L5LZ.model_rt_trans. exact RT. exact RT3.
  - exact IA.
  - exact AM3.
  - exact ILK.
  - exact HH3.
Qed.

(* [comment removed for export] *)
Lemma ctx_ro (R R1 : bvmap 5 word) (M : word -> option byte) (model model1 : Model) LB3 cr3 LK3 A3 :
  ctx R M model LB3 cr3 LK3 A3 -> (forall k, In k [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg k) = getr R (reg k)) ->
  ri_inv HI LB3 FF LK3 cr3 A3 M (vml_of model1) -> amodel_ok A3 model1 -> model_rt model model1 -> ctx R1 M model1 LB3 cr3 LK3 A3.
Proof.
  intros (HH & AM & RT & IA & ILK & RG & REST) KS HH1 AM1 RT1.
  split. exact HH1. split. exact AM1. split. { eapply L5LZ.model_rt_trans. exact RT. exact RT1. } split. exact IA. split. exact ILK.
  split. 2: exact REST.
  destruct RG as (g2 & g8 & g9 & g18 & g19 & g21 & g22 & g23 & g24 & gK). unfold regsN.
  repeat split; try (rewrite KS by inl; assumption).
  intros k Hk. rewrite KS. apply gK. exact Hk. revert Hk; apply (L5K.incl_b _ _); vm_compute; reflexivity.
Qed.

Lemma blocks_in3 gd gn LB3 A0 c0 : LB3 = blocks_of gn ++ blocks_of gd ++ LB -> (gd = Grown A0 c0 \/ gn = Grown A0 c0) -> In (A0, 8 * c0) LB3.
Proof. intros -> [->| ->]; cbn [blocks_of]; rewrite ?in_app_iff; cbn [In]; tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage4 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit) (LK3 : list fframe) (A3 : list (Z * Z))
      (gd gn : growth) (capd qd capn qn : Z) :
  ctx R M model LB3 cr3 LK3 A3 -> SEC = true ->
  obj_after M od bd (norm_words wd C0 true) gd (L5.BDyn capd qd) -> In (qd, 8 * capd) LB3 ->
  obj_after M on bn Dn gn (L5.BDyn capn qn) -> In (qn, 8 * capn) LB3 -> Z.of_nat (rlen Dn) + 1 <= capn ->
  (qd + 8 * capd <= qn \/ qn + 8 * capn <= qd) ->
  (forall a, aclient L ar LB FF sp NORM_SCR a -> L5.outside W a -> ~ (qn <= a < qn + 8 * capn)) ->
  LB3 = blocks_of gn ++ blocks_of gd ++ LB -> cr3 = adebl L cr (blocks_of gn ++ blocks_of gd) ->
  (match gd with Same => True | Grown A0 cap => afresh L ar LB (FF ++ LK3) M A0 (8 * cap) end) ->
  (match gn with Same => True | Grown A0 cap => afresh L ar (blocks_of gd ++ LB) (FF ++ LK3) M A0 (8 * cap) end) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R 0x9342c M model) K.
Proof.
  intros CTX HSEC OAd INd OAn INn CAPn APQ DWn ELB ECR FRd FRn.
  pose proof CTX as (HH & AM & RT & IA & ILK & RG & SV & STK3 & PX & SZd & SZn & SZp & EK & DK).
  pose proof sp_rng as (SPR & SLO & SHI & SPT).
  pose proof (stk_vis LB3 FF LK3 cr3 A3 M model sp HH STK3) as ((_ & A16) & W80 & XF & XB).
  pose proof (L5ASHROK.statics_vis L ar C HI LY HIok LB3 FF LK3 cr3 A3 M model HH) as (IMGC & CSB & CUAR).
  pose proof (obj_vis LB3 FF LK3 cr3 A3 M model od sp HH AOd SZd ltac:(clear - SLO; lia) SPT) as ((ODR & ODA & _) & _).
  pose proof (obj_vis LB3 FF LK3 cr3 A3 M model on sp HH AOn SZn ltac:(clear - SLO; lia) SPT) as ((ONR & ONA & _) & _).
  pose proof (px_vis LB3 FF LK3 cr3 A3 M model px sp HH STK3 P4 Spx (px_def M DK) Hpx2 SZp) as ((PXR & _) & _).
  assert (Hnd2 : (2 <= nd)%nat). { unfold SEC, second in HSEC. apply andb_prop in HSEC. destruct HSEC as [X _]. apply Nat.leb_le in X. exact X. }
  pose proof (Dn_rlen_pos Hnd2) as RPn. pose proof rlen_Dn_le as RLn. pose proof Dn_ok as DOK. pose proof Dn_len as DLEN.
  assert (HVN : 0 <= Z.of_nat nd <= 290) by (clear - Hnd; subst nd; Lia.lia).
  destruct RG as (g2 & g8 & g9 & g18 & g19 & g21 & g22 & g23 & g24 & gK).
  set (H := ahid A3 model) in *. set (MV := mrestrict H M) in *.
  (* [comment removed for export] *)
  pose proof (vnzG_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => od | 34%nat => on | 35%nat => Z.of_nat nd | 38%nat => px | 42%nat => U R 1 | 44%nat => U R 20 | _ => 0 end)) as P.
  cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx1 & R1 & M1v & MG1 & eFR & eFZ & (eMS & eKS & eR1 & eR10 & eR11)).
  apply (apiece_ro L ar C HI LY HIok LB3 FF LK3 cr3 A3 M model fx fx1 R _ R1 MULM M1v K HH AM eMS MG1 eFZ).
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1.
  pose proof (mem_eq_of_agree M M1 FRM1) as EM. subst M1.
  assert (CTX1 : ctx R1 M model1 LB3 cr3 LK3 A3).
  { apply (ctx_ro R R1 M model model1 LB3 cr3 LK3 A3 CTX). 2: exact HH1. 2: exact AM1. 2: exact RT1.
    intros k Hk. apply eKS. revert Hk; apply (L5K.incl_b _ KS_vnzG); vm_compute; reflexivity. }
  (* [comment removed for export] *)
  unfold obj_after in OAn. cbv zeta in OAn. destruct OAn as (WOn & NLEn & OBn2 & OLn2 & CAPm & GMn).
  replace (Nat.eqb (rlen Dn) 0) with false in OBn2, OLn2 by (symmetry; apply Nat.eqb_neq; clear - RPn; Lia.lia).
  set (fbn := match gn with Same => L5.bo_fb bn | Grown _ _ => Z.lor (L5.bo_fb bn) 1 end) in *.
  pose proof OBn2 as (_ & _ & _ & _ & _ & _ & _ & Ccapn & Qn8 & QnLO & QnHI & _). cbn [L5.bo_st] in Ccapn, Qn8, QnLO, QnHI.
  apply (mulm_step on fx1 R1 M model1 LB3 cr3 LK3 A3 0x93438 fbn (rlen Dn) capn qn (firstn (rlen Dn) Dn) CTX1 eR10 eR11 eR1).
  - split. clear; lia. reflexivity.
  - exact AOn.
  - unfold W, norm_W. right; left; reflexivity.
  - exact SZn.
  - exact OBn2.
  - apply (obj_limbs_prefix M fbn (length Dn)). exact OLn2. exact NLEn. exact I.
  - exact INn.
  - split. exact RPn. rewrite DLEN in NLEn. clear - RLn Hnn. subst nn. Lia.lia.
  - exact CAPn.
  - exists (blocks_of gn ++ blocks_of gd). rewrite ELB. rewrite app_assoc. reflexivity.
  - exact DWn.
  - (* [comment removed for export] *)
    intros fx5 R5 M5 model5 LK5 A5 CTX5 ILK5 KP5 POST. cbv zeta in POST. destruct POST as (LRW & WRW & NLE5 & OB5 & OL5).
    set (Fn := mulw_words (firstn (rlen Dn) Dn) MAXW) in *.
    apply (fin true fx5 R5 M5 model5 LB3 cr3 LK5 A5 gd gn (L5.BDyn capd qd) (L5.BDyn capn qn) CTX5 HSEC).
    + (* [comment removed for export] *)
      unfold obj_after in OAd |- *. cbv zeta in OAd |- *. destruct OAd as (WOd & NLEd & OBd2 & OLd2 & CAPmd & GMd).
      pose proof OBd2 as (_ & _ & _ & _ & _ & _ & _ & Ccapd & Qd8 & QdLO & QdHI & _). cbn [L5.bo_st] in Ccapd, Qd8, QdLO, QdHI.
      split. exact WOd. split. exact NLEd.
      split. { apply (big_at_kept LB3 FF M M5 sp on qn (8 * (Z.of_nat (rlen Dn) + 1)) od _ KP5 AOd). clear - APdn; lia. clear - ODR; lia. clear - ODR; lia. exact OBd2. }
      split. { apply (limbs_kept LB3 FF M M5 sp on qn (8 * (Z.of_nat (rlen Dn) + 1)) _ _ _ _ KP5). 2: exact OLd2.
               split. exact INd. split. clear - APQ CAPn; lia. split. exact CAPmd. split. clear - QdLO; lia. clear - QdHI; lia. }
      split. exact CAPmd. exact GMd.
    + (* [comment removed for export] *)
      unfold obj_after, norm_words. cbv zeta. fold Dn. fold Fn. rewrite LRW. fold fbn.
      split. exact WRW. split. exact NLE5. split. exact OB5. split. exact OL5. split. clear - CAPn; Lia.lia. exact GMn.
    + exact ELB.
    + exact ECR.
    + destruct gd as [|Ad cd]. exact I.
      apply (afresh_kept LB3 FF M M5 sp on qn (8 * (Z.of_nat (rlen Dn) + 1)) LB (FF ++ LK3) (FF ++ LK5) Ad cd KP5).
      apply (blocks_in3 (Grown Ad cd) gn LB3 Ad cd ELB). left; reflexivity.
      intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]. left; exact Hx. right; apply ILK5; exact Hx. exact FRd.
    + destruct gn as [|An cn]. exact I.
      apply (afresh_kept LB3 FF M M5 sp on qn (8 * (Z.of_nat (rlen Dn) + 1)) (blocks_of gd ++ LB) (FF ++ LK3) (FF ++ LK5) An cn KP5).
      apply (blocks_in3 gd (Grown An cn) LB3 An cn ELB). right; reflexivity.
      intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]. left; exact Hx. right; apply ILK5; exact Hx. exact FRn.
    + destruct gd. exact I. right. exact HSEC.
    + destruct gn. exact I. right. exact HSEC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage3 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit) (LK3 : list fframe) (A3 : list (Z * Z))
      (gd gn : growth) (capd qd capn qn : Z) :
  ctx R M model LB3 cr3 LK3 A3 -> SEC = true ->
  obj_after M od bd D gd (L5.BDyn capd qd) -> In (qd, 8 * capd) LB3 -> Z.of_nat (rlen D) + 1 <= capd ->
  obj_after M on bn Dn gn (L5.BDyn capn qn) -> In (qn, 8 * capn) LB3 -> Z.of_nat (rlen Dn) + 1 <= capn ->
  (qd + 8 * capd <= qn \/ qn + 8 * capn <= qd) ->
  (forall a, aclient L ar LB FF sp NORM_SCR a -> L5.outside W a -> ~ (qd <= a < qd + 8 * capd)) ->
  (forall a, aclient L ar LB FF sp NORM_SCR a -> L5.outside W a -> ~ (qn <= a < qn + 8 * capn)) ->
  LB3 = blocks_of gn ++ blocks_of gd ++ LB -> cr3 = adebl L cr (blocks_of gn ++ blocks_of gd) ->
  (match gd with Same => True | Grown A0 cap => afresh L ar LB (FF ++ LK3) M A0 (8 * cap) end) ->
  (match gn with Same => True | Grown A0 cap => afresh L ar (blocks_of gd ++ LB) (FF ++ LK3) M A0 (8 * cap) end) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R 0x93420 M model) K.
Proof.
  intros CTX HSEC OAd INd CAPd OAn INn CAPn APQ DWd DWn ELB ECR FRd FRn.
  pose proof CTX as (HH & AM & RT & IA & ILK & RG & SV & STK3 & PX & SZd & SZn & SZp & EK & DK).
  pose proof sp_rng as (SPR & SLO & SHI & SPT).
  pose proof (stk_vis LB3 FF LK3 cr3 A3 M model sp HH STK3) as ((_ & A16) & W80 & XF & XB).
  pose proof (L5ASHROK.statics_vis L ar C HI LY HIok LB3 FF LK3 cr3 A3 M model HH) as (IMGC & CSB & CUAR).
  pose proof (obj_vis LB3 FF LK3 cr3 A3 M model od sp HH AOd SZd ltac:(clear - SLO; lia) SPT) as ((ODR & ODA & _) & _).
  pose proof (obj_vis LB3 FF LK3 cr3 A3 M model on sp HH AOn SZn ltac:(clear - SLO; lia) SPT) as ((ONR & ONA & _) & _).
  pose proof (px_vis LB3 FF LK3 cr3 A3 M model px sp HH STK3 P4 Spx (px_def M DK) Hpx2 SZp) as ((PXR & _) & _).
  pose proof D_rlen_pos as RPd. pose proof rlen_D_le as RLd. pose proof D_ok as DOK. pose proof D_len as DLEN.
  assert (HVN : 0 <= Z.of_nat nd <= 290) by (clear - Hnd; subst nd; Lia.lia).
  destruct RG as (g2 & g8 & g9 & g18 & g19 & g21 & g22 & g23 & g24 & gK).
  set (H := ahid A3 model) in *. set (MV := mrestrict H M) in *.
  pose proof (vnzF_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => od | 34%nat => on | 35%nat => Z.of_nat nd | 38%nat => px | 42%nat => U R 1 | 44%nat => U R 20 | _ => 0 end)) as P.
  cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx1 & R1 & M1v & MG1 & eFR & eFZ & (eMS & eKS & eR1 & eR10 & eR11)).
  apply (apiece_ro L ar C HI LY HIok LB3 FF LK3 cr3 A3 M model fx fx1 R _ R1 MULM M1v K HH AM eMS MG1 eFZ).
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1.
  pose proof (mem_eq_of_agree M M1 FRM1) as EM. subst M1.
  assert (CTX1 : ctx R1 M model1 LB3 cr3 LK3 A3).
  { apply (ctx_ro R R1 M model model1 LB3 cr3 LK3 A3 CTX). 2: exact HH1. 2: exact AM1. 2: exact RT1.
    intros k Hk. apply eKS. revert Hk; apply (L5K.incl_b _ KS_vnzF); vm_compute; reflexivity. }
  unfold obj_after in OAd. cbv zeta in OAd. destruct OAd as (WOd & NLEd & OBd2 & OLd2 & CAPmd & GMd).
  replace (Nat.eqb (rlen D) 0) with false in OBd2, OLd2 by (symmetry; apply Nat.eqb_neq; clear - RPd; Lia.lia).
  set (fbd := match gd with Same => L5.bo_fb bd | Grown _ _ => Z.lor (L5.bo_fb bd) 1 end) in *.
  apply (mulm_step od fx1 R1 M model1 LB3 cr3 LK3 A3 0x9342c fbd (rlen D) capd qd (firstn (rlen D) D) CTX1 eR10 eR11 eR1).
  - split. clear; lia. reflexivity.
  - exact AOd.
  - unfold W, norm_W. left; reflexivity.
  - exact SZd.
  - exact OBd2.
  - apply (obj_limbs_prefix M fbd (length D)). exact OLd2. exact NLEd. exact I.
  - exact INd.
  - split. exact RPd. clear - RLd Hnd. subst nd. Lia.lia.
  - exact CAPd.
  - exists (blocks_of gn ++ blocks_of gd). rewrite ELB. rewrite app_assoc. reflexivity.
  - exact DWd.
  - (* [comment removed for export] *)
    intros fx5 R5 M5 model5 LK5 A5 CTX5 ILK5 KP5 POST. cbv zeta in POST. destruct POST as (LRW & WRW & NLE5 & OB5 & OL5).
    set (Fd := mulw_words (firstn (rlen D) D) MAXW) in *.
    apply (stage4 fx5 R5 M5 model5 LB3 cr3 LK5 A5 gd gn capd qd capn qn CTX5 HSEC).
    + unfold obj_after, norm_words. cbv zeta. fold D. fold Fd. rewrite LRW. fold fbd.
      split. exact WRW. split. exact NLE5. split. exact OB5. split. exact OL5. split. clear - CAPd; Lia.lia. exact GMd.
    + exact INd.
    + (* [comment removed for export] *)
      unfold obj_after in OAn |- *. cbv zeta in OAn |- *. destruct OAn as (WOn & NLEn & OBn2 & OLn2 & CAPmn & GMn).
      pose proof OBn2 as (_ & _ & _ & _ & _ & _ & _ & Ccapn & Qn8 & QnLO & QnHI & _). cbn [L5.bo_st] in Ccapn, Qn8, QnLO, QnHI.
      split. exact WOn. split. exact NLEn.
      split. { apply (big_at_kept LB3 FF M M5 sp od qd (8 * (Z.of_nat (rlen D) + 1)) on _ KP5 AOn). clear - APdn; lia. clear - ONR; lia. clear - ONR; lia. exact OBn2. }
      split. { apply (limbs_kept LB3 FF M M5 sp od qd (8 * (Z.of_nat (rlen D) + 1)) _ _ _ _ KP5). 2: exact OLn2.
               split. exact INn. split. clear - APQ CAPd; lia. split. exact CAPmn. split. clear - QnLO; lia. clear - QnHI; lia. }
      split. exact CAPmn. exact GMn.
    + exact INn.
    + exact CAPn.
    + exact APQ.
    + exact DWn.
    + exact ELB.
    + exact ECR.
    + destruct gd as [|Ad cd]. exact I.
      apply (afresh_kept LB3 FF M M5 sp od qd (8 * (Z.of_nat (rlen D) + 1)) LB (FF ++ LK3) (FF ++ LK5) Ad cd KP5).
      apply (blocks_in3 (Grown Ad cd) gn LB3 Ad cd ELB). left; reflexivity.
      intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]. left; exact Hx. right; apply ILK5; exact Hx. exact FRd.
    + destruct gn as [|An cn]. exact I.
      apply (afresh_kept LB3 FF M M5 sp od qd (8 * (Z.of_nat (rlen D) + 1)) (blocks_of gd ++ LB) (FF ++ LK3) (FF ++ LK5) An cn KP5).
      apply (blocks_in3 gd (Grown An cn) LB3 An cn ELB). right; reflexivity.
      intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]. left; exact Hx. right; apply ILK5; exact Hx. exact FRn.
Qed.

(* [comment removed for export] *)
Definition loc (st' : L5.bstore) (LB3 : list (Z * Z)) : Prop :=
  match st' with
  | L5.BDyn cap q => In (q, 8 * cap) LB3 /\ (forall a, aclient L ar LB FF sp NORM_SCR a -> L5.outside W a -> ~ (q <= a < q + 8 * cap))
  | L5.BInl _ _ => True
  end.

Lemma bgeu_Z (x y : Z) : 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> branch_taken BC_GEU (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof. intros Hx Hy. unfold branch_taken, bv_ltu. rewrite !BG.unsigned_lit by lia. reflexivity. Qed.
Lemma br_930c8 fx R M : msteps RSEGS (st fx R 0x9341c M) (st fx R (if branch_taken BC_GEU (getr R (reg 10)) (getr R (reg 11)) then 0x93440 else 0x93420) M).
Proof.
  rewrite <- r10, <- r11.
  apply (L5ACMP.br_site fx R M 0x9341c 0x93440 (0x9341c%bv : word) _ BC_GEU 10 11 _ ltac:(apply bv_eq; vm_compute; reflexivity) As0_code_93368_94368.F_9341c eq_refl As0_code_93368_94368.D_9341c);
    apply bv_eq; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shl_step (o : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit) (LK3 : list fframe) (A3 : list (Z * Z))
      (rr : Z) (b : L5.bigobj) (ws : list Z) :
  ctx R M model LB3 cr3 LK3 A3 ->
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 C0 -> getr R (reg 1) = Z_to_bv 64 rr -> L5.ra_ok rr ->
  aobj FF o 32 -> In (o, 32) W -> shadow_zero M o 4 ->
  L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> (1 <= L5.bo_len b <= 290)%nat ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB3 /\ Z.of_nat (L5.bo_len b) + 1 <= cap
                                             /\ (forall a, aclient L ar LB FF sp NORM_SCR a -> L5.outside W a -> ~ (q <= a < q + 8 * cap))) ->
  (1 <= C0 -> L5.bo_dyn b = false -> L5.bo_len b = 2%nat -> acredit_ok L cr3 64) ->
  (exists BX, LB3 = BX ++ LB) ->
  (forall (fx5 : FPState) (R5 : bvmap 5 word) (M5 : word -> option byte) (model5 : Model) (LK5 : list fframe) (A5 : list (Z * Z)) (g : growth) (st5 : L5.bstore)
          (LB5 : list (Z * Z)) (cr5 : credit) (d n : Z),
      ctx R5 M5 model5 LB5 cr5 LK5 A5 -> incl LK5 LK3 -> (forall k, In k cs_all -> getr R5 (reg k) = getr R (reg k)) ->
      keptP LB3 FF M M5 sp o d n -> (d = o + 16 /\ n <= 16 \/ exists c, L5.bo_st b = L5.BDyn c d /\ n <= 8 * c) ->
      obj_after M5 o b (shl_result ws C0) g st5 -> loc st5 LB5 ->
      LB5 = blocks_of g ++ LB3 -> cr5 = adebl L cr3 (blocks_of g) ->
      (match g with Same => True | Grown A0 cap => afresh L ar LB3 (FF ++ LK5) M5 A0 (8 * cap) /\ L5.bo_len b = 2%nat /\ 1 <= C0 end) ->
      srealizes RSEGS SCFG (cfg (fx:=fx5) R5 rr M5 model5) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R SHL M model) K.
Proof.
  intros CTX G10 G11' G1' RA' AOB OW SZo OB OL Hlen BLK CRD LBX NEXT.
  pose proof CTX as (HH & AM & RT & IA & ILK & RG & SV & STK3 & PX & SZd & SZn & SZp & EK & DK).
  destruct RG as (g2 & g8 & g9 & g18 & g19 & g21 & g22 & g23 & g24 & gK).
  pose proof sp_rng as (SPR & SLO & SHI & SPT). pose proof C0_rng as (C0R & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF3.
  assert (ND3 : NoDup (map ff_addr (FF ++ LK3))). { clear - WF3. decompose [and] WF3. assumption. } clear WF3.
  apply (SHLok fx R M model K LB3 FF LK3 cr3 A3 o (sp - 80) rr C0 b ws HH AM HK0).
  - rewrite r10. exact G10.
  - rewrite r11. exact G11'.
  - exact C0R.
  - clear - Hlen; Lia.lia.
  - clear - Hlen; Lia.lia.
  - intros DY. unfold L5.bo_cap. destruct (L5.bo_st b) as [v0 v1|cap q] eqn:E.
    + exfalso. destruct OB as (_ & _ & _ & OST). rewrite E in OST. destruct OST as (B0 & _). unfold L5.bo_dyn in DY. rewrite B0 in DY. discriminate.
    + exact (proj1 (proj2 (BLK cap q eq_refl))).
  - exact CRD.
  - rewrite r1. exact G1'.
  - exact RA'.
  - rewrite r2. exact g2.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - A32. lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite r4, (gK 4%nat ltac:(cbn; tauto)), <- r4. exact G4.
  - rewrite SHLSCR_EQ. eapply astk_sub. exact STK3. apply mem_grows_refl. clear; lia. clear; lia. rewrite SCR_EQ; clear; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - A32. lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (ffr_lk FF LK LK3 4 ROOM ILK ND3).
  - eapply ffrs_le. exact RS. clear; lia.
  - exact OB.
  - exact OL.
  - exact AOB.
  - exact SZo.
  - intros cap' q' E. exact (proj1 (BLK cap' q' E)).
  - intros fx5 R5 M5 model5 g5 LB5 cr5 LK5 A5 POST RT5 IA5 AM5 ILK5 HH5.
    unfold shl_postA_at in POST. cbv zeta in POST.
    destruct POST as (RP5 & B10 & WRW & NLE5 & st5 & OB5 & OL5 & GG).
    set (rw := shl_result ws C0) in *.
    assert (LRW : (length rw <= Datatypes.S (L5.bo_len b))%nat /\ (C0 = 0 -> length rw = L5.bo_len b) /\ (1 <= C0 -> length rw = Datatypes.S (L5.bo_len b))).
    { subst rw. unfold shl_result. pose proof (proj1 OL) as LW. destruct (Z.eqb_spec C0 0) as [E|E].
      - rewrite LW. split. Lia.lia. split. reflexivity. intros X. exfalso. clear - X E. lia.
      - rewrite shl_words_length, LW. split. Lia.lia. split. intros X; contradiction. reflexivity. }
    destruct LRW as (LRW1 & LRW0 & LRWp).
    destruct g5 as [|A5' c5].
    + (* [comment removed for export] *)
      destruct GG as (DYM & -> & -> & STM & AHP5). rewrite SHLSCR_EQ in AHP5.
      assert (DLOC : (L5.bo_data o b = o + 16 /\ 8 * Z.of_nat (length rw) <= 16) \/ (exists c, L5.bo_st b = L5.BDyn c (L5.bo_data o b) /\ 8 * Z.of_nat (length rw) <= 8 * c)).
      { unfold L5.bo_data. destruct (L5.bo_st b) as [v0 v1|cap q] eqn:E.
        - left. split. reflexivity. destruct DYM as [DY|M2]. 2:{ clear - M2; Lia.lia. }
          exfalso. destruct OB as (_ & _ & _ & OST). rewrite E in OST. destruct OST as (B0 & _). unfold L5.bo_dyn in DY. rewrite B0 in DY. discriminate.
        - right. exists cap. split. reflexivity. pose proof (proj1 (proj2 (BLK cap q eq_refl))) as X. clear - X LRW1. Lia.lia. }
      destruct (ctx_after R R5 M M5 model model5 LB3 LB3 cr3 cr3 LK3 LK5 A3 A5 _ o (L5.bo_data o b) (8 * Z.of_nat (length rw)) CTX RP5 HH5 AM5 RT5 IA5 ILK5 AHP5) as (CTX5 & KP5).
      * intros x Hx. exact Hx.
      * exact AOB.
      * exact OW.
      * destruct DLOC as [DL|(c & E & Hc)]. left; exact DL. right. exists c. split. 2: exact Hc. rewrite <- (proj1 (BLK c _ E)) || exact (proj1 (BLK c _ E)).
      * exact LBX.
      * intros a Hc Ho X. destruct DLOC as [(DE & Hn)|(c & E & Hn)].
        -- pose proof (Ho (o, 32) OW) as Y. unfold L5.in_rng in Y. cbn [fst snd] in Y. rewrite DE in X. clear - X Y Hn. lia.
        -- apply (proj2 (proj2 (BLK c _ E)) a Hc Ho). clear - X Hn. lia.
      * apply (NEXT fx5 R5 M5 model5 LK5 A5 Same st5 LB3 cr3 (L5.bo_data o b) (8 * Z.of_nat (length rw)) CTX5 ILK5).
        -- intros k Hk. apply (cs_of_preserved R R5 k RP5 Hk).
        -- exact KP5.
        -- exact DLOC.
        -- unfold obj_after. cbv zeta. fold rw. split. exact WRW. split. exact NLE5. split. exact OB5. split. exact OL5.
           split. { destruct st5 as [z0 z1|cap5 q5]; destruct (L5.bo_st b) as [v0 v1|cap q] eqn:E; try contradiction.
                    - destruct DYM as [DY|M2]. 2: exact M2. exfalso. destruct OB as (_ & _ & _ & OST). rewrite E in OST. destruct OST as (B0 & _). unfold L5.bo_dyn in DY. rewrite B0 in DY. discriminate.
                    - destruct STM as [-> ->]. pose proof (proj1 (proj2 (BLK cap q eq_refl))) as X. clear - X LRW1. Lia.lia. }
           exact STM.
        -- unfold loc. destruct st5 as [z0 z1|cap5 q5]. exact I. destruct (L5.bo_st b) as [v0 v1|cap q] eqn:E; try contradiction. destruct STM as [-> ->].
           split. exact (proj1 (BLK cap q eq_refl)). exact (proj2 (proj2 (BLK cap q eq_refl))).
        -- reflexivity.
        -- reflexivity.
        -- exact I.
    + (* [comment removed for export] *)
      destruct GG as (DYF & L2 & K1 & -> & -> & -> & -> & FRESH & AHP5). rewrite SHLSCR_EQ in AHP5.
      destruct (ctx_after R R5 M M5 model model5 LB3 ((A5', 64) :: LB3) cr3 (adebit L cr3 64) LK3 LK5 A3 A5 _ o (o + 16) 0 CTX RP5 HH5 AM5 RT5 IA5 ILK5 AHP5) as (CTX5 & KP5).
      * intros x Hx rr' [<-|[]]. apply (Hx (o, 32)). left; reflexivity.
      * exact AOB.
      * exact OW.
      * left. split. reflexivity. clear; lia.
      * exact LBX.
      * intros a _ _ X. clear - X. lia.
      * apply (NEXT fx5 R5 M5 model5 LK5 A5 (Grown A5' 8) (L5.BDyn 8 A5') ((A5', 64) :: LB3) (adebit L cr3 64) (o + 16) 0 CTX5 ILK5).
        -- intros k Hk. apply (cs_of_preserved R R5 k RP5 Hk).
        -- exact KP5.
        -- left. split. reflexivity. clear; lia.
        -- unfold obj_after. cbv zeta. fold rw. split. exact WRW. split. exact NLE5. split. exact OB5. split. exact OL5.
           split. { rewrite (LRWp K1), L2. clear; Lia.lia. } split. exact DYF. split; reflexivity.
        -- unfold loc. split. left; reflexivity.
           intros a Hc _ X. destruct FRESH as (BR & BA & FA & _). destruct LBX as (BX & ELB3).
           apply (fresh_block_not_client L ar C HI LY HIok LB FF LK cr A M0 _ sp NORM_SCR A5' 64 a HH0 SPT BR).
           { intros bb Hb. apply BA. rewrite ELB3. apply in_or_app. right. exact Hb. }
           { eapply fframes_apart_incl. exact FA. intros g0 Hg. apply in_or_app. left. exact Hg. }
           exact X. exact Hc.
        -- reflexivity.
        -- reflexivity.
        -- split. exact FRESH. split. exact L2. exact K1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stageE (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit) (LK3 : list fframe) (A3 : list (Z * Z))
      (gd gn : growth) (std stn : L5.bstore) :
  ctx R M model LB3 cr3 LK3 A3 -> getr R (reg 20) = Z_to_bv 64 (Z.of_nat nd) ->
  obj_after M od bd D gd std -> loc std LB3 -> obj_after M on bn Dn gn stn -> loc stn LB3 ->
  (forall cd qd cn qn, std = L5.BDyn cd qd -> stn = L5.BDyn cn qn -> qd + 8 * cd <= qn \/ qn + 8 * cn <= qd) ->
  (SEC = true -> (forall cd qd, std = L5.BDyn cd qd -> Z.of_nat (rlen D) + 1 <= cd) /\ (forall cn qn, stn = L5.BDyn cn qn -> Z.of_nat (rlen Dn) + 1 <= cn)) ->
  LB3 = blocks_of gn ++ blocks_of gd ++ LB -> cr3 = adebl L cr (blocks_of gn ++ blocks_of gd) ->
  (match gd with Same => True | Grown A0 cap => afresh L ar LB (FF ++ LK3) M A0 (8 * cap) end) ->
  (match gn with Same => True | Grown A0 cap => afresh L ar (blocks_of gd ++ LB) (FF ++ LK3) M A0 (8 * cap) end) ->
  (match gd with Same => True | Grown _ _ => (3 <= length D)%nat end) ->
  (match gn with Same => True | Grown _ _ => (3 <= length Dn)%nat end) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R 0x933a8 M model) K.
Proof.
  intros CTX g20 OAd LCd OAn LCn APQ SCAP ELB ECR FRd FRn GWd GWn.
  pose proof CTX as (HH & AM & RT & IA & ILK & RG & SV & STK3 & PX & SZd & SZn & SZp & EK & DK).
  pose proof sp_rng as (SPR & SLO & SHI & SPT).
  pose proof (stk_vis LB3 FF LK3 cr3 A3 M model sp HH STK3) as ((_ & A16) & W80 & XF & XB).
  pose proof (L5ASHROK.statics_vis L ar C HI LY HIok LB3 FF LK3 cr3 A3 M model HH) as (IMGC & CSB & CUAR).
  pose proof (obj_vis LB3 FF LK3 cr3 A3 M model od sp HH AOd SZd ltac:(clear - SLO; lia) SPT) as ((ODR & ODA & ODBIG & ODFR & _) & ODZ & ODW & ODV & XOD & XBD).
  pose proof (obj_vis LB3 FF LK3 cr3 A3 M model on sp HH AOn SZn ltac:(clear - SLO; lia) SPT) as ((ONR & ONA & _) & _).
  pose proof (px_vis LB3 FF LK3 cr3 A3 M model px sp HH STK3 P4 Spx (px_def M DK) Hpx2 SZp) as ((PXR & _) & _).
  pose proof D_rlen_pos as RPd. pose proof rlen_D_le as RLd. pose proof D_ok as DOK. pose proof D_len as DLEN.
  assert (HVN : 0 <= Z.of_nat nd <= 290) by (clear - Hnd; subst nd; Lia.lia).
  assert (FRD : sp - 80 + 80 <= od \/ od + 32 <= sp - 80) by (clear - ODFR; lia).
  destruct RG as (g2 & g8 & g9 & g18 & g19 & g21 & g22 & g23 & g24 & gK).
  set (H := ahid A3 model) in *. set (MV := mrestrict H M) in *.
  pose proof OAd as OAd0. unfold obj_after in OAd. cbv zeta in OAd. destruct OAd as (WOd & NLEd & OBd2 & OLd2 & CAPm & GMd).
  replace (Nat.eqb (rlen D) 0) with false in OBd2, OLd2 by (symmetry; apply Nat.eqb_neq; clear - RPd; Lia.lia).
  set (fbd := match gd with Same => L5.bo_fb bd | Grown _ _ => Z.lor (L5.bo_fb bd) 1 end) in *.
  pose proof OBd2 as (Pd0 & Hfbd & Pd8 & PST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Pd0, Hfbd, Pd8, PST.
  assert (HVF : 0 <= fbd <= 255) by (clear - Hfbd; lia).
  (* [comment removed for export] *)
  assert (RUN : exists (sec : bool) fx1 R1 M1v, SEC = sec /\ mem_grows MV M1v /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
            /\ msteps RSEGS (st fx R 0x933a8 MV) (st fx1 R1 (if sec then 0x93420 else 0x93440) M1v)
            /\ (forall k, In k [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg k) = getr R (reg k))).
  { destruct (Nat.eq_dec nd 1) as [ND1|ND1].
    - (* [comment removed for export] *)
      assert (HSEC : SEC = false). { unfold SEC, second. rewrite ND1. reflexivity. }
      rewrite ND1 in g20, g22, g23. change (Z.of_nat 1) with 1 in g20, g22, g23. change (8 * (1 - 1)) with 0 in g22. change (1 - 1) with 0 in g23.
      exists false. destruct std as [u0 u1|capd qd].
      + destruct PST as (Bd0 & _).
        pose proof (vnzE1i_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => od | 34%nat => on | 36%nat => fbd | 38%nat => px | 42%nat => U R 1 | _ => 0 end)) as P.
        cbn beta iota in P.
        feed P ltac:(first [apply UR | apply U_to | sc | (apply XBD; sc)]).
        destruct P as (fx1 & R1 & M1v & MG1 & eFR & eFZ & (eMS & eKS & _)).
        exists fx1, R1, M1v. split. exact HSEC. split. exact MG1. split. exact eFZ. split. exact eMS.
        intros k Hk. apply eKS. revert Hk; apply (L5K.incl_b _ KS_vnzE1i); vm_compute; reflexivity.
      + destruct PST as (Bd1 & Pd16 & Pd24 & CAPd2 & Ccapd & Qd8 & QdLO & QdHI & _).
        pose proof (vnzE1d_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => od | 34%nat => on | 36%nat => fbd | 37%nat => qd | 38%nat => px | 42%nat => U R 1 | _ => 0 end)) as P.
        cbn beta iota in P.
        assert (HVQ : 0 <= qd < 2 ^ 64) by (clear - Ccapd QdLO QdHI; lia).
        feed P ltac:(first [apply UR | apply U_to | sc | (apply XBD; sc) | (apply XOD; [clear; lia | clear; lia | sc])]).
        destruct P as (fx1 & R1 & M1v & MG1 & eFR & eFZ & (eMS & eKS & _)).
        exists fx1, R1, M1v. split. exact HSEC. split. exact MG1. split. exact eFZ. split. exact eMS.
        intros k Hk. apply eKS. revert Hk; apply (L5K.incl_b _ KS_vnzE1d); vm_compute; reflexivity.
    - (* [comment removed for export] *)
      assert (Hnd2 : (2 <= nd)%nat) by (clear - ND1 Hnd; subst nd; Lia.lia).
      assert (C0pos : C0 <> 0).
      { intros E. pose proof C0_rng as (_ & X). rewrite E in X. pose proof (TOPsm Hnd2) as Y. fold nd in Y. fold w0 in Y. clear - X Y. lia. }
      assert (LD : length D = Datatypes.S nd). { rewrite DLEN. destruct (Z.eqb_spec C0 0) as [E|E]. contradiction. reflexivity. }
      destruct std as [u0 u1|capd qd]. { exfalso. clear - CAPm LD Hnd2. Lia.lia. }
      destruct PST as (Bd1 & Pd16 & Pd24 & CAPd2 & Ccapd & Qd8 & QdLO & QdHI & _). destruct LCd as (INd & _).
      pose proof (L5ASHROK.block_vis L ar C HI LY HIok LB3 FF LK3 cr3 A3 M model qd capd sp HH INd ltac:(clear - Ccapd; lia) ltac:(clear - SLO; lia) SPT)
        as (QR & QD8 & QBIG & QFR & QSHD & QIMG & QW & QZ & QV & XQ). fold H in QV, XQ. fold MV in QW, QZ, XQ.
      pose proof (blk_obj_apart LB3 FF LK3 cr3 A3 M _ qd capd od HH INd AOd) as QO.
      destruct OLd2 as (L1 & L2 & L3). cbn [L5.bo_st L5.bo_len] in L1, L3.
      set (w1 := nth_w D (nd - 1)). set (wz := nth_w D (nd - 2)).
      pose proof (words_ok_nth D (nd - 1) DOK) as Rw1. pose proof (words_ok_nth D (nd - 2) DOK) as Rwz. fold w1 in Rw1. fold wz in Rwz.
      assert (X1 : L5.u64_at RSEGS M (8 * Z.of_nat nd + qd - 8) w1).
      { replace (8 * Z.of_nat nd + qd - 8) with (qd + 8 * Z.of_nat (nd - 1)) by (clear - Hnd2; Lia.lia). subst w1. unfold nth_w. apply L3. rewrite LD. clear - Hnd2; Lia.lia. }
      assert (X0 : L5.u64_at RSEGS M (8 * Z.of_nat nd + qd - 16) wz).
      { replace (8 * Z.of_nat nd + qd - 16) with (qd + 8 * Z.of_nat (nd - 2)) by (clear - Hnd2; Lia.lia). subst wz. unfold nth_w. apply L3. rewrite LD. clear - Hnd2; Lia.lia. }
      assert (CAPLEN : Z.of_nat nd + 1 <= capd). { rewrite LD in CAPm. clear - CAPm. Lia.lia. }
      assert (ALQ : aligned qd 8) by exact QD8. assert (HVQ : 4096 <= qd <= 140737488355328) by (clear - QR Ccapd; lia). assert (HVC : 1 <= capd <= 134217728) by (clear - Ccapd; lia).
      assert (HVQC : 4104 <= qd + 8 * capd <= 140737479966720) by (clear - QR Ccapd; lia).
      assert (FRQ : sp - 80 + 80 <= qd \/ qd + 8 * capd <= sp - 80) by (clear - QFR; lia).
      assert (HVL : 2 <= Z.of_nat nd <= 134217728) by (clear - Hnd2 HVN; Lia.lia).
      assert (HVCL : 0 <= -1 * Z.of_nat nd + capd <= 134217728) by (clear - CAPLEN Ccapd HVN; lia).
      assert (HW1 : 0 <= w1 <= 18446744073709551615) by (clear - Rw1; lia). assert (HWZ : 0 <= wz <= 18446744073709551615) by (clear - Rwz; lia).
      pose proof (vnzEd_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => od | 34%nat => on | 35%nat => Z.of_nat nd | 36%nat => fbd | 37%nat => qd | 38%nat => px | 39%nat => capd
                      | 40%nat => w1 | 41%nat => wz | 42%nat => U R 1 | _ => 0 end)) as P.
      cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XBD; sc) | (apply XOD; [clear; lia | clear; lia | sc]) | (apply XQ; [clear - Hnd2; Lia.lia | clear - CAPLEN; lia | sc])]).
      destruct P as (fx1 & R1 & M1v & MG1 & eFR & eFZ & (eMS & eKS & eR10 & eR11 & _)).
      pose proof (br_930c8 fx1 R1 M1v) as BR. rewrite eR10, eR11 in BR. rewrite (bgeu_Z w1 wz Rw1 Rwz) in BR.
      exists (w1 <? wz), fx1, R1, M1v.
      split. { unfold SEC, second. fold w1 wz. rewrite (proj2 (Nat.leb_le 2 nd) Hnd2). reflexivity. }
      split. exact MG1. split. exact eFZ.
      split. { eapply msteps_trans. exact eMS. destruct (w1 <? wz); cbn [negb] in BR; exact BR. }
      intros k Hk. apply eKS. revert Hk; apply (L5K.incl_b _ KS_vnzEd); vm_compute; reflexivity. }
  destruct RUN as (sec & fx1 & R1 & M1v & HSEC & MG1 & eFZ & eMS & eKS).
  apply (apiece_ro L ar C HI LY HIok LB3 FF LK3 cr3 A3 M model fx fx1 R _ R1 _ M1v K HH AM eMS MG1 eFZ).
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1.
  pose proof (mem_eq_of_agree M M1 FRM1) as EM. subst M1.
  assert (CTX1 : ctx R1 M model1 LB3 cr3 LK3 A3) by (apply (ctx_ro R R1 M model model1 LB3 cr3 LK3 A3 CTX eKS HH1 AM1 RT1)).
  destruct sec.
  - (* [comment removed for export] *)
    assert (Hnd2 : (2 <= nd)%nat). { unfold SEC, second in HSEC. apply andb_prop in HSEC. destruct HSEC as [X _]. apply Nat.leb_le in X. exact X. }
    assert (C0pos : C0 <> 0).
    { intros E. pose proof C0_rng as (_ & X). rewrite E in X. pose proof (TOPsm Hnd2) as Y. fold nd in Y. fold w0 in Y. clear - X Y. lia. }
    assert (LD : length D = Datatypes.S nd). { rewrite DLEN. destruct (Z.eqb_spec C0 0) as [E|E]. contradiction. reflexivity. }
    assert (LDn : length Dn = Datatypes.S nn). { rewrite Dn_len. destruct (Z.eqb_spec C0 0) as [E|E]. contradiction. reflexivity. }
    pose proof (proj1 (NN2 Hnd2)) as Hnn2. fold nn in Hnn2.
    destruct std as [u0 u1|capd qd]. { exfalso. clear - CAPm LD Hnd2. Lia.lia. }
    destruct stn as [v0 v1|capn qn]. { exfalso. destruct OAn as (_ & _ & _ & _ & X & _). rewrite LDn in X. clear - X Hnn2. Lia.lia. }
    destruct (SCAP HSEC) as (CAPd & CAPn). destruct LCd as (INd & DWd). destruct LCn as (INn & DWn).
    apply (stage3 fx1 R1 M model1 LB3 cr3 LK3 A3 gd gn capd qd capn qn CTX1 HSEC OAd0 INd (CAPd _ _ eq_refl) OAn INn (CAPn _ _ eq_refl) (APQ _ _ _ _ eq_refl eq_refl) DWd DWn ELB ECR FRd FRn).
  - apply (fin false fx1 R1 M model1 LB3 cr3 LK3 A3 gd gn std stn CTX1 HSEC).
    + exact OAd0.
    + exact OAn.
    + exact ELB.
    + exact ECR.
    + exact FRd.
    + exact FRn.
    + destruct gd. exact I. left. exact GWd.
    + destruct gn. exact I. left. exact GWn.
Qed.

Lemma cost_nonneg : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L. Proof. exact (aly_cost L C LY). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stageD (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit) (LK3 : list fframe) (A3 : list (Z * Z))
      (gd : growth) (std : L5.bstore) :
  ctx R M model LB3 cr3 LK3 A3 -> getr R (reg 20) = Z_to_bv 64 (Z.of_nat nd) ->
  obj_after M od bd D gd std -> loc std LB3 ->
  L5.big_at RSEGS M on bn -> L5C.obj_limbs RSEGS M bn wn ->
  (forall cap q, L5.bo_st bn = L5.BDyn cap q -> In (q, 8 * cap) LB3 /\ Z.of_nat nn + 1 <= cap
                                              /\ (forall a, aclient L ar LB FF sp NORM_SCR a -> L5.outside W a -> ~ (q <= a < q + 8 * cap))) ->
  (forall cd qd cn qn, std = L5.BDyn cd qd -> L5.bo_st bn = L5.BDyn cn qn -> qd + 8 * cd <= qn \/ qn + 8 * cn <= qd) ->
  (SEC = true -> forall cd qd, std = L5.BDyn cd qd -> Z.of_nat (rlen D) + 1 <= cd) ->
  LB3 = blocks_of gd ++ LB -> cr3 = adebl L cr (blocks_of gd) ->
  (match gd with Same => True | Grown A0 cap => afresh L ar LB (FF ++ LK3) M A0 (8 * cap) end) ->
  (match gd with Same => True | Grown _ _ => (3 <= length D)%nat end) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R 0x93394 M model) K.
Proof.
  intros CTX g20 OAd LCd OBn' OLn' BLKn3 APQ0 SCAPd ELB3 ECR3 FRd GWd.
  pose proof CTX as (HH & AM & RT & IA & ILK & RG & SV & STK3 & PX & SZd & SZn & SZp & EK & DK).
  pose proof sp_rng as (SPR & SLO & SHI & SPT). pose proof C0_rng as (C0R & _).
  pose proof (stk_vis LB3 FF LK3 cr3 A3 M model sp HH STK3) as ((_ & A16) & W80 & XF & XB).
  pose proof (L5ASHROK.statics_vis L ar C HI LY HIok LB3 FF LK3 cr3 A3 M model HH) as (IMGC & CSB & CUAR).
  pose proof (obj_vis LB3 FF LK3 cr3 A3 M model od sp HH AOd SZd ltac:(clear - SLO; lia) SPT) as ((ODR & ODA & _) & _).
  pose proof (obj_vis LB3 FF LK3 cr3 A3 M model on sp HH AOn SZn ltac:(clear - SLO; lia) SPT) as ((ONR & ONA & _) & _).
  pose proof (px_vis LB3 FF LK3 cr3 A3 M model px sp HH STK3 P4 Spx (px_def M DK) Hpx2 SZp) as ((PXR & PXA & PXBIG) & PXW & PXZ & XPX & _).
  assert (HVN : 0 <= Z.of_nat nd <= 290) by (clear - Hnd; subst nd; Lia.lia).
  assert (FRP : sp - 80 + 80 <= px \/ px + 4 <= sp - 80) by (clear - Spx; lia).
  destruct RG as (g2 & g8 & g9 & g18 & g19 & g21 & g22 & g23 & g24 & gK).
  set (H := ahid A3 model) in *. set (MV := mrestrict H M) in *.
  pose proof (vnzD_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => od | 34%nat => on | 35%nat => Z.of_nat nd | 38%nat => px | 42%nat => U R 1 | 43%nat => C0 | _ => 0 end)) as P.
  cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (apply XPX; sc)]).
  destruct P as (fx1 & R1 & M1v & MG1 & eFR & eFZ & (eMS & eKS & eR1 & eR10 & eR11)).
  apply (apiece_ro L ar C HI LY HIok LB3 FF LK3 cr3 A3 M model fx fx1 R _ R1 SHL M1v K HH AM eMS MG1 eFZ).
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1.
  pose proof (mem_eq_of_agree M M1 FRM1) as EM. subst M1.
  assert (CTX1 : ctx R1 M model1 LB3 cr3 LK3 A3).
  { apply (ctx_ro R R1 M model model1 LB3 cr3 LK3 A3 CTX). 2: exact HH1. 2: exact AM1. 2: exact RT1.
    intros k Hk. apply eKS. revert Hk; apply (L5K.incl_b _ KS_vnzD); vm_compute; reflexivity. }
  assert (g20' : getr R1 (reg 20) = Z_to_bv 64 (Z.of_nat nd)). { rewrite (eKS 20%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact g20. }
  apply (shl_step on fx1 R1 M model1 LB3 cr3 LK3 A3 0x933a8 bn wn CTX1 eR10 eR11 eR1).
  - split. clear; lia. reflexivity.
  - exact AOn.
  - unfold W, norm_W. right; left; reflexivity.
  - exact SZn.
  - exact OBn'.
  - exact OLn'.
  - exact Hnn.
  - exact BLKn3.
  - (* [comment removed for export] *)
    intros K1 DYF L2. pose proof cost_nonneg as (CK & CL & CO). destruct CR as [CR1 CR2]. unfold acredit_ok. rewrite ECR3.
    assert (CNn : cnt bn = 1). { unfold cnt. rewrite DYF. reflexivity. } rewrite CNn in CR1, CR2.
    destruct gd as [|Ad cd]; cbn [blocks_of adebl].
    + assert (X : 0 <= cnt bd) by (unfold cnt; destruct (L5.bo_dyn bd); clear; lia). split. clear - CR1 X CK. nia. clear - CR2 X CL CO. nia.
    + destruct OAd as (_ & _ & _ & _ & _ & (DYd & C8 & _)). assert (CNd : cnt bd = 1). { unfold cnt. rewrite DYd. reflexivity. } rewrite CNd in CR1, CR2.
      subst cd. unfold adebit. cbn [fst snd]. split. clear - CR1. lia. clear - CR2. lia.
  - exists (blocks_of gd). exact ELB3.
  - (* [comment removed for export] *)
    intros fx5 R5 M5 model5 LK5 A5 gn stn LB5 cr5 d n CTX5 ILK5 KR5 KP5 DLOC OAn5 LCn5 ELB5 ECR5 FRn5.
    apply (stageE fx5 R5 M5 model5 LB5 cr5 LK5 A5 gd gn std stn CTX5).
    + rewrite (KR5 20%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact g20'.
    + (* [comment removed for export] *)
      unfold obj_after in OAd |- *. cbv zeta in OAd |- *. destruct OAd as (WOd & NLEd & OBd2 & OLd2 & CAPmd & GMd).
      split. exact WOd. split. exact NLEd.
      split. { apply (big_at_kept LB3 FF M M5 sp on d n od _ KP5 AOd). clear - APdn; lia. clear - ODR; lia. clear - ODR; lia. exact OBd2. }
      split. { apply (limbs_kept LB3 FF M M5 sp on d n _ _ _ _ KP5). 2: exact OLd2.
               destruct std as [u0 u1|capd qd]. exact I. destruct LCd as (INd & _).
               pose proof OBd2 as (_ & _ & _ & _ & _ & _ & _ & Ccapd & Qd8 & QdLO & QdHI & _). cbn [L5.bo_st] in Ccapd, Qd8, QdLO, QdHI.
               split. exact INd. split.
               { destruct DLOC as [(-> & Hn)|(c & E & Hn)].
                 - pose proof (blk_obj_apart LB3 FF LK3 cr3 A3 M _ qd capd on HH INd AOn) as X. clear - X Hn Ccapd. lia.
                 - pose proof (APQ0 capd qd c d eq_refl E) as X. clear - X Hn. lia. }
               split. exact CAPmd. split. clear - QdLO; lia. clear - QdHI; lia. }
      split. exact CAPmd. exact GMd.
    + destruct std as [u0 u1|capd qd]. exact I. destruct LCd as (INd & DWd). split. 2: exact DWd. rewrite ELB5. apply in_or_app. right. exact INd.
    + exact OAn5.
    + exact LCn5.
    + (* [comment removed for export] *)
      intros cd qd cn qn Ed En. subst std stn. destruct LCd as (INd & _).
      destruct gn as [|An cn'].
      * destruct OAn5 as (_ & _ & _ & _ & _ & GMn). destruct (L5.bo_st bn) as [v0 v1|cap q] eqn:E; [contradiction|]. destruct GMn as [-> ->]. exact (APQ0 cd qd cap q eq_refl eq_refl).
      * destruct OAn5 as (_ & _ & _ & _ & _ & (_ & C8 & EST)). inversion EST; subst. destruct FRn5 as ((_ & BA & _) & _).
        pose proof (BA (qd, 8 * cd) INd) as X. cbn [fst snd] in X. clear - X. lia.
    + (* [comment removed for export] *)
      intros HSEC. split. { intros cd qd E. exact (SCAPd HSEC cd qd E). }
      intros cn qn En. subst stn. pose proof rlen_Dn_le as RLn.
      destruct gn as [|An cn'].
      * destruct OAn5 as (_ & _ & _ & _ & _ & GMn). destruct (L5.bo_st bn) as [v0 v1|cap q] eqn:E; [contradiction|]. destruct GMn as [-> ->].
        pose proof (proj2 (SECcap HSEC)) as X. unfold L5.bo_cap in X. rewrite E in X. fold nn in X.
        assert (DYn : L5.bo_dyn bn = true). { destruct OBn' as (_ & _ & _ & OST). rewrite E in OST. exact (proj1 OST). }
        specialize (X DYn). clear - X RLn. Lia.lia.
      * destruct OAn5 as (_ & _ & _ & _ & _ & (_ & C8 & EST)). inversion EST; subst. destruct FRn5 as (_ & L2 & _). fold nn in L2. clear - RLn L2. Lia.lia.
    + rewrite ELB5, ELB3. reflexivity.
    + rewrite ECR5, ECR3. symmetry. apply adebl_app.
    + destruct gd as [|Ad cd]. exact I.
      apply (afresh_kept LB3 FF M M5 sp on d n LB (FF ++ LK3) (FF ++ LK5) Ad cd KP5).
      rewrite ELB3. left. reflexivity.
      intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]. left; exact Hx. right; apply ILK5; exact Hx. exact FRd.
    + destruct gn as [|An cn']. exact I. rewrite <- ELB3. exact (proj1 FRn5).
    + exact GWd.
    + destruct gn as [|An cn']. exact I. destruct FRn5 as (_ & L2 & K1). rewrite Dn_len. fold nn in L2. rewrite L2.
      destruct (Z.eqb_spec C0 0) as [E|E]. exfalso; clear - E K1; lia. clear; Lia.lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma swrap64 (w : Z) : bv_swrap 64 w = (w + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63.
Proof. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64). reflexivity. Qed.
Lemma lts0_neg (w : Z) : 2 ^ 63 <= w < 2 ^ 64 -> branch_taken BC_LT (Z_to_bv 64 w) (Z_to_bv 64 0) = true.
Proof.
  intros Hw. unfold branch_taken, bv_lts. rewrite !Z_to_bv_signed, !swrap64. apply Z.ltb_lt.
  rewrite (Z.mod_small (0 + 2 ^ 63)) by Lia.lia.
  replace ((w + 2 ^ 63) mod 2 ^ 64) with (w + 2 ^ 63 - 2 ^ 64). Lia.lia.
  symmetry. rewrite <- (Z.mod_small (w + 2 ^ 63 - 2 ^ 64) (2 ^ 64)) by Lia.lia.
  replace (w + 2 ^ 63) with ((w + 2 ^ 63 - 2 ^ 64) + 1 * 2 ^ 64) at 1 by Lia.lia. rewrite Z.mod_add by Lia.lia. reflexivity.
Qed.
Lemma lts0_pos (w : Z) : 0 <= w < 2 ^ 63 -> branch_taken BC_LT (Z_to_bv 64 w) (Z_to_bv 64 0) = false.
Proof.
  intros Hw. unfold branch_taken, bv_lts. rewrite !Z_to_bv_signed, !swrap64. apply Z.ltb_ge.
  rewrite (Z.mod_small (0 + 2 ^ 63)) by Lia.lia. rewrite Z.mod_small by Lia.lia. Lia.lia.
Qed.
Lemma rl0 : (0%bv : bv 5) = reg 0. Proof. apply bv_eq. reflexivity. Qed.
Lemma br_93008 fx R M : msteps RSEGS (st fx R 0x9335c M) (st fx R (if branch_taken BC_LT (getr R (reg 10)) (getr R (reg 0)) then 0x93374 else 0x93360) M).
Proof.
  rewrite <- r10, <- rl0.
  apply (L5ACMP.br_site fx R M 0x9335c 0x93374 (0x9335c%bv : word) _ BC_LT 10 0 _ ltac:(apply bv_eq; vm_compute; reflexivity) As0_code_92368_93368.F_9335c eq_refl As0_code_92368_93368.D_9335c);
    apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma entry : srealizes RSEGS SCFG (cfg (fx:=fx0) R0 NORM M0 model0) K.
Proof.
  pose proof sp_rng as (SPR & SLO & SHI & SPT). pose proof C0_rng as (C0R & C0P). pose proof w0_rng as W0R.
  pose proof (stk_vis LB FF LK cr A M0 model0 sp HH0 STK) as ((_ & A16) & W80 & XF & _).
  pose proof (L5ASHROK.statics_vis L ar C HI LY HIok LB FF LK cr A M0 model0 HH0) as (IMGC & CSB & CUAR).
  pose proof (obj_vis LB FF LK cr A M0 model0 od sp HH0 AOd SZd0 ltac:(clear - SLO; lia) SPT) as ((ODR & ODA & ODBIG & ODFR & ODLO) & ODZ & ODW & ODV & XOD & XBD).
  pose proof (obj_vis LB FF LK cr A M0 model0 on sp HH0 AOn SZn0 ltac:(clear - SLO; lia) SPT) as ((ONR & ONA & ONBIG & ONFR & ONLO) & _).
  pose proof (px_vis LB FF LK cr A M0 model0 px sp HH0 STK P4 Spx Hpx Hpx2 SZp0) as ((PXR & PXA & PXBIG) & PXW & PXZ & XPX & PXH).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M0 model0 HH0) as (HOFF & VIS & _).
  assert (HVN : 1 <= Z.of_nat nd <= 290) by (clear - Hnd; subst nd; Lia.lia).
  assert (FRD : sp - 80 + 80 <= od \/ od + 32 <= sp - 80) by (clear - ODFR; lia).
  assert (FRP : sp - 80 + 80 <= px \/ px + 4 <= sp - 80) by (clear - Spx; lia).
  set (H := ahid A model0) in *. set (MV := mrestrict H M0) in *.
  pose proof OBd as (O0 & Hfb & O8 & OST). fold nd in O8.
  pose proof OLd as (Lws & Rws & LAT). fold nd in Lws, LAT.
  assert (HVF : 0 <= L5.bo_fb bd <= 255) by (clear - Hfb; lia).
  (* [comment removed for export] *)
  assert (RUNA : exists fx1 R1 M1v, mem_grows MV M1v
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
            /\ msteps RSEGS (st fx0 R0 NORM MV) (st fx1 R1 0x9335c M1v)
            /\ (forall x, In x [3; 4; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R0 (reg x))
            /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 80) /\ getr R1 (reg 8) = Z_to_bv 64 od /\ getr R1 (reg 9) = Z_to_bv 64 on /\ getr R1 (reg 10) = Z_to_bv 64 w0
            /\ getr R1 (reg 18) = Z_to_bv 64 px /\ getr R1 (reg 19) = Z_to_bv 64 2147450880 /\ getr R1 (reg 20) = Z_to_bv 64 (Z.of_nat nd)
            /\ getr R1 (reg 21) = Z_to_bv 64 (od / 8 + 2147450880) /\ getr R1 (reg 22) = Z_to_bv 64 (8 * Z.of_nat nd - 8) /\ getr R1 (reg 23) = Z_to_bv 64 (Z.of_nat nd - 1)
            /\ L5.u64_at RSEGS M1v (sp - 80) (U R0 24) /\ L5.u64_at RSEGS M1v (sp - 72) (U R0 23) /\ L5.u64_at RSEGS M1v (sp - 64) (U R0 22) /\ L5.u64_at RSEGS M1v (sp - 56) (U R0 21)
            /\ L5.u64_at RSEGS M1v (sp - 48) (U R0 20) /\ L5.u64_at RSEGS M1v (sp - 40) (U R0 19) /\ L5.u64_at RSEGS M1v (sp - 32) (U R0 18) /\ L5.u64_at RSEGS M1v (sp - 24) (U R0 9)
            /\ L5.u64_at RSEGS M1v (sp - 16) (U R0 8) /\ L5.u64_at RSEGS M1v (sp - 8) (U R0 1)).
  { destruct (L5.bo_st bd) as [v0 v1|cap q] eqn:EST.
    - destruct OST as (B0 & O16 & O24 & Hl2 & Rv0 & Rv1). fold nd in Hl2.
      assert (HVL2 : 1 <= Z.of_nat nd <= 2) by (clear - Hl2 HVN; Lia.lia).
      assert (TOPW : L5.u64_at RSEGS M0 (od + 8 * Z.of_nat nd + 8) w0).
      { subst w0. unfold nth_w. rewrite LAT. destruct nd as [|[|[|k]]]; try (exfalso; clear - HVL2; Lia.lia).
        - cbn [firstn nth Nat.sub]. replace (od + 8 * Z.of_nat 1 + 8) with (od + 16) by (clear; Lia.lia). exact O16.
        - cbn [firstn nth Nat.sub]. replace (od + 8 * Z.of_nat 2 + 8) with (od + 24) by (clear; Lia.lia). exact O24. }
      assert (HW0 : 0 <= w0 <= 18446744073709551615) by (clear - W0R; lia).
      pose proof (vnzAi_conc fx0 R0 MV (fun j => match j with 2%nat => sp | 33%nat => od | 34%nat => on | 35%nat => Z.of_nat nd | 36%nat => L5.bo_fb bd | 38%nat => px | 40%nat => w0 | _ => 0 end)) as P.
      cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XOD; [clear - HVL2; lia | clear - HVL2; lia | sc]) | (apply XBD; sc) ]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR18 & aR19 & aR20 & aR21 & aR22 & aR23 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
      exists fx1, R1, M1v. split. exact MG1. split. exact aFZ. split. exact aMS.
      split. { intros x Hx. apply aKS. revert Hx; apply (L5K.incl_b _ KS_vnzAi); vm_compute; reflexivity. }
      unfold U. repeat split; assumption.
    - destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). fold nd in Hlc. destruct (BLKd cap q eq_refl) as (INB & CAPB). fold nd in CAPB.
      pose proof (L5ASHROK.block_vis L ar C HI LY HIok LB FF LK cr A M0 model0 q cap sp HH0 INB ltac:(clear - Hcap; lia) ltac:(clear - SLO; lia) SPT)
        as (QR & QD8 & QBIG & QFR & QSHD & QIMG & QW & QZ & QV & XQ). fold H in QV, XQ. fold MV in QW, QZ, XQ.
      pose proof (blk_obj_apart LB FF LK cr A M0 _ q cap od HH0 INB AOd) as QO.
      assert (TOPW : L5.u64_at RSEGS M0 (8 * Z.of_nat nd + q - 8) w0).
      { subst w0. unfold nth_w. replace (8 * Z.of_nat nd + q - 8) with (q + 8 * Z.of_nat (nd - 1)) by (clear - HVN; Lia.lia). apply LAT. rewrite Lws. clear - HVN; Lia.lia. }
      assert (HW0 : 0 <= w0 <= 18446744073709551615) by (clear - W0R; lia).
      assert (ALQ : aligned q 8) by exact QD8. assert (HVQ : 4096 <= q <= 140737488355328) by (clear - QR Hcap; lia). assert (HVC : 1 <= cap <= 134217728) by (clear - Hcap; lia).
      assert (HVQC : 4104 <= q + 8 * cap <= 140737479966720) by (clear - QR Hcap; lia).
      assert (FRQ : sp - 80 + 80 <= q \/ q + 8 * cap <= sp - 80) by (clear - QFR; lia).
      assert (HVL : 1 <= Z.of_nat nd <= 134217728) by (clear - HVN; lia).
      assert (HVCL : 0 <= -1 * Z.of_nat nd + cap <= 134217728) by (clear - CAPB Hcap HVN; lia).
      pose proof (vnzAd_conc fx0 R0 MV (fun j => match j with 2%nat => sp | 33%nat => od | 34%nat => on | 35%nat => Z.of_nat nd | 36%nat => L5.bo_fb bd | 37%nat => q | 38%nat => px | 39%nat => cap | 40%nat => w0 | _ => 0 end)) as P.
      cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XOD; [clear; lia | clear; lia | sc]) | (apply XBD; sc) | (apply XQ; [clear - HVN; lia | clear - CAPB; lia | sc]) ]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR18 & aR19 & aR20 & aR21 & aR22 & aR23 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
      exists fx1, R1, M1v. split. exact MG1. split. exact aFZ. split. exact aMS.
      split. { intros x Hx. apply aKS. revert Hx; apply (L5K.incl_b _ KS_vnzAd); vm_compute; reflexivity. }
      unfold U. repeat split; assumption. }
  destruct RUNA as (fx1 & R1 & M1v & MG1 & AFZ & AMS & AKS & aR2 & aR8 & aR9 & aR10 & aR18 & aR19 & aR20 & aR21 & aR22 & aR23 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8).
  replace (8 * Z.of_nat nd - 8) with (8 * (Z.of_nat nd - 1)) in aR22 by (clear; lia).
  (* [comment removed for export] *)
  assert (W80' : L5.writable RSEGS M1v (sp - 80) 80) by (eapply L5.writable_grows; eauto).
  assert (IMGC' : L5.img_clear M1v 860160 880640). { intros a Ha. rewrite AFZ. apply IMGC. exact Ha. clear - Ha; lia. clear - Ha SPR; lia. }
  assert (CSB' : L5.u64_at RSEGS M1v 908088 2147450880). { eapply L5C.u64_at_agree. 4: exact CSB. 2: clear; lia. 2: clear; lia. intros i Hi. apply AFZ. clear - Hi; lia. clear - Hi SPR; lia. }
  assert (CUAR' : L5.u32_at RSEGS M1v 908096 1). { eapply u32_at_agree1. 4: exact CUAR. 2: clear; lia. 2: clear; lia. intros i Hi. apply AFZ. clear - Hi; lia. clear - Hi SPR; lia. }
  assert (PXW' : L5.writable RSEGS M1v px 4) by (eapply L5.writable_grows; eauto).
  assert (PXZ' : L5KA.zeros_at M1v (px / 8 + SB) 1).
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    eapply L5KA.zeros_at_agree1. 2: exact PXZ. intros i Hi. apply AFZ. clear - Hi PXR; unfold SB in *; lia. clear - Hi PXR SPR; unfold SB in *; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  assert (RUNB : exists fx3 R3 M3v, mem_grows M1v M3v
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (px <= i < px + 4) -> M3v (Z_to_bv 64 i) = M1v (Z_to_bv 64 i))
            /\ msteps RSEGS (st fx1 R1 0x9335c M1v) (st fx3 R3 SHL M3v)
            /\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat -> getr R3 (reg x) = getr R1 (reg x))
            /\ getr R3 (reg 1) = Z_to_bv 64 603028 /\ getr R3 (reg 10) = Z_to_bv 64 od /\ getr R3 (reg 11) = Z_to_bv 64 C0
            /\ getr R3 (reg 24) = Z_to_bv 64 (px / 8 + 2147450880) /\ L5.u32_at RSEGS M3v px C0).
  { pose proof (br_93008 fx1 R1 M1v) as BR. rewrite aR10, <- rl0, getr_zero in BR.
    destruct (Z_lt_le_dec w0 (2 ^ 63)) as [POS|NEG].
    - (* [comment removed for export] *)
      rewrite (lts0_pos w0) in BR by (clear - POS W0R; lia).
      pose proof (vnzP0_conc fx1 R1 M1v (fun j => match j with 2%nat => sp | 33%nat => od | 34%nat => on | 35%nat => Z.of_nat nd | 38%nat => px | 42%nat => U R1 1 | _ => 0 end)) as P.
      cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx2 & R2 & M2v & MG2 & pFR & pFZ & (pMS & pKS & pR11)).
      pose proof (mem_eq_of_agree M1v M2v pFZ) as EM2. subst M2v.
      assert (Y10 : getr R2 (10%bv : bv 5) = Z_to_bv 64 w0). { rewrite r10. rewrite (pKS 10%nat) by inl. exact aR10. }
      assert (Y11 : getr R2 (11%bv : bv 5) = Z_to_bv 64 0). { rewrite r11. exact pR11. }
      destruct (As0Clz.clz_loop (fx:=fx2) M1v (seg_rom RSEGS) R2 w0 0 Y10 Y11 ltac:(clear - POS W0R; lia) ltac:(clear; lia)) as (c & R2' & Hc & Hpow & Z10 & Z11 & ZK & MSC).
      assert (EC : c = C0). { unfold C0. apply clz_of_unique. clear - W0R; lia. clear - Hc; lia. exact Hpow. }
      subst c. rewrite Z.add_0_l in Z11.
      assert (K2 : forall i, i <> 10%nat -> i <> 11%nat -> (i < 32)%nat -> getr R2' (reg i) = getr R2 (reg i)).
      { intros i Hi10 Hi11 Hi32. apply ZK.
        all: try rewrite r10; try rewrite r11; intros E; apply (f_equal bv_unsigned) in E;
             rewrite !Z_to_bv_small in E by (unfold bv_modulus; replace (2 ^ Z.of_N 5) with 32 by reflexivity; Lia.lia); Lia.lia. }
      assert (KS2 : forall i, In i [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat -> getr R2' (reg i) = getr R1 (reg i)).
      { intros i Hi. rewrite K2. apply pKS. revert Hi; apply (L5K.incl_b _ KS_vnzP0); vm_compute; reflexivity.
        all: revert Hi; cbn [In]; intros Hi; decompose [or] Hi; subst; try Lia.lia; contradiction. }
      assert (E1 : (0x93364%bv : word) = Z_to_bv 64 0x93364) by (apply bv_eq; reflexivity).
      assert (E2 : (0x93370%bv : word) = Z_to_bv 64 0x93370) by (apply bv_eq; reflexivity).
      rewrite E1, E2 in MSC.
      pose proof (vnzB_conc fx2 R2' M1v (fun j => match j with 2%nat => sp | 33%nat => od | 34%nat => on | 35%nat => Z.of_nat nd | 38%nat => px | 42%nat => U R2' 1 | 43%nat => C0 | _ => 0 end)) as P.
      cbn beta iota in P.
      rewrite <- r11 in P.
      feed P ltac:(first [apply UR | apply U_to | exact Z11 | (rewrite KS2 by inl; sc) | sc]).
      destruct P as (fx3 & R3 & M3v & MG3 & bFR & bFZ & (bMS & bKS & bR1 & bR10 & bR24 & bPX)).
      exists fx3, R3, M3v. split. exact MG3. split. { intros i Hi Hn. apply bFZ. exact Hi. clear - Hn; lia. }
      split. { eapply msteps_trans. exact BR. eapply msteps_trans. exact pMS. eapply msteps_trans. exact MSC. exact bMS. }
      split. { intros x Hx. rewrite (bKS x) by (revert Hx; apply (L5K.incl_b _ KS_vnzB); vm_compute; reflexivity). apply KS2. revert Hx; apply (L5K.incl_b _ _); vm_compute; reflexivity. }
      split. exact bR1. split. exact bR10. split. { rewrite (bKS 11%nat) by inl. rewrite <- r11. exact Z11. } split. exact bR24. exact bPX.
    - (* [comment removed for export] *)
      rewrite (lts0_neg w0) in BR by (clear - NEG W0R; lia).
      assert (C00 : C0 = 0). { unfold C0. symmetry. apply clz_of_unique. clear - W0R; lia. clear; lia. rewrite Z.pow_0_r. clear - NEG W0R; lia. }
      pose proof (vnzN_conc fx1 R1 M1v (fun j => match j with 2%nat => sp | 33%nat => od | 34%nat => on | 35%nat => Z.of_nat nd | 38%nat => px | 42%nat => U R1 1 | _ => 0 end)) as P.
      cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx3 & R3 & M3v & MG3 & nFR & nFZ & (nMS & nKS & nR1 & nR10 & nR11 & nR24 & nPX)).
      exists fx3, R3, M3v. split. exact MG3. split. { intros i Hi Hn. apply nFZ. exact Hi. clear - Hn; lia. }
      split. { eapply msteps_trans. exact BR. exact nMS. }
      split. { intros x Hx. apply nKS. revert Hx; apply (L5K.incl_b _ KS_vnzN); vm_compute; reflexivity. }
      split. exact nR1. split. exact nR10. split. { rewrite C00. exact nR11. } split. exact nR24. rewrite C00. exact nPX. }
  destruct RUNB as (fx3 & R3 & M3v & MG3 & BFZ & BMS & BKS & bR1 & bR10 & bR11 & bR24 & bPX).
  set (WW := fun a => sp - 80 <= a < sp \/ px <= a < px + 4).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M0 model0 fx0 fx3 R0 NORM R3 SHL M3v WW K HH0 AM0 (msteps_trans _ _ _ _ AMS BMS) (mem_grows_trans _ _ _ MG1 MG3)).
  { intros a Ha Hna. subst WW; cbn beta in Hna. rewrite BFZ. apply AFZ. exact Ha. clear - Hna; lia. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. subst WW; cbn beta in Wa. split. apply stack_client. clear - Wa SLO SHI SPT Spx Hpx2; lia. clear; lia. clear - Wa SLO SPT Spx; lia. }
  intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
  assert (STK3 : astk ar M3 sp NORM_SCR). { eapply astk_grows. exact STK. exact MGM3. }
  pose proof (stk_vis LB FF LK cr A M3 model3 sp HH3 STK3) as (_ & _ & _ & XB3). rewrite AH3 in XB3. rewrite VIS3 in XB3.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> a < sp - 80 \/ (sp <= a /\ ~ (px <= a < px + 4)) -> M3 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
  { intros a Ha Ra. apply FRM3. exact Ha. subst WW; cbn beta. clear - Ra Spx. Lia.lia. }
  assert (CTX3 : ctx R3 M3 model3 LB cr LK A).
  { unfold ctx. split. exact HH3. split. exact AM3. split. exact RT3. split. apply incl_refl. split. apply incl_refl.
    split. { unfold regsN. rewrite !BKS by inl. repeat split; try assumption. intros k Hk. rewrite BKS. apply AKS. revert Hk; apply (L5K.incl_b _ _); vm_compute; reflexivity.
             revert Hk; apply (L5K.incl_b _ _); vm_compute; reflexivity. }
    split. { assert (KF : forall a v, sp - 80 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M3 a v).
             { intros a v Ha Hb Hc. apply XB3. exact Ha. exact Hb. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia.
               intros i Hi. apply BFZ. clear - Hi Ha Hb SPR; lia. clear - Hi Ha Hb Spx; lia. }
             unfold saved. repeat split; apply KF; first [assumption | clear; lia]. }
    split. exact STK3.
    split. { apply (proj1 (u32_at_vis H M3 px C0 ltac:(intros i Hi; apply PXH; clear - Hi; lia) ltac:(clear - PXR; lia) ltac:(clear - PXR; lia))). unfold H. rewrite VIS3. exact bPX. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split. { intros j Hj. unfold byte_at, S. rewrite KEEP3. apply SZd0. exact Hj. clear - Hj ODR; unfold SB; lia. left. clear - Hj ODR SPR; unfold SB; lia. }
    split. { intros j Hj. unfold byte_at, S. rewrite KEEP3. apply SZn0. exact Hj. clear - Hj ONR; unfold SB; lia. left. clear - Hj ONR SPR; unfold SB; lia. }
    split. { intros j Hj. unfold byte_at, S. rewrite KEEP3. apply SZp0. exact Hj. clear - Hj PXR; unfold SB; lia. left. clear - Hj PXR SPR; unfold SB; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split.
    - apply (ek_piece L ar LB FF sp NORM_SCR W M0 M3 WW FRM3). intros a Ha Hc Ho Wa. subst WW; cbn beta in Wa. destruct Wa as [Wa|Wa].
      + destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M0 _ sp NORM_SCR a HH0 SPT Hc) as [Y|Y]. rewrite SCR_EQ in Y. clear - Wa Y; lia. clear - Wa Y SLO; lia.
      + apply (Ho (px, 4)). unfold W, norm_W. right; right; left; reflexivity. unfold L5.in_rng; cbn [fst snd]. exact Wa.
    - apply dk_grows. exact MGM3. }
  (* [comment removed for export] *)
  assert (OBd3 : L5.big_at RSEGS M3 od bd). { eapply L5C.big_at_agree. 4: exact OBd. 2: clear - ODR; lia. 2: clear - ODR; lia. intros j Hj. apply KEEP3. clear - Hj ODR; lia. left. clear - Hj ODFR; lia. }
  assert (OBn3 : L5.big_at RSEGS M3 on bn). { eapply L5C.big_at_agree. 4: exact OBn. 2: clear - ONR; lia. 2: clear - ONR; lia. intros j Hj. apply KEEP3. clear - Hj ONR; lia. left. clear - Hj ONFR; lia. }
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as (WB0 & _).
  assert (BLKLOW : forall cap q, In (q, 8 * cap) LB -> 0 <= q /\ q + 8 * cap <= sp - 4096).
  { intros cap q INq. pose proof (proj1 (WB0 _ INq)) as (Q0 & _ & _ & _ & Q4 & _). cbn [fst snd] in Q0, Q4. clear - Q0 Q4 SLO. lia. }
  assert (OLd3 : L5C.obj_limbs RSEGS M3 bd wd).
  { split. exact Lws. split. exact Rws. fold nd. destruct (L5.bo_st bd) as [v0 v1|cap q] eqn:EST. exact LAT.
    destruct (BLKd cap q eq_refl) as (INB & CAPB). fold nd in CAPB. pose proof (BLKLOW cap q INB) as (Q0 & Q1).
    eapply (L5C.limbs_at_agree RSEGS M0 M3). 4: exact LAT. 2: exact Q0. 2:{ rewrite Lws. clear - CAPB Q1 SPR. lia. }
    intros j Hj. apply KEEP3. rewrite Lws in Hj. clear - Hj Q0 CAPB Q1 SPR; lia. left. rewrite Lws in Hj. clear - Hj CAPB Q1; lia. }
  pose proof OLn as (Lwn & Rwn & LATn). fold nn in Lwn, LATn.
  assert (OLn3 : L5C.obj_limbs RSEGS M3 bn wn).
  { split. exact Lwn. split. exact Rwn. fold nn. destruct (L5.bo_st bn) as [v0 v1|cap q] eqn:EST. exact LATn.
    destruct (BLKn cap q eq_refl) as (INB & CAPB). fold nn in CAPB. pose proof (BLKLOW cap q INB) as (Q0 & Q1).
    eapply (L5C.limbs_at_agree RSEGS M0 M3). 4: exact LATn. 2: exact Q0. 2:{ rewrite Lwn. clear - CAPB Q1 SPR. lia. }
    intros j Hj. apply KEEP3. rewrite Lwn in Hj. clear - Hj Q0 CAPB Q1 SPR; lia. left. rewrite Lwn in Hj. clear - Hj CAPB Q1; lia. }
  pose proof CTX3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SZd3 & SZn3 & _).
  (* [comment removed for export] *)
  assert (DWd0 : forall cap q, L5.bo_st bd = L5.BDyn cap q -> forall a, aclient L ar LB FF sp NORM_SCR a -> L5.outside W a -> ~ (q <= a < q + 8 * cap)).
  { intros cap q E a _ Ho X. apply (Ho (q, 8 * cap)). unfold W, norm_W, dyn_area. rewrite E. cbn [app In]. tauto. unfold L5.in_rng; cbn [fst snd]. exact X. }
  assert (DWn0 : forall cap q, L5.bo_st bn = L5.BDyn cap q -> forall a, aclient L ar LB FF sp NORM_SCR a -> L5.outside W a -> ~ (q <= a < q + 8 * cap)).
  { intros cap q E a _ Ho X. apply (Ho (q, 8 * cap)). unfold W, norm_W, dyn_area. rewrite E. destruct (L5.bo_st bd); cbn [app In]; tauto. unfold L5.in_rng; cbn [fst snd]. exact X. }
  apply (shl_step od fx3 R3 M3 model3 LB cr LK A 0x93394 bd wd CTX3 bR10 bR11 bR1).
  - split. clear; lia. reflexivity.
  - exact AOd.
  - unfold W, norm_W. left; reflexivity.
  - exact SZd3.
  - exact OBd3.
  - exact OLd3.
  - exact Hnd.
  - intros cap q E. destruct (BLKd cap q E) as (INB & CAPB). split. exact INB. split. exact CAPB. exact (DWd0 cap q E).
  - intros K1 DYF L2. pose proof cost_nonneg as (CK & CL & CO). destruct CR as [CR1 CR2]. unfold acredit_ok.
    assert (CNd : cnt bd = 1). { unfold cnt. rewrite DYF. reflexivity. } rewrite CNd in CR1, CR2.
    assert (X : 0 <= cnt bn) by (unfold cnt; destruct (L5.bo_dyn bn); clear; lia). split. clear - CR1 X CK. nia. clear - CR2 X CL CO. nia.
  - exists []. reflexivity.
  - (* [comment removed for export] *)
    intros fx5 R5 M5 model5 LK5 A5 gd std LB5 cr5 d n CTX5 ILK5 KR5 KP5 DLOC OAd5 LCd5 ELB5 ECR5 FRd5.
    apply (stageD fx5 R5 M5 model5 LB5 cr5 LK5 A5 gd std CTX5).
    + rewrite (KR5 20%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite BKS by inl. exact aR20.
    + exact OAd5.
    + exact LCd5.
    + apply (big_at_kept LB FF M3 M5 sp od d n on _ KP5 AOn). exact APdn. clear - ONR; lia. clear - ONR; lia. exact OBn3.
    + apply (limbs_kept_b LB FF M3 M5 sp od d n bn wn KP5). 2: exact OLn3.
      destruct (L5.bo_st bn) as [v0 v1|capn qn] eqn:ESTn. exact I. destruct (BLKn capn qn eq_refl) as (INn & CAPn). fold nn in CAPn. pose proof (BLKLOW capn qn INn) as (Q0 & Q1).
      split. exact INn. split.
      { destruct DLOC as [(-> & Hn)|(c & E & Hn)].
        - pose proof (blk_obj_apart LB FF LK cr A M0 _ qn capn od HH0 INn AOd) as X. pose proof OBn3 as (_ & _ & _ & OSTn). rewrite ESTn in OSTn. destruct OSTn as (_ & _ & _ & _ & Cc & _). clear - X Hn Cc. lia.
        - pose proof (APB c d capn qn E eq_refl) as X. clear - X Hn. lia. }
      split. fold nn. clear - CAPn; lia. split. exact Q0. clear - Q1 SPR; lia.
    + intros cap q E. destruct (BLKn cap q E) as (INn & CAPn). split. rewrite ELB5. apply in_or_app. right. exact INn. split. exact CAPn. exact (DWn0 cap q E).
    + (* [comment removed for export] *)
      intros cd qd cn qn Ed En. subst std. destruct (BLKn cn qn En) as (INn & _).
      destruct gd as [|Ad cd'].
      * destruct OAd5 as (_ & _ & _ & _ & _ & GMd). destruct (L5.bo_st bd) as [v0 v1|cap q] eqn:E; [contradiction|]. destruct GMd as [-> ->]. exact (APB cap q cn qn eq_refl En).
      * destruct OAd5 as (_ & _ & _ & _ & _ & (_ & Ccap8 & EST)). inversion EST; subst. destruct FRd5 as ((_ & BA & _) & _).
        pose proof (BA (qn, 8 * cn) INn) as X. cbn [fst snd] in X. clear - X. lia.
    + (* [comment removed for export] *)
      intros HSEC cd qd Ed. subst std. pose proof rlen_D_le as RLd.
      destruct gd as [|Ad cd'].
      * destruct OAd5 as (_ & _ & _ & _ & _ & GMd). destruct (L5.bo_st bd) as [v0 v1|cap q] eqn:E; [contradiction|]. destruct GMd as [-> ->].
        pose proof (proj1 (SECcap HSEC)) as X. unfold L5.bo_cap in X. rewrite E in X. fold nd in X.
        assert (DYd : L5.bo_dyn bd = true). { destruct OBd as (_ & _ & _ & OST'). rewrite E in OST'. exact (proj1 OST'). }
        specialize (X DYd). clear - X RLd. Lia.lia.
      * destruct OAd5 as (_ & _ & _ & _ & _ & (_ & Ccap8 & EST)). inversion EST; subst. destruct FRd5 as (_ & L2 & _). fold nd in L2. clear - RLd L2. Lia.lia.
    + rewrite ELB5. reflexivity.
    + rewrite ECR5. reflexivity.
    + destruct gd as [|Ad cd']. exact I. exact (proj1 FRd5).
    + destruct gd as [|Ad cd']. exact I. destruct FRd5 as (_ & L2 & K1). rewrite D_len. fold nd in L2. rewrite L2.
      destruct (Z.eqb_spec C0 0) as [E|E]. exfalso; clear - E K1; lia. clear; Lia.lia.
Qed.

End Call.

(* [comment removed for export] *)
Theorem norm_okA : norm_specA L ar HI.
Proof.
  intros fx R M model K LB FF LK cr A od on px sp r bd bn wd wn HH AM HK G11 G12 G13 G1 RA G2 A32 G4 STK ROOM RS OBd OLd Hnd TOPnz TOPsm OBn OLn Hnn NN2
         AOd SZd AOn SZn APdn P4 Spx Hpx Hpx2 SZp BLKd BLKn SECcap APB CR KONT.
  exact (entry fx R M model K LB FF LK cr A od on px sp r bd bn wd wn HH AM HK G11 G12 G13 G1 RA G2 A32 G4 STK ROOM RS OBd OLd Hnd TOPnz TOPsm OBn OLn Hnn NN2
           AOd SZd AOn SZn APdn P4 Spx Hpx Hpx2 SZp BLKd BLKn SECcap APB CR KONT).
Qed.
End WithIface.
End SCFG_1.
End L5ANORM.
