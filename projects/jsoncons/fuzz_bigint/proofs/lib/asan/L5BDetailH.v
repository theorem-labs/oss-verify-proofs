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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue BigModel BigFactsRun BigFactsDigits L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5AChk L5BChkAs0 L5ArithSpecsB0 L5ParseSpecsBB0 L5BDetailP L5BDetailK L5BDetailZ Bo0_code_8e368_8f368
     AsanPlanCore AsanPlanSound Bo0PlanKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADH.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5PSA. Import L5ADTP. Import L5ADK.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
(* [comment removed for export] *)
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma r13 : (13%bv : bv 5) = reg 13. Proof. apply bv_eq; reflexivity. Qed.
Lemma DSCR_EQ : L5PSB.DETAIL_SCRB = 4864. Proof. reflexivity. Qed.
Lemma ASG_EQ : ASSIGN_SCR = 4560. Proof. reflexivity. Qed.
Lemma MUL_EQ : L5ASB.MUL10_SCRB = 4624. Proof. reflexivity. Qed.
Lemma ADD_EQ : L5ASB.ADDD_SCRB = 4656. Proof. reflexivity. Qed.
Lemma RSV_EQ : RESERVE_SCR = 4368. Proof. reflexivity. Qed.
Lemma DEL_EQ : OPDEL_SCR = 4096. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma byte_of_u8 M a v : L5.u8_at RSEGS M a v -> (a < 0x10000 \/ 0x634000 <= a) -> 0 <= a < 2 ^ 64 -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros U0 HA Ha. unfold L5.u8_at in U0. cbn [rdn] in U0.
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:E.
  - inversion U0. reflexivity.
  - exfalso. unfold seg_rom in U0. unfold memory_read in U0. change (Z.of_N 1) with 1 in U0.
    rewrite (as0_in_hull (Z_to_bv 64 a)) in U0. discriminate U0.
    rewrite L5.unsigned_lit by lia. unfold APS.in_hull. cbn. destruct HA; [apply andb_false_intro1 | apply andb_false_intro2]; apply Z.leb_gt || apply Z.ltb_ge; lia.
Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Let LY2 : as0_layout2 L := as0_layout2_of L C LY.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.

Lemma statics_vis LB FF LK cr A M model :
  ri_inv HI LB FF LK cr A M (vml_of model) ->
  let MV := mrestrict (ahid A model) M in
  L5.img_clear MV 860160 884736 /\ L5.u64_at RSEGS MV 911160 2147450880 /\ L5.u32_at RSEGS MV 911168 1.
Proof.
  intros HH. pose proof (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (aly_segs L C LY) in ST.
  pose proof (statics_facts L C M LY ST) as (IMGC & CSB & CUAR & _).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & VIMG & _).
  split. apply img_clear_mrestrict. exact IMGC.
  split. apply (proj2 (u64_at_vis _ M _ _ (VIMG 911160 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CSB.
  apply (proj2 (u32_at_vis _ M _ _ (VIMG 911168 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CUAR.
Qed.

(* [comment removed for export] *)
Lemma ek_bytes LB FF sp scr M Mk p (s : list Z) :
  ek L ar LB FF sp scr [] M Mk -> asrc IL LB FF M p (Z.of_nat (length s)) -> 0 <= p -> p + Z.of_nat (length s) <= 2 ^ 64 ->
  L5.bytes_at RSEGS M p s -> L5.bytes_at RSEGS Mk p s.
Proof.
  intros EK SRC P0 P1 B. eapply L5C.bytes_at_agree. 4: exact B. 2: exact P0. 2: exact P1.
  intros i Hi. apply EK. split. lia. split. replace i with (p + (i - p)) by lia. apply (asrc_client L ar C IL LY LY2 ILY LB FF M sp scr p _ (i - p) SRC). lia. intros rr [].
Qed.
Lemma ek_src LB FF LK cr A sp scr M model Mk LB' FF' p m :
  ri_inv HI LB FF LK cr A M (vml_of model) ->
  ek L ar LB FF sp scr [] M Mk -> asrc IL LB FF M p m -> incl LB LB' -> incl FF FF' -> asrc IL LB' FF' Mk p m.
Proof.
  intros HH EK SRC IL1 IF1. eapply asrc_keep. exact SRC. exact IL1. exact IF1.
  intros so AO SZ j Hj. unfold byte_at. rewrite EK. apply SZ. exact Hj.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model so 24 sp scr HH AO ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & _ & _ & _ & _ & OCLSH).
  change (24 / 8) with 3 in OCLSH. split. unfold S, SB. lia. split. unfold S. apply OCLSH. exact Hj. intros rr [].
Qed.

(* [comment removed for export] *)
Definition frk (sb : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sb + 8) (U R 1) /\ L5.u64_at RSEGS M sb (U R 8) /\ L5.u64_at RSEGS M (sb - 8) (U R 9) /\ L5.u64_at RSEGS M (sb - 16) (U R 18) /\
  L5.u64_at RSEGS M (sb - 24) (U R 19) /\ L5.u64_at RSEGS M (sb - 32) (U R 20) /\ L5.u64_at RSEGS M (sb - 40) (U R 21) /\ L5.u64_at RSEGS M (sb - 48) (U R 22) /\
  L5.u64_at RSEGS M (sb - 56) (U R 23) /\ L5.u64_at RSEGS M (sb - 64) (U R 24) /\ L5.u64_at RSEGS M (sb - 72) (U R 25) /\ L5.u64_at RSEGS M (sb - 80) (U R 26) /\
  L5.u64_at RSEGS M (sb - 88) (U R 27).
Definition spk (sb F negz : Z) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sb - 112) F /\ L5.u64_at RSEGS M (sb - 144) F /\ L5.u64_at RSEGS M (sb - 152) F /\ L5.u64_at RSEGS M (sb - 168) negz.
Lemma frk_agree sb R M M' : frk sb R M -> (forall a, sb - 88 <= a < sb + 16 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> 160 <= sb -> sb + 16 <= 2 ^ 64 -> frk sb R M'.
Proof.
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) AG H0 H1. unfold frk.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
Lemma spk_agree sb F negz M M' : spk sb F negz M -> (forall a, sb - 168 <= a < sb - 104 -> ~ (sb - 136 <= a < sb - 128) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> 192 <= sb -> sb + 16 <= 2 ^ 64 -> spk sb F negz M'.
Proof.
  intros (C1 & C2 & C3 & C4) AG H0 H1. unfold spk.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
(* [comment removed for export] *)
Lemma stack_callee LBk FFk spc SCR W M M' a :
  ahpres L ar LBk FFk spc SCR W M M' -> (forall rr, In rr W -> fst rr + snd rr <= ahl_ceil ar) -> 0 <= a -> ahl_ceil ar <= a < 2 ^ 47 -> spc <= a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros (E & _) HW H0 Ha Hs. apply E. split. lia. split. apply stack_client. exact Ha. lia.
  intros rr Hr X. specialize (HW rr Hr). unfold L5.in_rng in X. lia.
Qed.
Lemma stack_rt LBk FFk spc scr M M' a :
  aheap_pres L ar LBk FFk spc scr M M' -> 0 <= a -> ahl_ceil ar <= a < 2 ^ 47 -> spc <= a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof. intros (E & _) H0 Ha Hs. apply E. lia. apply stack_client. exact Ha. lia. Qed.

(* [comment removed for export] *)
Section OWN.
Variables (sb F rs : Z) (R0 : bvmap 5 word) (negz : Z).
Hypothesis SBR : 140735332487520 <= sb <= 140737488355312.
Hypothesis SBC : ahl_ceil ar + 4096 <= sb - 192.
Hypothesis FRR : 4096 <= F /\ F + 256 <= 2 ^ 47 /\ (F / 8) * 8 = F.
Definition own (M : word -> option byte) : Prop := frk sb R0 M /\ spk sb F negz M /\ L5.defined M (F / 8 + SB) 32.
Lemma own_agree M M' : own M -> (forall a, sb - 168 <= a < sb + 16 -> ~ (sb - 136 <= a < sb - 128) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, F / 8 + SB <= a < F / 8 + SB + 32 -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) -> own M'.
Proof.
  intros (K1 & K2 & K3) AG DF. split. apply (frk_agree sb R0 M M' K1). intros a Ha. apply AG. lia. lia. lia. lia.
  split. apply (spk_agree sb F negz M M' K2). intros a Ha Hn. apply AG. lia. exact Hn. lia. lia.
  intros i Hi. apply DF. lia. apply K3. exact Hi.
Qed.
Lemma own_piece M M' (W : Z -> Prop) : own M -> (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_grows M M' ->
  (forall a, sb - 168 <= a < sb + 16 -> ~ (sb - 136 <= a < sb - 128) -> ~ W a) -> own M'.
Proof. intros O FRM MG NW. apply (own_agree M M' O). intros a Ha Hn. apply FRM. lia. apply NW. exact Ha. exact Hn. intros a _ X. apply MG. exact X. Qed.
Lemma own_rt LBk FFk spc scr M M' : own M -> aheap_pres L ar LBk FFk spc scr M M' -> In (F, 2, rs) FFk -> spc <= sb - 168 -> own M'.
Proof.
  intros O PRES INF Hs. apply (own_agree M M' O).
  - intros a Ha _. apply (stack_rt LBk FFk spc scr M M' a PRES). lia. lia. lia.
  - intros a Ha X. rewrite (proj1 PRES a). exact X. unfold SB in Ha. lia.
    apply (fframe_shadow_client L ar LBk FFk spc scr F 2 rs). exact INF. change (ff_bytes 2) with 256. unfold in_shadow_of, S. destruct FRR as (F0 & F1 & F8).
    clear - Ha F8. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma own_callee LBk FFk spc SCR W M M' : own M -> ahpres L ar LBk FFk spc SCR W M M' -> In (F, 2, rs) FFk -> spc <= sb - 168 ->
  (forall rr, In rr W -> fst rr + snd rr <= ahl_ceil ar) -> own M'.
Proof.
  intros O AH INF Hs HW. apply (own_agree M M' O).
  - intros a Ha _. apply (stack_callee LBk FFk spc SCR W M M' a AH HW). lia. lia. lia.
  - intros a Ha X. apply (proj2 (proj2 AH) a). unfold SB in Ha. lia. 2: exact X.
    apply (fframe_shadow_client L ar LBk FFk spc SCR F 2 rs). exact INF. change (ff_bytes 2) with 256. unfold in_shadow_of, S. destruct FRR as (F0 & F1 & F8).
    clear - Ha F8. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma own_mem LBk FFk spc scr (D : Z -> Prop) M M' : own M ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBk FFk spc scr a -> ~ D a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  In (F, 2, rs) FFk -> spc <= sb - 168 -> (forall a, D a -> a < ahl_ceil ar /\ ~ (F / 8 + SB <= a < F / 8 + SB + 32)) -> own M'.
Proof.
  intros O PRES INF Hs HD. apply (own_agree M M' O).
  - intros a Ha _. apply PRES. lia. apply stack_client. lia. lia. intros X. apply HD in X. lia.
  - intros a Ha X. rewrite PRES. exact X. unfold SB in Ha. lia. 2:{ intros Y. apply HD in Y. tauto. }
    apply (fframe_shadow_client L ar LBk FFk spc scr F 2 rs). exact INF. change (ff_bytes 2) with 256. unfold in_shadow_of, S. destruct FRR as (F0 & F1 & F8).
    clear - Ha F8. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma own_vis H M : own M -> avis H (sb - 192) 208 -> avis H (F / 8 + SB) 32 -> own (mrestrict H M).
Proof.
  intros O V1 V2. apply (own_agree M (mrestrict H M) O).
  - intros a Ha _. apply mrestrict_visible. replace a with ((sb - 192) + (a - (sb - 192))) by lia. apply V1. lia.
  - intros a Ha X. rewrite mrestrict_visible. exact X. replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by lia. apply V2. lia.
Qed.
End OWN.

(* [comment removed for export] *)
Lemma ek_obj LB FF LK cr A sp scr M model Mk o :
  ri_inv HI LB FF LK cr A M (vml_of model) -> ek L ar LB FF sp scr [] M Mk -> aobj FF o 32 ->
  (forall a, o <= a < o + 32 -> Mk (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\ (forall j, 0 <= j < 4 -> Mk (Z_to_bv 64 (S o + j)) = M (Z_to_bv 64 (S o + j))).
Proof.
  intros HH EK AO.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp scr HH AO ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & _ & _ & _ & OCL & OCLSH).
  change (32 / 8) with 4 in OCLSH. split.
  - intros a Ha. apply EK. split. lia. split. replace a with (o + (a - o)) by lia. apply OCL. lia. intros rr [].
  - intros j Hj. apply EK. split. unfold S, SB. lia. split. unfold S. apply OCLSH. exact Hj. intros rr [].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma apure LB FF LK cr A M model (fx fx1 : FPState) Ra (pc : Z) Rb (pc1 : Z) K :
  ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model ->
  msteps RSEGS (st fx Ra pc (mrestrict (ahid A model) M)) (st fx1 Rb pc1 (mrestrict (ahid A model) M)) ->
  (forall model1, ri_inv HI LB FF LK cr A M (vml_of model1) -> amodel_ok A model1 -> model_rt model model1 -> ahid A model1 = ahid A model ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) Rb pc1 M model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Ra pc M model) K.
Proof.
  intros HH AM MS KONT.
  apply (apiece_ro L ar C HI LY HIok LB FF LK cr A M model fx fx1 Ra pc Rb pc1 (mrestrict (ahid A model) M) K HH AM MS (mem_grows_refl _) (fun a _ => eq_refl)).
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1.
  assert (E : M1 = M) by (apply mem_eq_of_agree; exact FRM1). subst M1. apply KONT; assumption.
Qed.

(* [comment removed for export] *)
Lemma astk_after2 LB0 FF0 LK0 cr0 A0 M0 V0 LBk FFk M M1 M2 sp scr sp' scr' W :
  ri_inv HI LB0 FF0 LK0 cr0 A0 M0 V0 ->
  astk ar M sp scr -> mem_grows M M1 -> ahpres L ar LBk FFk sp' scr' W M1 M2 ->
  sp - scr <= sp' - scr' -> sp' <= sp -> 0 <= scr -> astk ar M2 sp scr.
Proof.
  intros HH (A16 & SLO & SHI & SPT & DSCR & DUP) MG (PRES & SDEF & DK) H1 H2 H0.
  assert (D : forall x, (sp - scr <= x < sp \/ sp <= x < ar_stack_top ar) -> M2 (Z_to_bv 64 x) <> None).
  { intros x Hx2. destruct (rng_dec x (sp' - scr') sp') as [I|O].
    - replace x with (sp' - scr' + (x - (sp' - scr'))) by lia. apply SDEF. lia.
    - pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
      apply DK. lia. apply stack_client. lia. exact O. apply MG. destruct (Z_lt_le_dec x sp).
      + replace x with (sp - scr + (x - (sp - scr))) by lia. apply DSCR. lia.
      + replace x with (sp + (x - sp)) by lia. apply DUP. lia. }
  split. exact A16. split. lia. split. lia. split. exact SPT. split.
  - intros j Hj. apply D. lia.
  - intros j Hj. apply D. lia.
Qed.

Lemma lb_remove_head q nq LBx : lb_remove q ((q, nq) :: LBx) = LBx.
Proof. cbn. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma lb_remove_skip q q' m LBx : q' <> q -> lb_remove q ((q', m) :: LBx) = (q', m) :: lb_remove q LBx.
Proof. intros NE. cbn. destruct (Z.eqb_spec q' q). contradiction. reflexivity. Qed.

(* [comment removed for export] *)
Lemma afresh_of_inv q nq LB FF LK cr A M V : ri_inv HI ((q, nq) :: LB) FF LK cr A M V -> afresh L ar LB (FF ++ LK) M q nq.
Proof.
  intros HH. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB (q, nq) (or_introl eq_refl)) as (BR & BD & BS & _ & BA & BF & _). cbn [fst snd] in *.
  rewrite lb_remove_head in BA. unfold afresh. split. exact BR. split. exact BA. split. exact BF. split. exact BD. exact BS.
Qed.

(* [comment removed for export] *)
Lemma not_client_bx FFx a : forall BX LBx,
  (forall b, In b BX -> ablock_range L ar (fst b) (snd b) /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + FS_BYTES <= fst b)) ->
  ar_fs ar <= a < ar_fs ar + FS_BYTES -> (2147446784 + 17592186048512 <= a \/ a + 1 <= 2147446784) ->
  ~ aclient L ar LBx FFx 0 0 a -> ~ aclient L ar (BX ++ LBx) FFx 0 0 a.
Proof.
  induction BX as [|b BX IH]; intros LBx HB HA HBIG NC. exact NC.
  cbn [app]. intros X. destruct (aclient_consb_inv L ar (BX ++ LBx) FFx b 0 0 a X) as [Y|[Y|Y]].
  - revert Y. apply IH. intros b' Hb'. apply HB. right; exact Hb'. exact HA. exact HBIG. exact NC.
  - destruct (HB b (or_introl eq_refl)) as (_ & Z0). clear - Y Z0 HA. lia.
  - destruct (HB b (or_introl eq_refl)) as ((B0 & _ & _ & B3 & _ & (_ & _ & B6)) & _). unfold in_shadow_of, S, SB in Y.
    assert (E1 : 0 <= fst b / 8) by (apply Z.div_pos; clear - B0; lia).
    assert (E2 : (fst b + snd b - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; clear - B6; lia).
    change ((2 ^ 47 - 1) / 8) with 17592186044415 in E2. clear - Y E1 E2 HBIG. lia.
Qed.
Lemma blocks_off_fs LBx FFx LKx crx Ax Mx Vx BX LBy : ri_inv HI LBx FFx LKx crx Ax Mx Vx -> LBx = BX ++ LBy ->
  forall b, In b BX -> ablock_range L ar (fst b) (snd b) /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + FS_BYTES <= fst b).
Proof.
  intros HH E b Hb. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB b ltac:(rewrite E; apply in_or_app; left; exact Hb)) as (BR & _ & _ & _ & _ & _ & BFS). split. exact BR. exact BFS.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CTX.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
          (p o sp r fb : Z) (neg : bool) (s : list Z) (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Local Notation sb := (sp - 16).
Local Notation n := (Z.of_nat (length s)).
Local Notation negz := (if neg then 1 else 0).
Local Notation FF' := ((F, 2, sp - 16 - 192 + 32) :: FF).

Record mctx : Prop := MCTX {
  c_HK : K [];
  c_RA : L5.ra_ok r;
  c_UR1 : U R 1 = r;
  c_G2 : getr R (reg 2) = Z_to_bv 64 sp;
  c_G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L);
  c_LEN : (length s <= 4999)%nat;
  c_HVN : 1 <= n <= 4999;
  c_CRD : parse_credit L cr (length s);
  c_SLO : ahl_ceil ar + 4096 + 4864 <= sp;
  c_SHI : sp <= ar_sptop ar;
  c_SPT : 140735340871680 <= ar_sptop ar <= 2 ^ 47;
  c_SA32 : aligned sb 32;
  c_SA16 : (sb - 192) mod 16 = 0;
  c_SPR : 0 <= sb < 2 ^ 64 /\ 140735332487520 <= sb <= 140737488355312;
  c_FFR : ffr FF LK 5;
  c_FFRS : ffrs FF sp;
  c_HH : ri_inv HI LB FF LK cr A M (vml_of model);
  c_BIG : L5.big_at RSEGS M o (L5.BO fb 0 (L5.BInl 0 0));
  c_FB3 : Z.land fb 3 = 0;
  c_AOB : aobj FF o 32;
  c_SZ : shadow_zero M o 4;
  c_BYTES : L5.bytes_at RSEGS M p s;
  c_BR : Forall (fun c => 0 <= c < 256) s;
  c_SRC : asrc IL LB FF M p n;
  c_APART : p + n <= o \/ o + 32 <= p;
  c_PRG : 4096 <= p <= 140737479966720 /\ p + n <= 140737479966720;
  c_OR : 6504448 <= o /\ o + 32 <= ahl_ceil ar /\ o + 32 <= 2 ^ 47 /\ o mod 8 = 0 /\ o / 8 * 8 = o;
  c_OBIG : 2147446784 + 17592186048512 <= o \/ o + 32 <= 2147446784;
  c_FS1 : ar_fs ar <= F;
  c_FS2 : F + 256 <= ar_fs ar + FS_BYTES;
  c_FAPP : app_mem F 256;
  c_FCEIL : F + 256 <= ahl_ceil ar;
  c_FAPART : fframes_apart F 256 (FF ++ LK2);
  c_FBLK : forall b : Z * Z, In b LB -> F + 256 <= fst b \/ fst b + snd b <= F;
  c_LKI2 : incl LK2 LK;
  c_FLP : ar_fs ar <= fl < ar_fs ar + FS_BYTES;
  c_FLNC : ~ aclient L ar LB FF' 0 0 fl;
  c_FLA : F + 256 <= fl \/ fl + 1 <= F;
  c_HH2 : ri_inv HI LB FF' LK2 cr A M2 (vml_of model2);
  c_FLC : cell_is RSEGS M2 (F + 256 - 8) 8 fl;
  c_FR : 4096 <= F /\ F + 256 <= 2 ^ 47 /\ 6504448 <= F /\ F + 256 <= ahl_ceil ar /\ 64 <= 256 <= 512;
  c_F32 : F mod 32 = 0;
  c_F8 : F / 8 * 8 = F;
  c_FBIG : 2147446784 + 17592186048512 <= F \/ F + 256 <= 2147446784;
  c_FLR : 4096 <= fl /\ fl + 1 <= 2 ^ 47 /\ 6504448 <= fl /\ fl + 1 <= ahl_ceil ar;
  c_FLBIG : 2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784;
  c_SF : sb - 192 + 208 <= F \/ F + 256 <= sb - 192;
  c_SFSH : sb - 192 + 208 <= F / 8 + SB \/ F / 8 + SB + 32 <= sb - 192;
  c_SFL : sb - 192 + 208 <= fl \/ fl + 1 <= sb - 192;
  c_OF : o + 32 <= F \/ F + 256 <= o;
  c_OFSH : o + 32 <= F / 8 + SB \/ F / 8 + SB + 32 <= o;
  c_OFL : o + 32 <= fl \/ fl + 1 <= o;
  c_FQ31 : (F + 256 - 1) / 8 = F / 8 + 31 /\ F mod 8 = 0;
  c_NCF : forall a : Z, F <= a < F + 256 \/ S F <= a <= S (F + 256 - 1) -> ~ aclient L ar LB FF sp L5PSB.DETAIL_SCRB a;
  c_NCS : forall a : Z, sb - 192 <= a < sb + 16 -> ~ aclient L ar LB FF sp L5PSB.DETAIL_SCRB a;
  c_SSH : L5ASB.stksh ar M (sp - L5PSB.DETAIL_SCRB);
  c_KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit)
                  (LK' : list fframe) (A' : list (Z * Z)),
      L5PSB.detail_postB L ar LB FF LK' cr M M' R R' o sp fb neg s LB' cr' -> model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' FF LK' cr' A' M' (vml_of model') -> srealizes RSEGS SCFG (cfg R' r M' model') K
}.
Ltac open_ctx CTX :=
  destruct CTX as [HK RA UR1 G2 G4 LEN HVN CRD SLO SHI SPT SA32 SA16 SPR FFR FFRS HH BIG FB3 AOB SZ BYTES BR SRC APART PRG OR OBIG FS1 FS2 FAPP FCEIL FAPART FBLK LKI2
                   FLP FLNC FLA HH2 FLC FR F32 F8 FBIG FLR FLBIG SF SFSH SFL OF OFSH OFL FQ31 NCF NCS SSH KONT].

(* [comment removed for export] *)
Definition RIDX : list nat := [2; 3; 4; 8; 9; 21; 26]%nat.
Definition rinv (Rc : bvmap 5 word) : Prop :=
  getr Rc (reg 2) = Z_to_bv 64 (sb - 192) /\ getr Rc (reg 8) = Z_to_bv 64 (sb + 16) /\ getr Rc (reg 9) = Z_to_bv 64 (sb - 192) /\
  getr Rc (reg 21) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr Rc (reg 26) = Z_to_bv 64 2147450880 /\
  getr Rc (reg 3) = getr R (reg 3) /\ getr Rc (reg 4) = getr R (reg 4).
Lemma rinv_keep Ra Rb : rinv Ra -> (forall k, In k RIDX -> getr Rb (reg k) = getr Ra (reg k)) -> rinv Rb.
Proof.
  intros (G2 & G8 & G9 & G21 & G26 & G3 & G4') KS. unfold rinv.
  rewrite !KS by (apply L5K.in_b; vm_compute; reflexivity). repeat split; assumption.
Qed.
Lemma rinv_ks Ra Rb (KS : list nat) : rinv Ra -> (forall x, In x KS -> getr Rb (reg x) = getr Ra (reg x)) ->
  forallb (fun i => existsb (Nat.eqb i) KS) RIDX = true -> rinv Rb.
Proof. intros RI HKS HB. apply (rinv_keep Ra Rb RI). intros k Hk. apply HKS. exact (L5K.incl_b RIDX KS HB k Hk). Qed.
Lemma rinv_pres Ra Rb : rinv Ra -> regs_preserved Ra Rb -> rinv Rb.
Proof.
  intros RI RP. apply (rinv_keep Ra Rb RI). intros k Hk. apply (cs_of_preserved Ra Rb k RP).
  revert Hk. apply (L5K.incl_b RIDX cs_all). vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Definition binv (W : list L5.range) (BX : list (Z * Z)) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)) : Prop :=
  ri_inv HI (BX ++ LB) FF' LKc crc Ac Mc (vml_of modelc) /\ amodel_ok Ac modelc /\ model_rt model modelc /\ incl A Ac /\ incl LKc LK /\
  astk ar Mc sp L5PSB.DETAIL_SCRB /\ ek L ar LB FF sp L5PSB.DETAIL_SCRB W M Mc /\ dk L ar LB FF sp L5PSB.DETAIL_SCRB M Mc /\ own sb F R negz Mc.

Lemma binv_model W BX Mc modelc LKc crc Ac model1 :
  binv W BX Mc modelc LKc crc Ac -> ri_inv HI (BX ++ LB) FF' LKc crc Ac Mc (vml_of model1) -> amodel_ok Ac model1 -> model_rt modelc model1 ->
  binv W BX Mc model1 LKc crc Ac.
Proof.
  intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9) HH1 AM1 RT1. unfold binv.
  split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5. split. exact B6. split. exact B7. split. exact B8. exact B9.
Qed.

(* [comment removed for export] *)
Lemma binv_piece (CTX : mctx) W BX Mc modelc LKc crc Ac M1 model1 (Wp : Z -> Prop) :
  binv W BX Mc modelc LKc crc Ac ->
  ri_inv HI (BX ++ LB) FF' LKc crc Ac M1 (vml_of model1) -> amodel_ok Ac model1 -> model_rt modelc model1 -> mem_grows Mc M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (sb - 176 <= a < sb - 168 \/ sb - 136 <= a < sb - 128) \/ F <= a < F + 256 \/ F / 8 + SB <= a < F / 8 + SB + 32) ->
  binv W BX M1 model1 LKc crc Ac.
Proof.
  open_ctx CTX. intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9) HH1 AM1 RT1 MG FRM WP.
  unfold binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5.
  split. eapply astk_grows. exact B6. exact MG.
  split. { eapply ek_trans. exact B7. apply (ek_piece L ar LB FF sp L5PSB.DETAIL_SCRB W Mc M1 Wp FRM). intros a Ha Hc _ X. destruct (WP a X) as [Y|[Y|Y]].
           - apply (NCS a). clear - Y; lia. exact Hc.
           - apply (NCF a). left; exact Y. exact Hc.
           - apply (NCF a). right. unfold S. rewrite (proj1 FQ31). clear - Y. unfold SB in Y |- *. lia. exact Hc. }
  split. { eapply dk_trans. exact B8. apply dk_grows. exact MG. }
  apply (own_piece sb F R negz (proj2 SPR) Mc M1 Wp B9 FRM MG). intros a Ha Hn X. destruct (WP a X) as [Y|[Y|Y]].
  - clear - Ha Hn Y; lia.
  - clear - Ha Y SF; lia.
  - clear - Ha Y SFSH; unfold SB in *; lia.
Qed.

Lemma binv_mem (CTX : mctx) W BX Mc modelc LKc crc Ac M1 model1 (D : Z -> Prop) :
  binv W BX Mc modelc LKc crc Ac ->
  ri_inv HI (BX ++ LB) FF' LKc crc Ac M1 (vml_of model1) -> amodel_ok Ac model1 -> model_rt modelc model1 ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BX ++ LB) FF' (sb - 192) 2560 a -> ~ D a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall a, sb - 192 - 2560 <= a < sb - 192 -> M1 (Z_to_bv 64 a) <> None) ->
  (forall a, D a -> M1 (Z_to_bv 64 a) <> None) -> (forall a, D a \/ ~ D a) ->
  (forall a, D a -> F + 32 <= a < F + 248) ->
  binv W BX M1 model1 LKc crc Ac.
Proof.
  open_ctx CTX. intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9) HH1 AM1 RT1 PRES SDEF DDEF DDEC DIN.
  assert (PRES' : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sb - 192) 2560 a -> ~ D a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hc ND. apply PRES. exact Ha. apply aclient_cons. apply aclient_appb. exact Hc. exact ND. }
  unfold binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5.
  split. { apply (astk_after_eq L ar C HI HIok (BX ++ LB) FF' LKc crc Ac Mc Mc M1 _ sp _ (sb - 192) 2560 B1 B6 (mem_grows_refl Mc)).
           - intros a Ha Hs Hns. apply PRES. exact Ha. apply stack_client. exact Hs. exact Hns. intros X. apply DIN in X. clear - X Hs FR FCEIL; lia.
           - exact SDEF.
           - rewrite DSCR_EQ; clear; lia.
           - clear; lia.
           - rewrite DSCR_EQ; clear; lia. }
  split. { eapply ek_trans. exact B7. apply (ek_mem L ar LB FF sp L5PSB.DETAIL_SCRB (sb - 192) 2560 D W Mc M1 PRES').
           - rewrite DSCR_EQ; clear; lia.
           - clear; lia.
           - intros a Hc _ X. apply DIN in X. apply (NCF a). left; clear - X; lia. exact Hc. }
  split. { eapply dk_trans. exact B8. apply (dk_mem L ar LB FF sp L5PSB.DETAIL_SCRB (sb - 192) 2560 D Mc M1 PRES' SDEF DDEF DDEC).
           - rewrite DSCR_EQ; clear; lia.
           - clear; lia. }
  apply (own_mem sb F (sb - 192 + 32) R negz (proj2 SPR) ltac:(clear - SLO; lia) ltac:(clear - FR F8; lia) (BX ++ LB) FF' (sb - 192) 2560 D Mc M1 B9 PRES).
  - left; reflexivity.
  - clear; lia.
  - intros a X. apply DIN in X. clear - X FR FCEIL FBIG. unfold SB. lia.
Qed.

Lemma binv_callee (CTX : mctx) W W1 BX BXa BX1 Mc modelc LKc crc Ac M1 model1 LK1 cr1 A1 SCRc (Wc : list L5.range) :
  binv W BX Mc modelc LKc crc Ac ->
  ahpres L ar (BXa ++ LB) FF' (sb - 192) SCRc Wc Mc M1 ->
  ri_inv HI (BX1 ++ LB) FF' LK1 cr1 A1 M1 (vml_of model1) -> amodel_ok A1 model1 -> model_rt modelc model1 -> incl Ac A1 -> incl LK1 LKc ->
  0 <= SCRc <= 4656 ->
  (forall rr, In rr Wc -> fst rr + snd rr <= ahl_ceil ar) ->
  (forall a, aclient L ar LB FF sp L5PSB.DETAIL_SCRB a -> L5.outside W1 a -> L5.outside Wc a) ->
  (forall a, L5.outside W1 a -> L5.outside W a) ->
  binv W1 BX1 M1 model1 LK1 cr1 A1.
Proof.
  open_ctx CTX. intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9) AH HH1 AM1 RT1 IA1 ILK1 HS WCEIL WOUT WW.
  unfold binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1.
  split. { intros x Hx. apply IA1. apply B4. exact Hx. } split. { intros x Hx. apply B5. apply ILK1. exact Hx. }
  split. { apply (astk_after2 _ _ _ _ _ _ _ (BXa ++ LB) FF' Mc Mc M1 sp L5PSB.DETAIL_SCRB (sb - 192) SCRc Wc B1 B6 (mem_grows_refl Mc) AH).
           - rewrite DSCR_EQ; clear - HS; lia.
           - clear; lia.
           - rewrite DSCR_EQ; clear; lia. }
  split. { eapply ek_trans. { apply (ek_W L ar LB FF sp L5PSB.DETAIL_SCRB W1 W M Mc B7). exact WW. }
           apply (ek_callee L ar LB BXa FF [(F, 2, sb - 192 + 32)] sp L5PSB.DETAIL_SCRB (sb - 192) SCRc W1 Wc Mc M1 AH).
           - rewrite DSCR_EQ; clear - HS; lia.
           - clear; lia.
           - exact WOUT. }
  split. { eapply dk_trans. exact B8. apply (dk_callee L ar LB BXa FF [(F, 2, sb - 192 + 32)] sp L5PSB.DETAIL_SCRB (sb - 192) SCRc Wc Mc M1 AH).
           - rewrite DSCR_EQ; clear - HS; lia.
           - clear; lia. }
  apply (own_callee sb F (sb - 192 + 32) R negz (proj2 SPR) ltac:(clear - SLO; lia) ltac:(clear - FR F8; lia) (BXa ++ LB) FF' (sb - 192) SCRc Wc Mc M1 B9 AH).
  - left; reflexivity.
  - clear; lia.
  - exact WCEIL.
Qed.

(* [comment removed for export] *)
Lemma vis_facts (CTX : mctx) W BX Mc modelc LKc crc Ac :
  binv W BX Mc modelc LKc crc Ac ->
  (L5.writable RSEGS (mrestrict (ahid Ac modelc) Mc) (sb - 192) 208 /\ L5.img_clear (mrestrict (ahid Ac modelc) Mc) 860160 884736 /\
   L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) 911160 2147450880 /\ L5.u32_at RSEGS (mrestrict (ahid Ac modelc) Mc) 911168 1) /\
  own sb F R negz (mrestrict (ahid Ac modelc) Mc) /\
  (L5.defined (mrestrict (ahid Ac modelc) Mc) F 256 /\ L5.writable RSEGS (mrestrict (ahid Ac modelc) Mc) F 256 /\
   L5.writable RSEGS (mrestrict (ahid Ac modelc) Mc) (F / 8 + SB) 32 /\ L5.u64_at RSEGS (mrestrict (ahid Ac modelc) Mc) (F + 248) fl /\
   L5.writable RSEGS (mrestrict (ahid Ac modelc) Mc) fl 1) /\
  (cell_is RSEGS Mc (F + 256 - 8) 8 fl /\ avis (ahid Ac modelc) fl 1 /\ avis (ahid Ac modelc) F 256 /\ avis (ahid Ac modelc) (sb - 192) 208).
Proof.
  open_ctx CTX. intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof (vis_pack L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (_ & VIS8 & _ & VFS8 & _ & _ & VFSSH8 & _).
  pose proof (statics_vis (BX ++ LB) FF' LKc crc Ac Mc modelc B1) as (IMGC8 & CSB8 & CUAR8).
  set (H8 := ahid Ac modelc) in *. set (MV8 := mrestrict H8 Mc) in *.
  assert (SV8 : avis H8 (sb - 192) 208). { apply (VIS8 (sb - 192) 208). clear - SLO; lia. clear - SPR; lia. }
  assert (FV8 : avis H8 F 256) by (apply (VFS8 F 256 FS1 FS2)).
  assert (SHV8 : avis H8 (F / 8 + SB) 32).
  { apply (VFSSH8 (F / 8 + SB) 32). intros i Hi. unfold in_shadow_of, S. clear - Hi FS1 FS2 F8 FR. unfold FS_BYTES, SB in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (W176h : L5.writable RSEGS MV8 (sb - 192) 208).
  { apply (proj2 (writable_vis H8 Mc (sb - 192) 208 SV8 ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar Mc sp). exact B6. rewrite DSCR_EQ. clear; lia. clear; lia. clear; lia. }
  assert (OWN8v : own sb F R negz MV8) by (apply (own_vis sb F R negz (proj2 SPR) H8 Mc B9 SV8 SHV8)).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & WF8 & _).
  assert (FDEF8 : L5.defined MV8 F 256). { apply (proj2 (defined_vis H8 Mc F 256 FV8)). exact (proj1 (proj2 (proj2 (proj2 (proj2 (WF8 _ (or_introl eq_refl))))))). }
  assert (FW8 : L5.writable RSEGS MV8 F 256). { apply (L5C.writable_of_defined RSEGS). exact FDEF8. clear - FR; lia. clear - FR; lia. }
  assert (FSHW8 : L5.writable RSEGS MV8 (F / 8 + SB) 32).
  { apply (L5C.writable_of_defined RSEGS). exact (proj2 (proj2 OWN8v)). clear - FR F8; unfold SB; lia. clear - FR F8; unfold SB; lia. }
  pose proof (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ modelc F 2 _ _ fl HH2 B1 (or_introl eq_refl) (or_introl eq_refl) (or_intror (or_introl eq_refl)) FLC) as [FLC8 FL8].
  change (ff_bytes 2) with 256 in FLC8, FL8. replace (F + 256 - 8) with (F + 248) in FL8 by (clear; lia).
  pose proof (fl_writable L ar C HI LY HIok _ FF' LKc _ Ac Mc _ fl B1 FLP) as [FLD8 FLW8].
  pose proof (fl_vis L ar C HI LY HIok _ FF' LKc _ Ac Mc modelc fl B1 FLP) as FLV8.
  assert (FLW8v : L5.writable RSEGS MV8 fl 1). { apply (proj2 (writable_vis H8 Mc fl 1 FLV8 ltac:(clear - FLR; lia) ltac:(clear - FLR; lia))). exact FLW8. }
  split. { split. exact W176h. split. exact IMGC8. split. exact CSB8. exact CUAR8. }
  split. exact OWN8v.
  split. { split. exact FDEF8. split. exact FW8. split. exact FSHW8. split. exact FL8. exact FLW8v. }
  split. exact FLC8. split. exact FLV8. split. exact FV8. exact SV8.
Qed.

(* [comment removed for export] *)
Definition Wret (a : Z) : Prop := (F <= a < F + 8 \/ F / 8 + SB <= a < F / 8 + SB + 32) \/ a = fl.

Lemma retire_core (CTX : mctx) W BX Mc modelc LKc crc Ac (fx fx9 : FPState) Rc (pc : Z) R9 M9v :
  binv W BX Mc modelc LKc crc Ac ->
  msteps RSEGS (st fx Rc pc (mrestrict (ahid Ac modelc) Mc)) (st fx9 R9 0x8f210 M9v) ->
  mem_grows (mrestrict (ahid Ac modelc) Mc) M9v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wret a -> M9v (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
  L5.u8_at RSEGS M9v fl 0 ->
  getr R9 (reg 1) = Z_to_bv 64 (U R 1) -> getr R9 (reg 2) = Z_to_bv 64 (sb + 16) ->
  (forall k, In k [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R9 (reg k) = Z_to_bv 64 (U R k)) ->
  getr R9 (reg 3) = getr R (reg 3) -> getr R9 (reg 4) = getr R (reg 4) ->
  (forall (Mf : word -> option byte) (modelf : Model),
      regs_preserved R R9 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wret a -> Mf (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      ahpres L ar LB FF sp L5PSB.DETAIL_SCRB W M Mf ->
      model_rt model modelf -> amodel_ok Ac modelf ->
      ri_inv HI (BX ++ LB) FF LKc crc Ac Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fx9) R9 r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc pc Mc modelc) K.
Proof.
  intros BI wMS MG9 wFZ wFL0 wR1 wR2 wRS wR3 wR4 KF.
  destruct (vis_facts CTX W BX Mc modelc LKc crc Ac BI) as (_ & _ & _ & (FLC8 & FLV8 & _ & _)).
  open_ctx CTX. destruct BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof (ret_to fx9 R9 M9v 0x8f210 W_8f210 r F_8f210 eq_refl D_8f210 ltac:(rewrite wR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
  pose proof (msteps_trans _ _ _ _ wMS RET) as MS10. clear wMS RET.
  assert (FLNC8 : ~ aclient L ar (BX ++ LB) FF' 0 0 fl).
  { apply (not_client_bx FF' fl BX LB). apply (blocks_off_fs _ _ _ _ _ _ _ BX LB B1 eq_refl). exact FLP. exact FLBIG. exact FLNC. }
  apply (apiece_retire L ar C HI LY HIok (BX ++ LB) FF LKc crc Ac Mc modelc fx fx9 Rc pc R9 r M9v Wret F 2 (sb - 192 + 32) fl K B1 B2).
  { exact FLC8. }
  { exact FLNC8. }
  { exact FLV8. }
  { clear - FLR; lia. }
  { exact MS10. }
  { exact MG9. }
  { exact wFZ. }
  { intros a Ha Wa. unfold Wret in Wa. destruct Wa as [[Wa|Wa]|Wa].
    - right. apply (fframe_client L ar (BX ++ LB) _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Wa; lia.
    - right. apply (fframe_shadow_client L ar (BX ++ LB) _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256.
      unfold in_shadow_of, S. rewrite (proj1 FQ31). clear - Wa. unfold SB in *. lia.
    - left; exact Wa. }
  { intros a. unfold Wret. repeat match goal with X : _ |- _ => clear X end.
    destruct (rng_dec a F (F + 8)); [left; tauto|]. destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + 32)); [left; tauto|]. destruct (Z.eq_dec a fl); [left; tauto|]. right; tauto. }
  { exact wFL0. }
  intros M9 model9 HH9 AM9 RT9 AH9 VIS9 MGM9 FRM9 EQ9.
  assert (ASTK9 : astk ar M9 sp L5PSB.DETAIL_SCRB). { eapply astk_grows. exact B6. exact MGM9. }
  apply (KF M9 model9).
  - apply preserved_by_index. intros k Hk. unfold cs_all in Hk. cbn [In] in Hk.
    destruct Hk as [<-|Hk]. { rewrite wR2, G2. f_equal. clear; lia. }
    destruct Hk as [<-|Hk]. { exact wR3. }
    destruct Hk as [<-|Hk]. { exact wR4. }
    repeat (destruct Hk as [<-|Hk]; [rewrite wRS by (apply L5K.in_b; vm_compute; reflexivity); symmetry; apply U_to |]). destruct Hk.
  - exact FRM9.
  - apply ahpres_of.
    + eapply ek_trans. exact B7.
      intros a (Ha & Hc & Ho). apply FRM9. exact Ha. unfold Wret. intros [[X|X]|X].
      * apply (NCF a). left; clear - X; lia. exact Hc.
      * apply (NCF a). right. unfold S. rewrite (proj1 FQ31). clear - X. unfold SB in X |- *. lia. exact Hc.
      * subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact Hc.
    + eapply astk_defined. exact ASTK9. clear; lia. clear; lia.
    + eapply dk_trans. exact B8. apply dk_grows. exact MGM9.
  - eapply L5LZ.model_rt_trans. exact B3. exact RT9.
  - exact AM9.
  - exact HH9.
Qed.

(* [comment removed for export] *)
Lemma exit_path (CTX : mctx) (Hdel : opdel_sized_spec L ar HI) W BX BXf (fx : FPState) Rc Mc modelc LKc crc Ac fbv lenv sto ec :
  binv W BX Mc modelc LKc crc Ac -> rinv Rc -> getr Rc (reg 24) = Z_to_bv 64 (F + 96) -> getr Rc (reg 20) = Z_to_bv 64 ec -> 0 <= ec < 2 ^ 64 ->
  L5.big_at RSEGS Mc (F + 96) (L5.BO fbv lenv sto) ->
  match sto with L5.BInl _ _ => BXf = BX | L5.BDyn cap q => In (q, 8 * cap) (BX ++ LB) /\ lb_remove q (BX ++ LB) = BXf ++ LB /\ L5.u64_at RSEGS Mc (sb - 176) (F + 112) end ->
  (forall (fxf : FPState) Rf Mf modelf LKf Af,
      regs_preserved R Rf -> getr Rf (reg 11) = Z_to_bv 64 ec ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BXf ++ LB) FF' (sb - 192) OPDEL_SCR a -> ~ Wret a -> Mf (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      ahpres L ar LB FF sp L5PSB.DETAIL_SCRB W M Mf ->
      model_rt model modelf -> incl A Af -> amodel_ok Af modelf -> incl LKf LK ->
      ri_inv HI (BXf ++ LB) FF LKf crc Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8f09c Mc modelc) K.
Proof.
  intros BI RI G24 G20 HEC VB STO KF.
  destruct (vis_facts CTX W BX Mc modelc LKc crc Ac BI) as ((W176 & IMGC & CSB & CUAR) & OWNv & (FDEFv & FWv & FSHWv & FLCv & FLWv) & (_ & _ & FV & SV)).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  destruct OWNv as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) & (S112 & S144 & S152 & S168) & FSD).
  pose proof RI as (G2' & G8 & G9 & G21 & G26 & G3 & G4').
  pose proof CTX as CTX'. open_ctx CTX'.
  assert (NR : 0 <= negz < 2 ^ 64) by (destruct neg; clear; lia).
  destruct SPR as [SPR0 SPR1].
  assert (ENDX : forall Mx Ax modelx, astk ar Mx sp L5PSB.DETAIL_SCRB -> avis (ahid Ax modelx) (sb - 192) 208 ->
            exists e, 0 <= e < 2 ^ 64 /\ L5.u64_at RSEGS (mrestrict (ahid Ax modelx) Mx) (sb - 136) e).
  { intros Mx Ax modelx AST SVx. apply (defined_word (mrestrict (ahid Ax modelx) Mx) (sb - 136)). 2: clear - SPR1; lia. 2: clear - SPR1; lia.
    apply (proj2 (defined_vis (ahid Ax modelx) Mx (sb - 136) 8 ltac:(eapply avis_sub; [exact SVx | clear; lia | clear; lia]))).
    eapply astk_defined. exact AST. rewrite DSCR_EQ. clear; lia. clear; lia. }
  destruct (ENDX Mc Ac modelc B6 SV) as (e1 & Re1 & ENDe1). fold MV in ENDe1.
  destruct VB as (VB1 & VB2 & VB3 & VB4). cbn [L5.bo_fb L5.bo_len L5.bo_st] in VB1, VB2, VB3, VB4.
  assert (VB1v : L5.u8_at RSEGS MV (F + 96) fbv).
  { apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F + 96) fbv ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))). exact VB1. }
  destruct sto as [v0 v1|cap q].
  - (* [comment removed for export] *)
    subst BXf. destruct VB4 as (VT0 & _).
    pose proof (dtWi_conc fx Rc MV (fun j => match j with 2%nat => sb | 35%nat => negz | 40%nat => F | 41%nat => fl
                  | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 18 | 46%nat => U R 19 | 47%nat => U R 20 | 48%nat => U R 21
                  | 49%nat => U R 22 | 50%nat => U R 23 | 51%nat => U R 24 | 52%nat => U R 25 | 53%nat => U R 26 | 54%nat => U R 27
                  | 57%nat => e1 | 58%nat => U Rc 1 | 59%nat => ec | 60%nat => fbv | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx9 & R9 & M9v & MG9 & wFR & wFZ & (wMS & wKS & wR1 & wR2 & wR8 & wR9 & wR10 & wR11 & wR18 & wR19 & wR20 & wR21 & wR22 & wR23 & wR24 & wR25 & wR26 & wR27 & wFL0 & WSH)).
    apply (retire_core CTX W BX Mc modelc LKc crc Ac fx fx9 Rc 0x8f09c R9 M9v BI wMS MG9).
    + intros a Ha Hna. apply wFZ. exact Ha. all: clear - Hna; unfold Wret in Hna; unfold SB in *; lia.
    + exact wFL0.
    + exact wR1.
    + exact wR2.
    + intros k Hk. cbn [In] in Hk.
      repeat (destruct Hk as [<-|Hk]; [first [exact wR8 | exact wR9 | exact wR18 | exact wR19 | exact wR20 | exact wR21 | exact wR22 | exact wR23 | exact wR24 | exact wR25 | exact wR26 | exact wR27] |]). destruct Hk.
    + rewrite (wKS 3%nat) by inl. exact G3.
    + rewrite (wKS 4%nat) by inl. exact G4'.
    + intros Mf modelf RPf FRMf AHf RTf AMf HHf.
      apply (KF fx9 R9 Mf modelf LKc Ac RPf wR11).
      * intros a Ha _ Hw. apply FRMf. exact Ha. exact Hw.
      * exact AHf.
      * exact RTf.
      * exact B4.
      * exact AMf.
      * exact B5.
      * exact HHf.
  - (* [comment removed for export] *)
    destruct STO as (INq & ELB & VCP). destruct VB4 as (VT1 & VC & VQ & _ & VCR & _ & VQ0 & VQ1 & _).
    assert (VCv : L5.u64_at RSEGS MV (F + 112) cap).
    { apply (proj2 (u64_at_vis (ahid Ac modelc) Mc (F + 112) cap ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))).
      replace (F + 112) with (F + 96 + 16) by (clear; lia). exact VC. }
    assert (VQv : L5.u64_at RSEGS MV (F + 120) q).
    { apply (proj2 (u64_at_vis (ahid Ac modelc) Mc (F + 120) q ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))).
      replace (F + 120) with (F + 96 + 24) by (clear; lia). exact VQ. }
    assert (VCPv : L5.u64_at RSEGS MV (sb - 176) (F + 112)).
    { apply (proj2 (u64_at_vis (ahid Ac modelc) Mc (sb - 176) (F + 112) ltac:(eapply avis_sub; [exact SV | clear; lia | clear; lia]) ltac:(clear - SPR1; lia) ltac:(clear - SPR1; lia))). exact VCP. }
    pose proof (dtWd_conc fx Rc MV (fun j => match j with 2%nat => sb | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 59%nat => ec
                  | 60%nat => fbv | 61%nat => q | 62%nat => cap | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & dFR & dFZ & (dMS & dKS & dR1 & dR10 & dR11)).
    assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply dFZ; exact Ha). subst M1v.
    apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x8f09c R1 OPDEL_SIZED K B1 B2 dMS).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (binv_model W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (Hdel fx1 R1 Mc model1 K (BX ++ LB) FF' LKc crc Ac q (8 * cap) (sb - 192) 585920 HH1 AM1 HK INq).
    + rewrite r10. exact dR10.
    + rewrite r1. exact dR1.
    + split. clear; lia. reflexivity.
    + rewrite r2, (dKS 2%nat) by inl. exact G2'.
    + rewrite r4, (dKS 4%nat) by inl. rewrite G4'. exact G4.
    + replace (sb - 192) with (sp - 208) by (clear; lia). apply (astk_sub ar Mc Mc sp L5PSB.DETAIL_SCRB 208 OPDEL_SCR B6 (mem_grows_refl Mc)).
      clear; lia. rewrite DEL_EQ; clear; lia. rewrite DEL_EQ, DSCR_EQ; clear; lia. replace (sp - 208) with (sb - 192) by (clear; lia). exact SA16.
    + intros fx2 R2 M2' model2' A2 RP2 AH2 RT2 IA2 AM2 HH2'. rewrite ELB in AH2, HH2'.
      assert (BI2 : binv W BXf M2' model2' LKc crc A2).
      { apply (binv_callee CTX W W BX BXf BXf Mc model1 LKc crc Ac M2' model2' LKc crc A2 OPDEL_SCR [] BI1 AH2 HH2' AM2 RT2 IA2 (incl_refl _)).
        - rewrite DEL_EQ; clear; lia.
        - intros rr [].
        - intros a _ _ rr [].
        - intros a X. exact X. }
      assert (RI2 : rinv R2). { apply (rinv_pres R1 R2). apply (rinv_ks Rc R1 KS_dtWd RI dKS). vm_compute; reflexivity. exact RP2. }
      assert (G20' : getr R2 (reg 20) = Z_to_bv 64 ec). { rewrite (cs_of_preserved R1 R2 20 RP2) by inl. rewrite (dKS 20%nat) by inl. exact G20. }
      assert (G24' : getr R2 (reg 24) = Z_to_bv 64 (F + 96)). { rewrite (cs_of_preserved R1 R2 24 RP2) by inl. rewrite (dKS 24%nat) by inl. exact G24. }
      clear W176 IMGC CSB CUAR FDEFv FWv FSHWv FLCv FLWv FV C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 S112 S144 S152 S168 FSD VB1v VCv VQv VCPv ENDe1 dMS dFR dFZ MG1.
      destruct (vis_facts CTX W BXf M2' model2' LKc crc A2 BI2) as ((W176 & IMGC & CSB & CUAR) & OWNv & (FDEFv & FWv & FSHWv & FLCv & FLWv) & (_ & _ & _ & SV2)).
      destruct (ENDX M2' A2 model2' (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 BI2)))))) SV2) as (e2 & Re2 & ENDe2).
      set (MV2 := mrestrict (ahid A2 model2') M2') in *.
      destruct OWNv as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) & (S112 & S144 & S152 & S168) & FSD).
      pose proof RI2 as (H2' & H8 & H9 & H21 & H26 & H3 & H4').
      pose proof (dtW2_conc fx2 R2 MV2 (fun j => match j with 2%nat => sb | 35%nat => negz | 40%nat => F | 41%nat => fl
                    | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 18 | 46%nat => U R 19 | 47%nat => U R 20 | 48%nat => U R 21
                    | 49%nat => U R 22 | 50%nat => U R 23 | 51%nat => U R 24 | 52%nat => U R 25 | 53%nat => U R 26 | 54%nat => U R 27
                    | 57%nat => e2 | 58%nat => U R2 1 | 59%nat => ec | _ => 0 end)) as P.
      cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx9 & R9 & M9v & MG9 & wFR & wFZ & (wMS & wKS & wR1 & wR2 & wR8 & wR9 & wR10 & wR11 & wR18 & wR19 & wR20 & wR21 & wR22 & wR23 & wR24 & wR25 & wR26 & wR27 & wFL0 & WSH)).
      apply (retire_core CTX W BXf M2' model2' LKc crc A2 fx2 fx9 R2 0x8f0c0 R9 M9v BI2 wMS MG9).
      * intros a Ha Hna. apply wFZ. exact Ha. all: clear - Hna; unfold Wret in Hna; unfold SB in *; lia.
      * exact wFL0.
      * exact wR1.
      * exact wR2.
      * intros k Hk. cbn [In] in Hk.
        repeat (destruct Hk as [<-|Hk]; [first [exact wR8 | exact wR9 | exact wR18 | exact wR19 | exact wR20 | exact wR21 | exact wR22 | exact wR23 | exact wR24 | exact wR25 | exact wR26 | exact wR27] |]). destruct Hk.
      * rewrite (wKS 3%nat) by inl. exact H3.
      * rewrite (wKS 4%nat) by inl. exact H4'.
      * intros Mf modelf RPf FRMf AHf RTf AMf HHf.
        apply (KF fx9 R9 Mf modelf LKc A2 RPf wR11).
        -- intros a Ha Hc Hw. rewrite (FRMf a Ha Hw). apply (proj1 AH2). split. exact Ha. split. exact Hc. intros rr [].
        -- exact AHf.
        -- exact RTf.
        -- intros x Hx. apply IA2. apply B4. exact Hx.
        -- exact AMf.
        -- exact B5.
        -- exact HHf.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma stksh_now (CTX : mctx) BX Mc modelc LKc crc Ac lo : binv [] BX Mc modelc LKc crc Ac -> sp - L5PSB.DETAIL_SCRB <= lo -> lo mod 8 = 0 -> L5ASB.stksh ar Mc lo.
Proof.
  open_ctx CTX. intros (_ & _ & _ & _ & _ & _ & B7 & _) H1 H8 j Hj. unfold byte_at.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP47 & _).
  unfold L5ASB.stksh in SSH. rewrite DSCR_EQ in *.
  assert (E : HeapIfaceA.S lo + j = HeapIfaceA.S (sp - 4864) + ((lo - (sp - 4864)) / 8 + j) /\ 0 <= (lo - (sp - 4864)) / 8 + j < (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 4864)) / 8).
  { unfold HeapIfaceA.S. clear - H1 H8 Hj SA32. unfold aligned in SA32. Lia.lia. }
  destruct E as [E ER]. rewrite E. rewrite B7. apply SSH. exact ER.
  split. { unfold HeapIfaceA.S, SB. clear - ER SPR SPT SLO TOP47. Lia.lia. }
  split. 2:{ intros rr []. }
  right; right; right; right; left. unfold in_shadow_of, HeapIfaceA.S. clear - ER SLO SHI SPT SPR SA32 TOP47. unfold aligned in SA32. unfold SB. Lia.lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

End CTX.
End WithIface.
End SCFG_1.
End L5ADH.
