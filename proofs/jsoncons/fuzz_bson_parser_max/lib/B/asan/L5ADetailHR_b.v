(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue BigModel BigFactsRun BigFactsDigits L5Defs L5Kn L5KnA L5Core L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore AsanPlanSound. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_lin P := lazymatch type of P with ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T) in P) | _ => idtac end.
Local Ltac pvz_clrT := repeat match goal with T := (_ /\ _) : Prop |- _ => clear T end.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADHR.
Import L5A. Import L5CA. Import L5CSA. Import L5SAR. Import L5CBR. 
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
(* [comment removed for export] *)
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
#[using="Type"] Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
#[using="Type"] Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
#[using="Type"] Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
#[using="Type"] Lemma r13 : (13%bv : bv 5) = reg 13. Proof. apply bv_eq; reflexivity. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma byte_of_u8 M a v : L5.u8_at RSEGS M a v -> (a < 0x10000 \/ 0x696000 <= a) -> 0 <= a < 2 ^ 64 -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
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
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.

#[using="SCFG_P L ar C LY HIok"] Lemma statics_vis LB FF LK cr A M model :
  ri_inv HI LB FF LK cr A M (vml_of model) ->
  let MV := mrestrict (ahid A model) M in
  L5.img_clear MV 1249280 1282048 /\ L5.u64_at RSEGS MV 1309752 2147450880 /\ L5.u32_at RSEGS MV 1309760 1.
Proof.
  intros HH. pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (aly_segs L C LY) in ST.
  pose proof (statics_facts L C M LY ST) as (IMGC & CSB & CUAR & _).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & VIMG & _).
  split. apply img_clear_mrestrict. exact IMGC.
  split. apply (proj2 (u64_at_vis _ M _ _ (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CSB.
  apply (proj2 (u32_at_vis _ M _ _ (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CUAR.
Qed.

(* [comment removed for export] *)
#[using="C LY LY2 ILY"] Lemma ek_bytes LB FF sp scr M Mk p (s : list Z) :
  ek L ar LB FF sp scr [] M Mk -> asrc IL LB FF M p (Z.of_nat (length s)) -> 0 <= p -> p + Z.of_nat (length s) <= 2 ^ 64 ->
  L5.bytes_at RSEGS M p s -> L5.bytes_at RSEGS Mk p s.
Proof.
  intros EK SRC P0 P1 B. eapply L5C.bytes_at_agree. 4: exact B. 2: exact P0. 2: exact P1.
  intros i Hi. apply EK. split. lia. split. replace i with (p + (i - p)) by lia. apply (asrc_client L ar C IL LY LY2 ILY LB FF M sp scr p _ (i - p) SRC). lia. intros rr [].
Qed.
#[using="SCFG_P C LY HIok"] Lemma ek_src LB FF LK cr A sp scr M model Mk LB' FF' p m :
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
  L5.u64_at RSEGS M (sb - 112) F /\ L5.u64_at RSEGS M (sb - 136) F /\ L5.u64_at RSEGS M (sb - 144) negz.
#[using="Type"] Lemma frk_agree sb R M M' : frk sb R M -> (forall a, sb - 88 <= a < sb + 16 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> 160 <= sb -> sb + 16 <= 2 ^ 64 -> frk sb R M'.
Proof.
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) AG H0 H1. unfold frk.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
#[using="Type"] Lemma spk_agree sb F negz M M' : spk sb F negz M -> (forall a, sb - 144 <= a < sb - 104 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> 160 <= sb -> sb + 16 <= 2 ^ 64 -> spk sb F negz M'.
Proof.
  intros (C1 & C2 & C3) AG H0 H1. unfold spk.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma stack_callee LBk FFk spc SCR W M M' a :
  ahpres L ar LBk FFk spc SCR W M M' -> (forall rr, In rr W -> fst rr + snd rr <= ahl_ceil ar) -> 0 <= a -> ahl_ceil ar <= a < 2 ^ 47 -> spc <= a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros (E & _) HW H0 Ha Hs. apply E. split. lia. split. apply stack_client. exact Ha. lia.
  intros rr Hr X. specialize (HW rr Hr). unfold L5.in_rng in X. lia.
Qed.
#[using="Type"] Lemma stack_rt LBk FFk spc scr M M' a :
  aheap_pres L ar LBk FFk spc scr M M' -> 0 <= a -> ahl_ceil ar <= a < 2 ^ 47 -> spc <= a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof. intros (E & _) H0 Ha Hs. apply E. lia. apply stack_client. exact Ha. lia. Qed.

(* [comment removed for export] *)
Section OWN.
Variables (sb F rs : Z) (R0 : bvmap 5 word) (negz : Z).
Hypothesis SBR : 140735332487488 <= sb <= 140737488355312.
Hypothesis SBC : ahl_ceil ar + 4096 <= sb - 160.
Hypothesis FRR : 4096 <= F /\ F + 256 <= 2 ^ 47 /\ (F / 8) * 8 = F.
Definition own (M : word -> option byte) : Prop := frk sb R0 M /\ spk sb F negz M /\ L5.defined M (F / 8 + SB) 32.
#[using="SBR"] Lemma own_agree M M' : own M -> (forall a, sb - 144 <= a < sb + 16 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, F / 8 + SB <= a < F / 8 + SB + 32 -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) -> own M'.
Proof.
  intros (K1 & K2 & K3) AG DF. split. apply (frk_agree sb R0 M M' K1). intros a Ha. apply AG. lia. lia. lia.
  split. apply (spk_agree sb F negz M M' K2). intros a Ha. apply AG. lia. lia. lia.
  intros i Hi. apply DF. lia. apply K3. exact Hi.
Qed.
#[using="SBR"] Lemma own_piece M M' (W : Z -> Prop) : own M -> (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_grows M M' ->
  (forall a, sb - 144 <= a < sb + 16 -> ~ W a) -> own M'.
Proof. intros O FRM MG NW. apply (own_agree M M' O). intros a Ha. apply FRM. lia. apply NW. exact Ha. intros a _ X. apply MG. exact X. Qed.
#[using="SBR SBC FRR"] Lemma own_rt LBk FFk spc scr M M' : own M -> aheap_pres L ar LBk FFk spc scr M M' -> In (F, 2, rs) FFk -> spc <= sb - 144 -> own M'.
Proof.
  intros O PRES INF Hs. apply (own_agree M M' O).
  - intros a Ha. apply (stack_rt LBk FFk spc scr M M' a PRES). lia. lia. lia.
  - intros a Ha X. rewrite (proj1 PRES a). exact X. unfold SB in Ha. lia.
    apply (fframe_shadow_client L ar LBk FFk spc scr F 2 rs). exact INF. change (ff_bytes 2) with 256. unfold in_shadow_of, S. destruct FRR as (F0 & F1 & F8).
    clear - Ha F8. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[using="SBR SBC FRR"] Lemma own_callee LBk FFk spc SCR W M M' : own M -> ahpres L ar LBk FFk spc SCR W M M' -> In (F, 2, rs) FFk -> spc <= sb - 144 ->
  (forall rr, In rr W -> fst rr + snd rr <= ahl_ceil ar) -> own M'.
Proof.
  intros O AH INF Hs HW. apply (own_agree M M' O).
  - intros a Ha. apply (stack_callee LBk FFk spc SCR W M M' a AH HW). lia. lia. lia.
  - intros a Ha X. apply (proj2 (proj2 AH) a). unfold SB in Ha. lia. 2: exact X.
    apply (fframe_shadow_client L ar LBk FFk spc SCR F 2 rs). exact INF. change (ff_bytes 2) with 256. unfold in_shadow_of, S. destruct FRR as (F0 & F1 & F8).
    clear - Ha F8. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[using="SBR SBC FRR"] Lemma own_mem LBk FFk spc scr (D : Z -> Prop) M M' : own M ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBk FFk spc scr a -> ~ D a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  In (F, 2, rs) FFk -> spc <= sb - 144 -> (forall a, D a -> a < ahl_ceil ar /\ ~ (F / 8 + SB <= a < F / 8 + SB + 32)) -> own M'.
Proof.
  intros O PRES INF Hs HD. apply (own_agree M M' O).
  - intros a Ha. apply PRES. lia. apply stack_client. lia. lia. intros X. apply HD in X. lia.
  - intros a Ha X. rewrite PRES. exact X. unfold SB in Ha. lia. 2:{ intros Y. apply HD in Y. tauto. }
    apply (fframe_shadow_client L ar LBk FFk spc scr F 2 rs). exact INF. change (ff_bytes 2) with 256. unfold in_shadow_of, S. destruct FRR as (F0 & F1 & F8).
    clear - Ha F8. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[using="SBR"] Lemma own_vis H M : own M -> avis H (sb - 160) 176 -> avis H (F / 8 + SB) 32 -> own (mrestrict H M).
Proof.
  intros O V1 V2. apply (own_agree M (mrestrict H M) O).
  - intros a Ha. apply mrestrict_visible. replace a with ((sb - 160) + (a - (sb - 160))) by lia. apply V1. lia.
  - intros a Ha X. rewrite mrestrict_visible. exact X. replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by lia. apply V2. lia.
Qed.
End OWN.

(* [comment removed for export] *)
#[using="SCFG_P C LY HIok"] Lemma ek_obj LB FF LK cr A sp scr M model Mk o :
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
#[using="L ar C LY HIok"] Lemma apure LB FF LK cr A M model (fx fx1 : FPState) Ra (pc : Z) Rb (pc1 : Z) K :
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
#[using="SCFG_P C HIok"] Lemma astk_after2 LB0 FF0 LK0 cr0 A0 M0 V0 LBk FFk M M1 M2 sp scr sp' scr' W :
  ri_inv HI LB0 FF0 LK0 cr0 A0 M0 V0 ->
  astk ar M sp scr -> mem_grows M M1 -> ahpres L ar LBk FFk sp' scr' W M1 M2 ->
  sp - scr <= sp' - scr' -> sp' <= sp -> 0 <= scr -> astk ar M2 sp scr.
Proof.
  intros HH (A16 & SLO & SHI & SPT & DSCR & DUP) MG (PRES & SDEF & DK) H1 H2 H0.
  assert (D : forall x, (sp - scr <= x < sp \/ sp <= x < ar_stack_top ar) -> M2 (Z_to_bv 64 x) <> None).
  { intros x Hx2. destruct (rng_dec x (sp' - scr') sp') as [I|O].
    - replace x with (sp' - scr' + (x - (sp' - scr'))) by lia. apply SDEF. lia.
    - pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
      apply DK. lia. apply stack_client. lia. exact O. apply MG. destruct (Z_lt_le_dec x sp).
      + replace x with (sp - scr + (x - (sp - scr))) by lia. apply DSCR. lia.
      + replace x with (sp + (x - sp)) by lia. apply DUP. lia. }
  split. exact A16. split. lia. split. lia. split. exact SPT. split.
  - intros j Hj. apply D. lia.
  - intros j Hj. apply D. lia.
Qed.

#[using="Type"] Lemma lb_remove_head q nq LBx : lb_remove q ((q, nq) :: LBx) = LBx.
Proof. cbn. rewrite Z.eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma lb_remove_skip q q' m LBx : q' <> q -> lb_remove q ((q', m) :: LBx) = (q', m) :: lb_remove q LBx.
Proof. intros NE. cbn. destruct (Z.eqb_spec q' q). contradiction. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma not_client_bx FFx a : forall BX LBx,
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
#[using="SCFG_P C HIok"] Lemma blocks_off_fs LBx FFx LKx crx Ax Mx Vx BX LBy : ri_inv HI LBx FFx LKx crx Ax Mx Vx -> LBx = BX ++ LBy ->
  forall b, In b BX -> ablock_range L ar (fst b) (snd b) /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + FS_BYTES <= fst b).
Proof.
  intros HH E b Hb. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB b ltac:(rewrite E; apply in_or_app; left; exact Hb)) as (BR & _ & _ & _ & _ & _ & BFS). split. exact BR. exact BFS.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithIface.
End SCFG_1.
End L5ADHR.
