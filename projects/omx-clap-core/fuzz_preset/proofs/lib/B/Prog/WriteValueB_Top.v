(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d), lane of write_value, under a Theorem Labs session: THE
   INDUCTION of write_value's walk on the depth n, over the draft's text of record twrite_value_specX
   (lib/A/PRH_FnWriter.v, lib/A/PRH_Base.v), at EVERY float state:
   - depth 0 and the leaves of any depth (null / false / true / number / string): WriteValueB_Leaf's five leaves; the
     literal and number leaves end in put's non-float post's R form fpostWmR (at wle' SEGS RZ_cf) at the entry float
     state, which is the float-form post's R form fpostWFmR by the ONE float lemma WriteValueB_Defs.wv_fpostW_FR
     (the entry rounding mode is 0: fpre's FRM0-ENTRY conjunct; the callee-saved f registers are the entry's own);
   - a container at depth S n': the container walk's three lemmas, here the Section hypotheses CONT / LOOP / CLOSE in
     the statements of WriteValueB_Cont.wv_cont / WriteValueB_Iter.wv_loop / WriteValueB_Close.wv_close (the
     composition file binds them), at the runner's memory invariant Pm := the memnorm keep from the entry, with the
     depth-n' text at every float state as the loop's induction hypothesis.
   The callee texts are the texts of record at EVERY float state (put_string and write_value itself exit at a new float state,
   so the calls after them run there). Numerals: 200 (LENGTH: write_value's frame 192 + 8). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import WriteValueB_Model WriteValueB_Base WriteValueB_Call
  WriteValueB_Leaf WriteValueB_Defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Set Default Proof Using "All".
(* NO float state in the Section context: every lemma below quantifies its own (the walk changes it), and every
   text / pre / post names it explicitly *)
Section d. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Section f.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib B.
(* image facts of the instance, discharged at PI_prog_B (B_entry_write_value / B_prog_obj_img) *)
Hypothesis Hent : SIGMA AS_write_value = BASE + AF_write_value.
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
(* ---- IMAGE FACTS OF THE INSTANCE (discharged at PI_prog_B, WriteValueB_Inst), both read off the generated
   listing ----
   the tag switch's seven table words: each is a ROM word of the read-only band, apart from the GOT word and from
   the shadow-base cell, and inside the image's low range *)
Hypothesis HJT : forall k : nat, (k < 7)%nat ->
  val_mem SEGS (fun _ => None) (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) 4 (WV_JTW k) /\
  0 <= WV_JTW k <= 2 ^ 31 - 1 /\
  0 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k /\
  VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= kLowMemEnd /\
  (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= VAL (A_OBJ 0) \/
   VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) /\
  (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= VAL (A_OBJ 12) \/
   VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) /\
  (forall i, 0 <= i < 4 -> in_img SEGS (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i) /\
     in_roP SEGS pa_relro_lo pa_relro_hi (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i) /\
     ~ Exists (in_zr (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i)) (as_owned_static B) /\
     ~ (as_errno B <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i < as_errno B + 4)).
(* and the literals: at any state of the run each is a legal put source whose home is kept (put_string's HLIT17
   shape), its bytes being the image's *)
Hypothesis HLIT : forall (k : nat) (bs : list Z) ly' S' Hp' (W' : world SEGS) m' md',
  In (k, bs) wv_lits ->
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m') ->
  src_rd W' m' (WV_STR k) bs /\ kept_at B [] (WV_STR k) (Z.of_nat (length bs)) /\
  (forall i, 0 <= i < Z.of_nat (length bs) -> in_img SEGS (WV_STR k + i)).
(* IMAGE FACT (discharged at PI_prog_B, WriteValueB_Inst): no static of alloc.c lies in the read-only band, so
   a journal's image clause keeps the band (the same text as put_string's and pj_write's walks) *)
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_B).


Section cl.
Variable CTX0 : list (list Z).
(* the callee texts, the draft's texts of record VERBATIM (lib/A/PRH_FnWriter.v), at every float state; owners: put (tput_specX) the put lane,
   put_string (tput_string_specX) the put_string lane, indent (tindent_specX) the indent lane; strlen: the engine's row
   YGcallMxmn.astrlen_realizes_xrom (a Theorem Labs lane) *)
Hypothesis PUT : forall fx' : YK11.FPState, tput_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis PUTSTR : forall fx' : YK11.FPState,
  tput_string_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis INDENT : forall fx' : YK11.FPState,
  tindent_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
(* the head is at least one shadow granule wide (PRH_Base.v's one spelling; at the instance the allocator-model owner's preset_head_wide) *)
Hypothesis HW : prh_head_wide.
Hypothesis STRLEN : forall fx' : YK11.FPState,
  YGcallMxmn.astrlen_realizes_xrom (fx := fx') SEGS B ARx pa_relro_lo pa_relro_hi (SIGMA AS___wrap_strlen).
(* THE CONTAINER WALK's three lemmas, in their statements (WriteValueB_Cont / _Iter / _Close; bound in the
   composition file). The container's run crosses its puts' grows, so the joins' continuations are the combinators'
   R-forms at wle' SEGS RZ_cf and the walk concludes SRr' *)
Hypothesis CONT : forall (fx : YK11.FPState) (Pm : (word -> option byte) -> Prop) (PLAW : srr_inv_laws SEGS Pm)
  (PCALL : srr_inv_call SEGS Pm) (n' : nat) (X : wvx) ch,
  y_fx X = fx ->
  (exists l, y_t X = PjTree.JArr l) \/ (exists l, y_t X = PjTree.JObj l) ->
  STK_write_value (S n') <= y_STK X -> wv_pre B ARx CTX0 Pm X ch ->
  wv_HEADKR B ARx Pm (wle' SEGS RZ_cf) X -> wv_CLOSEKR B ARx Pm (wle' SEGS RZ_cf) X ->
  SRr' SEGS RZ_cf (y_W X) (cfg_at (fx := fx) SEGS (SIGMA AS_write_value) (y_regs X) (y_mem X) (y_md X))
    (wv_Qfin B ARx Pm X).
Hypothesis LOOP : forall (Pm : (word -> option byte) -> Prop) (PLAW : srr_inv_laws SEGS Pm)
  (PCALL : srr_inv_call SEGS Pm) (n' : nat) (X : wvx) ch,
  (forall fx' : YK11.FPState, twrite_value_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n') ->
  STK_write_value (S n') <= y_STK X -> (PjTree.depth (y_t X) <= S n')%nat -> wv_pre B ARx CTX0 Pm X ch ->
  wv_CLOSEKR B ARx Pm (wle' SEGS RZ_cf) X -> wv_HEADKR B ARx Pm (wle' SEGS RZ_cf) X.
Hypothesis CLOSE : forall (Pm : (word -> option byte) -> Prop) (PLAW : srr_inv_laws SEGS Pm)
  (PCALL : srr_inv_call SEGS Pm) (n' : nat) (X : wvx) ch,
  (exists l, y_t X = PjTree.JArr l) \/ (exists l, y_t X = PjTree.JObj l) ->
  STK_write_value (S n') <= y_STK X -> wv_pre B ARx CTX0 Pm X ch ->
  wv_CLOSEKR B ARx Pm (wle' SEGS RZ_cf) X.


(* the stack need at depth 0 covers each leaf's tail callee (numerals of the instance) *)
Lemma wv_stk_mono : forall n, STK_write_value 0 <= STK_write_value n.
Proof.
intros n. unfold STK_write_value.
assert (Hf : 0 <= pi_frame F_write_value) by (vm_compute; congruence).
assert (Hn : 1 <= Z.of_nat (S n)) by lia. nia.
Qed.
Lemma wv_stk_leaf : 200 + STK_RT_STR <= STK_write_value 0 /\ STK_put <= STK_write_value 0 /\
  STK_put_string <= STK_write_value 0.
Proof. repeat split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* THE FLOAT POST OF THE NON-FLOAT LEAVES (the ONE float lemma per arm, FRM0-ENTRY): put's post at the entry float
   state is the text's float-form post, the entry rounding mode being 0 (fpre's last conjunct); both at the move's
   relation wle' SEGS RZ_cf *)
Lemma wv_leaf_F : forall (fx : YK11.FPState) STK d FP (regs : bvmap 5 word) ly S Hp (W : world SEGS) mem md ch
  Q W' c',
  fpre (fx := fx) B ARx STK ly S Hp W regs mem md ch ->
  fpostWmR (fx := fx) B ARx SK (wle' SEGS RZ_cf) STK d FP regs ly S Hp W mem md Q W' c' ->
  fpostWFmR (fx := fx) B ARx SK (wle' SEGS RZ_cf) STK d FP regs ly S Hp W mem md Q W' c'.
Proof.
intros fx STK d FP regs ly S Hp W mem md ch Q W' c' (_ & _ & _ & _ & Hz) H.
exact (wv_fpostW_FR (fx := fx) B ARx (wle' SEGS RZ_cf) fx STK d FP regs ly S Hp W mem md (fQmn mem Q) W' c' Hz
  (wv_fregs_kept_refl fx) H).
Qed.

(* ONE STEP OF THE INDUCTION: the text at depth n at the float state fx, from the text at depth n - 1 at every float
   state *)
Lemma wv_text_core : forall (fx : YK11.FPState) (n : nat),
  (forall n', n = S n' -> forall fx' : YK11.FPState,
     twrite_value_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n') ->
  twrite_value_specX (fx := fx) (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n.
Proof.
intros fx n IHS.
pose proof wv_stk_leaf as (SL1 & SL2 & SL3).
assert (SL0 : 0 <= STK_RT_STR) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (wv_stk_mono n) as SLm.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o v pretty dep d buf st t D Lam peak ran
  HPRE Hroom Hrp Hlen4 Hcons Hcl H10 H11 H12 H13 Hpr Hdep Hdd Hdn Hcut Hch0 HS0 HWIN Ho1 Ho2 HOUT HLED Hev HNODE HLOC HRA HTV HD
  Hoff Hfr Hwmax Hhead Hlive.
destruct t as [ | | | txt bits | s | items | members ].
(* the leaves *)
- eapply (SRr'_mono SEGS RZ_cf);
  [ eapply (@WriteValueB_Leaf.wv_leaf_lit fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx) HW (STRLEN fx) PjTree.JNull (or_introl eq_refl) rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch) with (STKv := STK_write_value n);
    try eassumption; lia
  | intros W' c' _ HQ; exact (wv_leaf_F fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPRE HQ) ].
- eapply (SRr'_mono SEGS RZ_cf);
  [ eapply (@WriteValueB_Leaf.wv_leaf_lit fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx) HW (STRLEN fx) PjTree.JFalse (or_intror (or_introl eq_refl)) rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W
      regs mem md ch) with (STKv := STK_write_value n); try eassumption; lia
  | intros W' c' _ HQ; exact (wv_leaf_F fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPRE HQ) ].
- eapply (SRr'_mono SEGS RZ_cf);
  [ eapply (@WriteValueB_Leaf.wv_leaf_lit fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx) HW (STRLEN fx) PjTree.JTrue (or_intror (or_intror eq_refl)) rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W
      regs mem md ch) with (STKv := STK_write_value n); try eassumption; lia
  | intros W' c' _ HQ; exact (wv_leaf_F fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPRE HQ) ].
- eapply (SRr'_mono SEGS RZ_cf);
  [ eapply (@WriteValueB_Leaf.wv_leaf_num fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx) HW (STRLEN fx) txt bits rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch) with (STKv := STK_write_value n); try eassumption; lia
  | intros W' c' _ HQ; exact (wv_leaf_F fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPRE HQ) ].
- eapply (@WriteValueB_Leaf.wv_leaf_str fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx) HW (STRLEN fx) s rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch) with (STKv := STK_write_value n); try eassumption; lia.
(* the containers: depth at least 1, so n = S n' *)
- destruct n as [|n']; [exfalso; cbn [PjTree.depth] in Hdn; lia|].
  pose proof (IHS n' eq_refl) as IH.
  pose (X := mkWVX fx d (STK_write_value (Datatypes.S n')) ly S Hp W regs mem md o v pretty dep buf st (PjTree.JArr items) D Lam
    peak ran most own rp_sm rp_x rp_os rp_i rp_H0 rp_hist).
  pose (Pm := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
  assert (PLAW : srr_inv_laws SEGS Pm) by (apply srr_inv_laws_imp; apply srr_inv_laws_memnorm_k).
  assert (PCALL : srr_inv_call SEGS Pm) by (apply srr_inv_call_imp).
  assert (HP : wv_pre B ARx CTX0 Pm X ch)
    by exact (conj HPRE (conj Hroom (conj Hrp (conj Hcl (conj H10 (conj H11 (conj H12 (conj H13 (conj Hpr (conj Hdep
      (conj Hdd (conj Hcut (conj Hch0 (conj HS0 (conj HWIN (conj Ho1 (conj Ho2 (conj HOUT (conj HLED (conj Hev
      (conj HNODE (conj HLOC (conj HRA (conj HTV (conj HD (conj Hoff (conj Hfr (conj Hwmax (conj Hhead (conj Hlive
      (conj (fun h => h) (conj Hcons Hlen4)))))))))))))))))))))))))))))))).
  assert (HSH : (exists l, y_t X = PjTree.JArr l) \/ (exists l, y_t X = PjTree.JObj l))
    by exact (or_introl (ex_intro _ _ eq_refl)).
  pose proof (CLOSE Pm PLAW PCALL n' X ch HSH (Z.le_refl _) HP) as HCL.
  pose proof (CONT fx Pm PLAW PCALL n' X ch eq_refl HSH (Z.le_refl _) HP
    (LOOP Pm PLAW PCALL n' X ch IH (Z.le_refl _) Hdn HP HCL) HCL) as HC.
  eapply (SRr'_mono SEGS RZ_cf); [exact HC|].
  intros W2 c2 _ ((fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k & Hc2 & HZ2 & HK2 & HJ2 & HW2 & HP2 & HQ) & HPm2).
  exists fx2, ly2, S2, Hp2, regs2, mem2, md2, k.
  split; [exact Hc2|]; split; [exact HZ2|]; split; [exact HK2|]; split; [exact HJ2|]; split; [exact HW2|];
    split; [exact HP2|].
  split; [exact HQ | subst c2; exact HPm2].
- destruct n as [|n']; [exfalso; cbn [PjTree.depth] in Hdn; lia|].
  pose proof (IHS n' eq_refl) as IH.
  pose (X := mkWVX fx d (STK_write_value (Datatypes.S n')) ly S Hp W regs mem md o v pretty dep buf st (PjTree.JObj members) D
    Lam peak ran most own rp_sm rp_x rp_os rp_i rp_H0 rp_hist).
  pose (Pm := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
  assert (PLAW : srr_inv_laws SEGS Pm) by (apply srr_inv_laws_imp; apply srr_inv_laws_memnorm_k).
  assert (PCALL : srr_inv_call SEGS Pm) by (apply srr_inv_call_imp).
  assert (HP : wv_pre B ARx CTX0 Pm X ch)
    by exact (conj HPRE (conj Hroom (conj Hrp (conj Hcl (conj H10 (conj H11 (conj H12 (conj H13 (conj Hpr (conj Hdep
      (conj Hdd (conj Hcut (conj Hch0 (conj HS0 (conj HWIN (conj Ho1 (conj Ho2 (conj HOUT (conj HLED (conj Hev
      (conj HNODE (conj HLOC (conj HRA (conj HTV (conj HD (conj Hoff (conj Hfr (conj Hwmax (conj Hhead (conj Hlive
      (conj (fun h => h) (conj Hcons Hlen4)))))))))))))))))))))))))))))))).
  assert (HSH : (exists l, y_t X = PjTree.JArr l) \/ (exists l, y_t X = PjTree.JObj l))
    by exact (or_intror (ex_intro _ _ eq_refl)).
  pose proof (CLOSE Pm PLAW PCALL n' X ch HSH (Z.le_refl _) HP) as HCL.
  pose proof (CONT fx Pm PLAW PCALL n' X ch eq_refl HSH (Z.le_refl _) HP
    (LOOP Pm PLAW PCALL n' X ch IH (Z.le_refl _) Hdn HP HCL) HCL) as HC.
  eapply (SRr'_mono SEGS RZ_cf); [exact HC|].
  intros W2 c2 _ ((fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k & Hc2 & HZ2 & HK2 & HJ2 & HW2 & HP2 & HQ) & HPm2).
  exists fx2, ly2, S2, Hp2, regs2, mem2, md2, k.
  split; [exact Hc2|]; split; [exact HZ2|]; split; [exact HK2|]; split; [exact HJ2|]; split; [exact HW2|];
    split; [exact HP2|].
  split; [exact HQ | subst c2; exact HPm2].
Qed.

(* THE INDUCTION ON THE DEPTH, at every float state (the loop's recursive calls run at the float state the previous
   callee left) *)
Theorem wv_text_all : forall (n : nat) (fx : YK11.FPState),
  twrite_value_specX (fx := fx) (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n.
Proof.
induction n as [|n IHn]; intros fx; apply wv_text_core.
- intros n' Hn. discriminate Hn.
- intros n' Hn. injection Hn as <-. exact IHn.
Qed.

End cl.
End h.
End f.
End d.
