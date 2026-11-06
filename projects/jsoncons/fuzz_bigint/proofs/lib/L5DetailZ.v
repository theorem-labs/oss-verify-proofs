(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_20088_210bc BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkDq BigLinkReduce BigZskip
     BigModel BigFactsBase BigFactsOps BigFactsRun BigFactsDigits
     L5Defs L5Core L5CoreKit L5CoreSpecs L5KnP L5ParseArith L5ParseKit L5ParseSpecs L5DetailA ZskipAll.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto.

Module L5DETZ.
Import L5CS L5PS L5DA.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition DRET : Z := 0x20d34.      (* [comment removed for export] *)
Definition ZHEAD : Z := 0x20bf4.     (* [comment removed for export] *)
Definition ZBR : Z := 0x20c04.       (* [comment removed for export] *)
Definition DL_HEAD : Z := 0x20c98.
Definition DL_EXIT : Z := 0x20cc8.
Definition DL_ERR : Z := 0x20d38.
Ltac uscr := unfold DETAIL_SCR, ADDD_SCR, MUL10_SCR, ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_detail fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R DRET M) (st fx R r M).
Proof. intros H1 Hr He. apply (BRED.ret_to fx R M DRET W_20d34 r F_20d34 eq_refl D_20d34 H1 Hr He). Qed.

Lemma br_20acc fx R M :
  msteps RSEGS (st fx R ZBR M) (st fx R (if branch_taken BC_EQ (getr R (reg 10)) (getr R (reg 8)) then 0x20c18 else 0x20c08) M).
Proof.
  rewrite <- L5CoreKit.L5K.rl10, <- L5CoreKit.L5K.rl8.
  apply (@BDQ.br_site fx M R ZBR 0x20c18 (0x20c04%bv : word) _ BC_EQ 10 8 _ eq_refl F_20c04 eq_refl D_20c04). vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land3_bits fb : 0 <= fb -> Z.land fb 3 = 0 -> Z.testbit fb 0 = false /\ Z.testbit fb 1 = false.
Proof.
  intros Hfb H. split.
  - apply (f_equal (fun x => Z.testbit x 0)) in H. rewrite Z.land_spec in H. change (Z.testbit 3 0) with true in H. rewrite Bool.andb_true_r in H. rewrite H. reflexivity.
  - apply (f_equal (fun x => Z.testbit x 1)) in H. rewrite Z.land_spec in H. change (Z.testbit 3 1) with true in H. rewrite Bool.andb_true_r in H. rewrite H. reflexivity.
Qed.
Lemma lit_of_word (w : word) : Z_to_bv 64 (bv_unsigned w) = w.
Proof. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma wrange (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia. Qed.
Lemma ra_ok_lit z : 0 <= z < 2 ^ 47 -> z mod 2 = 0 -> L5.ra_ok z.
Proof. intros; split; assumption. Qed.

Lemma mod16_8 sp k : sp mod 16 = 0 -> (sp + 8 * k) mod 8 = 0.
Proof.
  intros H. apply Z.mod_divide in H. 2: lia. destruct H as [q Hq]. subst sp.
  replace (q * 16 + 8 * k) with ((q * 2 + k) * 8) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma big_at_zero M a : L5.u8_at RSEGS M a 0 -> L5.u64_at RSEGS M (a + 8) 0 -> L5.u64_at RSEGS M (a + 16) 0 -> L5.u64_at RSEGS M (a + 24) 0 ->
  L5.big_at RSEGS M a (L5.BO 0 0 (L5.BInl 0 0)).
Proof. intros H0 H8 H16 H24. unfold L5.big_at; cbn. repeat split; try assumption; try lia; reflexivity. Qed.
Lemma obj_limbs_zero M : L5C.obj_limbs RSEGS M (L5.BO 0 0 (L5.BInl 0 0)) [].
Proof. unfold L5C.obj_limbs; cbn. repeat split. constructor. Qed.

(* [comment removed for export] *)
Lemma segs_below : forallb (fun seg => Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) 0x91000) RSEGS = true.
Proof. vm_compute. reflexivity. Qed.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis Hres : reserve_spec L HI.
Hypothesis Hmul : mul10_spec L HI.
Hypothesis Hadd : addd_spec L HI.
Hypothesis Hasg : assign_spec L HI.
Hypothesis Hdel : opdel_sized_spec L HI.
(* [comment removed for export] *)
Hypothesis KPOS : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_overhead L.

Lemma credit_le_refl c : credit_le c c. Proof. unfold credit_le. lia. Qed.
Lemma credit_le_trans a b c : credit_le a b -> credit_le b c -> credit_le a c. Proof. unfold credit_le. lia. Qed.
Lemma credit_le_debit c n : 0 <= n -> credit_le (debit L c n) c.
Proof. intros Hn. unfold credit_le, debit. cbn. lia. Qed.
Lemma debit_mono c c' n : credit_le c c' -> credit_le (debit L c n) (debit L c' n).
Proof. unfold credit_le, debit. cbn. lia. Qed.
Lemma debit_le_amount c n n' : n' <= n -> credit_le (debit L c n) (debit L c n').
Proof. unfold credit_le, debit. cbn. lia. Qed.
Lemma vblk_pos m : 0 <= vblk m.
Proof. unfold vblk. destruct (m <? 39)%nat. lia. pose proof (round_up_ge_S (num_words_est m)). lia. Qed.
Lemma parse_debit_le c m : credit_le (parse_debit L c m) c.
Proof. unfold parse_debit. eapply credit_le_trans. apply credit_le_debit. apply vblk_pos. apply credit_le_debit. apply vblk_pos. Qed.

Lemma IMGLO : 0 <= hl_img_lo L <= hl_img_hi L. Proof. rewrite (ly_img_lo L LY), (ly_img_hi L LY). lia. Qed.
Lemma IMGHI : hl_img_hi L <= 0x7fff7f800000. Proof. rewrite (ly_img_hi L LY). lia. Qed.
Lemma SEGSB : forallb (fun seg => Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) (hl_img_hi L)) RSEGS = true.
Proof. rewrite (ly_img_hi L LY). exact segs_below. Qed.
Lemma ERRNO_LO : hl_errno L + 4 <= hl_img_hi L. Proof. rewrite (ly_errno L LY), (ly_img_hi L LY). lia. Qed.
Lemma ERR : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L. Proof. rewrite (ly_errno L LY), (ly_img_lo L LY), (ly_img_hi L LY). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma detail_len0 :
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (p o sp r fb : Z) (neg : bool),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 0 -> getr R 13%bv = Z_to_bv 64 o ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> L5C.stk (hl_sptop L) M sp DETAIL_SCR ->
    L5.big_at RSEGS M o (L5.BO fb 0 (L5.BInl 0 0)) -> sp <= o -> o + 32 <= hl_sptop L -> 4096 <= p -> p <= 2 ^ 47 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        detail_post L LB cr M M' R R' o sp fb neg [] LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R DETAIL M model) K.
Proof.
  intros fx R M model K LB cr p o sp r fb neg HH MOK H10 H11 H13 H1 RA H2 STK OB Olo Ohi Plo Phi KONT.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF). pose proof RA as [Hr He]. uscr.
  assert (WR96: L5.writable RSEGS M (sp - 96) 96).
  { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  rewrite L5CoreKit.L5K.rl10 in H10. rewrite L5CoreKit.L5K.rl11 in H11. rewrite L5CoreKit.L5K.rl2 in H2. rewrite L5CoreKit.L5K.rl1 in H1.
  destruct (pa0_conc fx R M sp p H2 H10 H11 ltac:(lia) ltac:(lia) ltac:(lia) A16 WR96)
    as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & FR1 & GR1).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml.
  { eapply msteps_trans. exact MS1. apply ret_detail. rewrite R1_1. exact H1. exact Hr. exact He. }
  apply (KONT fx1 R1 M1 model LB cr).
  - split. { apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. cbn in Hi.
             destruct Hi as [<-|Hi]. { rewrite R1_2, H2. reflexivity. }
             apply K1. L5CoreKit.L5K.inlist Hi. }
    right. split. left; reflexivity. split. rewrite L5CoreKit.L5K.rl11. exact R1_11.
    split. reflexivity. split.
    { eapply (L5C.big_at_agree RSEGS M M1). intros i Hi. apply FR1. rewrite BG.unsigned_lit by lia. lia. lia. lia. exact OB. }
    split. { apply parse_debit_le. }
    split.
    + intros a (Ha & CA & NE & _). uscr. apply FR1. rewrite BG.unsigned_lit by lia.
      destruct CA as [IB|[[S1 S2]|IM]].
      * destruct IB as (bb & Hb & Hin). pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) bb Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). lia.
      * lia.
      * rewrite (ly_img_hi L LY) in IM. lia.
    + split. { uscr. intros i Hi. apply GR1. apply DEF. lia. } intros a _ _ _ Hd. apply GR1. exact Hd.
  - apply L5C.model_but_vm_refl.
  - eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 96)) as [Hlt|Hge]. left. apply FR1. rewrite BG.unsigned_lit by lia. lia.
    destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']. right; left. lia. left. apply FR1. rewrite BG.unsigned_lit by lia. lia. exact GR1.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dec_all_zero ds : Forall (fun c => c = 48) ds -> dec ds = 0.
Proof. intros H. unfold dec. rewrite (dec_acc_zeros 0 ds H). lia. Qed.
Lemma digits_ok_of_zero ds : Forall (fun c => c = 48) ds -> digits_ok ds.
Proof. intros H. unfold digits_ok. eapply Forall_impl. 2: exact H. intros a ->. lia. Qed.

(* [comment removed for export] *)
Lemma detail_allzero :
  forall (fx : FPState) (R : bvmap 5 word) (M0 M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (p o sp r fb : Z) (neg : bool) (ds : list Z) (R0 : bvmap 5 word),
    let m := Z.of_nat (length ds) in
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    (1 <= length ds)%nat -> (length ds <= 4999)%nat -> Forall (fun c => c = 48) ds ->
    (* [comment removed for export] *)
    getr R (reg 2) = Z_to_bv 64 (sp - 96) -> getr R (reg 4) = Z_to_bv 64 TP ->
    getr R (reg 10) = Z_to_bv 64 p -> getr R (reg 11) = Z_to_bv 64 48 -> getr R (reg 8) = Z_to_bv 64 (p + m) ->
    getr R (reg 9) = Z_to_bv 64 o ->
    (* [comment removed for export] *)
    getr R0 (reg 2) = Z_to_bv 64 sp -> getr R0 (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
    L5.u64_at RSEGS M (sp - 8) r ->
    L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R0 (reg 8))) -> L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R0 (reg 9))) ->
    L5.u64_at RSEGS M (sp - 32) (bv_unsigned (getr R0 (reg 18))) -> L5.u64_at RSEGS M (sp - 40) (bv_unsigned (getr R0 (reg 19))) ->
    L5.u64_at RSEGS M (sp - 48) (bv_unsigned (getr R0 (reg 20))) -> L5.u64_at RSEGS M (sp - 56) (bv_unsigned (getr R0 (reg 21))) ->
    L5.u64_at RSEGS M (sp - 64) (bv_unsigned (getr R0 (reg 22))) ->
    (forall i, In i [3; 4; 23; 24; 25; 26; 27]%nat -> getr R (reg i) = getr R0 (reg i)) ->
    (* [comment removed for export] *)
    L5C.stk (hl_sptop L) M sp DETAIL_SCR ->
    L5.big_at RSEGS M o (L5.BO fb 0 (L5.BInl 0 0)) -> Z.land fb 3 = 0 -> o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    L5.bytes_at RSEGS M p ds -> 4096 <= p -> p + m <= 2 ^ 47 ->
    L5C.hpres L LB sp DETAIL_SCR [(o, 32)] M0 M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        detail_post L LB cr M0 M' R0 R' o sp fb neg ds LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R ZHEAD M model) K.
Proof.
  intros fx R M0 M model K LB cr p o sp r fb neg ds R0 m HH MOK HK0 Hlen Hlen2 ZER H2 H4 H10 H11 H8 H9 H02 H01 RA C8 C16 C24 C32 C40 C48 C56 C64 KR
         STK OB Hfb3 Ao Olo Ohi WO DG Plo Phi HP0 KONT.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF). pose proof RA as [Hr He]. subst m. uscr.
  pose proof (L5PK.lb_wf_of_heap L HI LB cr M _ HIok HH) as LBWF.
  (* [comment removed for export] *)
  destruct (@zskip_all fx M (seg_rom RSEGS) p (Z.of_nat (length ds)) ds eq_refl ltac:(lia)
              ltac:(intros i Hi; apply DG; exact Hi)
              ltac:(intros i Hi; apply (proj1 (Forall_nth _ _) ZER i 0 Hi)) R Hlen
              ltac:(rewrite L5CoreKit.L5K.rl10; exact H10) ltac:(rewrite L5CoreKit.L5K.rl8; exact H8) ltac:(rewrite L5CoreKit.L5K.rl11; exact H11))
    as (R1 & MS1 & Q10 & Q12 & QR).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml.
  { unfold ZHEAD. rewrite (BI.pc_lit 134132 (0x20bf4%bv : word)) by reflexivity. exact MS1. }
  rewrite <- (BI.pc_lit ZBR (0x20c04%bv : word)) by reflexivity.
  (* [comment removed for export] *)
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. { apply br_20acc. }
  rewrite <- L5CoreKit.L5K.rl10, Q10. rewrite <- L5CoreKit.L5K.rl8, (QR 8%bv) by (intro X; discriminate X).
  rewrite L5CoreKit.L5K.rl8, H8. cbn [branch_taken]. unfold c_eq. rewrite bv_eqb_refl.
  (* [comment removed for export] *)
  assert (R1_2: getr R1 (reg 2) = Z_to_bv 64 (sp - 96)). { rewrite <- L5CoreKit.L5K.rl2, QR by (intro X; discriminate X). rewrite L5CoreKit.L5K.rl2. exact H2. }
  assert (R1_9: getr R1 (reg 9) = Z_to_bv 64 o). { rewrite <- L5CoreKit.L5K.rl9, QR by (intro X; discriminate X). rewrite L5CoreKit.L5K.rl9. exact H9. }
  assert (WR96: L5.writable RSEGS M (sp - 96) 96).
  { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  destruct (pa2_conc fx R1 M sp o R1_2 R1_9 ltac:(lia) ltac:(lia) ltac:(lia) A16 WR96)
    as (fx2 & R2 & M2 & MS2 & K2 & R2_1 & R2_2 & R2_10 & R2_11 & T72 & T80 & T88 & T96 & FR2 & GR2).
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS2.
  (* [comment removed for export] *)
  assert (AG2: forall a, ~ (sp - 96 <= a < sp - 64) -> 0 <= a < 2 ^ 64 -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hra. apply FR2. rewrite BG.unsigned_lit by lia. lia. }
  pose proof (land3_bits fb ltac:(destruct OB as (_ & Hf & _); cbn [L5.bo_fb] in Hf; lia) Hfb3) as [B0 B1].
  (* [comment removed for export] *)
  eapply (Hasg fx2 R2 M2 model K LB cr o (sp - 96) (sp - 96) 0x20c34 (L5.BO fb 0 (L5.BInl 0 0)) (L5.BO 0 0 (L5.BInl 0 0)) []).
  - eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB cr M M2 (m_vmmaps model) [(sp - 96, 32)]). exact HIok. exact HH. exact (ly_ro L LY). lia.
    { intros x Hx. apply FR2. intros Hin. apply (Hx (sp - 96, 32)). left; reflexivity. unfold L5.in_rng; cbn. lia. } exact GR2.
    constructor. left. cbn. lia. constructor.
  - exact MOK.
  - exact HK0.
  - rewrite L5CoreKit.L5K.rl10. exact R2_10.
  - rewrite L5CoreKit.L5K.rl11. exact R2_11.
  - cbn. lia.
  - intros D. exfalso. revert D. unfold L5.bo_dyn. cbn [L5.bo_fb]. rewrite B0. discriminate.
  - cbn. intros H3. lia.
  - rewrite L5CoreKit.L5K.rl1. exact R2_1.
  - apply ra_ok_lit. lia. reflexivity.
  - rewrite L5CoreKit.L5K.rl2. exact R2_2.
  - rewrite L5CoreKit.L5K.rl4, (K2 4%nat) by (apply L5KP.In_of_existsb; reflexivity). rewrite <- L5CoreKit.L5K.rl4, QR by (intro X; discriminate X). rewrite L5CoreKit.L5K.rl4. exact H4.
  - (* [comment removed for export] *)
    split. { replace (sp - 96) with (sp + (-6) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    uscr. split. lia. split. lia. split. lia.
    eapply L5.defined_grows. exact GR2. eapply L5.defined_sub. exact DEF. lia. lia.
  - eapply (L5C.big_at_agree RSEGS M M2). intros i Hi. apply AG2; lia. lia. lia. exact OB.
  - exact Ao.
  - lia.
  - exact Ohi.
  - eapply L5.writable_grows. exact GR2. exact WO.
  - cbn. intros cap q D. discriminate D.
  - (* [comment removed for export] *)
    apply big_at_zero. exact T96. replace (sp - 96 + 8) with (sp - 88) by lia; exact T88. replace (sp - 96 + 16) with (sp - 80) by lia; exact T80.
    replace (sp - 96 + 24) with (sp - 72) by lia; exact T72.
  - apply obj_limbs_zero.
  - replace (sp - 96) with (sp + 8 * (-12)) by lia. apply mod16_8. exact A16.
  - lia.
  - lia.
  - cbn. intros cap q D. discriminate D.
  - right. lia.
  - cbn. intros c q c' q' D. discriminate D.
  - (* [comment removed for export] *)
    intros fx3 R3 M3 model3 g LB3 cr3 POST MBV HH3.
    destruct POST as (RP & RA0 & PG). cbn [L5.bo_len] in PG.
    destruct g as [|A cap].
    2: { destruct PG as (Hd & H3 & _). cbn in H3. lia. }
    destruct PG as (_ & ELB & ECR & (st' & OB3 & OL3 & ST3) & HP3). subst LB3 cr3.
    cbn [L5.bo_fb L5.bo_st L5.bo_len L5.bo_data assign_fb Nat.eqb] in OB3, OL3, ST3, HP3.
    destruct st' as [w0 w1|cc qq]. 2: { destruct ST3. }
    (* [comment removed for export] *)
    assert (AG3: forall a n, sp - 96 <= a -> a + n <= sp -> L5C.agree_on M2 M3 a n).
    { intros a n Ha Hn. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP3. uscr; lia. uscr; lia. lia. lia.
      intros i Hi r' [<-|[<-|[]]]; unfold L5.in_rng; cbn; lia. }
    assert (T3: forall a v, sp - 96 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M2 a v -> L5.u64_at RSEGS M3 a v).
    { intros a v Ha Ha8 Hu. eapply (L5C.u64_at_agree RSEGS M2 M3). apply AG3; lia. lia. lia. exact Hu. }
    assert (T23: forall a v, sp - 64 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M3 a v).
    { intros a v Ha Ha8 Hu. apply T3. lia. lia. eapply (L5C.u64_at_agree RSEGS M M2). intros i Hi. apply AG2; lia. lia. lia. exact Hu. }
    pose proof (RP 2%bv ltac:(cbn; tauto)) as P2. pose proof (RP 8%bv ltac:(cbn; tauto)) as P8.
    rewrite L5CoreKit.L5K.rl2 in P2. rewrite L5CoreKit.L5K.rl8 in P8.
    assert (R3_2: getr R3 (reg 2) = Z_to_bv 64 (sp - 96)) by (rewrite P2; exact R2_2).
    assert (R3_8: getr R3 (reg 8) = Z_to_bv 64 (p + Z.of_nat (length ds))).
    { rewrite P8, (K2 8%nat) by (apply L5KP.In_of_existsb; reflexivity). rewrite <- L5CoreKit.L5K.rl8, QR by (intro X; discriminate X). rewrite L5CoreKit.L5K.rl8. exact H8. }
    assert (T96': L5.u8_at RSEGS M3 (sp - 96) 0).
    { eapply (L5C.u8_at_agree RSEGS M2 M3). apply AG3; lia. lia. lia. exact T96. }
    pose proof (wrange (getr R0 (reg 8))) as W8. pose proof (wrange (getr R0 (reg 9))) as W9. pose proof (wrange (getr R0 (reg 18))) as W18.
    pose proof (wrange (getr R0 (reg 19))) as W19. pose proof (wrange (getr R0 (reg 20))) as W20. pose proof (wrange (getr R0 (reg 21))) as W21.
    pose proof (wrange (getr R0 (reg 22))) as W22.
    destruct (pa3_conc fx3 R3 M3 sp (p + Z.of_nat (length ds)) r (bv_unsigned (getr R0 (reg 8))) (bv_unsigned (getr R0 (reg 9)))
                (bv_unsigned (getr R0 (reg 18))) (bv_unsigned (getr R0 (reg 19))) (bv_unsigned (getr R0 (reg 20))) (bv_unsigned (getr R0 (reg 21)))
                (bv_unsigned (getr R0 (reg 22))) R3_2 R3_8 ltac:(lia) ltac:(lia) ltac:(lia) W8 W9 W18 W19 W20 W21 W22 ltac:(lia) A16
                T96' (T23 (sp - 8) _ ltac:(lia) ltac:(lia) C8) (T23 (sp - 16) _ ltac:(lia) ltac:(lia) C16) (T23 (sp - 24) _ ltac:(lia) ltac:(lia) C24)
                (T23 (sp - 32) _ ltac:(lia) ltac:(lia) C32) (T23 (sp - 40) _ ltac:(lia) ltac:(lia) C40) (T23 (sp - 48) _ ltac:(lia) ltac:(lia) C48)
                (T23 (sp - 56) _ ltac:(lia) ltac:(lia) C56) (T23 (sp - 64) _ ltac:(lia) ltac:(lia) C64))
      as (fx4 & R4 & M4 & MS4 & K4 & R4_1 & R4_2 & R4_8 & R4_9 & R4_10 & R4_11 & R4_18 & R4_19 & R4_20 & R4_21 & R4_22 & FR4 & GR4).
    eapply (L5.cps_of_msteps RSEGS). { rewrite (L5C.halted_but_vm _ _ MBV). exact Mh. } { rewrite (L5C.lazy_but_vm _ _ MBV). exact Ml. }
    { eapply msteps_trans. exact MS4. apply ret_detail. exact R4_1. exact Hr. exact He. }
    apply (KONT fx4 R4 M4 model3 LB cr).
    + (* [comment removed for export] *)
      split.
      { apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. cbn in Hi.
        destruct Hi as [<-|Hi]. { rewrite R4_2, H02. reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite (K4 3%nat) by (apply L5KP.In_of_existsb; reflexivity). rewrite <- L5CoreKit.L5K.rl3, (RP 3%bv) by (cbn; tauto). rewrite L5CoreKit.L5K.rl3.
                                  rewrite (K2 3%nat) by (apply L5KP.In_of_existsb; reflexivity). rewrite <- L5CoreKit.L5K.rl3, QR by (intro X; discriminate X). rewrite L5CoreKit.L5K.rl3. apply (KR 3%nat). cbn; tauto. }
        destruct Hi as [<-|Hi]. { rewrite (K4 4%nat) by (apply L5KP.In_of_existsb; reflexivity). rewrite <- L5CoreKit.L5K.rl4, (RP 4%bv) by (cbn; tauto). rewrite L5CoreKit.L5K.rl4.
                                  rewrite (K2 4%nat) by (apply L5KP.In_of_existsb; reflexivity). rewrite <- L5CoreKit.L5K.rl4, QR by (intro X; discriminate X). rewrite L5CoreKit.L5K.rl4. apply (KR 4%nat). cbn; tauto. }
        destruct Hi as [<-|Hi]. { rewrite R4_8. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R4_9. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R4_18. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R4_19. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R4_20. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R4_21. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R4_22. apply lit_of_word. }
        assert (G: forall j, In j [23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R0 (reg j)).
        { intros j Hj.
          assert (A4: In j KS_A3) by (pose proof Hj as H'; L5CoreKit.L5K.inlist H').
          assert (A2: In j KS_A2) by (pose proof Hj as H'; L5CoreKit.L5K.inlist H').
          assert (AC: In j L5CoreKit.L5K.CS) by (pose proof Hj as H'; L5CoreKit.L5K.inlist H').
          assert (AK: In j [3; 4; 23; 24; 25; 26; 27]%nat) by (pose proof Hj as H'; L5CoreKit.L5K.inlist H').
          rewrite (K4 j A4). rewrite (L5CoreKit.L5K.regs_preserved_index R2 R3 j RP AC). rewrite (K2 j A2).
          assert (NE10: reg j <> 10%bv). { intros E. cbn in Hj. repeat (destruct Hj as [<-|Hj]; [discriminate E|]). destruct Hj. }
          assert (NE12: reg j <> 12%bv). { intros E. cbn in Hj. repeat (destruct Hj as [<-|Hj]; [discriminate E|]). destruct Hj. }
          rewrite (QR (reg j) NE10 NE12). apply (KR j AK). }
        apply G. L5CoreKit.L5K.inlist Hi. }
      left. split. exact Hlen. split. apply digits_ok_of_zero. exact ZER. split. rewrite L5CoreKit.L5K.rl11. exact R4_11.
      (* [comment removed for export] *)
      unfold parse_post. rewrite (dec_all_zero ds ZER). rewrite nwords_0. change (wlist 0 0) with (@nil Z).
      exists (L5.BInl w0 w1). split.
      { (* [comment removed for export] *) replace (res_fb fb 0 neg) with fb. 2: { unfold res_fb. cbn. destruct neg; cbn; lia. }
        eapply (L5C.big_at_agree RSEGS M3 M4). intros i Hi. apply FR4. lia. lia. exact OB3. }
      split. { replace (res_fb fb 0 neg) with fb. 2: { unfold res_fb. cbn. destruct neg; cbn; lia. } cbn. destruct OL3 as (L1 & L2 & L3). cbn in L1, L2, L3.
               split. exact L1. split. exact L2. exact L3. }
      split. { split. cbn. lia. reflexivity. }
      split. { apply parse_debit_le. }
      (* [comment removed for export] *)
      assert (HP2: L5C.hpres L LB sp DETAIL_SCR [(o, 32)] M0 M2).
      { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [(o,32)] M0 M M2 [(sp - 96, 32)]). exact LBWF. uscr; lia. exact HP0.
        intros x Hx. apply FR2. intros Hin. apply (Hx (sp - 96, 32)). left; reflexivity. unfold L5.in_rng; cbn; lia. exact GR2.
        constructor. apply L5PK.wr_scratch; uscr; lia. constructor. }
      assert (HP3': L5C.hpres L LB sp DETAIL_SCR [(o, 32)] M0 M3).
      { eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LB sp DETAIL_SCR [(o,32)] (sp - 96) ASSIGN_SCR _ M0 M2 M3). exact LBWF. uscr; lia. lia.
        exact HP2. exact HP3. apply L5PK.lb_sub_refl. uscr; lia. lia. uscr; lia.
        constructor. eapply L5PK.wr_declared. left; reflexivity. lia. lia. constructor. apply L5PK.wr_empty. lia. constructor. }
      eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp DETAIL_SCR [(o,32)] M0 M3 M4 []). exact LBWF. uscr; lia. exact HP3'.
      intros x Hx. apply FR4. exact GR4. constructor.
    + exact MBV.
    + eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB cr M3 M4 (m_vmmaps model3) []). exact HIok. exact HH3. exact (ly_ro L LY). lia.
      intros x Hx. apply FR4. exact GR4. constructor.
Qed.


End WithHeap.
End SCFG_1.

End L5DETZ.
