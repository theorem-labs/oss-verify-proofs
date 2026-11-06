(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface LibIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     Ub0_code_201fc_21084 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkDivBaseU BigModel BigFactsDigits
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5KnP L5ParseArith L5ParseKit L5ParseSpecsU L5Bytes L5E1AU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Module L5STRKU.
Import L5CSU L5PSU L5E1U.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Ltac inl := cbn; repeat (first [ left; reflexivity | right ]).
Ltac uscr := unfold STRCTOR_SCR, TOBIG_SCR, DETAIL_SCR, ADDD_SCR, MUL10_SCR, ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.
Section SCFG_2.
Context {SCFG_P : ScfgP}.

Definition TB3RET : Z := 0x20c70.   (* [comment removed for export] *)
Definition SRET : Z := 0x20c88.     (* [comment removed for export] *)
Definition THROW0 : Z := 0x20c90.   (* [comment removed for export] *)
Definition AALLOC_RET : Z := 0x3fee0.
Definition CAT : Z := 0x20ca4.
Definition SYSERR : Z := 0x20cb4.
Definition MALLOC_RET : Z := 0x5abc8.
Definition THROW : Z := 0x20ccc.

(* [comment removed for export] *)
Record layoutx (L : heap_layout) : Prop := LAYX {
  lyx_ro : forall a, hl_alloc_ro L a ->
             a < 0x5b000 \/ (0x5f0e8 <= a < 0x5f0f0) \/ (0x911a8 <= a < 0x911b0) \/ (0x911c8 <= a < 0x91238) \/ (0x915e0 <= a < 0x915e8) \/ hl_sptop L <= a }.

(* [comment removed for export] *)
Definition statx (a : Z) : Prop :=
  (EH_CAUGHT <= a < EH_CAUGHT + 12) \/ (SYSCAT_GUARD <= a < SYSCAT_GUARD + 2) \/ (UW_FLAGS <= a < UW_FLAGS + 6) \/ (ERRNO <= a < ERRNO + 4).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_sret fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R SRET M) (st fx R r M).
Proof. intros H1 Hr He. apply (BDU.ret_to fx R M SRET W_20c88 r F_20c88 eq_refl D_20c88 H1 Hr He). Qed.
Lemma lit_of_word (w : word) : Z_to_bv 64 (bv_unsigned w) = w.
Proof. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma wrange (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia. Qed.
Lemma ra_ok_lit z : 0 <= z < 2 ^ 47 -> z mod 2 = 0 -> L5.ra_ok z.
Proof. intros; split; assumption. Qed.
Lemma land252_3 fb : 0 <= fb < 256 -> Z.land (Z.land fb 252) 3 = 0.
Proof. intros H. rewrite <- Z.land_assoc. change (Z.land 252 3) with 0. apply Z.land_0_r. Qed.
Lemma land1_even n : 0 <= n -> 0 <= Z.land (2 * n) 1 <= 0.
Proof.
  intros Hn. assert (E: Z.land (2 * n) 1 = 0). { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2. rewrite Z.mul_comm. apply Z_mod_mult. }
  rewrite E. lia.
Qed.
Lemma land1_odd_byte w0 : 0 <= w0 -> Z.testbit w0 0 = true -> 1 <= Z.land (L5B.byte_k w0 0) 1 <= 1.
Proof.
  intros Hw Hb. unfold L5B.byte_k. rewrite Z.mul_0_r, Z.shiftr_0_r. rewrite Z.bit0_odd in Hb.
  assert (E: Z.land (w0 mod 256) 1 = 1).
  { change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
    rewrite <- (Znumtheory.Zmod_div_mod 2 256 w0). rewrite Zmod_odd, Hb. reflexivity. lia. lia. exists 128; reflexivity. }
  rewrite E. lia.
Qed.
Lemma obj_limbs_agree M M' b ws :
  L5C.obj_limbs RSEGS M b ws ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> L5C.agree_on M M' q (8 * Z.of_nat (length ws)) /\ 0 <= q /\ q + 8 * Z.of_nat (length ws) <= 2 ^ 64) ->
  L5C.obj_limbs RSEGS M' b ws.
Proof.
  intros (L1 & L2 & L3) HQ. split. exact L1. split. exact L2. destruct (L5.bo_st b) as [v0 v1|cap q] eqn:EB. exact L3.
  destruct (HQ cap q eq_refl) as (AG & Q0 & Q1). eapply (L5C.limbs_at_agree RSEGS M M'). exact AG. exact Q0. exact Q1. exact L3.
Qed.
(* [comment removed for export] *)
Lemma writable_img M a n : wseg_ok RSEGS (Z_to_bv 64 a) (Z.to_nat n) = true -> 0 <= a -> 0 < n -> a + n <= 2 ^ 64 -> L5.writable RSEGS M a n.
Proof.
  intros W Ha Hn Han d k Hd Hk. destruct k as [|k]. reflexivity.
  eapply (store_ok_sub RSEGS M (Z_to_bv 64 a) _ (Z.to_nat n) (S k)).
  - rewrite BG.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
  - apply store_ok_wseg. exact W.
  - rewrite !BG.unsigned_lit by lia. lia.
  - rewrite !BG.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma wseg_guard : wseg_ok RSEGS (Z_to_bv 64 SYSCAT_GUARD) 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_errno : wseg_ok RSEGS (Z_to_bv 64 ERRNO) 4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_uncaught : wseg_ok RSEGS (Z_to_bv 64 EH_UNCAUGHT) 4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_uwflags : wseg_ok RSEGS (Z_to_bv 64 UW_FLAGS) 6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rom_errno : L5B.rom_ok RSEGS ERRNO 4 = true. Proof. vm_compute. reflexivity. Qed.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis LYX : layoutx L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis Htb3 : tobig3_spec L HI.
Hypothesis KPOS : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_overhead L.

Lemma IMGLO : 0 <= hl_img_lo L <= hl_img_hi L. Proof. rewrite (ly_img_lo L LY), (ly_img_hi L LY). lia. Qed.
Lemma IMGHI : hl_img_hi L <= 0x7fff7f800000. Proof. rewrite (ly_img_hi L LY). lia. Qed.
Lemma ERR : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L. Proof. rewrite (ly_errno L LY), (ly_img_lo L LY), (ly_img_hi L LY). lia. Qed.
Lemma ERRNO_LO : hl_errno L + 4 <= hl_img_hi L. Proof. rewrite (ly_errno L LY), (ly_img_hi L LY). lia. Qed.
Lemma credit_le_trans a b c : credit_le a b -> credit_le b c -> credit_le a c. Proof. unfold credit_le. lia. Qed.
Lemma credit_ok_mono c c' n : credit_le c c' -> credit_ok L c n -> credit_ok L c' n.
Proof. unfold credit_le, credit_ok. lia. Qed.
Lemma debit_mono c c' n : credit_le c c' -> credit_le (debit L c n) (debit L c' n).
Proof. unfold credit_le, debit. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma hpres_of_core LBx spx M1 M2 : heap_pres_core L LBx spx M1 M2 -> L5C.hpres L LBx spx (hl_stack L) [] M1 M2.
Proof.
  intros [P D]. apply L5C.hpres_intro.
  - intros a (Ha & CA & NE & _). apply P. exact Ha. exact CA. exact NE.
  - intros i Hi. apply D. lia.
  - intros a Ha CA NE H0. rewrite (P a Ha CA NE). exact H0.
Qed.

(* [comment removed for export] *)
Lemma hi_heap_clientx LB cr M M' VM :
  hi_heap HI LB cr M VM -> 0x7fff80000000 <= hl_sptop L ->
  (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) \/ (hl_sptop L - 8388608 <= a < hl_sptop L) \/ in_block LB a \/ statx a) ->
  mem_grows M M' -> hi_heap HI LB cr M' VM.
Proof.
  intros HH Hsp Hchg Hgr. pose proof IMGHI as IH'. eapply (hio_frame L SCFG HI HIok). exact HH.
  - intros a Ha Hpriv. destruct (Hchg a Ha) as [E|[S|[B|X]]]. exact E.
    + exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. lia. apply (ly_ro L LY) in P. lia.
    + exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. exact (P2 B). apply (ly_ro L LY) in P.
      destruct B as (b & Hb & Hin). pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M VM HH) b Hb) as ((R0 & R1 & R2 & R3 & R4) & _).
      lia.
    + exfalso. unfold statx, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, ERRNO in X. destruct Hpriv as [(P1 & P2 & P3)|P].
      * apply P3. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY). lia. intros HS. apply (ly_static L LY) in HS. lia.
      * apply (lyx_ro L LYX) in P. lia.
  - intros x Hx. apply Hgr. exact Hx.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stat_rd (av a : Z) : Prop :=
  (EH_CAUGHT <= a < EH_CAUGHT + 12) \/ (SYSCAT_GUARD <= a < SYSCAT_GUARD + 2) \/ (UW_FLAGS <= a < UW_FLAGS + 6) \/
  (TD_LOCALE <= a < TD_LOCALE + 8) \/ (LOCALE_MSGCAT <= a < LOCALE_MSGCAT + 8) \/ (CANARY <= a < CANARY + 8) \/ (AUXVP <= a < AUXVP + 8) \/
  (av <= a < av + 160) \/ (0x10000 <= a < 0x60100) \/ (0x60128 <= a < 0x60148) \/ (0x60158 <= a < 0x60160).

Lemma u32_at_agree M M' a v : L5C.agree_on M M' a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof. intros AG Ha Hn H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4 a); auto. Qed.

Lemma e1_statics_keep M M' gd fl av uid rnd canary hw :
  e1_statics M gd fl av uid rnd canary hw -> (forall a, stat_rd av a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  e1_statics M' gd fl av uid rnd canary hw.
Proof.
  intros (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20) K.
  unfold e1_statics. unfold stat_rd, EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in *.
  assert (AG: forall a n, (forall i, a <= i < a + n -> (459768 <= i < 459768 + 12) \/ (460320 <= i < 460320 + 2) \/ (462433 <= i < 462433 + 6) \/
     (462600 <= i < 462600 + 8) \/ (594472 <= i < 594472 + 8) \/ (594344 <= i < 594344 + 8) \/ (594384 <= i < 594384 + 8) \/
     (av <= i < av + 160) \/ (0x10000 <= i < 0x60100) \/ (0x60128 <= i < 0x60148) \/ (0x60158 <= i < 0x60160)) -> L5C.agree_on M M' a n).
  { intros a n H i Hi. apply K. apply H. exact Hi. }
  Ltac cell AG := first [ eapply (L5C.u64_at_agree RSEGS); [apply AG; intros; lia | lia | lia | assumption]
                        | eapply u32_at_agree; [apply AG; intros; lia | lia | lia | assumption]
                        | eapply (L5C.u8_at_agree RSEGS); [apply AG; intros; lia | lia | lia | assumption] ].
  split. cell AG. split. cell AG. split. cell AG. split. cell AG.
  split. { destruct fl. destruct S5 as (F1 & F2 & F3 & F4 & F5 & F6). repeat split; cell AG. destruct S5 as (F1 & F2 & F3). repeat split; cell AG. }
  split. cell AG. split. cell AG. split. cell AG. split. cell AG. split. exact S10. split. exact S11. split. exact S12.
  split. { intros j Hj. eapply (L5C.u64_at_agree RSEGS). apply AG. intros; lia. lia. lia. apply S13. exact Hj. }
  split. exact S14. split. exact S15. split. exact S16. split. exact S17.
  split. { intros i Hi. rewrite K by lia. apply S18. exact Hi. }
  split. { intros i Hi. rewrite K by lia. apply S19. exact Hi. }
  intros i Hi. rewrite K by lia. apply S20. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma stat_keep_hpres av LBx spx scr W M1 M2 :
  L5C.hpres L LBx spx scr W M1 M2 -> hl_sptop L - 2 ^ 23 + scr <= spx -> 0 <= scr -> 0x7fff80000000 <= hl_sptop L -> spx <= av -> av + 160 <= 2 ^ 64 ->
  (forall i, stat_rd av i -> L5.outside W i) ->
  forall a, stat_rd av a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof.
  intros HP Hsp Hscr Hst Hav Hav2 HO a Ha. apply (L5C.hpres_kept L LBx spx scr W M1 M2 a HP).
  pose proof Ha as Ha'. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha.
  assert (D: av <= a < av + 160 \/ (0x10000 <= a < 0x91230 /\ (a < 0x70e94 \/ 0x70e98 <= a))) by lia.
  destruct D as [AV|[IM NE]].
  - apply L5C.kept_stack. lia. lia. lia. rewrite (ly_errno L LY); lia. exact Hst. apply HO. exact Ha'.
  - apply L5C.kept_static. rewrite (ly_img_lo L LY), (ly_img_hi L LY); lia. intros HS; apply (ly_static L LY) in HS; lia.
    rewrite (ly_img_lo L LY); lia. rewrite (ly_img_hi L LY); lia. rewrite (ly_errno L LY); lia. apply HO. exact Ha'.
Qed.
(* [comment removed for export] *)
Lemma defined_across LBx spx scrx W M1 M2 lo n :
  L5C.hpres L LBx spx scrx W M1 M2 -> hl_sptop L - 8388608 <= lo -> 0x7fff80000000 <= hl_sptop L -> lo + n <= 2 ^ 64 -> 0 <= scrx ->
  L5.defined M1 lo n -> L5.defined M2 lo n.
Proof.
  intros HP Hlo Hst Hn Hs D i Hi.
  destruct (Z_lt_le_dec (lo + i) (spx - scrx)) as [B|B1]. 2: destruct (Z_lt_le_dec (lo + i) spx) as [B2|B3].
  - apply (L5C.hpres_cdef L LBx spx scrx W M1 M2 (lo + i) HP). lia. right; left. lia. unfold in_errno. rewrite (ly_errno L LY). lia. apply D. lia.
  - replace (lo + i) with (spx - scrx + (lo + i - (spx - scrx))) by lia. apply (L5C.hpres_defined L LBx spx scrx W M1 M2 HP). lia.
  - apply (L5C.hpres_cdef L LBx spx scrx W M1 M2 (lo + i) HP). lia. right; left. lia. unfold in_errno. rewrite (ly_errno L LY). lia. apply D. lia.
Qed.
(* [comment removed for export] *)
Lemma e1_statics_reguard M M' gd fl av uid rnd canary hw :
  e1_statics M gd fl av uid rnd canary hw ->
  L5.u8_at RSEGS M' SYSCAT_GUARD 1 -> L5.u8_at RSEGS M' (SYSCAT_GUARD + 1) 1 ->
  (forall a, stat_rd av a -> ~ (SYSCAT_GUARD <= a < SYSCAT_GUARD + 2) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  e1_statics M' true fl av uid rnd canary hw.
Proof.
  intros (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20) G0 G1 K.
  unfold e1_statics. unfold stat_rd, EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in *.
  assert (AG: forall a n, (forall i, a <= i < a + n -> ((459768 <= i < 459768 + 12) \/ (460320 <= i < 460320 + 2) \/ (462433 <= i < 462433 + 6) \/
     (462600 <= i < 462600 + 8) \/ (594472 <= i < 594472 + 8) \/ (594344 <= i < 594344 + 8) \/ (594384 <= i < 594384 + 8) \/
     (av <= i < av + 160) \/ (0x10000 <= i < 0x60100) \/ (0x60128 <= i < 0x60148) \/ (0x60158 <= i < 0x60160)) /\ ~ (460320 <= i < 460320 + 2)) -> L5C.agree_on M M' a n).
  { intros a n H i Hi. destruct (H i Hi) as [H1 H2]. apply K. exact H1. exact H2. }
  Ltac cellg AG := first [ eapply (L5C.u64_at_agree RSEGS); [apply AG; intros; lia | lia | lia | assumption]
                         | eapply u32_at_agree; [apply AG; intros; lia | lia | lia | assumption]
                         | eapply (L5C.u8_at_agree RSEGS); [apply AG; intros; lia | lia | lia | assumption] ].
  split. cellg AG. split. cellg AG. split. exact G0. split. exact G1.
  split. { destruct fl. destruct S5 as (F1 & F2 & F3 & F4 & F5 & F6). repeat split; cellg AG. destruct S5 as (F1 & F2 & F3). repeat split; cellg AG. }
  split. cellg AG. split. cellg AG. split. cellg AG. split. cellg AG. split. exact S10. split. exact S11. split. exact S12.
  split. { intros j Hj. eapply (L5C.u64_at_agree RSEGS). apply AG. intros; lia. lia. lia. apply S13. exact Hj. }
  split. exact S14. split. exact S15. split. exact S16. split. exact S17.
  split. { intros i Hi. rewrite K by lia. apply S18. exact Hi. }
  split. { intros i Hi. rewrite K by lia. apply S19. exact Hi. }
  intros i Hi. rewrite K by lia. apply S20. exact Hi.
Qed.

Lemma u8_of_zeros M a n i : L5KP.zeros_at M a n -> 0 <= i < n -> L5.u8_at RSEGS M (a + i) 0.
Proof. intros Z0 Hi. unfold L5.u8_at. rewrite (L5B.rdn_S RSEGS). rewrite (Z0 i Hi). reflexivity. Qed.

(* [comment removed for export] *)
Lemma hpres_W_mono LBx spx scr W W' M1 M2 : L5C.hpres L LBx spx scr W M1 M2 -> (forall a, L5.outside W' a -> L5.outside W a) -> L5C.hpres L LBx spx scr W' M1 M2.
Proof.
  intros HP HW. apply L5C.hpres_intro.
  - intros a (Ha & CA & NE & OW). apply (L5C.hpres_kept L LBx spx scr W M1 M2 a HP). split. exact Ha. split. exact CA. split. exact NE. apply HW. exact OW.
  - exact (L5C.hpres_defined L LBx spx scr W M1 M2 HP).
  - intros a Ha CA NE. exact (L5C.hpres_cdef L LBx spx scr W M1 M2 a HP Ha CA NE).
Qed.
(* [comment removed for export] *)
Lemma auxv_cells M av uid rnd hw :
  (forall j, (j < 20)%nat -> L5.u64_at RSEGS M (av + 8 * Z.of_nat j) (nth j (auxv20 uid rnd hw) 0)) ->
  L5.u64_at RSEGS M (av) 3 /\ L5.u64_at RSEGS M (av + 8) 65600 /\ L5.u64_at RSEGS M (av + 16) 4 /\ L5.u64_at RSEGS M (av + 24) 56 /\ L5.u64_at RSEGS M (av + 32) 5 /\ L5.u64_at RSEGS M (av + 40) 10 /\ L5.u64_at RSEGS M (av + 48) 16 /\ L5.u64_at RSEGS M (av + 56) hw /\ L5.u64_at RSEGS M (av + 64) 6 /\ L5.u64_at RSEGS M (av + 72) 4096 /\ L5.u64_at RSEGS M (av + 80) 11 /\ L5.u64_at RSEGS M (av + 88) uid /\ L5.u64_at RSEGS M (av + 96) 12 /\ L5.u64_at RSEGS M (av + 104) uid /\ L5.u64_at RSEGS M (av + 112) 23 /\ L5.u64_at RSEGS M (av + 120) 0 /\ L5.u64_at RSEGS M (av + 128) 25 /\ L5.u64_at RSEGS M (av + 136) rnd /\ L5.u64_at RSEGS M (av + 144) 0 /\ L5.u64_at RSEGS M (av + 152) 0.
Proof.
  intros H. unfold auxv20 in H.
  pose proof (H 0%nat ltac:(lia)) as X0. cbn [nth] in X0. replace (av + 8 * Z.of_nat 0) with (av) in X0 by lia.
  pose proof (H 1%nat ltac:(lia)) as X1. cbn [nth] in X1. replace (av + 8 * Z.of_nat 1) with (av + 8) in X1 by lia.
  pose proof (H 2%nat ltac:(lia)) as X2. cbn [nth] in X2. replace (av + 8 * Z.of_nat 2) with (av + 16) in X2 by lia.
  pose proof (H 3%nat ltac:(lia)) as X3. cbn [nth] in X3. replace (av + 8 * Z.of_nat 3) with (av + 24) in X3 by lia.
  pose proof (H 4%nat ltac:(lia)) as X4. cbn [nth] in X4. replace (av + 8 * Z.of_nat 4) with (av + 32) in X4 by lia.
  pose proof (H 5%nat ltac:(lia)) as X5. cbn [nth] in X5. replace (av + 8 * Z.of_nat 5) with (av + 40) in X5 by lia.
  pose proof (H 6%nat ltac:(lia)) as X6. cbn [nth] in X6. replace (av + 8 * Z.of_nat 6) with (av + 48) in X6 by lia.
  pose proof (H 7%nat ltac:(lia)) as X7. cbn [nth] in X7. replace (av + 8 * Z.of_nat 7) with (av + 56) in X7 by lia.
  pose proof (H 8%nat ltac:(lia)) as X8. cbn [nth] in X8. replace (av + 8 * Z.of_nat 8) with (av + 64) in X8 by lia.
  pose proof (H 9%nat ltac:(lia)) as X9. cbn [nth] in X9. replace (av + 8 * Z.of_nat 9) with (av + 72) in X9 by lia.
  pose proof (H 10%nat ltac:(lia)) as X10. cbn [nth] in X10. replace (av + 8 * Z.of_nat 10) with (av + 80) in X10 by lia.
  pose proof (H 11%nat ltac:(lia)) as X11. cbn [nth] in X11. replace (av + 8 * Z.of_nat 11) with (av + 88) in X11 by lia.
  pose proof (H 12%nat ltac:(lia)) as X12. cbn [nth] in X12. replace (av + 8 * Z.of_nat 12) with (av + 96) in X12 by lia.
  pose proof (H 13%nat ltac:(lia)) as X13. cbn [nth] in X13. replace (av + 8 * Z.of_nat 13) with (av + 104) in X13 by lia.
  pose proof (H 14%nat ltac:(lia)) as X14. cbn [nth] in X14. replace (av + 8 * Z.of_nat 14) with (av + 112) in X14 by lia.
  pose proof (H 15%nat ltac:(lia)) as X15. cbn [nth] in X15. replace (av + 8 * Z.of_nat 15) with (av + 120) in X15 by lia.
  pose proof (H 16%nat ltac:(lia)) as X16. cbn [nth] in X16. replace (av + 8 * Z.of_nat 16) with (av + 128) in X16 by lia.
  pose proof (H 17%nat ltac:(lia)) as X17. cbn [nth] in X17. replace (av + 8 * Z.of_nat 17) with (av + 136) in X17 by lia.
  pose proof (H 18%nat ltac:(lia)) as X18. cbn [nth] in X18. replace (av + 8 * Z.of_nat 18) with (av + 144) in X18 by lia.
  pose proof (H 19%nat ltac:(lia)) as X19. cbn [nth] in X19. replace (av + 8 * Z.of_nat 19) with (av + 152) in X19 by lia.
  repeat split; assumption.
Qed.


End WithHeap.
End SCFG_2.

End L5STRKU.
