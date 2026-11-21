(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the auxv region is 464 bytes, was 160, the auxv fact is the launch's vector, carried over memory that agrees on it (auxv_ok_agree), and the type words a scan of it reads come from that vector (auxv_vec_type). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface LibIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_20088_210bc BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkReduce BigModel BigFactsDigits
     L5Defs L5Core L5CoreKit L5CoreKitS L5CoreSpecs L5KnP L5ParseArith L5ParseKit L5ParseSpecs L5Bytes L5E1A.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Module L5STRK.
Import L5CS L5PS L5E1.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Ltac inl := cbn; repeat (first [ left; reflexivity | right ]).
Ltac uscr := unfold STRCTOR_SCR, TOBIG_SCR, DETAIL_SCR, ADDD_SCR, MUL10_SCR, ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.
Section SCFG_2.
Context {SCFG_P : ScfgP}.

Definition TB3RET : Z := 0x20a14.   (* [comment removed for export] *)
Definition SRET : Z := 0x20a2c.     (* [comment removed for export] *)
Definition THROW0 : Z := 0x20a34.   (* [comment removed for export] *)
Definition AALLOC_RET : Z := 0x3f3e4.
Definition CAT : Z := 0x20a3c.
Definition SYSERR : Z := 0x20a4c.
Definition MALLOC_RET : Z := 0x5a0cc.
Definition THROW : Z := 0x20a64.

(* [comment removed for export] *)
Record layoutx (L : heap_layout) : Prop := LAYX {
  lyx_ro : forall a, hl_alloc_ro L a ->
             a < 0x5b000 \/ (0x5e5f0 <= a < 0x5e5f8) \/ (0x906a8 <= a < 0x906b0) \/ (0x906c8 <= a < 0x90738) \/ (0x90ae0 <= a < 0x90ae8) \/ hl_sptop L <= a }.

(* [comment removed for export] *)
Definition statx (a : Z) : Prop :=
  (EH_CAUGHT <= a < EH_CAUGHT + 12) \/ (SYSCAT_GUARD <= a < SYSCAT_GUARD + 2) \/ (UW_FLAGS <= a < UW_FLAGS + 6) \/ (ERRNO <= a < ERRNO + 4).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_sret fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R SRET M) (st fx R r M).
Proof. intros H1 Hr He. apply (BRED.ret_to fx R M SRET W_20a2c r F_20a2c eq_refl D_20a2c H1 Hr He). Qed.
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
  (av <= a < av + 464) \/ (0x10000 <= a < 0x5f608) \/ (0x5f630 <= a < 0x5f650) \/ (0x5f660 <= a < 0x5f668).

Lemma u32_at_agree M M' a v : L5C.agree_on M M' a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof. intros AG Ha Hn H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4 a); auto. Qed.

Lemma e1_statics_keep M M' gd fl av uid rnd canary hw :
  e1_statics M gd fl av uid rnd canary hw -> (forall a, stat_rd av a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  e1_statics M' gd fl av uid rnd canary hw.
Proof.
  intros (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20) K.
  unfold e1_statics. unfold stat_rd, EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in *.
  assert (AG: forall a n, (forall i, a <= i < a + n -> (456952 <= i < 456952 + 12) \/ (457504 <= i < 457504 + 2) \/ (459617 <= i < 459617 + 6) \/
     (459784 <= i < 459784 + 8) \/ (591656 <= i < 591656 + 8) \/ (591528 <= i < 591528 + 8) \/ (591568 <= i < 591568 + 8) \/
     (av <= i < av + 464) \/ (0x10000 <= i < 0x5f608) \/ (0x5f630 <= i < 0x5f650) \/ (0x5f660 <= i < 0x5f668)) -> L5C.agree_on M M' a n).
  { intros a n H i Hi. apply K. apply H. exact Hi. }
  Ltac cell AG := first [ eapply (L5C.u64_at_agree RSEGS); [apply AG; intros; lia | lia | lia | assumption]
                        | eapply u32_at_agree; [apply AG; intros; lia | lia | lia | assumption]
                        | eapply (L5C.u8_at_agree RSEGS); [apply AG; intros; lia | lia | lia | assumption] ].
  split. cell AG. split. cell AG. split. cell AG. split. cell AG.
  split. { destruct fl. destruct S5 as (F1 & F2 & F3 & F4 & F5 & F6). repeat split; cell AG. destruct S5 as (F1 & F2 & F3). repeat split; cell AG. }
  split. cell AG. split. cell AG. split. cell AG. split. cell AG. split. exact S10. split. exact S11. split. exact S12.
  split. { apply (auxv_ok_agree M M' av uid rnd hw S13); [lia | intros i Hi; apply K; lia]. }
  split. exact S14. split. exact S15. split. exact S16. split. exact S17.
  split. { intros i Hi. rewrite K by lia. apply S18. exact Hi. }
  split. { intros i Hi. rewrite K by lia. apply S19. exact Hi. }
  intros i Hi. rewrite K by lia. apply S20. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma stat_keep_hpres av LBx spx scr W M1 M2 :
  L5C.hpres L LBx spx scr W M1 M2 -> hl_sptop L - 2 ^ 23 + scr <= spx -> 0 <= scr -> 0x7fff80000000 <= hl_sptop L -> spx <= av -> av + 464 <= 2 ^ 64 ->
  (forall i, stat_rd av i -> L5.outside W i) ->
  forall a, stat_rd av a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof.
  intros HP Hsp Hscr Hst Hav Hav2 HO a Ha. apply (L5C.hpres_kept L LBx spx scr W M1 M2 a HP).
  pose proof Ha as Ha'. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha.
  assert (D: av <= a < av + 464 \/ (0x10000 <= a < 0x90730 /\ (a < 0x70394 \/ 0x70398 <= a))) by lia.
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
  assert (AG: forall a n, (forall i, a <= i < a + n -> ((456952 <= i < 456952 + 12) \/ (457504 <= i < 457504 + 2) \/ (459617 <= i < 459617 + 6) \/
     (459784 <= i < 459784 + 8) \/ (591656 <= i < 591656 + 8) \/ (591528 <= i < 591528 + 8) \/ (591568 <= i < 591568 + 8) \/
     (av <= i < av + 464) \/ (0x10000 <= i < 0x5f608) \/ (0x5f630 <= i < 0x5f650) \/ (0x5f660 <= i < 0x5f668)) /\ ~ (457504 <= i < 457504 + 2)) -> L5C.agree_on M M' a n).
  { intros a n H i Hi. destruct (H i Hi) as [H1 H2]. apply K. exact H1. exact H2. }
  Ltac cellg AG := first [ eapply (L5C.u64_at_agree RSEGS); [apply AG; intros; lia | lia | lia | assumption]
                         | eapply u32_at_agree; [apply AG; intros; lia | lia | lia | assumption]
                         | eapply (L5C.u8_at_agree RSEGS); [apply AG; intros; lia | lia | lia | assumption] ].
  split. cellg AG. split. cellg AG. split. exact G0. split. exact G1.
  split. { destruct fl. destruct S5 as (F1 & F2 & F3 & F4 & F5 & F6). repeat split; cellg AG. destruct S5 as (F1 & F2 & F3). repeat split; cellg AG. }
  split. cellg AG. split. cellg AG. split. cellg AG. split. cellg AG. split. exact S10. split. exact S11. split. exact S12.
  split. { apply (auxv_ok_agree M M' av uid rnd hw S13); [lia | intros i Hi; apply K; lia]. }
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
(* The words of the LPS 727298f3 vector a scan of it reads ([dl_iterate_phdr]
   looks for AT_PHDR and AT_PHNUM up to AT_NULL): every type word, the three
   program-header values, and AT_NULL's value.  [r] is CONFIG_RSEQ. *)
Lemma auxv_vec_type la ph entry gid ae uid rnd hw i :
  (i < StackLayout.auxv_count (StackLayout.la_rseq la))%nat ->
  nth (2 * i) (auxv_vec la ph entry gid ae uid rnd hw) 0 = nth i (auxv_types (StackLayout.la_rseq la)) 0.
Proof.
  intros Hi. destruct la as [eh c ms r]. cbn [StackLayout.la_rseq] in *.
  destruct r; cbn [StackLayout.auxv_count] in Hi; (do 29 (destruct i as [|i]; [reflexivity|])); Lia.lia.
Qed.

(* [auxv_cells] also gives the whole vector defined, the [KUnk] fact of the
   throw-path certificates' start knowledge ([SegAuxv.aux_kn]): every word of it
   is a [u64_at] of the launch's vector, above the image. *)
Lemma auxv_cells M av uid rnd hw :
  auxv_ok M av uid rnd hw -> 2 ^ 40 <= av ->
  exists r : bool,
    av + 16 * Z.of_nat (length (auxv_types r)) <= 2 ^ 47
    /\ (forall i, (i < length (auxv_types r))%nat -> L5.u64_at RSEGS M (av + 16 * Z.of_nat i) (nth i (auxv_types r) 0))
    /\ L5.u64_at RSEGS M (av + 216) 0x10040 /\ L5.u64_at RSEGS M (av + 232) 56 /\ L5.u64_at RSEGS M (av + 248) 10
    /\ L5.defined M av (16 * Z.of_nat (length (auxv_types r)))
    /\ L5.u64_at RSEGS M (av + 16 * Z.of_nat (length (auxv_types r)) - 8) 0.
Proof.
  intros (la & ph & entry & gid & ae & P1 & P2 & P3 & B & W) AVLO.
  assert (LT : forall r, length (auxv_types r) = StackLayout.auxv_count r) by (intros []; reflexivity).
  assert (C27 : (27 <= StackLayout.auxv_count (StackLayout.la_rseq la))%nat)
    by (unfold StackLayout.auxv_count; destruct (StackLayout.la_rseq la); cbn; Lia.lia).
  assert (DEF : L5.defined M av (16 * Z.of_nat (StackLayout.auxv_count (StackLayout.la_rseq la)))).
  { intros i Hi.
    pose proof (Z.div_mod i 8 ltac:(Lia.lia)) as DM. pose proof (Z.mod_pos_bound i 8 ltac:(Lia.lia)) as MB.
    assert (Hk : (Z.to_nat (i / 8) < 2 * StackLayout.auxv_count (StackLayout.la_rseq la))%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; Lia.lia). Lia.lia. }
    pose proof (W _ Hk) as U. rewrite Z2Nat.id in U by (apply Z.div_pos; Lia.lia).
    pose proof (L5KS.u64_at_defined2 M (av + 8 * (i / 8)) _ U ltac:(Lia.lia) ltac:(right; Lia.lia) ltac:(Lia.lia)) as D8.
    replace (av + i) with (av + 8 * (i / 8) + i mod 8) by Lia.lia. apply D8. Lia.lia. }
  exists (StackLayout.la_rseq la). rewrite LT. split; [exact B|]. split.
  { intros i Hi. rewrite <- (auxv_vec_type la ph entry gid ae uid rnd hw i Hi).
    replace (av + 16 * Z.of_nat i) with (av + 8 * Z.of_nat (2 * i)) by Lia.lia. apply W. Lia.lia. }
  pose proof (W 27%nat ltac:(Lia.lia)) as X27. pose proof (W 29%nat ltac:(Lia.lia)) as X29. pose proof (W 31%nat ltac:(Lia.lia)) as X31.
  change (nth 27 (auxv_vec la ph entry gid ae uid rnd hw) 0) with (bv_unsigned (Z_to_bv 64 (Z.of_N (ph_addr ph)))) in X27.
  change (nth 29 (auxv_vec la ph entry gid ae uid rnd hw) 0) with (bv_unsigned (Z_to_bv 64 (Z.of_N (ph_ent ph)))) in X29.
  change (nth 31 (auxv_vec la ph entry gid ae uid rnd hw) 0) with (bv_unsigned (Z_to_bv 64 (Z.of_N (ph_num ph)))) in X31.
  rewrite P1 in X27. rewrite P2 in X29. rewrite P3 in X31.
  change (bv_unsigned (Z_to_bv 64 0x10040)) with 0x10040 in X27.
  change (bv_unsigned (Z_to_bv 64 56)) with 56 in X29.
  change (bv_unsigned (Z_to_bv 64 10)) with 10 in X31.
  replace (av + 8 * Z.of_nat 27) with (av + 216) in X27 by Lia.lia.
  replace (av + 8 * Z.of_nat 29) with (av + 232) in X29 by Lia.lia.
  replace (av + 8 * Z.of_nat 31) with (av + 248) in X31 by Lia.lia.
  split; [exact X27|]. split; [exact X29|]. split; [exact X31|]. split; [exact DEF|].
  destruct la as [eh c ms r]. cbn [StackLayout.la_rseq] in *.
  destruct r; cbn [StackLayout.auxv_count] in *.
  - pose proof (W 57%nat ltac:(Lia.lia)) as XN. replace (av + 16 * Z.of_nat 29 - 8) with (av + 8 * Z.of_nat 57) by Lia.lia. exact XN.
  - pose proof (W 53%nat ltac:(Lia.lia)) as XN. replace (av + 16 * Z.of_nat 27 - 8) with (av + 8 * Z.of_nat 53) by Lia.lia. exact XN.
Qed.


End WithHeap.
End SCFG_2.

End L5STRK.
