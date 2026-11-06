(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the take block of ent_build's cases 6 and 7
   (fuzz_take, fuzz.h:59-65, with the body copy of pod.h:347 / 356) inside LLVMFuzzerTestOneInput (0x80c40),
   lib/AU/HPgW6cEng.v's w6c_take_stmt at both of its entries, 0x8227c (case 6) and 0x8244c (case 7). Proves no
   function (kind: segment lemma).

   THE CODE (the two entries run the same four instructions, then share 0x82464):
     pc0       sw a2,4(s4)              e62.size := sz (a2 = sz, s4 = F + 0x210)
     pc0 + 4   bltu a2,a1 -> pc0 + 12; pc0 + 8 mv a2,a1             n := min(sz, left) (a1 = left)
     pc0 + 12  not a0,s2; bgeu a0,a2 -> 0x82464                     the UBSan test of fuzz.h:63 (its `unimp` arm
                                                                     needs ~cur <u n, which cur <= 2^47 rules out)
     0x82464   add s10,s2,a2; sub s5,a1,a2; ld a0,0x118(s1); mv a1,s2
     0x82474   jal __asan_memcpy        e62.body[0 .. n) := the n input bytes at the cursor
     0x82478   mv a3,s10; mv t1,s5; j 0x82614; 0x82614 ld s2,0x138(s1)  -> J
   THE PROOF: one token-engine run from w6c_tss pc0 true (s4 pinned to F + 0x210) up to `bltu`, the branch split
   (srr_branch_tok), one run per arm to the callee's entry; then w6c_take_call: the call through the Section
   hypothesis INTRIN (the kernel's contract of __asan_memcpy at 0x51d8c, AMEMCPY) and one run from w6c_tss 0x82478
   false to J. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgCaseBJ HPgW6cEng HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Lemma w6c_ret_cpy : YK0s.ret_ok (Z_to_bv 64 W6C_RCPY).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma w6c_take_cs : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w6c_take_clob -> acallee_saved (bv_unsigned r).
Proof. apply w6c_cs. vm_compute. reflexivity. Qed.
Definition w6c_take_clob1 : list (bv 5) := [1; 10; 11; 12; 20; 21; 26]%bv.
Lemma w6c_take_notin1 : forall r : bv 5, ~ In r w6c_take_clob -> ~ In r w6c_take_clob1 \/ r = 20%bv.
Proof.
intros r Hn. destruct (base.decide (r = 20%bv)) as [E|E]; [right; exact E|left].
intros X. apply Hn. cbv [In w6c_take_clob1] in X. cbv [In w6c_take_clob].
destruct X as [X|[X|[X|[X|[X|[X|[X|[]]]]]]]]; subst r;
  first [ exfalso; apply E; reflexivity | repeat (first [left; reflexivity | right]) ].
Qed.
Lemma w6c_take_notin2 : forall r : bv 5, ~ In r w6c_take_clob -> ~ In r [6; 13; 18]%bv.
Proof. intros r Hn X. apply Hn. cbv [In w6c_take_clob] in X |- *. tauto. Qed.
(* the extra atom facts of the take block: the cursor, the size and what is left *)
Definition w6c_tkG : list (nat * afact) :=
  [(18%nat, mkAF 1 (2 ^ 47) 0); (12%nat, mkAF 0 11 0); (11%nat, mkAF 0 (2 ^ 47) 0)].
Lemma w6c_min_len : forall sz (q : list byte), 0 <= sz ->
  Z.of_nat (length (firstn (Z.to_nat sz) q)) = Z.min sz (Z.of_nat (length q)).
Proof. intros sz q Hsz. rewrite length_firstn, Nat2Z.inj_min, Z2Nat.id by lia. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis INTRIN : w6c_intrin_law B.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6C_CPY.

(* ---- from the callee's entry to J ---- *)
Lemma w6c_take_call : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos pp c2 sz : Z) (q : list byte) (ms : machine_state) md,
  w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF -> getr regs 20 = w64 (F + 0x210) ->
  0 <= sz <= 11 -> 0 <= pp <= 2 ^ 47 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0x210) 104 ->
  shadow_hull_vis (aview rsegs (w_H W) memc) (F + 0x210) 104 ->
  hm_bytes rsegs (w_H W) memc c2 q ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF c2 (Z.of_nat (length q)) ->
  (0 < Z.of_nat (length q) -> shadow_hull_vis (aview rsegs (w_H W) memc) c2 (Z.of_nat (length q))) ->
  amem_range c2 (Z.of_nat (length q)) -> 1 <= c2 ->
  (forall a, c2 <= a < c2 + Z.of_nat (length q) ->
     ~ (R - T_SEG_STK <= a < R + 0x198) /\ ~ (F + 0x20 <= a < F + 0x278)) ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 W6C_CPY) (ms_mem ms) (seg_rom rsegs) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 W6C_RCPY ->
  getr (ms_regs ms) 10 = w64 (F + 0x218) -> getr (ms_regs ms) 11 = w64 c2 ->
  getr (ms_regs ms) 12 = w64 (Z.of_nat (length (firstn (Z.to_nat sz) q))) ->
  getr (ms_regs ms) 20 = w64 (F + 0x210) ->
  getr (ms_regs ms) 21 = w64 (Z.of_nat (length q) - Z.of_nat (length (firstn (Z.to_nat sz) q))) ->
  getr (ms_regs ms) 26 = w64 (c2 + Z.of_nat (length (firstn (Z.to_nat sz) q))) ->
  (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w6c_take_clob1 -> getr (ms_regs ms) r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x214 <= a < F + 0x218) ->
     aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
  val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x214) 4 sz ->
  SRr rsegs W (mkCfg ms md)
   (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6C_J w6c_take_clob
     (w6c_take_wr R F (Z.of_nat (length (firstn (Z.to_nat sz) q))))
     (fun W2 regs2 mem2 => W2 = W /\
        getr regs2 13 = w64 (c2 + Z.of_nat (length (firstn (Z.to_nat sz) q))) /\
        getr regs2 6 = w64 (Z.of_nat (length (skipn (Z.to_nat sz) q))) /\
        getr regs2 18 = w64 (pp + 0x4000) /\ getr regs2 20 = w64 (F + 0x210) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x214) 4 sz /\
        hm_bytes rsegs (w_H W2) mem2 (F + 0x218) (firstn (Z.to_nat sz) q))).
Proof using MTL INTRIN AMEMCPY.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos pp c2 sz q ms md
  Hctx H2 H3 H4 H9 H27 H20 Hsz Hpp V118 V130 V138 HraE HhE Hq Hraq Hhq Hamq Hc2 Hdq
  HJ Hio Ems R1 R10 R11 R12 R20 R21 R26 Kept1 KE1 VS.
destruct Hctx as (_ & HR32 & HRc & HRsp & Hsp47 & HSTK & Hown & HF & HF1 & HF2 & HF32 & HFapp & HFp).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof asan_consts as (Hceil & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp16 & _).
unfold T_SEG_STK, ASTACK in *.
set (n := Z.of_nat (length (firstn (Z.to_nat sz) q))) in *.
assert (Hn : n = Z.min sz (Z.of_nat (length q))) by (subst n; apply w6c_min_len; lia).
assert (HRb : 0x10007fffc000 <= R <= 2 ^ 47 - 0x220) by lia.
assert (HFb : 4096 <= F <= 2 ^ 47 - 1024) by lia.
assert (HFa : F + 1024 <= kLowShadowBeg \/ kHighMemBeg <= F) by (unfold in_app, ASAN_CEIL in HFapp; lia).
assert (Hcq : c2 + Z.of_nat (length q) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamq; lia).
(* a shadow byte of an application range below 2^47 is not one of e62's bytes *)
assert (Hband : forall x m s, 0 <= x -> 0 < m -> x + m <= 2 ^ 47 - 1 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + m - 1) / 8 * 8 + 8 ->
  0 <= s < 2 ^ 64 /\ ~ (F + 0x214 <= s < F + 0x278)).
{ intros x m s Hx Hm Hxm Hs. pose proof (cj_hull_band x m s Hx Hm Hxm Hs) as X.
  unfold kLowMemEnd, kHighMemBeg in X. unfold kLowShadowBeg, kHighMemBeg in HFa. lia. }
assert (Hsh : forall x, 0 <= x < 2 ^ 47 ->
  0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\ ~ (F + 0x214 <= shadow_of_addr SHADOW_OFF x < F + 0x278)).
{ intros x Hx. pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as X.
  unfold kLowMemEnd, kHighMemBeg in X. unfold kLowShadowBeg, kHighMemBeg in HFa. lia. }
(* the copied bytes at the callee's entry *)
assert (Hp : hm_bytes rsegs (w_H W) (ms_mem ms) c2 (firstn (Z.to_nat sz) q)).
{ rewrite <- (firstn_skipn (Z.to_nat sz) q) in Hq. apply hm_bytes_app in Hq as [Hq1 _].
  apply (hm_bytes_kept rsegs (w_H W) memc); [exact Hq1|]. intros x Hx. fold n in Hx.
  apply KE1; [lia|]. destruct (Hdq x ltac:(lia)) as [_ X]. lia. }
(* ---- the call: __asan_memcpy(F + 0x218, c2, n) ---- *)
rewrite Ems.
eapply SRr_bind.
{ apply (INTRIN OCpy W6C_CPY AMEMCPY W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    (F + 0x218) c2 n (R - sp0) (Z_to_bv 64 W6C_RCPY) HJ R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite (Kept1 2%bv) by w6c_side. rewrite H2. unfold w64.
    rewrite unsigned_lit_small by lia. lia.
  - assert (HR16 : R mod 16 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.mod_divide in HR32; [|lia]. destruct HR32 as [q0 Hq0]. exists (2 * q0). lia. }
    rewrite Zminus_mod, HR16, Hsp16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite (Kept1 3%bv) by w6c_side. exact H3.
  - rewrite (Kept1 4%bv) by w6c_side. exact H4.
  - exact R1.
  - exact w6c_ret_cpy.
  - intros a Ha. split.
    + unfold awr_byte. right; right; right. exists 4, pos. split; [exact Hown|]. left.
      unfold in_zr. cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 4) with 1024. lia.
    + unfold ESTACK. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. unfold kLowShadowBeg, kHighMemBeg in HFa.
    pose proof alloc_ceiling_lt. lia.
  - apply (hm_ra_kept rsegs (w_H W) memc (w_H W) (ms_mem ms));
      [apply (ra_sub _ _ (F + 0x210) 104); [exact HraE | lia | lia]|].
    intros x Hx. destruct (Hsh x ltac:(lia)) as [X1 X2]. apply KE1; [exact X1 | lia].
  - intros Hn0. apply (hm_hull_kept rsegs (w_H W) memc (w_H W) (ms_mem ms)).
    + apply (hm_hull_sub _ (F + 0x210) 104); [exact HhE | lia | lia | lia].
    + intros s Hs Hne. destruct (Hband (F + 0x218) n s ltac:(lia) Hn0 ltac:(lia) Hs) as [Hs1 Hs2].
      rewrite (KE1 s Hs1 ltac:(lia)). exact Hne.
  - split; [lia|]. split; [lia|]. split.
    + intros a Ha. split.
      * pose proof (proj1 (hm_bytes_aview rsegs (w_H W) (ms_mem ms) c2 (firstn (Z.to_nat sz) q)) Hp
          (Z.to_nat (a - c2)) ltac:(fold n; lia)) as A.
        rewrite Z2Nat.id in A by lia. replace (c2 + (a - c2)) with a in A by lia. rewrite A. discriminate.
      * unfold spZ. rewrite (Kept1 2%bv) by w6c_side. rewrite H2. unfold w64.
        rewrite unsigned_lit_small by lia. unfold ESTACK. destruct (Hdq a ltac:(lia)) as [X _]. lia.
    + split.
      * destruct (Z_le_gt_dec n 0) as [Hn0|Hn0]; [lia|].
        destruct (Z_le_gt_dec (F + 0x218 + n) c2) as [X|X]; [left; exact X|].
        destruct (Z_le_gt_dec (c2 + n) (F + 0x218)) as [Y|Y]; [right; exact Y|].
        exfalso. destruct (Hdq (Z.max c2 (F + 0x218)) ltac:(lia)) as [_ X2]. apply X2. lia.
      * split; [unfold amem_range in *; lia|]. split.
        -- apply (hm_ra_kept rsegs (w_H W) memc (w_H W) (ms_mem ms));
             [apply (ra_sub _ _ c2 (Z.of_nat (length q))); [exact Hraq | lia | lia]|].
           intros x Hx. destruct (Hsh x ltac:(lia)) as [X1 X2]. apply KE1; [exact X1 | lia].
        -- intros Hn0. apply (hm_hull_kept rsegs (w_H W) memc (w_H W) (ms_mem ms)).
           ++ apply (hm_hull_sub _ c2 (Z.of_nat (length q))); [apply Hhq; lia | lia | lia | lia].
           ++ intros s Hs Hne. destruct (Hband c2 n s ltac:(lia) Hn0 ltac:(lia) Hs) as [Hs1 Hs2].
              rewrite (KE1 s Hs1 ltac:(lia)). exact Hne. }
cbv beta. intros W2 c3 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & HP2 & Ha02 & HD2 & HK2 & Hpr2).
replace (sp0 + (R - sp0)) with R in HK2 by lia.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x214 <= a < F + 0x218 + n) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha X1 X2. rewrite (HK2 a Ha ltac:(lia) X2). apply KE1; [exact Ha | lia]. }
assert (G9 : getr regs2 9 = w64 R).
{ transitivity (getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia))|].
  rewrite (Kept1 9%bv) by w6c_side. exact H9. }
assert (G27 : getr regs2 27 = w64 SHADOW_OFF).
{ transitivity (getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia))|].
  rewrite (Kept1 27%bv) by w6c_side. exact H27. }
assert (G20 : getr regs2 20 = w64 (F + 0x210)).
{ transitivity (getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]. }
assert (G21 : getr regs2 21 = w64 (Z.of_nat (length q) - n)).
{ transitivity (getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact R21]. }
assert (G26 : getr regs2 26 = w64 (c2 + n)).
{ transitivity (getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact R26]. }
assert (KV : forall a m v, val_mem rsegs (mrestrict (w_H W) memc) a m v ->
  (forall i, 0 <= i < Z.of_nat m -> 0 <= a + i < 2 ^ 64 /\ ~ (F + 0x214 <= a + i < F + 0x218 + n) /\ ~ (R - ESTACK <= a + i < R)) ->
  val_mem rsegs (mrestrict (w_H W) mem2) a m v).
{ intros a m v V X. apply (w6c_val_kept (w_H W) (w_H W) memc mem2 a m v V). intros i Hi.
  destruct (X i Hi) as (X1 & X2 & X3). exact (K2 (a + i) X1 X2 X3). }
pose proof (KV _ _ _ V118 ltac:(intros i Hi; cbn in Hi; unfold ESTACK; lia)) as V118'.
pose proof (KV _ _ _ V130 ltac:(intros i Hi; cbn in Hi; unfold ESTACK; lia)) as V130'.
pose proof (KV _ _ _ V138 ltac:(intros i Hi; cbn in Hi; unfold ESTACK; lia)) as V138'.
assert (VS2 : val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x214) 4 sz).
{ apply (w6c_val_kept (w_H W) (w_H W) (ms_mem ms) mem2 _ _ _ VS). intros i Hi. cbn in Hi.
  apply HK2; [lia | lia | unfold ESTACK; lia]. }
assert (Hp2 : hm_bytes rsegs (w_H W) mem2 (F + 0x218) (firstn (Z.to_nat sz) q)).
{ apply (hm_memcpy_bytes rsegs (w_H W) (ms_mem ms) (w_H W) mem2 c2); [exact Hp|]. intros i Hi. apply HD2. fold n. lia. }
(* ---- run 2: 0x82478 .. J ---- *)
pose proof (w6c_tentry W6C_RCPY false [] W regs2 mem2 R F pp ltac:(unfold W6C_RCPY; lia) G9 G27 HRb HR32 HFb HF32
  ltac:(lia) ltac:(lia) V118' V130' V138' ltac:(intros X; discriminate X) I) as HS2.
remember (Ereg regs2 (w6c_extra F 0 0 pp)) as E2 eqn:HE2.
assert (HAE2 : env_agree 32 (Ereg regs2 (w6c_extra F 0 0 pp)) E2) by (subst E2; apply env_agree_refl).
assert (F21 : ew E2 21 = Z_to_bv 64 (Z.of_nat (length q) - n))
  by (subst E2; rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl); exact G21).
assert (F26 : ew E2 26 = Z_to_bv 64 (c2 + n)) by (subst E2; rewrite (ew_Ereg_nat regs2 _ 26 26%bv eq_refl); exact G26).
assert (F35 : ew E2 35 = Z_to_bv 64 pp) by (subst E2; exact (w6c_e35 regs2 F 0 0 pp)).
assert (SHOK2 : sh_ok rsegs w6c_Bx [] E2 (mrestrict (w_H W) mem2)) by constructor.
assert (U32b : bv_unsigned (ew E2 32) = F)
  by (subst E2; rewrite (w6c_e32 regs2 F 0 0 pp); apply unsigned_lit_small; lia).
clear HE2.
aj_run_to_tok w6c_tbl_ok HS2 HJ2 SHOK2 w6c_Bspan W6C_J;
  [ apply (w6c_tawr _ false _ _ _ _ _ _ _ F pos U32b Hown HF) | ].
w6c_ew HS2 F21. w6c_ew HS2 F26. w6c_ew HS2 F35.
lazymatch goal with Hf : frame_of E2 (ss_mem (w6c_tss W6C_RCPY false [])) (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (w6c_frame_ro E2 _ _ Hf) as KR2 end.
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msf) |- _ =>
  assert (KE2 : forall a, aview rsegs (w_H W) (ms_mem msf) a = aview rsegs (w_H W) mem2 a)
    by (intros a; unfold aview, mbyte; rewrite KR2; reflexivity);
  assert (Kept2 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [6; 13; 18]%bv -> getr (ms_regs msf) r = getr regs2 r)
    by (eapply (regs_kept_of_st_ok rsegs _ _ _ regs2 _ (w_H W) _ HSx); [env_agree_chain HAE2 | vm_compute; reflexivity]);
  apply (w6c_post_of_run B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6C_J w6c_take_clob
    (w6c_take_wr R F n) _ _ _ msf _ HSx eq_refl eq_refl HJ2) end.
- eapply same_io_trans; [|eapply same_io_trans; [exact Hio2|]]; [exact Hio | cb_kio].
- intros r Hr0 Hnr. rewrite (Kept2 r Hr0 (w6c_take_notin2 r Hnr)).
  rewrite (w6c_reg_cs (ms_regs ms) regs2 r HP2 (w6c_take_cs r Hr0 Hnr)).
  destruct (w6c_take_notin1 r Hnr) as [X| ->]; [exact (Kept1 r Hr0 X)|]. rewrite R20. symmetry. exact H20.
- intros a Ha Hnw. unfold w6c_take_wr, T_SEG_STK, ASTACK in Hnw. cbv beta in Hnw. rewrite KE2.
  apply K2; [exact Ha | intros X; apply Hnw; right; exact X | intros X; apply Hnw; left; unfold ESTACK in X; lia].
- split; [reflexivity|].
  split; [w6c_reg HS2 (13%bv : bv 5); unfold w64; apply w6c_den0; [exact F26' | lia]|].
  split; [w6c_reg HS2 (6%bv : bv 5); unfold w64; rewrite length_skipn; rewrite (w6c_den0 _ 21 _ F21') by lia;
          f_equal; rewrite Hn; lia|].
  split; [w6c_reg HS2 (18%bv : bv 5); unfold w64; apply w6c_den_off; [exact F35' | lia | lia]|].
  split; [rewrite (Kept2 20%bv) by w6c_side; exact G20|].
  split.
  + apply (w6c_val_kept (w_H W) (w_H W) mem2 _ _ _ _ VS2). intros i Hi. apply KE2.
  + apply (hm_bytes_kept rsegs (w_H W) mem2); [exact Hp2|]. intros x _. apply KE2.
Qed.

(* the write windows of a take state lie in e62's size word *)
Local Ltac w6c_tk_wrl U32 :=
  let a := fresh "a" in let Ha := fresh "Ha" in let X := fresh "X" in
  intros a Ha; pose proof (fun Hsk => w6c_tw_sk _ _ true a Hsk Ha) as X;
  specialize (X ltac:(vm_compute; reflexivity)); rewrite ?ew_ewset_other in X by lia; rewrite U32 in X; exact X.
(* the second run of an arm: to the callee's entry *)
Local Ltac w6c_tk_run HS HJ SHOK U32 Hown HF F pos :=
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_CPY;
    [ eapply (w6c_tawr_sk _ _ true _ _ _ _ _ _ _ F pos);
        [vm_compute; reflexivity | rewrite ?ew_ewset_other by lia; exact U32 | exact Hown | exact HF] | ];
  w6c_keep (fun a => F + 0x214 <= a < F + 0x218) ltac:(w6c_tk_wrl U32).
(* the trap arm of the UBSan test 0x8228c / 0x8245c: ~cur <u n is false *)
Local Ltac w6c_tk_trap Hc E18 E12 E11 c2 sz :=
  exfalso; rewrite branch_geu_U, (U_not _ 18 c2 E18 ltac:(lia)) in Hc;
  rewrite ?(U_atom _ 12 sz E12) in Hc by lia; rewrite ?(U_atom _ 11 _ E11) in Hc by lia;
  apply negb_false_iff, Z.ltb_lt in Hc; lia.
(* the callee's entry: w6c_take_call (TC, its static premises given), with n held by atom na (value X) *)
Local Ltac w6c_tk_fin TC na X Ena E11 E12 E18 E32 U32 HAE KE Hnv regs W HJx :=
  lazymatch goal with HSx : st_ok _ ?Ev ?ssf (restrict (w_H ?Wx) ?msf) |- SRr _ _ (mkCfg ?msf ?mdf) _ =>
  let Hr1 := fresh "Hr1" in w6c_rnth HSx 1%nat Hr1;
  eapply (TC msf mdf HJx);
  [ cb_kio
  | exact (st_ok_restrict_mkst rsegs (w_H Wx) Ev ssf msf HSx eq_refl)
  | w6c_reg HSx (1%bv : bv 5); apply w6c_den_lit; unfold W6C_RCPY; lia
  | w6c_reg HSx (10%bv : bv 5); unfold w64; apply w6c_den_off; [exact E32 | lia | lia]
  | w6c_reg HSx (11%bv : bv 5); unfold w64; apply w6c_den0; [exact E18 | lia]
  | w6c_reg HSx (12%bv : bv 5); unfold w64; rewrite Hnv; apply w6c_den0; [exact Ena | lia]
  | w6c_reg HSx (20%bv : bv 5); unfold w64; apply w6c_den_off; [exact E32 | lia | lia]
  | w6c_reg HSx (21%bv : bv 5); unfold w64; rewrite Hnv;
    first [ apply w6c_den_subm; [exact E11 | exact Ena | lia | lia]
          | rewrite Z.sub_diag; apply w6c_den_lit; lia
          | lazymatch goal with |- ?g => fail 1 "reg21" g end ]
  | w6c_reg HSx (26%bv : bv 5); unfold w64; rewrite Hnv;
    first [ rewrite (w6c_den_add _ na 18 X _ Ena E18) by lia; f_equal; lia | fail 1 "reg26" ]
  | first [ eapply (regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HSx); [env_agree_chain HAE | vm_compute; reflexivity]
          | fail 1 "kept" ]
  | exact KE
  | lazymatch type of U32 with bv_unsigned _ = ?Fv => lazymatch type of E12 with _ = Z_to_bv 64 ?szv =>
    let U32x := fresh "U32x" in let E12x := fresh "E12x" in
    assert (U32x : bv_unsigned (ew Ev 32) = Fv) by (rewrite ?ew_ewset_other by lia; exact U32);
    assert (E12x : ew Ev 12 = Z_to_bv 64 szv) by (rewrite ?ew_ewset_other by lia; exact E12);
    exact (w6c_field _ _ 32%nat Fv _ _ _ _ _ 0x214 4 (SOff 12 0) szv Hr1 U32x ltac:(cbn; tauto)
      ltac:(apply w6c_den0; [exact E12x | lia]) ltac:(cbn; lia) ltac:(cbn; lia)) end end ]
  end.

(* ---- the take block, from either entry ---- *)
Theorem w6c_take : forall pc0, pc0 = W6C_T6 \/ pc0 = W6C_T7 -> w6c_take_stmt B MT pc0.
Proof using MTL INTRIN AMEMCPY.
intros pc0 Hpc0. unfold w6c_take_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos pp c2 sz q
  Hctx H2 H3 H4 H9 H27 H12 H11 H18 H20 Hsz Hpp V118 V130 V138 HraE HhE Hq Hraq Hhq Hamq Hc2 Hdq.
pose proof Hctx as (HJ & HR32 & HRc & HRsp & Hsp47 & HSTK & Hown & HF & HF1 & HF2 & HF32 & HFapp & HFp).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof asan_consts as (Hceil & _).
assert (HRb : 0x10007fffc000 <= R <= 2 ^ 47 - 0x220) by (unfold T_SEG_STK, ASTACK in *; lia).
assert (HFb : 4096 <= F <= 2 ^ 47 - 1024) by lia.
assert (Hcq : c2 + Z.of_nat (length q) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamq; lia).
assert (HG : atoms_ok (Ereg regs (w6c_extra F 0 0 pp)) w6c_tkG).
{ cbn [w6c_tkG atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (w6c_U_reg regs _ 18 18%bv c2 eq_refl H18) by lia.
  rewrite (w6c_U_reg regs _ 12 12%bv sz eq_refl H12) by lia.
  rewrite (w6c_U_reg regs _ 11 11%bv _ eq_refl H11) by lia.
  change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (HFR : F + 1024 <= R) by (unfold T_SEG_STK, ASTACK in *; lia).
pose proof (w6c_tentry pc0 true w6c_tkG W regs memc R F pp ltac:(destruct Hpc0 as [-> | ->]; unfold W6C_T6, W6C_T7; lia)
  H9 H27 HRb HR32 HFb HF32 ltac:(lia) ltac:(lia) V118 V130 V138 ltac:(intros _ o Ho; apply HFp; lia) HG) as HS0.
remember (Ereg regs (w6c_extra F 0 0 pp)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (w6c_extra F 0 0 pp)) E) by (subst E; apply env_agree_refl).
assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat (length q))) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 sz) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E18 : ew E 18 = Z_to_bv 64 c2) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (w6c_e32 regs F 0 0 pp)).
assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok rsegs w6c_Bx w6c_SH4 E (mrestrict (w_H W) memc)).
{ subst E. apply (w6c_shok4 regs (w_H W) memc F 0 0 pp H27 HFb HFapp).
  apply (ra_sub _ _ (F + 0x210) 104); [exact HraE | lia | lia]. }
pose proof (st_ok_pin_sv rsegs E _ _ (20%bv : bv 5) (SOff 32 0x210) HS0 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite (w6c_den_off E 32 F 0x210 E32) by lia; exact (eq_sym H20))) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts w6c_tss] in HS. clear HS0.
clear HE.
unfold cfg_at. change (w64 pc0) with (Z_to_bv 64 pc0).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x214 <= a < F + 0x218) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
pose proof (w6c_take_call STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos pp c2 sz q)
  as TC0.
pose proof (fun ms md => TC0 ms md Hctx H2 H3 H4 H9 H27 H20 Hsz Hpp V118 V130 V138 HraE HhE Hq Hraq Hhq Hamq Hc2 Hdq)
  as TC.
clear TC0.
pose proof (w6c_min_len sz q ltac:(lia)) as Hmin.
destruct Hpc0 as [-> | ->]; (
(aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_CPY;
   [ apply (w6c_tawr _ true _ _ _ _ _ _ _ F pos U32 Hown HF) | ]);
w6c_keep (fun a => F + 0x214 <= a < F + 0x218) ltac:(w6c_tk_wrl U32);
srr_branch_tok w6c_tbl_ok HS SHOK w6c_Bspan;
[ (* sz < left: n = sz *)
  assert (Hnv : Z.of_nat (length (firstn (Z.to_nat sz) q)) = sz)
    by (rewrite branch_ltu_U, (U_atom _ 12 sz E12), (U_atom _ 11 _ E11) in Hc by lia;
        apply Z.ltb_lt in Hc; rewrite (w6c_min_len sz q) by lia; lia);
  clear Hc; w6c_tk_run HS HJ SHOK U32 Hown HF F pos; srr_branch_tok w6c_tbl_ok HS SHOK w6c_Bspan;
  [ w6c_tk_run HS HJ SHOK U32 Hown HF F pos; w6c_tk_fin TC 12%nat sz E12 E11 E12 E18 E32 U32 HAE KE Hnv regs W HJ
  | w6c_tk_trap Hc E18 E12 E11 c2 sz ]
| (* sz >= left: n = left *)
  assert (Hnv : Z.of_nat (length (firstn (Z.to_nat sz) q)) = Z.of_nat (length q))
    by (rewrite branch_ltu_U, (U_atom _ 12 sz E12), (U_atom _ 11 _ E11) in Hc by lia;
        apply Z.ltb_ge in Hc; rewrite (w6c_min_len sz q) by lia; lia);
  clear Hc; w6c_tk_run HS HJ SHOK U32 Hown HF F pos; srr_branch_tok w6c_tbl_ok HS SHOK w6c_Bspan;
  [ w6c_tk_run HS HJ SHOK U32 Hown HF F pos;
    w6c_tk_fin TC 11%nat (Z.of_nat (length q)) E11 E11 E12 E18 E32 U32 HAE KE Hnv regs W HJ
  | w6c_tk_trap Hc E18 E12 E11 c2 sz ] ]).
Qed.
End d.
End b.

Print Assumptions w6c_take_call.
Print Assumptions w6c_take.
