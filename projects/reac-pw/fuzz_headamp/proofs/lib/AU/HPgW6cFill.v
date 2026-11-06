(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the fill block of ent_build's case 8
   (pod.h:364) inside LLVMFuzzerTestOneInput (0x80c40), lib/AU/HPgW6cEng.v's w6c_fill_stmt. Proves no function
   (kind: segment lemma).

   THE CODE (registers as lib/AU/HPgW6cEng.v's w6c_fill_stmt gives them: s1 = R, s11 = K, a2 = the size,
   s2 = the cursor, s4 = what is left):
     0x822b0  ld s5,0x130(s1)          s5 := F + 0x210 (&e62)
     0x822b4  sw a2,4(s5)              e62.size := a2
     0x822b8  ld a0,0x118(s1); 0x822bc mv a1,zero
     0x822c0  jal __asan_memset        e62.body[0 .. a2) := 0 (a2 <= 3)
     0x822c4  mv t1,s4; 0x822c8 mv s4,s5; 0x822cc j 0x82610; 0x82610 mv a3,s2; 0x82614 ld s2,0x138(s1)  -> J
   THE PROOF is three steps: one token-engine run from w6c_tss 0x822b0 true (R's cells and e62's size word) to the
   callee's entry; the call through the Section hypothesis INTRIN (w6c_intrin_law, the kernel's contract of
   __asan_memset at 0x52228, AMEMSET); one run from w6c_tss 0x822c4 false (R's cells) to J. *)
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

Lemma w6c_ret_set : YK0s.ret_ok (Z_to_bv 64 W6C_RSET).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma w6c_fill_cs : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w6c_fill_clob -> acallee_saved (bv_unsigned r).
Proof. apply w6c_cs. vm_compute. reflexivity. Qed.
Lemma w6c_fill_notin1 : forall r : bv 5, ~ In r w6c_fill_clob -> ~ In r [1; 10; 11; 21]%bv.
Proof. intros r Hn X. apply Hn. cbv [In w6c_fill_clob] in X |- *. tauto. Qed.
Lemma w6c_fill_notin2 : forall r : bv 5, ~ In r w6c_fill_clob -> ~ In r [6; 13; 18; 20]%bv.
Proof. intros r Hn X. apply Hn. cbv [In w6c_fill_clob] in X |- *. tauto. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis INTRIN : w6c_intrin_law B.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6C_SET.

Theorem w6c_fill : w6c_fill_stmt B MT.
Proof using MTL INTRIN AMEMSET.
unfold w6c_fill_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos pp c2 lf sz
  Hctx H2 H3 H4 H9 H27 H12 H18 H20 Hsz Hc2 Hlf Hpp V118 V130 V138 HraE HhE.
destruct Hctx as (HJ & HR32 & HRc & HRsp & Hsp47 & HSTK & Hown & HF & HF1 & HF2 & HF32 & HFapp & HFp).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof asan_consts as (Hceil & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp16 & _).
unfold T_SEG_STK, ASTACK in *.
assert (HRb : 0x10007fffc000 <= R <= 2 ^ 47 - 0x220) by lia.
assert (HFb : 4096 <= F <= 2 ^ 47 - 1024) by lia.
assert (HFa : F + 1024 <= kLowShadowBeg \/ kHighMemBeg <= F).
{ unfold in_app, ASAN_CEIL in HFapp. lia. }
(* the shadow bytes of e62's hull lie in the shadow band, apart from the frame's own bytes *)
assert (Hband : forall n s, 0 < n <= 3 ->
  shadow_addr (F + 0x218) / 8 * 8 <= s < shadow_addr (F + 0x218 + n - 1) / 8 * 8 + 8 ->
  0 <= s < 2 ^ 64 /\ ~ (F + 0x214 <= s < F + 0x21c)).
{ intros n s Hn Hs. pose proof (cj_hull_band (F + 0x218) n s ltac:(lia) ltac:(lia) ltac:(lia) Hs) as X.
  unfold kLowMemEnd, kHighMemBeg in X. unfold kLowShadowBeg, kHighMemBeg in HFa. lia. }
(* ---- run 1: 0x822b0 .. the callee's entry ---- *)
pose proof (w6c_tentry W6C_F8 true [] W regs memc R F pp ltac:(unfold W6C_F8; lia) H9 H27 HRb HR32 HFb HF32
  ltac:(lia) ltac:(lia) V118 V130 V138 ltac:(intros _ o Ho; apply HFp; lia) I) as HS.
remember (Ereg regs (w6c_extra F 0 0 pp)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (w6c_extra F 0 0 pp)) E) by (subst E; apply env_agree_refl).
assert (U9 : bv_unsigned (ew E 9) = R) by (subst E; exact (w6c_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
assert (E12 : ew E 12 = Z_to_bv 64 sz) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (w6c_e32 regs F 0 0 pp)).
assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok rsegs w6c_Bx w6c_SH4 E (mrestrict (w_H W) memc)).
{ subst E. apply (w6c_shok4 regs (w_H W) memc F 0 0 pp H27 HFb HFapp).
  apply (ra_sub _ _ (F + 0x210) 104); [exact HraE | lia | lia]. }
clear HE.
unfold cfg_at. change (w64 W6C_F8) with (Z_to_bv 64 W6C_F8).
aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_SET;
  [ apply (w6c_tawr _ true _ _ _ _ _ _ _ F pos U32 Hown HF) | ].
(* the state at the callee's entry *)
w6c_ew HS E12. w6c_ew HS E32. w6c_ew HS U32. w6c_ew HS U9.
assert (KE1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x214 <= a < F + 0x218) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ apply (cb_kept_run (fun a => F + 0x214 <= a < F + 0x218) E (ss_mem (w6c_tss W6C_F8 true [])) (w_H W) memc memc (ms_mem ms)).
  - intros; reflexivity.
  - exact HFr.
  - intros a Ha. pose proof (w6c_tw E true a Ha) as X. rewrite U32 in X. exact X. }
w6c_rnth HS 1%nat Hr1.
assert (VS : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x214) 4 sz).
{ exact (w6c_field _ _ 32%nat F _ _ _ _ _ 0x214 4 (SOff 12 0) sz Hr1 U32' ltac:(cbn; tauto)
    ltac:(apply w6c_den0; [exact E12' | lia]) ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 W6C_RSET)
  by (w6c_reg HS (1%bv : bv 5); apply w6c_den_lit; unfold W6C_RSET; lia).
assert (R10 : getr (ms_regs ms) 10 = w64 (F + 0x218))
  by (w6c_reg HS (10%bv : bv 5); unfold w64; apply w6c_den_off; [exact E32' | lia | lia]).
assert (R11 : getr (ms_regs ms) 11 = w64 0) by (w6c_reg HS (11%bv : bv 5); unfold w64; apply w6c_den_lit; lia).
assert (R12 : getr (ms_regs ms) 12 = w64 sz) by (w6c_reg HS (12%bv : bv 5); unfold w64; apply w6c_den0; [exact E12' | lia]).
assert (R21 : getr (ms_regs ms) 21 = w64 (F + 0x210))
  by (w6c_reg HS (21%bv : bv 5); unfold w64; apply w6c_den_off; [exact E32' | lia | lia]).
assert (Kept1 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [1; 10; 11; 21]%bv -> getr (ms_regs ms) r = getr regs r).
{ eapply (regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity]. }
assert (Hk1 : forall rg : bv 5, In rg [2; 3; 4; 9; 18; 20; 27]%bv -> getr (ms_regs ms) rg = getr regs rg).
{ intros rg Hin. apply Kept1.
  - cbv [In] in Hin. repeat (destruct Hin as [<-|Hin]; [vm_compute; discriminate|]). destruct Hin.
  - intros X. cbv [In] in Hin, X. repeat (destruct Hin as [<-|Hin]; [repeat (destruct X as [X|X]; [discriminate X|]); exact X|]).
    destruct Hin. }
assert (Hsp1 : getr (ms_regs ms) 2 = w64 R) by (rewrite (Hk1 2%bv) by (cbv; tauto); exact H2).
(* ---- the call: __asan_memset(F + 0x218, 0, sz) ---- *)
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl).
cbn [ss_pc].
eapply SRr_bind.
{ apply (INTRIN OSet W6C_SET AMEMSET W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    (F + 0x218) 0 sz (R - sp0) (Z_to_bv 64 W6C_RSET) HJ R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Hsp1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - assert (HR16 : R mod 16 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.mod_divide in HR32; [|lia]. destruct HR32 as [q Hq]. exists (2 * q). lia. }
    rewrite Zminus_mod, HR16, Hsp16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite (Hk1 3%bv) by (cbv; tauto). exact H3.
  - rewrite (Hk1 4%bv) by (cbv; tauto). exact H4.
  - exact R1.
  - exact w6c_ret_set.
  - intros a Ha. split.
    + unfold awr_byte. right; right; right. exists 4, pos. split; [exact Hown|]. left.
      unfold in_zr. cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 4) with 1024. lia.
    + unfold ESTACK. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. unfold kLowShadowBeg, kHighMemBeg in HFa.
    pose proof alloc_ceiling_lt. lia.
  - apply (hm_ra_kept rsegs (w_H W) memc (w_H W) (ms_mem ms));
      [apply (ra_sub _ _ (F + 0x210) 104); [exact HraE | lia | lia]|].
    intros x Hx. apply KE1.
    + pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as X. unfold kLowMemEnd, kHighMemBeg in X. lia.
    + apply (hm_shadow_not_app x F 1024) in HFapp; [| unfold kHighMemEnd; lia]. lia.
  - intros Hn0. apply (hm_hull_kept rsegs (w_H W) memc (w_H W) (ms_mem ms)).
    + apply (hm_hull_sub _ (F + 0x210) 104); [exact HhE | lia | lia | lia].
    + intros s Hs Hne. destruct (Hband sz s ltac:(lia) Hs) as [Hs1 Hs2]. rewrite (KE1 s Hs1 ltac:(lia)). exact Hne.
  - exact I. }
cbv beta. intros W2 c3 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & HP2 & Ha02 & HD2 & HK2 & Hpr2).
replace (sp0 + (R - sp0)) with R in HK2 by lia.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x214 <= a < F + 0x218 + sz) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha X1 X2. rewrite (HK2 a Ha ltac:(lia) X2). apply KE1; [exact Ha | lia]. }
assert (G9 : getr regs2 9 = w64 R).
{ transitivity (getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia))|].
  rewrite (Hk1 9%bv) by (cbv; tauto). exact H9. }
assert (G27 : getr regs2 27 = w64 SHADOW_OFF).
{ transitivity (getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia))|].
  rewrite (Hk1 27%bv) by (cbv; tauto). exact H27. }
assert (G18 : getr regs2 18 = w64 c2).
{ transitivity (getr (ms_regs ms) 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia))|].
  rewrite (Hk1 18%bv) by (cbv; tauto). exact H18. }
assert (G20 : getr regs2 20 = w64 lf).
{ transitivity (getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia))|].
  rewrite (Hk1 20%bv) by (cbv; tauto). exact H20. }
assert (G21 : getr regs2 21 = w64 (F + 0x210)).
{ transitivity (getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact R21]. }
assert (KV : forall a n v, val_mem rsegs (mrestrict (w_H W) memc) a n v ->
  (forall i, 0 <= i < Z.of_nat n -> 0 <= a + i < 2 ^ 64 /\ ~ (F + 0x214 <= a + i < F + 0x218 + sz) /\ ~ (R - ESTACK <= a + i < R)) ->
  val_mem rsegs (mrestrict (w_H W) mem2) a n v).
{ intros a n v V X. apply (w6c_val_kept (w_H W) (w_H W) memc mem2 a n v V). intros i Hi.
  destruct (X i Hi) as (X1 & X2 & X3). exact (K2 (a + i) X1 X2 X3). }
pose proof (KV _ _ _ V118 ltac:(intros i Hi; cbn in Hi; unfold ESTACK; lia)) as V118'.
pose proof (KV _ _ _ V130 ltac:(intros i Hi; cbn in Hi; unfold ESTACK; lia)) as V130'.
pose proof (KV _ _ _ V138 ltac:(intros i Hi; cbn in Hi; unfold ESTACK; lia)) as V138'.
assert (VS2 : val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x214) 4 sz).
{ apply (w6c_val_kept (w_H W) (w_H W) (ms_mem ms) mem2 _ _ _ VS). intros i Hi. cbn in Hi.
  apply HK2; [lia | lia | unfold ESTACK; lia]. }
(* ---- run 2: 0x822c4 .. J ---- *)
pose proof (w6c_tentry W6C_RSET false [] W regs2 mem2 R F pp ltac:(unfold W6C_RSET; lia) G9 G27 HRb HR32 HFb HF32
  ltac:(lia) ltac:(lia) V118' V130' V138' ltac:(intros X; discriminate X) I) as HS2.
remember (Ereg regs2 (w6c_extra F 0 0 pp)) as E2 eqn:HE2.
assert (HAE2 : env_agree 32 (Ereg regs2 (w6c_extra F 0 0 pp)) E2) by (subst E2; apply env_agree_refl).
assert (F18 : ew E2 18 = Z_to_bv 64 c2) by (subst E2; rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl); exact G18).
assert (F20 : ew E2 20 = Z_to_bv 64 lf) by (subst E2; rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl); exact G20).
assert (F21 : ew E2 21 = Z_to_bv 64 (F + 0x210))
  by (subst E2; rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl); exact G21).
assert (F35 : ew E2 35 = Z_to_bv 64 pp) by (subst E2; exact (w6c_e35 regs2 F 0 0 pp)).
assert (SHOK2 : sh_ok rsegs w6c_Bx [] E2 (mrestrict (w_H W) mem2)) by constructor.
assert (U32b : bv_unsigned (ew E2 32) = F)
  by (subst E2; rewrite (w6c_e32 regs2 F 0 0 pp); apply unsigned_lit_small; lia).
clear HE2.
aj_run_to_tok w6c_tbl_ok HS2 HJ2 SHOK2 w6c_Bspan W6C_J;
  [ apply (w6c_tawr _ false _ _ _ _ _ _ _ F pos U32b Hown HF) | ].
w6c_ew HS2 F18. w6c_ew HS2 F20. w6c_ew HS2 F21. w6c_ew HS2 F35.
pose proof (w6c_frame_ro E2 _ _ HFr0) as KR2.
assert (KE2 : forall a, aview rsegs (w_H W) (ms_mem ms0) a = aview rsegs (w_H W) mem2 a).
{ intros a. unfold aview, mbyte. rewrite KR2. reflexivity. }
assert (Kept2 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [6; 13; 18; 20]%bv -> getr (ms_regs ms0) r = getr regs2 r).
{ eapply (regs_kept_of_st_ok rsegs _ _ _ regs2 _ (w_H W) _ HS2); [env_agree_chain HAE2 | vm_compute; reflexivity]. }
apply (w6c_post_of_run B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6C_J w6c_fill_clob
  (w6c_fill_wr R F sz) _ _ _ ms0 _ HS2 eq_refl eq_refl HJ2).
- eapply same_io_trans; [|eapply same_io_trans; [exact Hio2|]]; cb_kio.
- intros r Hr0 Hn. rewrite (Kept2 r Hr0 (w6c_fill_notin2 r Hn)).
  rewrite (w6c_reg_cs (ms_regs ms) regs2 r HP2 (w6c_fill_cs r Hr0 Hn)).
  exact (Kept1 r Hr0 (w6c_fill_notin1 r Hn)).
- intros a Ha Hn. unfold w6c_fill_wr, T_SEG_STK, ASTACK in Hn. cbv beta in Hn. rewrite KE2.
  apply K2; [exact Ha | intros X; apply Hn; right; exact X | intros X; apply Hn; left; unfold ESTACK in X; lia].
- split; [reflexivity|].
  split; [w6c_reg HS2 (13%bv : bv 5); unfold w64; apply w6c_den0; [exact F18' | lia]|].
  split; [w6c_reg HS2 (6%bv : bv 5); unfold w64; apply w6c_den0; [exact F20' | lia]|].
  split; [w6c_reg HS2 (18%bv : bv 5); unfold w64; apply w6c_den_off; [exact F35' | lia | lia]|].
  split; [w6c_reg HS2 (20%bv : bv 5); unfold w64; apply w6c_den0; [exact F21' | lia]|].
  split.
  + apply (w6c_val_kept (w_H W) (w_H W) mem2 (ms_mem ms0) _ _ _ VS2). intros i Hi. apply KE2.
  + intros i Hi. rewrite KE2. rewrite (HD2 i Hi). reflexivity.
Qed.
End d.
End b.

Print Assumptions w6c_fill.
