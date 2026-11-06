(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from part of proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v (link_ML, link_SMP, link_FFL, link_ASF, link_AMEMSET, link_AMEMCPY, tfib_ROB) for libreac/fuzz_grant: the facts are stated at GrantB and at the listing's instance PI_grant, the stack_malloc, bcmp and set_shadow_f5 entries of the memory-checking runtime, the walks' PALib and PALibF records, the shadow of the image and of its registered globals, the image's read-only tables and the image facts of ctrl_finish and reac_ctrl_parse are added; module paths changed. *)
(* The closing instances of the walks of fuzz_grant's program code: every Section
   hypothesis on the image-symbol record, the image and the memory-checking runtime
   that the walks of lib/A/Prog take, proved at fuzz_grant.asan's own record GrantB
   (lib/A/AD2l.v) and image instance PI_grant (GrantImg.v). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK04 YA0i YA0n YP09 YI04 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG05 YG0q YG0t YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import AB1v AF0l AF0m AD2l.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require AE2k AE2q AE2r AE2s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import SetShadowDef YF0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Rt Require SetShadow StackMalloc0 AF0s AF0u StackMalloc4.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable GrantSyms GrantList GrantAddr GrantPa GrantImg GrantPaLib GrantFrame GrantBase GrantRo GrantCloseChk.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantSweepModel GroupaModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- fuzz_grant.asan's registered globals ----------------------------------
   The 13 descriptors of the array __asan_register_elf_globals registers
   (asan_globals, 0xa1120, 0x340 bytes), as (beginning, size), read from the
   asan_globals array of the fuzz_grant.asan ELF this image is made from: POLL, HEAD_ACK,
   HEAD_MARK, __const.check_groupa.frame, .str.4, GRANT_GROUPB, TMPL_BOX_HB,
   TMPL_HEADAMP, GRANT_HEAD_ACK, GRANT_HEAD_MARK, JOIN_0013, JOIN_0014,
   CTRL_FRAMES. *)
Definition GRANT_GLOBS : list (Z * Z) :=
  [(0x20e80, 18); (0x20ec0, 34); (0x20f20, 34); (0x20f80, 50); (0x21020, 7); (0x21040, 204);
   (0x21140, 32); (0x21180, 32); (0x211c0, 34); (0x21220, 34); (0x212c0, 32); (0x21300, 32);
   (0x9c580, 264)].

(* The harness's own POLL table (fuzz/fuzz_grant.c, `static const uint8_t POLL[6][3]`). *)
Definition GRANT_POLLz : list Z := [0; 0; 4; 6; 0; 8; 16; 0; 17; 16; 17; 9; 17; 0; 17; 17; 17; 9].

(* ---- the checks, by computation on fuzz_grant.asan ------------------------------ *)
Lemma grant_vscan : vscan Tfib_zero_shadow Tfib_const_shadow (Pos.to_nat 4096) (IMG_LO / 8) (IMG_TOP / 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma grant_globs_chk : forallb (glob_chk Tfib_zero_shadow Tfib_const_shadow) GRANT_GLOBS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zs_align_chk : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0) && (0 <=? snd r))%bool Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zs_align : forall q m, In (q, m) Tfib_zero_shadow -> q mod 8 = 0 /\ m mod 8 = 0 /\ 0 <= m.
Proof.
intros q m Hin. pose proof (proj1 (forallb_forall _ _) zs_align_chk (q, m) Hin) as Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma grant_ro_segs_chk :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? AE2k.A_ofl_head))%bool tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- 1. the allocator laws ---------------------------------------------------------- *)
Lemma grant_LAWS : AR_laws tfibsegs GrantB.
Proof. exact (AR_laws_ok tfibsegs GrantB). Qed.

(* ---- 2. the walks' records PALib and PALibF ----------------------------------------- *)
Lemma grant_VAL : forall i, (i < 34)%nat -> pa_val (PAImg := PI_grant) (A_OBJ i) = grant_obj i.
Proof. intros i Hi. do 34 (destruct i as [|i]; [reflexivity|]). lia. Qed.

Lemma grant_BASE : pa_val (PAImg := PI_grant) A_TEXT = 0x806b0.
Proof. reflexivity. Qed.

Lemma grant_api_env : api_env tfibsegs GrantB.
Proof.
split; [|split].
- cbn [as_errno GrantB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno GrantB] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
  eexists. split; [do 3 right; left; reflexivity|].
  match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) =>
    let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end.
  lia.
- split; apply (ts_universe_drv GrantB GrantB_syms);
    cbn [as_code GrantB Tfib_code pc_malloc_ra0 pc_free_ra0 DRV_TRACES In];
    repeat (first [left; reflexivity | right]).
Qed.

Lemma grant_PALib : PALib (PI := PI_grant) GrantB.
Proof.
constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- rewrite !grant_VAL by lia. cbn [grant_obj]. lia.
- exact grant_api_env.
- reflexivity.
- reflexivity.
- rewrite grant_BASE. cbn [as_code GrantB Tfib_code pc_free_ra0 pc_malloc_ra0]. lia.
Qed.

Lemma grant_PALibF : PALibF (PI := PI_grant) GrantB.
Proof.
constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- rewrite !grant_VAL by lia. cbn [zseps zseps_from fst snd grant_obj as_uar_cell GrantB]. repeat split; lia.
Qed.

(* ---- 3. the model, the side stack's progress, the frame flags, the frame free -------- *)
Lemma grant_ML : model_laws (as_universe GrantB).
Proof. exact (model_laws_ok (as_universe GrantB) (ts_universe GrantB GrantB_syms)). Qed.

Lemma grant_SMP : stack_malloc_progressP GrantB.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe GrantB) s cid W Hc Hn). Qed.

Lemma grant_FFL : frame_flag_lawP tfibsegs GrantB.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ grant_LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ grant_LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (grant_img_cover ly S md L) as [C1 C2].
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma grant_ASF : astack_free_law tfibsegs GrantB.
Proof. exact (astack_free_law_ok tfibsegs GrantB). Qed.

(* ---- 4. the memory-checking runtime's entries the listing calls -------------------- *)
Lemma grant_sigma_memset : pa_sigma (PAImg := PI_grant) GS___asan_memset = 0x51c98.
Proof. reflexivity. Qed.
Lemma grant_sigma_memcpy : pa_sigma (PAImg := PI_grant) GS___asan_memcpy = 0x517fc.
Proof. reflexivity. Qed.
Lemma grant_sigma_bcmp : pa_sigma (PAImg := PI_grant) GS___interceptor_trampoline_bcmp = 0x42144.
Proof. reflexivity. Qed.
Lemma grant_sigma_ssf5 : pa_sigma (PAImg := PI_grant) GS___asan_set_shadow_f5 = 0x547c4.
Proof. reflexivity. Qed.
Lemma grant_sigma_sm0 : pa_sigma (PAImg := PI_grant) GS___asan_stack_malloc_0 = 0x3cda4.
Proof. reflexivity. Qed.
Lemma grant_sigma_sm1 : pa_sigma (PAImg := PI_grant) GS___asan_stack_malloc_1 = 0x3cf18.
Proof. reflexivity. Qed.
Lemma grant_sigma_sm2 : pa_sigma (PAImg := PI_grant) GS___asan_stack_malloc_2 = 0x3d0a8.
Proof. reflexivity. Qed.
Lemma grant_sigma_sm4 : pa_sigma (PAImg := PI_grant) GS___asan_stack_malloc_4 = 0x3d244.
Proof. reflexivity. Qed.

Lemma grant_AMEMSET : aintrin_realizes tfibsegs GrantB OSet (pa_sigma (PAImg := PI_grant) GS___asan_memset).
Proof.
rewrite grant_sigma_memset.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (AE2r.asan_memset_realizes GrantB grant_LAWS GrantB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.

Lemma grant_AMEMCPY : aintrin_realizes tfibsegs GrantB OCpy (pa_sigma (PAImg := PI_grant) GS___asan_memcpy).
Proof.
rewrite grant_sigma_memcpy.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
exact (AE2q.asan_memcpy_realizes GrantB grant_LAWS GrantB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.

Lemma grant_ABCMP : abcmp_realizes tfibsegs GrantB (pa_sigma (PAImg := PI_grant) GS___interceptor_trampoline_bcmp).
Proof. rewrite grant_sigma_bcmp. exact (AE2s.bcmp_icpt_contract GrantB grant_LAWS GrantB_syms). Qed.

Lemma grant_ASM0 : astack_malloc_realizes tfibsegs GrantB 0.
Proof. exact (StackMalloc0.stack_malloc0_contract GrantB grant_LAWS GrantB_syms). Qed.
Lemma grant_ASM1 : astack_malloc_realizes tfibsegs GrantB 1.
Proof. exact (AF0s.stack_malloc1_contract GrantB grant_LAWS GrantB_syms). Qed.
Lemma grant_ASM2 : astack_malloc_realizes tfibsegs GrantB 2.
Proof. exact (AF0u.stack_malloc2_contract GrantB grant_LAWS GrantB_syms). Qed.
Lemma grant_ASM4 : astack_malloc_realizes tfibsegs GrantB 4.
Proof. exact (StackMalloc4.stack_malloc4_contract GrantB grant_LAWS GrantB_syms). Qed.

Lemma grant_SSF5 : SetShadowDef.aset_shadow_realizes tfibsegs GrantB (pa_sigma (PAImg := PI_grant) GS___asan_set_shadow_f5) 0xf5.
Proof. rewrite grant_sigma_ssf5. exact (SetShadow.grant_set_shadow_f5 GrantB grant_LAWS GrantB_syms). Qed.

(* ---- 5. the read-only range lies below the sink's overflow head -------------------- *)
#[global] Instance grant_RO :
  @ro_below_ofl tfibsegs (pa_relro_lo (PAImg := PI_grant)) (pa_relro_hi (PAImg := PI_grant)) AE2k.tfib_sink_head.
Proof.
intros a [(s & Hin & Hw & Hr) | Hr]; cbn [YI16.sk_ofl_head AE2k.tfib_sink_head].
- pose proof (proj1 (forallb_forall _ _) grant_ro_segs_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb.
  cbn [orb] in Hb. apply Z.leb_le in Hb. lia.
- change (0x9c1a0 <= a < 0x9d568) in Hr. unfold AE2k.A_ofl_head. lia.
Qed.

(* ---- 6. the shadow of the image and of its registered globals ----------------------- *)
(* A shadow cell of the start-up certificate holds its byte in every state. *)
Lemma grant_shadow_cell : forall ly S (W : world tfibsegs) mem md s v,
  AR tfibsegs GrantB ly S W mem md -> In (z1 (ANum s) v) Tfib_const_shadow ->
  aview tfibsegs (w_H W) mem s = Some (YG0f.le_byte v 1 0).
Proof.
intros ly S W mem md s v HAR Hin.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite Forall_forall in HC.
assert (Hin' : In (z1 (ANum s) v) (as_const GrantB ly)).
{ cbn [as_const GrantB]. unfold Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hin. }
specialize (HC _ Hin'). unfold cell_holds, z1, c1 in HC. cbn [c_at c_val c_w aeval] in HC.
specialize (HC 0%nat ltac:(lia)). cbn [Z.of_nat] in HC. rewrite Z.add_0_r in HC. exact HC.
Qed.

(* A granule of a zero-shadow range of the certificate has shadow byte 0 in every state. *)
Lemma grant_zs_rd : forall ly S (W : world tfibsegs) mem md q m j,
  AR tfibsegs GrantB ly S W mem md -> In (q, m) Tfib_zero_shadow -> q / 8 <= j < (q + m) / 8 ->
  aview tfibsegs (w_H W) mem (SHADOW_OFF + j) = Some 0.
Proof.
intros ly S W mem md q m j HAR Hin Hj.
pose proof (al_zshadow _ _ grant_LAWS ly S W mem md (q, m) HAR (or_intror Hin)) as Hz. cbn [fst snd] in Hz.
destruct (zs_align q m Hin) as (Hq & Hm & Hm0).
assert (E : (q + m) / 8 = q / 8 + m / 8).
{ pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
  replace (q + m) with (m + q / 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
replace (SHADOW_OFF + j) with (shadow_of_addr SHADOW_OFF q + (j - q / 8)) by (unfold shadow_of_addr; lia).
apply Hz. lia.
Qed.

Lemma grant_img_shadow_vis : img_shadow_vis tfibsegs GrantB.
Proof.
intros ly S W mem md a HAR Ha. unfold shadow_addr.
assert (E8 : 8 * (IMG_TOP / 8) = IMG_TOP) by (vm_compute; reflexivity).
assert (Hj : IMG_LO / 8 <= a / 8 < IMG_TOP / 8).
{ split; [apply Z.div_le_mono; lia | apply Z.div_lt_upper_bound; lia]. }
destruct (vscan_ok _ _ _ _ _ grant_vscan (a / 8) Hj) as [(q & m & Hin & Hq) | Hc].
- rewrite (grant_zs_rd ly S W mem md q m (a / 8) HAR Hin Hq). discriminate.
- apply existsb_exists in Hc as (c & Hin & Hb). destruct (is_shc_eq _ _ Hb) as [v ->].
  rewrite (grant_shadow_cell ly S W mem md _ v HAR Hin). discriminate.
Qed.

Lemma grant_globs_marked : globs_marked tfibsegs GrantB GRANT_GLOBS.
Proof.
intros ly S W mem md q sz Hin HAR.
pose proof (proj1 (forallb_forall _ _) grant_globs_chk (q, sz) Hin) as Hb. unfold glob_chk in Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb Hlast]. apply andb_prop in Hb as [Hb Hfull]. apply andb_prop in Hb as [Hq Hsz].
apply Z.eqb_eq in Hq. apply Z.leb_le in Hsz.
apply existsb_exists in Hfull as ([r0 m0] & Hr & Hf). cbn [fst snd] in Hf.
apply andb_prop in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf1. apply Z.leb_le in Hf2.
destruct (zs_align r0 m0 Hr) as (Hr8 & Hm8 & Hm0).
split; [exact Hq|]. split; [exact Hsz|]. intros i Hi.
pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. pose proof (Z.div_mod r0 8 ltac:(lia)) as Dr.
pose proof (Z.div_mod sz 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as Bs.
pose proof (Z.div_mod (sz + 7) 8 ltac:(lia)) as Ds7. pose proof (Z.mod_pos_bound (sz + 7) 8 ltac:(lia)) as Bs7.
pose proof (Z.div_mod (r0 + m0) 8 ltac:(lia)) as Drm. pose proof (Z.mod_pos_bound (r0 + m0) 8 ltac:(lia)) as Brm.
destruct (i <? sz / 8) eqn:Hlt.
- apply Z.ltb_lt in Hlt. unfold shadow_of_addr.
  replace (SHADOW_OFF + q / 8 + i) with (SHADOW_OFF + (q / 8 + i)) by lia.
  apply (grant_zs_rd ly S W mem md r0 m0); [exact HAR | exact Hr | lia].
- apply Z.ltb_ge in Hlt.
  assert (Hi' : i = sz / 8) by lia.
  apply orb_true_iff in Hlast as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; lia|].
  apply existsb_exists in H0 as (c & Hc & Hcb). apply is_shv_eq in Hcb. subst c. subst i.
  unfold shadow_of_addr.
  rewrite (grant_shadow_cell ly S W mem md _ _ HAR Hc). rewrite le_byte1 by lia. reflexivity.
Qed.

Lemma grant_glob_POLL : In (pa_val (PAImg := PI_grant) (A_OBJ 6), 18) GRANT_GLOBS.
Proof. rewrite grant_VAL by lia. cbn [grant_obj GRANT_GLOBS In]. repeat (first [left; reflexivity | right]). Qed.
Lemma grant_glob_HEAD_ACK : In (pa_val (PAImg := PI_grant) (A_OBJ 4), 34) GRANT_GLOBS.
Proof. rewrite grant_VAL by lia. cbn [grant_obj GRANT_GLOBS In]. repeat (first [left; reflexivity | right]). Qed.
Lemma grant_glob_HEAD_MARK : In (pa_val (PAImg := PI_grant) (A_OBJ 5), 34) GRANT_GLOBS.
Proof. rewrite grant_VAL by lia. cbn [grant_obj GRANT_GLOBS In]. repeat (first [left; reflexivity | right]). Qed.
Lemma grant_glob_GROUPB : In (pa_val (PAImg := PI_grant) (A_OBJ 19), 204) GRANT_GLOBS.
Proof. rewrite grant_VAL by lia. cbn [grant_obj GRANT_GLOBS In]. repeat (first [left; reflexivity | right]). Qed.
Lemma grant_glob_GRANT_HEAD_ACK : In (pa_val (PAImg := PI_grant) (A_OBJ 20), 34) GRANT_GLOBS.
Proof. rewrite grant_VAL by lia. cbn [grant_obj GRANT_GLOBS In]. repeat (first [left; reflexivity | right]). Qed.
Lemma grant_glob_GRANT_HEAD_MARK : In (pa_val (PAImg := PI_grant) (A_OBJ 21), 34) GRANT_GLOBS.
Proof. rewrite grant_VAL by lia. cbn [grant_obj GRANT_GLOBS In]. repeat (first [left; reflexivity | right]). Qed.

(* The ranges the walks read lie in one zero-shadow range of the certificate. *)
Lemma grant_zs_ROW : in_zs GrantB (pa_val (PAImg := PI_grant) (A_OBJ 18)) 24.
Proof. rewrite grant_VAL by lia. apply in_zs_of_b. vm_compute. reflexivity. Qed.
Lemma grant_zs_TMPL : in_zs GrantB 0x21180 32.
Proof. apply in_zs_of_b. vm_compute. reflexivity. Qed.
Lemma grant_zs_JT : in_zs GrantB (pa_val (PAImg := PI_grant) (A_OBJ 24)) 40.
Proof. rewrite grant_VAL by lia. apply in_zs_of_b. vm_compute. reflexivity. Qed.
Lemma grant_zs_T0 : in_zs GrantB (pa_val (PAImg := PI_grant) (A_OBJ 9)) 16.
Proof. rewrite grant_VAL by lia. apply in_zs_of_b. vm_compute. reflexivity. Qed.

(* The 64-byte margin of each table read inside the image. *)
Lemma grant_margin : forall i n, (i < 34)%nat ->
  ((IMG_LO + 64 <=? grant_obj i) && (grant_obj i + n + 64 <=? IMG_TOP))%bool = true ->
  IMG_LO + 64 <= pa_val (PAImg := PI_grant) (A_OBJ i) /\ pa_val (PAImg := PI_grant) (A_OBJ i) + n + 64 <= IMG_TOP.
Proof.
intros i n Hi Hb. rewrite grant_VAL by exact Hi. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. split; [exact H1 | exact H2].
Qed.
Lemma grant_rng_POLL : IMG_LO + 64 <= pa_val (PAImg := PI_grant) (A_OBJ 6) /\ pa_val (PAImg := PI_grant) (A_OBJ 6) + 18 + 64 <= IMG_TOP.
Proof. apply grant_margin; [lia | vm_compute; reflexivity]. Qed.
Lemma grant_rng_HEAD_ACK : IMG_LO + 64 <= pa_val (PAImg := PI_grant) (A_OBJ 4) /\ pa_val (PAImg := PI_grant) (A_OBJ 4) + 34 + 64 <= IMG_TOP.
Proof. apply grant_margin; [lia | vm_compute; reflexivity]. Qed.
Lemma grant_rng_HEAD_MARK : IMG_LO + 64 <= pa_val (PAImg := PI_grant) (A_OBJ 5) /\ pa_val (PAImg := PI_grant) (A_OBJ 5) + 34 + 64 <= IMG_TOP.
Proof. apply grant_margin; [lia | vm_compute; reflexivity]. Qed.
Lemma grant_rng_T0 : IMG_LO + 64 <= pa_val (PAImg := PI_grant) (A_OBJ 9) /\ pa_val (PAImg := PI_grant) (A_OBJ 9) + 16 + 64 <= IMG_TOP.
Proof. apply grant_margin; [lia | vm_compute; reflexivity]. Qed.
Lemma grant_rng_ROW : IMG_LO + 64 <= pa_val (PAImg := PI_grant) (A_OBJ 18) /\ pa_val (PAImg := PI_grant) (A_OBJ 18) + 24 + 64 <= IMG_TOP.
Proof. apply grant_margin; [lia | vm_compute; reflexivity]. Qed.
Lemma grant_rng_GROUPB : IMG_LO + 64 <= pa_val (PAImg := PI_grant) (A_OBJ 19) /\ pa_val (PAImg := PI_grant) (A_OBJ 19) + 204 + 64 <= IMG_TOP.
Proof. apply grant_margin; [lia | vm_compute; reflexivity]. Qed.
Lemma grant_rng_GRANT_HEAD_ACK : IMG_LO + 64 <= pa_val (PAImg := PI_grant) (A_OBJ 20) /\ pa_val (PAImg := PI_grant) (A_OBJ 20) + 34 + 64 <= IMG_TOP.
Proof. apply grant_margin; [lia | vm_compute; reflexivity]. Qed.
Lemma grant_rng_GRANT_HEAD_MARK : IMG_LO + 64 <= pa_val (PAImg := PI_grant) (A_OBJ 21) /\ pa_val (PAImg := PI_grant) (A_OBJ 21) + 34 + 64 <= IMG_TOP.
Proof. apply grant_margin; [lia | vm_compute; reflexivity]. Qed.
Lemma grant_rng_JT : IMG_LO + 64 <= pa_val (PAImg := PI_grant) (A_OBJ 24) /\ pa_val (PAImg := PI_grant) (A_OBJ 24) + 40 + 64 <= IMG_TOP.
Proof. apply grant_margin; [lia | vm_compute; reflexivity]. Qed.
Lemma grant_rng_TMPL : IMG_LO + 64 <= 0x21180 /\ 0x21180 + 32 + 64 <= IMG_TOP.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* ---- 7. the image's read-only tables, from the rom bytes --------------------------- *)
#[local] Notation PRLO := (pa_relro_lo (PAImg := PI_grant)).
#[local] Notation PRHI := (pa_relro_hi (PAImg := PI_grant)).
Ltac tbl_obj i :=
  let H := fresh "H" in let mem := fresh "mem" in let HR := fresh "HR" in
  intros H mem HR; rewrite (grant_VAL i) by lia; cbn [grant_obj];
  apply (arodata_garr8 tfibsegs 0x9c1a0 0x9d568 GrantB); [vm_compute; reflexivity | exact HR].

(* GRANT_GROUPB (object 19, 0x21040, 204 bytes): reac_ctrl_identity_poll_block,
   reac_ctrl_build_grant_sweep and the entry function's group-B loop. *)
Lemma grant_tbl_GROUPB : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  garr8 tfibsegs (mrestrict H mem) (pa_val (PAImg := PI_grant) (A_OBJ 19)) GBallz.
Proof. tbl_obj 19%nat. Qed.
(* GRANT_HEAD_ACK and GRANT_HEAD_MARK (objects 20, 21): reac_ctrl_build_grant_sweep. *)
Lemma grant_tbl_GRANT_HEAD_ACK : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  garr8 tfibsegs (mrestrict H mem) (pa_val (PAImg := PI_grant) (A_OBJ 20)) HEAD_ACK34z.
Proof. tbl_obj 20%nat. Qed.
Lemma grant_tbl_GRANT_HEAD_MARK : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  garr8 tfibsegs (mrestrict H mem) (pa_val (PAImg := PI_grant) (A_OBJ 21)) HEAD_MARK34z.
Proof. tbl_obj 21%nat. Qed.
(* HEAD_ACK and HEAD_MARK of the harness (objects 4, 5): the entry function's sweep phase. *)
Lemma grant_tbl_HEAD_ACK : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  garr8 tfibsegs (mrestrict H mem) (pa_val (PAImg := PI_grant) (A_OBJ 4)) HEAD_ACK34z.
Proof. tbl_obj 4%nat. Qed.
Lemma grant_tbl_HEAD_MARK : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  garr8 tfibsegs (mrestrict H mem) (pa_val (PAImg := PI_grant) (A_OBJ 5)) HEAD_MARK34z.
Proof. tbl_obj 5%nat. Qed.
(* POLL of the harness (object 6, 18 bytes): the entry function's group-B loop. *)
Lemma grant_tbl_POLL : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  garr8 tfibsegs (mrestrict H mem) (pa_val (PAImg := PI_grant) (A_OBJ 6)) GRANT_POLLz.
Proof. tbl_obj 6%nat. Qed.
(* __const.check_groupa.frame (object 9): the 16 bytes check_groupa copies. *)
Lemma grant_tbl_T0 : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  garr8 tfibsegs (mrestrict H mem) (pa_val (PAImg := PI_grant) (A_OBJ 9)) T0z.
Proof. tbl_obj 9%nat. Qed.
(* TMPL_HEADAMP (0x21180, 32 bytes), the template ctrl_lay_block copies (TM). *)
Lemma grant_tbl_TMPL : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  garr8 tfibsegs (mrestrict H mem) 0x21180 T32z.
Proof.
intros H mem HR. apply (arodata_garr8 tfibsegs 0x9c1a0 0x9d568 GrantB); [vm_compute; reflexivity | exact HR].
Qed.

(* ctrl_lay_block's row (object 18, in .data.rel.ro) and jump table (object 24). *)
Ltac row_obj i :=
  let H := fresh "H" in let mem := fresh "mem" in let HR := fresh "HR" in
  intros H mem HR; rewrite (grant_VAL i) by lia; cbn [grant_obj]; apply garr8_val_mem;
  apply (arodata_garr8 tfibsegs 0x9c1a0 0x9d568 GrantB); [vm_compute; reflexivity | exact HR].
Lemma grant_row_k : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  val_mem tfibsegs (mrestrict H mem) (pa_val (PAImg := PI_grant) (A_OBJ 18) + 2) 1 2.
Proof. row_obj 18%nat. Qed.
Lemma grant_row_tm : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  val_mem tfibsegs (mrestrict H mem) (pa_val (PAImg := PI_grant) (A_OBJ 18) + 8) 8 0x21180.
Proof. row_obj 18%nat. Qed.
Lemma grant_row_ao : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  val_mem tfibsegs (mrestrict H mem) (pa_val (PAImg := PI_grant) (A_OBJ 18) + 16) 1 18.
Proof. row_obj 18%nat. Qed.
Lemma grant_row_al : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  val_mem tfibsegs (mrestrict H mem) (pa_val (PAImg := PI_grant) (A_OBJ 18) + 17) 1 3.
Proof. row_obj 18%nat. Qed.
Lemma grant_jt_e : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  val_mem tfibsegs (mrestrict H mem) (pa_val (PAImg := PI_grant) (A_OBJ 24) + 8) 4 0x621e4.
Proof. row_obj 24%nat. Qed.
(* The jump table's entry lands on ctrl_lay_block's case at +0x1dc. *)
Lemma grant_jt_eq : pa_val (PAImg := PI_grant) (A_OBJ 24) + 0x621e4 = pa_val (PAImg := PI_grant) A_TEXT + AF_ctrl_lay_block + 0x1dc.
Proof. rewrite grant_VAL by lia. rewrite grant_BASE. reflexivity. Qed.
Lemma grant_je_rng : 0 <= 0x621e4 < 2 ^ 31.
Proof. lia. Qed.
(* The row and the jump table do not overlap. *)
Lemma grant_row_jt : pa_val (PAImg := PI_grant) (A_OBJ 18) + 24 <= pa_val (PAImg := PI_grant) (A_OBJ 24) \/
  pa_val (PAImg := PI_grant) (A_OBJ 24) + 40 <= pa_val (PAImg := PI_grant) (A_OBJ 18).
Proof. rewrite !grant_VAL by lia. cbn [grant_obj]. lia. Qed.

(* ---- 8. the image facts of ctrl_finish (CtrlFinish.v) ---------------------------- *)
(* Every address of the image's range lies in one of the four loaded segments. *)
Ltac seg_bnd := match goal with |- Z.le ?lo ?x /\ Z.lt ?x (Z.add ?lo' ?sz) =>
  let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end; lia.
Lemma grant_in_img : forall a, IMG_LO <= a < IMG_TOP -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
destruct (Z.lt_ge_cases a 0x30000) as [H0|H0]; [eexists; split; [left; reflexivity | seg_bnd]|].
destruct (Z.lt_ge_cases a 0x9c000) as [H1|H1]; [eexists; split; [right; left; reflexivity | seg_bnd]|].
destruct (Z.lt_ge_cases a 0x9e000) as [H2|H2]; [eexists; split; [right; right; left; reflexivity | seg_bnd]|].
eexists; split; [do 3 right; left; reflexivity | seg_bnd].
Qed.
(* HGOTimg, HCELimg: the shadow base's GOT word (object 1) and its cell (object 32). *)
Lemma grant_cf_gotimg : forall a, pa_val (PAImg := PI_grant) (A_OBJ 1) <= a < pa_val (PAImg := PI_grant) (A_OBJ 1) + 8 ->
  in_img (pa_segs (PAImg := PI_grant)) a.
Proof. intros a Ha. rewrite (grant_VAL 1) in Ha by lia. cbn [grant_obj] in Ha. apply grant_in_img. lia. Qed.
Lemma grant_cf_celimg : forall a, pa_val (PAImg := PI_grant) (A_OBJ 32) <= a < pa_val (PAImg := PI_grant) (A_OBJ 32) + 8 ->
  in_img (pa_segs (PAImg := PI_grant)) a.
Proof. intros a Ha. rewrite (grant_VAL 32) in Ha by lia. cbn [grant_obj] in Ha. apply grant_in_img. lia. Qed.
(* HROWimg, HROWsep: the 3 bytes of the CTRL_FRAMES row (object 18) ctrl_finish reads. *)
Lemma grant_cf_rowimg : forall a, pa_val (PAImg := PI_grant) (A_OBJ 18) + 18 <= a < pa_val (PAImg := PI_grant) (A_OBJ 18) + 18 + 3 ->
  in_img (pa_segs (PAImg := PI_grant)) a.
Proof. intros a Ha. rewrite (grant_VAL 18) in Ha by lia. cbn [grant_obj] in Ha. apply grant_in_img. lia. Qed.
Lemma grant_cf_rowsep :
  (pa_val (PAImg := PI_grant) (A_OBJ 18) + 21 <= pa_val (PAImg := PI_grant) (A_OBJ 1) \/
   pa_val (PAImg := PI_grant) (A_OBJ 1) + 8 <= pa_val (PAImg := PI_grant) (A_OBJ 18) + 18) /\
  (pa_val (PAImg := PI_grant) (A_OBJ 18) + 21 <= pa_val (PAImg := PI_grant) (A_OBJ 32) \/
   pa_val (PAImg := PI_grant) (A_OBJ 32) + 8 <= pa_val (PAImg := PI_grant) (A_OBJ 18) + 18).
Proof. rewrite !grant_VAL by lia. cbn [grant_obj]. lia. Qed.
(* tctrl_finish_spec's premises on the row (CtrlFinish.v:274-275): its 3 bytes, and
   that they are marked usable. *)
Lemma grant_cf_row : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  garr8 tfibsegs (mrestrict H mem) (pa_val (PAImg := PI_grant) (A_OBJ 18) + 18) [16; 6; 2].
Proof.
intros H mem HR. rewrite (grant_VAL 18) by lia. cbn [grant_obj].
apply (arodata_garr8 tfibsegs 0x9c1a0 0x9d568 GrantB); [vm_compute; reflexivity | exact HR].
Qed.
Lemma grant_cf_row_ra : forall ly S (W : world tfibsegs) mem md,
  AR tfibsegs GrantB ly S W mem md ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (pa_val (PAImg := PI_grant) (A_OBJ 18) + 18) 3.
Proof.
intros ly S W mem md HAR. eapply (ro_usable tfibsegs GrantB grant_LAWS ly S W mem md); [exact HAR|].
rewrite (grant_VAL 18) by lia. apply in_zs_of_b. vm_compute. reflexivity.
Qed.

(* ---- 9. the image facts of reac_ctrl_parse (CtrlParse.v) -------------------------- *)
(* .str.4 (object 15, 0x21020, a registered global of 7 bytes): the six 0xff bytes the
   bcmp wrapper compares the frame with. *)
Lemma grant_glob_BCAST : In (pa_val (PAImg := PI_grant) (A_OBJ 15), 7) GRANT_GLOBS.
Proof. rewrite grant_VAL by lia. cbn [grant_obj GRANT_GLOBS In]. repeat (first [left; reflexivity | right]). Qed.
Lemma grant_rng_BCAST : IMG_LO + 64 <= pa_val (PAImg := PI_grant) (A_OBJ 15) /\ pa_val (PAImg := PI_grant) (A_OBJ 15) + 6 + 64 <= IMG_TOP.
Proof. apply grant_margin; [lia | vm_compute; reflexivity]. Qed.
Lemma grant_bcast_val : forall (H : word -> bool) mem,
  arodata_okP tfibsegs PRLO PRHI GrantB (aview tfibsegs H mem) ->
  forall i, 0 <= i < 6 -> aview tfibsegs H mem (pa_val (PAImg := PI_grant) (A_OBJ 15) + i) = Some 255.
Proof.
intros H mem HR i Hi. rewrite (grant_VAL 15) by lia. cbn [grant_obj].
replace i with (Z.of_nat (Z.to_nat i)) by lia.
assert (Hj : (Z.to_nat i < length [255; 255; 255; 255; 255; 255])%nat) by (cbn [length]; lia).
rewrite (arodata_aview_tbl tfibsegs 0x9c1a0 0x9d568 GrantB 0x21020 [255; 255; 255; 255; 255; 255] H mem
  ltac:(vm_compute; reflexivity) HR _ Hj).
f_equal. destruct (Z.to_nat i) as [|[|[|[|[|[|k]]]]]]; try reflexivity. cbn [length] in Hj. lia.
Qed.

End b.
