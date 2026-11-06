(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 (pa_i_memset_at, as
   hbp_i_memset_at; pa_i_bv5_cases, pa_i_cs, pa_i_pres and pa_i_mod16_sub, as hbp_i_*; pa_int7's route, one engine state
   up to each call and a fresh one after it) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618
   (pa_piece_int7, as hbp_piece_int7) for reac-pw/fuzz_headamp's image B: the block walked new against image B's own
   instructions (the scope stores of e, __asan_memset of e's body, the two header words, the out-of-line pod_write_ent
   under PweSpec.pod_write_ent_specX, the restores of the loop's three values), the cut states of lib/AU/HPgSeg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropInt.v; 532 of its 586 lines of code are new or changed and 907 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the builder piece W8 of
   LLVMFuzzerTestOneInput 0x80c40, J 0x82618 -> C 0x81888 / CL 0x82a18 (pod.h:428-433), composed from the blocks of
   lib/AU/HPgW8BKit.v and the two calls of lib/AU/HPgW8BCall.v: lib/AU/HPgSeg.v hsu_piece_W8_stmt at
   headamp_himg_B / headamp_bld_B. Proves no function (kind: segment lemma).

   THE WALK. A (the check of pp->len, the capacity test, the arguments) -> pod_write_ent 0x84634 -> on `first` = 0,
   C0; on `first` = 1, C1 (n_ent := n_ent + 1 and the arguments of the record copy) -> __asan_memcpy 0x51d8c -> C2;
   then the thirteen scope-closing stores of e62 (lib/AU/HPgSteps.v hdu_scope_e62_out, which also makes the pod
   index a1 + 1 and s7 = -8) and D (the loop's test).

   WHAT THE PIECE WRITES, and so what the two cuts it ends at carry: the n = |enc_pod ed| bytes at buf[len] and the
   len cell (pod_write_ent), on `first` = 1 also the n_ent cell and ent[n_ent] (the record copy), e62's thirteen
   shadow granules (closed again, 0xf8), and the two callees' stacks below R. Every other byte is as at J, so the
   first block holds the image of the record with one more pod (lib/AU/HPgW8ImgU.v wiu_final) and the frame's shadow
   is the prologue's again.

   REGISTERS AND R-CELLS: s1 = R (x9), s2 = pp + 0x4000 (x18), s3 = the frame's shadow base (x19), s4 = &e62 (x20),
   s5 (x21) and s10 (x26) take the cursor a3 (x13) and what is left t1 (x6) at J, s7 (x23) = pp at J and -8 at the
   end, s11 (x27) = K; R+0x150, R+0x140, R+0x158, R+0x128, R+0xe0, R+0x120, R+0xd8, R+0xd0. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import PweSpec HPgW8BKit HPgW8ImgU HPgW8BCall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ================================ the bytes a step leaves alone ================================
   A step of the walk may end in a later world (a callee's post), so "unchanged" relates two views. *)
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition hw8_un (H H' : word -> bool) (m m' : word -> option byte) (P : Z -> Prop) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H' m' a = aview rsegs H m a.
Lemma hw8_un_trans : forall H1 H2 H3 m1 m2 m3 (P Q : Z -> Prop),
hw8_un H1 H2 m1 m2 P -> hw8_un H2 H3 m2 m3 Q -> hw8_un H1 H3 m1 m3 (fun a => P a \/ Q a).
Proof. intros H1 H2 H3 m1 m2 m3 P Q U1 U2 a Ha Hn. rewrite (U2 a Ha) by tauto. apply U1; tauto. Qed.
Lemma hw8_un_weaken : forall H H' m m' (P Q : Z -> Prop),
hw8_un H H' m m' P -> (forall a, P a -> Q a) -> hw8_un H H' m m' Q.
Proof. intros H H' m m' P Q U HPQ a Ha Hn. apply U; [exact Ha|]. intros Hp. exact (Hn (HPQ a Hp)). Qed.
Lemma hw8_un_val : forall H H' m m' (P : Z -> Prop) a n v,
hw8_un H H' m m' P -> val_mem rsegs (mrestrict H m) a n v ->
0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat n -> ~ P x) ->
val_mem rsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' P a n v U V H0 H1 HP kk Hk.
rewrite (mbyte_of_aview rsegs H H' m m' (a + Z.of_nat kk)); [exact (V kk Hk)|].
apply U; [lia | apply HP; lia].
Qed.
Lemma hw8_un_bytes : forall H H' m m' (P : Z -> Prop) a l,
hw8_un H H' m m' P -> hm_bytes rsegs H m a l ->
0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat (length l) -> ~ P x) ->
hm_bytes rsegs H' m' a l.
Proof.
intros H H' m m' P a l U Hb H0 H1 HP.
apply (hm_bytes_kept rsegs H m H' m' a l Hb). intros x Hx. apply U; [lia | apply HP; lia].
Qed.
Lemma hw8_un_fsh : forall H H' m m' (P : Z -> Prop) F pat,
hw8_un H H' m m' P -> hd_fsh rsegs H m F pat ->
0 <= shadow_addr F -> shadow_addr F + Z.of_nat (length pat) <= 2 ^ 64 ->
(forall i, 0 <= i < Z.of_nat (length pat) -> ~ P (shadow_addr F + i)) ->
hd_fsh rsegs H' m' F pat.
Proof.
intros H H' m m' P F pat U Hf H0 H1 HP.
apply (hm_fsh_kept rsegs H m H' m' F pat Hf). intros i Hi. apply U; [lia | apply HP; lia].
Qed.

(* application memory and the shadow map are apart *)
Lemma hw8_app_sh_apart : forall p n F,
in_app p n -> 0 <= n -> 4096 <= F -> F + 1024 <= alloc_ceiling ->
p + n <= shadow_addr F \/ shadow_addr F + 128 <= p.
Proof.
intros p n F Happ Hn HF0 HFc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Happ as (H1 & [H2 | (H2 & H3)]);
unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
[left | right]; Z.div_mod_to_equations; lia.
Qed.

(* a callee-saved register of a call that keeps them *)
Lemma hw8_pres_bv : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' HP r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hr. Qed.
End u.

Ltac hw8_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.
Ltac hw8_notin :=
  let H := fresh "H" in intros H; cbn [In] in H;
  repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
Ltac hw8_nz := vm_compute; discriminate.
(* two ranges that are apart hold no address in common; as an implication, so that no disjunction of the walk's
   context reaches `lia` (which case-splits over the whole context) *)
Lemma hw8_apart_l : forall u v w z x, (u + v <= w \/ w + z <= u) -> u <= x < u + v -> w <= x < w + z -> False.
Proof. intros u v w z x [H|H] H1 H2; lia. Qed.


Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis PWE : pod_write_ent_specX rsegs B MT HW8_PWE.
Hypothesis ACPY : aintrin_realizes rsegs B OCpy HW8_MEMCPY.
Hypothesis BLKA : hw8_blkA_stmt B.
Hypothesis BLKC0 : hw8_blkC0_stmt B.
Hypothesis BLKC1 : hw8_blkC1_stmt B.
Hypothesis BLKC2 : hw8_blkC2_stmt B.
Hypothesis BLKD : hw8_blkD_stmt B.
Hypothesis JF : hw8_J_facts_stmt B MT.
Hypothesis FIN : hw8_finish_stmt B MT.

(* the frame's address does not move inside the journal *)
Lemma hw8_fa_eq : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world rsegs) mem' md' k cid pos,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k cid pos HJ.
pose proof HJ as (_ & Hly & _). unfold frame_addr.
destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.

Theorem hsu_piece_W8_B : hsu_piece_W8_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof.
intros cx POST rest i k HST HFC HFCL ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed Hi Hk HJcut.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_lt rc) as Hc47.
assert (HT : T_SEG_STK = 16384) by reflexivity.
assert (HTp : T_pwe_STK = 4144) by reflexivity.
assert (HE : ESTACK = 4096) by reflexivity.
assert (HOL : OFF_LEN = 16384) by reflexivity.
assert (HOE : OFF_ENT = 16404) by reflexivity.
assert (HONE : OFF_N_ENT = 19732) by reflexivity.
assert (HES4 : ENT_SIZE = 104) by reflexivity.
assert (HPS : PP_SIZE = 19744) by reflexivity.
assert (HPB : POD_BUF_MAX = 16384) by reflexivity.
pose proof (JF cx rest sh np ps cnt es rr r ed ly2 S2 W2 regs2 mem2 md2 HST HJcut) as HFX.
cbv zeta in HFX.
destruct HFX as (HJ2 & Hev & Hpp2 & Hfresh & Hown4 & Hfr2 & HFa & R2 & R3 & R4 & R9 & R18 & R19 & R20 & R23 & R27 &
  V150 & V140 & V158 & V128 & Ve0 & V120 & Vd8 & Vd0 & HEM & HIMG & VLEN & HNE & HFSH & Hpp16 & Happ & Hpp0 & Hppc &
  HF32 & HFapp & HF0 & HFc & HpF & HRc & HR32 & HRsz & Hsp16 & Hsp47 & HSTK & HL & HL8 & Hwf & Hes32 & Hkkcnt &
  Hcnt & Hfs01 & Hfs & HPV & HPAE & HES & Hps2).
set (R := e_R (x_e cx)) in *. set (F := e_F (x_e cx)) in *. set (pp := e_pp (x_e cx)) in *.
set (L := Z.of_nat (length (pc_buf (PbCut sh ps (Some es))))) in *.
pose proof Hwf as (Hty & Hbody & Hsz).
pose proof (zlen_enc_pod ed Hwf) as Henc.
pose proof (pad8_bound (e_size ed)) as Hpad.
assert (Hpwe : pwe_len ed = 8 + e_size ed + pad8 (e_size ed)) by exact Henc.
assert (Hpwe60 : 8 <= pwe_len ed <= 60) by lia.
assert (Hlem : length (ent_mem ed) = 104%nat) by (apply length_ent_mem; rewrite Hbody; lia).
assert (Hkk : 0 <= Z.of_nat (length es) < 32) by lia.
assert (Hpp8 : pp mod 8 = 0).
{ apply Z.mod_divide in Hpp16; [|lia]. destruct Hpp16 as [q Hq]. rewrite Hq.
  replace (q * 16) with ((q * 2) * 8) by ring. apply Z_mod_mult. }
assert (HF8 : F mod 8 = 0).
{ apply Z.mod_divide in HF32; [|lia]. destruct HF32 as [q Hq]. rewrite Hq.
  replace (q * 32) with ((q * 4) * 8) by ring. apply Z_mod_mult. }
assert (Hsa0 : 0 <= shadow_addr F).
{ unfold shadow_addr, SHADOW_OFF. assert (0 <= F / 8) by (apply Z.div_pos; lia). lia. }
assert (Hsa64 : shadow_addr F + 128 <= 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. assert (F / 8 <= F) by (apply Z.div_le_upper_bound; lia). lia. }
assert (HshR : shadow_addr F + 128 <= R - T_SEG_STK).
{ unfold shadow_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. }
assert (Hsapp : pp + PP_SIZE <= shadow_addr F \/ shadow_addr F + 128 <= pp)
  by (apply hw8_app_sh_apart; [exact Happ | lia | exact HF0 | exact HFc]).
assert (HsaF : F + 1024 <= shadow_addr F \/ shadow_addr F + 128 <= F)
  by (apply hw8_app_sh_apart; [exact HFapp | lia | exact HF0 | exact HFc]).
(* the three apartness facts as implications, and no disjunction left *)
assert (HAppSh : forall x, pp <= x < pp + PP_SIZE -> shadow_addr F <= x < shadow_addr F + 128 -> False)
  by (intros x H1 H2; exact (hw8_apart_l _ _ _ _ _ Hsapp H1 H2)).
assert (HAppF : forall x, pp <= x < pp + PP_SIZE -> F <= x < F + 1024 -> False)
  by (intros x H1 H2; exact (hw8_apart_l _ _ _ _ _ HpF H1 H2)).
assert (HFSh : forall x, F <= x < F + 1024 -> shadow_addr F <= x < shadow_addr F + 128 -> False)
  by (intros x H1 H2; exact (hw8_apart_l _ _ _ _ _ HsaF H1 H2)).
clear Hsapp HsaF.
(* The piece's end takes the segment's start, the cut J and the two continuations; specialise it here and drop
   those four texts, so that the arithmetic of the walk runs in a small context. *)
pose proof (fun ly' S' W' regs' mem' md' lastb =>
  FIN cx POST rest i k ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed ly' S' W' regs' mem' md' lastb
    HST Hi Hk HJcut HFC HFCL) as FIN'.
clear HST HJcut HFC HFCL JF FIN.
(* ------------------------------- A: J -> pod_write_ent's entry ------------------------------- *)
replace (bi_J headamp_bld_B) with HW8_J by reflexivity.
eapply SRr_bind.
{ apply (BLKA (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem2 md2 (x_k cx) regs2 R pp L); try assumption; lia. }
intros W' c' _ (-> & regsA & memA & mdA & -> & HJA & HioA & AK & AU & (A1 & A10 & A11 & A21 & A26)).
clear BLKA.
assert (UA : hw8_un (w_H W2) (w_H W2) mem2 memA (fun _ => False)) by exact AU.
assert (AR2 : getr regsA 2 = w64 R) by (rewrite (AK 2%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact R2).
assert (AR3 : getr regsA 3 = w64 (as_gp B)) by (rewrite (AK 3%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact R3).
assert (AR4 : getr regsA 4 = w64 (as_tp B)) by (rewrite (AK 4%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact R4).
assert (AR9 : getr regsA 9 = w64 R) by (rewrite (AK 9%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact R9).
assert (AR19 : getr regsA 19 = w64 (shadow_addr F))
  by (rewrite (AK 19%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact R19).
assert (AR20 : getr regsA 20 = w64 (F + 0x210)) by (rewrite (AK 20%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact R20).
assert (AR23 : getr regsA 23 = w64 pp) by (rewrite (AK 23%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact R23).
assert (AR27 : getr regsA 27 = w64 SHADOW_OFF)
  by (rewrite (AK 27%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact R27).
assert (A11' : getr regsA 11 = w64 (F + 0x210)) by (rewrite A11; exact R20).
assert (VLENA : val_mem rsegs (mrestrict (w_H W2) memA) (pp + OFF_LEN) 8 L).
{ eapply hw8_un_val; [exact UA | exact VLEN | lia | cbn [Z.of_nat]; lia | intros x Hx HC; exact HC]. }
assert (HEMA : hm_bytes rsegs (w_H W2) memA (F + 0x210) (ent_mem ed)).
{ eapply hw8_un_bytes; [exact UA | exact HEM | lia | rewrite Hlem; cbn [Z.of_nat]; lia
  | intros x Hx HC; exact HC]. }
assert (HFSHA : hd_fsh rsegs (w_H W2) memA F (hmu_sh false false false false false true false false)).
{ eapply hw8_un_fsh; [exact UA | exact HFSH | lia | rewrite hmu_sh_len; cbn [Z.of_nat]; lia
  | intros x Hx HC; exact HC]. }
(* ------------------------------- the call of pod_write_ent ------------------------------- *)
eapply SRr_bind.
{ apply (hw8_pwe_step B MT PWE (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) ly2 S2 W2 memA mdA (x_k cx) regsA R pp F L ed (x_pos cx)); try assumption; lia. }
intros W3 c3 _ (fx2 & ly3 & S3 & regsB & memB & mdB & -> & Hfx2 & HJB & HpB & HfrB & HpermB & HioB & HmoB & HkB &
  (HENC & HLENB & HSHB & HRAppB & HRAqB)).
cbn beta in Hfx2. subst fx2. rewrite A1.
clear PWE.
assert (HspA : spZ regsA = R) by (unfold spZ; rewrite AR2; apply unsigned_lit_small; lia).
assert (UB : hw8_un (w_H W2) (w_H W3) memA memB
  (fun a => (R - T_pwe_STK <= a < R) \/ pwe_E pp L ed a)).
{ intros a Ha Hn. apply HkB; [exact Ha | rewrite HspA; intros HC; apply Hn; left; exact HC
  | intros HC; apply Hn; right; exact HC]. }
assert (UAB : hw8_un (w_H W2) (w_H W3) mem2 memB
  (fun a => (R - T_pwe_STK <= a < R) \/ pwe_E pp L ed a)).
{ eapply hw8_un_weaken; [exact (hw8_un_trans _ _ _ _ _ _ _ _ UA UB) | intros a [[] | HQ]; exact HQ]. }
assert (Hpp3 : In (pp, PP_SIZE) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact HpermB | exact Hpp2]).
assert (Hfr3 : In (4, x_pos cx) (frames S3)) by (rewrite HfrB; exact Hfr2).
assert (HFa3 : frame_addr ly3 4 (x_pos cx) = F).
{ rewrite (hw8_fa_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJB).
  rewrite <- (hw8_fa_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2). exact HFa. }
assert (BR2 : getr regsB 2 = w64 R) by (rewrite (hw8_pres_bv _ _ HpB 2%bv ltac:(hw8_cs)); exact AR2).
assert (BR3 : getr regsB 3 = w64 (as_gp B)) by (rewrite (hw8_pres_bv _ _ HpB 3%bv ltac:(hw8_cs)); exact AR3).
assert (BR4 : getr regsB 4 = w64 (as_tp B)) by (rewrite (hw8_pres_bv _ _ HpB 4%bv ltac:(hw8_cs)); exact AR4).
assert (BR9 : getr regsB 9 = w64 R) by (rewrite (hw8_pres_bv _ _ HpB 9%bv ltac:(hw8_cs)); exact AR9).
assert (BR19 : getr regsB 19 = w64 (shadow_addr F))
  by (rewrite (hw8_pres_bv _ _ HpB 19%bv ltac:(hw8_cs)); exact AR19).
assert (BR20 : getr regsB 20 = w64 (F + 0x210))
  by (rewrite (hw8_pres_bv _ _ HpB 20%bv ltac:(hw8_cs)); exact AR20).
assert (BR23 : getr regsB 23 = w64 pp) by (rewrite (hw8_pres_bv _ _ HpB 23%bv ltac:(hw8_cs)); exact AR23).
assert (BR27 : getr regsB 27 = w64 SHADOW_OFF)
  by (rewrite (hw8_pres_bv _ _ HpB 27%bv ltac:(hw8_cs)); exact AR27).
(* the real-frame cells and the frame's shadow after the call *)
assert (HcellB : forall o v, 0 <= o -> o + 8 <= 0x198 ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (R + o) 8 v -> val_mem rsegs (mrestrict (w_H W3) memB) (R + o) 8 v).
{ intros o v Ho1 Ho2 HV. eapply hw8_un_val; [exact UAB | exact HV | lia | cbn [Z.of_nat]; lia |].
  intros x Hx [HS | HPE]; [lia | unfold pwe_E in HPE; destruct HPE as [HPE|HPE]; lia]. }
assert (HFSHB : hd_fsh rsegs (w_H W3) memB F (hmu_sh false false false false false true false false)).
{ eapply hw8_un_fsh; [exact UAB | exact HFSH | lia | rewrite hmu_sh_len; cbn [Z.of_nat]; lia |].
  intros j Hj. rewrite hmu_sh_len in Hj. cbn [Z.of_nat] in Hj.
  intros [HS | HPE]; [lia | unfold pwe_E in HPE; destruct HPE as [HPE|HPE];
    apply (HAppSh (shadow_addr F + j)); lia]. }
assert (HEMB : hm_bytes rsegs (w_H W3) memB (F + 0x210) (ent_mem ed)).
{ eapply hw8_un_bytes; [exact UAB | exact HEM | lia | rewrite Hlem; cbn [Z.of_nat]; lia |].
  intros x Hx. rewrite Hlem in Hx. cbn [Z.of_nat] in Hx.
  intros [HS | HPE]; [lia | unfold pwe_E in HPE; destruct HPE as [HPE|HPE]; apply (HAppF x); lia]. }
(* ------------------------------- the two arms of `first` ------------------------------- *)
destruct Hfs01 as [Hf0 | Hf1].
- (* ---------------- first = 0: no record copy ---------------- *)
  assert (Hfirst : pc_first (PbCut sh ps (Some es)) = false).
  { rewrite Hf0 in Hfs. destruct (pc_first (PbCut sh ps (Some es))); [discriminate | reflexivity]. }
  rewrite Hf0 in V140.
  eapply SRr_bind.
  { apply (BLKC0 (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
      ly3 S3 W3 memB mdB (x_k cx) regsB R (Z.of_nat (length es))).
    - exact HJB.
    - lia.
    - lia.
    - exact BR9.
    - apply HcellB; [lia | lia | exact V140].
    - apply HcellB; [lia | lia | exact V158].
    - exact Hkk. }
  intros W' c' _ (-> & regsC & memC & mdC & -> & HJC & HioC & CK & CU & (C10 & C11)).
  clear BLKC0 BLKC1 BLKC2 ACPY.
  assert (UC : hw8_un (w_H W3) (w_H W3) memB memC (fun _ => False)) by exact CU.
  assert (CR9 : getr regsC 9 = w64 R) by (rewrite (CK 9%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact BR9).
  assert (CR19 : getr regsC 19 = w64 (shadow_addr F))
    by (rewrite (CK 19%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact BR19).
  assert (UABC : hw8_un (w_H W2) (w_H W3) mem2 memC
    (fun a => (R - T_pwe_STK <= a < R) \/ pwe_E pp L ed a)).
  { eapply hw8_un_weaken; [exact (hw8_un_trans _ _ _ _ _ _ _ _ UAB UC) | intros a [HP | []]; exact HP]. }
  (* the scope-closing stores of e62 *)
  eapply SRr_bind.
  { apply (hdu_scope_e62_out B MT MTL LAWS (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx)
      (x_mem0 cx) (x_md0 cx) (x_own cx) ly3 S3 W3 memC mdC (x_k cx) regsC 4 (x_pos cx)).
    - exact HJC.
    - exact Hown4.
    - lia.
    - rewrite HFa3. exact CR19.
    - exact C10.
    - rewrite HFa3. exact Hsa0.
    - rewrite HFa3. lia.
    - vm_compute; discriminate. }
  intros W4 c4 _ (ly4 & S4 & regsD & memD & mdD & -> & HJD & DK & HfrD & HpermD & HioD & HmoD & DU & (DSH & DRx)).
  rewrite HFa3 in DU, DSH.
  destruct DRx as (Dinc & Ds7).
  assert (D11 : getr regsD 11 = w64 (Z.of_nat (length es) + 1)) by (apply Dinc; [exact C11 | lia]).
  assert (UD : hw8_un (w_H W3) (w_H W4) memC memD
    (fun a => shadow_addr F + 66 <= a < shadow_addr F + 79)) by exact DU.
  assert (DR9 : getr regsD 9 = w64 R) by (rewrite (DK 9%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact CR9).
  assert (UCD : hw8_un (w_H W2) (w_H W4) mem2 memD
    (fun a => ((R - T_pwe_STK <= a < R) \/ pwe_E pp L ed a) \/
              (shadow_addr F + 66 <= a < shadow_addr F + 79)))
    by exact (hw8_un_trans _ _ _ _ _ _ _ _ UABC UD).
  (* the loop's test *)
  eapply SRr_bind.
  { apply (BLKD (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
      ly4 S4 W4 memD mdD (x_k cx) regsD R (Z.of_nat (length es) + 1) cnt).
    - exact HJD.
    - lia.
    - lia.
    - exact DR9.
    - exact D11.
    - eapply hw8_un_val; [exact UCD | exact V128 | lia | cbn [Z.of_nat]; lia |].
      intros x Hx [[HS | HPE] | HSh]; [lia | unfold pwe_E in HPE; destruct HPE as [HPE|HPE]; lia | lia].
    - lia.
    - lia. }
  intros W' c' _ (-> & regsE & memE & mdE & -> & HJE & HioE & EK & EU & _).
  clear BLKD.
  assert (UE : hw8_un (w_H W4) (w_H W4) memD memE (fun _ => False)) by exact EU.
  assert (UF : hw8_un (w_H W2) (w_H W4) mem2 memE
    (fun a => ((R - T_pwe_STK <= a < R) \/ pwe_E pp L ed a) \/
              (shadow_addr F + 66 <= a < shadow_addr F + 79))).
  { eapply hw8_un_weaken; [exact (hw8_un_trans _ _ _ _ _ _ _ _ UCD UE) | intros a [HP | []]; exact HP]. }
  assert (UBE : hw8_un (w_H W3) (w_H W4) memB memE
    (fun a => shadow_addr F + 66 <= a < shadow_addr F + 79)).
  { eapply hw8_un_weaken;
    [exact (hw8_un_trans _ _ _ _ _ _ _ _ (hw8_un_trans _ _ _ _ _ _ _ _ UC UD) UE)
    | intros a [[[] | HSh] | []]; exact HSh]. }
  (* the end: the cut C or CL *)
  assert (Hlast : (Z.of_nat (length es) + 1 =? cnt) = (Z.of_nat (S k) =? cnt)).
  { f_equal. rewrite <- Hk. lia. }
  rewrite Hlast.
  apply (FIN' ly4 S4 W4 regsE memE mdE (Z.of_nat (S k) =? cnt) eq_refl HJE).
  + rewrite HfrD. exact HfrB.
  + eapply Permutation_trans; [exact HpermD | exact HpermB].
  + eapply same_io_trans; [exact HioA|]. eapply same_io_trans; [exact HioB|].
    eapply same_io_trans; [exact HioC|]. eapply same_io_trans; [exact HioD | exact HioE].
  + replace 0 with (0 + 0) by reflexivity. exact (mle_station MT _ _ _ 0 0 MTL HmoB HmoD).
  + intros r0 Hr0.
    assert (HC : bv_unsigned r0 <> 0 /\ ~ In r0 [10]%bv /\ ~ In r0 [11; 23]%bv /\ ~ In r0 [10; 11]%bv /\
                 acallee_saved (bv_unsigned r0) /\ ~ In r0 [1; 10; 11; 21; 26]%bv)
      by (cbv [hw8_keepF] in Hr0; cbn [In] in Hr0;
          repeat (destruct Hr0 as [<-|Hr0];
            [split; [hw8_nz|]; split; [hw8_notin|]; split; [hw8_notin|]; split; [hw8_notin|];
             split; [hw8_cs | hw8_notin] |]); destruct Hr0).
    destruct HC as (Hz & H1 & H2 & H3 & H4 & H5).
    rewrite (EK r0 Hz H1), (DK r0 Hz H2), (CK r0 Hz H3), (hw8_pres_bv _ _ HpB r0 H4), (AK r0 Hz H5). reflexivity.
  + rewrite (EK 21%bv ltac:(hw8_nz) ltac:(hw8_notin)), (DK 21%bv ltac:(hw8_nz) ltac:(hw8_notin)),
            (CK 21%bv ltac:(hw8_nz) ltac:(hw8_notin)), (hw8_pres_bv _ _ HpB 21%bv ltac:(hw8_cs)). exact A21.
  + rewrite (EK 26%bv ltac:(hw8_nz) ltac:(hw8_notin)), (DK 26%bv ltac:(hw8_nz) ltac:(hw8_notin)),
            (CK 26%bv ltac:(hw8_nz) ltac:(hw8_notin)), (hw8_pres_bv _ _ HpB 26%bv ltac:(hw8_cs)). exact A26.
  + rewrite (EK 11%bv ltac:(hw8_nz) ltac:(hw8_notin)).
    replace (Z.of_nat (S k)) with (Z.of_nat (length es) + 1) by (rewrite Hk; lia). exact D11.
  + rewrite (EK 23%bv ltac:(hw8_nz) ltac:(hw8_notin)). exact Ds7.
  + intros a Ha HnS HnP HnSh. apply UF; [exact Ha|]. intros [[HS | HPE] | HSh].
    * apply HnS. lia.
    * apply HnP. unfold pwe_E in HPE. destruct HPE as [HPE|HPE]; lia.
    * exact (HnSh HSh).
  + intros o Ho. etransitivity.
    * apply (UE (shadow_addr F + o)); [lia | intros HC; exact HC].
    * replace 248 with ((-8) mod 256) by reflexivity. apply DSH. lia.
  + eapply (wiu_final (w_H W2) (w_H W4) mem2 memE pp sh ps es ed HPV HPAE HES Hwf Hps2 Hes32 ltac:(lia)
      ltac:(lia) HIMG).
    * eapply hw8_un_bytes; [exact UBE | exact HENC | lia | lia |].
      intros x Hx HSh. apply (HAppSh x); lia.
    * assert (HLEN2 : val_mem rsegs (mrestrict (w_H W3) memB) (pp + OFF_LEN) 8
        (L + 8 + e_size ed + pad8 (e_size ed)))
        by (replace (L + 8 + e_size ed + pad8 (e_size ed)) with (L + pwe_len ed) by lia; exact HLENB).
      eapply hw8_un_val; [exact UBE | exact HLEN2 | lia | cbn [Z.of_nat]; lia |].
      intros x Hx HSh. apply (HAppSh x); lia.
    * intros Ht. rewrite Hfirst in Ht. discriminate.
    * intros a Ha Hn1 Hn2 _. apply UF; [lia|]. intros [[HS | HPE] | HSh].
      -- lia.
      -- unfold pwe_E in HPE. destruct HPE as [HPE | HPE]; [apply Hn1 | apply Hn2]; lia.
      -- apply (HAppSh a); lia.
- (* ---------------- first = 1: the record is copied into ent[n_ent] ---------------- *)
  assert (Hfirst : pc_first (PbCut sh ps (Some es)) = true).
  { rewrite Hf1 in Hfs. destruct (pc_first (PbCut sh ps (Some es))); [reflexivity | discriminate]. }
  rewrite Hf1 in V140.
  pose proof (HNE Hf1) as VNE.
  eapply SRr_bind.
  { apply (BLKC1 (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
      ly3 S3 W3 memB mdB (x_k cx) regsB R pp (Z.of_nat (length es))).
    - exact HJB.
    - exact Hpp3.
    - exact Hfresh.
    - lia.
    - lia.
    - exact BR9.
    - exact BR23.
    - exact BR27.
    - apply HcellB; [lia | lia | exact V140].
    - apply HcellB; [lia | lia | exact V158].
    - apply HcellB; [lia | lia | exact Ve0].
    - apply HcellB; [lia | lia | exact V120].
    - apply HcellB; [lia | lia | exact Vd8].
    - apply HcellB; [lia | lia | exact Vd0].
    - eapply hw8_un_val; [exact UAB | exact VNE | lia | cbn [Z.of_nat]; lia |].
      intros x Hx [HS | HPE]; [lia | unfold pwe_E in HPE; destruct HPE as [HPE|HPE]; lia].
    - exact Hkk. }
  intros W' c' _ (-> & regsC & memC & mdC & -> & HJC & HioC & CK & CU & (C1a & C10 & C11 & C12 & CNE)).
  clear BLKC0 BLKC1.
  assert (UC : hw8_un (w_H W3) (w_H W3) memB memC (fun a => pp + 0x4d14 <= a < pp + 0x4d18)) by exact CU.
  assert (CR2 : getr regsC 2 = w64 R) by (rewrite (CK 2%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact BR2).
  assert (CR3 : getr regsC 3 = w64 (as_gp B)) by (rewrite (CK 3%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact BR3).
  assert (CR4 : getr regsC 4 = w64 (as_tp B)) by (rewrite (CK 4%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact BR4).
  assert (CR9 : getr regsC 9 = w64 R) by (rewrite (CK 9%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact BR9).
  assert (CR19 : getr regsC 19 = w64 (shadow_addr F))
    by (rewrite (CK 19%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact BR19).
  assert (C11' : getr regsC 11 = w64 (F + 0x210)) by (rewrite C11; exact BR20).
  assert (HFSHC : hd_fsh rsegs (w_H W3) memC F (hmu_sh false false false false false true false false)).
  { eapply hw8_un_fsh; [exact UC | exact HFSHB | lia | rewrite hmu_sh_len; cbn [Z.of_nat]; lia |].
    intros j Hj. rewrite hmu_sh_len in Hj. cbn [Z.of_nat] in Hj.
    intros HPE. apply (HAppSh (shadow_addr F + j)); lia. }
  assert (HEMC : hm_bytes rsegs (w_H W3) memC (F + 0x210) (ent_mem ed)).
  { eapply hw8_un_bytes; [exact UC | exact HEMB | lia | rewrite Hlem; cbn [Z.of_nat]; lia |].
    intros x Hx. rewrite Hlem in Hx. cbn [Z.of_nat] in Hx. intros HPE. apply (HAppF x); lia. }
  (* ---- the record copy ---- *)
  eapply SRr_bind.
  { apply (hw8_cpy_step B ACPY (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
      (x_md0 cx) (x_own cx) ly3 S3 W3 memC mdC (x_k cx) regsC R pp F (Z.of_nat (length es)) (x_pos cx));
    try assumption; lia. }
  intros W' c' _ (-> & regsM & memM & mdM & -> & HJM & HioM & HpM & M10 & Mcpy & MU & Mpres).
  clear ACPY.
  assert (UM : hw8_un (w_H W3) (w_H W3) memC memM
    (fun a => (pp + 0x4014 + 104 * Z.of_nat (length es) <= a < pp + 0x4014 + 104 * Z.of_nat (length es) + 104) \/
              (R - ESTACK <= a < R))).
  { intros a Ha Hn. apply MU; [exact Ha | intros HC; apply Hn; left; exact HC
    | intros HC; apply Hn; right; exact HC]. }
  assert (MR9 : getr regsM 9 = w64 R) by (rewrite (hw8_pres_bv _ _ HpM 9%bv ltac:(hw8_cs)); exact CR9).
  assert (MR19 : getr regsM 19 = w64 (shadow_addr F))
    by (rewrite (hw8_pres_bv _ _ HpM 19%bv ltac:(hw8_cs)); exact CR19).
  (* ---- C2 ---- *)
  eapply SRr_bind.
  { apply (BLKC2 (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
      ly3 S3 W3 memM mdM (x_k cx) regsM R (Z.of_nat (length es))).
    - exact HJM.
    - lia.
    - lia.
    - exact MR9.
    - eapply hw8_un_val.
      + exact (hw8_un_trans _ _ _ _ _ _ _ _ UC UM).
      + apply HcellB; [lia | lia | exact V158].
      + lia.
      + cbn [Z.of_nat]; lia.
      + intros x Hx [HNE' | [HD | HS]]; lia.
    - exact Hkk. }
  intros W' c' _ (-> & regsN & memN & mdN & -> & HJN & HioN & NK & NU & (N10 & N11)).
  clear BLKC2.
  assert (UN : hw8_un (w_H W3) (w_H W3) memM memN (fun _ => False)) by exact NU.
  assert (NR9 : getr regsN 9 = w64 R) by (rewrite (NK 9%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact MR9).
  assert (NR19 : getr regsN 19 = w64 (shadow_addr F))
    by (rewrite (NK 19%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact MR19).
  (* ---- the scope-closing stores of e62 ---- *)
  eapply SRr_bind.
  { apply (hdu_scope_e62_out B MT MTL LAWS (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx)
      (x_mem0 cx) (x_md0 cx) (x_own cx) ly3 S3 W3 memN mdN (x_k cx) regsN 4 (x_pos cx)).
    - exact HJN.
    - exact Hown4.
    - lia.
    - rewrite HFa3. exact NR19.
    - exact N10.
    - rewrite HFa3. exact Hsa0.
    - rewrite HFa3. lia.
    - vm_compute. discriminate. }
  intros W4 c4 _ (ly4 & S4 & regsD & memD & mdD & -> & HJD & DK & HfrD & HpermD & HioD & HmoD & DU & (DSH & DRx)).
  rewrite HFa3 in DU, DSH.
  destruct DRx as (Dinc & Ds7).
  assert (D11 : getr regsD 11 = w64 (Z.of_nat (length es) + 1)) by (apply Dinc; [exact N11 | lia]).
  assert (UD : hw8_un (w_H W3) (w_H W4) memN memD
    (fun a => shadow_addr F + 66 <= a < shadow_addr F + 79)) by exact DU.
  assert (DR9 : getr regsD 9 = w64 R) by (rewrite (DK 9%bv ltac:(hw8_nz) ltac:(hw8_notin)); exact NR9).
  assert (UABCMN : hw8_un (w_H W2) (w_H W3) mem2 memN
    (fun a => (((R - T_pwe_STK <= a < R) \/ pwe_E pp L ed a) \/ (pp + 0x4d14 <= a < pp + 0x4d18)) \/
              ((pp + 0x4014 + 104 * Z.of_nat (length es) <= a <
                pp + 0x4014 + 104 * Z.of_nat (length es) + 104) \/ (R - ESTACK <= a < R)))).
  { eapply hw8_un_weaken;
    [exact (hw8_un_trans _ _ _ _ _ _ _ _
       (hw8_un_trans _ _ _ _ _ _ _ _ (hw8_un_trans _ _ _ _ _ _ _ _ UAB UC) UM) UN)
    | intros a [HP | []]; exact HP]. }
  assert (UCD : hw8_un (w_H W2) (w_H W4) mem2 memD
    (fun a => ((((R - T_pwe_STK <= a < R) \/ pwe_E pp L ed a) \/ (pp + 0x4d14 <= a < pp + 0x4d18)) \/
               ((pp + 0x4014 + 104 * Z.of_nat (length es) <= a <
                 pp + 0x4014 + 104 * Z.of_nat (length es) + 104) \/ (R - ESTACK <= a < R))) \/
              (shadow_addr F + 66 <= a < shadow_addr F + 79)))
    by exact (hw8_un_trans _ _ _ _ _ _ _ _ UABCMN UD).
  (* ---- the loop's test ---- *)
  eapply SRr_bind.
  { apply (BLKD (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
      ly4 S4 W4 memD mdD (x_k cx) regsD R (Z.of_nat (length es) + 1) cnt).
    - exact HJD.
    - lia.
    - lia.
    - exact DR9.
    - exact D11.
    - eapply hw8_un_val; [exact UCD | exact V128 | lia | cbn [Z.of_nat]; lia |].
      intros x Hx [[[[HS | HPE] | HNE'] | [HD | HS']] | HSh];
      [lia | unfold pwe_E in HPE; destruct HPE as [HPE|HPE]; lia | lia | lia | lia | lia].
    - lia.
    - lia. }
  intros W' c' _ (-> & regsE & memE & mdE & -> & HJE & HioE & EK & EU & _).
  clear BLKD.
  assert (UE : hw8_un (w_H W4) (w_H W4) memD memE (fun _ => False)) by exact EU.
  assert (UF : hw8_un (w_H W2) (w_H W4) mem2 memE
    (fun a => ((((R - T_pwe_STK <= a < R) \/ pwe_E pp L ed a) \/ (pp + 0x4d14 <= a < pp + 0x4d18)) \/
               ((pp + 0x4014 + 104 * Z.of_nat (length es) <= a <
                 pp + 0x4014 + 104 * Z.of_nat (length es) + 104) \/ (R - ESTACK <= a < R))) \/
              (shadow_addr F + 66 <= a < shadow_addr F + 79))).
  { eapply hw8_un_weaken; [exact (hw8_un_trans _ _ _ _ _ _ _ _ UCD UE) | intros a [HP | []]; exact HP]. }
  (* the record now lies in ent[n_ent] *)
  assert (HENT : hm_bytes rsegs (w_H W3) memM (pp + 0x4014 + 104 * Z.of_nat (length es)) (ent_mem ed)).
  { apply (hm_memcpy_bytes rsegs (w_H W3) memC (w_H W3) memM (F + 0x210)
      (pp + 0x4014 + 104 * Z.of_nat (length es)) (ent_mem ed) HEMC).
    intros i0 Hi0. rewrite Hlem in Hi0. cbn [Z.of_nat] in Hi0. exact (Mcpy i0 ltac:(lia)). }
  assert (UMD : hw8_un (w_H W3) (w_H W4) memM memE
    (fun a => shadow_addr F + 66 <= a < shadow_addr F + 79)).
  { eapply hw8_un_weaken;
    [exact (hw8_un_trans _ _ _ _ _ _ _ _ (hw8_un_trans _ _ _ _ _ _ _ _ UN UD) UE)
    | intros a [[[] | HSh] | []]; exact HSh]. }
  assert (UNE : hw8_un (w_H W3) (w_H W4) memC memE
    (fun a => ((pp + 0x4014 + 104 * Z.of_nat (length es) <= a <
                pp + 0x4014 + 104 * Z.of_nat (length es) + 104) \/ (R - ESTACK <= a < R)) \/
              (shadow_addr F + 66 <= a < shadow_addr F + 79))).
  { eapply hw8_un_weaken;
    [exact (hw8_un_trans _ _ _ _ _ _ _ _
       (hw8_un_trans _ _ _ _ _ _ _ _ (hw8_un_trans _ _ _ _ _ _ _ _ UM UN) UD) UE)
    | intros a [[[HP | []] | HSh] | []]; [left; exact HP | right; exact HSh]]. }
  assert (UBE : hw8_un (w_H W3) (w_H W4) memB memE
    (fun a => (pp + 0x4d14 <= a < pp + 0x4d18) \/
              (((pp + 0x4014 + 104 * Z.of_nat (length es) <= a <
                 pp + 0x4014 + 104 * Z.of_nat (length es) + 104) \/ (R - ESTACK <= a < R)) \/
               (shadow_addr F + 66 <= a < shadow_addr F + 79))))
    by exact (hw8_un_trans _ _ _ _ _ _ _ _ UC UNE).
  (* the end: the cut C or CL *)
  assert (Hlast : (Z.of_nat (length es) + 1 =? cnt) = (Z.of_nat (S k) =? cnt)).
  { f_equal. rewrite <- Hk. lia. }
  rewrite Hlast.
  apply (FIN' ly4 S4 W4 regsE memE mdE (Z.of_nat (S k) =? cnt) eq_refl HJE).
  + rewrite HfrD. exact HfrB.
  + eapply Permutation_trans; [exact HpermD | exact HpermB].
  + eapply same_io_trans; [exact HioA|]. eapply same_io_trans; [exact HioB|].
    eapply same_io_trans; [exact HioC|]. eapply same_io_trans; [exact HioM|].
    eapply same_io_trans; [exact HioN|]. eapply same_io_trans; [exact HioD | exact HioE].
  + replace 0 with (0 + 0) by reflexivity. exact (mle_station MT _ _ _ 0 0 MTL HmoB HmoD).
  + intros r0 Hr0.
    assert (HC : bv_unsigned r0 <> 0 /\ ~ In r0 [10]%bv /\ ~ In r0 [11; 23]%bv /\ ~ In r0 [10; 11]%bv /\
                 acallee_saved (bv_unsigned r0) /\ ~ In r0 [1; 10; 11; 12]%bv /\
                 ~ In r0 [1; 10; 11; 21; 26]%bv).
    { cbv [hw8_keepF] in Hr0; cbn [In] in Hr0;
      repeat (destruct Hr0 as [<-|Hr0];
        [split; [hw8_nz|]; split; [hw8_notin|]; split; [hw8_notin|]; split; [hw8_notin|];
         split; [hw8_cs|]; split; [hw8_notin | hw8_notin] |]); destruct Hr0. }
    destruct HC as (Hz & H1 & H2 & H3 & H4 & H5 & H6).
    rewrite (EK r0 Hz H1), (DK r0 Hz H2), (NK r0 Hz H3), (hw8_pres_bv _ _ HpM r0 H4),
            (CK r0 Hz H5), (hw8_pres_bv _ _ HpB r0 H4), (AK r0 Hz H6). reflexivity.
  + rewrite (EK 21%bv ltac:(hw8_nz) ltac:(hw8_notin)), (DK 21%bv ltac:(hw8_nz) ltac:(hw8_notin)),
            (NK 21%bv ltac:(hw8_nz) ltac:(hw8_notin)), (hw8_pres_bv _ _ HpM 21%bv ltac:(hw8_cs)),
            (CK 21%bv ltac:(hw8_nz) ltac:(hw8_notin)), (hw8_pres_bv _ _ HpB 21%bv ltac:(hw8_cs)). exact A21.
  + rewrite (EK 26%bv ltac:(hw8_nz) ltac:(hw8_notin)), (DK 26%bv ltac:(hw8_nz) ltac:(hw8_notin)),
            (NK 26%bv ltac:(hw8_nz) ltac:(hw8_notin)), (hw8_pres_bv _ _ HpM 26%bv ltac:(hw8_cs)),
            (CK 26%bv ltac:(hw8_nz) ltac:(hw8_notin)), (hw8_pres_bv _ _ HpB 26%bv ltac:(hw8_cs)). exact A26.
  + rewrite (EK 11%bv ltac:(hw8_nz) ltac:(hw8_notin)).
    replace (Z.of_nat (S k)) with (Z.of_nat (length es) + 1) by (rewrite Hk; lia). exact D11.
  + rewrite (EK 23%bv ltac:(hw8_nz) ltac:(hw8_notin)). exact Ds7.
  + intros a Ha HnS HnP HnSh. apply UF; [exact Ha|].
    intros [[[[HS | HPE] | HNE'] | [HD | HS']] | HSh].
    * apply HnS. lia.
    * apply HnP. unfold pwe_E in HPE. destruct HPE as [HPE|HPE]; lia.
    * apply HnP. lia.
    * apply HnP. lia.
    * apply HnS. lia.
    * exact (HnSh HSh).
  + intros o Ho. etransitivity.
    * apply (UE (shadow_addr F + o)); [lia | intros HC; exact HC].
    * replace 248 with ((-8) mod 256) by reflexivity. apply DSH. lia.
  + eapply (wiu_final (w_H W2) (w_H W4) mem2 memE pp sh ps es ed HPV HPAE HES Hwf Hps2 Hes32 ltac:(lia)
      ltac:(lia) HIMG).
    * eapply hw8_un_bytes; [exact UBE | exact HENC | lia | lia |].
      intros x Hx [HNE' | [[HD | HS'] | HSh]]; [lia | lia | lia | apply (HAppSh x); lia].
    * assert (HLEN2 : val_mem rsegs (mrestrict (w_H W3) memB) (pp + OFF_LEN) 8
        (L + 8 + e_size ed + pad8 (e_size ed)))
        by (replace (L + 8 + e_size ed + pad8 (e_size ed)) with (L + pwe_len ed) by lia; exact HLENB).
      eapply hw8_un_val; [exact UBE | exact HLEN2 | lia | cbn [Z.of_nat]; lia |].
      intros x Hx [HNE' | [[HD | HS'] | HSh]]; [lia | lia | lia | apply (HAppSh x); lia].
    * intros _. split.
      -- eapply hw8_un_val; [exact UNE | exact CNE | lia | cbn [Z.of_nat]; lia |].
         intros x Hx [[HD | HS] | HSh]; [lia | lia | apply (HAppSh x); lia].
      -- replace (OFF_ENT + ENT_SIZE * Z.of_nat (length es))
           with (0x4014 + 104 * Z.of_nat (length es)) by lia.
         replace (pp + (0x4014 + 104 * Z.of_nat (length es)))
           with (pp + 0x4014 + 104 * Z.of_nat (length es)) by lia.
         eapply hw8_un_bytes; [exact UMD | exact HENT | lia | rewrite Hlem; cbn [Z.of_nat]; lia |].
         intros x Hx. rewrite Hlem in Hx. cbn [Z.of_nat] in Hx.
         intros HSh. apply (HAppSh x); lia.
    * intros a Ha Hn1 Hn2 Hn3. destruct (Hn3 Hfirst) as [Hn4 Hn5].
      apply UF; [lia|]. intros [[[[HS | HPE] | HNE'] | [HD | HS']] | HSh].
      -- lia.
      -- unfold pwe_E in HPE. destruct HPE as [HPE | HPE]; [apply Hn1 | apply Hn2]; lia.
      -- apply Hn4. lia.
      -- apply Hn5. lia.
      -- lia.
      -- apply (HAppSh a); lia.
Qed.
End b.

Print Assumptions hsu_piece_W8_B.
