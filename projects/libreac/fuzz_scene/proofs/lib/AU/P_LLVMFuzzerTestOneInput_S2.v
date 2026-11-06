(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S2 of the ASan+UBSan walk of libreac/fuzz_scene's
   LLVMFuzzerTestOneInput (fuzz_scene.asan-ubsan, sha256
   e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f): cut C2 0x82d94 .. cut C3 0x82e50.
   rule 24: no function is proved here; this file proves the walk SEGMENT statement seg_S2_stmt
   (lib/AU/P_LLVMFuzzerTestOneInput_seg.v) under the callee contracts named at its Section hypotheses. *)

(*   The block, in this build's own registers (the asan twin keeps body in a7 / [s1+0x58] and step in [s1+0x50]):
     0x82d94-0x82dc8  blk's unpoison (shadow cells 0x12-0x16 of F's shadow), s2 = (n' <> 8904), s5 = body,
                      memset's arguments; __asan_memset(blk, 0xa5, 34) 0x82dcc through aj_intrin_at;
     0x82dd0-0x82ddc  four register moves (s5 = body and s7 = step are callee-saved, so nothing is spilled);
                      reac_ctrl_build_scene_step(blk, body, n', step) 0x82de0 through a Theorem Labs lane's journal-form BSS;
     0x82de4-0x82e0c  a1 = -(s2 | sx16(s4) < 0 | ~(sx16(s7) < 343)); `bne a0,a1` to 0x83238
                      (__asan_handle_no_return; abort) is REFUTED: a0 is BSS's -1/0 and s2u_rcheck /
                      s2u_ok_iff show a1 is exactly that value;
     0x82e10-0x82e14  s4 = body; `beqz a0` splits the arms;
     accepting arm    0x82e40-0x82e4c: check_step(blk, body, step) through cl_callS and a Theorem Labs lane's TCHECKX; it returns
                      to C3 itself;
     refusing arm     0x82e18-0x82e34: the 34-turn loop over blk, run by the executor over blk's 34 literal 0xa5
                      chunks (the refusing call kept blk); a0 stays 0, so `beqz a0` 0x82e38 jumps to C3 and the
                      abort `j` 0x82e3c to 0x83238 is not reached.
   No __asan_report_* branch lies on this segment.  Both arms establish cut_C3 through the one lemma TOC3. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import YC1g YC4b YC45 YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock SceneTM.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_seg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_reac_ctrl_build_scene_step.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_frame P_check_step_cut P_check_step.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* gate 6h: the sink head is a named Section Context and every statement below takes it by name *)
Context (SK : YI16.sink_head).
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
(* ---- small image-free helpers (shadow arithmetic, a shadow cell read out of a symbolic region, what a run
   keeps); the same four that lib/AU/P_check_step_S3.v uses, under this lane's names ---- *)
Lemma s2u_div8_add : forall x c, x mod 8 = 0 -> (x + 8 * c) / 8 = x / 8 + c.
Proof.
intros x c Hx. rewrite (Z.div_mod x 8) at 1 by lia. rewrite Hx, Z.add_0_r.
replace (8 * (x / 8) + 8 * c) with ((x / 8 + c) * 8) by lia. apply Z.div_mul. lia.
Qed.
Lemma s2u_ra_part : forall (rd : reader) a q r, a mod 8 = 0 -> 0 <= q -> 0 < r < 8 ->
(forall i, 0 <= i < q -> rd (SHADOW_OFF + a / 8 + i) = Some 0) -> rd (SHADOW_OFF + a / 8 + q) = Some r ->
range_addressable rd SHADOW_OFF a (8 * q + r).
Proof.
intros rd a q r Ha Hq Hr H0 Hl x Hx. unfold shadow_of_addr.
assert (Ex : x / 8 = a / 8 + (x - a) / 8).
{ replace x with (a + (x - a)) at 1 by lia. rewrite (Z.div_mod a 8) at 1 by lia. rewrite Ha, Z.add_0_r.
  replace (8 * (a / 8) + (x - a)) with ((x - a) + (a / 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (Hd : 0 <= (x - a) / 8 < q + 1) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite Ex, Z.add_assoc.
destruct (Z.eq_dec ((x - a) / 8) q) as [Eq|Nq].
- rewrite Eq. exists r. split; [exact Hl|]. right.
  assert (Hm : x mod 8 = (x - a) mod 8).
  { rewrite (Z.div_mod a 8) at 1 by lia. rewrite Ha, Z.add_0_r.
    replace (x - 8 * (a / 8)) with (x + (- (a / 8)) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  pose proof (Z.div_mod (x - a) 8 ltac:(lia)) as Hdm. rewrite Eq in Hdm. lia.
- exists 0. split; [apply H0; lia | left; reflexivity].
Qed.
Lemma s2u_shb : forall E (H : word -> bool) mem n b cs lo hi wlo whi od v,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 (SLit v))) cs -> 0 <= v < 256 ->
aview SEGS H mem (b + od) = Some v.
Proof.
intros E H mem n b cs lo hi wlo whi od v HR Hn Hc Hv.
apply aview_of_val_mem1; [|exact Hv].
exact (field_of_region E _ n b cs lo hi wlo whi od 1 (SLit v) v HR Hn Hc eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma s2u_kept_run : forall E rs (H : word -> bool) (mA mB : word -> option byte) a,
frame_of E rs (mrestrict H mA) (mrestrict H mB) -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview SEGS H mB a = aview SEGS H mA a.
Proof. intros E rs H mA mB a HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn. Qed.

Lemma s2u_sh_off : forall x k c i, x mod 8 = 0 -> k = 8 * c ->
shadow_of_addr SHADOW_OFF (x + k) + i = SHADOW_OFF + x / 8 + (c + i).
Proof. intros x k c i Hx ->. unfold shadow_of_addr. rewrite s2u_div8_add by exact Hx. lia. Qed.
Lemma s2u_zc : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. exact Hz. Qed.
(* ---- the arithmetic of the result check 0x82de4-0x82e08: a1 = -(s2 | sx16(s4) < 0 | ~(sx16(s7) < 343)),
   with s2 = (n' <> 8904) from 0x82db0-0x82db4, s4 = sx16(256 * b4) and s7 = step = sx16(b3 + 256 * b4) ---- *)
Lemma s2u_swrap_small : forall v, - 2 ^ 63 <= v < 2 ^ 63 -> bv_swrap 64 (v mod 2 ^ 64) = v.
Proof.
intros v Hv. change (v mod 2 ^ 64) with (bv_wrap 64 v). rewrite bv_swrap_wrap.
apply swrap64_id. unfold half64. lia.
Qed.
Lemma s2u_sx_shift : forall v, -32768 <= v < 32768 ->
zcanon (zalu_raw 63 64 ALU_SRA (zcanon (zalu_raw 63 64 ALU_SLL (v mod 2 ^ 64) (zcanon 48))) (zcanon 48))
= v mod 2 ^ 64.
Proof.
intros v Hv. cbn [zalu_raw]. change (zcanon 48) with 48. change (Z.land 48 63) with 48.
rewrite Z.shiftl_mul_pow2 by lia.
assert (E1 : zcanon (v mod 2 ^ 64 * 2 ^ 48) = (v * 2 ^ 48) mod 2 ^ 64).
{ unfold zcanon, M64. rewrite Z.mul_mod_idemp_l by lia. reflexivity. }
rewrite E1, s2u_swrap_small by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma s2u_slt : forall v k, - 2 ^ 63 <= v < 2 ^ 63 -> 0 <= k < 2 ^ 63 ->
zalu_raw 63 64 ALU_SLT (v mod 2 ^ 64) (zcanon k) = if v <? k then 1 else 0.
Proof.
intros v k Hv Hk. cbn [zalu_raw]. rewrite s2u_swrap_small by lia. rewrite (s2u_zc k) by lia.
rewrite swrap64_id by (unfold half64; lia). reflexivity.
Qed.
Lemma s2u_rcheck : forall E b3 b4 npv,
0 <= b3 < 256 -> 0 <= b4 < 256 ->
U E (SOff 18 0) = (if npv =? 8904 then 0 else 1) ->
U E (SOff 20 0) = sx16 (256 * b4) mod 2 ^ 64 ->
U E (SOff 23 0) = sx16 (b3 + 256 * b4) mod 2 ^ 64 ->
U E (SAlu ALU_SUB (SLit 0)
  (SAlu ALU_OR
    (SAlu ALU_OR (SOff 18 0) (SAlu ALU_SLT (SAlu ALU_SRA (SAlu ALU_SLL (SOff 20 0) (SLit 48)) (SLit 48)) (SLit 0)))
    (SAlu ALU_XOR (SAlu ALU_SLT (SAlu ALU_SRA (SAlu ALU_SLL (SOff 23 0) (SLit 48)) (SLit 48)) (SLit 343)) (SLit 1))))
= if (npv =? 8904) && (0 <=? sx16 (b3 + 256 * b4)) && (sx16 (b3 + 256 * b4) <=? 342) then 0 else 2 ^ 64 - 1.
Proof.
intros E b3 b4 npv H3 H4 E18 E20 E23.
assert (R4 : -32768 <= sx16 (256 * b4) < 32768) by (unfold sx16; destruct (Z.ltb_spec (256 * b4) 32768); lia).
assert (R3 : -32768 <= sx16 (b3 + 256 * b4) < 32768) by (unfold sx16; destruct (Z.ltb_spec (b3 + 256 * b4) 32768); lia).
assert (Q1 : (sx16 (256 * b4) <? 0) = negb (0 <=? sx16 (b3 + 256 * b4))).
{ unfold sx16. destruct (Z.ltb_spec (256 * b4) 32768); destruct (Z.ltb_spec (b3 + 256 * b4) 32768);
  match goal with |- (?x <? 0) = negb (0 <=? ?y) => destruct (Z.ltb_spec x 0); destruct (Z.leb_spec 0 y) end;
  first [reflexivity | exfalso; lia]. }
assert (Q2 : (sx16 (b3 + 256 * b4) <? 343) = (sx16 (b3 + 256 * b4) <=? 342)).
{ destruct (Z.ltb_spec (sx16 (b3 + 256 * b4)) 343); destruct (Z.leb_spec (sx16 (b3 + 256 * b4)) 342);
  first [reflexivity | exfalso; lia]. }
rewrite !U_SAlu, !U_SLit, E18, E20, E23.
rewrite !s2u_sx_shift by lia.
rewrite !s2u_slt by lia.
rewrite Q1, Q2.
destruct (npv =? 8904), (0 <=? sx16 (b3 + 256 * b4)), (sx16 (b3 + 256 * b4) <=? 342); vm_compute; reflexivity.
Qed.
Lemma s2u_neq_flag : forall npv, 0 <= npv <= 65535 ->
bv_unsigned (alu64 ALU_SLTU (Z_to_bv 64 0) (alu64 ALU_XOR (Z_to_bv 64 npv) (Z_to_bv 64 8904)))
= if npv =? 8904 then 0 else 1.
Proof.
intros npv Hn. rewrite !zalu64_sound, unsigned_lit. unfold zalu64. cbn [zalu_raw].
rewrite ?(s2u_zc npv) by lia. rewrite ?(s2u_zc 8904) by lia. rewrite ?(s2u_zc 0) by lia.
assert (X0 : 0 <= Z.lxor npv 8904) by (apply Z.lxor_nonneg; lia).
assert (X1 : Z.lxor npv 8904 < 2 ^ 16).
{ destruct (Z.eq_dec (Z.lxor npv 8904) 0) as [->|Hne]; [lia|].
  apply Z.log2_lt_pow2; [lia|].
  pose proof (Z.log2_lxor npv 8904 ltac:(lia) ltac:(lia)) as HL.
  assert (Z.log2 npv < 16).
  { destruct (Z.eq_dec npv 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  assert (Z.log2 8904 < 16) by (vm_compute; reflexivity). lia. }
rewrite ?(s2u_zc (Z.lxor npv 8904)) by lia. rewrite ?(s2u_zc 0) by lia.
destruct (Z.eqb_spec npv 8904) as [->|Hne].
- vm_compute. reflexivity.
- assert (Hx : Z.lxor npv 8904 <> 0) by (intros Hx; apply Hne; apply Z.lxor_eq_0_iff; exact Hx).
  destruct (Z.ltb_spec 0 (Z.lxor npv 8904)); [|lia]. vm_compute. reflexivity.
Qed.

(* build_scene_step's own acceptance test, at blk <> 0, body <> 0 and a sign-extended 16-bit step *)
Lemma s2u_ok_iff : forall blk body npv st, blk <> 0 -> body <> 0 -> -32768 <= st < 32768 ->
scene_step_okZ blk body npv (st mod 2 ^ 64) = (npv =? 8904) && (0 <=? st) && (st <=? 342).
Proof.
intros blk body npv st Hb Hd Hst. unfold scene_step_okZ, SCENE_BYTES, SCENE_LAST.
replace (blk =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb).
replace (body =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hd).
cbn [negb andb].
destruct (Z.leb_spec 0 st) as [H0|H0].
- rewrite Z.mod_small by lia. destruct (npv =? 8904); reflexivity.
- replace (st mod 2 ^ 64 <=? 342) with false; [destruct (npv =? 8904); reflexivity|].
  symmetry. apply Z.leb_gt. rewrite <- (Z_mod_plus_full st 1). rewrite Z.mod_small by lia. lia.
Qed.
(* blk after the refusing call: the 34 bytes the memset 0x82dcc wrote, as literal chunks of a read-only region *)
Definition s2u_blk_chunks : list YP09.chunk := map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit 165))) (seq 0 34).
(* the caller chain at a call of the walk, from the saved ra and s0 of `sc_saves`: a Theorem Labs lane's s5_chain
   (at 61818d377d8, lib/A/P_LLVMFuzzerTestOneInput_S5_kit.v; cgif A/ACf5.v:172-186
   rt_chain), image-free, under this lane's name *)
Lemma s2u_chain : forall ly (rd rd' : reader) (regs : bvmap 5 word) sp',
achain ly rd (spZ regs) (s0Z regs) [] -> ly_top ly <= 2 ^ 64 ->
(forall a, spZ regs <= a < 2 ^ 64 -> rd' a = rd a) ->
rdword rd' (spZ regs - 8) = Some (raZ regs) -> rdword rd' (spZ regs - 16) = Some (s0Z regs) -> 4096 <= raZ regs ->
alloc_ceiling <= spZ regs -> spZ regs mod 8 = 0 -> sp' + 16 <= spZ regs ->
achain ly rd' sp' (spZ regs) (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []).
Proof.
intros ly rd rd' regs sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal Hsp'.
destruct (Z.ltb_spec (spZ regs + 16) (ly_top ly)) as [Hlt | Hge].
- replace (spZ regs - 8) with (spZ regs + -8) in H8 by lia. replace (spZ regs - 16) with (spZ regs + -16) in H16 by lia.
  apply (achain_push ly rd rd' (spZ regs) (s0Z regs) (raZ regs) [] sp' Hch Htop64 Hk);
  [replace (spZ regs - 8) with (spZ regs + -8) by lia; exact H8 | replace (spZ regs - 16) with (spZ regs + -16) by lia; exact H16
  | exact Hra | exact Hceil | exact Hal | lia | exact Hsp'].
- left. split; [right; left; lia | reflexivity].
Qed.

Section h.
Variable B : asyms.
(* A Theorem Labs lane (the walk's own Context RO, lib/AU/P_LLVMFuzzerTestOneInput.v:189): the read-only window is below the
   sink's overflow head; with arodata_okS of the entry it keeps the image bytes at every later state. *)
Context (RO : ro_below_ofl (SK := SK) SEGS pa_relro_lo pa_relro_hi).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
(* A Theorem Labs lane *)
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset).
(* A Theorem Labs lane *)
Hypothesis BSS : treac_ctrl_build_scene_step_spec (SK := SK) (PI := PI_scene) B.
(* A Theorem Labs lane *)
Hypothesis TCHECKX : tcheck_step_specX SK (PI := PI_scene) B.
(* Two Theorem Labs lanes (B's static tables) with a third (the start-up certificate): the walk statement's
   static shadow of reac_ctrl_build_scene_step.TAIL_TRAILER, lib/AU/P_LLVMFuzzerTestOneInput.v HB_Z_TT / HB_C_TT, in
   its text with the walk file's two plain literal Definitions A_TAIL_TRAILER = 0x20e20 and TAIL_TRAILER_N = 12
   written in place and TT_SHCELLS unfolded, so the walk's hypotheses are these up to delta (the walk file is not
   Required here: in the scratch build, Requiring it made the short name YI16 resolve to another module); and its
   minimal image-byte premise HRO_TT, verbatim.  A Theorem Labs lane's accepting-call premises on the trailer are derived from
   these below (s2u_tt). *)
Hypothesis HB_Z_TT : in_zs B (0x20e20 - 0x20) (0x20 + (12 - 12 mod 8)).
Hypothesis HB_C_TT : forall ly, Forall (fun c => In c (as_const B ly))
  (z1 (ANum (shadow_addr (0x20e20 + 8))) (12 mod 8)
   :: map (fun k => z1 (ANum (shadow_addr (0x20e20 + 8) + 1 + Z.of_nat k)) 0xf9) (seq 0 2)).
Hypothesis HRO_TT : forall i, 0 <= i < 12 ->
  ~ Exists (in_zr (0x20e20 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x20e20 + i < as_errno B + 4).
(* ---- the trailer's bytes, addressability and shadow hull at any AR state that keeps the image bytes ---- *)
Lemma s2u_const1 : forall ly S (W : world SEGS) mem md a v, AR SEGS B ly S W mem md ->
In (z1 (ANum a) v) (as_const B ly) -> aview SEGS (w_H W) mem a = Some (le_byte v 1 0).
Proof.
intros ly S W mem md a v HAR Hin.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ Hin) as X.
unfold cell_holds in X. cbn [c_at YG0f.c_val c_w aeval z1 c1] in X. specialize (X 0%nat ltac:(lia)). rewrite Z.add_0_r in X. exact X.
Qed.
Lemma s2u_zs_byte : forall ly S (W : world SEGS) mem md a n x, AR SEGS B ly S W mem md ->
in_zs B a n -> a <= x < a + n -> aview SEGS (w_H W) mem (SHADOW_OFF + x / 8) = Some 0.
Proof.
intros ly S W mem md a n x HAR (q & m & Hin & H1 & H2) Hx.
destruct (zs_range SEGS B q m Hin ly S W mem md HAR) as (Hq0 & Hm0 & Hq8 & Hm8 & Hhi).
pose proof (zs_zero SEGS B LAWS q m Hin ly S W mem md HAR) as Hz.
assert (Ex : x / 8 = q / 8 + (x - q) / 8).
{ replace x with ((x - q) + (q / 8) * 8) at 1 by (pose proof (Z.div_mod q 8 ltac:(lia)); lia). rewrite Z.div_add by lia. lia. }
unfold zero_shadow, shadow_of_addr in Hz.
rewrite Ex, Z.add_assoc. apply Hz. split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod m 8 ltac:(lia)). lia.
Qed.
Lemma s2u_in_ro : forall a, existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a)
  && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) SEGS = true -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Proof.
intros a H. apply existsb_exists in H as (s & Hs & Hb). left. exists s. split; [exact Hs|].
apply andb_prop in Hb as (Hb & H3). apply andb_prop in Hb as (H1 & H2).
apply Bool.negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. auto.
Qed.
Lemma s2u_tt : forall ly S (W' : world SEGS) (m : word -> option byte) md, AR SEGS B ly S W' m md ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m) ->
  (forall i, 0 <= i < 12 ->
     aview SEGS (w_H W') m (A_TT + i) = Some (bv_unsigned (nth (Z.to_nat i) scene_trailer (Z_to_bv 8 0)))) /\
  range_addressable (aview SEGS (w_H W') m) SHADOW_OFF A_TT 12 /\
  shadow_hull_vis (aview SEGS (w_H W') m) A_TT 12.
Proof.
intros ly S W' m md HAR HRD.
assert (EA : A_TT = 0x20e20) by (vm_compute; reflexivity). rewrite EA.
pose proof (HB_C_TT ly) as HC. cbn [map seq] in HC.
pose proof (Forall_inv HC) as C0. pose proof (Forall_inv (Forall_inv_tail HC)) as C1.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as C2. cbv beta in C0, C1, C2.
change (shadow_addr (0x20e20 + 8)) with 2147467717 in C0, C1, C2.
change (12 mod 8) with 4 in C0. change (2147467717 + 1 + Z.of_nat 0) with 2147467718 in C1.
change (2147467717 + 1 + Z.of_nat 1) with 2147467719 in C2.
pose proof HB_Z_TT as HZ. change (0x20e20 - 0x20) with 0x20e00 in HZ.
change (0x20 + (12 - 12 mod 8)) with 40 in HZ.
split; [|split].
- intros i Hi. destruct (HRO_TT i Hi) as (Ho & He).
  assert (Hro : in_roP SEGS pa_relro_lo pa_relro_hi (0x20e20 + i)).
  { apply s2u_in_ro.
    assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11) by lia.
    destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
    vm_compute; reflexivity. }
  rewrite (HRD _ Hro Ho He).
  assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
  vm_compute; reflexivity.
- change 12 with (8 * 1 + 4). apply s2u_ra_part; [reflexivity | lia | lia | |].
  + intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r.
    exact (s2u_zs_byte ly S W' m md 0x20e00 40 0x20e20 HAR HZ ltac:(lia)).
  + change (SHADOW_OFF + 0x20e20 / 8 + 1) with 2147467717. rewrite (s2u_const1 ly S W' m md _ _ HAR C0). reflexivity.
- intros s Hs. change (shadow_addr 0x20e20 / 8 * 8) with 2147467712 in Hs.
  change (shadow_addr (0x20e20 + 12 - 1) / 8 * 8 + 8) with 2147467720 in Hs.
  assert (Hc : 2147467712 <= s < 2147467717 \/ s = 2147467717 \/ s = 2147467718 \/ s = 2147467719) by lia.
  destruct Hc as [Hc | [-> | [-> | ->]]].
  + replace s with (SHADOW_OFF + (0x20e00 + 8 * (s - 2147467712)) / 8).
    * rewrite (s2u_zs_byte ly S W' m md 0x20e00 40 _ HAR HZ); [discriminate | lia].
    * rewrite s2u_div8_add by reflexivity. unfold SHADOW_OFF. change (0x20e00 / 8) with 16832. lia.
  + rewrite (s2u_const1 ly S W' m md _ _ HAR C0). discriminate.
  + rewrite (s2u_const1 ly S W' m md _ _ HAR C1). discriminate.
  + rewrite (s2u_const1 ly S W' m md _ _ HAR C2). discriminate.
Qed.
Variable WK : swalk.
(* the walk kit's read-only window is the listing's (one text across all lanes; the composition discharges both
   by eq_refl) *)
Hypothesis HWRLO : sw_rlo WK = pa_relro_lo.
Hypothesis HWRHI : sw_rhi WK = pa_relro_hi.
(* the composition (walk HSTK: LLVMF_SPDROP + ASTACK <= LLVMF_STK, with sw_stk WK = LLVMF_STK): the deepest callee
   window below the realigned sp; it covers memset's ESTACK, build_scene_step's 4144 and check_step's 8496 *)
Hypothesis HSTK : 240 + ASTACK <= sw_stk WK.
(* the composition (walk HEV, LLVMF_EV = 6 <= EV_LIB): the walk's event budget leaves room for the one allocator
   event (M1) the journal has counted at C2, so check_step's `st_nev S + 0 <= EV_MAX` holds at its call *)
Hypothesis HWKev : 1 <= sw_ev WK.

Let RUNP := SRr_run_pi_AJ (SK := SK) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (SK := SK) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (SK := SK) B LAWS.
Let BR := paj_branch (PI := PI_scene).

(* reduce one `vat` clause of a cut to the register or spill-slot equation it stands for *)
Local Ltac vred H :=
  cbn [sg2_sp0 sg2_sp1 sg2_F sg2_Fsp sg2_shF sg2_shbase sg2_blki sg2_blk sg2_expect sg2_mac sg2_shexp
       sg2_body sg2_nprime sg2_Fb sg2_nn sg2_flags sg2_step sg2_s7v
       sg3_sp0 sg3_sp1 sg3_F sg3_Fb sg3_Fsp sg3_shF sg3_blki sg3_expect sg3_mac sg3_shexp
       sg3_body sg3_nn sg3_nprime sg3_flags sg3_step
       sg_cid sg_off_blk sg_off_blki sg_off_mac sg_off_expect scene_geom_asan_ubsan] in H;
  cbv [vat RV_s0 RV_s1 RV_s2 RV_s3 RV_s4 RV_s5 RV_s6 RV_s7 RV_s8 RV_s9 RV_s10 RV_s11 RV_a1 RV_a6 RV_t2] in H.

Theorem seg_S2 : seg_S2_stmt (SK := SK) SEGS B ameter_triv WK scene_geom_asan_ubsan.
Proof.
unfold seg_S2_stmt. intros cx POST HBASE HC3 ly3 S3 W3 regs3 mem3 md3 bs body bb HCUT.
destruct HBASE as (HBASE0 & HSP1).
destruct HBASE0 as (HAFN & Hra & Ha0 & Ha1 & Hpn & Hfr0 & Hev0 & Hlive0 & HROD0 & HSINK & HFD & HFS & HMO).
destruct HCUT as (HJc & HAB & HBB & HBLK & HLBB & HGBB & HFRM & HSAV & HSHBG & HSHI & HSHB & HMACO
  & HIMG & HIN & HNN & HMAC
  & V_sp0 & V_sp1 & V_F & V_Fsp & V_shF & V_shbase & V_blki & V_blk & V_expect & V_mac & V_shexp
  & V_body & V_np & V_Fb & V_nn & V_flags & V_step & V_s7v).
remember (sc_nprime scene_geom_asan_ubsan bs) as npv eqn:Enpv.
remember (sc_nn scene_geom_asan_ubsan bs) as nnv eqn:Ennv.
assert (Ennv2 : nnv = if npv =? 0 then 1 else npv) by (rewrite Ennv, Enpv; reflexivity).
(* ---- names and the facts every block of this segment uses ---- *)
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
assert (EFe : sc_F SEGS scene_geom_asan_ubsan cx = frame_addr (c_ly cx) 8 (c_fpos cx)) by reflexivity.
set (sp0 := spZ (c_regs cx)) in *.
set (sp1 := c_sp1 cx) in *.
set (fpos := c_fpos cx) in *.
set (F := sc_F SEGS scene_geom_asan_ubsan cx) in *.
destruct HJc as (HJ & HFRS3 & HMOLE).
destruct HIMG as (HSP3 & HGP3 & HTP3 & HROD3).
destruct HAFN as (HAR0 & HraA & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT0).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR3 & Hly3 & Hsecs3 & Hwle3 & Hio3 & Hfrs3 & Hnev3 & Hk3 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17).
assert (Hfin3 : In (8, fpos) (frames S3)) by (rewrite HFRS3; left; reflexivity).
assert (EFly : frame_addr ly3 8 fpos = F).
{ destruct Hly3 as (_ & _ & _ & _ & _ & EFa & _). rewrite EFe. unfold frame_addr. rewrite EFa. reflexivity. }
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 fpos HAR3 Hfin3) as (HF32 & _ & HFpres & HFSpres).
rewrite EFly in HF4096, HFceil, HFapp, HF32, HFpres, HFSpres.
change (fs_frame_bytes 8) with 16384 in HF4096, HFceil, HFapp, HFpres, HFSpres.
change (16384 / 8) with 2048 in HFSpres.
unfold shadow_addr in HFSpres.
assert (HF8 : F mod 8 = 0) by (pose proof (Z.div_mod F 32 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
set (sF := SHADOW_OFF + F / 8) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
pose proof alloc_ceiling_val as HACV0.
assert (HsFlo : 2147450880 + 512 <= sF) by (subst sF; unfold SHADOW_OFF;
  pose proof (Z.div_le_lower_bound F 8 512 ltac:(lia) ltac:(lia)); lia).
assert (HsFhi : sF + 2048 <= 17594333495296) by (subst sF; unfold SHADOW_OFF;
  pose proof (Z.mul_div_le F 8 ltac:(lia)); lia).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
assert (ECS : TCHECK_STEP_STK = 8496) by (vm_compute; reflexivity).
assert (EBW : SCENE_STEP_WIN = 4144) by (vm_compute; reflexivity).
assert (Ho1 : sp0 - 255 <= sp1 <= sp0 - 224 /\ sp1 mod 32 = 0).
{ rewrite HSP1. pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)) as Hm.
  split; [lia|]. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
destruct Ho1 as (Hob & Ho32).
assert (Ho16 : (sp1 - sp0) mod 16 = 0).
{ apply Z.mod_divide in Ho32; [|lia]. apply Z.mod_divide in Hal16; [|lia].
  destruct Ho32 as [q1 Hq1]. destruct Hal16 as [q2 Hq2].
  apply Z.mod_divide; [lia|]. exists (2 * q1 - q2). lia. }
assert (HWin : alloc_ceiling + 16624 <= sp0) by lia.
(* ---- the cut's values, with the table's projections reduced ---- *)
vred V_sp0. vred V_sp1. vred V_F. vred V_Fsp. vred V_shF. vred V_shbase. vred V_blki. vred V_blk.
vred V_expect. vred V_mac. vred V_shexp. vred V_body. vred V_np. vred V_Fb. vred V_nn.
vred V_flags. vred V_step. vred V_s7v.
cbn [sg_sh_blki_lo sg_sh_blki_hi sg_sh_blk_lo sg_sh_blk_hi sg_off_blk sg_off_mac sg_off_blki sg_off_expect
  sg_blk_n sg_mac_n sg_scene_n sg_cid scene_geom_asan_ubsan] in HSHI, HSHB, HMACO, HAB, HBB, HBLK, HLBB, HNN.
unfold sc_shr in HSHI, HSHB.
unfold sc_frame in HFRM. cbn [sg_cid scene_geom_asan_ubsan] in HFRM.
change (fs_frame_bytes 8) with 16384 in HFRM.
destruct HFRM as (HFLAG & HFRMp & HFRMs).
(* ---- entry block 0x82d94 .. jal __asan_memset 0x82dcc: blk's unpoison (shadow cells 0x12 .. 0x16), the
   n' <> 8904 flag into s2, body into s5, and memset's three arguments ---- *)
unfold cfg_at. cbn [sg_pc_c2 scene_geom_asan_ubsan].
replace (w64 (BASE + AF_LLVMFuzzerTestOneInput + SEG_C2_off))
  with (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + SEG_C2_off))) by (unfold w64; f_equal; lia).
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regs3 []) E) by
  (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r) by
  (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U19 : bv_unsigned (ew E 19) = sF).
{ rewrite (EE 19%nat 19%bv eq_refl), V_shF. unfold shadow_addr, w64. apply unsigned_lit_small. unfold sF in *. lia. }
assert (HS : st_ok_pi SEGS VAL E
  (mkSS (AF_LLVMFuzzerTestOneInput + SEG_C2_off) sr_atoms
     [YP09.mkRegion (Some 19%nat) 18 23 18 23 []] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + SEG_C2_off))) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
    rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
  - cbn. tauto.
  - unfold facts_ok; cbn; tauto. }
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hin & Ha). destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19 in Ha.
  right; right; right. exists 8, fpos. split; [left; reflexivity|]. right.
  unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EFly.
  change (fs_frame_bytes 8 / 8) with 2048. unfold sF in Ha. lia. }
(* ---- __asan_memset(blk, 0xa5, 34) at 0x82dcc ---- *)
rename ms into msA, HJ into HJA, HFr into HFrA. clear HF HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (18%bv : bv 5) Rs2. prreg HS (19%bv : bv 5) Rs3.
prreg HS (20%bv : bv 5) Rs4. prreg HS (21%bv : bv 5) Rs5. prreg HS (23%bv : bv 5) Rs7.
prreg HS (24%bv : bv 5) Rs8. prreg HS (25%bv : bv 5) Rs9. prreg HS (27%bv : bv 5) Rs11.
rewrite (EE 8%nat 8%bv eq_refl), V_sp0 in Rs0.
rewrite (EE 9%nat 9%bv eq_refl), V_sp1 in Rs1.
rewrite (EE 19%nat 19%bv eq_refl), V_shF in Rs3.
rewrite (EE 20%nat 20%bv eq_refl), V_s7v in Rs4.
rewrite (EE 7%nat 7%bv eq_refl), V_body in Rs5.
rewrite (EE 23%nat 23%bv eq_refl), V_step in Rs7.
rewrite (EE 24%nat 24%bv eq_refl), V_np in Rs8.
rewrite (EE 25%nat 25%bv eq_refl), V_blki in Rs9.
rewrite (EE 27%nat 27%bv eq_refl), V_blk in Rs11.
rewrite (EE 24%nat 24%bv eq_refl), V_np in Rs2.
rewrite (EE 27%nat 27%bv eq_refl), V_blk in Ra0.
rewrite (EE 2%nat 2%bv eq_refl) in Rsp. rewrite (EE 3%nat 3%bv eq_refl), HGP3 in Rgp.
rewrite (EE 4%nat 4%bv eq_refl), HTP3 in Rtp.
assert (EspA : spZ (ms_regs msA) = sp0 + (sp1 - sp0)).
{ replace (spZ (ms_regs msA)) with (spZ regs3) by (unfold spZ; rewrite Rsp; reflexivity). rewrite HSP3. lia. }
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRA. cbn [ms_mem restrict setpc ss_mem] in HRA.
assert (ZA : forall j, 18 <= j < 23 -> aview SEGS (w_H W3) (ms_mem msA) (sF + j) = Some (if j =? 22 then 2 else 0)).
{ intros j Hj. assert (Hj' : j = 18 \/ j = 19 \/ j = 20 \/ j = 21 \/ j = 22) by lia.
  destruct Hj' as [-> | [-> | [-> | [-> | ->]]]]; cbn [Z.eqb Pos.eqb];
  (eapply s2u_shb; [exact HRA | exact U19 | cbn; tauto | lia]). }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (sF + 18 <= a < sF + 23) ->
  aview SEGS (w_H W3) (ms_mem msA) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. eapply s2u_kept_run; [exact HFrA | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Har. rewrite U19 in Har. lia. }
clear HFrA HRA.
pmkst HS.
eapply SRr_bind.
{ eapply (aj_intrin_at (SK := SK) SEGS B LAWS pa_segs_low OSet (SIGMA SS___asan_memset) AMEMSET W3 (ms_regs msA) (ms_mem msA)
    (sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, fpos)] ly3 S3 _ 1
    (F + 144) 165 34 (sp1 - sp0) (Z_to_bv 64 (BASE + 1324)) HJA).
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - lia. - lia. - lia.
  - exact EspA.
  - exact Ho16. - lia. - rewrite Hes. lia.
  - exact Rgp. - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [| rewrite Hes; lia].
    right; right; right. exists 8, fpos. split; [left; reflexivity|]. left.
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFly. change (fs_frame_bytes 8) with 16384. lia.
  - unfold amem_range. unfold kHighMemBeg, kLowMemEnd, kHighMemEnd. lia.
  - replace (F + 144) with (F + 8 * 18) by lia. replace 34 with (8 * 4 + 2) by lia.
    apply s2u_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
    + intros i Hi. rewrite s2u_div8_add by exact HF8.
      replace (SHADOW_OFF + (F / 8 + 18) + i) with (sF + (18 + i)) by (unfold sF; lia). rewrite ZA by lia.
      destruct (Z.eqb_spec (18 + i) 22); [lia | reflexivity].
    + rewrite s2u_div8_add by exact HF8.
      replace (SHADOW_OFF + (F / 8 + 18) + 4) with (sF + 22) by (unfold sF; lia). rewrite ZA by lia. reflexivity.
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem msA) _ 8 fpos (F + 144) 34 (proj1 HJA) Hfin3);
    [rewrite EFly; lia | rewrite EFly; change (fs_frame_bytes 8) with 16384; lia | lia].
  - exact I. }
cbv beta. intros W4 c4 _ (-> & regsB & memB & mdB & -> & HJB & HPB & Ha0B & HeffB & HfrB & HpresB).
(* ---- run 2: 0x82dd0 .. jal reac_ctrl_build_scene_step 0x82de0 (four register moves; s5 = body and s7 = step
   are callee-saved across the memset, so this build neither spills nor reloads) ---- *)
rewrite Hes in HfrB.
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 144 <= a < F + 178) -> ~ (sF + 18 <= a < sF + 23) ->
  ~ (sp1 - 4096 <= a < sp1) -> aview SEGS (w_H W3) memB a = aview SEGS (w_H W3) mem3 a).
{ intros a H1 H2 H3 H4. rewrite HfrB by lia. apply KA; lia. }
assert (KR8 : getr regsB 8%bv = getr (ms_regs msA) 8%bv) by exact (HPB 8 ltac:(unfold acallee_saved; lia)).
assert (KR9 : getr regsB 9%bv = getr (ms_regs msA) 9%bv) by exact (HPB 9 ltac:(unfold acallee_saved; lia)).
assert (KR18 : getr regsB 18%bv = getr (ms_regs msA) 18%bv) by exact (HPB 18 ltac:(unfold acallee_saved; lia)).
assert (KR19 : getr regsB 19%bv = getr (ms_regs msA) 19%bv) by exact (HPB 19 ltac:(unfold acallee_saved; lia)).
assert (KR20 : getr regsB 20%bv = getr (ms_regs msA) 20%bv) by exact (HPB 20 ltac:(unfold acallee_saved; lia)).
assert (KR21 : getr regsB 21%bv = getr (ms_regs msA) 21%bv) by exact (HPB 21 ltac:(unfold acallee_saved; lia)).
assert (KR23 : getr regsB 23%bv = getr (ms_regs msA) 23%bv) by exact (HPB 23 ltac:(unfold acallee_saved; lia)).
assert (KR24 : getr regsB 24%bv = getr (ms_regs msA) 24%bv) by exact (HPB 24 ltac:(unfold acallee_saved; lia)).
assert (KR25 : getr regsB 25%bv = getr (ms_regs msA) 25%bv) by exact (HPB 25 ltac:(unfold acallee_saved; lia)).
assert (KR27 : getr regsB 27%bv = getr (ms_regs msA) 27%bv) by exact (HPB 27 ltac:(unfold acallee_saved; lia)).
assert (KR2 : getr regsB 2%bv = getr (ms_regs msA) 2%bv) by exact (HPB 2 ltac:(unfold acallee_saved; lia)).
assert (KR3 : getr regsB 3%bv = getr (ms_regs msA) 3%bv) by exact (HPB 3 ltac:(unfold acallee_saved; lia)).
assert (KR4 : getr regsB 4%bv = getr (ms_regs msA) 4%bv) by exact (HPB 4 ltac:(unfold acallee_saved; lia)).
rewrite <- KR8 in Rs0. rewrite <- KR9 in Rs1. rewrite <- KR18 in Rs2. rewrite <- KR19 in Rs3.
rewrite <- KR20 in Rs4. rewrite <- KR21 in Rs5. rewrite <- KR23 in Rs7. rewrite <- KR24 in Rs8.
rewrite <- KR25 in Rs9. rewrite <- KR27 in Rs11. rewrite <- KR2 in Rsp. rewrite <- KR3 in Rgp. rewrite <- KR4 in Rtp.
clear HS Ra0 Ra1 Ra2 Rra HE HEI EE HAG U19 E KR8 KR9 KR18 KR19 KR20 KR21 KR23 KR24 KR25 KR27 KR2 KR3 KR4.
set (stepv := sc_step bs mod 2 ^ 64) in *.
remember (Eimg (Ereg regsB [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regsB []) E) by
  (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsB r) by
  (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof HJB as (HARB & HlyB & _ & _ & _ & HfrsB & _ & _ & JB9 & JB10 & JB11 & JB12 & JB13 & JB14 & _).
assert (HS : st_ok_pi SEGS VAL E (mkSS 1324 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regsB (Z_to_bv 64 (BASE + 1324)) memB (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - unfold facts_ok; cbn; tauto. }
paj_run_shc RUNP RUNC HS HJB.
{ intros a (r & Hin & _). destruct Hin. }
(* ---- reac_ctrl_build_scene_step(blk, body, n', step) at 0x82de0 ---- *)
rename ms into msC, HJB into HJC, HFr into HFrC. clear HF HG.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (12%bv : bv 5) Qa2.
prreg HS (13%bv : bv 5) Qa3. prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp.
prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
prreg HS (8%bv : bv 5) Qs0. prreg HS (9%bv : bv 5) Qs1. prreg HS (18%bv : bv 5) Qs2. prreg HS (19%bv : bv 5) Qs3.
prreg HS (20%bv : bv 5) Qs4. prreg HS (21%bv : bv 5) Qs5. prreg HS (23%bv : bv 5) Qs7.
prreg HS (24%bv : bv 5) Qs8. prreg HS (25%bv : bv 5) Qs9. prreg HS (27%bv : bv 5) Qs11.
rewrite (EE 27%nat 27%bv eq_refl), Rs11 in Qa0.
rewrite (EE 21%nat 21%bv eq_refl), Rs5 in Qa1.
rewrite (EE 24%nat 24%bv eq_refl), Rs8 in Qa2.
rewrite (EE 23%nat 23%bv eq_refl), Rs7 in Qa3.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Qsp.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Qgp. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Qtp.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Qs0. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Qs1.
rewrite (EE 18%nat 18%bv eq_refl), Rs2 in Qs2. rewrite (EE 19%nat 19%bv eq_refl), Rs3 in Qs3.
rewrite (EE 20%nat 20%bv eq_refl), Rs4 in Qs4. rewrite (EE 21%nat 21%bv eq_refl), Rs5 in Qs5.
rewrite (EE 23%nat 23%bv eq_refl), Rs7 in Qs7. rewrite (EE 24%nat 24%bv eq_refl), Rs8 in Qs8.
rewrite (EE 25%nat 25%bv eq_refl), Rs9 in Qs9. rewrite (EE 27%nat 27%bv eq_refl), Rs11 in Qs11.
clear Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs7 Rs8 Rs9 Rs11 Rsp Rgp Rtp.
assert (EspC : spZ (ms_regs msC) = sp0 + (sp1 - sp0)).
{ replace (spZ (ms_regs msC)) with (spZ regs3) by (unfold spZ; rewrite Qsp; reflexivity). rewrite HSP3. lia. }
assert (KC : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msC) a = aview SEGS (w_H W3) memB a).
{ intros a Ha. eapply s2u_kept_run; [exact HFrC | exact Ha |]. intros (r & Hin & _). destruct Hin. }
pose proof HJC as (HARC & HlyC & _ & _ & _ & HfrsC & _ & _ & JC9 & JC10 & JC11 & JC12 & JC13 & JC14 & _).
(* blk's five shadow cells and the frame bytes, at the state the call starts from *)
assert (ZC : forall j, 18 <= j < 23 -> aview SEGS (w_H W3) (ms_mem msC) (sF + j) = Some (if j =? 22 then 2 else 0)).
{ intros j Hj. rewrite KC by lia. rewrite HfrB by lia. apply ZA. lia. }
assert (HBLKC : forall i, 0 <= i < 34 -> aview SEGS (w_H W3) (ms_mem msC) (F + 144 + i) = Some 165).
{ intros i Hi. rewrite KC by lia. change 165 with (165 mod 256). apply HeffB. lia. }
assert (RAC : range_addressable (aview SEGS (w_H W3) (ms_mem msC)) SHADOW_OFF (F + 144) 34).
{ replace (F + 144) with (F + 8 * 18) by lia. replace 34 with (8 * 4 + 2) by lia.
  apply s2u_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
  - intros i Hi. rewrite s2u_div8_add by exact HF8.
    replace (SHADOW_OFF + (F / 8 + 18) + i) with (sF + (18 + i)) by (unfold sF; lia). rewrite ZC by lia.
    destruct (Z.eqb_spec (18 + i) 22); [lia | reflexivity].
  - rewrite s2u_div8_add by exact HF8.
    replace (SHADOW_OFF + (F / 8 + 18) + 4) with (sF + 22) by (unfold sF; lia). rewrite ZC by lia. reflexivity. }
destruct HNN as (HNN1 & HNN2).
assert (HNP : 0 <= npv <= 65535).
{ rewrite Enpv. unfold sc_nprime, sc_u16. cbn [sg_scene_n scene_geom_asan_ubsan].
  destruct (HIN 1 ltac:(lia)) as (H1 & _). destruct (HIN 2 ltac:(lia)) as (H2 & _).
  destruct (Z.land (bs 0) 1 =? 0); lia. }
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem msC) _ 8 fpos HARC Hfin3) as (_ & _ & HFpresC & _).
rewrite EFly in HFpresC. change (fs_frame_bytes 8) with 16384 in HFpresC.
pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem msC) _ 8 fpos HARC Hfin3) as HFimg.
rewrite EFly in HFimg. change (fs_frame_bytes 8) with 16384 in HFimg. unfold off_img in HFimg.
pose proof (pa_obj_img OBJ_TT ltac:(unfold OBJ_TT; lia)) as HTTimg.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem msC) _ body nnv 8 fpos HARC
  ltac:(rewrite HAB; apply in_or_app; right; left; reflexivity) Hfin3) as HSEPbf.
unfold zdisjoint in HSEPbf. cbn [fst snd] in HSEPbf. rewrite EFly in HSEPbf.
change (fs_frame_bytes 8) with 16384 in HSEPbf.
destruct HBLK as (HB4096 & HBz2 & HBceil & HBal & HBwr & HBtok).
pose proof (req_size_pos nnv ltac:(lia)) as (HRS1 & HRS2).
pose proof (zone2_band _ _ HBz2) as HBband.
assert (HBODYC : forall i, 0 <= i < nnv ->
  aview SEGS (w_H W3) (ms_mem msC) (body + i) = Some (bv_unsigned (nth (Z.to_nat i) bb (Z_to_bv 8 0)))).
{ intros i Hi. rewrite KC by lia. rewrite HfrB by lia. rewrite KA by lia.
  destruct (garr8_nthZ SEGS (mrestrict (w_H W3) mem3) body (u8s bb) i HGBB ltac:(lia)
    ltac:(unfold u8s; rewrite length_map; lia)) as (Hv & Hr).
  unfold u8s in Hv, Hr. rewrite (map_nth bv_unsigned bb (Z_to_bv 8 0)) in Hv, Hr.
  apply aview_of_val_mem1; [exact Hv | exact Hr]. }
pmkst HS.
rewrite pa_sigma_reac_ctrl_build_scene_step.
eapply SRr_bind.
{ eapply (BSS W3 (ms_regs msC) (ms_mem msC) _ (sw_stk WK) sp0 (sp1 - sp0) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(8, fpos)] ly3 S3 1 (F + 144) body npv stepv bb HJC).
  - exact EspC.
  - exact Ho16.
  - lia.
  - rewrite EBW. lia.
  - exact Qgp.
  - exact Qtp.
  - rewrite Qra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Qa0.
  - exact Qa1.
  - exact Qa2.
  - exact Qa3.
  - lia.
  - lia.
  - lia.
  - unfold stepv. pose proof (Z.mod_pos_bound (sc_step bs) (2 ^ 64) ltac:(lia)). lia.
  - intros HOK. destruct (okZ_true _ _ _ _ HOK) as (Hbk0 & Hbd0 & Hn8904 & Hst342).
    unfold SCENE_BYTES in Hn8904. unfold SCENE_LAST in Hst342.
    assert (Enn8 : nnv = 8904) by (rewrite Ennv2, <- Hn8904; destruct (Z.eqb_spec npv 0); lia).
    split.
    { exists 8, fpos. split; [left; reflexivity|]. split; [lia|].
      rewrite EFly. change (fs_frame_bytes 8) with 16384. unfold BLK_LEN. lia. }
    split.
    { intros a Ha. unfold BLK_LEN in Ha. apply (proj1 (HFpresC a ltac:(lia))). }
    split.
    { unfold BLK_LEN. exact RAC. }
    split.
    { apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem msC) _ 8 fpos (F + 144) BLK_LEN HARC Hfin3);
      [rewrite EFly; lia | rewrite EFly; change (fs_frame_bytes 8) with 16384; unfold BLK_LEN; lia | unfold BLK_LEN; lia]. }
    split.
    { exists body, nnv. split; [rewrite HAB; apply in_or_app; right; left; reflexivity|].
      split; [lia|]. unfold SCENE_BYTES. lia. }
    split.
    { unfold SCENE_BYTES. lia. }
    split.
    { intros i Hi. unfold SCENE_BYTES in Hi. apply HBODYC. lia. }
    assert (HRDP0 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)))
      by (rewrite <- HWRLO, <- HWRHI; exact HROD0).
    pose proof (arodata_ok_journalP (SK := SK) SEGS pa_relro_lo pa_relro_hi pa_relro_img (RO := RO) B (sw_stk WK) sp0 []
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, fpos)] ly3 S3 W3 (ms_mem msC) _ 1 HJC HRDP0) as HRDC.
    destruct (s2u_tt ly3 S3 W3 (ms_mem msC) _ HARC HRDC) as (HTT1 & HTT2 & HTT3).
    split; [unfold TT_LEN; exact HTT1|].
    split; [unfold TT_LEN; exact HTT2|].
    split; [unfold TT_LEN; exact HTT3|].
    unfold TT_LEN, BLK_LEN, A_TT. lia. }
cbv beta. intros W5 c5 _ (-> & regsD & memD & mdD & -> & HJD & HPD & HeffD & HpresD & HrD).
(* ---- what the state after the call keeps of the cut C2, and the cut C3 from it: both arms of B end at C3
   (0x82e50) in a state whose memory agrees with memD outside the callee window and blk, so the cut is
   established once, here, for any such final state ---- *)
assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 144 <= a < F + 178) -> ~ (sF + 18 <= a < sF + 23) ->
  ~ (sp1 - 4144 <= a < sp1) -> aview SEGS (w_H W3) memD a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha H1 H2 H3.
  rewrite (HeffD a Ha ltac:(rewrite EspC, EBW; lia) ltac:(intros _; unfold BLK_LEN; lia)).
  rewrite (KC a Ha). apply KB; lia. }
assert (ZD : forall j, 18 <= j < 23 -> aview SEGS (w_H W3) memD (sF + j) = Some (if j =? 22 then 2 else 0)).
{ intros j Hj. rewrite (HeffD (sF + j) ltac:(lia) ltac:(rewrite EspC, EBW; lia) ltac:(intros _; unfold BLK_LEN; lia)).
  apply ZC. exact Hj. }
assert (EC3 : AF_LLVMFuzzerTestOneInput + SEG_C3_off = 1452) by (vm_compute; reflexivity).
assert (TOC3 : forall ly' S' W' regs' mem' md',
  ajournal (SK := SK) SEGS B (sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, fpos)]
    ly' S' W' mem' md' 1 ->
  ablocks B ly' S' = ablocks B ly3 S3 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - 8496 <= a < sp1) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) memD a) ->
  (forall a, (F <= a < F + 16384 \/ sF <= a < sF + 2048) -> ~ (F + 144 <= a < F + 178) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) memD a) ->
  (forall i, 0 <= i < req_size nnv -> aview SEGS (w_H W') mem' (body + i) = aview SEGS (w_H W3) memD (body + i)) ->
  getr regs' 8%bv = w64 sp0 -> getr regs' 9%bv = w64 sp1 -> getr regs' 19%bv = w64 (shadow_addr F) ->
  getr regs' 20%bv = w64 body -> getr regs' 23%bv = w64 stepv -> getr regs' 24%bv = w64 npv ->
  getr regs' 25%bv = w64 (F + 32) -> spZ regs' = sp1 ->
  getr regs' 3%bv = w64 (as_gp B) -> getr regs' 4%bv = w64 (as_tp B) ->
  SRr SEGS W' (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 1452)) mem' (seg_rom SEGS)) md') POST).
{ intros ly' S' W' regs' mem' md' HJx HABx MA MF MB R8 R9 R19 R20 R23 R24 R25 Rsp' R3 R4.
  pose proof HJx as (HARx & Hlyx & _ & _ & _ & Hfrsx & _).
  assert (HFRx : frames S' = [(8, fpos)]) by (rewrite Hfrsx, Hfr0; reflexivity).
  assert (Hfinx : In (8, fpos) (frames S')) by (rewrite HFRx; left; reflexivity).
  assert (EFlyx : frame_addr ly' 8 fpos = F).
  { destruct Hlyx as (_ & _ & _ & _ & _ & EFa & _). rewrite EFe. unfold frame_addr. rewrite EFa. reflexivity. }
  destruct (al_frames _ _ LAWS ly' S' W' mem' md' 8 fpos HARx Hfinx) as (_ & _ & HFpresx & HFSpresx).
  rewrite EFlyx in HFpresx, HFSpresx. change (fs_frame_bytes 8) with 16384 in HFpresx, HFSpresx.
  change (16384 / 8) with 2048 in HFSpresx. unfold shadow_addr in HFSpresx.
  assert (MF3 : forall a, (F <= a < F + 16384 \/ sF <= a < sF + 2048) -> ~ (F + 144 <= a < F + 178) ->
    ~ (sF + 18 <= a < sF + 23) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha H1 H2. rewrite (MF a Ha H1). apply KD; lia. }
  assert (MA3 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - 8496 <= a < sp1) ->
    aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha H1. rewrite (MA a Ha H1). apply KD; lia. }
  assert (MB3 : forall i, 0 <= i < req_size nnv ->
    aview SEGS (w_H W') mem' (body + i) = aview SEGS (w_H W3) mem3 (body + i)).
  { intros i Hi. rewrite (MB i Hi). apply KD; lia. }
  assert (SP3 : forall off, 0 <= off <= 216 -> rdword (aview SEGS (w_H W') mem') (sp1 + off)
    = rdword (aview SEGS (w_H W3) mem3) (sp1 + off)).
  { intros off Hoff. apply rdword_ext. intros k Hk. apply MA3; lia. }
  replace (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 1452)) mem' (seg_rom SEGS)) md')
    with (cfg_at SEGS (sg_pc_c3 scene_geom_asan_ubsan) regs' mem' md')
    by (unfold cfg_at; cbn [sg_pc_c3 scene_geom_asan_ubsan]; unfold w64; rewrite <- EC3; do 3 f_equal; lia).
  apply (HC3 ly' S' W' regs' mem' md' bs body bb).
  unfold cut_C3, sc_j, sc_frame, sc_shr, sc_open, sc_img.
  cbn [sg_cid sg_sh_blki_lo sg_sh_blki_hi sg_off_blk sg_blk_n sg_off_mac sg_mac_n sg_scene_n scene_geom_asan_ubsan].
  change (sc_F SEGS scene_geom_asan_ubsan cx) with F. change (spZ (c_regs cx)) with sp0. change (c_sp1 cx) with sp1.
  change (c_fpos cx) with fpos. rewrite <- Ennv, <- Enpv.
  change (fs_frame_bytes 8) with 16384.
  split.
  { split; [exact HJx|]. split; [exact HFRx|]. cbn. exact I. }
  split.
  { rewrite HABx. exact HAB. }
  split.
  { rewrite (blocks_bytes_bsum B ly' S'), HABx, <- (blocks_bytes_bsum B ly3 S3). exact HBB. }
  split.
  { exact (conj HB4096 (conj HBz2 (conj HBceil (conj HBal (conj HBwr HBtok))))). }
  split; [exact HLBB|].
  split.
  { apply (garr8_frame SEGS (mrestrict (w_H W3) mem3)); [exact HGBB|].
    intros a Ha. unfold u8s in Ha. rewrite length_map in Ha. apply mbyte_of_aview.
    replace a with (body + (a - body)) by lia. apply MB3. lia. }
  split.
  { split.
    { rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [exact HFLAG|].
      intros k Hk. apply MF3; lia. }
    split.
    { intros a Ha. exact (proj1 (HFpresx a Ha)). }
    { intros a Ha. unfold shadow_addr in Ha. change (SHADOW_OFF + F / 8) with sF in Ha, HFSpresx.
      change (16384 / 8) with 2048 in Ha.
      pose proof (HFSpresx (a - sF)) as HH.
      replace (sF + (a - sF)) with a in HH by lia.
      assert (Hai : 0 <= a - sF < 2048) by lia.
      exact (proj1 (HH Hai)). } }
  split.
  { intros j Hj. rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [exact (HSAV j Hj)|].
    intros k Hk. apply MA3; lia. }
  split.
  { unfold sc_shbg in HSHBG |- *. cbn [sg_sh_bg scene_geom_asan_ubsan] in HSHBG |- *.
    rewrite Forall_forall in HSHBG |- *. intros t Ht. specialize (HSHBG t Ht). unfold sc_shr in HSHBG |- *.
    change (sc_F SEGS scene_geom_asan_ubsan cx) with F in HSHBG |- *.
    intros o Ho. assert (Ht' : 0 <= fst (fst t) /\ snd (fst t) <= 0x498 /\ (snd (fst t) <= 18 \/ 23 <= fst (fst t))).
    { cbn in Ht. repeat (destruct Ht as [<- | Ht]; [cbn; lia|]). destruct Ht. }
    rewrite MF3; [apply HSHBG; exact Ho | unfold shadow_addr in *; lia | unfold shadow_addr in *; lia
      | unfold shadow_addr in *; lia]. }
  split.
  { intros o Ho. rewrite MF3; [apply HSHI; exact Ho | unfold shadow_addr; lia | unfold shadow_addr; lia
      | unfold shadow_addr; lia]. }
  split.
  { unfold block_shadow. split; [rewrite Z.add_mod, HF8 by lia; reflexivity|]. split; [lia|].
    change ((34 + 7) / 8) with 5. change (34 / 8) with 4. change (34 mod 8) with 2.
    intros i Hi. unfold shadow_of_addr.
    replace (SHADOW_OFF + (F + 144) / 8 + i) with (sF + (18 + i))
      by (unfold sF; replace (F + 144) with (F + 8 * 18) by lia; rewrite s2u_div8_add by exact HF8; lia).
    rewrite MF; [| lia | lia]. rewrite ZD by lia.
    assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
    destruct Hi' as [-> | [-> | [-> | [-> | ->]]]]; reflexivity. }
  split.
  { unfold block_shadow in HMACO |- *.
    destruct HMACO as (HM1 & HM2 & HM3). split; [exact HM1|]. split; [exact HM2|].
    intros i Hi. change ((6 + 7) / 8) with 1 in Hi. rewrite <- (HM3 i Hi).
    rewrite (s2u_sh_off _ 112 14 i) by (first [exact HF8 | reflexivity]).
    rewrite (s2u_sh_off _ 112 14 i) by (first [exact HF8 | reflexivity]).
    exact (MF3 (sF + (14 + i)) ltac:(lia) ltac:(lia) ltac:(lia)). }
  split.
  { split; [exact Rsp'|]. split; [exact R3|]. split; [exact R4|].
    rewrite HWRLO, HWRHI. rewrite HWRLO, HWRHI in HROD0.
    exact (arodata_ok_journalP (SK := SK) SEGS pa_relro_lo pa_relro_hi pa_relro_img (RO := RO) B (sw_stk WK) sp0 []
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, fpos)] ly' S' W' mem' md' 1 HJx HROD0). }
  split; [exact HIN|].
  split; [lia|].
  split.
  { apply (garr8_frame SEGS (mrestrict (w_H W3) mem3)); [exact HMAC|].
    intros a Ha. cbn [sc_macb length] in Ha. apply mbyte_of_aview. apply MF3; lia. }
  cbv [vat RV_s0 RV_s1 RV_s2 RV_s3 RV_s4 RV_s5 RV_s6 RV_s7 RV_s8 RV_s9 RV_s10 RV_s11 RV_a1 RV_a6 RV_t2].
  cbn [sg3_sp0 sg3_sp1 sg3_F sg3_Fb sg3_Fsp sg3_shF sg3_blki sg3_expect sg3_mac sg3_shexp
       sg3_body sg3_nn sg3_nprime sg3_flags sg3_step sg_off_blki sg_off_expect sg_off_mac scene_geom_asan_ubsan].
  split; [exact R8|]. split; [exact R9|].
  split; [rewrite (SP3 24) by lia; exact V_Fb|].
  split; [rewrite (SP3 40) by lia; exact V_Fsp|].
  split; [rewrite (SP3 40) by lia; exact V_Fsp|].
  split; [exact R19|]. split; [exact R25|].
  split; [rewrite (SP3 48) by lia; exact V_expect|].
  split; [rewrite (SP3 56) by lia; exact V_mac|].
  split; [rewrite (SP3 16) by lia; exact V_shexp|].
  split; [exact R20|].
  split; [rewrite (SP3 32) by lia; exact V_nn|].
  split; [exact R24|].
  split; [rewrite (SP3 88) by lia; exact V_flags|].
  exact R23. }
(* ---- the result check 0x82de4 .. 0x82e0c: a1 = -(n' <> 8904 | sx16(s4) < 0 | ~(sx16(step) < 343)) ---- *)
rewrite Qra.
assert (KD8 : getr regsD 8%bv = getr (ms_regs msC) 8%bv) by exact (HPD 8 ltac:(unfold acallee_saved; lia)).
assert (KD9 : getr regsD 9%bv = getr (ms_regs msC) 9%bv) by exact (HPD 9 ltac:(unfold acallee_saved; lia)).
assert (KD18 : getr regsD 18%bv = getr (ms_regs msC) 18%bv) by exact (HPD 18 ltac:(unfold acallee_saved; lia)).
assert (KD19 : getr regsD 19%bv = getr (ms_regs msC) 19%bv) by exact (HPD 19 ltac:(unfold acallee_saved; lia)).
assert (KD20 : getr regsD 20%bv = getr (ms_regs msC) 20%bv) by exact (HPD 20 ltac:(unfold acallee_saved; lia)).
assert (KD21 : getr regsD 21%bv = getr (ms_regs msC) 21%bv) by exact (HPD 21 ltac:(unfold acallee_saved; lia)).
assert (KD23 : getr regsD 23%bv = getr (ms_regs msC) 23%bv) by exact (HPD 23 ltac:(unfold acallee_saved; lia)).
assert (KD24 : getr regsD 24%bv = getr (ms_regs msC) 24%bv) by exact (HPD 24 ltac:(unfold acallee_saved; lia)).
assert (KD25 : getr regsD 25%bv = getr (ms_regs msC) 25%bv) by exact (HPD 25 ltac:(unfold acallee_saved; lia)).
assert (KD27 : getr regsD 27%bv = getr (ms_regs msC) 27%bv) by exact (HPD 27 ltac:(unfold acallee_saved; lia)).
assert (KD2 : getr regsD 2%bv = getr (ms_regs msC) 2%bv) by exact (HPD 2 ltac:(unfold acallee_saved; lia)).
assert (KD3 : getr regsD 3%bv = getr (ms_regs msC) 3%bv) by exact (HPD 3 ltac:(unfold acallee_saved; lia)).
assert (KD4 : getr regsD 4%bv = getr (ms_regs msC) 4%bv) by exact (HPD 4 ltac:(unfold acallee_saved; lia)).
rewrite <- KD8 in Qs0. rewrite <- KD9 in Qs1. rewrite <- KD18 in Qs2. rewrite <- KD19 in Qs3.
rewrite <- KD20 in Qs4. rewrite <- KD21 in Qs5. rewrite <- KD23 in Qs7. rewrite <- KD24 in Qs8.
rewrite <- KD25 in Qs9. rewrite <- KD27 in Qs11. rewrite <- KD2 in Qsp. rewrite <- KD3 in Qgp. rewrite <- KD4 in Qtp.
clear HS HFrC Qa0 Qa1 Qa2 Qa3 HE HEI EE HAG E KD8 KD9 KD18 KD19 KD20 KD21 KD23 KD24 KD25 KD27 KD2 KD3 KD4.
remember (Eimg (Ereg regsD [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regsD []) E) by
  (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsD r) by
  (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (mkSS 1344 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regsD (Z_to_bv 64 (BASE + 1344)) memD (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - unfold facts_ok; cbn; tauto. }
(* the values the check reads: a0 (the callee's result), s2, s4 and s7 *)
assert (Hb3 : 0 <= bs 3 < 256) by exact (proj1 (HIN 3 ltac:(lia))).
assert (Hb4 : 0 <= bs 4 < 256) by exact (proj1 (HIN 4 ltac:(lia))).
assert (Rst : -32768 <= sx16 (bs 3 + 256 * bs 4) < 32768)
  by (unfold sx16; destruct (Z.ltb_spec (bs 3 + 256 * bs 4) 32768); lia).
assert (EOK : scene_step_okZ (F + 144) body npv stepv
  = (npv =? 8904) && (0 <=? sx16 (bs 3 + 256 * bs 4)) && (sx16 (bs 3 + 256 * bs 4) <=? 342)).
{ unfold stepv, sc_step. apply s2u_ok_iff; lia. }
assert (UA18 : U E (SOff 18 0) = if npv =? 8904 then 0 else 1).
{ rewrite U_SOff, (EE 18%nat 18%bv eq_refl), Qs2, Z.add_0_r. unfold w64. rewrite s2u_neq_flag by lia.
  apply s2u_zc. destruct (npv =? 8904); lia. }
assert (UA20 : U E (SOff 20 0) = sx16 (256 * bs 4) mod 2 ^ 64).
{ rewrite U_SOff, (EE 20%nat 20%bv eq_refl), Qs4, Z.add_0_r. unfold w64. rewrite unsigned_lit.
  unfold zcanon, M64, sc_s7v. rewrite !Zmod_mod. reflexivity. }
assert (UA23 : U E (SOff 23 0) = sx16 (bs 3 + 256 * bs 4) mod 2 ^ 64).
{ rewrite U_SOff, (EE 23%nat 23%bv eq_refl), Qs7, Z.add_0_r. unfold w64. rewrite unsigned_lit.
  unfold zcanon, M64, stepv, sc_step. rewrite !Zmod_mod. reflexivity. }
assert (UA10 : U E (SOff 10 0) = if scene_step_okZ (F + 144) body npv stepv then 0 else 2 ^ 64 - 1).
{ rewrite U_SOff, (EE 10%nat 10%bv eq_refl), Z.add_0_r.
  destruct (scene_step_okZ (F + 144) body npv stepv); [destruct HrD as (HrD & _)|]; rewrite HrD;
  unfold w64; rewrite unsigned_lit; vm_compute; reflexivity. }
paj_run_shc RUNP RUNC HS HJD.
{ intros a (r & Hin & _). destruct Hin. }
rename ms into msE, HJD into HJE, HFr into HFrE. clear HF HG.
(* 0x82e0c `bne a0,a1` to the abort at 0x83238 (__asan_handle_no_return; abort): not taken, because the callee's
   result is exactly -(the check's condition) *)
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ne_U in Hc.
  rewrite (s2u_rcheck E (bs 3) (bs 4) npv Hb3 Hb4 UA18 UA20 UA23) in Hc.
  rewrite <- EOK, UA10 in Hc. destruct (scene_step_okZ (F + 144) body npv stepv); vm_compute in Hc; discriminate Hc. }
clear Hc.
(* 0x82e10 `mv s4,s5`; 0x82e14 `beqz a0` splits the accepting call (check_step) from the refusing one ("changed") *)
paj_run_shc RUNP RUNC HS HJE.
{ intros a (r & Hin & _). destruct Hin. }
rename ms into msF, HJE into HJF, HFr into HFrF. clear HF HG.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) memD a).
{ intros a Ha.
  rewrite (s2u_kept_run _ _ _ _ _ a HFrF Ha ltac:(intros (r & Hr & _); vm_compute in Hr; destruct Hr)).
  exact (s2u_kept_run _ _ _ _ _ a HFrE Ha ltac:(intros (r & Hr & _); vm_compute in Hr; destruct Hr)). }
clear HFrE HFrF.
psrr_branch_pi RUNP BR HS.
- (* the accepting call (a0 = 0): 0x82e40 .. jal check_step 0x82e4c, which returns to C3 *)
  assert (HOK : scene_step_okZ (F + 144) body npv stepv = true).
  { rewrite branch_eq_U, UA10, U_lit in Hc by lia.
    destruct (scene_step_okZ (F + 144) body npv stepv); [reflexivity | vm_compute in Hc; discriminate Hc]. }
  rewrite HOK in HrD. destruct HrD as (HrD0 & HrDblk).
  paj_run_shc RUNP RUNC HS HJF.
  { intros a (r & Hin & _). vm_compute in Hin. destruct Hin. }
  rename ms into msH, HJF into HJH, HFr into HFrH. clear HF HG.
  assert (KH : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msH) a = aview SEGS (w_H W3) memD a).
  { intros a Ha.
    rewrite (s2u_kept_run _ _ _ _ _ a HFrH Ha ltac:(intros (r & Hr & _); vm_compute in Hr; destruct Hr)).
    exact (KF a Ha). }
  clear HFrH.
  prreg HS (10%bv : bv 5) H10. prreg HS (11%bv : bv 5) H11. prreg HS (12%bv : bv 5) H12. prreg HS (1%bv : bv 5) H1.
  prreg HS (8%bv : bv 5) H8. prreg HS (9%bv : bv 5) H9. prreg HS (19%bv : bv 5) H19. prreg HS (20%bv : bv 5) H20.
  prreg HS (23%bv : bv 5) H23. prreg HS (24%bv : bv 5) H24. prreg HS (25%bv : bv 5) H25.
  prreg HS (2%bv : bv 5) H2. prreg HS (3%bv : bv 5) H3. prreg HS (4%bv : bv 5) H4.
  rewrite (EE 27%nat 27%bv eq_refl), Qs11 in H10. rewrite (EE 21%nat 21%bv eq_refl), Qs5 in H11.
  rewrite (EE 23%nat 23%bv eq_refl), Qs7 in H12.
  rewrite (EE 8%nat 8%bv eq_refl), Qs0 in H8. rewrite (EE 9%nat 9%bv eq_refl), Qs1 in H9.
  rewrite (EE 19%nat 19%bv eq_refl), Qs3 in H19. rewrite (EE 21%nat 21%bv eq_refl), Qs5 in H20.
  rewrite (EE 23%nat 23%bv eq_refl), Qs7 in H23. rewrite (EE 24%nat 24%bv eq_refl), Qs8 in H24.
  rewrite (EE 25%nat 25%bv eq_refl), Qs9 in H25.
  rewrite (EE 2%nat 2%bv eq_refl), Qsp in H2. rewrite (EE 3%nat 3%bv eq_refl), Qgp in H3.
  rewrite (EE 4%nat 4%bv eq_refl), Qtp in H4.
  assert (EspH : spZ (ms_regs msH) = sp0 + (sp1 - sp0)).
  { replace (spZ (ms_regs msH)) with (spZ regs3) by (unfold spZ; rewrite H2; reflexivity). rewrite HSP3. lia. }
  destruct (okZ_true _ _ _ _ HOK) as (_ & _ & Hn8904 & Hst342). unfold SCENE_BYTES in Hn8904. unfold SCENE_LAST in Hst342.
  assert (Enn8 : nnv = 8904) by (rewrite Ennv2, Hn8904; reflexivity).
  pose proof (proj1 HJH) as HARH.
  pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
  pmkst HS.
  rewrite pa_sigma_check_step.
  set (CH1 := if sp0 + 16 <? ly_top ly3 then [(sp0, raZ (c_regs cx), s0Z (c_regs cx))] else []).
  eapply SRr_bind.
  { eapply (cl_callS (SK := SK) (PI := PI_scene) B LAWS W3 (ms_regs msH) (ms_mem msH) _ (sw_stk WK) sp0 []
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, fpos)] ly3 S3 _ 1 TCHECK_STEP_STK [] EV_CHECK_STEP
      (sp1 - sp0) (getr (ms_regs msH) 1%bv) CH1 (fun ly' S' W' regs' mem' md' => ablocks B ly' S' = ablocks B ly3 S3) HJH).
    - exact EspH.
    - exact Ho16.
    - lia.
    - rewrite ECS. lia.
    - rewrite ECS. lia.
    - exact H3.
    - exact H4.
    - reflexivity.
    - rewrite H1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite H1. rewrite unsigned_lit_small by lia. lia.
    - replace (sp0 + (sp1 - sp0)) with sp1 by lia.
      replace (s0Z (ms_regs msH)) with sp0 by (unfold s0Z; rewrite H8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
      assert (HchL : achain ly3 (aview SEGS (w_H (c_W cx)) (c_mem cx)) (spZ (c_regs cx)) (s0Z (c_regs cx)) []).
      { apply (achain_ly_top (c_ly cx) ly3); [exact Etop3 | exact Hch]. }
      unfold CH1.
      apply (s2u_chain ly3 (aview SEGS (w_H (c_W cx)) (c_mem cx)) (aview SEGS (w_H W3) (ms_mem msH)) (c_regs cx) sp1 HchL).
      + rewrite Etop3. lia.
      + intros a Ha. rewrite (KH a ltac:(lia)). rewrite (KD a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        apply J9; lia.
      + rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) (ms_mem msH))).
        * replace (spZ (c_regs cx) - 8) with (sp0 - 8 - 8 * 0) by (unfold sp0; lia). exact (HSAV 0 ltac:(lia)).
        * intros k Hk. etransitivity; [apply KH; lia|]. apply KD; lia.
      + rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) (ms_mem msH))).
        * replace (spZ (c_regs cx) - 16) with (sp0 - 8 - 8 * 1) by (unfold sp0; lia). exact (HSAV 1 ltac:(lia)).
        * intros k Hk. etransitivity; [apply KH; lia|]. apply KD; lia.
      + exact Hra4.
      + lia.
      + pose proof (Z.mod_divide sp0 16 ltac:(lia)) as [Hd _]. destruct (Hd Hal16) as [q Hq].
        apply Z.mod_divide; [lia|]. exists (2 * q). lia.
      + lia.
    - intros HPRE.
      assert (HRDP0 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)))
        by (rewrite <- HWRLO, <- HWRHI; exact HROD0).
      assert (ZH : forall j, 18 <= j < 23 -> aview SEGS (w_H W3) (ms_mem msH) (sF + j) = Some (if j =? 22 then 2 else 0)).
      { intros j Hj. rewrite (KH (sF + j) ltac:(lia)). apply ZD. exact Hj. }
      apply (TCHECKX ly3 S3 W3 (ms_regs msH) (ms_mem msH) _ CH1 (F + 144) body stepv bb HPRE).
      + rewrite EspH. replace (sp0 + (sp1 - sp0)) with sp1 by lia. exact Ho32.
      + rewrite EspH, Etop3. lia.
      + rewrite HFRS3. cbn. lia.
      + exact (arodata_ok_journalP (SK := SK) SEGS pa_relro_lo pa_relro_hi pa_relro_img (RO := RO) B (sw_stk WK) sp0 []
          (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, fpos)] ly3 S3 W3 (ms_mem msH) _ 1 HJH HRDP0).
      + exact H10.
      + exact H11.
      + exact H12.
      + unfold CS_LAST. split; [unfold stepv; apply Z.mod_pos_bound; lia | exact Hst342].
      + unfold afobj, CS_BLK_LEN. split.
        { exists 8, fpos. split; [exact Hfin3|]. split; [lia|]. rewrite EFly. split; [exact HF8|].
          change (fs_frame_bytes 8) with 16384. lia. }
        split; [rewrite Z.add_mod, HF8 by lia; reflexivity|].
        replace (F + 144) with (F + 8 * 18) by lia. replace 34 with (8 * 4 + 2) by lia.
        apply s2u_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
        * intros i Hi. rewrite s2u_div8_add by exact HF8.
          replace (SHADOW_OFF + (F / 8 + 18) + i) with (sF + (18 + i)) by (unfold sF; lia). rewrite ZH by lia.
          destruct (Z.eqb_spec (18 + i) 22); [lia | reflexivity].
        * rewrite s2u_div8_add by exact HF8.
          replace (SHADOW_OFF + (F / 8 + 18) + 4) with (sF + 22) by (unfold sF; lia). rewrite ZH by lia. reflexivity.
      + rewrite HAB. apply in_or_app. right. left. unfold CS_BODY_LEN. rewrite Enn8. reflexivity.
      + unfold CS_BODY_LEN. apply Nat2Z.inj. rewrite Z2Nat.id by lia. lia.
      + intros i Hi. unfold CS_BODY_LEN in Hi. rewrite (KH (body + i) ltac:(lia)).
        rewrite (HeffD (body + i) ltac:(lia) ltac:(rewrite EspC, EBW; lia) ltac:(intros _; unfold BLK_LEN; lia)).
        apply HBODYC. lia.
      + intros i Hi. unfold CS_BLK_LEN in Hi. rewrite (KH (F + 144 + i) ltac:(lia)). apply HrDblk. unfold BLK_LEN. lia.
      + unfold EV_CHECK_STEP. lia.
      + unfold LIVE_CHECK_STEP. pose proof (wf_live _ _ _ _ _ (am_wf _ _ _ _ (proj1 HAR3))) as HLV. lia.
    - intros a Ha. left. exact Ha. }
  cbv beta. intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HJ6c & HP6 & HAB6).
  rewrite H1. change (1 + EV_CHECK_STEP) with 1 in HJ6.
  pose proof HJ6c as (_ & _ & _ & _ & _ & _ & _ & _ & C9 & C10 & C11 & C12 & _).
  rewrite ECS in C9.
  assert (HinB : In (body, nnv) (ablocks B ly3 S3)) by (rewrite HAB; apply in_or_app; right; left; reflexivity).
  assert (P8 : getr regs6 8%bv = getr (ms_regs msH) 8%bv) by exact (HP6 8 ltac:(unfold acallee_saved; lia)).
  assert (P9 : getr regs6 9%bv = getr (ms_regs msH) 9%bv) by exact (HP6 9 ltac:(unfold acallee_saved; lia)).
  assert (P19 : getr regs6 19%bv = getr (ms_regs msH) 19%bv) by exact (HP6 19 ltac:(unfold acallee_saved; lia)).
  assert (P20 : getr regs6 20%bv = getr (ms_regs msH) 20%bv) by exact (HP6 20 ltac:(unfold acallee_saved; lia)).
  assert (P23 : getr regs6 23%bv = getr (ms_regs msH) 23%bv) by exact (HP6 23 ltac:(unfold acallee_saved; lia)).
  assert (P24 : getr regs6 24%bv = getr (ms_regs msH) 24%bv) by exact (HP6 24 ltac:(unfold acallee_saved; lia)).
  assert (P25 : getr regs6 25%bv = getr (ms_regs msH) 25%bv) by exact (HP6 25 ltac:(unfold acallee_saved; lia)).
  assert (P2 : getr regs6 2%bv = getr (ms_regs msH) 2%bv) by exact (HP6 2 ltac:(unfold acallee_saved; lia)).
  assert (P3 : getr regs6 3%bv = getr (ms_regs msH) 3%bv) by exact (HP6 3 ltac:(unfold acallee_saved; lia)).
  assert (P4 : getr regs6 4%bv = getr (ms_regs msH) 4%bv) by exact (HP6 4 ltac:(unfold acallee_saved; lia)).
  apply (TOC3 ly6 S6 W6 regs6 mem6 md6 HJ6 HAB6).
  + intros a Ha Hn. rewrite (C9 a Ha ltac:(lia)). apply KH. lia.
  + intros a Ha Hn.
    assert (Hz : in_zr a (frame_rng ly3 (8, fpos)) \/ in_zr a (shadow_addr (frame_addr ly3 8 fpos), fs_frame_bytes 8 / 8)).
    { unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFly. change (fs_frame_bytes 8) with 16384. change (16384 / 8) with 2048.
      unfold shadow_addr. change (SHADOW_OFF + F / 8) with sF. destruct Ha as [Ha | Ha]; [left | right]; clear - Ha; lia. }
    rewrite (C12 8 fpos a Hfin3 Hz (inFP_nil a)). apply KH.
    destruct Ha as [Ha | Ha]; clear - Ha HF4096 HFceil AC1 HsFlo HsFhi; lia.
  + intros i Hi. rewrite (C10 body nnv i HinB ltac:(rewrite HAB6; exact HinB) Hi (inFP_nil (body + i))).
    apply KH. lia.
  + rewrite P8. exact H8.
  + rewrite P9. exact H9.
  + rewrite P19. exact H19.
  + rewrite P20. exact H20.
  + rewrite P23. exact H23.
  + rewrite P24. exact H24.
  + rewrite P25. exact H25.
  + replace (spZ regs6) with (spZ (ms_regs msH)) by (unfold spZ; rewrite P2; reflexivity). rewrite EspH. lia.
  + rewrite P3. exact H3.
  + rewrite P4. exact H4.
- (* the refusing call (a0 = -1): the 34-turn "changed" loop 0x82e18-0x82e34 reads blk, which the refusing
     call left as the memset wrote it (a Theorem Labs lane's post: only the own stack window changes), so a0 stays 0 and
     `beqz a0` 0x82e38 jumps to C3; the abort `j` 0x82e3c to 0x83238 is not reached *)
  assert (HOK : scene_step_okZ (F + 144) body npv stepv = false).
  { rewrite branch_eq_U, UA10, U_lit in Hc by lia.
    destruct (scene_step_okZ (F + 144) body npv stepv); [vm_compute in Hc; discriminate Hc | reflexivity]. }
  assert (HBLKF : forall i, 0 <= i < 34 -> aview SEGS (w_H W3) (ms_mem msF) (F + 144 + i) = Some 165).
  { intros i Hi. rewrite (KF (F + 144 + i) ltac:(lia)).
    rewrite (HeffD (F + 144 + i) ltac:(lia) ltac:(rewrite EspC, EBW; lia)
      ltac:(intros Hk; rewrite HOK in Hk; discriminate Hk)).
    apply HBLKC. exact Hi. }
  assert (U27 : bv_unsigned (ew E 27) = F + 144).
  { rewrite (EE 27%nat 27%bv eq_refl), Qs11. unfold w64. apply unsigned_lit_small. lia. }
  pose proof (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 27%nat) 0 34 0 0 s2u_blk_chunks) HS
    ltac:(vm_compute; reflexivity)) as HS'.
  assert (HRB : region_ok SEGS E (ms_mem (restrict (w_H W3) msF)) (YP09.mkRegion (Some 27%nat) 0 34 0 0 s2u_blk_chunks)).
  { unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
    rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    unfold s2u_blk_chunks. apply Forall_forall. intros c Hc'. apply in_map_iff in Hc' as (j & <- & Hj).
    apply in_seq in Hj.
    apply (chunk_ok_val SEGS E _ (F + 144) (Z.of_nat j) 1 (SLit 165) 165); [reflexivity | cbn; lia | cbn; lia |].
    exact (proj1 (val_mem1_of_aview SEGS (w_H W3) (ms_mem msF) _ 165 (HBLKF (Z.of_nat j) ltac:(lia)))). }
  specialize (HS' HRB ltac:(vm_compute; exact I)). clear HS HRB. rename HS' into HS.
  paj_run_to_shc RUNTOP HS HJF (AF_LLVMFuzzerTestOneInput + SEG_C3_off).
  { intros a (r & Hin & Ha). vm_compute in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
  rename ms into msG, HJF into HJG, HFr into HFrG. clear HF HG.
  assert (KG : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msG) a = aview SEGS (w_H W3) memD a).
  { intros a Ha.
    rewrite (s2u_kept_run _ _ _ _ _ a HFrG Ha ltac:(intros (r & Hr & Ha'); vm_compute in Hr; destruct Hr as [<- | []];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha'; lia)).
    exact (KF a Ha). }
  prreg HS (8%bv : bv 5) G8. prreg HS (9%bv : bv 5) G9. prreg HS (19%bv : bv 5) G19. prreg HS (20%bv : bv 5) G20.
  prreg HS (23%bv : bv 5) G23. prreg HS (24%bv : bv 5) G24. prreg HS (25%bv : bv 5) G25.
  prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4.
  pmkst HS.
  apply (TOC3 ly3 S3 W3 (ms_regs msG) (ms_mem msG) _ HJG eq_refl).
  + intros a Ha Hn. apply KG. lia.
  + intros a Ha Hn. apply KG. destruct Ha as [Ha | Ha]; clear - Ha HF4096 HFceil AC1 HsFlo HsFhi; lia.
  + intros i Hi. apply KG. lia.
  + rewrite G8, (EE 8%nat 8%bv eq_refl). exact Qs0.
  + rewrite G9, (EE 9%nat 9%bv eq_refl). exact Qs1.
  + rewrite G19, (EE 19%nat 19%bv eq_refl). exact Qs3.
  + rewrite G20, (EE 21%nat 21%bv eq_refl). exact Qs5.
  + rewrite G23, (EE 23%nat 23%bv eq_refl). exact Qs7.
  + rewrite G24, (EE 24%nat 24%bv eq_refl). exact Qs8.
  + rewrite G25, (EE 25%nat 25%bv eq_refl). exact Qs9.
  + replace (spZ (ms_regs msG)) with (spZ regs3) by (unfold spZ; rewrite G2, (EE 2%nat 2%bv eq_refl), Qsp; reflexivity).
    exact HSP3.
  + rewrite G3, (EE 3%nat 3%bv eq_refl). exact Qgp.
  + rewrite G4, (EE 4%nat 4%bv eq_refl). exact Qtp.
Qed.
End h.
End d.
