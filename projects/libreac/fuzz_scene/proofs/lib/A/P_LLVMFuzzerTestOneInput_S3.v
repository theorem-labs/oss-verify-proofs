(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S3 of the ASan walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput
   (fuzz_scene.asan, sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026): ONE turn of the
   whole_transfer loop, 0x82dc4 .. 0x82e70 (44 instructions), proved against the cut statements of
   lib/A/P_LLVMFuzzerTestOneInput_seg.v, which this file does not change. *)

(*   The statement proved here is `seg_S3_turn_stmt SEGS B ameter_triv WK scene_geom_asan`: from `cut_T k` at the
   loop head (BASE + AF_LLVMFuzzerTestOneInput + 0x54c) the turn reaches either `cut_T (k+1)` at the same pc, or
   `cut_TX` at the loop exit (BASE + ... + 0x5fc) when k + 1 = 343, so the lane takes the two continuations
   `sc_from_T ... (k+1)` and `sc_from_TX ...` as hypotheses and concludes `sc_from_T ... k`.

   BUILD REQUIREMENT (a Theorem Labs lane's 05:55Z ruling): scene_seg_S3 takes TLF (PALibF B) as an argument, and PALibF is
   dischargeable only over a Theorem Labs lane's ruled lib/{A,AU}/Prog/SceneFrame.v from a working branch 8df4a950395
   (the released lib/A/Prog/SceneFrame.v before its comment pass, file sha256 8c8597ed07af, where palf_sm8 = StackMalloc8Tbl.PC_STACK_MALLOC_8).  Over the frozen
   SceneFrame.v (sha256 fa3ffeab2cf2; internal record) PALibF is unsatisfiable (palf_sm8 demands pa_sigma SS___asan_stack_malloc_8 = 0), so this file must be
   built against the ruled SceneFrame.v.

   The cuts are SEMANTIC (no symbolic state is part of a cut).  The walk is written in the form of a Theorem Labs lane's
   proved check_step segments (a working branch f6b5a0ae303 lib/A/P_check_step_S3.v): each straight
   run starts from a fresh, minimal symbolic state built with `pa_entry_st_ok_full` from the semantic facts that
   hold at its first pc, and what a run or a call leaves is carried as semantic facts (register equations, the
   bytes the run wrote, and "every other byte is kept").

   The turn, by pc offset in LLVMFuzzerTestOneInput (0x82878), as MEASURED on the image
   (my-dis-LLVMF.asan.txt (sha256 4a1063815890; internal record)):
     +0x54c..+0x560  sb zero,4(s3) .. sb a0,8(s3): blk.i's five shadow cells become 00 00 00 00 02;
     +0x564..+0x574  a0 = s9 (blk.i), a1 = [s1+0x58] (body), a2 = s11 (8904), a3 = s6 (k), jal build_scene_step;
     +0x578          bnez a0 -> abort (decided: the contract's accepting post gives a0 = 0);
     +0x57c          bnez s6 -> +0x594 (the k = 0 split);
     +0x580..+0x590  k = 0 only: declared := blk.i[7]<<8 | blk.i[8] = 0x22c8 = 8904, into [s1+0x40];
     +0x594..+0x5a8  n_k := blk.i[4]<<8 | blk.i[5] = scene_len k; s8 := n_k + got; bgeu s8,s2(8905) -> abort
                     (refuted by scT_bnd);
     +0x5ac..+0x5b8  a0 = blk.i, a1 = body, a2 = k, jal check_step;
     +0x5bc..+0x5d4  a1 = blk.i + (k = 0 ? 9 : 7), a0 = again + got, a2 = n_k, jal __asan_memcpy;
     +0x5d8..+0x5ec  the five shadow cells become f8 again; k := k + 1;
     +0x5f0..+0x5f8  got := s8; bne s6,343 -> the loop head, else fall through to +0x5fc.
   Every branch above is either decided by the run or split and refuted here; no other control flow exists in the
   range (PROGFNS.md:154: 44 instructions, no inline ASan check).  *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK0f YN01.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO0b.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00 YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock SceneTM.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import YC1g YC1h YC81 YC4b YC45 YC88 YC85 SceneACjr SceneACja.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_ctx.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_seg.
(* A Theorem Labs lane (at f2a5e8f959d): reac_ctrl_build_scene_step's caller-journal
   contract. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_reac_ctrl_build_scene_step.
(* A Theorem Labs lane (at f6b5a0ae303): check_step's contract, its window, and the frame
   object lemma afobj_of_own. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_check_step_frame P_check_step.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* reac_ctrl_build_scene_step.TAIL_TRAILER, as lib/A/P_LLVMFuzzerTestOneInput.v names it (that file is not
   Required here: it Requires modules this lane does not use).  Same bodies, so the composition's hypotheses
   HB_Z_TT / HB_C_TT are convertible to this file's. *)
Definition A_TAIL_TRAILER : Z := 0x20e20.
Definition TAIL_TRAILER_N : Z := 12.
Definition TT_SHCELLS : list acell :=
z1 (ANum (shadow_addr (A_TAIL_TRAILER + 8))) (TAIL_TRAILER_N mod 8)
:: map (fun k => z1 (ANum (shadow_addr (A_TAIL_TRAILER + 8) + 1 + Z.of_nat k)) 0xf9) (seq 0 2).

(* ---- pure helpers, in the form of a Theorem Labs lane's P_check_step_S3.v ---- *)
Lemma t3_div8_add : forall x c, x mod 8 = 0 -> (x + 8 * c) / 8 = x / 8 + c.
Proof.
intros x c Hx. rewrite (Z.div_mod x 8) at 1 by lia. rewrite Hx, Z.add_0_r.
replace (8 * (x / 8) + 8 * c) with ((x / 8 + c) * 8) by lia. apply Z.div_mul. lia.
Qed.
Lemma t3_ra_part : forall (rd : reader) a q r, a mod 8 = 0 -> 0 <= q -> 0 < r < 8 ->
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
  { rewrite (Z.div_mod a 8) at 1 by lia. rewrite Ha, Z.add_0_r. replace (x - 8 * (a / 8)) with (x + (- (a / 8)) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  pose proof (Z.div_mod (x - a) 8 ltac:(lia)) as Hdm. rewrite Eq in Hdm. lia.
- exists 0. split; [apply H0; lia | left; reflexivity].
Qed.
Lemma t3_eqb_refl : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.
Lemma t3_lb10 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. change (2 ^ 8) with 256.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma t3_bu_range : forall x : byte, 0 <= bv_unsigned x < 256.
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.
(* the two symbolic shapes the turn's byte reads build: zext8 of an atom, and (zext8 hi << 8) | zext8 lo. *)
Lemma t3_U_zext8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> U E (SExt false 8 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt, (U_atom E n v Hn) by lia. cbv beta iota.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma t3_U_or0 : forall E e, U E (SAlu ALU_OR (SLit 0) e) = U E e.
Proof.
intros E e. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0.
rewrite Z.lor_0_l. apply zcanon_id. apply U_range.
Qed.
Lemma t3_U_sll8 : forall E e x, U E e = x -> 0 <= x < 256 -> U E (SAlu ALU_SLL e (SLit 8)) = 256 * x.
Proof.
intros E e x Hx Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
change (Z.land (zcanon 8) 63) with 8. rewrite Hx, Z.shiftl_mul_pow2 by lia.
change (2 ^ 8) with 256. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma t3_U_or_bytes : forall E e1 e2 x y, U E e1 = 256 * x -> U E e2 = y -> 0 <= x < 256 -> 0 <= y < 256 ->
U E (SAlu ALU_OR e1 e2) = 256 * x + y.
Proof.
intros E e1 e2 x y H1 H2 Hx Hy. rewrite U_SAlu. cbn [zalu_raw]. rewrite H1, H2.
change 256 with (2 ^ 8) at 1. rewrite Z.lor_comm, (lor_add_high y x 8) by (cbn; lia).
rewrite zcanon_id by (unfold M64; cbn; lia). cbn. lia.
Qed.

(* the value the turn's `s8 = (0 | zext8 blk.i[5]) + s4` carries: scene_len k + got. *)
Lemma t3_U_s8 : forall E k got, ew E 32 = Z_to_bv 64 (scene_len k) -> ew E 20 = Z_to_bv 64 got ->
0 <= got -> scene_len k + got < 2 ^ 64 -> 0 <= scene_len k < 256 ->
U E (SAlu ALU_ADD (SAlu ALU_OR (SLit 0) (SExt false 8 (SOff 32 0))) (SOff 20 0)) = scene_len k + got.
Proof.
intros E k got H32 H20 Hg Hsum Hlen.
rewrite U_SAlu. cbn [zalu_raw].
rewrite t3_U_or0, (t3_U_zext8 E 32 (scene_len k) H32 Hlen), (U_atom E 20 got H20) by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* gate 6h: the sink head is an explicit Section variable, passed by name at every term that takes one; never an
   instance Coq picks for itself (two global src0_sink_head instances are in this tree's import closure). *)
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
#[local] Notation TPI := (@pl_tpi scene_listing PL_scene).

(* ---- the turn's pcs, as offsets in LLVMFuzzerTestOneInput (AF_LLVMFuzzerTestOneInput = 0) ---- *)
Definition S3_K : Z := AF_LLVMFuzzerTestOneInput + SEG_T_off.        (* +0x54c, the loop head *)
Definition S3_KX : Z := AF_LLVMFuzzerTestOneInput + SEG_TX_off.      (* +0x5fc, the loop exit *)

Lemma t3_kept_run : forall E rs (H : word -> bool) (mA mB : word -> option byte) a,
frame_of E rs (mrestrict H mA) (mrestrict H mB) -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H mB a = aview SEGS H mA a.
Proof. intros E rs H mA mB a HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn. Qed.
Lemma t3_shb : forall E (H : word -> bool) mem n b cs lo hi wlo whi od v,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 (SLit v))) cs -> 0 <= v < 256 ->
aview SEGS H mem (b + od) = Some v.
Proof.
intros E H mem n b cs lo hi wlo whi od v HR Hn Hc Hv.
apply aview_of_val_mem1; [|exact Hv]. exact (field_of_region E _ n b cs lo hi wlo whi od 1 (SLit v) v HR Hn Hc eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma t3_vm1 : forall (H : word -> bool) (m : word -> option byte) a v,
aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof. intros H m a v Hv. exact (proj1 (val_mem1_of_aview SEGS H m a v Hv)). Qed.

Section h.
Variable B : asyms.
Variable WK : swalk.
(* -- framework laws and the glue's instances, as in lib/A/P_LLVMFuzzerTestOneInput.v (its Section h).
   AR_laws is a theorem, not a hypothesis (AR_laws_ok, Reusable/YG0q.v:803; ENTRY-REVIEW.md R4). -- *)
Context {RO : ro_below_ofl (SK := SK) SEGS (@pa_relro_lo _ scene_listing PI_scene) (@pa_relro_hi _ scene_listing PI_scene)}.
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis TL : PALib (L := scene_listing) (PI := PI_scene) B.
Hypothesis TLF : PALibF (L := scene_listing) (PI := PI_scene) B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* -- the walk's budgets, as lib/A/P_LLVMFuzzerTestOneInput.v:187-190 fixes them for the record the composition
   supplies (240 is that file's LLVMF_SPDROP, 6 its LLVMF_EV, 65535 its LLVMF_NMAX) -- *)
Hypothesis HSTK : 240 + ASTACK <= sw_stk WK.
Hypothesis HSTK_CS : 240 + TCHECK_STEP_STK <= sw_stk WK.
Hypothesis HEV : 6 <= sw_ev WK.
Hypothesis HLIVE : 2 * 65535 <= sw_live WK.
(* A Theorem Labs lane's ruling 04:04Z: segment-Section binding beside Variable WK, discharged by the composition by eq_refl; not in
   the statement file and not conditional. *)
Hypothesis HWRLO : sw_rlo WK = @pa_relro_lo _ scene_listing PI_scene.
Hypothesis HWRHI : sw_rhi WK = @pa_relro_hi _ scene_listing PI_scene.
(* -- the static shadow and bytes of reac_ctrl_build_scene_step.TAIL_TRAILER (0x20e20, 12 bytes), which
   build_scene_step's accepting premise names.  HB_Z_TT and HB_C_TT are lib/A/P_LLVMFuzzerTestOneInput.v:265-266
   verbatim.  HRO_TT is the trailer's BYTES in a Theorem Labs lane's ro_bytes form (its HRO_CF for check_step's frame
   initializer): the 12 bytes are read-only, not runtime-owned, not the errno cell, and equal to scene_trailer in
   the image.  A static fact of the image and of B, closed by vm_compute at the composition. -- *)
Hypothesis HB_Z_TT : in_zs B (A_TAIL_TRAILER - 0x20) (0x20 + (TAIL_TRAILER_N - TAIL_TRAILER_N mod 8)).
Hypothesis HB_C_TT : forall ly, Forall (fun c => In c (as_const B ly)) TT_SHCELLS.
(* = entry statement Section h, lib/A/P_LLVMFuzzerTestOneInput.v:202-203 at 327f73c7513 (announced 04:57Z); minimal
   form, no longer conditional.  The in_roP half and the twelve ROM bytes are derived below (t3_tt_bytes), not assumed. *)
Hypothesis HRO_TT : forall i, 0 <= i < 12 -> ~ Exists (in_zr (0x20e20 + i)) (as_owned_static B) /\
~ (as_errno B <= 0x20e20 + i < as_errno B + 4).
(* -- the turn's three callees -- *)
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
Hypothesis BSS : treac_ctrl_build_scene_step_spec (SK := SK) (PI := PI_scene) B.
Hypothesis TCHECKX : tcheck_step_specX (PI := PI_scene) SK B.

Let RUNP := SRr_run_pi_AJ (SK := SK) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (SK := SK) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (SK := SK) B LAWS.
Let BR := paj_branch (PI := PI_scene).

(* ---- the trailer's static facts at any AR state ---- *)
Lemma t3_const1 : forall ly S (W : world SEGS) mem md a v, AR SEGS B ly S W mem md ->
In (z1 (ANum a) v) (as_const B ly) -> aview SEGS (w_H W) mem a = Some (le_byte v 1 0).
Proof.
intros ly S W mem md a v HAR Hin.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ Hin) as X.
unfold cell_holds in X. cbn [c_at YG0f.c_val c_w aeval z1 c1] in X. specialize (X 0%nat ltac:(lia)). rewrite Z.add_0_r in X. exact X.
Qed.
Lemma t3_zs_byte : forall ly S (W : world SEGS) mem md a n x, AR SEGS B ly S W mem md ->
in_zs B a n -> a <= x < a + n -> aview SEGS (w_H W) mem (SHADOW_OFF + x / 8) = Some 0.
Proof.
intros ly S W mem md a n x HAR (q & m & Hin & Hq1 & Hq2) Hx.
destruct (zs_range SEGS B q m Hin ly S W mem md HAR) as (Hq0 & Hm0 & Hq8 & Hm8 & Hhi).
pose proof (zs_zero SEGS B LAWS q m Hin ly S W mem md HAR) as Hz.
assert (Eq8 : q = 8 * (q / 8)) by (pose proof (Z.div_mod q 8 ltac:(lia)); lia).
assert (Em8 : m = 8 * (m / 8)) by (pose proof (Z.div_mod m 8 ltac:(lia)); lia).
assert (Ex : x / 8 = q / 8 + (x - q) / 8).
{ replace x with ((x - q) + (q / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
rewrite Ex, Z.add_assoc. apply Hz. split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; lia.
Qed.
Lemma t3_tt_cells : forall ly,
In (z1 (ANum 0x7fffc1c5) 4) (as_const B ly) /\ In (z1 (ANum 0x7fffc1c6) 0xf9) (as_const B ly) /\
In (z1 (ANum 0x7fffc1c7) 0xf9) (as_const B ly).
Proof.
intros ly. pose proof (HB_C_TT ly) as X.
unfold TT_SHCELLS, A_TAIL_TRAILER, TAIL_TRAILER_N in X. cbn [map seq] in X.
apply Forall_cons_iff in X as (X1 & X). apply Forall_cons_iff in X as (X2 & X). apply Forall_cons_iff in X as (X3 & _).
repeat split.
- exact X1.
- exact X2.
- exact X3.
Qed.
Lemma t3_tt_ra : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF A_TAIL_TRAILER 12.
Proof.
intros ly S W mem md HAR. destruct (t3_tt_cells ly) as (C1 & _ & _).
unfold A_TAIL_TRAILER. change 12 with (8 * 1 + 4).
apply t3_ra_part; [reflexivity | lia | lia | |].
- intros i Hi. assert (i = 0) as -> by lia. rewrite Z.add_0_r.
  exact (t3_zs_byte ly S W mem md _ _ 0x20e20 HAR HB_Z_TT
    ltac:(unfold A_TAIL_TRAILER, TAIL_TRAILER_N; change (12 mod 8) with 4; lia)).
- change (SHADOW_OFF + 0x20e20 / 8 + 1) with 0x7fffc1c5. rewrite (t3_const1 ly S W mem md _ _ HAR C1). reflexivity.
Qed.
Lemma t3_tt_hull : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (aview SEGS (w_H W) mem) A_TAIL_TRAILER 12.
Proof.
intros ly S W mem md HAR s Hs. destruct (t3_tt_cells ly) as (C1 & C2 & C3).
assert (K1 : shadow_addr A_TAIL_TRAILER / 8 * 8 = 0x7fffc1c0) by (vm_compute; reflexivity).
assert (K2 : shadow_addr (A_TAIL_TRAILER + 12 - 1) / 8 * 8 + 8 = 0x7fffc1c8) by (vm_compute; reflexivity).
rewrite K1, K2 in Hs.
assert (Hc : (0x7fffc1c0 <= s < 0x7fffc1c5) \/ s = 0x7fffc1c5 \/ s = 0x7fffc1c6 \/ s = 0x7fffc1c7) by lia.
destruct Hc as [Hc | [-> | [-> | ->]]].
- replace s with (SHADOW_OFF + (0x20e00 + 8 * (s - 0x7fffc1c0)) / 8).
  + rewrite (t3_zs_byte ly S W mem md _ _ (0x20e00 + 8 * (s - 0x7fffc1c0)) HAR HB_Z_TT); [discriminate|].
    unfold A_TAIL_TRAILER, TAIL_TRAILER_N. change (12 mod 8) with 4. lia.
  + rewrite (t3_div8_add 0x20e00 (s - 0x7fffc1c0)) by reflexivity. change (0x20e00 / 8) with 16832.
    unfold SHADOW_OFF. lia.
- rewrite (t3_const1 ly S W mem md _ _ HAR C1). discriminate.
- rewrite (t3_const1 ly S W mem md _ _ HAR C2). discriminate.
- rewrite (t3_const1 ly S W mem md _ _ HAR C3). discriminate.
Qed.
(* the IMAGE half of the trailer, derived (not assumed), in the form of a Theorem Labs lane's s2u_in_ro / s2u_tt
   (at 729b9b9d254, lib/AU/P_LLVMFuzzerTestOneInput_S2.v:258, :283-292): in_roP by an
   existsb over SEGS at one literal address, and each ROM byte by vm_compute, both on the TWELVE concrete i (never
   a forallb / scan over all bytes, which does not terminate on this tree -- measured, a Theorem Labs lane 04:2xZ). *)
Lemma t3_in_ro : forall a,
existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) SEGS = true ->
in_roP SEGS (@pa_relro_lo _ scene_listing PI_scene) (@pa_relro_hi _ scene_listing PI_scene) a.
Proof.
intros a H. apply existsb_exists in H as (s & Hs & Hb). left. exists s. split; [exact Hs|].
apply andb_prop in Hb as (Hb & H3). apply andb_prop in Hb as (H1 & H2).
apply Bool.negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. auto.
Qed.
Lemma t3_tt_bytes : forall (W : world SEGS) mem,
arodata_okP SEGS (@pa_relro_lo _ scene_listing PI_scene) (@pa_relro_hi _ scene_listing PI_scene) B (aview SEGS (w_H W) mem) ->
forall i, 0 <= i < 12 -> aview SEGS (w_H W) mem (A_TAIL_TRAILER + i) = Some (bv_unsigned (nth (Z.to_nat i) scene_trailer (Z_to_bv 8 0))).
Proof.
intros W mem HR i Hi. destruct (HRO_TT i Hi) as (H2 & H3). unfold A_TAIL_TRAILER.
assert (Hro : in_roP SEGS (@pa_relro_lo _ scene_listing PI_scene) (@pa_relro_hi _ scene_listing PI_scene) (0x20e20 + i)).
{ apply t3_in_ro.
  assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]; vm_compute; reflexivity. }
rewrite (HR (0x20e20 + i) Hro H2 H3).
assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11) by lia.
destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]; vm_compute; reflexivity.
Qed.

(* ---- the registers the turn keeps (callee-saved, and untouched by the runs): sp, gp, tp, s0 = entry sp,
   s1 = sp1, s2 = 8905, s3 = shadow(F), s4 = got, s5 = -8, s6 = k, s7 = blk.i + 9, s9 = blk.i, s11 = 8904.
   In the form of a Theorem Labs lane's s3_rk (P_check_step_S3.v). ---- *)
Definition t3_rk (sp0 sp1 gp tp F got k : Z) (r : bvmap 5 word) : Prop :=
  getr r 2 = w64 sp1 /\ getr r 3 = w64 gp /\ getr r 4 = w64 tp /\ getr r 8 = w64 sp0 /\ getr r 9 = w64 sp1 /\
  getr r 18 = w64 8905 /\ getr r 19 = w64 (shadow_addr F) /\ getr r 20 = w64 got /\ getr r 21 = w64 (2 ^ 64 - 8) /\
  getr r 22 = w64 k /\ getr r 23 = w64 (F + 41) /\ getr r 25 = w64 (F + 32) /\ getr r 27 = w64 8904.
Lemma t3_rk_pres : forall sp0 sp1 gp tp F got k (r r' : bvmap 5 word),
  aregs_preserved r r' -> t3_rk sp0 sp1 gp tp F got k r -> t3_rk sp0 sp1 gp tp F got k r'.
Proof.
intros sp0 sp1 gp tp F got k r r' H (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E27).
unfold t3_rk.
repeat split; match goal with |- getr r' ?x = ?v => transitivity (getr r x);
  [let n := eval vm_compute in (bv_unsigned x) in exact (H n ltac:(unfold acallee_saved; lia)) | assumption] end.
Qed.
Lemma t3_rk_kept : forall sp0 sp1 gp tp F got k (r r' : bvmap 5 word),
  (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27]%bv -> getr r' x = getr r x) ->
  t3_rk sp0 sp1 gp tp F got k r -> t3_rk sp0 sp1 gp tp F got k r'.
Proof.
intros sp0 sp1 gp tp F got k r r' H (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E27).
repeat split; (etransitivity; [apply H; cbn; tauto | assumption]).
Qed.

(* ================================================================================================================
   THE CHECK_STEP CALL, as its own state and lemma.  t3_pre_chk is the state at +0x5b8 (S3_K + 108), the `jal
   check_step`: BOTH k arms reach it with these facts, and they differ only in how the declared slot came to hold
   8904.  t3_chk is the call itself: cl_callS (lib/A/Prog/YC85.v:383) with TCHECKX, whose afn_pre premises are
   exactly what t3_pre_chk carries; what it must hand on is the OUTER journal at the cut's budget, the preserved
   registers and the new layout / state / world, from which the caller re-derives its memory facts through the
   journal's own clauses (Reusable/YCbq.v:359-372).
   ================================================================================================================ *)
Definition t3_pre_chk (cx : rtcx SEGS) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (body again : Z) (b : list byte) (k F : Z)
(lyb : alayout) (Sb : astate) (Wb : world SEGS)
(regsX : bvmap 5 word) (memX : word -> option byte) (mdX : Model) : Prop :=
ajournal (SK := SK) SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(8, c_fpos cx)] lyb Sb Wb memX mdX 2 /\
ablocks B lyb Sb = ablocks B ly3 S3 /\ frames Sb = frames S3 /\ blocks_bytes Sb <= blocks_bytes S3 /\
t3_rk (spZ (c_regs cx)) (c_sp1 cx) (as_gp B) (as_tp B) F (scT_off k) k regsX /\
getr regsX 10 = w64 (F + 32) /\ getr regsX 11 = w64 body /\ getr regsX 12 = w64 k /\
getr regsX 1 = w64 (BASE + S3_K + 112) /\
getr regsX 24 = w64 (scene_len k + scT_off k) /\ getr regsX 26 = w64 (scene_len k) /\
(forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ c_sp1 cx <= a) ->
 ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) -> ~ (F + 32 <= a < F + 32 + 34) ->
 ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
 aview SEGS (w_H Wb) memX a = aview SEGS (w_H W3) mem3 a) /\
(forall i, 0 <= i < 34 -> aview SEGS (w_H Wb) memX (F + 32 + i)
 = Some (bv_unsigned (nth (Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))) /\
(forall j, 4 <= j < 9 -> aview SEGS (w_H Wb) memX (shadow_addr F + j) = Some (if j =? 8 then 2 else 0)) /\
rdword (aview SEGS (w_H Wb) memX) (c_sp1 cx + 0x40) = Some 8904 /\
rdword (aview SEGS (w_H Wb) memX) (c_sp1 cx + 0x48) = Some (F + 39) /\
rdword (aview SEGS (w_H Wb) memX) (c_sp1 cx + 0x50) = Some again.

(* the state after check_step returns, at +0x5bc (S3_K + 112): the same facts at the layout, state, world and
   memory check_step left, bridged to the cut's (ly3 S3 W3 mem3).  A Theorem Labs lane proves t3_chk into it; a Theorem Labs lane proves
   t3_cpy from it to t3_post_memcpy. *)
Definition t3_post_chk (cx : rtcx SEGS) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (body again : Z) (b : list byte) (k F : Z)
(ly4 : alayout) (S4 : astate) (W4 : world SEGS)
(regsY : bvmap 5 word) (memY : word -> option byte) (mdY : Model) : Prop :=
ajournal (SK := SK) SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(8, c_fpos cx)] ly4 S4 W4 memY mdY 2 /\
ablocks B ly4 S4 = ablocks B ly3 S3 /\ frames S4 = frames S3 /\ blocks_bytes S4 <= blocks_bytes S3 /\
t3_rk (spZ (c_regs cx)) (c_sp1 cx) (as_gp B) (as_tp B) F (scT_off k) k regsY /\
getr regsY 24 = w64 (scene_len k + scT_off k) /\ getr regsY 26 = w64 (scene_len k) /\
(forall a, 0 <= a < 2 ^ 64 -> (c_sp1 cx <= a \/ in_frames ly3 (frames S3) a \/ (exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= a < p + req_size n) \/ (in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))) ->
 ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) -> ~ (F + 32 <= a < F + 32 + 34) ->
 ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
 aview SEGS (w_H W4) memY a = aview SEGS (w_H W3) mem3 a) /\
(forall i, 0 <= i < 34 -> aview SEGS (w_H W4) memY (F + 32 + i)
 = Some (bv_unsigned (nth (Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))) /\
(forall j, 4 <= j < 9 -> aview SEGS (w_H W4) memY (shadow_addr F + j) = Some (if j =? 8 then 2 else 0)) /\
rdword (aview SEGS (w_H W4) memY) (c_sp1 cx + 0x40) = Some 8904 /\
rdword (aview SEGS (w_H W4) memY) (c_sp1 cx + 0x48) = Some (F + 39) /\
rdword (aview SEGS (w_H W4) memY) (c_sp1 cx + 0x50) = Some again.

Lemma t3_chk : forall (cx : rtcx SEGS) POST k ly3 S3 W3 regs3 mem3 md3 bs body again b lyb Sb Wb regsX memX mdX,
sc_base SEGS B ameter_triv WK cx -> 0 <= k < sg_nturns scene_geom_asan ->
cut_T (SK := SK) SEGS B ameter_triv WK scene_geom_asan cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
t3_pre_chk cx ly3 S3 W3 mem3 body again b k (sc_F SEGS scene_geom_asan cx) lyb Sb Wb regsX memX mdX ->
(forall ly4 S4 W4 regsY memY mdY,
 t3_post_chk cx ly3 S3 W3 mem3 body again b k (sc_F SEGS scene_geom_asan cx) ly4 S4 W4 regsY memY mdY ->
 SRr SEGS W4 (mkCfg (mkst regsY (Z_to_bv 64 (BASE + (S3_K + 112))) memY (seg_rom SEGS)) mdY) POST) ->
SRr SEGS Wb (mkCfg (mkst regsX (Z_to_bv 64 (SIGMA SS_check_step)) memX (seg_rom SEGS)) mdX) POST.
Proof.
intros cx POST k ly3 S3 W3 regs3 mem3 md3 bs body again b lyb Sb Wb regsX memX mdX HB Hk HC Hpre HK.
(* ---------------- the entry (as scene_seg_S3, S3.v:475-477 at 1e5c1c2be13) ---------------- *)
pose proof HB as (HB0 & Hsp1eq).
pose proof HB0 as (HPRE & Hra0 & Hp10 & Hp11 & Hin0 & HfrS & Hnev0 & Hbb0 & HRO0 & Hsink0 & Hfd0 & Hfs0 & Hmo0).
pose proof HPRE as (HAR0 & Hrok0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & Hqt0).
(* ---------------- the cut (S3.v:479-492) ---------------- *)
pose proof HC as HCd.
unfold cut_T, sc_frame, sc_shr, sc_shbg, sc_open in HCd.
remember (sc_F SEGS scene_geom_asan cx) as F eqn:HFdef in *.
cbn [vat scene_geom_asan sgT_sp0 sgT_sp1 sgT_Fsp sgT_shF sgT_blki sgT_srcA sgT_srcB sgT_mac sgT_shexp
sgT_body sgT_again sgT_nprime sgT_got sgT_k sgT_decl sgT_n1 sgT_extra sgT_nagain sgT_expect sgT_Fb
sgT_nn sgT_body2 sgT_f8 sg_cid sg_off_blki sg_off_mac sg_off_expect sg_scene_n sg_nturns sg_sh_bg
sg_sh_blki_lo sg_sh_blki_hi sg_off_blk sg_blk_n sg_mac_n
RV_s0 RV_s1 RV_s2 RV_s3 RV_s4 RV_s5 RV_s6 RV_s7 RV_s8 RV_s9 RV_s10 RV_s11 fst snd] in HCd.
destruct HCd as (Hk0 & Hwhole & HJj & Habl & Hbbs & HBOK & HAOK & Hsepba & Hblen & Hgbody & Hja &
HFR & HSV & HSBG & HSHB & HOPB & HOPM & HIMG & HIN & HMAC &
Rsp0 & Rsp1 & Qfsp & Rsh & Rblki & Qsrca & Rsrcb & Qmac & Qshexp & Qbody & Qagain & Qnprime &
Rgot & Rk & Qdecl & Rn1 & Hextra & Hnag & Qexpect & Qfb & Qnn & Hbody2 & Rf8).
pose proof HJj as (HJ & HfrS3 & Hmole).
pose proof HJ as (HAR3 & HLY3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresS & HstkS & _).
pose proof HstkS as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 HLY3) as (Eab & EFA & Eown).
assert (HinF : In (8, c_fpos cx) (frames S3)) by (rewrite HfrS3; left; reflexivity).
assert (EFAF : frame_addr ly3 8 (c_fpos cx) = F)
by (rewrite HFdef; unfold sc_F, rt_F; cbn [sg_cid scene_geom_asan]; apply EFA).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 HinF) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 HinF) as (HF32 & _ & HFpres & HFSpres).
rewrite EFAF in HF4096, HFceil, HFapp, HF32.
change (fs_frame_bytes 8) with 16384 in HF4096, HFceil, HFapp.
pose proof (@YM05.alloc_ceiling_value rc) as Hacv.
assert (HF8 : F mod 8 = 0) by (pose proof (Z.div_mod F 32 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
assert (HFdiv : 0 <= F / 8 <= F) by (split; [apply Z.div_pos; lia | pose proof (Z.mul_div_le F 8 ltac:(lia)); lia]).
assert (Hac8 : 8 * (alloc_ceiling / 8) <= alloc_ceiling) by (apply Z.mul_div_le; lia).
assert (HFdiv3 : F / 8 + 2048 <= alloc_ceiling / 8)
  by (rewrite <- (t3_div8_add F 2048) by exact HF8; apply Z.div_le_mono; lia).
assert (HshLT : shadow_addr F + 2048 <= alloc_ceiling) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (HshLO : 2147450880 <= shadow_addr F) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (Hsp1lo : spZ (c_regs cx) - 240 <= c_sp1 cx <= spZ (c_regs cx) - 224).
{ rewrite Hsp1eq. pose proof (sp1_facts (spZ (c_regs cx) - 224)) as X.
  destruct X as (X1 & _ & _); [lia | rewrite Zminus_mod, Hsp0al; reflexivity | lia]. }
assert (Hsp1_32 : c_sp1 cx mod 32 = 0) by (rewrite Hsp1eq, Z.mul_comm; apply Z_mod_mult).
assert (Hsp1al : c_sp1 cx mod 16 = 0).
{ rewrite Hsp1eq. pose proof (sp1_facts (spZ (c_regs cx) - 224)) as X.
  destruct X as (_ & _ & X3); [lia | rewrite Zminus_mod, Hsp0al; reflexivity | exact X3]. }
assert (Ho16 : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0) by (rewrite Zminus_mod, Hsp1al, Hsp0al; reflexivity).
assert (Esh : forall i, SHADOW_OFF + (F + 32) / 8 + i = shadow_addr F + (4 + i)).
{ intros i. unfold shadow_addr. replace (F + 32) with (F + 8 * 4) by lia. rewrite t3_div8_add by exact HF8. lia. }
assert (HkR : 0 <= k <= 342) by (cbn [sg_nturns scene_geom_asan] in Hk; lia).
pose proof HBOK as (Hb4096 & Hbz & Hbceil & Hb16 & _ & _).
change (req_size 8904) with 8904 in Hbceil, Hbbs.
assert (HbodyIn : In (body, 8904) (ablocks B ly3 S3))
  by (rewrite Habl; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (U8s : forall j, nth j (u8s b) 0 = bv_unsigned (nth j b (Z_to_bv 8 0))).
{ intros j. unfold u8s. rewrite <- (map_nth (fun x : byte => bv_unsigned x) b (Z_to_bv 8 0) j). reflexivity. }
assert (FFS : TCHECK_STEP_STK = 8496) by reflexivity.
assert (ES3K : S3_K = 1356) by (unfold S3_K; reflexivity).
pose proof (@pa_base_lo _ scene_listing PL_scene PI_scene) as HBlo.
pose proof (@pa_B_ok _ scene_listing PI_scene) as (HBA0 & HBA1 & _).
(* ---------------- the call state (t3_pre_chk) ---------------- *)
destruct Hpre as (HJb & Eabb & Efrb & Ebbb & RKX & Xa0 & Xa1 & Xa2 & Xra & Xs8 & Xs10 & KX & XBLK & XSH &
Xdecl & Xsrc & Xagain).
pose proof RKX as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X25 & X27).
pose proof HJb as (HARb & HLYb & _ & _ & _ & Hfrsb & Hnevb & _ & HKb & _).
pose proof HLYb as (_ & _ & _ & _ & _ & HFb & _ & _ & Etopb & _).
assert (EFAFb : frame_addr lyb 8 (c_fpos cx) = F).
{ rewrite HFdef. unfold sc_F, rt_F, frame_addr. cbn [sg_cid scene_geom_asan]. rewrite HFb. reflexivity. }
assert (EspX : spZ regsX = c_sp1 cx) by (unfold spZ; rewrite X2; unfold w64; apply unsigned_lit_small; lia).
assert (Es0X : s0Z regsX = spZ (c_regs cx)) by (unfold s0Z; rewrite X8; unfold w64; apply unsigned_lit_small; lia).
assert (Hret : YK0s.ret_ok (getr regsX 1)).
{ rewrite Xra, ES3K. unfold w64. replace (BASE + 1356 + 112) with (BASE + 1468) by lia.
  apply ret_ok_codeptr_v; [lia | reflexivity]. }
assert (Hra4 : 4096 <= raZ regsX).
{ unfold raZ. rewrite Xra, ES3K. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* the 13 saved words of the entry's caller, at the call state (KX: they lie above sp1) *)
assert (HSVb : forall j, 0 <= j < 13 -> rdword (aview SEGS (w_H Wb) memX) (spZ (c_regs cx) - 8 - 8 * j)
  = Some (bv_unsigned (getr (c_regs cx) (nth (Z.to_nat j) sc_saved_regs 0%bv)))).
{ intros j Hj. rewrite <- (HSV j Hj). apply rdword_ext. intros i Hi. apply KX; lia. }
(* ---------------- check_step's premises (a Theorem Labs lane's s3_chk_pre, 67cd72b99e4 AU S3.v:1781-1840) ---------------- *)
assert (Hch : exists ch, achain lyb (aview SEGS (w_H Wb) memX) (spZ regsX) (s0Z regsX) ch).
{ rewrite EspX, Es0X.
  destruct (Z.ltb_spec (spZ (c_regs cx)) (ly_top (c_ly cx) - 16)) as [Hlo16 | Hhi16].
  - exists [(spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx))].
    apply (achain_ly_top (c_ly cx) lyb); [exact Etopb|].
    apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) (aview SEGS (w_H Wb) memX)
      (spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] (c_sp1 cx) Hch0).
    + lia.
    + intros a Ha. apply HKb; lia.
    + replace (spZ (c_regs cx) - 8) with (spZ (c_regs cx) - 8 - 8 * 0) by lia. exact (HSVb 0 ltac:(lia)).
    + replace (spZ (c_regs cx) - 16) with (spZ (c_regs cx) - 8 - 8 * 1) by lia. exact (HSVb 1 ltac:(lia)).
    + exact Hra40.
    + lia.
    + apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hsp0al; [|lia]. destruct Hsp0al as [u Hu].
      exists (2 * u). lia.
    + exact Hlo16.
    + lia.
  - exists []. left. split; [right; left; rewrite Etopb; lia | reflexivity]. }
destruct Hch as (ch & Hch).
assert (HPREb : afn_pre SEGS B TCHECK_STEP_STK lyb Sb Wb regsX memX mdX ch).
{ eapply (afn_pre_at (SK := SK) SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(8, c_fpos cx)] lyb Sb Wb memX mdX 2 regsX TCHECK_STEP_STK (c_sp1 cx - spZ (c_regs cx)) ch HJb).
  - rewrite EspX. lia.
  - exact Ho16.
  - lia.
  - lia.
  - lia.
  - exact Hret.
  - exact Hra4.
  - exact X3.
  - exact X4.
  - exact Hch. }
assert (HRO0P : arodata_okP SEGS (@pa_relro_lo _ scene_listing PI_scene) (@pa_relro_hi _ scene_listing PI_scene) B
  (aview SEGS (w_H (c_W cx)) (c_mem cx))) by (rewrite <- HWRLO, <- HWRHI; exact HRO0).
pose proof (arodata_ok_journalP (SK := SK) SEGS _ _ pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJb HRO0P) as HRODb.
assert (P7 : afobj SEGS B lyb Sb Wb memX (F + 32) CS_BLK_LEN).
{ unfold afobj, CS_BLK_LEN. split; [|split].
  - exists 8, (c_fpos cx). split; [rewrite Efrb, HfrS3; left; reflexivity|]. split; [lia|]. rewrite EFAFb.
    split; [exact HF8|]. split; [lia|]. change (fs_frame_bytes 8) with 16384. lia.
  - rewrite Z.add_mod, HF8 by lia. reflexivity.
  - change 34 with (8 * 4 + 2). apply t3_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
    + intros i Hi. rewrite Esh, XSH by lia. destruct (Z.eqb_spec (4 + i) 8); [lia | reflexivity].
    + rewrite Esh, XSH by lia. reflexivity. }
assert (P10 : forall i, 0 <= i < CS_BODY_LEN ->
  aview SEGS (w_H Wb) memX (body + i) = Some (bv_unsigned (nth (Z.to_nat i) b (Z_to_bv 8 0)))).
{ intros i Hi. unfold CS_BODY_LEN in Hi.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 body 8904 8 (c_fpos cx) HAR3 HbodyIn HinF) as Hsep.
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite EFAF in Hsep.
  change (req_size 8904) with 8904 in Hsep. change (fs_frame_bytes 8) with 16384 in Hsep.
  rewrite KX.
  - destruct (Hgbody (Z.to_nat i) ltac:(unfold u8s; rewrite length_map; lia)) as (Hv & Hr).
    rewrite Z2Nat.id in Hv by lia. rewrite (aview_of_val_mem1 SEGS _ _ _ _ Hv Hr). rewrite U8s. reflexivity.
  - lia.
  - left. lia.
  - lia.
  - lia.
  - unfold zone2, off_img in Hbz. change (req_size 8904) with 8904 in Hbz.
    unfold shadow_addr, SHADOW_OFF in *. lia. }
(* ---------------- the call (a Theorem Labs lane's s3m_call, AU S3.v:2473-2495) ---------------- *)
rewrite pa_sigma_check_step.
eapply SRr_bind.
{ exact (TCHECKX lyb Sb Wb regsX memX mdX ch (F + 32) body k b HPREb
    ltac:(rewrite EspX; exact Hsp1_32) ltac:(rewrite EspX, Etopb; lia)
    ltac:(rewrite Efrb, HfrS3; cbn [length]; lia) HRODb
    Xa0 Xa1 Xa2 ltac:(unfold CS_LAST; lia) P7
    ltac:(rewrite Eabb, Habl; unfold CS_BODY_LEN; apply in_or_app; left; apply in_or_app; right; left; reflexivity)
    ltac:(unfold CS_BODY_LEN; apply Nat2Z.inj; rewrite Hblen; reflexivity)
    P10 XBLK
    ltac:(unfold EV_CHECK_STEP; lia) ltac:(unfold LIVE_CHECK_STEP; lia)). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJi & HP & HQ2).
cbv beta in HQ2.
rewrite Xra.
replace (w64 (BASE + S3_K + 112)) with (Z_to_bv 64 (BASE + (S3_K + 112))) by (unfold w64; f_equal; lia).
apply (HK ly2 S2 W2 regs2 mem2 md2).
pose proof (ajournal_sub (SK := SK) SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  _ _ _ _ _ _ _ _ _ _ HJb HJi ltac:(rewrite EspX, FFS; lia) ltac:(rewrite EspX; lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJc.
rewrite EspX in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & Hfr2 & _ & _ & G1 & G2 & G3 & G4 & _).
(* the callee keeps, across its journal: at or above sp1, the caller's frame and its shadow, the live blocks and
   the non-owned image bytes (a Theorem Labs lane's s3m_mid_j, AU S3.v:2376-2395) *)
assert (KH : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wb) memX a)
  by (intros a Ha0; apply G1; lia).
assert (KF : forall a, in_zr a (F, 16384) \/ in_zr a (shadow_addr F, 2048) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wb) memX a).
{ intros a Ha0. apply (G4 8 (c_fpos cx) a); [rewrite Efrb, HfrS3; left; reflexivity | | apply inFP_nil].
  unfold frame_rng. cbn [fst snd]. rewrite EFAFb. change (fs_frame_bytes 8) with 16384.
  change (16384 / 8) with 2048. exact Ha0. }
unfold t3_post_chk.
split; [exact HJc|].
split; [rewrite HQ2; exact Eabb|].
split; [rewrite Hfr2; exact Efrb|].
split; [rewrite (blocks_bytes_bsum B ly2 S2), HQ2, <- (blocks_bytes_bsum B lyb Sb); exact Ebbb|].
split; [exact (t3_rk_pres _ _ _ _ _ _ _ regsX regs2 HP RKX)|].
split.
{ assert (E24 : getr regs2 24 = getr regsX 24) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
  rewrite E24. exact Xs8. }
split.
{ assert (E26 : getr regs2 26 = getr regsX 26) by exact (HP 26 ltac:(unfold acallee_saved; lia)).
  rewrite E26. exact Xs10. }
split.
{ intros a Ha Hcls Hn1 Hn2 Hn3.
  assert (Hlh : (a < alloc_ceiling \/ c_sp1 cx <= a) /\ aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wb) memX a).
  { destruct Hcls as [Hhi | [Hfr | [Hbl | Him]]].
    - split; [right; exact Hhi | apply KH; lia].
    - unfold in_frames in Hfr. destruct Hfr as (cid & pos & Hin & Hr). rewrite HfrS3 in Hin. destruct Hin as [Ecp | []].
      injection Ecp as <- <-.
      assert (Hr' : in_zr a (F, 16384) \/ in_zr a (shadow_addr F, 2048)) by (rewrite <- EFAF; exact Hr).
      clear Hr. rename Hr' into Hr.
      split; [|apply KF; exact Hr].
      left. unfold in_zr in Hr. cbn [fst snd] in Hr. lia.
    - destruct Hbl as (p & n & Hp & Hpa).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR3 Hp) as (_ & _ & Hpc & _).
      split; [left; lia|].
      replace a with (p + (a - p)) by lia.
      apply (G2 p n (a - p)); [rewrite Eabb; exact Hp | rewrite HQ2, Eabb; exact Hp | lia | apply inFP_nil].
    - destruct Him as (Himg & Ho & He).
      pose proof (pa_segs_low a Himg) as Hl. unfold kLowMemEnd in Hl.
      split; [left; lia|].
      apply (G3 a Himg Ho He). apply fp_spares_closed, sink_closed_nil. }
  destruct Hlh as (Hlh & E2).
  rewrite E2. exact (KX a Ha Hlh Hn1 Hn2 Hn3). }
split.
{ intros i Hi. rewrite <- (XBLK i Hi). apply KF. left. unfold in_zr. cbn [fst snd]. lia. }
split.
{ intros j Hj. rewrite <- (XSH j Hj). apply KF. right. unfold in_zr. cbn [fst snd]. lia. }
split; [rewrite <- Xdecl; apply rdword_ext; intros i Hi; apply KH; lia|].
split; [rewrite <- Xsrc; apply rdword_ext; intros i Hi; apply KH; lia|].
rewrite <- Xagain; apply rdword_ext; intros i Hi; apply KH; lia.
Qed.

(* ================================================================================================================
   THE LAST PIECE OF THE TURN, as its own state and lemma, so it can be proved apart from the walk above.
   t3_post_memcpy is the state at +0x5d8 (S3_K + 140), the instruction __asan_memcpy returns to: blk.i's five
   shadow cells still read 00 00 00 00 02, `again` already holds the k-th piece, and s4 / s6 still carry the OLD
   got and k (the turn increments k at +0x5e8 and moves got at +0x5f0).  t3_close runs the nine instructions that
   are left, 0x82e50 .. 0x82e70 (sb s5,4(s3); sb s5,5(s3); sb s5,6(s3); sb s5,7(s3); addiw s6,s6,1; sb s5,8(s3);
   mv s4,s8; addi a0,zero,0x157; bne s6,a0) and rebuilds cut_T at k + 1, or cut_TX when
   k + 1 = 343, and applies the lane's two continuations.  Its world (ly5 S5 W5) is the one __asan_memcpy left,
   bridged to the cut's (ly3 S3 W3 mem3).
   ================================================================================================================ *)
Definition t3_post_memcpy (cx : rtcx SEGS) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(mem3 : word -> option byte) (body again : Z) (b : list byte) (k F : Z)
(ly5 : alayout) (S5 : astate) (W5 : world SEGS)
(regsD : bvmap 5 word) (memD : word -> option byte) (mdD : Model) : Prop :=
(* the caller journal of the whole turn so far, at the cut's own event budget (every callee of the turn adds 0) *)
ajournal (SK := SK) SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(8, c_fpos cx)] ly5 S5 W5 memD mdD 2 /\
ablocks B ly5 S5 = ablocks B ly3 S3 /\ frames S5 = frames S3 /\ blocks_bytes S5 <= blocks_bytes S3 /\
(* the registers the turn keeps, still at the OLD got and k *)
t3_rk (spZ (c_regs cx)) (c_sp1 cx) (as_gp B) (as_tp B) F (scT_off k) k regsD /\
getr regsD 24 = w64 (scene_len k + scT_off k) /\ getr regsD 26 = w64 (scene_len k) /\
(* every byte the turn did not write is the byte the cut had *)
(forall a, 0 <= a < 2 ^ 64 -> (c_sp1 cx <= a \/ in_frames ly3 (frames S3) a \/ (exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= a < p + req_size n) \/ (in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))) ->
 ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) -> ~ (F + 32 <= a < F + 32 + 34) ->
 ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
 ~ (again + scT_off k <= a < again + scT_off k + scene_len k) ->
 aview SEGS (w_H W5) memD a = aview SEGS (w_H W3) mem3 a) /\
(* blk.i, as reac_ctrl_build_scene_step left it *)
(forall i, 0 <= i < 34 -> aview SEGS (w_H W5) memD (F + 32 + i)
 = Some (bv_unsigned (nth (Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))) /\
(* blk.i's five shadow cells, still unpoisoned *)
(forall j, 4 <= j < 9 -> aview SEGS (w_H W5) memD (shadow_addr F + j) = Some (if j =? 8 then 2 else 0)) /\
(* the spill slots the turn wrote or needs: declared, blk.i + 7, again *)
rdword (aview SEGS (w_H W5) memD) (c_sp1 cx + 0x40) = Some 8904 /\
rdword (aview SEGS (w_H W5) memD) (c_sp1 cx + 0x48) = Some (F + 39) /\
rdword (aview SEGS (w_H W5) memD) (c_sp1 cx + 0x50) = Some again /\
(* what __asan_memcpy wrote: the k-th piece of b, at again + got *)
(forall i, 0 <= i < scene_len k -> aview SEGS (w_H W5) memD (again + scT_off k + i)
 = Some (bv_unsigned (nth (Z.to_nat (if k =? 0 then 9 else 7) + Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))).

(* ================================================================================================================
   THE STEP KIT, copied verbatim (names prefixed t3c_) from a Theorem Labs lane's proved segment S4,
   at 2172fd006fcdec4e76fd263628b4680caf80c583,
   lib/A/P_LLVMFuzzerTestOneInput_S4.v: one concrete machine step per instruction form, through
   SRr_step (Reusable/YA0n.v:133) and the YK11 / YK14 step lemmas, with the instruction word taken from the
   position-abstract listing by ScenePaLib.pa_fetch_pw.  Each lemma takes the RAW decoded fields and an
   equation to the named register / immediate, because decode_any's fields carry the opaque proof
   Z_to_bv_obligation_1 and can never be matched against a literal.
   ================================================================================================================ *)
Lemma t3c_fetch : forall k w, plookup TPI k = Some (PW w) ->
fetch_word SEGS (Z_to_bv 64 (BASE + k)) = Some (Z_to_bv 32 w).
Proof. intros k w H. exact (pa_fetch_pw k w H). Qed.

Lemma t3c_unrestrict_mkst : forall (H : word -> bool) full regs pc m rom,
unrestrict H full (mkst regs pc m rom) = mkst regs pc (munrestrict H full m) rom.
Proof. intros. unfold unrestrict, mkst. cbn. reflexivity. Qed.

(* One machine step whose result is again a (regs, pc, mem) triple with the same memory. *)
Lemma t3c_reg : forall (W : world SEGS) regs k mem md regs' k' Q,
RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (seg_rom SEGS))
= MachineOk (mkst regs' (Z_to_bv 64 (BASE + k')) (mrestrict (w_H W) mem) (seg_rom SEGS)) ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + k')) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md regs' k' Q Hs HK.
eapply (SRr_step SEGS pa_wx W (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 (BASE + k')) (mrestrict (w_H W) mem) (seg_rom SEGS)) md Q).
- reflexivity.
- rewrite restrict_mkst_fx. exact Hs.
- intros md' Hm. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict. exact (HK md' Hm).
Qed.


(* One machine step whose result is again a (regs, pc, mem) triple with the same memory. *)
Lemma t3c_step_at : forall (W : world SEGS) regs k mem md regs' pc' Q,
RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (seg_rom SEGS))
= MachineOk (mkst regs' pc' (mrestrict (w_H W) mem) (seg_rom SEGS)) ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs' pc' mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md regs' pc' Q Hs HK.
eapply (SRr_step SEGS pa_wx W (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS))
(mkst regs' pc' (mrestrict (w_H W) mem) (seg_rom SEGS)) md Q).
- reflexivity.
- rewrite restrict_mkst_fx. exact Hs.
- intros md' Hm. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict. exact (HK md' Hm).
Qed.

Lemma t3c_pc4 : forall k, v_addi (Z_to_bv 64 (BASE + k)) 4 = Z_to_bv 64 (BASE + (k + 4)).
Proof. intros k. rewrite YCbn.v_addi_lit. f_equal. lia. Qed.

Lemma t3c_opimm : forall (W : world SEGS) regs k mem md Q w op rd rs (imm : bv 12) v,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (OpImm op rd rs imm, 4%Z) -> bv_eqb rd 0 = false ->
alu64 op (getr regs rs) (sext 64 imm) = v ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst (regupd regs rd v) (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w op rd rs imm v Hpl He Hd Hrd Hv HK.
eapply t3c_reg; [|exact HK].
rewrite (step_opimm_gen SEGS regs _ _ _ (Z_to_bv 32 w) op rd rs imm (t3c_fetch k w Hpl) He Hd).
rewrite Hrd, Hv, t3c_pc4. reflexivity.
Qed.

Lemma t3c_mv : forall (W : world SEGS) regs k mem md Q w rd0 rs0 (imm : bv 12) rd rs zi v,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd0 rs0 imm, 4%Z) ->
rd0 = rd -> rs0 = rs -> bv_signed imm = zi -> bv_eqb rd 0 = false ->
v_addi (getr regs rs) zi = v ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst (regupd regs rd v) (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w rd0 rs0 imm rd rs zi v Hpl He Hd Erd Ers Ezi Hrd Hv HK.
subst rd0 rs0 zi.
eapply t3c_reg; [|exact HK].
rewrite (step_addi SEGS regs _ _ _ (Z_to_bv 32 w) rd rs imm (t3c_fetch k w Hpl) He Hd).
rewrite Hrd, Hv, t3c_pc4. reflexivity.
Qed.

Lemma t3c_add : forall (W : world SEGS) regs k mem md Q w rd0 rs10 rs20 rd rs1 rs2 v,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Op ALU_ADD rd0 rs10 rs20, 4%Z) ->
rd0 = rd -> rs10 = rs1 -> rs20 = rs2 -> bv_eqb rd 0 = false ->
v_add (getr regs rs1) (getr regs rs2) = v ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst (regupd regs rd v) (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w rd0 rs10 rs20 rd rs1 rs2 v Hpl He Hd Erd Er1 Er2 Hrd Hv HK.
subst rd0 rs10 rs20.
eapply t3c_reg; [|exact HK].
rewrite (step_add SEGS regs _ _ _ (Z_to_bv 32 w) rd rs1 rs2 (t3c_fetch k w Hpl) He Hd).
rewrite Hrd, Hv, t3c_pc4. reflexivity.
Qed.
Lemma t3c_branch : forall (W : world SEGS) regs k mem md Q w c rs1 rs2 (imm : bv 13),
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Branch c rs1 rs2 imm, 4%Z) ->
(branch_taken c (getr regs rs1) (getr regs rs2) = true -> forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (k + bv_signed imm))) mem (seg_rom SEGS)) md') Q) ->
(branch_taken c (getr regs rs1) (getr regs rs2) = false -> forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w c rs1 rs2 imm Hpl He Hd HT HF.
destruct (branch_taken c (getr regs rs1) (getr regs rs2)) eqn:Hb.
- eapply t3c_reg; [|exact (HT eq_refl)].
rewrite (step_branch_tk_gen SEGS regs _ _ _ (Z_to_bv 32 w) c rs1 rs2 imm (t3c_fetch k w Hpl) He Hd Hb).
unfold btgt. rewrite YCbn.v_addi_lit.
replace (BASE + k + bv_signed imm) with (BASE + (k + bv_signed imm)) by lia. reflexivity.
- eapply t3c_reg; [|exact (HF eq_refl)].
rewrite (step_branch_ft_gen SEGS regs _ _ _ (Z_to_bv 32 w) c rs1 rs2 imm (t3c_fetch k w Hpl) He Hd Hb).
rewrite t3c_pc4. reflexivity.
Qed.

Lemma t3c_branch_off : forall (W : world SEGS) regs k mem md Q w c r1 r2 (imm : bv 13) rs1 rs2 off,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Branch c r1 r2 imm, 4%Z) ->
r1 = rs1 -> r2 = rs2 -> bv_signed imm = off ->
(branch_taken c (getr regs rs1) (getr regs rs2) = true -> forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (k + off))) mem (seg_rom SEGS)) md') Q) ->
(branch_taken c (getr regs rs1) (getr regs rs2) = false -> forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w c r1 r2 imm rs1 rs2 off Hpl He Hd E1 E2 Hoff HT HF.
subst r1 r2.
apply (t3c_branch W regs k mem md Q w c rs1 rs2 imm Hpl He Hd); rewrite ?Hoff; assumption.
Qed.

Lemma t3c_ld : forall (W : world SEGS) regs k mem md Q w rd0 rs0 (imm : bv 12) rd rs zi a v,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd0 rs0 imm, 4%Z) ->
rd0 = rd -> rs0 = rs -> bv_signed imm = zi -> bv_eqb rd 0 = false ->
bv_unsigned (getr regs rs) + zi = a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
rdword (aview SEGS (w_H W) mem) a = Some v ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst (regupd regs rd (Z_to_bv 64 v)) (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w rd0 rs0 imm rd rs zi a v Hpl He Hd Erd Ers Ezi Hrd Ha Ha0 Ha8 Hrw HK.
subst rd0 rs0 zi.
pose proof (val_mem_of_rdword SEGS (w_H W) mem a v Hrw) as Hv.
destruct (word_mem_ld SEGS (mrestrict (w_H W) mem) a v Hv Ha0 Ha8) as (bs & Hbs & Hval).
eapply t3c_reg; [|exact HK].
rewrite (step_ld SEGS regs _ _ _ (Z_to_bv 32 w) rd rs imm bs (Z_to_bv 64 v) (t3c_fetch k w Hpl) He Hd
ltac:(unfold v_addi; rewrite Ha; exact Hbs) Hval).
rewrite Hrd, t3c_pc4. reflexivity.
Qed.

Lemma t3c_call : forall (W : world SEGS) regs k mem md Q s (rd : bv 5),
plookup TPI k = Some (PCall s rd) ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst (regupd regs rd (Z_to_bv 64 (BASE + (k + 4)))) (Z_to_bv 64 (SIGMA s))
mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q s rd Hpl HK.
rewrite <- (@pl_tpi_eq scene_listing PL_scene) in Hpl.
pose proof (cert_slot ssym (clookup (@pa_tbl _ scene_listing PI_scene))
(@pa_val _ scene_listing PI_scene) (@pa_sigma _ scene_listing PI_scene) scene_listing
(@pa_cert _ scene_listing PI_scene) k (PCall s rd) Hpl) as (Hck & Hk0 & Hk4).
unfold pi_slot_check in Hck.
destruct (clookup (@pa_tbl _ scene_listing PI_scene) (BASE + k)) as [wz|] eqn:Hf; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as (Hsz & Hck).
destruct i; try discriminate Hck.
apply andb_prop in Hck as (Hck & Htgt). apply andb_prop in Hck as (Hrdeq & Hrd0).
apply Z.eqb_eq in Hsz. apply Z.eqb_eq in Htgt.
apply reg_eqb_eq in Hrdeq. apply Bool.negb_true_iff in Hrd0. subst.
eapply t3c_step_at; [|exact HK].
rewrite (step_jal_link SEGS regs _ _ _ (Z_to_bv 32 wz) _ _
(pa_fetch_ok _ _ Hf) ltac:(eapply not_ecall_of_decode; [exact Hdec | discriminate]) Hdec).
assert (E0 : (0%bv : bv 5) = Z_to_bv 5 0) by (apply bv_eq; reflexivity).
rewrite E0, Hrd0. unfold btgt. rewrite !YCbn.v_addi_lit.
replace (BASE + k + 4) with (BASE + (k + 4)) by lia.
f_equal. f_equal. apply zv_zcanon_eq. rewrite <- Htgt. unfold zcanon, M64.
symmetry. apply Z.mod_mod. lia.
Qed.

Lemma t3c_bv_small : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Hz.
Qed.

Lemma t3c_base_lo : 0x10000 <= BASE /\ 0 <= BASE /\ BASE + 2 ^ 40 < 2 ^ 64 /\ BASE mod 4 = 0.
Proof.
pose proof (@pa_base_lo _ scene_listing PL_scene PI_scene) as H1.
pose proof (@pa_B_ok _ scene_listing PI_scene) as (H2 & H3 & H4). auto.
Qed.

Lemma t3c_ret : forall k, 0 <= k < 2 ^ 40 -> k mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 (BASE + k)).
Proof. intros k H1 H2. exact (ret_ok_codeptr_v k H1 H2). Qed.

Lemma t3c_ra4096 : forall k, 0 <= k < 2 ^ 40 -> 4096 <= bv_unsigned (Z_to_bv 64 (BASE + k)).
Proof.
intros k Hk. pose proof t3c_base_lo as (Hb1 & Hb2 & Hb3 & _).
rewrite t3c_bv_small by lia. lia.
Qed.


(* the decoded fields must be INSTANTIATED before vm_compute sees the goal: an evar in it makes vm_compute
   spin (measured here: 420 s and 32 GB on one instruction).  So take the decode's normal form first and
   unify the lemma's fields with it. *)
Ltac t3c_dec :=
lazymatch goal with
| |- decode_any ?w = Some (?i, _) =>
  let d := eval vm_compute in (decode_any w) in
  lazymatch d with
  | Some (?i0, _) => unify i i0
  end; vm_compute; reflexivity
end.
Ltac t3c_kept H r := rewrite (H r ltac:(cbv; lia) ltac:(cbv; lia) ltac:(cbv; lia) ltac:(cbv; lia)).
Ltac t3c_pick H R r :=
rewrite (getr_other _ 1%bv _ r ltac:(reg_neq_tac)), (getr_other _ 12%bv _ r ltac:(reg_neq_tac)),
(getr_other _ 10%bv _ r ltac:(reg_neq_tac)), (getr_other _ 10%bv _ r ltac:(reg_neq_tac));
t3c_kept H r; exact R.

Lemma t3c_jmat : forall (cx : rtcx SEGS) ly S (W : world SEGS) mem md md' ev,
ajournal (SK := SK) SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(8, c_fpos cx)] ly S W mem md ev ->
same_but_materialized md md' ->
ajournal (SK := SK) SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(8, c_fpos cx)] ly S W mem md' ev.
Proof.
intros cx ly S W mem md md' ev HJ Hm.
rewrite (same_but_materialized_wvb md md' Hm).
apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma t3_cpy : forall (cx : rtcx SEGS) POST k ly3 S3 W3 regs3 mem3 md3 bs body again b ly4 S4 W4 regsY memY mdY,
sc_base SEGS B ameter_triv WK cx -> 0 <= k < sg_nturns scene_geom_asan ->
cut_T (SK := SK) SEGS B ameter_triv WK scene_geom_asan cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
t3_post_chk cx ly3 S3 W3 mem3 body again b k (sc_F SEGS scene_geom_asan cx) ly4 S4 W4 regsY memY mdY ->
(forall ly5 S5 W5 regsD memD mdD,
 t3_post_memcpy cx ly3 S3 W3 mem3 body again b k (sc_F SEGS scene_geom_asan cx) ly5 S5 W5 regsD memD mdD ->
 SRr SEGS W5 (mkCfg (mkst regsD (Z_to_bv 64 (BASE + (S3_K + 140))) memD (seg_rom SEGS)) mdD) POST) ->
SRr SEGS W4 (mkCfg (mkst regsY (Z_to_bv 64 (BASE + (S3_K + 112))) memY (seg_rom SEGS)) mdY) POST.
Proof.
intros cx POST k ly3 S3 W3 regs3 mem3 md3 bs body again b ly4 S4 W4 regsY memY mdY HB Hk HC HPC HK.
pose proof HB as (HB0 & Hsp1eq).
pose proof HB0 as (HPRE & Hra0 & Hp10 & Hp11 & Hin0 & HfrS & Hnev0 & Hbb0 & HRO0 & Hsink0 & Hfd0 & Hfs0 & Hmo0).
pose proof HPRE as (HAR0 & Hrok0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & Hqt0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC as HCd.
unfold cut_T, sc_frame, sc_shr, sc_shbg, sc_open in HCd.
remember (sc_F SEGS scene_geom_asan cx) as F eqn:HFdef in *.
cbn [vat scene_geom_asan sgT_sp0 sgT_sp1 sgT_Fsp sgT_shF sgT_blki sgT_srcA sgT_srcB sgT_mac sgT_shexp
sgT_body sgT_again sgT_nprime sgT_got sgT_k sgT_decl sgT_n1 sgT_extra sgT_nagain sgT_expect sgT_Fb
sgT_nn sgT_body2 sgT_f8 sg_cid sg_off_blki sg_off_mac sg_off_expect sg_scene_n sg_nturns sg_sh_bg
sg_sh_blki_lo sg_sh_blki_hi sg_off_blk sg_blk_n sg_mac_n
RV_s0 RV_s1 RV_s2 RV_s3 RV_s4 RV_s5 RV_s6 RV_s7 RV_s8 RV_s9 RV_s10 RV_s11 fst snd] in HCd.
destruct HCd as (Hk0 & Hwhole & HJj & Habl & Hbbs & HBOK & HAOK & Hsepba & Hblen & Hgbody & Hja &
HFR & HSV & HSBG & HSHB & HOPB & HOPM & HIMG & HIN & HMAC &
Rsp0 & Rsp1 & Qfsp & Rsh & Rblki & Qsrca & Rsrcb & Qmac & Qshexp & Qbody & Qagain & Qnprime &
Rgot & Rk & Qdecl & Rn1 & Hextra & Hnag & Qexpect & Qfb & Qnn & Hbody2 & Rf8).
unfold RV_s0, RV_s1, RV_s2, RV_s3, RV_s4, RV_s5, RV_s6, RV_s7, RV_s8, RV_s9, RV_s10, RV_s11 in
Rsp0, Rsp1, Rsh, Rblki, Rsrcb, Rgot, Rk, Rn1, Hextra, Rf8.
pose proof HJj as (HJ & HfrS3 & Hmole).
pose proof HJ as (HAR3 & HLY3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresS & HstkS & _).
pose proof HstkS as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 HLY3) as (Eab & EFA & Eown).
assert (HinF : In (8, c_fpos cx) (frames S3)) by (rewrite HfrS3; left; reflexivity).
assert (EFAF : frame_addr ly3 8 (c_fpos cx) = F)
by (rewrite HFdef; unfold sc_F, rt_F; cbn [sg_cid scene_geom_asan]; apply EFA).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 HinF) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 HinF) as (HF32 & _ & HFpres & HFSpres).
pose proof (frm_off_imgP B ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 HinF) as HFimg.
rewrite EFAF in HF4096, HFceil, HFapp, HF32, HFpres, HFSpres, HFimg.
change (fs_frame_bytes 8) with 16384 in HF4096, HFceil, HFapp, HFpres, HFSpres, HFimg.
change (16384 / 8) with 2048 in HFSpres.
assert (HF8 : F mod 8 = 0) by (pose proof (Z.div_mod F 32 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
assert (HF32al : (F + 32) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite HF8; reflexivity).
assert (HFdiv : 0 <= F / 8 <= F) by (split; [apply Z.div_pos; lia | pose proof (Z.mul_div_le F 8 ltac:(lia)); lia]).
assert (HFdiv2 : F / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (Hac8 : alloc_ceiling / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia).
assert (HFdiv3 : F / 8 + 2048 <= alloc_ceiling / 8)
  by (rewrite <- (t3_div8_add F 2048) by exact HF8; apply Z.div_le_mono; lia).
assert (Hsp1lo : spZ (c_regs cx) - 240 <= c_sp1 cx <= spZ (c_regs cx) - 224).
{ rewrite Hsp1eq. pose proof (sp1_facts (spZ (c_regs cx) - 224)) as X.
  destruct X as (X1 & _ & _); [lia | rewrite Zminus_mod, Hsp0al; reflexivity | lia]. }
assert (Hsp1al : c_sp1 cx mod 16 = 0).
{ rewrite Hsp1eq. pose proof (sp1_facts (spZ (c_regs cx) - 224)) as X.
  destruct X as (_ & _ & X3); [lia | rewrite Zminus_mod, Hsp0al; reflexivity | exact X3]. }
assert (HshLT : shadow_addr F + 2048 <= c_sp1 cx) by (unfold shadow_addr, SHADOW_OFF in *; unfold ASTACK in HSTK; lia).
assert (HshLO : 2147450880 <= shadow_addr F) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (Esh : forall i, SHADOW_OFF + (F + 32) / 8 + i = shadow_addr F + (4 + i)).
{ intros i. unfold shadow_addr. replace (F + 32) with (F + 8 * 4) by lia. rewrite t3_div8_add by exact HF8. lia. }
pose proof HBOK as (Hb4096 & Hbz & Hbceil & Hb16 & _ & _).
pose proof HAOK as (Ha4096 & Haz & Haceil & Ha16 & Hawr & Haftok).
cbn [sg_scene_n scene_geom_asan] in Hbceil, Haceil, Hblen.
change (req_size 8904) with 8904 in Hbceil, Haceil.
pose proof HIMG as (HspE & HgpE & HtpE & HROD3).
assert (RK3 : t3_rk (spZ (c_regs cx)) (c_sp1 cx) (as_gp B) (as_tp B) F (scT_off k) k regs3).
{ unfold t3_rk. pose proof Hextra as Hx18. apply Forall_cons_iff in Hx18 as (X18 & _). cbn [fst snd vat] in X18.
  pose proof HspE as Hsp2. unfold spZ in Hsp2.
  split; [rewrite <- Hsp2; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  replace (F + 41) with (F + 32 + 9) by lia.
  repeat split; assumption. }
assert (Ho16 : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0) by (rewrite Zminus_mod, Hsp1al, Hsp0al; reflexivity).
assert (HkR : 0 <= k <= 342) by (cbn [sg_nturns scene_geom_asan] in Hk; lia).
assert (HTTd : A_TAIL_TRAILER + 12 <= F + 32 \/ F + 32 + 34 <= A_TAIL_TRAILER)
by (unfold A_TAIL_TRAILER; unfold off_img in HFimg; lia).

(* the state the check_step call left *)
destruct HPC as (HJ4 & Eab4 & Efr4 & Ebb4 & RK4 & R24 & R26 & Hkeep & Hblki & Hsh & Hd40 & Hd48 & Hd50).
destruct RK4 as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R25 & R27).
pose proof (scT_bnd k HkR) as (Hoff0 & Hoffn & Hlen14).
assert (Hsp1b : 0 <= c_sp1 cx /\ c_sp1 cx + 0x58 <= 2 ^ 64) by lia.
(* ---- the four instructions after the k split, and the call ---- *)
assert (Htail : forall (regsA : bvmap 5 word) mdA,
ajournal (SK := SK) SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(8, c_fpos cx)] ly4 S4 W4 memY mdA 2 ->
getr regsA 11 = w64 (F + (if k =? 0 then 41 else 39)) ->
(forall r : bv 5, bv_unsigned r <> 1 -> bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 ->
 getr regsA r = getr regsY r) ->
SRr SEGS W4 (mkCfg (mkst regsA (Z_to_bv 64 (BASE + (S3_K + 124))) memY (seg_rom SEGS)) mdA) POST).
{ intros regsA mdA HJA Ra1 Hkept.
  (* +0x5c8  ld a0,0x50(s1) *)
  eapply (t3c_ld W4 regsA (S3_K + 124) memY mdA POST 0x504b503 _ _ _ 10%bv 9%bv 0x50 (c_sp1 cx + 0x50) again);
  [vm_compute; reflexivity | vm_compute; reflexivity | t3c_dec
  | apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity
  | t3c_kept Hkept (9%bv : bv 5); rewrite R9; rewrite unsigned_lit_small by lia; reflexivity
  | lia | lia | exact Hd50 | ].
  intros mdB HmB. replace (S3_K + 124 + 4) with (S3_K + 128) by lia.
  (* +0x5cc  add a0,a0,s4 *)
  eapply (t3c_add W4 _ (S3_K + 128) memY mdB POST 0x1450533 _ _ _ 10%bv 10%bv 20%bv (w64 (again + scT_off k)));
  [vm_compute; reflexivity | vm_compute; reflexivity | t3c_dec
  | apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity
  | rewrite (getr_same regsA 10%bv _ ltac:(reg_neq_tac)); rewrite (getr_other regsA 10%bv _ 20%bv ltac:(reg_neq_tac));
    t3c_kept Hkept (20%bv : bv 5); rewrite R20; unfold v_add, w64; rewrite !unsigned_lit_small by lia; reflexivity | ].
  intros mdC HmC. replace (S3_K + 128 + 4) with (S3_K + 132) by lia.
  (* +0x5d0  mv a2,s10 *)
  eapply (t3c_mv W4 _ (S3_K + 132) memY mdC POST 0xd0613 _ _ _ 12%bv 26%bv 0 (w64 (scene_len k)));
  [vm_compute; reflexivity | vm_compute; reflexivity | t3c_dec
  | apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity
  | rewrite (getr_other _ 10%bv _ 26%bv ltac:(reg_neq_tac)), (getr_other regsA 10%bv _ 26%bv ltac:(reg_neq_tac));
    t3c_kept Hkept (26%bv : bv 5); rewrite R26; apply v_addi_0 | ].
  intros mdD HmD. replace (S3_K + 132 + 4) with (S3_K + 136) by lia.
  (* +0x5d4  jal __asan_memcpy *)
  eapply (t3c_call W4 _ (S3_K + 136) memY mdD POST SS___asan_memcpy 1%bv);
  [vm_compute; reflexivity | ].
  intros mdE HmE. replace (S3_K + 136 + 4) with (S3_K + 140) by lia.
  (* ---- the call: aj_intrin_atS OCpy at SIGMA SS___asan_memcpy ---- *)
  set (d := again + scT_off k) in *.
  set (x := F + (if k =? 0 then 41 else 39)) in *.
  assert (Hdeq : d = again + scT_off k) by reflexivity.
  assert (Hxeq : x = F + (if k =? 0 then 41 else 39)) by reflexivity.
  clearbody d x.
  assert (HJE : ajournal (SK := SK) SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
  (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 W4 memY mdE 2)
  by (eapply t3c_jmat; [eapply t3c_jmat; [eapply t3c_jmat; [eapply t3c_jmat; [exact HJA | exact HmB] | exact HmC] | exact HmD] | exact HmE]).
  pose proof HJ4 as (HAR4 & HLY4 & _).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR0 HLY4) as (Eabl4 & EFA4 & Eown4).
  assert (HinF4 : In (8, c_fpos cx) (frames S4)) by (rewrite Efr4; exact HinF).
  assert (EFAF4 : frame_addr ly4 8 (c_fpos cx) = F) by (rewrite <- EFAF; rewrite EFA4, EFA; reflexivity).
  assert (HinA4 : In (again, 8904) (ablocks B ly4 S4)).
  { rewrite Eab4, Habl. apply in_or_app. right. cbn [sg_scene_n scene_geom_asan]. left. reflexivity. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ again 8904 HAR4 HinA4) as (HAin & HAapp & HAceil4 & HAzone & HApres).
  change (req_size 8904) with 8904 in HAceil4, HApres.
  assert (Hdn : 0 <= d /\ d + scene_len k <= again + 8904) by (rewrite Hdeq; lia).
  assert (Hxr : F + 32 <= x /\ x + scene_len k <= F + 32 + 34).
  { rewrite Hxeq. unfold scene_len. destruct (Z.eqb_spec k 0); [lia|]. destruct (Z.eqb_spec k 342); lia. }
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (Has : ASTACK = 16384) by reflexivity.
  assert (Hshlow : forall X, 0 <= X -> X + 16384 <= alloc_ceiling -> shadow_addr X + 2048 < alloc_ceiling).
  { intros X H0 Hc. unfold shadow_addr, SHADOW_OFF.
    assert (X / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
    assert (alloc_ceiling / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia). lia. }
  assert (HwinA : forall a, a < alloc_ceiling ->
  ~ (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)) - ESTACK <= a < spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))).
  { intros a Ha. lia. }
  assert (HwinB : forall a, c_sp1 cx <= a ->
  ~ (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)) - ESTACK <= a < spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))).
  { intros a Ha. lia. }
  assert (HwinN : forall a,
  (c_sp1 cx <= a \/ in_frames ly3 (frames S3) a \/ (exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= a < p + req_size n)
   \/ (in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))) ->
  ~ (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)) - ESTACK <= a < spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))).
  { intros a [Ha | [Ha | [(p & n & Hin & Hp) | (Himg & _ & _)]]].
    - apply HwinB; lia.
    - destruct Ha as (cid & pos & Hin & Hr). rewrite HfrS3 in Hin. destruct Hin as [E | []].
      assert (Hcp : cid = 8 /\ pos = c_fpos cx) by (injection E as E1 E2; split; symmetry; assumption).
      destruct Hcp as (Ecid & Epos). rewrite Ecid, Epos in Hr.
      destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 HinF) as (Hf1 & Hf2 & _).
      rewrite EFAF in Hf1, Hf2. change (fs_frame_bytes 8) with 16384 in Hf2.
      pose proof (Hshlow F ltac:(lia) ltac:(lia)) as Hsl.
      apply HwinA. unfold in_zr in Hr. cbn [fst snd] in Hr.
      rewrite EFAF in Hr. change (fs_frame_bytes 8) with 16384 in Hr. change (16384 / 8) with 2048 in Hr. lia.
    - apply HwinA. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR3 Hin) as (_ & _ & Hc & _). lia.
    - apply HwinA. pose proof (pa_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow. lia. }
  (* the facts the post needs, taken before the call while the register map has a name *)
  assert (Hdisj : again + 8904 <= F \/ F + 16384 <= again).
  { pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 memY mdY again 8904 8 (c_fpos cx) HAR4 HinA4 HinF4) as Hsep.
    unfold zdisjoint in Hsep. rewrite EFAF4 in Hsep. change (req_size 8904) with 8904 in Hsep.
    change (fs_frame_bytes 8) with 16384 in Hsep. cbn [fst snd] in Hsep. exact Hsep. }
  assert (HkLSB2 : kLowShadowBeg = 2147446784) by reflexivity.
  assert (Hshdis : forall j, 4 <= j < 9 -> ~ (d <= shadow_addr F + j < d + scene_len k)).
  { intros j Hj. rewrite Hdeq. unfold shadow_addr, SHADOW_OFF.
    destruct HAzone as (_ & [Hl | (Hh & _)]); change (req_size 8904) with 8904 in *; lia. }
  match goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ => pose (RGC := rg) end.
  assert (RKcall : t3_rk (spZ (c_regs cx)) (c_sp1 cx) (as_gp B) (as_tp B) F (scT_off k) k RGC).
  { unfold t3_rk, RGC. repeat split;
    [ t3c_pick Hkept R2 (2%bv : bv 5) | t3c_pick Hkept R3 (3%bv : bv 5) | t3c_pick Hkept R4 (4%bv : bv 5)
    | t3c_pick Hkept R8 (8%bv : bv 5) | t3c_pick Hkept R9 (9%bv : bv 5) | t3c_pick Hkept R18 (18%bv : bv 5)
    | t3c_pick Hkept R19 (19%bv : bv 5) | t3c_pick Hkept R20 (20%bv : bv 5) | t3c_pick Hkept R21 (21%bv : bv 5)
    | t3c_pick Hkept R22 (22%bv : bv 5) | t3c_pick Hkept R23 (23%bv : bv 5) | t3c_pick Hkept R25 (25%bv : bv 5)
    | t3c_pick Hkept R27 (27%bv : bv 5) ]. }
  assert (R24c : getr RGC 24 = w64 (scene_len k + scT_off k)) by (unfold RGC; t3c_pick Hkept R24 (24%bv : bv 5)).
  assert (R26c : getr RGC 26 = w64 (scene_len k)) by (unfold RGC; t3c_pick Hkept R26 (26%bv : bv 5)).
  eapply SRr_bind.
  { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA SS___asan_memcpy) AMEMCPY
    W4 _ memY (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(8, c_fpos cx)] ly4 S4 mdE 2 d x (scene_len k) (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + (S3_K + 140)))).
    - exact HJE.
    - rewrite (getr_other _ 1%bv _ 10%bv ltac:(reg_neq_tac)), (getr_other _ 12%bv _ 10%bv ltac:(reg_neq_tac)).
      apply getr_same; reg_neq_tac.
    - rewrite (getr_other _ 1%bv _ 11%bv ltac:(reg_neq_tac)), (getr_other _ 12%bv _ 11%bv ltac:(reg_neq_tac)),
      (getr_other _ 10%bv _ 11%bv ltac:(reg_neq_tac)), (getr_other _ 10%bv _ 11%bv ltac:(reg_neq_tac)). exact Ra1.
    - rewrite (getr_other _ 1%bv _ 12%bv ltac:(reg_neq_tac)). apply getr_same; reg_neq_tac.
    - lia.
    - lia.
    - lia.
    - unfold spZ. rewrite (getr_other _ 1%bv _ 2%bv ltac:(reg_neq_tac)), (getr_other _ 12%bv _ 2%bv ltac:(reg_neq_tac)),
      (getr_other _ 10%bv _ 2%bv ltac:(reg_neq_tac)), (getr_other _ 10%bv _ 2%bv ltac:(reg_neq_tac)).
      t3c_kept Hkept (2%bv : bv 5). rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - exact Ho16.
    - lia.
    - lia.
    - rewrite (getr_other _ 1%bv _ 3%bv ltac:(reg_neq_tac)), (getr_other _ 12%bv _ 3%bv ltac:(reg_neq_tac)),
      (getr_other _ 10%bv _ 3%bv ltac:(reg_neq_tac)), (getr_other _ 10%bv _ 3%bv ltac:(reg_neq_tac)).
      t3c_kept Hkept (3%bv : bv 5). exact R3.
    - rewrite (getr_other _ 1%bv _ 4%bv ltac:(reg_neq_tac)), (getr_other _ 12%bv _ 4%bv ltac:(reg_neq_tac)),
      (getr_other _ 10%bv _ 4%bv ltac:(reg_neq_tac)), (getr_other _ 10%bv _ 4%bv ltac:(reg_neq_tac)).
      t3c_kept Hkept (4%bv : bv 5). exact R4.
    - apply getr_same; reg_neq_tac.
    - apply t3c_ret; [unfold S3_K, AF_LLVMFuzzerTestOneInput, SEG_T_off; lia
                     |unfold S3_K, AF_LLVMFuzzerTestOneInput, SEG_T_off; reflexivity].
    - intros a Ha. split.
      + replace a with (again + (scT_off k + (a - d))) by lia.
        apply (Hawr (ablocks B ly4 S4) ly4 [(8, c_fpos cx)] (scT_off k + (a - d)) HinA4).
        change (req_size 8904) with 8904. lia.
      + apply HwinA. lia.
    - apply (amem_range_of_block SEGS B LAWS ly4 S4 W4 memY mdY again 8904 d (scene_len k) HAR4 HinA4 ltac:(lia));
      change (req_size 8904) with 8904; lia.
    - eapply (range_addressable_of_block SEGS B LAWS ly4 S4 W4 memY mdY again 8904 d (scene_len k) HAR4 HinA4 ltac:(lia));
      change (req_size 8904) with 8904; lia.
    - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly4 S4 W4 memY mdY again 8904 d (scene_len k) HAR4 HinA4 ltac:(lia));
      change (req_size 8904) with 8904; lia.
    - split; [lia|]. split; [lia|]. split.
      + intros a Ha. split.
        * replace a with (F + 32 + (x - (F + 32) + (a - x))) by lia.
          rewrite Hblki by lia. discriminate.
        * unfold spZ. rewrite (getr_other _ 1%bv _ 2%bv ltac:(reg_neq_tac)), (getr_other _ 12%bv _ 2%bv ltac:(reg_neq_tac)),
          (getr_other _ 10%bv _ 2%bv ltac:(reg_neq_tac)), (getr_other _ 10%bv _ 2%bv ltac:(reg_neq_tac)).
          t3c_kept Hkept (2%bv : bv 5). rewrite R2. unfold w64. rewrite unsigned_lit_small by lia.
          lia.
      + split.
        * pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 memY mdY again 8904 8 (c_fpos cx) HAR4 HinA4 HinF4) as Hsep.
          unfold zdisjoint in Hsep. rewrite EFAF4 in Hsep. change (req_size 8904) with 8904 in Hsep.
          change (fs_frame_bytes 8) with 16384 in Hsep. cbn [fst snd] in Hsep.
          destruct Hsep as [Hs|Hs]; [left|right]; rewrite Hdeq in *; lia.
        * split; [|split].
          -- apply amem_range_high; [lia| |lia].
             assert (HkLSB : kLowShadowBeg = 2147446784) by reflexivity.
             destruct HFapp as (_ & [Hl | (Hh & _)]); [left | right]; lia.
          -- apply (range_addressable_sub (aview SEGS (w_H W4) memY) SHADOW_OFF (F + 32) 34 x (scene_len k));
             [|lia|lia].
             apply (t3_ra_part (aview SEGS (w_H W4) memY) (F + 32) 4 2); [exact HF32al | lia | lia | |].
             ++ intros i Hi. rewrite Esh by lia. rewrite Hsh by lia.
                replace (4 + i =? 8) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
             ++ rewrite Esh. rewrite Hsh by lia. reflexivity.
          -- intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly4 S4 W4 memY mdY 8 (c_fpos cx) x (scene_len k) HAR4 HinF4);
             try rewrite EFAF4; try change (fs_frame_bytes 8) with 16384; lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres2 & Heff & Hkept2 & Hpres2 & Hmat2).
  assert (Hslot : forall off v, 0x40 <= off <= 0x50 ->
  rdword (aview SEGS (w_H W4) memY) (c_sp1 cx + off) = Some v ->
  rdword (aview SEGS (w_H W4) mem2) (c_sp1 cx + off) = Some v).
  { intros off v Hoff Hr. rewrite <- Hr. apply rdword_ext. intros i Hi.
    apply (Hkept2 (c_sp1 cx + off + i) ltac:(lia) ltac:(rewrite Hdeq in *; lia) ltac:(apply HwinB; lia)). }
  (* ---- the state __asan_memcpy returns to ---- *)
  apply (HK ly4 S4 W4 regs2 mem2 md2).
  unfold t3_post_memcpy.
  split; [exact HJ2|]. split; [exact Eab4|]. split; [exact Efr4|]. split; [exact Ebb4|].
  split; [exact (t3_rk_pres _ _ _ _ _ _ _ _ _ HP2 RKcall)|].
  split.
  { transitivity (getr RGC 24%bv); [|exact R24c]. exact (HP2 24 ltac:(unfold acallee_saved; lia)). }
  split.
  { transitivity (getr RGC 26%bv); [|exact R26c]. exact (HP2 26 ltac:(unfold acallee_saved; lia)). }
  split.
  { intros a Ha Hc1 Hc40 Hcb Hcs Hcc.
    rewrite (Hkept2 a Ha ltac:(rewrite Hdeq; exact Hcc) (HwinN a Hc1)).
    exact (Hkeep a Ha Hc1 Hc40 Hcb Hcs). }
  split.
  { intros i Hi. rewrite (Hkept2 (F + 32 + i) ltac:(lia) ltac:(rewrite Hdeq in *; lia)
    ltac:(apply HwinA; lia)). exact (Hblki i Hi). }
  split.
  { intros j Hj. rewrite (Hkept2 (shadow_addr F + j) ltac:(unfold shadow_addr, SHADOW_OFF in *; lia)
    (Hshdis j Hj) ltac:(apply HwinA; pose proof (Hshlow F ltac:(lia) ltac:(lia)); lia)). exact (Hsh j Hj). }
  split; [exact (Hslot 0x40 8904 ltac:(lia) Hd40)|].
  split; [exact (Hslot 0x48 (F + 39) ltac:(lia) Hd48)|].
  split; [exact (Hslot 0x50 again ltac:(lia) Hd50)|].
  intros i Hi. rewrite Hdeq in *. rewrite (Heff i Hi).
  replace (x + i) with (F + 32 + ((if k =? 0 then 9 else 7) + i))
  by (rewrite Hxeq; destruct (Z.eqb_spec k 0); lia).
  rewrite Hblki by (destruct (Z.eqb_spec k 0); lia).
  rewrite Z2Nat.inj_add by (destruct (Z.eqb_spec k 0); lia). reflexivity.

  }
(* ---- the guard: mv a1,s7 ; beqz s6 ---- *)
(* +0x5bc  mv a1,s7 *)
eapply (t3c_mv W4 regsY (S3_K + 112) memY mdY POST 0xb8593 _ _ _ 11%bv 23%bv 0 (w64 (F + 41)));
[vm_compute; reflexivity | vm_compute; reflexivity | t3c_dec
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| rewrite R23; apply v_addi_0 | ].
intros md1 Hm1. replace (S3_K + 112 + 4) with (S3_K + 116) by lia.
(* +0x5c0  beqz s6,+8 *)
eapply (t3c_branch_off W4 _ (S3_K + 116) memY md1 POST 0xb0463 BC_EQ _ _ _ 22%bv 0%bv 8);
[vm_compute; reflexivity | vm_compute; reflexivity | t3c_dec
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | | ].
- (* k = 0: a1 keeps blk.i + 9 *)
intros Hb md2 Hm2.
rewrite (getr_other regsY 11%bv _ 22%bv ltac:(reg_neq_tac)), R22, getr_zero in Hb.
rewrite (branch_eq_lit _ 0 ltac:(lia)) in Hb.
unfold w64 in Hb. rewrite unsigned_lit_small in Hb by lia.
apply Z.eqb_eq in Hb.
replace (S3_K + 116 + 8) with (S3_K + 124) by lia.
apply (Htail _ md2 (t3c_jmat cx ly4 S4 W4 memY md1 md2 2 (t3c_jmat cx ly4 S4 W4 memY mdY md1 2 HJ4 Hm1) Hm2)).
+ rewrite (getr_same regsY 11%bv _ ltac:(reg_neq_tac)). rewrite Hb. reflexivity.
+ intros r H1 H10 H11 H12. apply getr_other. intros Hc. apply H11. rewrite Hc. reflexivity.
- (* k <> 0: a1 := blk.i + 7 *)
intros Hb md2 Hm2.
rewrite (getr_other regsY 11%bv _ 22%bv ltac:(reg_neq_tac)), R22, getr_zero in Hb.
rewrite (branch_eq_lit _ 0 ltac:(lia)) in Hb.
unfold w64 in Hb. rewrite unsigned_lit_small in Hb by lia.
apply Z.eqb_neq in Hb.
replace (S3_K + 116 + 4) with (S3_K + 120) by lia.
(* +0x5c4  ld a1,0x48(s1) *)
eapply (t3c_ld W4 _ (S3_K + 120) memY md2 POST 0x484b583 _ _ _ 11%bv 9%bv 0x48 (c_sp1 cx + 0x48) (F + 39));
[vm_compute; reflexivity | vm_compute; reflexivity | t3c_dec
| apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity
| rewrite (getr_other regsY 11%bv _ 9%bv ltac:(reg_neq_tac)), R9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
| lia | lia | exact Hd48 | ].
intros md3' Hm3. replace (S3_K + 120 + 4) with (S3_K + 124) by lia.
apply (Htail _ md3' (t3c_jmat cx ly4 S4 W4 memY md2 md3' 2
(t3c_jmat cx ly4 S4 W4 memY md1 md2 2 (t3c_jmat cx ly4 S4 W4 memY mdY md1 2 HJ4 Hm1) Hm2) Hm3)).
+ rewrite (getr_same _ 11%bv _ ltac:(reg_neq_tac)).
  destruct (Z.eqb_spec k 0); [lia | reflexivity].
+ intros r H1 H10 H11 H12.
  rewrite (getr_other _ 11%bv _ r ltac:(intros Hc; apply H11; rewrite Hc; reflexivity)).
  apply getr_other. intros Hc. apply H11. rewrite Hc. reflexivity.
Qed.

(* ================================================================================================================
   t3z: a Theorem Labs lane's proof of t3_close (at 646014fbde56).  The re-poison stores and
   the latch, +0x5d8 .. +0x5f8: ONE plain symbolic run (paj_run_shc over SRr_run_pi_AJ; the five stores write the
   frame's shadow, which the token executor refuses) from a fresh state holding only blk.i's five shadow cells as a
   writable region with no chunks, the branch split (psrr_branch_pi), and in each arm a run to the cut pc
   (paj_run_to_shc to +0x54c or +0x5fc); the cut is rebuilt by t3z_next_T.  Only the classes of t3_post_memcpy's
   kept clause that cut_T reads are used: the stack above sp1, the frame and its shadow, body and again.
   Lemmas copied from another lane carry their citation.
   ================================================================================================================ *)
(* ---- t3c: pure helpers, image-free ---- *)
(* `addiw rd,rs,1` on k < 2^31 - 1: copied from a Theorem Labs lane's s3t_addiw1 (at 67cd72b99e4,
   lib/AU/P_LLVMFuzzerTestOneInput_S3.v:2993-3000), with that lane's s3e_unsigned64 replaced by this tree's
   unsigned_lit_small (Reusable/YP03.v:651, the same statement). *)
Lemma t3z_addiw1 : forall k, 0 <= k < 2 ^ 31 - 1 ->
sext 64 (alu32 ALU_ADD (low32 (w64 k)) (low32 (Z_to_bv 64 1))) = w64 (k + 1).
Proof.
intros k Hk.
replace (low32 (Z_to_bv 64 1)) with (sext 32 (Z_to_bv 12 1)) by (apply bv_eq; vm_compute; reflexivity).
rewrite w_addiw. replace (bv_signed (Z_to_bv 12 1)) with 1 by (vm_compute; reflexivity).
apply bv_eq. unfold w64. rewrite v_addiw_small; rewrite ?unsigned_lit_small; lia.
Qed.
(* the value of the symbolic form s_aluw3 leaves for `addiw rd,rs,1` (YP0e.v:1597), when rs holds a small k *)
Lemma t3z_aluw_add1 : forall E n k, ew E n = Z_to_bv 64 k -> 0 <= k < 2 ^ 31 - 1 ->
sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 1)) = Z_to_bv 64 (k + 1).
Proof.
intros E n k Hn Hk.
first
[ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Hn; exact (t3z_addiw1 k Hk)
| change (sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 1)))
  with (sext 64 (alu32 ALU_ADD (low32 (sv_denot E (SOff n 0))) (low32 (sv_denot E (SLit 1)))));
  rewrite (denot_lit_U E (SOff n 0)), (U_atom E n k Hn) by lia;
  rewrite (denot_lit_U E (SLit 1)), (U_lit E 1) by lia;
  rewrite zalu32_sound; f_equal;
  unfold zalu32, zu32, M32; cbn [zalu_raw];
  rewrite (Z.mod_small k) by lia; rewrite (Z.mod_small 1) by lia;
  unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with 2147483648; change (bv_modulus 32) with 4294967296;
  rewrite (Z.mod_small (k + 1 + 2147483648)) by lia;
  unfold zcanon, M64; rewrite Z.mod_small by lia; lia ].
Qed.
(* `declared` is 8904 at every head after the first: copied from a Theorem Labs lane's s3_decl_next
   (at a17a864ad65, lib/AU/P_LLVMFuzzerTestOneInput_S3.v:923-924). *)
Lemma t3z_decl_next : forall k, 0 <= k -> (if k + 1 =? 0 then 0 else 8904) = 8904.
Proof. intros k Hk. destruct (Z.eqb_spec (k + 1) 0) as [He|_]; [lia | reflexivity]. Qed.
(* block_shadow reads only the shadow cells of its object: copied from a Theorem Labs lane's s3n_open_keep (a17a864ad65,
   lib/AU/P_LLVMFuzzerTestOneInput_S3.v:1891-1897). *)
Lemma t3z_open_keep : forall (rd rd' : Z -> option Z) p n,
(forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr SHADOW_OFF p + i) = rd (shadow_of_addr SHADOW_OFF p + i)) ->
block_shadow rd SHADOW_OFF p n -> block_shadow rd' SHADOW_OFF p n.
Proof.
intros rd rd' p n HK (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. rewrite HK by exact Hi. exact (H3 i Hi).
Qed.
(* the again buffer at the latch: copied from a Theorem Labs lane's s3_again_step_list (a17a864ad65, :894-908). *)
Lemma t3z_again_step_list : forall (b ja : list byte) (k : Z),
length b = 8904%nat -> 0 <= k <= 342 -> Z.of_nat (length ja) = 8904 - scT_off k ->
firstn (Z.to_nat (scT_off k)) b
++ (firstn (Z.to_nat (scene_len k)) (skipn (Z.to_nat (scT_src k)) (scene_block b k))
++ skipn (Z.to_nat (scene_len k)) ja)
= firstn (Z.to_nat (scT_off (k + 1))) b ++ skipn (Z.to_nat (scene_len k)) ja
/\ Z.of_nat (length (skipn (Z.to_nat (scene_len k)) ja)) = 8904 - scT_off (k + 1).
Proof.
intros b ja k Hb Hk Hja.
pose proof (scT_bnd k Hk) as (Hlo & Hhi & Hlen).
pose proof (scT_off_step k Hk) as Hstep.
split.
- rewrite app_assoc. rewrite (scT_again_step b k Hb Hk). reflexivity.
- rewrite length_skipn. lia.
Qed.

(* ---- t3c: memory helpers at SEGS ---- *)
(* a one-byte chunk of a run's region pins that byte, whatever symbolic value it holds: copied from a Theorem Labs lane's
   s3t_chunk_byte (at 67cd72b99e4, lib/AU/P_LLVMFuzzerTestOneInput_S3.v:2980-2990), with
   s3e_unsigned64 replaced by unsigned_lit_small (Reusable/YP03.v:651). *)
Lemma t3z_chunk_byte : forall E (m : word -> option byte) base off e v,
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 1 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
mbyte SEGS m (base + off) = Some (Z_to_bv 8 v).
Proof.
intros E m base off e v Hc He Hv. unfold YP09.chunk_ok in Hc.
destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (x & Hx & Hm).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hx, Hm. injection Hx as <-.
rewrite Z.add_0_r in Hm. rewrite Hm. f_equal.
unfold YP09.byte_of_word. rewrite He, unsigned_lit_small by lia.
replace (8 * 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
Qed.
(* a shadow cell the run stored `sb s5` into: the chunk holds s5's atom, whose low byte is 0xf8 *)
Lemma t3z_shb_f8 : forall E (H : word -> bool) mem n b cs lo hi wlo whi od,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 (SOff 21 0))) cs -> ew E 21 = Z_to_bv 64 (2 ^ 64 - 8) ->
aview SEGS H mem (b + od) = Some 0xf8.
Proof.
intros E H mem n b cs lo hi wlo whi od (_ & _ & _ & Hcs) Hn Hc H21.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
assert (Hd : sv_denot E (SOff 21 0) = Z_to_bv 64 (2 ^ 64 - 8))
  by (rewrite (denot_lit_U E (SOff 21 0)), (U_atom E 21 (2 ^ 64 - 8) H21) by lia; reflexivity).
unfold aview. rewrite (t3z_chunk_byte _ _ _ _ _ _ Hck Hd ltac:(lia)). reflexivity.
Qed.
(* a spilled doubleword moves with the eight bytes it reads: copied from a Theorem Labs lane's s3n_spill (a17a864ad65, :1871-1878) *)
Lemma t3z_spill : forall (W W' : world SEGS) (mem mem' : word -> option byte) (a v : Z),
rdword (aview SEGS (w_H W) mem) a = Some v ->
(forall i, 0 <= i < 8 -> aview SEGS (w_H W') mem' (a + i) = aview SEGS (w_H W) mem (a + i)) ->
rdword (aview SEGS (w_H W') mem') a = Some v.
Proof.
intros W W' mem mem' a v Hv HK.
rewrite (rdword_ext (aview SEGS (w_H W) mem)); [exact Hv|]. exact HK.
Qed.
(* copied from a Theorem Labs lane's s3_keep_garr8_pt (a17a864ad65, :654-661) *)
Lemma t3z_keep_garr8 : forall (W W' : world SEGS) (mem mem' : word -> option byte) (a0 : Z) (l : list Z),
garr8 SEGS (mrestrict (w_H W) mem) a0 l ->
(forall a, a0 <= a < a0 + Z.of_nat (length l) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
garr8 SEGS (mrestrict (w_H W') mem') a0 l.
Proof.
intros W W' mem mem' a0 l HG HK. apply (garr8_frame SEGS _ _ a0 l HG).
intros a Ha. apply (mbyte_of_aview SEGS). exact (HK a Ha).
Qed.
(* copied from a Theorem Labs lane's s3_keep_saves_pt (a17a864ad65, :721-728) *)
Lemma t3z_keep_saves : forall (cx : rtcx SEGS) (W W' : world SEGS) (mem mem' : word -> option byte),
sc_saves SEGS cx W mem ->
(forall a, spZ (c_regs cx) - 104 <= a < spZ (c_regs cx) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
sc_saves SEGS cx W' mem'.
Proof.
intros cx W W' mem mem' HS HK j Hj.
rewrite (rdword_ext (aview SEGS (w_H W) mem)); [exact (HS j Hj)|]. intros i Hi. apply HK. lia.
Qed.
(* the frame-object clauses of the cut, at the asan table, with F named: in the form of a Theorem Labs lane's s3_keep_frame_pt /
   s3_keep_shr_pt (a17a864ad65, :519-537, :598-606). *)
Lemma t3z_keep_frame : forall (cx : rtcx SEGS) F (W W' : world SEGS) (mem mem' : word -> option byte),
F = sc_F SEGS scene_geom_asan cx ->
sc_frame SEGS scene_geom_asan cx W mem ->
(forall a, F + 16384 - 8 <= a < F + 16384 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall a, F <= a < F + 16384 -> apresent (w_H W') mem' a) ->
(forall o, 0 <= o < 2048 -> apresent (w_H W') mem' (shadow_addr F + o)) ->
sc_frame SEGS scene_geom_asan cx W' mem'.
Proof.
intros cx F W W' mem mem' -> HF HK HP HPS. unfold sc_frame in *. destruct HF as (HR & _ & _).
change (fs_frame_bytes (sg_cid scene_geom_asan)) with 16384 in HR |- *.
split; [|split].
- rewrite (rdword_ext (aview SEGS (w_H W) mem)); [exact HR|]. intros i Hi. apply HK. lia.
- intros a Ha. exact (HP a Ha).
- intros a Ha. change (16384 / 8) with 2048 in Ha.
  replace a with (shadow_addr (sc_F SEGS scene_geom_asan cx) + (a - shadow_addr (sc_F SEGS scene_geom_asan cx))) by lia.
  apply HPS. lia.
Qed.
Lemma t3z_keep_shr : forall (cx : rtcx SEGS) F (W W' : world SEGS) (mem mem' : word -> option byte) (l h v : Z),
F = sc_F SEGS scene_geom_asan cx -> sc_shr SEGS scene_geom_asan cx W mem l h v ->
(forall a, shadow_addr F + l <= a < shadow_addr F + h -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
sc_shr SEGS scene_geom_asan cx W' mem' l h v.
Proof. intros cx F W W' mem mem' l h v -> HS HK o Ho. rewrite HK by lia. exact (HS o Ho). Qed.
Lemma t3z_shr_of : forall (cx : rtcx SEGS) F (W : world SEGS) (mem : word -> option byte) (l h v : Z),
F = sc_F SEGS scene_geom_asan cx ->
(forall o, l <= o < h -> aview SEGS (w_H W) mem (shadow_addr F + o) = Some v) ->
sc_shr SEGS scene_geom_asan cx W mem l h v.
Proof. intros cx F W mem l h v -> H. exact H. Qed.
Lemma t3z_keep_open : forall (cx : rtcx SEGS) F (W W' : world SEGS) (mem mem' : word -> option byte) (off len : Z),
F = sc_F SEGS scene_geom_asan cx -> sc_open SEGS scene_geom_asan cx W mem off len ->
(forall i, 0 <= i < (len + 7) / 8 ->
 aview SEGS (w_H W') mem' (shadow_of_addr SHADOW_OFF (F + off) + i)
 = aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF (F + off) + i)) ->
sc_open SEGS scene_geom_asan cx W' mem' off len.
Proof. intros cx F W W' mem mem' off len -> HO HK. unfold sc_open in *. exact (t3z_open_keep _ _ _ _ HK HO). Qed.
(* the memcpy's bytes spliced into again: copied from a Theorem Labs lane's s3n_garr8_splice (a17a864ad65, :1901-1931) *)
Lemma t3z_garr8_splice : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z) (pre src ja : list byte),
garr8 SEGS (mrestrict H m) a (u8s (pre ++ ja)) ->
(length src <= length ja)%nat ->
garr8 SEGS (mrestrict H' m') (a + Z.of_nat (length pre)) (u8s src) ->
(forall x, a <= x < a + Z.of_nat (length pre) -> aview SEGS H' m' x = aview SEGS H m x) ->
(forall x, a + Z.of_nat (length pre) + Z.of_nat (length src) <=
x < a + Z.of_nat (length pre) + Z.of_nat (length ja) -> aview SEGS H' m' x = aview SEGS H m x) ->
garr8 SEGS (mrestrict H' m') a (u8s (pre ++ src ++ skipn (length src) ja)).
Proof.
intros H H' m m' a pre src ja HG Hle HS Hkpre Hktail.
unfold u8s in HG, HS |- *. rewrite map_app in HG.
destruct (proj1 (garr8_app SEGS (mrestrict H m) a _ _) HG) as (HGp & HGj).
rewrite length_map in HGj.
assert (HJsplit : map (fun x : byte => bv_unsigned x) ja
= map (fun x : byte => bv_unsigned x) (firstn (length src) ja)
++ map (fun x : byte => bv_unsigned x) (skipn (length src) ja)).
{ rewrite <- map_app, firstn_skipn. reflexivity. }
rewrite HJsplit in HGj.
destruct (proj1 (garr8_app SEGS (mrestrict H m) (a + Z.of_nat (length pre)) _ _) HGj) as (_ & HGt).
rewrite length_map, length_firstn, (Nat.min_l _ _ Hle) in HGt.
rewrite !map_app.
apply (proj2 (garr8_app SEGS (mrestrict H' m') a _ _)). split.
- apply (garr8_frame SEGS (mrestrict H m) _ a _ HGp).
  intros x Hx. apply (mbyte_of_aview SEGS). apply Hkpre. rewrite length_map in Hx. exact Hx.
- rewrite length_map.
  apply (proj2 (garr8_app SEGS (mrestrict H' m') (a + Z.of_nat (length pre)) _ _)). split; [exact HS|].
  rewrite length_map.
  apply (garr8_frame SEGS (mrestrict H m) _ _ _ HGt).
  intros x Hx. apply (mbyte_of_aview SEGS). apply Hktail.
  rewrite length_map, length_skipn in Hx. lia.
Qed.
(* the `exists ja` clause of cut_T at k + 1: copied from a Theorem Labs lane's s3n_again_next (a17a864ad65, :1935-1978), with
   its one-byte view lemma replaced by this tree's val_mem1_of_aview (lib/A/Prog/YC88.v:75). *)
Lemma t3z_again_next : forall (W3 W' : world SEGS) (mem3 mem' : word -> option byte) (again : Z)
(b ja : list byte) (k : Z),
length b = 8904%nat -> 0 <= k <= 342 -> Z.of_nat (length ja) = 8904 - scT_off k ->
garr8 SEGS (mrestrict (w_H W3) mem3) again (u8s (firstn (Z.to_nat (scT_off k)) b ++ ja)) ->
(forall a, again <= a < again + 8904 -> ~ (again + scT_off k <= a < again + scT_off k + scene_len k) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall i, 0 <= i < scene_len k ->
aview SEGS (w_H W') mem' (again + scT_off k + i)
= Some (bv_unsigned (nth (Z.to_nat (scT_src k + i)) (scene_block b k) (Z_to_bv 8 0)))) ->
exists ja' : list byte, Z.of_nat (length ja') = 8904 - scT_off (k + 1) /\
garr8 SEGS (mrestrict (w_H W') mem') again (u8s (firstn (Z.to_nat (scT_off (k + 1))) b ++ ja')).
Proof.
intros W3 W' mem3 mem' again b ja k Hb Hk Hja HG HK HC.
pose proof (scT_bnd k Hk) as (Hlo & Hhi & Hlen).
assert (Hsrc : 7 <= scT_src k /\ scT_src k + scene_len k <= 33)
by (unfold scT_src, scene_len; destruct (k =? 0); [lia | destruct (k =? 342); lia]).
pose proof (scT_block_len b k Hb Hk) as Hbl.
destruct (t3z_again_step_list b ja k Hb Hk Hja) as (Heq & Hlen').
exists (skipn (Z.to_nat (scene_len k)) ja). split; [exact Hlen'|].
rewrite <- Heq.
set (src := firstn (Z.to_nat (scene_len k)) (skipn (Z.to_nat (scT_src k)) (scene_block b k))).
set (pre := firstn (Z.to_nat (scT_off k)) b).
assert (Hsl : length src = Z.to_nat (scene_len k)).
{ unfold src. rewrite length_firstn, length_skipn, Hbl. lia. }
assert (Hpl : length pre = Z.to_nat (scT_off k)).
{ unfold pre. rewrite length_firstn, Hb. apply Nat.min_l.
  change 8904%nat with (Z.to_nat 8904). lia. }
rewrite <- Hsl.
apply (t3z_garr8_splice (w_H W3) (w_H W') mem3 mem' again pre src ja HG).
- rewrite Hsl. lia.
- rewrite Hpl, Z2Nat.id by lia.
  intros j Hj. unfold u8s in Hj. rewrite length_map, Hsl in Hj.
  assert (Hn : nth j (u8s src) 0 = bv_unsigned (nth j src (Z_to_bv 8 0)))
  by (unfold u8s; exact (map_nth bv_unsigned src (Z_to_bv 8 0) j)).
  assert (Hs : nth j src (Z_to_bv 8 0) = nth (Z.to_nat (scT_src k + Z.of_nat j)) (scene_block b k) (Z_to_bv 8 0)).
  { unfold src. rewrite nth_firstn.
    replace (j <? Z.to_nat (scene_len k))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_skipn. f_equal. lia. }
  rewrite Hn, Hs.
  exact (val_mem1_of_aview SEGS (w_H W') mem' (again + scT_off k + Z.of_nat j) _ (HC (Z.of_nat j) ltac:(lia))).
- intros x Hx. rewrite Hpl, Z2Nat.id in Hx by lia. apply HK; lia.
- intros x Hx. rewrite Hpl, Hsl, !Z2Nat.id in Hx by lia. apply HK; lia.
Qed.

(* the registers at the head of turn k + 1: t3_rk at the new got and k, from the old one and what the run did *)
Lemma t3z_rk_next : forall sp0 sp1 gp tp F got k got' k' (r r' : bvmap 5 word),
t3_rk sp0 sp1 gp tp F got k r ->
(forall x, In x [2; 3; 4; 8; 9; 18; 19; 21; 23; 25; 27]%bv -> getr r' x = getr r x) ->
getr r' 20 = w64 got' -> getr r' 22 = w64 k' -> t3_rk sp0 sp1 gp tp F got' k' r'.
Proof.
intros sp0 sp1 gp tp F got k got' k' r r' (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E27)
HK H20 H22.
unfold t3_rk.
repeat split; first [exact H20 | exact H22 | (etransitivity; [apply HK; cbn; tauto | assumption])].
Qed.

(* ---- the geometry of the cut that the re-assembly needs: where the frame, its shadow, the stack window and the two
   heap blocks lie, and that they are pairwise apart.  From the entry facts and cut_T alone. ---- *)
Lemma t3z_geo : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k F,
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := SK) SEGS B ameter_triv WK scene_geom_asan cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
F = sc_F SEGS scene_geom_asan cx ->
(frame_addr ly3 8 (c_fpos cx) = F /\ frames S3 = [(8, c_fpos cx)] /\
 In (body, 8904) (ablocks B ly3 S3) /\ In (again, 8904) (ablocks B ly3 S3)) /\
(4096 <= F /\ F + 16384 <= alloc_ceiling /\ (F + 16384 <= 2147446784 \/ 17594333495296 <= F) /\
 2147450880 <= shadow_addr F /\ shadow_addr F + 2048 <= 17594333495296 /\
 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000) /\
(alloc_ceiling + 16384 <= c_sp1 cx /\ c_sp1 cx + 224 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47) /\
(4096 <= body /\ body + 8904 <= alloc_ceiling /\ (body + 8904 <= 2147446784 \/ 17594333495296 <= body)) /\
(4096 <= again /\ again + 8904 <= alloc_ceiling /\ (again + 8904 <= 2147446784 \/ 17594333495296 <= again)) /\
(body + 8904 <= F \/ F + 16384 <= body) /\ (again + 8904 <= F \/ F + 16384 <= again) /\
(again + 8904 <= body \/ body + 8904 <= again).
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k F HB HC HFdef.
pose proof HB as (HB0 & Hsp1eq).
pose proof HB0 as (HPRE & _).
pose proof HPRE as (HAR0 & _).
pose proof HC as (_ & _ & HJj & Habl & _ & HBOK & HAOK & Hsepba & _).
pose proof HJj as (HJ & HfrS3 & _).
cbn [sg_cid sg_scene_n scene_geom_asan] in HfrS3, Habl, Hsepba.
pose proof HJ as (HAR3 & HLY3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HstkS & _).
pose proof HstkS as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 HLY3) as (_ & EFA & _).
assert (HinF : In (8, c_fpos cx) (frames S3)) by (rewrite HfrS3; left; reflexivity).
assert (EFAF : frame_addr ly3 8 (c_fpos cx) = F)
by (rewrite HFdef; unfold sc_F, rt_F; cbn [sg_cid scene_geom_asan]; apply EFA).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 HinF) as (HF4096 & HFceil & HFapp).
rewrite EFAF in HF4096, HFceil, HFapp. change (fs_frame_bytes 8) with 16384 in HFceil, HFapp.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
assert (HFdiv : 0 <= F / 8 <= F) by (split; [apply Z.div_pos; lia | pose proof (Z.mul_div_le F 8 ltac:(lia)); lia]).
assert (Hac8 : alloc_ceiling / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia).
assert (HFdiv3 : F / 8 + 2048 <= alloc_ceiling / 8)
  by (rewrite <- (Z.div_add F 2048 8) by lia; apply Z.div_le_mono; lia).
assert (Gsh : 2147450880 <= shadow_addr F /\ shadow_addr F + 2048 <= 17594333495296)
  by (unfold shadow_addr, SHADOW_OFF; lia).
assert (GF : F + 16384 <= 2147446784 \/ 17594333495296 <= F)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp; lia).
assert (Hsp1lo : spZ (c_regs cx) - 240 <= c_sp1 cx <= spZ (c_regs cx) - 224).
{ rewrite Hsp1eq. pose proof (sp1_facts (spZ (c_regs cx) - 224)) as X.
  destruct X as (X1 & _ & _); [lia | rewrite Zminus_mod, Hsp0al; reflexivity | lia]. }
assert (Gsp : alloc_ceiling + 16384 <= c_sp1 cx) by (unfold ASTACK in HSTK; lia).
pose proof HBOK as (Hb4096 & Hbz & Hbceil & _ & _ & _).
pose proof HAOK as (Ha4096 & Haz & Haceil & _ & _ & _).
cbn [sg_scene_n scene_geom_asan] in Hbz, Hbceil, Haz, Haceil.
change (req_size 8904) with 8904 in Hbz, Hbceil, Haz, Haceil.
unfold zone2, off_img in Hbz, Haz.
assert (Hbin : In (body, 8904) (ablocks B ly3 S3))
  by (rewrite Habl; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (Hain : In (again, 8904) (ablocks B ly3 S3)) by (rewrite Habl; apply in_or_app; right; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 body 8904 8 (c_fpos cx) HAR3 Hbin HinF) as Gbf.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 again 8904 8 (c_fpos cx) HAR3 Hain HinF) as Gaf.
rewrite EFAF in Gbf, Gaf. unfold zdisjoint in Gbf, Gaf. cbn [fst snd] in Gbf, Gaf.
change (req_size 8904) with 8904 in Gbf, Gaf. change (fs_frame_bytes 8) with 16384 in Gbf, Gaf.
refine (conj (conj EFAF (conj HfrS3 (conj Hbin Hain))) _).
repeat split; lia.
Qed.

(* ---- THE RE-ASSEMBLY of cut_T at k + 1 (the asan form of a Theorem Labs lane's s3_next_T, a17a864ad65 :1998-2165).
   The turn's effect, in the forms t3_post_memcpy and the run hand over: the journal at the new state with the block
   list, frames and live bytes of the cut; the registers as t3_rk at the new got and k; memory as the post-memcpy
   memory memD, equal to the cut's on each range the cut reads (the stack window, the frame, the frame's shadow,
   body, again) outside what the turn wrote, and the run's memory mem', equal to memD outside blk.i's five shadow
   cells, which now read 0xf8; `declared` and the memcpy's bytes, read in memD.  No clause asks for any byte below
   alloc_ceiling outside those ranges. ---- *)
Lemma t3z_next_T : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k
(ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (memD mem' : word -> option byte) (md' : Model),
sc_base SEGS B ameter_triv WK cx -> k < 343 ->
cut_T (SK := SK) SEGS B ameter_triv WK scene_geom_asan cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
ajournal (SK := SK) SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(8, c_fpos cx)] ly' S' W' mem' md' 2 ->
ablocks B ly' S' = ablocks B ly3 S3 -> frames S' = frames S3 -> blocks_bytes S' <= blocks_bytes S3 ->
t3_rk (spZ (c_regs cx)) (c_sp1 cx) (as_gp B) (as_tp B) (sc_F SEGS scene_geom_asan cx) (scT_off (k + 1)) (k + 1) regs' ->
(forall a, body <= a < body + 8904 -> aview SEGS (w_H W') memD a = aview SEGS (w_H W3) mem3 a) ->
(forall a, again <= a < again + 8904 -> ~ (again + scT_off k <= a < again + scT_off k + scene_len k) ->
 aview SEGS (w_H W') memD a = aview SEGS (w_H W3) mem3 a) ->
(forall a, sc_F SEGS scene_geom_asan cx <= a < sc_F SEGS scene_geom_asan cx + 16384 ->
 ~ (sc_F SEGS scene_geom_asan cx + 32 <= a < sc_F SEGS scene_geom_asan cx + 32 + 34) ->
 aview SEGS (w_H W') memD a = aview SEGS (w_H W3) mem3 a) ->
(forall a, shadow_addr (sc_F SEGS scene_geom_asan cx) <= a < shadow_addr (sc_F SEGS scene_geom_asan cx) + 2048 ->
 ~ (shadow_addr (sc_F SEGS scene_geom_asan cx) + 4 <= a < shadow_addr (sc_F SEGS scene_geom_asan cx) + 9) ->
 aview SEGS (w_H W') memD a = aview SEGS (w_H W3) mem3 a) ->
(forall a, c_sp1 cx + 8 <= a < spZ (c_regs cx) -> ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) ->
 aview SEGS (w_H W') memD a = aview SEGS (w_H W3) mem3 a) ->
(forall a, 0 <= a < 2 ^ 64 ->
 ~ (shadow_addr (sc_F SEGS scene_geom_asan cx) + 4 <= a < shadow_addr (sc_F SEGS scene_geom_asan cx) + 9) ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W') memD a) ->
rdword (aview SEGS (w_H W') memD) (c_sp1 cx + 0x40) = Some 8904 ->
(forall i, 0 <= i < scene_len k -> aview SEGS (w_H W') memD (again + scT_off k + i)
 = Some (bv_unsigned (nth (Z.to_nat (if k =? 0 then 9 else 7) + Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))) ->
(forall j, 4 <= j < 9 -> aview SEGS (w_H W') mem' (shadow_addr (sc_F SEGS scene_geom_asan cx) + j) = Some 0xf8) ->
cut_T (SK := SK) SEGS B ameter_triv WK scene_geom_asan cx ly' S' W' regs' mem' md' bs body again b (k + 1).
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ly' S' W' regs' memD mem' md'
HB Hk343 HC HJ' Hab' Hfr' Hbb' RK KBD KAD KFD KSD KKD KM Ddecl Dcpy Hsh.
pose proof HB as (HB0 & _).
pose proof HB0 as (HPRE & _ & _ & _ & _ & _ & _ & _ & HRO0 & _).
pose proof HPRE as (HAR0 & _).
remember (sc_F SEGS scene_geom_asan cx) as F eqn:HFdef in *.
destruct (t3z_geo cx ly3 S3 W3 regs3 mem3 md3 bs body again b k F HB HC HFdef) as
((EFAF & HfrS3 & Hbin & Hain) & (HF4096 & HFceil & GF & Gsh0 & Gsh1 & CR) & (Gsp & Gsp1 & Gsp0) &
 (Hb4096 & Hbceil & Hbz) & (Ha4096 & Haceil & Haz) & Gbf & Gaf & Gsep).
pose proof HC as HCd.
unfold cut_T in HCd.
rewrite <- HFdef in HCd.
cbn [vat scene_geom_asan sgT_sp0 sgT_sp1 sgT_Fsp sgT_shF sgT_blki sgT_srcA sgT_srcB sgT_mac sgT_shexp
sgT_body sgT_again sgT_nprime sgT_got sgT_k sgT_decl sgT_n1 sgT_extra sgT_nagain sgT_expect sgT_Fb
sgT_nn sgT_body2 sgT_f8 sg_cid sg_off_blki sg_off_mac sg_off_expect sg_scene_n sg_nturns sg_sh_bg
sg_sh_blki_lo sg_sh_blki_hi sg_off_blk sg_blk_n sg_mac_n
RV_s0 RV_s1 RV_s2 RV_s3 RV_s4 RV_s5 RV_s6 RV_s7 RV_s8 RV_s9 RV_s10 RV_s11 fst snd] in HCd.
destruct HCd as (Hk0 & Hwhole & HJj & Habl & Hbbs & HBOK & HAOK & Hsepba & Hblen & Hgbody & Hja &
HFR & HSV & HSBG & HSHB & HOPB & HOPM & HIMG & HIN & HMAC &
Rsp0 & Rsp1 & Qfsp & Rsh & Rblki & Qsrca & Rsrcb & Qmac & Qshexp & Qbody & Qagain & Qnprime &
Rgot & Rk & Qdecl & Rn1 & Hextra & Hnag & Qexpect & Qfb & Qnn & Hbody2 & Rf8).
assert (HkR : 0 <= k <= 342) by lia.
pose proof (scT_bnd k HkR) as (Goff0 & Goff1 & Glen).
assert (Hb : length b = 8904%nat) by (change 8904%nat with (Z.to_nat 8904); lia).
(* the cut's memory at the new state, on each range the cut reads *)
assert (KB : forall a, body <= a < body + 8904 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a)
  by (intros a Ha; rewrite KM by lia; apply KBD; lia).
assert (KA : forall a, again <= a < again + 8904 -> ~ (again + scT_off k <= a < again + scT_off k + scene_len k) ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a)
  by (intros a Ha Hn; rewrite KM by lia; apply KAD; lia).
assert (KF : forall a, F <= a < F + 16384 -> ~ (F + 32 <= a < F + 32 + 34) ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a)
  by (intros a Ha Hn; rewrite KM by lia; apply KFD; lia).
assert (KS : forall a, shadow_addr F <= a < shadow_addr F + 2048 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a)
  by (intros a Ha Hn; rewrite KM by lia; apply KSD; lia).
assert (KK : forall a, c_sp1 cx + 8 <= a < spZ (c_regs cx) -> ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a)
  by (intros a Ha Hn; rewrite KM by lia; apply KKD; lia).
assert (Ddecl' : rdword (aview SEGS (w_H W') mem') (c_sp1 cx + 0x40) = Some 8904).
{ rewrite (rdword_ext (aview SEGS (w_H W') memD)); [exact Ddecl|]. intros j Hj. apply KM; lia. }
assert (Dcpy' : forall i, 0 <= i < scene_len k -> aview SEGS (w_H W') mem' (again + scT_off k + i)
  = Some (bv_unsigned (nth (Z.to_nat (scT_src k + i)) (scene_block b k) (Z_to_bv 8 0)))).
{ intros i Hi. rewrite KM by lia. rewrite (Dcpy i Hi). unfold scT_src.
  rewrite (Z2Nat.inj_add (if k =? 0 then 9 else 7) i) by (destruct (k =? 0); lia). reflexivity. }
(* the new state's frame: presence from AR, at the new layout *)
pose proof HJ' as (HAR' & HLY' & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly' HAR0 HLY') as (_ & EFA' & _).
assert (EFAF' : frame_addr ly' 8 (c_fpos cx) = F)
by (rewrite HFdef; unfold sc_F, rt_F; cbn [sg_cid scene_geom_asan]; apply EFA').
assert (HinF' : In (8, c_fpos cx) (frames S')) by (rewrite Hfr', HfrS3; left; reflexivity).
destruct (al_frames _ _ LAWS ly' S' W' mem' md' 8 (c_fpos cx) HAR' HinF') as (_ & _ & HFpres' & HFSpres').
rewrite EFAF' in HFpres', HFSpres'. change (fs_frame_bytes 8) with 16384 in HFpres', HFSpres'.
change (16384 / 8) with 2048 in HFSpres'.
(* the read-only bytes at the new state, through the journal *)
assert (HRO0P : arodata_okP SEGS (@pa_relro_lo _ scene_listing PI_scene) (@pa_relro_hi _ scene_listing PI_scene) B
  (aview SEGS (w_H (c_W cx)) (c_mem cx))) by (rewrite <- HWRLO, <- HWRHI; exact HRO0).
pose proof (arodata_ok_journalP (SK := SK) SEGS _ _ pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' HRO0P) as HRODA.
pose proof RK as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E27).
(* the goal *)
unfold cut_T. rewrite <- HFdef.
cbn [vat scene_geom_asan sgT_sp0 sgT_sp1 sgT_Fsp sgT_shF sgT_blki sgT_srcA sgT_srcB sgT_mac sgT_shexp
sgT_body sgT_again sgT_nprime sgT_got sgT_k sgT_decl sgT_n1 sgT_extra sgT_nagain sgT_expect sgT_Fb
sgT_nn sgT_body2 sgT_f8 sg_cid sg_off_blki sg_off_mac sg_off_expect sg_scene_n sg_nturns
sg_sh_blki_lo sg_sh_blki_hi sg_off_blk sg_blk_n sg_mac_n
RV_s0 RV_s1 RV_s2 RV_s3 RV_s4 RV_s5 RV_s6 RV_s7 RV_s8 RV_s9 RV_s10 RV_s11 fst snd].
split; [lia|].
split; [exact Hwhole|].
split.
{ unfold sc_j. cbn [sg_cid scene_geom_asan mo_le ameter_triv].
  split; [exact HJ'|]. split; [rewrite Hfr'; exact HfrS3 | exact I]. }
split; [rewrite Hab'; exact Habl|].
split; [lia|].
split; [exact HBOK|].
split; [exact HAOK|].
split; [exact Hsepba|].
split; [exact Hblen|].
split.
{ apply (t3z_keep_garr8 W3 W' mem3 mem' body (u8s b) Hgbody).
  intros a Ha. unfold u8s in Ha. rewrite length_map in Ha. apply KB. lia. }
split.
{ destruct Hja as (ja & Hjal & Hgja). exact (t3z_again_next W3 W' mem3 mem' again b ja k Hb HkR Hjal Hgja KA Dcpy'). }
split.
{ apply (t3z_keep_frame cx F W3 W' mem3 mem' HFdef HFR).
  - intros a Ha. apply KF; lia.
  - intros a Ha. exact (proj1 (HFpres' a Ha)).
  - intros o Ho. exact (proj1 (HFSpres' o Ho)). }
split.
{ apply (t3z_keep_saves cx W3 W' mem3 mem' HSV). intros a Ha. apply KK; lia. }
split.
{ unfold sc_shbg in HSBG |- *. cbn [sg_sh_bg scene_geom_asan] in HSBG |- *.
  apply Forall_forall. intros t Ht.
  pose proof (proj1 (Forall_forall _ _) HSBG t Ht) as Ht1. cbv beta in Ht1 |- *.
  assert (Hbnd : 0 <= fst (fst t) /\ snd (fst t) <= 2048 /\ (snd (fst t) <= 4 \/ 9 <= fst (fst t))).
  { destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd]; lia. }
  destruct Hbnd as (Hl & Hh & Hout).
  apply (t3z_keep_shr cx F W3 W' mem3 mem' _ _ _ HFdef Ht1).
  intros a Ha. apply KS; lia. }
split; [exact (t3z_shr_of cx F W' mem' 4 9 0xf8 HFdef Hsh)|].
split.
{ apply (t3z_keep_open cx F W3 W' mem3 mem' 144 34 HFdef HOPB).
  intros i Hi. change ((34 + 7) / 8) with 5 in Hi.
  assert (E : shadow_of_addr SHADOW_OFF (F + 144) = shadow_addr F + 18).
  { unfold shadow_of_addr, shadow_addr. replace (F + 144) with (F + 18 * 8) by ring. rewrite Z.div_add by lia. ring. }
  rewrite E. apply KS; lia. }
split.
{ apply (t3z_keep_open cx F W3 W' mem3 mem' 112 6 HFdef HOPM).
  intros i Hi. change ((6 + 7) / 8) with 1 in Hi.
  assert (E : shadow_of_addr SHADOW_OFF (F + 112) = shadow_addr F + 14).
  { unfold shadow_of_addr, shadow_addr. replace (F + 112) with (F + 14 * 8) by ring. rewrite Z.div_add by lia. ring. }
  rewrite E. apply KS; lia. }
split.
{ unfold sc_img. split; [unfold spZ; rewrite E2; unfold w64; apply unsigned_lit_small; lia|].
  split; [exact E3|]. split; [exact E4|]. rewrite HWRLO, HWRHI. exact HRODA. }
split; [exact HIN|].
split.
{ apply (t3z_keep_garr8 W3 W' mem3 mem' (F + 112) (sc_macb bs) HMAC).
  intros a Ha. assert (Hl6 : Z.of_nat (length (sc_macb bs)) = 6) by reflexivity. rewrite Hl6 in Ha.
  apply KF; lia. }
(* the located values *)
split; [exact E8|].
split; [exact E9|].
split; [apply (t3z_spill _ _ _ _ _ _ Qfsp); intros j Hj; apply KK; lia|].
split; [exact E19|].
split; [exact E25|].
split; [apply (t3z_spill _ _ _ _ _ _ Qsrca); intros j Hj; apply KK; lia|].
split; [replace (F + 32 + 9) with (F + 41) by lia; exact E23|].
split; [apply (t3z_spill _ _ _ _ _ _ Qmac); intros j Hj; apply KK; lia|].
split; [apply (t3z_spill _ _ _ _ _ _ Qshexp); intros j Hj; apply KK; lia|].
split; [apply (t3z_spill _ _ _ _ _ _ Qbody); intros j Hj; apply KK; lia|].
split; [apply (t3z_spill _ _ _ _ _ _ Qagain); intros j Hj; apply KK; lia|].
split; [apply (t3z_spill _ _ _ _ _ _ Qnprime); intros j Hj; apply KK; lia|].
split; [exact E20|].
split; [exact E22|].
split; [rewrite (t3z_decl_next k) by lia; exact Ddecl'|].
split; [exact E27|].
split; [apply Forall_cons; [cbn [fst snd vat]; exact E18 | apply Forall_nil]|].
split; [first [exact I | cbn; exact I]|].
split; [apply (t3z_spill _ _ _ _ _ _ Qexpect); intros j Hj; apply KK; lia|].
split; [apply (t3z_spill _ _ _ _ _ _ Qfb); intros j Hj; apply KK; lia|].
split; [apply (t3z_spill _ _ _ _ _ _ Qnn); intros j Hj; apply KK; lia|].
split; [first [exact I | cbn; exact I]|].
exact E21.
Qed.

(* the register a run leaves, with its symbolic value computed (prreg, lib/A/Prog/ScenePaLib.v:366, without the
   normalisation of the denotation) *)
Local Ltac t3z_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

Lemma t3_close : forall (cx : rtcx SEGS) POST k ly3 S3 W3 regs3 mem3 md3 bs body again b ly5 S5 W5 regsD memD mdD,
sc_base SEGS B ameter_triv WK cx -> 0 <= k < sg_nturns scene_geom_asan ->
(k + 1 < sg_nturns scene_geom_asan ->
 sc_from_T (SK := SK) SEGS B ameter_triv WK scene_geom_asan cx POST (k + 1)) ->
sc_from_TX (SK := SK) SEGS B ameter_triv WK scene_geom_asan cx POST ->
cut_T (SK := SK) SEGS B ameter_triv WK scene_geom_asan cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
t3_post_memcpy cx ly3 S3 W3 mem3 body again b k (sc_F SEGS scene_geom_asan cx) ly5 S5 W5 regsD memD mdD ->
SRr SEGS W5 (mkCfg (mkst regsD (Z_to_bv 64 (BASE + (S3_K + 140))) memD (seg_rom SEGS)) mdD) POST.
Proof.
intros cx POST k ly3 S3 W3 regs3 mem3 md3 bs body again b ly5 S5 W5 regsD memD mdD HB Hk HT HTX HC Hpm.
unfold t3_post_memcpy in Hpm.
destruct Hpm as (HJ & Hab5 & Hfr5 & Hbb5 & RKD & D24 & D26 & KD & DBLK & DSH & Ddecl & Dsrc & Dagain & Dcpy).
pose proof HB as (HB0 & _).
pose proof HB0 as (HPRE & _).
pose proof HPRE as (HAR0 & _).
destruct (t3z_geo cx ly3 S3 W3 regs3 mem3 md3 bs body again b k (sc_F SEGS scene_geom_asan cx) HB HC eq_refl) as
((EFAF3 & HfrS3 & Hbin & Hain) & (G4096 & GFceil & GF & Gsh0 & Gsh1 & CR) & (Gsp & Gsp1 & Gsp0) &
 (Hb4096 & Hbceil & Hbz) & (Ha4096 & Haceil & Haz) & Gbf & Gaf & Gsep).
pose proof HJ as (HAR5 & HLY5 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly5 HAR0 HLY5) as (_ & EFA5 & _).
assert (HkR : 0 <= k <= 342) by (cbn [sg_nturns scene_geom_asan] in Hk; lia).
remember (sc_F SEGS scene_geom_asan cx) as F eqn:HFdef in *.
assert (EFAF5 : frame_addr ly5 8 (c_fpos cx) = F)
by (rewrite HFdef; unfold sc_F, rt_F; cbn [sg_cid scene_geom_asan]; apply EFA5).
assert (HinF5 : In (8, c_fpos cx) (frames S5)) by (rewrite Hfr5, HfrS3; left; reflexivity).
destruct (al_frames _ _ LAWS ly5 S5 W5 memD mdD 8 (c_fpos cx) HAR5 HinF5) as (_ & _ & _ & HFSpres).
rewrite EFAF5 in HFSpres. change (fs_frame_bytes 8) with 16384 in HFSpres.
change (16384 / 8) with 2048 in HFSpres.
pose proof (scT_bnd k HkR) as (Goff0 & Goff1 & Glen).
(* ---- the post-memcpy memory against the cut, on each range the cut reads: through the classes of
   t3_post_memcpy's kept clause (the stack above sp1, the frame and its shadow, the two heap blocks) ---- *)
assert (KBD : forall a, body <= a < body + 8904 -> aview SEGS (w_H W5) memD a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply KD; [lia | | lia | lia | lia | lia].
  right; right; left. exists body, 8904. split; [exact Hbin | change (req_size 8904) with 8904; lia]. }
assert (KAD : forall a, again <= a < again + 8904 -> ~ (again + scT_off k <= a < again + scT_off k + scene_len k) ->
  aview SEGS (w_H W5) memD a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. apply KD; [lia | | lia | lia | lia | exact Hn].
  right; right; left. exists again, 8904. split; [exact Hain | change (req_size 8904) with 8904; lia]. }
assert (KFD : forall a, F <= a < F + 16384 -> ~ (F + 32 <= a < F + 32 + 34) ->
  aview SEGS (w_H W5) memD a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. apply KD; [lia | | lia | exact Hn | lia | lia].
  right; left. exists 8, (c_fpos cx). split; [rewrite HfrS3; left; reflexivity|].
  left. unfold in_zr. cbn [fst snd]. rewrite EFAF3. change (fs_frame_bytes 8) with 16384. lia. }
assert (KSD : forall a, shadow_addr F <= a < shadow_addr F + 2048 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
  aview SEGS (w_H W5) memD a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. apply KD; [lia | | lia | lia | exact Hn | lia].
  right; left. exists 8, (c_fpos cx). split; [rewrite HfrS3; left; reflexivity|].
  right. unfold in_zr. cbn [fst snd]. rewrite EFAF3. change (fs_frame_bytes 8 / 8) with 2048. lia. }
assert (KKD : forall a, c_sp1 cx + 8 <= a < spZ (c_regs cx) -> ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) ->
  aview SEGS (w_H W5) memD a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. apply KD; [lia | left; lia | exact Hn | lia | lia | lia]. }
pose proof RKD as (D2 & D3 & D4 & D8 & D9 & D18 & D19 & D20 & D21 & D22 & D23 & D25 & D27).
(* ---- the symbolic state at +0x5d8: only blk.i's five shadow cells, writable, no chunks ---- *)
remember (Eimg (Ereg regsD [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsD r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regsD []) E)
  by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (U19 : bv_unsigned (ew E 19) = shadow_addr F)
  by (rewrite (EE 19%nat 19%bv eq_refl), D19; unfold w64; apply unsigned_lit_small; lia).
assert (E21 : ew E 21 = Z_to_bv 64 (2 ^ 64 - 8)) by (rewrite (EE 21%nat 21%bv eq_refl), D21; reflexivity).
assert (E22 : ew E 22 = Z_to_bv 64 k) by (rewrite (EE 22%nat 22%bv eq_refl), D22; reflexivity).
assert (E24 : ew E 24 = Z_to_bv 64 (scene_len k + scT_off k)) by (rewrite (EE 24%nat 24%bv eq_refl), D24; reflexivity).
assert (HS : st_ok_pi SEGS VAL E (mkSS (S3_K + 140) sr_atoms [YP09.mkRegion (Some 19%nat) 4 9 4 9 []]
  None (mkFacts [] [] []))
  (restrict (w_H W5) (mkst regsD (Z_to_bv 64 (BASE + (S3_K + 140))) memD (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|].
    split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFSpres o ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok; cbn; tauto. }
(* ---- the run, +0x5d8 .. the bne at +0x5f8 ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hin & Ha). destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite U19 in Ha. right; right; right. exists 8, (c_fpos cx). split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite EFAF5. change (fs_frame_bytes 8 / 8) with 2048. lia. }
rename ms into ms1, HJ into HJ1, HFr into HFr1. clear HF HG.
set (md1 := with_vm_backing (m_vm_lazy mdD) mat mdD) in *. clearbody md1. clear mat.
psrr_branch_pi RUNP BR HS.
{ (* taken: k + 1 <> 343, the back edge to the loop head *)
  assert (Hk1 : k + 1 <> 343).
  { rewrite branch_ne_U in Hc. unfold U in Hc. rewrite (t3z_aluw_add1 E 22 k E22 ltac:(lia)) in Hc.
    change (sv_denot E (SLit 343)) with (Z_to_bv 64 343) in Hc.
    rewrite !unsigned_lit_small in Hc by lia.
    apply (proj1 (negb_true_iff _)) in Hc. apply (proj1 (Z.eqb_neq _ _)) in Hc. exact Hc. }
  paj_run_to_shc RUNTOP HS HJ1 S3_K.
  { intros a (r & Hin & Ha). destruct Hin as [<- | []];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha.
    rewrite U19 in Ha. right; right; right. exists 8, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFAF5. change (fs_frame_bytes 8 / 8) with 2048. lia. }
  rename ms into ms2, HJ1 into HJ2, HFr into HFr2. clear HF HG.
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
    aview SEGS (w_H W5) (ms_mem ms2) a = aview SEGS (w_H W5) memD a).
  { intros a Ha Hn.
    rewrite (t3_kept_run E _ (w_H W5) (ms_mem ms1) (ms_mem ms2) a HFr2 Ha).
    - eapply t3_kept_run; [exact HFr1 | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | []];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Har. rewrite U19 in Har. lia.
    - intros (r & Hin & Har). destruct Hin as [<- | []];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Har. rewrite U19 in Har. lia. }
  assert (Hsh : forall j, 4 <= j < 9 -> aview SEGS (w_H W5) (ms_mem ms2) (shadow_addr F + j) = Some 0xf8).
  { pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRA. cbn [ms_mem restrict] in HRA.
    intros j Hj. assert (Hj' : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia.
    destruct Hj' as [-> | [-> | [-> | [-> | ->]]]];
    (eapply t3z_shb_f8; [exact HRA | exact U19 | cbn; tauto | exact E21]). }
  assert (KR2 : forall x, In x [2; 3; 4; 8; 9; 18; 19; 21; 23; 24; 25; 27]%bv -> getr (ms_regs ms2) x = getr regsD x)
    by (intros x Hx; exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W5) ms2) regsD []
          [2; 3; 4; 8; 9; 18; 19; 21; 23; 24; 25; 27]%bv HS HAG eq_refl x Hx)).
  assert (R20 : getr (ms_regs ms2) 20 = w64 (scT_off (k + 1))).
  { t3z_reg HS (20%bv : bv 5) Hr. rewrite Hr.
    rewrite (denot_lit_U E (SOff 24 0)), (U_atom E 24 _ E24) by (pose proof (scT_bnd k HkR); lia).
    unfold w64. f_equal. rewrite (scT_off_step k HkR). lia. }
  assert (R22 : getr (ms_regs ms2) 22 = w64 (k + 1)).
  { t3z_reg HS (22%bv : bv 5) Hr. rewrite Hr.
    exact (t3z_aluw_add1 E 22 k E22 ltac:(lia)). }
  assert (RK2 : t3_rk (spZ (c_regs cx)) (c_sp1 cx) (as_gp B) (as_tp B) F (scT_off (k + 1)) (k + 1) (ms_regs ms2)).
  { apply (t3z_rk_next _ _ _ _ _ _ _ _ _ regsD _ RKD); [| exact R20 | exact R22].
    intros x Hx. apply KR2. cbn in Hx |- *. tauto. }
  subst F.
  pose proof (t3z_next_T cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ly5 S5 W5 (ms_regs ms2) memD (ms_mem ms2) md2
    HB ltac:(lia) HC HJ2 Hab5 Hfr5 Hbb5 RK2 KBD KAD KFD KSD KKD KM Ddecl Dcpy Hsh) as HCUT.
  unfold sc_from_T in HT.
  pmkst HS.
  specialize (HT ltac:(cbn [sg_nturns scene_geom_asan]; lia) ly5 S5 W5 (ms_regs ms2) (ms_mem ms2) md2 bs body again b HCUT).
  unfold cfg_at in HT. cbn [sg_pc_t scene_geom_asan] in HT.
  match goal with |- SRr _ _ (mkCfg (mkst _ ?pc _ _) _) _ =>
    replace pc with (w64 (BASE + AF_LLVMFuzzerTestOneInput + SEG_T_off))
    by (unfold w64, AF_LLVMFuzzerTestOneInput, SEG_T_off; f_equal; lia) end.
  exact HT. }
{ (* not taken: k + 1 = 343, the fall-through to the loop exit *)
  assert (Hk1 : k + 1 = 343).
  { rewrite branch_ne_U in Hc. unfold U in Hc. rewrite (t3z_aluw_add1 E 22 k E22 ltac:(lia)) in Hc.
    change (sv_denot E (SLit 343)) with (Z_to_bv 64 343) in Hc.
    rewrite !unsigned_lit_small in Hc by lia.
    apply (proj1 (negb_false_iff _)) in Hc. apply (proj1 (Z.eqb_eq _ _)) in Hc. exact Hc. }
  paj_run_to_shc RUNTOP HS HJ1 S3_KX.
  { intros a (r & Hin & Ha). destruct Hin as [<- | []];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha.
    rewrite U19 in Ha. right; right; right. exists 8, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFAF5. change (fs_frame_bytes 8 / 8) with 2048. lia. }
  rename ms into ms2, HJ1 into HJ2, HFr into HFr2. clear HF HG.
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
    aview SEGS (w_H W5) (ms_mem ms2) a = aview SEGS (w_H W5) memD a).
  { intros a Ha Hn.
    rewrite (t3_kept_run E _ (w_H W5) (ms_mem ms1) (ms_mem ms2) a HFr2 Ha).
    - eapply t3_kept_run; [exact HFr1 | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | []];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Har. rewrite U19 in Har. lia.
    - intros (r & Hin & Har). destruct Hin as [<- | []];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Har. rewrite U19 in Har. lia. }
  assert (Hsh : forall j, 4 <= j < 9 -> aview SEGS (w_H W5) (ms_mem ms2) (shadow_addr F + j) = Some 0xf8).
  { pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRA. cbn [ms_mem restrict] in HRA.
    intros j Hj. assert (Hj' : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia.
    destruct Hj' as [-> | [-> | [-> | [-> | ->]]]];
    (eapply t3z_shb_f8; [exact HRA | exact U19 | cbn; tauto | exact E21]). }
  assert (KR2 : forall x, In x [2; 3; 4; 8; 9; 18; 19; 21; 23; 24; 25; 27]%bv -> getr (ms_regs ms2) x = getr regsD x)
    by (intros x Hx; exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W5) ms2) regsD []
          [2; 3; 4; 8; 9; 18; 19; 21; 23; 24; 25; 27]%bv HS HAG eq_refl x Hx)).
  assert (R20 : getr (ms_regs ms2) 20 = w64 (scT_off (k + 1))).
  { t3z_reg HS (20%bv : bv 5) Hr. rewrite Hr.
    rewrite (denot_lit_U E (SOff 24 0)), (U_atom E 24 _ E24) by (pose proof (scT_bnd k HkR); lia).
    unfold w64. f_equal. rewrite (scT_off_step k HkR). lia. }
  assert (R22 : getr (ms_regs ms2) 22 = w64 (k + 1)).
  { t3z_reg HS (22%bv : bv 5) Hr. rewrite Hr. exact (t3z_aluw_add1 E 22 k E22 ltac:(lia)). }
  assert (R24 : getr (ms_regs ms2) 24 = w64 8904).
  { rewrite (KR2 24%bv ltac:(cbn; tauto)), D24. replace k with 342 by lia. reflexivity. }
  assert (RK2 : t3_rk (spZ (c_regs cx)) (c_sp1 cx) (as_gp B) (as_tp B) F (scT_off (k + 1)) (k + 1) (ms_regs ms2)).
  { apply (t3z_rk_next _ _ _ _ _ _ _ _ _ regsD _ RKD); [| exact R20 | exact R22].
    intros x Hx. apply KR2. cbn in Hx |- *. tauto. }
  subst F.
  pose proof (t3z_next_T cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ly5 S5 W5 (ms_regs ms2) memD (ms_mem ms2) md2
    HB ltac:(lia) HC HJ2 Hab5 Hfr5 Hbb5 RK2 KBD KAD KFD KSD KKD KM Ddecl Dcpy Hsh) as HCUT.
  replace (k + 1) with 343 in HCUT, R20 by lia.
  assert (HTXC : cut_TX (SK := SK) SEGS B ameter_triv WK scene_geom_asan cx ly5 S5 W5 (ms_regs ms2) (ms_mem ms2) md2
    bs body again b).
  { unfold cut_TX. cbn [sg_nturns sg_scene_n sgT_got sgTX_got2 scene_geom_asan vat RV_s4 RV_s8].
    split; [exact HCUT|]. split; [etransitivity; [exact R20 | reflexivity] | exact R24]. }
  unfold sc_from_TX in HTX.
  pmkst HS.
  specialize (HTX ly5 S5 W5 (ms_regs ms2) (ms_mem ms2) md2 bs body again b HTXC).
  unfold cfg_at in HTX. cbn [sg_pc_tx scene_geom_asan] in HTX.
  match goal with |- SRr _ _ (mkCfg (mkst _ ?pc _ _) _) _ =>
    replace pc with (w64 (BASE + AF_LLVMFuzzerTestOneInput + SEG_TX_off))
    by (unfold w64, AF_LLVMFuzzerTestOneInput, SEG_TX_off; f_equal; lia) end.
  exact HTX. }
Qed.

(* the three seams composed: from t3_pre_chk (the check_step call site) to POST, worlds threaded Wb -> W4 -> W5
   end to end.  This is the world-consistency check (a Theorem Labs lane 05:0xZ) and the tool the theorem uses at +0x5b8. *)
Lemma t3_from_pre_chk : forall (cx : rtcx SEGS) POST k ly3 S3 W3 regs3 mem3 md3 bs body again b lyb Sb Wb regsX memX mdX,
sc_base SEGS B ameter_triv WK cx -> 0 <= k < sg_nturns scene_geom_asan ->
(k + 1 < sg_nturns scene_geom_asan ->
 sc_from_T (SK := SK) SEGS B ameter_triv WK scene_geom_asan cx POST (k + 1)) ->
sc_from_TX (SK := SK) SEGS B ameter_triv WK scene_geom_asan cx POST ->
cut_T (SK := SK) SEGS B ameter_triv WK scene_geom_asan cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
t3_pre_chk cx ly3 S3 W3 mem3 body again b k (sc_F SEGS scene_geom_asan cx) lyb Sb Wb regsX memX mdX ->
SRr SEGS Wb (mkCfg (mkst regsX (Z_to_bv 64 (SIGMA SS_check_step)) memX (seg_rom SEGS)) mdX) POST.
Proof.
intros cx POST k ly3 S3 W3 regs3 mem3 md3 bs body again b lyb Sb Wb regsX memX mdX HB Hk HT HTX HC Hpre.
apply (t3_chk cx POST k ly3 S3 W3 regs3 mem3 md3 bs body again b lyb Sb Wb regsX memX mdX HB Hk HC Hpre).
intros ly4 S4 W4 regsY memY mdY Hpost.
apply (t3_cpy cx POST k ly3 S3 W3 regs3 mem3 md3 bs body again b ly4 S4 W4 regsY memY mdY HB Hk HC Hpost).
intros ly5 S5 W5 regsD memD mdD Hpm.
apply (t3_close cx POST k ly3 S3 W3 regs3 mem3 md3 bs body again b ly5 S5 W5 regsD memD mdD HB Hk HT HTX HC Hpm).
Qed.

(* ---- the turn ---- *)
Theorem scene_seg_S3 : seg_S3_turn_stmt (SK := SK) SEGS B ameter_triv WK scene_geom_asan.
Proof.
unfold seg_S3_turn_stmt. intros cx POST k HB Hk HT HTX.
unfold sc_from_T. intros ly3 S3 W3 regs3 mem3 md3 bs body again b HC.
pose proof HB as (HB0 & Hsp1eq).
pose proof HB0 as (HPRE & Hra0 & Hp10 & Hp11 & Hin0 & HfrS & Hnev0 & Hbb0 & HRO0 & Hsink0 & Hfd0 & Hfs0 & Hmo0).
pose proof HPRE as (HAR0 & Hrok0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & Hqt0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC as HCd.
unfold cut_T, sc_frame, sc_shr, sc_shbg, sc_open in HCd.
remember (sc_F SEGS scene_geom_asan cx) as F eqn:HFdef in *.
cbn [vat scene_geom_asan sgT_sp0 sgT_sp1 sgT_Fsp sgT_shF sgT_blki sgT_srcA sgT_srcB sgT_mac sgT_shexp
sgT_body sgT_again sgT_nprime sgT_got sgT_k sgT_decl sgT_n1 sgT_extra sgT_nagain sgT_expect sgT_Fb
sgT_nn sgT_body2 sgT_f8 sg_cid sg_off_blki sg_off_mac sg_off_expect sg_scene_n sg_nturns sg_sh_bg
sg_sh_blki_lo sg_sh_blki_hi sg_off_blk sg_blk_n sg_mac_n
RV_s0 RV_s1 RV_s2 RV_s3 RV_s4 RV_s5 RV_s6 RV_s7 RV_s8 RV_s9 RV_s10 RV_s11 fst snd] in HCd.
destruct HCd as (Hk0 & Hwhole & HJj & Habl & Hbbs & HBOK & HAOK & Hsepba & Hblen & Hgbody & Hja &
HFR & HSV & HSBG & HSHB & HOPB & HOPM & HIMG & HIN & HMAC &
Rsp0 & Rsp1 & Qfsp & Rsh & Rblki & Qsrca & Rsrcb & Qmac & Qshexp & Qbody & Qagain & Qnprime &
Rgot & Rk & Qdecl & Rn1 & Hextra & Hnag & Qexpect & Qfb & Qnn & Hbody2 & Rf8).
unfold RV_s0, RV_s1, RV_s2, RV_s3, RV_s4, RV_s5, RV_s6, RV_s7, RV_s8, RV_s9, RV_s10, RV_s11 in
Rsp0, Rsp1, Rsh, Rblki, Rsrcb, Rgot, Rk, Rn1, Hextra, Rf8.
pose proof HJj as (HJ & HfrS3 & Hmole).
pose proof HJ as (HAR3 & HLY3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresS & HstkS & _).
pose proof HstkS as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 HLY3) as (Eab & EFA & Eown).
assert (HinF : In (8, c_fpos cx) (frames S3)) by (rewrite HfrS3; left; reflexivity).
assert (EFAF : frame_addr ly3 8 (c_fpos cx) = F)
by (rewrite HFdef; unfold sc_F, rt_F; cbn [sg_cid scene_geom_asan]; apply EFA).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 HinF) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 HinF) as (HF32 & _ & HFpres & HFSpres).
pose proof (frm_off_imgP B ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 HinF) as HFimg.
rewrite EFAF in HF4096, HFceil, HFapp, HF32, HFpres, HFSpres, HFimg.
change (fs_frame_bytes 8) with 16384 in HF4096, HFceil, HFapp, HFpres, HFSpres, HFimg.
change (16384 / 8) with 2048 in HFSpres.
assert (HF8 : F mod 8 = 0) by (pose proof (Z.div_mod F 32 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
assert (HFdiv : 0 <= F / 8 <= F) by (split; [apply Z.div_pos; lia | pose proof (Z.mul_div_le F 8 ltac:(lia)); lia]).
assert (HFdiv2 : F / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (Hac8 : alloc_ceiling / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia).
assert (HFdiv3 : F / 8 + 2048 <= alloc_ceiling / 8)
  by (rewrite <- (t3_div8_add F 2048) by exact HF8; apply Z.div_le_mono; lia).
assert (Hsp1lo : spZ (c_regs cx) - 240 <= c_sp1 cx <= spZ (c_regs cx) - 224).
{ rewrite Hsp1eq. pose proof (sp1_facts (spZ (c_regs cx) - 224)) as X.
  destruct X as (X1 & _ & _); [lia | rewrite Zminus_mod, Hsp0al; reflexivity | lia]. }
assert (Hsp1al : c_sp1 cx mod 16 = 0).
{ rewrite Hsp1eq. pose proof (sp1_facts (spZ (c_regs cx) - 224)) as X.
  destruct X as (_ & _ & X3); [lia | rewrite Zminus_mod, Hsp0al; reflexivity | exact X3]. }
assert (HshLT : shadow_addr F + 2048 <= c_sp1 cx) by (unfold shadow_addr, SHADOW_OFF in *; unfold ASTACK in HSTK; lia).
assert (HshLO : 2147450880 <= shadow_addr F) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (Esh : forall i, SHADOW_OFF + (F + 32) / 8 + i = shadow_addr F + (4 + i)).
{ intros i. unfold shadow_addr. replace (F + 32) with (F + 8 * 4) by lia. rewrite t3_div8_add by exact HF8. lia. }
pose proof HBOK as (Hb4096 & Hbz & Hbceil & Hb16 & _ & _).
pose proof HAOK as (Ha4096 & Haz & Haceil & Ha16 & _ & _).
cbn [sg_scene_n scene_geom_asan] in Hbceil, Haceil, Hblen.
change (req_size 8904) with 8904 in Hbceil, Haceil.
pose proof HIMG as (HspE & HgpE & HtpE & HROD3).
assert (RK3 : t3_rk (spZ (c_regs cx)) (c_sp1 cx) (as_gp B) (as_tp B) F (scT_off k) k regs3).
{ unfold t3_rk. pose proof Hextra as Hx18. apply Forall_cons_iff in Hx18 as (X18 & _). cbn [fst snd vat] in X18.
  pose proof HspE as Hsp2. unfold spZ in Hsp2.
  split; [rewrite <- Hsp2; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  replace (F + 41) with (F + 32 + 9) by lia.
  repeat split; assumption. }
assert (Ho16 : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0) by (rewrite Zminus_mod, Hsp1al, Hsp0al; reflexivity).
assert (HkR : 0 <= k <= 342) by (cbn [sg_nturns scene_geom_asan] in Hk; lia).
assert (HTTd : A_TAIL_TRAILER + 12 <= F + 32 \/ F + 32 + 34 <= A_TAIL_TRAILER)
by (unfold A_TAIL_TRAILER; unfold off_img in HFimg; lia).
(* ---- run 1: +0x54c .. jal reac_ctrl_build_scene_step (+0x574) ---- *)
unfold cfg_at. cbn [sg_pc_t scene_geom_asan].
replace (w64 (BASE + AF_LLVMFuzzerTestOneInput + SEG_T_off)) with (Z_to_bv 64 (BASE + S3_K)) by (unfold w64, S3_K; f_equal; lia).
remember (Eimg (Ereg regs3 [Z_to_bv 64 body])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs3 [Z_to_bv 64 body]) E) by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 body) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), Rsp1; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = shadow_addr F) by (rewrite (EE 19%nat 19%bv eq_refl), Rsh; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS S3_K sr_atoms
  [YP09.mkRegion (Some 19%nat) 4 9 4 9 []; YP09.mkRegion (Some 9%nat) 0x58 0x60 0x60 0x60 [YP09.mkChunk 0x58 (CVal 8 (SOff 32 0))]]
  None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + S3_K)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|].
      split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFSpres o ltac:(lia))).
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0x58 8%N (SOff 32 0) body);
      [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword _ _ _ _ _ Qbody).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19. split; [split; [left; lia | exact I] | split; exact I].
  - unfold facts_ok; cbn; tauto. }
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hin & Ha). destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - rewrite U19 in Ha. right; right; right. exists 8, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFAF. change (fs_frame_bytes 8 / 8) with 2048. lia.
  - lia. }
rename ms into msA, HJ into HJA, HFr into HFrA. clear HF HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3.
prreg HS (1%bv : bv 5) Rra.
rewrite (EE 25%nat 25%bv eq_refl), Rblki in Ra0.
rewrite E32 in Ra1.
rewrite (EE 27%nat 27%bv eq_refl), Rn1 in Ra2.
rewrite (EE 22%nat 22%bv eq_refl), Rk in Ra3.
assert (KR1 : forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27]%bv -> getr (ms_regs msA) x = getr regs3 x)
  by (intros x Hx; exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) msA) regs3 [Z_to_bv 64 body]
        [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27]%bv HS HAG eq_refl x Hx)).
pose proof (t3_rk_kept _ _ _ _ _ _ _ _ _ KR1 RK3) as RKA.
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRA. cbn [ms_mem restrict] in HRA.
assert (ZA : forall j, 4 <= j < 9 -> aview SEGS (w_H W3) (ms_mem msA) (shadow_addr F + j) = Some (if j =? 8 then 2 else 0)).
{ intros j Hj. assert (Hj' : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia.
  destruct Hj' as [-> | [-> | [-> | [-> | ->]]]]; cbn [Z.eqb Pos.eqb];
  (eapply t3_shb; [exact HRA | exact U19 | cbn; tauto | lia]). }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
  aview SEGS (w_H W3) (ms_mem msA) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. eapply t3_kept_run; [exact HFrA | exact Ha |]. intros (r & Hin & Har).
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Har; [rewrite U19 in Har; lia | lia]. }
clear HFrA HRA.
pmkst HS.
assert (EspA : spZ (ms_regs msA) = c_sp1 cx) by (unfold spZ in *; rewrite (KR1 2%bv ltac:(cbn; tauto)); exact HspE).
assert (HOKT : scene_step_okZ (F + 32) body 8904 k = true).
{ unfold scene_step_okZ, SCENE_BYTES, SCENE_LAST.
  rewrite (proj2 (Z.eqb_neq (F + 32) 0)) by lia. rewrite (proj2 (Z.eqb_neq body 0)) by lia.
  rewrite Z.eqb_refl. rewrite (proj2 (Z.leb_le k 342)) by lia. reflexivity. }
assert (HRO0P : arodata_okP SEGS (@pa_relro_lo _ scene_listing PI_scene) (@pa_relro_hi _ scene_listing PI_scene) B
  (aview SEGS (w_H (c_W cx)) (c_mem cx))) by (rewrite <- HWRLO, <- HWRHI; exact HRO0).
pose proof (arodata_ok_journalP (SK := SK) SEGS _ _ pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJA HRO0P) as HRODA.
assert (ETT : A_TT (PI := PI_scene) = A_TAIL_TRAILER) by (vm_compute; reflexivity).
assert (U8s : forall j, nth j (u8s b) 0 = bv_unsigned (nth j b (Z_to_bv 8 0))).
{ intros j. unfold u8s. rewrite <- (map_nth (fun x : byte => bv_unsigned x) b (Z_to_bv 8 0) j). reflexivity. }
(* ---- reac_ctrl_build_scene_step (blk.i, body, 8904, k) ---- *)
rewrite pa_sigma_reac_ctrl_build_scene_step.
eapply SRr_bind.
{ eapply (BSS W3 (ms_regs msA) (ms_mem msA) _ (sw_stk WK) (spZ (c_regs cx)) (c_sp1 cx - spZ (c_regs cx)) []
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly3 S3 2 (F + 32) body 8904 k b HJA).
  - rewrite EspA. lia.
  - exact Ho16.
  - lia.
  - unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK. unfold ASTACK in HSTK. lia.
  - rewrite (KR1 3%bv ltac:(cbn; tauto)). exact HgpE.
  - rewrite (KR1 4%bv ltac:(cbn; tauto)). exact HtpE.
  - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - exact Ra3.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros _. unfold BLK_LEN, SCENE_BYTES, TT_LEN.
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]].
    + exists 8, (c_fpos cx). split; [left; reflexivity|]. split; [lia|]. rewrite EFAF.
      change (fs_frame_bytes 8) with 16384. lia.
    + intros a Ha.
      destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem msA) _ 8 (c_fpos cx) (proj1 HJA) HinF) as (_ & _ & HFpA & _).
      rewrite EFAF in HFpA. change (fs_frame_bytes 8) with 16384 in HFpA. exact (proj1 (HFpA a ltac:(lia))).
    + change 34 with (8 * 4 + 2). apply t3_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
      * intros i Hi. rewrite Esh, ZA by lia. destruct (Z.eqb_spec (4 + i) 8); [lia | reflexivity].
      * rewrite Esh, ZA by lia. reflexivity.
    + apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem msA) _ 8 (c_fpos cx) (F + 32) 34 (proj1 HJA) HinF);
      rewrite ?EFAF; [lia | change (fs_frame_bytes 8) with 16384; lia | lia].
    + exists body, 8904. split; [rewrite Habl; apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
      change (req_size 8904) with 8904. lia.
    + apply Nat2Z.inj. rewrite Hblen. reflexivity.
    + intros i Hi. rewrite KA.
      * destruct (Hgbody (Z.to_nat i) ltac:(unfold u8s; rewrite length_map; lia)) as (Hv & Hr).
        rewrite Z2Nat.id in Hv by lia. rewrite (aview_of_val_mem1 SEGS _ _ _ _ Hv Hr). rewrite U8s. reflexivity.
      * lia.
      * unfold zone2, off_img in Hbz. change (req_size 8904) with 8904 in Hbz.
        unfold shadow_addr, SHADOW_OFF in *. lia.
    + intros i Hi. rewrite ETT. exact (t3_tt_bytes W3 (ms_mem msA) HRODA i Hi).
    + rewrite ETT. exact (t3_tt_ra ly3 S3 W3 (ms_mem msA) _ (proj1 HJA)).
    + rewrite ETT. exact (t3_tt_hull ly3 S3 W3 (ms_mem msA) _ (proj1 HJA)).
    + rewrite ETT. exact HTTd. }
cbv beta. intros W2 c2 _ (-> & regsB & memB & mdB & -> & HJB & HPB & HfrB & HpresB & HOKB).
rewrite HOKT in HOKB. destruct HOKB as (Ha0B & HblkB).
pose proof (t3_rk_pres _ _ _ _ _ _ _ _ _ HPB RKA) as RKB.
pose proof RKB as (B2 & B3 & B4 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B25 & B27).
clear HS.
(* ---- run 2: +0x578 (bnez a0, a0 = 0) .. ---- *)
rewrite Rra.
set (n5 := bv_unsigned (nth 5 (scene_block b k) (Z_to_bv 8 0))) in *.
set (n7 := bv_unsigned (nth 7 (scene_block b k) (Z_to_bv 8 0))) in *.
set (n8 := bv_unsigned (nth 8 (scene_block b k) (Z_to_bv 8 0))) in *.
remember (Eimg (Ereg regsB [Z_to_bv 64 n5; Z_to_bv 64 n7; Z_to_bv 64 n8; Z_to_bv 64 body])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regsB r) by (intros n r Hn; subst E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG2 : env_agree 32 (Ereg regsB [Z_to_bv 64 n5; Z_to_bv 64 n7; Z_to_bv 64 n8; Z_to_bv 64 body]) E2)
  by (split; [intros n Hn; subst E2; apply Eimg_low; unfold A_TEXT; lia | subst E2; reflexivity]).
assert (E2_32 : ew E2 32 = Z_to_bv 64 n5) by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsB _ 0)).
assert (E2_33 : ew E2 33 = Z_to_bv 64 n7) by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsB _ 1)).
assert (E2_34 : ew E2 34 = Z_to_bv 64 n8) by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsB _ 2)).
assert (E2_35 : ew E2 35 = Z_to_bv 64 body) by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsB _ 3)).
assert (U9B : bv_unsigned (ew E2 9) = c_sp1 cx) by (rewrite (EE2 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; lia).
assert (U25B : bv_unsigned (ew E2 25) = F + 32) by (rewrite (EE2 25%nat 25%bv eq_refl), B25; unfold w64; apply unsigned_lit_small; lia).
assert (Hn5 : 0 <= n5 < 256) by (unfold n5; apply t3_bu_range).
assert (Hn7 : 0 <= n7 < 256) by (unfold n7; apply t3_bu_range).
assert (Hn8 : 0 <= n8 < 256) by (unfold n8; apply t3_bu_range).
assert (HspF : F + 16384 + 16384 <= c_sp1 cx) by (unfold ASTACK in HSTK; lia).
pose proof HJB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresB2 & _).
assert (KB : forall a, 0 <= a < 2 ^ 64 -> c_sp1 cx <= a -> aview SEGS (w_H W3) memB a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hsa. rewrite HfrB; [| exact Ha | rewrite EspA; lia | intros _; unfold BLK_LEN; lia].
  rewrite KA; [reflexivity | exact Ha | lia]. }
assert (Qbody2 : rdword (aview SEGS (w_H W3) memB) (c_sp1 cx + 0x58) = Some body).
{ rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [exact Qbody|]. intros j Hj. apply KB; lia. }
assert (Qdecl2 : rdword (aview SEGS (w_H W3) memB) (c_sp1 cx + 0x40) = Some (if k =? 0 then 0 else 8904)).
{ rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [exact Qdecl|]. intros j Hj. apply KB; lia. }
assert (Hdv : 0 <= (if k =? 0 then 0 else 8904) < 2 ^ 64) by (destruct (k =? 0); lia).
assert (HS0 : st_ok_pi SEGS VAL E2 (mkSS (S3_K + 44) sr_atoms
  [YP09.mkRegion (Some 25%nat) 0 34 0 0
     [YP09.mkChunk 4 (CVal 1 (SLit 0)); YP09.mkChunk 5 (CVal 1 (SOff 32 0));
      YP09.mkChunk 7 (CVal 1 (SOff 33 0)); YP09.mkChunk 8 (CVal 1 (SOff 34 0))];
   YP09.mkRegion (Some 9%nat) 0x40 0x60 0x40 0x48
     [YP09.mkChunk 0x40 (CVal 8 (SLit (if k =? 0 then 0 else 8904))); YP09.mkChunk 0x58 (CVal 8 (SOff 35 0))]]
  None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regsB (Z_to_bv 64 (BASE + (S3_K + 44))) memB (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U25B. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      * apply (chunk_ok_val SEGS E2 _ _ 4 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
        apply t3_vm1. rewrite (HblkB 4 ltac:(unfold BLK_LEN; lia)). reflexivity.
      * apply (chunk_ok_val SEGS E2 _ _ 5 1%N (SOff 32 0) n5);
        [cbn [sv_denot]; rewrite E2_32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
        apply t3_vm1. rewrite (HblkB 5 ltac:(unfold BLK_LEN; lia)). reflexivity.
      * apply (chunk_ok_val SEGS E2 _ _ 7 1%N (SOff 33 0) n7);
        [cbn [sv_denot]; rewrite E2_33, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
        apply t3_vm1. rewrite (HblkB 7 ltac:(unfold BLK_LEN; lia)). reflexivity.
      * apply (chunk_ok_val SEGS E2 _ _ 8 1%N (SOff 34 0) n8);
        [cbn [sv_denot]; rewrite E2_34, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
        apply t3_vm1. rewrite (HblkB 8 ltac:(unfold BLK_LEN; lia)). reflexivity.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9B. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HpresB2; unfold ASTACK in HSTK; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E2 _ _ 0x40 8%N (SLit (if k =? 0 then 0 else 8904)) (if k =? 0 then 0 else 8904));
        [reflexivity | cbn; destruct (k =? 0); lia | cbn; lia |].
        exact (val_mem_of_rdword _ _ _ _ _ Qdecl2).
      * apply (chunk_ok_val SEGS E2 _ _ 0x58 8%N (SOff 35 0) body);
        [cbn [sv_denot]; rewrite E2_35, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
        exact (val_mem_of_rdword _ _ _ _ _ Qbody2).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9B, U25B. split; [split; [left; lia | exact I] | split; exact I].
  - unfold facts_ok; cbn; tauto. }
assert (HS := st_ok_pi_pin_reg' E2 _ _ 10%bv 0 HS0 ltac:(cbn [restrict ms_regs mkst]; exact Ha0B) eq_refl).
clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
paj_run_shc RUNP RUNC HS HJB.
{ intros a (r & Hin & Ha). destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - lia.
  - rewrite U9B in Ha. left. unfold ASTACK in HSTK. lia. }
rename ms into msB0, HJB into HJB0, HFr into HFrB0. clear HF HG.
assert (En5 : n5 = scene_len k) by (unfold n5; rewrite scT_nth5; apply bu_lit; pose proof (scT_bnd k HkR); lia).
(* ---- the rest of the turn, from the check_step call site, shared by the two k arms.  The two arms reach this
   point with the same registers and the same memory facts; only the way the declared slot came to hold 8904
   differs (stored at k = 0, already there at k <> 0). ---- *)
assert (EXIT : forall (regsX : bvmap 5 word) (memX : word -> option byte) (mdX : Model),
  ajournal (SK := SK) SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(8, c_fpos cx)] ly3 S3 W3 memX mdX 2 ->
  t3_rk (spZ (c_regs cx)) (c_sp1 cx) (as_gp B) (as_tp B) F (scT_off k) k regsX ->
  getr regsX 10 = w64 (F + 32) -> getr regsX 11 = w64 body -> getr regsX 12 = w64 k ->
  getr regsX 1 = w64 (BASE + S3_K + 0x70) ->
  getr regsX 24 = w64 (scene_len k + scT_off k) -> getr regsX 26 = w64 (scene_len k) ->
  (forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ c_sp1 cx <= a) ->
     ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) -> ~ (F + 32 <= a < F + 32 + 34) ->
     ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
     aview SEGS (w_H W3) memX a = aview SEGS (w_H W3) mem3 a) ->
  (forall i, 0 <= i < 34 -> aview SEGS (w_H W3) memX (F + 32 + i)
     = Some (bv_unsigned (nth (Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))) ->
  (forall j, 4 <= j < 9 -> aview SEGS (w_H W3) memX (shadow_addr F + j) = Some (if j =? 8 then 2 else 0)) ->
  rdword (aview SEGS (w_H W3) memX) (c_sp1 cx + 0x40) = Some 8904 ->
  rdword (aview SEGS (w_H W3) memX) (c_sp1 cx + 0x48) = Some (F + 39) ->
  rdword (aview SEGS (w_H W3) memX) (c_sp1 cx + 0x50) = Some again ->
  SRr SEGS W3 (mkCfg (mkst regsX (Z_to_bv 64 (SIGMA SS_check_step)) memX (seg_rom SEGS)) mdX) POST).
{ clear HS HJB0 HFrB0 En5.
  intros regsX memX mdX HJX RKX Xa0 Xa1 Xa2 Xra Xs8 Xs10 KX XBLK XSH Xdecl Xsrc Xagain.
  apply (t3_from_pre_chk cx POST k ly3 S3 W3 regs3 mem3 md3 bs body again b ly3 S3 W3 regsX memX mdX
    HB ltac:(change (sg_nturns scene_geom_asan) with 343; lia) HT HTX HC).
  unfold t3_pre_chk. rewrite <- !HFdef.
  split; [exact HJX|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  split; [exact RKX|]. split; [exact Xa0|]. split; [exact Xa1|]. split; [exact Xa2|].
  split; [exact Xra|]. split; [exact Xs8|]. split; [exact Xs10|].
  split; [exact KX|]. split; [exact XBLK|]. split; [exact XSH|].
  split; [exact Xdecl|]. split; [exact Xsrc|]. exact Xagain. }
psrr_branch_pi RUNP BR HS.
{ (* k <> 0 *)
  rewrite branch_ne_U in Hc. rewrite (U_atom E2 22 k) in Hc;
  [| cbn [ew ewset]; rewrite (EE2 22%nat 22%bv eq_refl); exact B22 | lia].
  rewrite U_lit in Hc by lia. apply (proj1 (negb_true_iff _)) in Hc. apply (proj1 (Z.eqb_neq _ _)) in Hc.
  rename Hc into HkNZ.
  paj_run_shc RUNP RUNC HS HJB0.
  { intros a (r & Hin & Ha). destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha.
    - lia.
    - rewrite U9B in Ha. left. unfold ASTACK in HSTK. lia. }
  rename ms into msB1, HJB0 into HJB1, HFr into HFrB1. clear HF HG.
  assert (HU8 : U E2 (SAlu ALU_ADD (SAlu ALU_OR (SLit 0) (SExt false 8 (SOff 32 0))) (SOff 20 0))
    = scene_len k + scT_off k).
  { pose proof (scT_bnd k HkR) as Hb3.
    apply (t3_U_s8 E2 k (scT_off k));
    [ rewrite E2_32, En5; reflexivity
    | cbn [ew ewset]; rewrite (EE2 20%nat 20%bv eq_refl); exact B20
    | lia | lia | lia ]. }
  assert (HU2 : U E2 (SOff 18 0) = 8905)
    by (apply (U_atom E2 18 8905); [cbn [ew ewset]; rewrite (EE2 18%nat 18%bv eq_refl); exact B18 | lia]).
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_geu_U, HU8, HU2 in Hc.
    apply (proj1 (negb_true_iff _)) in Hc. apply (proj1 (Z.ltb_ge _ _)) in Hc.
    pose proof (scT_bnd k HkR). lia. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJB1.
  { intros a (r & Hin & Ha). destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha.
    - lia.
    - rewrite U9B in Ha. left. unfold ASTACK in HSTK. lia. }
  rename ms into msC, HJB1 into HJC, HFr into HFrC. clear HF HG.
  prreg HS (10%bv : bv 5) Ca0. prreg HS (11%bv : bv 5) Ca1. prreg HS (12%bv : bv 5) Ca2.
  prreg HS (1%bv : bv 5) Cra.
  rewrite (EE2 25%nat 25%bv eq_refl), B25 in Ca0.
  rewrite E2_35 in Ca1.
  rewrite (EE2 22%nat 22%bv eq_refl), B22 in Ca2.
  assert (KR2 : forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27]%bv -> getr (ms_regs msC) x = getr regsB x)
    by (intros x Hx; exact (regs_kept_of_st_ok SEGS E2 _ (restrict (w_H W3) msC) regsB
          [Z_to_bv 64 n5; Z_to_bv 64 n7; Z_to_bv 64 n8; Z_to_bv 64 body]
          [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27]%bv HS HAG2 eq_refl x Hx)).
  idtac.
  pose proof (t3_rk_kept _ _ _ _ _ _ _ _ _ KR2 RKB) as RKC.
  pose proof RKC as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G25 & G27).
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) ->
    aview SEGS (w_H W3) (ms_mem msC) a = aview SEGS (w_H W3) memB a).
  { intros a Ha Hn.
    assert (K1 : aview SEGS (w_H W3) (ms_mem msC) a = aview SEGS (w_H W3) (ms_mem msB1) a).
    { eapply t3_kept_run; [exact HFrC | exact Ha |]. intros (r & Hin & Har).
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Har;
      [lia | rewrite U9B in Har; lia]. }
    assert (K2 : aview SEGS (w_H W3) (ms_mem msB1) a = aview SEGS (w_H W3) (ms_mem msB0) a).
    { eapply t3_kept_run; [exact HFrB1 | exact Ha |]. intros (r & Hin & Har).
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Har;
      [lia | rewrite U9B in Har; lia]. }
    rewrite K1, K2. eapply t3_kept_run; [exact HFrB0 | exact Ha |]. intros (r & Hin & Har).
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Har;
    [lia | rewrite U9B in Har; lia]. }
  clear HFrC HFrB1 HFrB0.
  pmkst HS.
  assert (EspC : spZ (ms_regs msC) = c_sp1 cx)
    by (unfold spZ; rewrite G2; unfold w64; rewrite unsigned_lit_small by lia; lia).
  assert (Es0C : s0Z (ms_regs msC) = spZ (c_regs cx))
    by (unfold s0Z; rewrite G8; unfold w64; rewrite unsigned_lit_small by lia; lia).
  assert (Hr24 : bv_unsigned (getr (ms_regs msC) 24) = scene_len k + scT_off k).
  { lazymatch type of HS with
    | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms 24%bv HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) 24%bv) in change (sr_get (ss_regs ss) 24%bv) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
    | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms 24%bv HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) 24%bv) in change (sr_get (ss_regs ss) 24%bv) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
    end.
    rewrite Hr. fold (U E2 (SAlu ALU_ADD (SAlu ALU_OR (SLit 0) (SExt false 8 (SOff 32 0))) (SOff 20 0))). exact HU8. }
  assert (Hr26 : bv_unsigned (getr (ms_regs msC) 26) = scene_len k).
  { lazymatch type of HS with
    | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms 26%bv HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) 26%bv) in change (sr_get (ss_regs ss) 26%bv) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
    | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms 26%bv HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) 26%bv) in change (sr_get (ss_regs ss) 26%bv) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
    end.
    rewrite Hr. fold (U E2 (SAlu ALU_OR (SLit 0) (SExt false 8 (SOff 32 0)))).
    rewrite t3_U_or0, (t3_U_zext8 E2 32 n5 E2_32 Hn5). exact En5. }
  pose proof (st_ok_region_nth E2 _ _ 1 _ HS eq_refl) as HSK. cbn [ms_mem restrict] in HSK.
  assert (ES3K : S3_K = 1356) by (unfold S3_K; reflexivity).
  assert (HbndC : 0 <= scene_len k + scT_off k < 2 ^ 64) by (pose proof (scT_bnd k HkR); lia).
  assert (HlenC : 0 <= scene_len k < 256) by (pose proof (scT_bnd k HkR); lia).
  (* the combined keep: every byte outside the decl slot, BSS's stack window, blk.i and blk.i's shadow is mem3's *)
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) ->
    ~ (spZ (ms_regs msA) - SCENE_STEP_WIN <= a < spZ (ms_regs msA)) ->
    ~ (F + 32 <= a < F + 32 + 34) -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
    aview SEGS (w_H W3) (ms_mem msC) a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha Hd Hw Hb Hs. rewrite (KC a Ha Hd).
    rewrite (HfrB a Ha Hw ltac:(intros _; unfold BLK_LEN; lia)). exact (KA a Ha Hs). }
  assert (HwinV : SCENE_STEP_WIN = 4144) by (unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK; reflexivity).
  assert (HshW : shadow_addr F + 9 + 4144 <= c_sp1 cx)
    by (unfold shadow_addr, SHADOW_OFF in *; unfold ASTACK in HSTK; lia).
  assert (HcB : c_sp1 cx + 0x60 <= 2 ^ 64) by (unfold ASTACK in HSTK; lia).
  (* blk.i's shadow cells are outside blk.i: F is app memory (in_app), low (shadow above) or high (shadow below) *)
  assert (HshNB : forall j, 4 <= j < 9 -> ~ (F + 32 <= shadow_addr F + j < F + 32 + 34)).
  { intros j Hj. pose proof HFapp as HA.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, alloc_ceiling in HA. unfold shadow_addr, SHADOW_OFF.
    destruct HA as (HA0 & [HA1 | (HA2 & HA3)]); lia. }
  apply (EXIT (ms_regs msC) (ms_mem msC) _).
  - exact HJC.
  - exact RKC.
  - exact Ca0.
  - exact Ca1.
  - exact Ca2.
  - rewrite Cra. unfold w64. rewrite ES3K. f_equal; lia.
  - (* s8 *) apply bv_eq. rewrite Hr24. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by exact HbndC. reflexivity.
  - (* s10 *) apply bv_eq. rewrite Hr26. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
  - (* keep *) intros a Ha Hreg Hd Hb Hs. apply KALL; try assumption.
    rewrite EspA. unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK. unfold ASTACK in HSTK.
    destruct Hreg as [Hreg | Hreg]; lia.
  - (* blk.i bytes *) intros i Hi. rewrite (KC (F + 32 + i) ltac:(lia) ltac:(lia)).
    exact (HblkB i ltac:(unfold BLK_LEN; lia)).
  - (* blk.i shadow *) intros j Hj.
    rewrite (KC (shadow_addr F + j) ltac:(lia) ltac:(lia)).
    rewrite (HfrB (shadow_addr F + j) ltac:(lia) ltac:(rewrite EspA, HwinV; lia)
      ltac:(intros _; unfold BLK_LEN; exact (HshNB j Hj))).
    exact (ZA j Hj).
  - (* decl *)
    assert (Hdv8 : (if k =? 0 then 0 else 8904) = 8904) by (rewrite (proj2 (Z.eqb_neq k 0) HkNZ); reflexivity).
    rewrite <- Hdv8. apply rdword_of_val_mem; [| destruct (k =? 0); lia].
    exact (field_of_region E2 _ 9 (c_sp1 cx) _ 64 96 64 72 0x40 8%N (SLit (if k =? 0 then 0 else 8904))
      (if k =? 0 then 0 else 8904) HSK U9B ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  - (* srcA *) rewrite (rdword_ext (aview SEGS (w_H W3) mem3)).
    + replace (F + 39) with (F + 32 + 7) by lia. exact Qsrca.
    + intros j Hj. apply KALL; [lia | lia | rewrite EspA; unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK; unfold ASTACK in HSTK; lia | lia
        | unfold shadow_addr, SHADOW_OFF in *; lia].
  - (* again *) rewrite (rdword_ext (aview SEGS (w_H W3) mem3)).
    + exact Qagain.
    + intros j Hj. apply KALL; [lia | lia | rewrite EspA; unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK; unfold ASTACK in HSTK; lia | lia
        | unfold shadow_addr, SHADOW_OFF in *; lia]. }
{ (* k = 0 *)
  rewrite branch_ne_U in Hc. rewrite (U_atom E2 22 k) in Hc;
  [| cbn [ew ewset]; rewrite (EE2 22%nat 22%bv eq_refl); exact B22 | lia].
  rewrite U_lit in Hc by lia. apply (proj1 (negb_false_iff _)) in Hc. apply (proj1 (Z.eqb_eq _ _)) in Hc.
  rename Hc into HkZ.
  paj_run_shc RUNP RUNC HS HJB0.
  { intros a (r & Hin & Ha). destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha.
    - lia.
    - rewrite U9B in Ha. left. unfold ASTACK in HSTK. lia. }
  rename ms into msB1, HJB0 into HJB1, HFr into HFrB1. clear HF HG.
  assert (HU8 : U E2 (SAlu ALU_ADD (SAlu ALU_OR (SLit 0) (SExt false 8 (SOff 32 0))) (SOff 20 0))
    = scene_len k + scT_off k).
  { pose proof (scT_bnd k HkR) as Hb3.
    apply (t3_U_s8 E2 k (scT_off k));
    [ rewrite E2_32, En5; reflexivity
    | cbn [ew ewset]; rewrite (EE2 20%nat 20%bv eq_refl); exact B20
    | lia | lia | lia ]. }
  assert (HU2 : U E2 (SOff 18 0) = 8905)
    by (apply (U_atom E2 18 8905); [cbn [ew ewset]; rewrite (EE2 18%nat 18%bv eq_refl); exact B18 | lia]).
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_geu_U, HU8, HU2 in Hc.
    apply (proj1 (negb_true_iff _)) in Hc. apply (proj1 (Z.ltb_ge _ _)) in Hc.
    pose proof (scT_bnd k HkR). lia. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJB1.
  { intros a (r & Hin & Ha). destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha.
    - lia.
    - rewrite U9B in Ha. left. unfold ASTACK in HSTK. lia. }
  rename ms into msC, HJB1 into HJC, HFr into HFrC. clear HF HG.
  prreg HS (10%bv : bv 5) Ca0. prreg HS (11%bv : bv 5) Ca1. prreg HS (12%bv : bv 5) Ca2.
  prreg HS (1%bv : bv 5) Cra.
  rewrite (EE2 25%nat 25%bv eq_refl), B25 in Ca0.
  rewrite E2_35 in Ca1.
  rewrite (EE2 22%nat 22%bv eq_refl), B22 in Ca2.
  assert (KR2 : forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27]%bv -> getr (ms_regs msC) x = getr regsB x)
    by (intros x Hx; exact (regs_kept_of_st_ok SEGS E2 _ (restrict (w_H W3) msC) regsB
          [Z_to_bv 64 n5; Z_to_bv 64 n7; Z_to_bv 64 n8; Z_to_bv 64 body]
          [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27]%bv HS HAG2 eq_refl x Hx)).
  idtac.
  pose proof (t3_rk_kept _ _ _ _ _ _ _ _ _ KR2 RKB) as RKC.
  pose proof RKC as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G25 & G27).
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) ->
    aview SEGS (w_H W3) (ms_mem msC) a = aview SEGS (w_H W3) memB a).
  { intros a Ha Hn.
    assert (K1 : aview SEGS (w_H W3) (ms_mem msC) a = aview SEGS (w_H W3) (ms_mem msB1) a).
    { eapply t3_kept_run; [exact HFrC | exact Ha |]. intros (r & Hin & Har).
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Har;
      [lia | rewrite U9B in Har; lia]. }
    assert (K2 : aview SEGS (w_H W3) (ms_mem msB1) a = aview SEGS (w_H W3) (ms_mem msB0) a).
    { eapply t3_kept_run; [exact HFrB1 | exact Ha |]. intros (r & Hin & Har).
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Har;
      [lia | rewrite U9B in Har; lia]. }
    rewrite K1, K2. eapply t3_kept_run; [exact HFrB0 | exact Ha |]. intros (r & Hin & Har).
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Har;
    [lia | rewrite U9B in Har; lia]. }
  clear HFrC HFrB1 HFrB0.
  pmkst HS.
  assert (EspC : spZ (ms_regs msC) = c_sp1 cx)
    by (unfold spZ; rewrite G2; unfold w64; rewrite unsigned_lit_small by lia; lia).
  assert (Es0C : s0Z (ms_regs msC) = spZ (c_regs cx))
    by (unfold s0Z; rewrite G8; unfold w64; rewrite unsigned_lit_small by lia; lia).
  assert (Hr24 : bv_unsigned (getr (ms_regs msC) 24) = scene_len k + scT_off k).
  { lazymatch type of HS with
    | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms 24%bv HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) 24%bv) in change (sr_get (ss_regs ss) 24%bv) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
    | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms 24%bv HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) 24%bv) in change (sr_get (ss_regs ss) 24%bv) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
    end.
    rewrite Hr. fold (U E2 (SAlu ALU_ADD (SAlu ALU_OR (SLit 0) (SExt false 8 (SOff 32 0))) (SOff 20 0))). exact HU8. }
  assert (Hr26 : bv_unsigned (getr (ms_regs msC) 26) = scene_len k).
  { lazymatch type of HS with
    | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms 26%bv HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) 26%bv) in change (sr_get (ss_regs ss) 26%bv) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
    | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms 26%bv HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) 26%bv) in change (sr_get (ss_regs ss) 26%bv) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
    end.
    rewrite Hr. fold (U E2 (SAlu ALU_OR (SLit 0) (SExt false 8 (SOff 32 0)))).
    rewrite t3_U_or0, (t3_U_zext8 E2 32 n5 E2_32 Hn5). exact En5. }
  pose proof (st_ok_region_nth E2 _ _ 1 _ HS eq_refl) as HSK. cbn [ms_mem restrict] in HSK.
  assert (ES3K : S3_K = 1356) by (unfold S3_K; reflexivity).
  assert (HbndC : 0 <= scene_len k + scT_off k < 2 ^ 64) by (pose proof (scT_bnd k HkR); lia).
  assert (HlenC : 0 <= scene_len k < 256) by (pose proof (scT_bnd k HkR); lia).
  (* the combined keep: every byte outside the decl slot, BSS's stack window, blk.i and blk.i's shadow is mem3's *)
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) ->
    ~ (spZ (ms_regs msA) - SCENE_STEP_WIN <= a < spZ (ms_regs msA)) ->
    ~ (F + 32 <= a < F + 32 + 34) -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
    aview SEGS (w_H W3) (ms_mem msC) a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha Hd Hw Hb Hs. rewrite (KC a Ha Hd).
    rewrite (HfrB a Ha Hw ltac:(intros _; unfold BLK_LEN; lia)). exact (KA a Ha Hs). }
  assert (HwinV : SCENE_STEP_WIN = 4144) by (unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK; reflexivity).
  assert (HshW : shadow_addr F + 9 + 4144 <= c_sp1 cx)
    by (unfold shadow_addr, SHADOW_OFF in *; unfold ASTACK in HSTK; lia).
  assert (HcB : c_sp1 cx + 0x60 <= 2 ^ 64) by (unfold ASTACK in HSTK; lia).
  (* blk.i's shadow cells are outside blk.i: F is app memory (in_app), low (shadow above) or high (shadow below) *)
  assert (HshNB : forall j, 4 <= j < 9 -> ~ (F + 32 <= shadow_addr F + j < F + 32 + 34)).
  { intros j Hj. pose proof HFapp as HA.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, alloc_ceiling in HA. unfold shadow_addr, SHADOW_OFF.
    destruct HA as (HA0 & [HA1 | (HA2 & HA3)]); lia. }
  apply (EXIT (ms_regs msC) (ms_mem msC) _).
  - exact HJC.
  - exact RKC.
  - exact Ca0.
  - exact Ca1.
  - exact Ca2.
  - rewrite Cra. unfold w64. rewrite ES3K. f_equal; lia.
  - (* s8 *) apply bv_eq. rewrite Hr24. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by exact HbndC. reflexivity.
  - (* s10 *) apply bv_eq. rewrite Hr26. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
  - (* keep *) intros a Ha Hreg Hd Hb Hs. apply KALL; try assumption.
    rewrite EspA. unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK. unfold ASTACK in HSTK.
    destruct Hreg as [Hreg | Hreg]; lia.
  - (* blk.i bytes *) intros i Hi. rewrite (KC (F + 32 + i) ltac:(lia) ltac:(lia)).
    exact (HblkB i ltac:(unfold BLK_LEN; lia)).
  - (* blk.i shadow *) intros j Hj.
    rewrite (KC (shadow_addr F + j) ltac:(lia) ltac:(lia)).
    rewrite (HfrB (shadow_addr F + j) ltac:(lia) ltac:(rewrite EspA, HwinV; lia)
      ltac:(intros _; unfold BLK_LEN; exact (HshNB j Hj))).
    exact (ZA j Hj).
  - (* decl, k = 0: the store at +0x590 wrote (blk[7] << 8) | blk[8] = 0x22c8 = 8904 *)
    assert (HUd : U E2 (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 33 0)) (SLit 8)) (SExt false 8 (SOff 34 0)))
      = 8904).
    { rewrite (t3_U_or_bytes E2 _ _ n7 n8).
      - unfold n7, n8. rewrite HkZ, scT_nth7_0, scT_nth8_0, !Z_to_bv_unsigned. unfold bv_wrap.
        change (bv_modulus 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
      - apply (t3_U_sll8 E2 _ n7); [exact (t3_U_zext8 E2 33 n7 E2_33 Hn7) | exact Hn7].
      - exact (t3_U_zext8 E2 34 n8 E2_34 Hn8).
      - exact Hn7.
      - exact Hn8. }
    assert (Hden : sv_denot E2 (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 33 0)) (SLit 8))
      (SExt false 8 (SOff 34 0))) = Z_to_bv 64 8904).
    { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite (Z.mod_small 8904) by lia.
      fold (U E2 (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 33 0)) (SLit 8)) (SExt false 8 (SOff 34 0)))).
      exact HUd. }
    apply rdword_of_val_mem; [| lia].
    exact (field_of_region E2 _ 9 (c_sp1 cx) _ 64 96 64 72 0x40 8%N
      (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 33 0)) (SLit 8)) (SExt false 8 (SOff 34 0))) 8904
      HSK U9B ltac:(cbn; tauto) Hden ltac:(cbn; lia) ltac:(cbn; lia)).
  - (* srcA *) rewrite (rdword_ext (aview SEGS (w_H W3) mem3)).
    + replace (F + 39) with (F + 32 + 7) by lia. exact Qsrca.
    + intros j Hj. apply KALL; [lia | lia | rewrite EspA; unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK; unfold ASTACK in HSTK; lia | lia
        | unfold shadow_addr, SHADOW_OFF in *; lia].
  - (* again *) rewrite (rdword_ext (aview SEGS (w_H W3) mem3)).
    + exact Qagain.
    + intros j Hj. apply KALL; [lia | lia | rewrite EspA; unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK; unfold ASTACK in HSTK; lia | lia
        | unfold shadow_addr, SHADOW_OFF in *; lia]. }
Qed.
End h.
End d.
