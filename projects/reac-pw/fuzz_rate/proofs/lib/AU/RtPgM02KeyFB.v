(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyBase.v, RPgM02KeyI.v and RPgM02KeyV.v
   at 595d8c5dd1b5 (the value language of the value entry's address and of a `lw`, the expect_value cases, the
   shadow entry over the value entry, the value dispatch, the Int arm and the value tail),
   proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyF.v at 7e8cf15c304a (the Float arm: the size test, the `flw` and
   pod_nearest) and proofs/reac-pw/fuzz_rate/lib/A/RtPgScanF.v at 22306b8175e6 (the pairs of the scan across a
   key) for reac-pw/fuzz_rate image A: role's pcs become rate's, the shadow base is rate's s2 (atom 18), role's Role
   answers become Rate.expect_value / Rate.rate_of_pairs, role's value tail (a bound test and check_role) becomes
   rate's check_rate on the hz cell, the out cell is R+0x158, the `flw` is stepped by YA0n.SRr_step, and the key
   compare (the spills, the strcmp wrapper, the mismatch exit to O) is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgM02Key.v at 48d3cf0d8e40 (its Float arm, the
   m2kf_* lemmas and m2k_float) for image B (fuzz_rate.asan-ubsan): image B's pcs (FLT 0x82d70, the `flw` 0x82dbc,
   pod_nearest 0x83fcc called from 0x82dc4, JN 0x82dd0, MAL 0x82de0); the cuts are lib/AU/RtPgSegB.v's (rs_ -> rsb_)
   and the interfaces lib/AU/RtPgM02KitB.v's (m2k_ -> m2kb_); the shadow base is s4 (atom 20); image B forms the
   addresses of the size and of the body from a7 + s8 and a4 + s8 (image A: one register), so the walk's entry state
   carries the engine's alias facts for the two sums (atom 10 = &ent[v] plus a constant) and the real-frame cell
   R+0x138 = 0x4018; s8 changes at 0x82d90, so the size walk keeps the registers m2kfb_L (cs_eq) instead of every
   callee-saved register; pod_nearest's out cell is R+0x198 (rt_seg_pre's hi_rz [(0x198, 16)] at rate_himg_B);
   pod_nearest's contract is the Section hypothesis HNEAR (image A: m2k_near from lib/A/RtPgNearA.v). *)
(* reac-pw/fuzz_rate, image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded code bytes are the pin's): the
   Float arm of LLVMFuzzerTestOneInput's segment M02, FLT 0x82d70 -> MAL 0x82de0 / JN 0x82dd0. Proves no function
   (kind: segment lemma): m2kb_float, lib/AU/RtPgM02KitB.v's m2kb_float_stmt.

   THE CODE (lib/AU/RtPgM02BaseB.v lists it with every pc):
     0x82d70 .. 0x82d80  a1 := a7 + s8 (= &ent[v] + 4) and its shadow check (slow block 0x83424)
     0x82d84 .. 0x82d8c  lw a0,4(a0) = the size; size < 4 -> MAL                              m2kfb_walk1
     0x82d90 .. 0x82db8  s8 := a4 + s8; a0 := s8 + R+0x138 (0x4018) + 4 and its shadow check
                         (slow block 0x834e4); a0 := s8 + 0x401c (= &ent[v] + 8)
     0x82dbc             flw fa0,0(a0) (the body word)                                         m2kfb_flw
     0x82dc0 .. 0x82dc4  a0 := R + 0x198; jal pod_nearest 0x83fcc, ra = 0x82dc8              m2kfb_walk2
     0x82dc8 .. 0x82dcc  beqz a0 -> MAL; lw a2,0x198(s1); falls into JN 0x82dd0              m2kfb_walk3

   SECTION HYPOTHESES of m2kb_float: MTL : ameter_laws MT, and HNEAR : pod_nearest's contract
   (RtPgCSpec.rt_pod_nearest_specX at M2B_NEAREST) at every float state; the float state the `flw` leaves is not the
   cut's. lib/AU/RtPgNearB.v rt_pod_nearest_B instantiates it. The frame's laws come from the kernel theorem
   YG0q.AR_laws_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YA0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Nearest Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSegB RtPgMemB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgCheck RtPgM02BaseB RtPgM02KitB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ===================================== the float state after the `flw` ===================================== *)
(* 0x82dbc flw fa0,0(a0): f10 holds the NaN-boxed binary32 b, the rest of f is kept [A's m2kf_fx4 and its lemmas] *)
Definition m2kfb_fx4 (f : YK11.FPState) (b : Z) : YK11.FPState :=
YK11.mkFP (bvmap_set (Z_to_bv 5 10) (nan_box (Z_to_bv 32 b)) (@fp_regs f)) (@fp_csr f).

Lemma m2kfb_fxk_trans : forall ks ks' f g h,
rt_fxk ks f g -> rt_fxk ks' g h -> (forall z, In z ks' -> In z ks) -> rt_fxk ks f h.
Proof.
intros ks ks' f g h (Hg & _) (Hh & Hcsr) Hin. split; [|exact Hcsr].
intros k Hk. rewrite (Hh k ltac:(intros Hc; exact (Hk (Hin _ Hc)))). exact (Hg k Hk).
Qed.

Lemma m2kfb_fxk_set : forall ks f g b, In 10 ks -> rt_fxk ks f g -> rt_fxk ks f (m2kfb_fx4 g b).
Proof.
intros ks f g b Hr (Hg & Hcsr). split; [|exact Hcsr].
intros k Hk. unfold m2kfb_fx4. cbn [fp_regs].
destruct (base.decide (k = Z_to_bv 5 10)) as [->|Hne]; [exfalso; exact (Hk Hr)|].
change (bvmap_set (Z_to_bv 5 10) (nan_box (Z_to_bv 32 b)) (@fp_regs g))
  with (regupd (@fp_regs g) (Z_to_bv 5 10) (nan_box (Z_to_bv 32 b))).
rewrite (regupd_other (@fp_regs g) (Z_to_bv 5 10) (nan_box (Z_to_bv 32 b)) k Hne). exact (Hg k Hk).
Qed.

Lemma m2kfb_f10 : forall f b, Sem.reg_get (@fp_regs (m2kfb_fx4 f b)) (Z_to_bv 5 10) = Sem.nan_box (Z_to_bv 32 b).
Proof. intros f b. unfold m2kfb_fx4. cbn [fp_regs]. apply regupd_same. Qed.

(* the low 4 bytes of an 8-byte cell *)
Lemma m2kfb_val_lo4 : forall m a v, val_mem rsegs m a 8 v -> val_mem rsegs m a 4 (v mod 2 ^ 32).
Proof.
intros m a v H k Hk. rewrite (H k ltac:(lia)). f_equal.
rewrite !rtmb_le_byte_bv by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
apply Z.bits_inj'. intros i Hi. destruct (Z_lt_le_dec i 8) as [Hl|Hg].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* ===================================== the registers the size walk keeps ===================================== *)
(* sp, gp, tp, s0, s1, s3, s4, s5, s6, s7 and s10: every callee-saved register the cuts name; s8 (x24) is not kept,
   0x82d90 overwrites it *)
Definition m2kfb_L : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 26]%bv.

Lemma m2kfb_L_cs : forall r, In r m2kfb_L -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [m2kfb_L In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.

Lemma m2kfb_L5_sub : forall r, In r m2kb_L5 -> In r m2kfb_L.
Proof. intros r Hr. cbv [m2kb_L5 m2kfb_L In] in Hr |- *. tauto. Qed.

Ltac m2kfb_inL := cbv [m2kfb_L In]; repeat (first [left; apply bv_eq; reflexivity | right]).

Lemma m2kfb_L_234 : forall ra rb, cs_eq m2kfb_L ra rb ->
forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr rb (Z_to_bv 5 r) = getr ra (Z_to_bv 5 r).
Proof. intros ra rb H r [->|[->| ->]]; apply H; m2kfb_inL. Qed.

(* ===================================== the entry state of the size walk ===================================== *)
(* The size and the body word of the value entry at atom 10 = &ent[v] (the extra atoms 32 and 33), and the real-frame
   cell R+0x138 = 0x4018 at atom 9 = R. *)
Definition m2kfb_R10 : YP09.region :=
YP09.mkRegion (Some 10%nat) 4 12 0 0 [YP09.mkChunk 4 (CVal 4 (SOff 32 0)); YP09.mkChunk 8 (CVal 4 (SOff 33 0))].
Definition m2kfb_R9 : YP09.region := m2b_frame 0x138 0x140 0 0 [YP09.mkChunk 0x138 (CVal 8 (SLit 0x4018))].
(* the engine's alias facts: a7 + s8 = &ent[v] + 4 (0x82d70) and a4 + s8 = &ent[v] - 0x4014 (0x82d90), with
   a7 = pp + 0x4018 (atom 17), s8 = 104 v (atom 24), a4 = pp (atom 14) *)
Definition m2kfb_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 17 0) (SOff 24 0), SOff 10 4);
  (SAlu ALU_ADD (SOff 14 0) (SOff 24 0), SOff 10 (-0x4014)) ].
(* atom 9 is s1 = R, atom 20 is s4 = the runtime's shadow offset, atom 10 is a0 = &ent[v]; every bound a numeral *)
Definition m2kfb_facts : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
          (10%nat, mkAF 4096 0x7fffff800000 0) ] [] m2kfb_alias.

Lemma m2kfb_facts_ok : forall E R a p s,
bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 20) = SHADOW_OFF ->
ew E 10 = Z_to_bv 64 a -> ew E 17 = Z_to_bv 64 (p + 0x4018) -> ew E 24 = Z_to_bv 64 s -> ew E 14 = Z_to_bv 64 p ->
a = p + 0x4014 + s -> 0 <= p -> 0 <= s -> 4096 <= a <= 0x7fffff800000 ->
facts_ok E m2kfb_facts.
Proof.
intros E R a p s H9 HR Hal H20 E10 E17 E24 E14 Ha Hp Hs Hab.
assert (H10 : bv_unsigned (ew E 10) = a) by (rewrite E10; apply unsigned_lit_small; lia).
split; [|split; [exact I|]].
- cbn [m2kfb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite H9, H20, H10. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
  repeat split; try lia.
  all: try apply Z.mod_1_r.
- cbn [m2kfb_facts f_alias alias_ok m2kfb_alias]. repeat split; apply U_inj.
  + rewrite U_SAlu, (U_atom _ 17 (p + 0x4018) E17), (U_atom _ 24 s E24), (U_atom_off _ 10 a 4 E10) by lia.
    cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
  + rewrite U_SAlu, (U_atom _ 14 p E14), (U_atom _ 24 s E24), (U_atom_off _ 10 a (-0x4014) E10) by lia.
    cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ===================================== the `flw` ===================================== *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* 0x82dbc flw fa0,0(a0) with a0 = a and the 4 bytes at a holding b; the walk goes on at 0x82dc0 [A's m2kf_flw] *)
Lemma m2kfb_flw : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) a b,
getr regs (Z_to_bv 5 10) = Z_to_bv 64 a ->
val_mem rsegs (mrestrict (w_H W) mem) a 4 b -> 0 <= b < 2 ^ 32 ->
(forall md', same_but_materialized md md' -> SRr rsegs W (@cfg_at (m2kfb_fx4 fx b) rsegs 0x82dc0 regs mem md') Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x82dbc) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q a b H10 Hval Hb HK.
assert (Hrd : rdn rsegs (mrestrict (w_H W) mem) (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 b)).
{ apply (proj2 (YP09.rdn_mbytes rsegs _ _ _ _)). split; [apply length_Z_to_le_bytes|].
  intros i Hi. rewrite (Hval i Hi).
  rewrite (nth_error_nth' (Z_to_le_bytes 4 b) (Z_to_bv 8 0)) by (rewrite length_Z_to_le_bytes; exact Hi).
  rewrite rtmb_nth_le_bytes by exact Hi. rewrite rtmb_le_byte_bv by exact Hi. reflexivity. }
assert (Hw : bv_extract 0 32 (le_bytes_to_word (Z_to_le_bytes 4 b)) = Z_to_bv 32 b).
{ rewrite le_bytes_to_word_Z, Cursor.bytes_le_to_Z_Z_to_le_bytes.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small b (2 ^ 32)) by lia.
  apply bv_eq. rewrite bv_extract_unsigned, unsigned_lit_small by lia. rewrite Z_to_bv_unsigned.
  try (f_equal; apply Z.shiftr_0_r). }
eapply (SRr_step rsegs ck_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (YK0o.fp_step_flw fx rsegs regs (Z_to_bv 64 0x82dbc) (mrestrict (w_H W) mem) (seg_rom rsegs)
    (Z_to_bv 32 0x52507) (Z_to_bv 5 10) (Z_to_bv 5 10) (Z_to_bv 12 0) (Z_to_bv 64 a) (Z_to_le_bytes 4 b));
  [ reflexivity | vm_refl_bv | vm_compute; reflexivity | vm_refl_bv
  | rewrite H10; replace (bv_signed (Z_to_bv 12 0)) with 0 by reflexivity; apply v_addi_0
  | exact Hrd ].
- intros md' Hsame. rewrite unrestrict_mkst_mrestrict, Hw.
  replace (v_addi (Z_to_bv 64 0x82dbc) 4) with (w64 0x82dc0) by reflexivity.
  exact (HK md' Hsame).
Qed.
End s.

(* ===================================== the three runs ===================================== *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HNEAR : forall fy : YK11.FPState, rt_pod_nearest_specX (fx := fy) rsegs B MT M2B_NEAREST.

(* 0x82d70 .. 0x82db8: the size test, then the body's address; stop at the `flw` 0x82dbc, which m2kfb_flw steps.
   a0 = a0v = &ent[v] = p + 0x4014 + s with a7 = p + 0x4018, s8 = s, a4 = p *)
Lemma m2kfb_walk1 : forall (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2
  a0v p s sz bw,
rsb_pre rsegs B cx -> rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)) -> getr regs2 (Z_to_bv 5 20) = w64 SHADOW_OFF ->
getr regs2 (Z_to_bv 5 10) = w64 a0v -> getr regs2 (Z_to_bv 5 17) = w64 (p + 0x4018) ->
getr regs2 (Z_to_bv 5 24) = w64 s -> getr regs2 (Z_to_bv 5 14) = w64 p ->
a0v = p + 0x4014 + s -> 0 <= p -> 0 <= s ->
4096 <= a0v -> a0v + 16 <= alloc_ceiling ->
(a0v + 16 <= kLowShadowBeg \/ kHighMemBeg <= a0v) ->
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF a0v 16 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x138) 8 0x4018 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (a0v + 4) 4 sz -> 0 <= sz < 2 ^ 31 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (a0v + 8) 4 bw -> 0 <= bw < 2 ^ 32 ->
(sz < 4 -> forall regs3 mem3 md3,
  rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 -> cs_eq m2kfb_L regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W2 (@cfg_at fx rsegs M2B_MAL regs3 mem3 md3) POST) ->
(4 <= sz -> forall regs3 mem3 md3,
  rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 -> cs_eq m2kfb_L regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W2 (@cfg_at (m2kfb_fx4 fx bw) rsegs 0x82dc0 regs3 mem3 md3) POST) ->
SRr rsegs W2 (@cfg_at fx rsegs M2KB_FLT regs2 mem2 md2) POST.
Proof using MTL.
intros cx POST ly2 S2 W2 regs2 mem2 md2 a0v p s sz bw Hpre Hcore H9 H20 H10 H17 H24 H14 Hea Hp Hs Ha1 Ha2 Happ
  Hra H138 Hsz Hsz' Hbw Hbw' KMAL KF.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (E9 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 9 = Z_to_bv 64 (q_R (x_e rsegs cx)))
by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
assert (E20 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 20 = Z_to_bv 64 SHADOW_OFF)
by (rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl); exact H20).
assert (E10 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 10 = Z_to_bv 64 a0v)
by (rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact H10).
assert (E17 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 17 = Z_to_bv 64 (p + 0x4018))
by (rewrite (ew_Ereg_nat regs2 _ 17 17%bv eq_refl); exact H17).
assert (E24 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 24 = Z_to_bv 64 s)
by (rewrite (ew_Ereg_nat regs2 _ 24 24%bv eq_refl); exact H24).
assert (E14 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 14 = Z_to_bv 64 p)
by (rewrite (ew_Ereg_nat regs2 _ 14 14%bv eq_refl); exact H14).
assert (E32 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 32 = Z_to_bv 64 sz)
by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 33 = Z_to_bv 64 bw)
by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (B9 : bv_unsigned (ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 9) = q_R (x_e rsegs cx))
by (rewrite E9; apply unsigned_lit_small; lia).
assert (B10 : bv_unsigned (ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 10) = a0v)
by (rewrite E10; apply unsigned_lit_small; lia).
pose proof (m2b_entry (fx := fx) M2KB_FLT [] [m2kfb_R10; m2kfb_R9] m2kfb_facts W2 regs2
  [Z_to_bv 64 sz; Z_to_bv 64 bw] mem2 (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  [ apply (rtmb_ro_region rsegs _ (w_H W2) mem2 10 a0v 4 12);
    [ exact B10 | lia | lia |
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (chunk_ok_val rsegs _ _ a0v 4 4 (SOff 32 0) sz);
        [ apply m2kb_denot_of_U; apply U_atom; [exact E32 | lia] | cbn; lia | cbn; lia | exact Hsz ]
      | apply (chunk_ok_val rsegs _ _ a0v 8 4 (SOff 33 0) bw);
        [ apply m2kb_denot_of_U; apply U_atom; [exact E33 | lia] | exact Hbw' | cbn; lia | exact Hbw ] ] ]
  | unfold m2kfb_R9, m2b_frame;
    apply (rtmb_ro_region rsegs _ (w_H W2) mem2 9 (q_R (x_e rsegs cx)) 0x138 0x140);
    [ exact B9 | lia | lia |
      apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val rsegs _ _ (q_R (x_e rsegs cx)) 0x138 8 (SLit 0x4018) 0x4018);
      [ reflexivity | cbn; lia | cbn; lia | exact H138 ] ] ])).
specialize (HS ltac:(cbn [pairwise_disjoint all_disjoint]; split; [split; [|exact I] | split; exact I];
  unfold extent_disjoint, m2kfb_R10, m2kfb_R9, m2b_frame; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite B10, B9; left; unfold T_SEG_STK, ASTACK in *; lia)).
specialize (HS (m2kfb_facts_ok (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) (q_R (x_e rsegs cx)) a0v p s
  B9 ltac:(lia) Hal ltac:(rewrite E20; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
  E10 E17 E24 E14 Hea Hp Hs ltac:(lia))).
assert (SHOK : sh_ok rsegs M2B_Bx m2kb_SH (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) (mrestrict (w_H W2) mem2)).
{ apply (m2kb_sh_ok W2 mem2 _ a0v); [| | exact Hra | exact Happ].
  - unfold M2B_Bx. apply U_atom; [exact E20 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E10 | lia]. }
remember (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) E) by (subst E; apply env_agree_refl).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 M2KB_FLT) with (Z_to_bv 64 M2KB_FLT).
(* 0x82d70 .. 0x82d88, stop at 0x82d8c bltu size,4 *)
m2b_run m2b_awr. ck_keep m2b_kwr.
m2b_branch Hb.
all: rewrite branch_ltu_U, (m2kb_U_sext32 E 32 sz E32 ltac:(lia)), U_lit, (m2kb_sx_id sz Hsz') in Hb by lia.
- (* taken: the size is below 4, to MAL *)
  assert (Hlt : sz < 4) by (apply Z.ltb_lt; exact Hb).
  m2b_run_to m2b_awr M2B_MAL. ck_keep m2b_kwr.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    assert (Hpr : cs_eq m2kfb_L regs2 (ms_regs ms))
    by (eapply cs_eq_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with M2B_MAL by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KMAL Hlt (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ);
    [ exact (m2kfb_L_234 _ _ Hpr) | reflexivity | apply Permutation_refl | m2b_io
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
  | exact Hpr
  | intros a Ha; exact (KE a Ha (fun x => x)) ]
  end.
- (* not taken: the body's address, then the `flw` *)
  assert (Hge : 4 <= sz) by (apply Z.ltb_ge; exact Hb).
  m2b_run m2b_awr. ck_keep m2b_kwr.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msT end.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H msT), HAE : env_agree 32 _ ?E |- _ =>
    assert (G10 : getr (ms_regs msT) (Z_to_bv 5 10) = Z_to_bv 64 (a0v + 8))
    by (rewrite (st_ok_restrict_reg rsegs H E ss msT (Z_to_bv 5 10) HS);
        replace (sr_get (ss_regs ss) (Z_to_bv 5 10)) with (SOff 10 8) by (vm_compute; reflexivity);
        apply m2kb_denot_of_U; apply U_atom_off; [exact E10 | lia | lia]);
    assert (Hpr : cs_eq m2kfb_L regs2 (ms_regs msT))
    by (eapply cs_eq_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss msT HS eq_refl);
    replace (ss_pc ss) with 0x82dbc by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msT) ?mdT _ |- _ =>
  apply (m2kfb_flw W2 (ms_regs msT) (ms_mem msT) mdT POST (a0v + 8) bw G10);
  [ apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 (ms_mem msT) (a0v + 8) 4 bw); [|exact Hbw];
    intros k Hk; cbn in Hk; exact (KE (a0v + 8 + k) ltac:(lia) (fun x => x))
  | exact Hbw'
  | intros md' Hsame; rewrite (same_but_materialized_wvb mdT md' Hsame);
    apply (KF Hge (ms_regs msT) (ms_mem msT));
    [ apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msT) (ms_mem msT) _ Hcore);
      [ eapply ajournal_materialize; eassumption
      | exact (m2kfb_L_234 _ _ Hpr) | reflexivity | apply Permutation_refl | m2b_io
      | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
    | exact Hpr
    | intros a Ha; exact (KE a Ha (fun x => x)) ] ]
  end.
Qed.

(* the out cell R + 0x198 of pod_nearest: its 8 bytes are marked usable at every state of the segment (hi_rz at
   the segment's start; the shadow bytes lie in the high shadow, below R - T_SEG_STK and apart from rsb_E2) *)
Lemma m2kfb_ra_out : forall (cx : rsb_scx rsegs) ly4 S4 W4 regs4 mem4 md4,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly4 S4 W4 regs4 mem4 md4 ->
range_addressable (aview rsegs (w_H W4) mem4) SHADOW_OFF (q_R (x_e rsegs cx) + 0x198) 8.
Proof.
intros cx ly4 S4 W4 regs4 mem4 md4 Hpre Hpod Hcore.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & _).
pose proof (m2b_frameF B cx Hpre) as (F32 & F4096 & Fceil & Fapp & _).
pose proof asan_consts as (C1 & _).
pose proof Hpre as Hp. unfold rsb_pre, rt_seg_pre in Hp.
destruct Hp as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrz & _).
cbn [hi_rz rate_himg_B] in Hrz. rewrite Forall_cons_iff in Hrz. destruct Hrz as (Hrz & _). cbn [fst snd] in Hrz.
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpod) as (_ & P4096 & Pceil & Papp & _).
assert (Hreq : q_len (x_e rsegs cx) <= req_size (q_len (x_e rsegs cx)))
by (unfold req_size; destruct (Z.eqb_spec (q_len (x_e rsegs cx)) 0); lia).
destruct Hcore as (_ & _ & _ & _ & _ & _ & HK).
intros x Hx. destruct (Hrz x ltac:(lia)) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
rewrite <- Hsv.
assert (L1 : 2 ^ 43 <= x / 8) by (apply Z.div_le_lower_bound; lia).
assert (L2 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (q_F (x_e rsegs cx)) 8 ltac:(lia)) as DF.
pose proof (Z.mod_pos_bound (q_F (x_e rsegs cx)) 8 ltac:(lia)) as MF.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Papp.
apply HK.
- unfold shadow_of_addr, SHADOW_OFF. lia.
- rewrite HR. unfold shadow_of_addr, SHADOW_OFF, T_SEG_STK, ASTACK. lia.
- unfold rsb_E2, rt_inw. cbn [hi_w2 rate_himg_B]. intros [Hw|Hw].
  + rewrite !Exists_cons, Exists_nil in Hw. cbn [rt_xv fst snd] in Hw.
    unfold shadow_of_addr, shadow_addr, SHADOW_OFF, T_SEG_STK, ASTACK in *.
    destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[]]]]]]]; lia.
  + unfold shadow_of_addr, SHADOW_OFF in Hw. lia.
Qed.

(* 0x82dc0 .. 0x82dc4 at the float state after the `flw`, then pod_nearest *)
Lemma m2kfb_walk2 : forall (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2 b,
rsb_pre rsegs B cx -> rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
getr regs2 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)) ->
0 <= b < 2 ^ 32 -> Sem.reg_get (@fp_regs fx) (Z_to_bv 5 10) = Sem.nan_box (Z_to_bv 32 b) ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3,
  rt_fxk [15] fx fx3 ->
  rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  getr regs3 (Z_to_bv 5 10) = w64 (rt_near_rc (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX)) ->
  match Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX with
  | Some r => val_mem rsegs (mrestrict (w_H W3) mem3) (q_R (x_e rsegs cx) + 0x198) 8 (r mod 2 ^ 64)
  | None => True
  end ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_nearest_STK <= a < q_R (x_e rsegs cx)) ->
   ~ (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\
      q_R (x_e rsegs cx) + 0x198 <= a < q_R (x_e rsegs cx) + 0x198 + 8) ->
   aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W3 (@cfg_at fx3 rsegs 0x82dc8 regs3 mem3 md3) POST) ->
SRr rsegs W2 (@cfg_at fx rsegs 0x82dc0 regs2 mem2 md2) POST.
Proof using MTL HNEAR.
intros cx POST ly2 S2 W2 regs2 mem2 md2 b Hpre Hcore Hpod H9 Hb HF10 Hfrm KN.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (Hsp : spZ regs2 = q_R (x_e rsegs cx)).
{ rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
assert (E9 : ew (Ereg regs2 []) 9 = Z_to_bv 64 (q_R (x_e rsegs cx)))
by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
pose proof (m2b_entry (fx := fx) 0x82dc0 [] [] (mkFacts [] [] []) W2 regs2 [] mem2 (Forall_nil _) eq_refl
  (Forall_nil _) I ltac:(repeat split)) as HS.
remember (Ereg regs2 []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2B_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 0x82dc0) with (Z_to_bv 64 0x82dc0).
(* 0x82dc0 addi a0,s1,0x198; 0x82dc4 jal pod_nearest: stop at 0x83fcc *)
m2b_run m2b_awr. ck_keep m2b_kwr.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msT end.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H msT), HAE : env_agree 32 _ ?E |- _ =>
  assert (G10 : getr (ms_regs msT) (Z_to_bv 5 10) = w64 (q_R (x_e rsegs cx) + 0x198))
  by (rewrite (st_ok_restrict_reg rsegs H E ss msT (Z_to_bv 5 10) HS);
      replace (sr_get (ss_regs ss) (Z_to_bv 5 10)) with (SOff 9 0x198) by (vm_compute; reflexivity);
      apply m2kb_denot_of_U; apply U_atom_off; [exact E9 | lia | lia]);
  assert (G1 : getr (ms_regs msT) 1 = w64 0x82dc8)
  by (rewrite (st_ok_restrict_reg rsegs H E ss msT 1%bv HS);
      replace (sr_get (ss_regs ss) 1%bv) with (SLit 0x82dc8) by (vm_compute; reflexivity);
      reflexivity);
  assert (Hpr : aregs_preserved regs2 (ms_regs msT))
  by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
  rewrite (st_ok_restrict_mkst rsegs H E ss msT HS eq_refl);
  replace (ss_pc ss) with M2B_NEAREST by (vm_compute; reflexivity)
end.
assert (HspT : spZ (ms_regs msT) = q_R (x_e rsegs cx)) by (rewrite (m2b_sp_pres _ _ Hpr); exact Hsp).
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msT) ?mdT _ |- _ =>
assert (HcoreT : rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 (ms_regs msT) (ms_mem msT) mdT)
by (apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msT) (ms_mem msT) mdT Hcore HJ);
    [ intros r Hr; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | m2b_io
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ])
end.
assert (HEc : forall a, (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\
  q_R (x_e rsegs cx) + 0x198 <= a < q_R (x_e rsegs cx) + 0x198 + 8) -> rsb_E2 rsegs cx a).
{ intros a (_ & Ha). left. unfold rt_inw. cbn [hi_w2 rate_himg_B].
  rewrite !Exists_cons. cbn [rt_xv fst snd].
  right. right. right. right. right. left. lia. }
eapply SRr_bind.
{ apply (HNEAR fx (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem msT) _ (x_k rsegs cx) (ms_regs msT)
    (q_R (x_e rsegs cx) + 0x198) b).
  - apply (m2b_pre_call B MT cx _ _ _ _ _ _ _ T_nearest_STK Hpre HcoreT);
    [ rewrite G1; vm_compute; reflexivity
    | unfold raZ; rewrite G1; unfold w64; rewrite unsigned_lit_small by lia; lia
    | exact HspT | unfold T_nearest_STK, T_SEG_STK, ASTACK; lia ].
  - exact G10.
  - exact Hb.
  - exact HF10.
  - unfold rt_wcell. rewrite HspT. unfold T_SEG_STK, ASTACK in *. split; [left; split; lia | left; lia].
  - pose proof (Z.div_mod (q_R (x_e rsegs cx)) 16 ltac:(lia)) as D. rewrite Hal in D.
    replace (q_R (x_e rsegs cx) + 0x198) with ((2 * (q_R (x_e rsegs cx) / 16) + 51) * 8) by lia.
    apply Z_mod_mult.
  - exact (m2kfb_ra_out cx ly2 S2 W2 (ms_regs msT) (ms_mem msT) _ Hpre Hpod HcoreT).
  - exact (m2b_rom_at B MT cx ly2 S2 W2 (ms_regs msT) (ms_mem msT) _ Hpre Hpod HcoreT).
  - exact Hfrm. }
intros W3 c3 _ Hpost.
destruct (m2b_core_call B MT MTL cx (rsb_E2 rsegs cx)
  (fun x => Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\
     q_R (x_e rsegs cx) + 0x198 <= x < q_R (x_e rsegs cx) + 0x198 + 8) T_nearest_STK ly2 S2 W2 (ms_regs msT)
  (ms_mem msT) _ _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_nearest_STK, T_SEG_STK, ASTACK; lia) HEc Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & Hrc3).
subst c3. rewrite G1. destruct Hrc3 as (H10' & Hval').
apply (KN fx3 ly3 S3 W3 regs3 mem3 md3 Hfx3 Hcore3 (aregs_preserved_trans _ _ _ Hpr Hpres3) H10' Hval').
intros a Ha Hs Hn. rewrite (Hkept3 a Ha Hs Hn). exact (KE a Ha (fun x => x)).
Qed.

(* 0x82dc8 beqz a0 -> MAL; 0x82dcc lw a2,0x198(s1); to JN 0x82dd0 *)
Lemma m2kfb_walk3 : forall (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2
  (o : option Z),
rsb_pre rsegs B cx -> rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)) ->
getr regs2 (Z_to_bv 5 10) = w64 (rt_near_rc o) ->
match o with
| Some r => val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x198) 8 (r mod 2 ^ 64)
| None => True
end ->
(o = None -> forall regs3 mem3 md3,
  rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W2 (@cfg_at fx rsegs M2B_MAL regs3 mem3 md3) POST) ->
(forall r, o = Some r -> forall regs3 mem3 md3,
  rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  getr regs3 (Z_to_bv 5 12) = w64 (m2kb_sx (r mod 2 ^ 32)) ->
  SRr rsegs W2 (@cfg_at fx rsegs M2KB_JN regs3 mem3 md3) POST) ->
SRr rsegs W2 (@cfg_at fx rsegs 0x82dc8 regs2 mem2 md2) POST.
Proof using MTL.
intros cx POST ly2 S2 W2 regs2 mem2 md2 o Hpre Hcore H9 H10 Hval KN KS.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (proj1 Hcore) as HJ.
destruct o as [r|].
- (* Some r: the `beqz` is not taken; a2 = the low word of the 8 bytes at R + 0x198, sign-extended *)
  assert (Hr32 : 0 <= r mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (Hval4 : val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x198) 4 (r mod 2 ^ 32)).
  { pose proof (m2kfb_val_lo4 _ _ _ Hval) as V.
    replace (r mod 2 ^ 64 mod 2 ^ 32) with (r mod 2 ^ 32) in V; [exact V|].
    symmetry. apply (Z.mod_mod_divide r (2 ^ 64) (2 ^ 32)). exists (2 ^ 32). reflexivity. }
  assert (E9 : ew (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 32)]) 9 = Z_to_bv 64 (q_R (x_e rsegs cx)))
  by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
  assert (E32 : ew (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 32)]) 32 = Z_to_bv 64 (r mod 2 ^ 32))
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  pose proof (m2b_entry (fx := fx) 0x82dc8 [((10%bv : bv 5), SLit 1)]
    [m2b_frame 0x198 0x19c 0 0 [YP09.mkChunk 0x198 (CVal 4 (SOff 32 0))]] m2b_facts W2 regs2
    [Z_to_bv 64 (r mod 2 ^ 32)] mem2) as HS.
  specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
    [ intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
    | rewrite ck_lit; symmetry; exact H10 ]) eq_refl).
  specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; unfold m2b_frame;
    apply (rtmb_ro_region rsegs _ (w_H W2) mem2 9 (q_R (x_e rsegs cx)) 0x198 0x19c);
    [ rewrite E9; apply unsigned_lit_small; lia | lia | lia |
      apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val rsegs _ _ (q_R (x_e rsegs cx)) 0x198 4 (SOff 32 0) (r mod 2 ^ 32));
      [ apply m2kb_denot_of_U; apply U_atom; [exact E32 | lia] | cbn; lia | cbn; lia | exact Hval4 ] ])).
  specialize (HS ltac:(cbn; tauto)
    (m2b_facts_ok (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 32)]) (q_R (x_e rsegs cx))
      ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal)).
  remember (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 32)]) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 32)]) E) by (subst E; apply env_agree_refl).
  assert (SHOK : sh_ok rsegs M2B_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
  unfold cfg_at. change (w64 0x82dc8) with (Z_to_bv 64 0x82dc8).
  m2b_run_to m2b_awr M2KB_JN. ck_keep m2b_kwr.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    assert (G12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (m2kb_sx (r mod 2 ^ 32)))
    by (rewrite (st_ok_restrict_reg rsegs H E ss ms (Z_to_bv 5 12) HS);
        replace (sr_get (ss_regs ss) (Z_to_bv 5 12)) with (SExt true 32 (SOff 32 0)) by (vm_compute; reflexivity);
        apply m2kb_denot_of_U; apply (m2kb_U_sext32 E 32 (r mod 2 ^ 32) E32 Hr32));
    assert (Hpr : aregs_preserved regs2 (ms_regs ms))
    by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with M2KB_JN by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KS r eq_refl (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ);
    [ intros q Hq; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | m2b_io
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
  | exact Hpr
  | intros a Ha; exact (KE a Ha (fun x => x))
  | exact G12 ]
  end.
- (* None: the `beqz` is taken, to MAL *)
  pose proof (m2b_entry (fx := fx) 0x82dc8 [((10%bv : bv 5), SLit 0)] [] (mkFacts [] [] []) W2 regs2 [] mem2) as HS.
  specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
    [ intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
    | rewrite ck_lit; symmetry; exact H10 ]) eq_refl (Forall_nil _) I ltac:(repeat split)).
  remember (Ereg regs2 []) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl).
  assert (SHOK : sh_ok rsegs M2B_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
  unfold cfg_at. change (w64 0x82dc8) with (Z_to_bv 64 0x82dc8).
  m2b_run_to m2b_awr M2B_MAL. ck_keep m2b_kwr.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    assert (Hpr : aregs_preserved regs2 (ms_regs ms))
    by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with M2B_MAL by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KN eq_refl (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ);
    [ intros q Hq; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | m2b_io
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
  | exact Hpr
  | intros a Ha; exact (KE a Ha (fun x => x)) ]
  end.
Qed.
End w.

(* ===================================== FLT -> MAL / JN ===================================== *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
(* pod_nearest 0x83fcc at every float state (lib/AU/RtPgNearB.v rt_pod_nearest_B): the Float arm calls it at the
   float state the `flw` leaves *)
Hypothesis HNEAR : forall fy : YK11.FPState, rt_pod_nearest_specX (fx := fy) rsegs B MT M2B_NEAREST.

Lemma m2kb_float : m2kb_float_stmt B MT.
Proof using MTL HNEAR.
unfold m2kb_float_stmt, m2kb_K_float.
intros cx POST rec Hpre HMAL HJOIN fx3 ly3 S3 W3 regs3 mem3 md3 e v HA HL Hv Hent Hty Hm.
pose proof HA as (Hbase & Hat & Hhz).
pose proof Hbase as (Hcore & Hfxk & _ & _ & _ & _ & _ & _ & Hpod & _).
destruct Hent as (Hewf & _ & Hvs & Hvb & Hra & Ha1 & Ha2 & Happ).
pose proof Hewf as (Hwt & Hwb & Hws).
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & _).
pose proof (m2kb_apart B cx Hpre) as (Hp0 & _).
(* A's cut: rsb_L_chk, then s10 = the code, s6 = the mask, s7 = the flags byte, R+0x60 = F, R+0x168 = pp *)
pose proof Hat as Hat'. unfold rsb_at_cx, rsb_at, rsb_L_chk, rsb_Hc in Hat'.
rewrite Forall_app, Forall_app, !Forall_cons_iff in Hat'.
destruct Hat' as (((A8 & A9 & A19 & A20 & AC178 & A21 & AC10 & AC50 & _) &
                   (AC48 & AC30 & AC38 & AC40 & AC18 & AC148 & _)) & (A26 & A22 & A23 & AC60 & AC168 & _)).
cbn [rt_at rt_xv fst snd] in A9, A20, A26, A22, A23.
assert (HatA : rsb_at_cx rsegs cx W3 mem3 regs3 (rsb_L_chk rsegs cx ++ m2kb_L_FP cx)).
{ unfold rsb_at_cx, rsb_at in Hat |- *. rewrite Forall_app in Hat |- *. destruct Hat as (HL1 & HL2).
  split; [exact HL1|]. rewrite !Forall_cons_iff in HL2. destruct HL2 as (_ & _ & _ & X60 & X168 & _).
  unfold m2kb_L_FP. apply Forall_cons; [exact X60|]. apply Forall_cons; [exact X168 | apply Forall_nil]. }
(* FLT's own values: a0 = &ent[v], a7 = pp + 0x4018, s8 = 104 v, a4 = pp, R+0x138 = 0x4018 *)
pose proof HL as HL'. unfold rsb_at_cx, rsb_at, m2kb_L_flt in HL'. rewrite !Forall_cons_iff in HL'.
destruct HL' as (L10 & L17 & L24 & L14 & LC138 & _). cbn [rt_at rt_xv fst snd] in L10, L17, L24, L14, LC138.
replace (0x4018 mod 2 ^ 64) with 0x4018 in LC138 by reflexivity.
unfold m2kb_ea in Ha1, Ha2, Happ, Hra, Hvs, Hvb, L10.
assert (HPA : rsb_PA rsegs cx rec = Rate.expect_value e).
{ destruct Hm as (HE0 & HPs & HPf).
  rewrite <- HE0, (surjective_pairing (rsb_PA rsegs cx rec)), HPf, HPs. symmetry. apply surjective_pairing. }
(* the exit to A's cut, from the cut at FLT, at a state whose registers m2kfb_L are kept, whose memory agrees outside
   m2kb_wz and whose float state keeps fx outside fa0, fa3, fa4, fa5 *)
assert (XA : forall (fx5 : YK11.FPState) ly5 S5 W5 regs5 mem5 md5,
  rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly5 S5 W5 regs5 mem5 md5 -> cs_eq m2kfb_L regs3 regs5 ->
  rt_fxk [10; 13; 14; 15] fx fx5 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ m2kb_wz cx a -> aview rsegs (w_H W5) mem5 a = aview rsegs (w_H W3) mem3 a) ->
  rsb_cut_A (fx := fx) rsegs B MT cx fx5 rec ly5 S5 W5 regs5 mem5 md5).
{ intros fx5 ly5 S5 W5 regs5 mem5 md5 Hcore5 Hcs5 Hfxk5 K5.
  apply (m2kb_cut_A B MT cx fx3 fx5 rec ly3 S3 W3 regs3 mem3 md3 ly5 S5 W5 regs5 mem5 md5 Hpre Hbase Hhz HatA
    Hcore5 Hfxk5 (m2kb_cs_sub _ _ _ _ m2kfb_L5_sub Hcs5)).
  - rewrite (Hcs5 (Z_to_bv 5 26) ltac:(m2kfb_inL)). exact A26.
  - rewrite (Hcs5 (Z_to_bv 5 22) ltac:(m2kfb_inL)). exact A22.
  - rewrite (Hcs5 (Z_to_bv 5 23) ltac:(m2kfb_inL)). exact A23.
  - exact K5. }
apply (m2kfb_walk1 (fx := fx3) B MT MTL cx POST ly3 S3 W3 regs3 mem3 md3
  (q_pp (x_e rsegs cx) + 0x4014 + 104 * Z.of_nat v) (q_pp (x_e rsegs cx)) (104 * Z.of_nat v) (e_size e) (m2kb_bw e)
  Hpre Hcore A9 A20 L10 L17 L24 L14 eq_refl ltac:(lia) ltac:(lia) Ha1 Ha2 Happ Hra LC138 Hvs ltac:(lia) Hvb
  (m2kb_bw_range e Hewf)).
- (* the size is below 4: MAL *)
  intros Hlt regs4 mem4 md4 Hcore4 Hcs4 K4.
  apply (HMAL fx3 ly3 S3 W3 regs4 mem4 md4 rec).
  apply m2kb_mal_of_A.
  + apply (XA fx3 ly3 S3 W3 regs4 mem4 md4 Hcore4 Hcs4 Hfxk). intros a Ha _. exact (K4 a Ha).
  + rewrite HPA, m2kb_expect_none; [reflexivity | right; exact Hlt].
  + rewrite HPA, m2kb_expect_none; [reflexivity | right; exact Hlt].
- (* the body word in fa0, then pod_nearest *)
  intros Hge regs4 mem4 md4 Hcore4 Hcs4 K4.
  assert (Hfxk4 : rt_fxk [10; 13; 14; 15] fx (m2kfb_fx4 fx3 (m2kb_bw e)))
  by (apply m2kfb_fxk_set; [left; reflexivity | exact Hfxk]).
  apply (m2kfb_walk2 (fx := m2kfb_fx4 fx3 (m2kb_bw e)) B MT MTL HNEAR cx POST ly3 S3 W3 regs4 mem4 md4 (m2kb_bw e)
    Hpre Hcore4 Hpod ltac:(rewrite (Hcs4 (Z_to_bv 5 9) ltac:(m2kfb_inL)); exact A9) (m2kb_bw_range e Hewf)
    (m2kfb_f10 fx3 (m2kb_bw e)) (proj2 Hfxk)).
  intros fx5 ly5 S5 W5 regs5 mem5 md5 Hfx5 Hcore5 Hpr5 H10' Hval' K5.
  assert (Hfxk5 : rt_fxk [10; 13; 14; 15] fx fx5)
  by (apply (m2kfb_fxk_trans _ _ _ _ _ Hfxk4 Hfx5); intros z Hz; cbn in Hz |- *; tauto).
  assert (Hcs35 : cs_eq m2kfb_L regs3 regs5)
  by exact (cs_eq_trans _ _ _ _ Hcs4 (cs_eq_of_pres _ _ _ m2kfb_L_cs Hpr5)).
  apply (m2kfb_walk3 (fx := fx5) B MT MTL cx POST ly5 S5 W5 regs5 mem5 md5
    (Nearest.nearest (m2kb_bw e) Nearest.INT32_MIN Nearest.INT32_MAX) Hpre Hcore5
    ltac:(rewrite (Hcs35 (Z_to_bv 5 9) ltac:(m2kfb_inL)); exact A9) H10' Hval').
  + (* None: MAL *)
    intros Hn regs6 mem6 md6 Hcore6 Hpr6 K6.
    apply (HMAL fx5 ly5 S5 W5 regs6 mem6 md6 rec).
    assert (HPA' : rsb_PA rsegs cx rec = (None, -1)).
    { rewrite HPA, (m2kb_expect_float e Hty Hge), <- (m2kb_bw_rd32 e Hewf Hge), Hn. reflexivity. }
    apply m2kb_mal_of_A; [| rewrite HPA'; reflexivity | rewrite HPA'; reflexivity].
    apply (XA fx5 ly5 S5 W5 regs6 mem6 md6 Hcore6 (cs_eq_trans _ _ _ _ Hcs35 (cs_eq_of_pres _ _ _ m2kfb_L_cs Hpr6))
      Hfxk5).
    intros a Ha Hw. unfold m2kb_wz in Hw.
    rewrite (K6 a Ha), (K5 a Ha ltac:(unfold T_nearest_STK, T_SEG_STK, ASTACK in *; lia)
      ltac:(intros (Hne & _); exact (Hne Hn))).
    exact (K4 a Ha).
  + (* Some r: the join *)
    intros r Hr regs6 mem6 md6 Hcore6 Hpr6 K6 H12.
    assert (HPA' : rsb_PA rsegs cx rec = (Some r, 1)).
    { rewrite HPA, (m2kb_expect_float e Hty Hge), <- (m2kb_bw_rd32 e Hewf Hge), Hr. reflexivity. }
    apply (HJOIN fx5 ly5 S5 W5 regs6 mem6 md6).
    * apply (XA fx5 ly5 S5 W5 regs6 mem6 md6 Hcore6 (cs_eq_trans _ _ _ _ Hcs35 (cs_eq_of_pres _ _ _ m2kfb_L_cs Hpr6))
        Hfxk5).
      intros a Ha Hw. unfold m2kb_wz in Hw.
      rewrite (K6 a Ha), (K5 a Ha ltac:(unfold T_nearest_STK, T_SEG_STK, ASTACK in *; lia)
        ltac:(intros (_ & Hx); lia)).
      exact (K4 a Ha).
    * rewrite HPA'. reflexivity.
    * rewrite H12. unfold rsb_hz, Rate.written_or. rewrite HPA'. reflexivity.
Qed.
End t.

Print Assumptions m2kb_float.
