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
   m2kf_* lemmas and m2k_float) for image B (fuzz_rate.asan-ubsan). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgM02KeyFB.v at f07713e8e823 for
   reac-pw/fuzz_role image B (fuzz_role.asan-ubsan): image B's pcs (FLT 0x8247c, the `flw` 0x824c8, pod_nearest
   0x82eb4 called from 0x824d0, JN 0x824dc, MAL 0x824f8); the cuts are lib/AU/RPgSeg.v's (rsb_ -> rs_) and the
   interfaces lib/AU/RPgM02KeyBase.v's (m2kb_ -> m2k_); the shadow base is s11 (atom 27); the addresses of the size
   and of the body are a7 + s7 and s6 + s7 (s6 = pp), with the real-frame cell R+0x120 = 0x4018; s7 changes at
   0x8249c, so the size walk keeps the registers m2kf_L; pod_nearest's out cell is R+0x178 (rl_seg_pre's hi_rz
   [(0x178, 16)] at role_himg_B), read back by the 8-byte `ld a2,0x178(s1)` 0x824d8, so the join's value is the
   8-byte word r mod 2^64 of pod_nearest's answer r and role's value tail decides on it (a role when it is 0 or 1,
   lib/A/RPgM02KeyF.v's model); pod_nearest's contract is the theorem lib/AU/RPgNearA.v rl_pod_nearest_B under the
   Section hypotheses LAWS, HGOT and HSC (fuzz_rate: the hypothesis HNEAR). *)
(* reac-pw/fuzz_role, image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, the same loaded bytes): the Float arm of
   LLVMFuzzerTestOneInput's segment M02, FLT 0x8247c -> MAL 0x824f8 / JN 0x824dc. Proves no function (kind: segment
   lemma): rl_m02_key_float_B, lib/AU/RPgM02KeyBase.v's m2k_float_stmt.

   THE CODE (lib/AU/RPgM02Base.v lists it with every pc):
     0x8247c .. 0x8248c  a1 := a7 + s7 (= &ent[v] + 4) and its instrumented check 0x82488 (slow block 0x82944)
     0x82490 .. 0x82498  lw a0,4(a0) = the size; size < 4 -> MAL                              m2kf_walk1
     0x8249c .. 0x824c4  s7 := s6 + s7; a0 := s7 + R+0x120 (0x4018) + 4 and its instrumented check 0x824b4
                         (slow block 0x82a0c); a0 := s7 + 0x401c (= &ent[v] + 8)
     0x824c8             flw fa0,0(a0) (the body word)                                         m2kf_flw
     0x824cc .. 0x824d0  a0 := R + 0x178; jal pod_nearest 0x82eb4, ra = 0x824d4              m2kf_walk2
     0x824d4 .. 0x824d8  beqz a0 -> MAL (pod_nearest's failure arm: no nearest int32); ld a2,0x178(s1); falls into
                         JN 0x824dc                                                            m2kf_walk3
   The two instrumented checks pass (the shadow entry over the 16 bytes of ent[v]), so their slow blocks return to the
   fast path and the error path is not reached.

   SECTION HYPOTHESES of rl_m02_key_float_B: MTL : ameter_laws MT, LAWS : AR_laws rsegs B, and the two cells the
   pod_nearest lift reads, HGOT : as_got_shadow B = 0x9aad0 and HSC : as_shadow_cell B = 0xa3678. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o YA0d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Nearest Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgSeg RPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgCheck RPgCheckStr RPgM02Base RPgM02KeyBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgNearImg RPgNearA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== the float state after the `flw` ===================================== *)
(* 0x824c8 flw fa0,0(a0): f10 holds the NaN-boxed binary32 b, the rest of f is kept *)
Definition m2kf_fx4 (f : YK11.FPState) (b : Z) : YK11.FPState :=
YK11.mkFP (bvmap_set (Z_to_bv 5 10) (nan_box (Z_to_bv 32 b)) (@fp_regs f)) (@fp_csr f).

Lemma m2kf_fxk_trans : forall ks ks' f g h,
rl_fxk ks f g -> rl_fxk ks' g h -> (forall z, In z ks' -> In z ks) -> rl_fxk ks f h.
Proof.
intros ks ks' f g h (Hg & _) (Hh & Hcsr) Hin. split; [|exact Hcsr].
intros k Hk. rewrite (Hh k ltac:(intros Hc; exact (Hk (Hin _ Hc)))). exact (Hg k Hk).
Qed.

Lemma m2kf_fxk_set : forall ks f g b, In 10 ks -> rl_fxk ks f g -> rl_fxk ks f (m2kf_fx4 g b).
Proof.
intros ks f g b Hr (Hg & Hcsr). split; [|exact Hcsr].
intros k Hk. unfold m2kf_fx4. cbn [fp_regs].
destruct (base.decide (k = Z_to_bv 5 10)) as [->|Hne]; [exfalso; exact (Hk Hr)|].
change (bvmap_set (Z_to_bv 5 10) (nan_box (Z_to_bv 32 b)) (@fp_regs g))
  with (regupd (@fp_regs g) (Z_to_bv 5 10) (nan_box (Z_to_bv 32 b))).
rewrite (regupd_other (@fp_regs g) (Z_to_bv 5 10) (nan_box (Z_to_bv 32 b)) k Hne). exact (Hg k Hk).
Qed.

Lemma m2kf_f10 : forall f b, Sem.reg_get (@fp_regs (m2kf_fx4 f b)) (Z_to_bv 5 10) = Sem.nan_box (Z_to_bv 32 b).
Proof. intros f b. unfold m2kf_fx4. cbn [fp_regs]. apply regupd_same. Qed.

(* pod_nearest's answer r (an int32) as the 8-byte word the `ld` reads back: r itself when r >= 0, r + 2^64 when
   r < 0; so the word is below 2 exactly when r is 0 or 1 *)
Lemma m2kf_mod_small : forall r, - 2 ^ 31 <= r <= 2 ^ 31 - 1 -> (r mod 2 ^ 64 < 2 <-> (r = 0 \/ r = 1)).
Proof.
intros r Hr. destruct (Z_lt_le_dec r 0) as [Hn|Hp].
- replace (r mod 2 ^ 64) with (r + 2 ^ 64) by (apply (Z.mod_unique _ _ (-1)); lia).
  split; intros; lia.
- rewrite Z.mod_small by lia. split; intros; lia.
Qed.

(* ===================================== the registers the size walk keeps ===================================== *)
(* sp, gp, tp, rs_L_chk's six (s0, s1, s2, s3, s4, s11) and T's four (s6, s8, s9, s10): every callee-saved register
   the cuts name; s7 (x23) is not kept, 0x8249c overwrites it *)
Definition m2kf_L : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 26; 27]%bv.

Lemma m2kf_L_cs : forall r, In r m2kf_L -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [m2kf_L In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.

Lemma m2kf_L5_sub : forall r, In r m2k_L5 -> In r m2kf_L.
Proof. intros r Hr. cbv [m2k_L5 m2kf_L In] in Hr |- *. tauto. Qed.

Ltac m2kf_inL := cbv [m2kf_L In]; repeat (first [left; apply bv_eq; reflexivity | right]).

Lemma m2kf_L_234 : forall ra rb, cs_eq m2kf_L ra rb ->
forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr rb (Z_to_bv 5 r) = getr ra (Z_to_bv 5 r).
Proof. intros ra rb H r [->|[->| ->]]; apply H; m2kf_inL. Qed.

(* ===================================== the entry state of the size walk ===================================== *)
(* The size and the body word of the value entry at atom 10 = &ent[v] (the extra atoms 32 and 33), and the real-frame
   cell R+0x120 = 0x4018 at atom 9 = R. *)
Definition m2kf_R10 : YP09.region :=
YP09.mkRegion (Some 10%nat) 4 12 0 0 [YP09.mkChunk 4 (CVal 4 (SOff 32 0)); YP09.mkChunk 8 (CVal 4 (SOff 33 0))].
Definition m2kf_R9 : YP09.region := m2_frame 0x120 0x128 0 0 [YP09.mkChunk 0x120 (CVal 8 (SLit 0x4018))].
(* the engine's alias facts: a7 + s7 = &ent[v] + 4 (0x8247c) and s6 + s7 = &ent[v] - 0x4014 (0x8249c), with
   a7 = pp + 0x4018 (atom 17), s7 = 104 v (atom 23), s6 = pp (atom 22) *)
Definition m2kf_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 17 0) (SOff 23 0), SOff 10 4);
  (SAlu ALU_ADD (SOff 22 0) (SOff 23 0), SOff 10 (-0x4014)) ].
(* atom 9 is s1 = R, atom 27 is s11 = the runtime's shadow offset, atom 10 is a0 = &ent[v]; every bound a numeral *)
Definition m2kf_facts : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
          (10%nat, mkAF 4096 0x7fffff800000 0) ] [] m2kf_alias.

Lemma m2kf_facts_ok : forall E R a p s,
bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 27) = SHADOW_OFF ->
ew E 10 = Z_to_bv 64 a -> ew E 17 = Z_to_bv 64 (p + 0x4018) -> ew E 23 = Z_to_bv 64 s -> ew E 22 = Z_to_bv 64 p ->
a = p + 0x4014 + s -> 0 <= p -> 0 <= s -> 4096 <= a <= 0x7fffff800000 ->
facts_ok E m2kf_facts.
Proof.
intros E R a p s H9 HR Hal H27 E10 E17 E23 E22 Ha Hp Hs Hab.
assert (H10 : bv_unsigned (ew E 10) = a) by (rewrite E10; apply unsigned_lit_small; lia).
split; [|split; [exact I|]].
- cbn [m2kf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite H9, H27, H10. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
  repeat split; try lia.
  all: try apply Z.mod_1_r.
- cbn [m2kf_facts f_alias alias_ok m2kf_alias]. repeat split; apply U_inj.
  + rewrite U_SAlu, (U_atom _ 17 (p + 0x4018) E17), (U_atom _ 23 s E23), (U_atom_off _ 10 a 4 E10) by lia.
    cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
  + rewrite U_SAlu, (U_atom _ 22 p E22), (U_atom _ 23 s E23), (U_atom_off _ 10 a (-0x4014) E10) by lia.
    cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ===================================== the `flw` ===================================== *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* 0x824c8 flw fa0,0(a0) with a0 = a and the 4 bytes at a holding b; the walk goes on at 0x824cc *)
Lemma m2kf_flw : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) a b,
getr regs (Z_to_bv 5 10) = Z_to_bv 64 a ->
val_mem rsegs (mrestrict (w_H W) mem) a 4 b -> 0 <= b < 2 ^ 32 ->
(forall md', same_but_materialized md md' -> SRr rsegs W (@cfg_at (m2kf_fx4 fx b) rsegs 0x824cc regs mem md') Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x824c8) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q a b H10 Hval Hb HK.
assert (Hrd : rdn rsegs (mrestrict (w_H W) mem) (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 b)).
{ apply (proj2 (YP09.rdn_mbytes rsegs _ _ _ _)). split; [apply length_Z_to_le_bytes|].
  intros i Hi. rewrite (Hval i Hi).
  rewrite (nth_error_nth' (Z_to_le_bytes 4 b) (Z_to_bv 8 0)) by (rewrite length_Z_to_le_bytes; exact Hi).
  rewrite rm_nth_le_bytes by exact Hi. rewrite rm_le_byte_bv by exact Hi. reflexivity. }
assert (Hw : bv_extract 0 32 (le_bytes_to_word (Z_to_le_bytes 4 b)) = Z_to_bv 32 b).
{ rewrite le_bytes_to_word_Z, Cursor.bytes_le_to_Z_Z_to_le_bytes.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small b (2 ^ 32)) by lia.
  apply bv_eq. rewrite bv_extract_unsigned, unsigned_lit_small by lia. rewrite Z_to_bv_unsigned.
  try (f_equal; apply Z.shiftr_0_r). }
eapply (SRr_step rsegs m2_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (YK0o.fp_step_flw fx rsegs regs (Z_to_bv 64 0x824c8) (mrestrict (w_H W) mem) (seg_rom rsegs)
    (Z_to_bv 32 0x52507) (Z_to_bv 5 10) (Z_to_bv 5 10) (Z_to_bv 12 0) (Z_to_bv 64 a) (Z_to_le_bytes 4 b));
  [ reflexivity | vm_refl_bv | vm_compute; reflexivity | vm_refl_bv
  | rewrite H10; replace (bv_signed (Z_to_bv 12 0)) with 0 by reflexivity; apply v_addi_0
  | exact Hrd ].
- intros md' Hsame. rewrite unrestrict_mkst_mrestrict, Hw.
  replace (v_addi (Z_to_bv 64 0x824c8) 4) with (w64 0x824cc) by reflexivity.
  exact (HK md' Hsame).
Qed.
End s.

(* ===================================== the three runs ===================================== *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HGOT : as_got_shadow B = 0x9aad0.
Hypothesis HSC : as_shadow_cell B = 0xa3678.

(* 0x8247c .. 0x824c4: the size test, then the body's address; stop at the `flw` 0x824c8, which m2kf_flw steps.
   a0 = a0v = &ent[v] = p + 0x4014 + s with a7 = p + 0x4018, s7 = s, s6 = p *)
Lemma m2kf_walk1 : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2
  a0v p s sz bw,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)) -> getr regs2 (Z_to_bv 5 27) = w64 SHADOW_OFF ->
getr regs2 (Z_to_bv 5 10) = w64 a0v -> getr regs2 (Z_to_bv 5 17) = w64 (p + 0x4018) ->
getr regs2 (Z_to_bv 5 23) = w64 s -> getr regs2 (Z_to_bv 5 22) = w64 p ->
a0v = p + 0x4014 + s -> 0 <= p -> 0 <= s ->
4096 <= a0v -> a0v + 16 <= alloc_ceiling ->
(a0v + 16 <= kLowShadowBeg \/ kHighMemBeg <= a0v) ->
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF a0v 16 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x120) 8 0x4018 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (a0v + 4) 4 sz -> 0 <= sz < 2 ^ 31 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (a0v + 8) 4 bw -> 0 <= bw < 2 ^ 32 ->
(sz < 4 -> forall regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 -> cs_eq m2kf_L regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W2 (@cfg_at fx rsegs M2_MAL regs3 mem3 md3) POST) ->
(4 <= sz -> forall regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 -> cs_eq m2kf_L regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W2 (@cfg_at (m2kf_fx4 fx bw) rsegs 0x824cc regs3 mem3 md3) POST) ->
SRr rsegs W2 (@cfg_at fx rsegs M2K_FLT regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST ly2 S2 W2 regs2 mem2 md2 a0v p s sz bw Hpre Hcore H9 H27 H10 H17 H23 H22 Hea Hp Hs Ha1 Ha2 Happ
  Hra H120 Hsz Hsz' Hbw Hbw' KMAL KF.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
assert (E9 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 9 = Z_to_bv 64 (e_R (x_e rsegs cx)))
by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
assert (E27 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 27 = Z_to_bv 64 SHADOW_OFF)
by (rewrite (ew_Ereg_nat regs2 _ 27 27%bv eq_refl); exact H27).
assert (E10 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 10 = Z_to_bv 64 a0v)
by (rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact H10).
assert (E17 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 17 = Z_to_bv 64 (p + 0x4018))
by (rewrite (ew_Ereg_nat regs2 _ 17 17%bv eq_refl); exact H17).
assert (E23 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 23 = Z_to_bv 64 s)
by (rewrite (ew_Ereg_nat regs2 _ 23 23%bv eq_refl); exact H23).
assert (E22 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 22 = Z_to_bv 64 p)
by (rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl); exact H22).
assert (E32 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 32 = Z_to_bv 64 sz)
by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 33 = Z_to_bv 64 bw)
by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (B9 : bv_unsigned (ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 9) = e_R (x_e rsegs cx))
by (rewrite E9; apply unsigned_lit_small; lia).
assert (B10 : bv_unsigned (ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 10) = a0v)
by (rewrite E10; apply unsigned_lit_small; lia).
pose proof (m2_entry (fx := fx) M2K_FLT [] [m2kf_R10; m2kf_R9] m2kf_facts W2 regs2
  [Z_to_bv 64 sz; Z_to_bv 64 bw] mem2 (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  [ apply (rm_ro_region rsegs _ (w_H W2) mem2 10 a0v 4 12);
    [ exact B10 | lia | lia |
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (chunk_ok_val rsegs _ _ a0v 4 4 (SOff 32 0) sz);
        [ apply m2k_denot_of_U; apply U_atom; [exact E32 | lia] | cbn; lia | cbn; lia | exact Hsz ]
      | apply (chunk_ok_val rsegs _ _ a0v 8 4 (SOff 33 0) bw);
        [ apply m2k_denot_of_U; apply U_atom; [exact E33 | lia] | exact Hbw' | cbn; lia | exact Hbw ] ] ]
  | unfold m2kf_R9, m2_frame;
    apply (rm_ro_region rsegs _ (w_H W2) mem2 9 (e_R (x_e rsegs cx)) 0x120 0x128);
    [ exact B9 | lia | lia |
      apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val rsegs _ _ (e_R (x_e rsegs cx)) 0x120 8 (SLit 0x4018) 0x4018);
      [ reflexivity | cbn; lia | cbn; lia | exact H120 ] ] ])).
specialize (HS ltac:(cbn [pairwise_disjoint all_disjoint]; split; [split; [|exact I] | split; exact I];
  unfold extent_disjoint, m2kf_R10, m2kf_R9, m2_frame; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite B10, B9; left; unfold T_SEG_STK, ASTACK in *; lia)).
specialize (HS (m2kf_facts_ok (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) (e_R (x_e rsegs cx)) a0v p s
  B9 ltac:(lia) Hal ltac:(rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
  E10 E17 E23 E22 Hea Hp Hs ltac:(lia))).
assert (SHOK : sh_ok rsegs M2_Bx m2k_SH (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) (mrestrict (w_H W2) mem2)).
{ apply (m2k_sh_ok W2 mem2 _ a0v); [| | exact Hra | exact Happ].
  - unfold M2_Bx. apply U_atom; [exact E27 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E10 | lia]. }
remember (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) E) by (subst E; apply env_agree_refl).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 M2K_FLT) with (Z_to_bv 64 M2K_FLT).
(* 0x8247c .. 0x82494, stop at 0x82498 bltu size,4 *)
m2_run m2_awr. ck_keep m2_kwr.
m2_branch Hb.
all: rewrite branch_ltu_U, (m2k_U_sext32 E 32 sz E32 ltac:(lia)), U_lit, (m2k_sx_id sz Hsz') in Hb by lia.
- (* taken: the size is below 4, to MAL *)
  assert (Hlt : sz < 4) by (apply Z.ltb_lt; exact Hb).
  m2_run_to m2_awr M2_MAL. ck_keep m2_kwr.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    assert (Hpr : cs_eq m2kf_L regs2 (ms_regs ms))
    by (eapply cs_eq_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with M2_MAL by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KMAL Hlt (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ);
    [ exact (m2kf_L_234 _ _ Hpr) | reflexivity | apply Permutation_refl | m2_io
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
  | exact Hpr
  | intros a Ha; exact (KE a Ha (fun x => x)) ]
  end.
- (* not taken: the body's address, then the `flw` *)
  assert (Hge : 4 <= sz) by (apply Z.ltb_ge; exact Hb).
  m2_run m2_awr. ck_keep m2_kwr.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msT end.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H msT), HAE : env_agree 32 _ ?E |- _ =>
    assert (G10 : getr (ms_regs msT) (Z_to_bv 5 10) = Z_to_bv 64 (a0v + 8))
    by (rewrite (st_ok_restrict_reg rsegs H E ss msT (Z_to_bv 5 10) HS);
        replace (sr_get (ss_regs ss) (Z_to_bv 5 10)) with (SOff 10 8) by (vm_compute; reflexivity);
        apply m2k_denot_of_U; apply U_atom_off; [exact E10 | lia | lia]);
    assert (Hpr : cs_eq m2kf_L regs2 (ms_regs msT))
    by (eapply cs_eq_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss msT HS eq_refl);
    replace (ss_pc ss) with 0x824c8 by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msT) ?mdT _ |- _ =>
  apply (m2kf_flw W2 (ms_regs msT) (ms_mem msT) mdT POST (a0v + 8) bw G10);
  [ apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 (ms_mem msT) (a0v + 8) 4 bw); [|exact Hbw];
    intros k Hk; cbn in Hk; exact (KE (a0v + 8 + k) ltac:(lia) (fun x => x))
  | exact Hbw'
  | intros md' Hsame; rewrite (same_but_materialized_wvb mdT md' Hsame);
    apply (KF Hge (ms_regs msT) (ms_mem msT));
    [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msT) (ms_mem msT) _ Hcore);
      [ eapply ajournal_materialize; eassumption
      | exact (m2kf_L_234 _ _ Hpr) | reflexivity | apply Permutation_refl | m2_io
      | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
    | exact Hpr
    | intros a Ha; exact (KE a Ha (fun x => x)) ] ]
  end.
Qed.

(* the out cell R + 0x178 of pod_nearest: its 8 bytes are marked usable at every state of the segment (hi_rz at
   the segment's start; the shadow bytes lie in the high shadow, below R - T_SEG_STK and apart from rs_E2) *)
Lemma m2kf_ra_out : forall (cx : rs_scx rsegs) ly4 S4 W4 regs4 mem4 md4,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly4 S4 W4 regs4 mem4 md4 ->
range_addressable (aview rsegs (w_H W4) mem4) SHADOW_OFF (e_R (x_e rsegs cx) + 0x178) 8.
Proof using LAWS.
intros cx ly4 S4 W4 regs4 mem4 md4 Hpre Hpod Hcore.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & _).
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & Fapp & _).
pose proof asan_consts as (C1 & _).
pose proof Hpre as Hp. unfold rs_pre, rl_seg_pre in Hp.
destruct Hp as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrz & _).
cbn [hi_rz role_himg_B] in Hrz. rewrite Forall_cons_iff in Hrz. destruct Hrz as (Hrz & _). cbn [fst snd] in Hrz.
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpod) as (_ & P4096 & Pceil & Papp & _).
assert (Hreq : e_len (x_e rsegs cx) <= req_size (e_len (x_e rsegs cx)))
by (unfold req_size; destruct (Z.eqb_spec (e_len (x_e rsegs cx)) 0); lia).
destruct Hcore as (_ & _ & _ & _ & _ & _ & HK).
intros x Hx. destruct (Hrz x ltac:(lia)) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
rewrite <- Hsv.
assert (L1 : 2 ^ 43 <= x / 8) by (apply Z.div_le_lower_bound; lia).
assert (L2 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (e_F (x_e rsegs cx)) 8 ltac:(lia)) as DF.
pose proof (Z.mod_pos_bound (e_F (x_e rsegs cx)) 8 ltac:(lia)) as MF.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Papp.
apply HK.
- unfold shadow_of_addr, SHADOW_OFF. lia.
- rewrite HR. unfold shadow_of_addr, SHADOW_OFF, T_SEG_STK, ASTACK. lia.
- unfold rs_E2, rl_inw. cbn [hi_w2 role_himg_B]. intros [Hw|Hw].
  + rewrite !Exists_cons, Exists_nil in Hw. cbn [rl_xv fst snd] in Hw.
    unfold shadow_of_addr, shadow_addr, SHADOW_OFF, T_SEG_STK, ASTACK in *.
    destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[]]]]]]; lia.
  + unfold shadow_of_addr, SHADOW_OFF in Hw. lia.
Qed.

(* 0x824cc .. 0x824d0 at the float state after the `flw`, then pod_nearest *)
Lemma m2kf_walk2 : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2 b,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
getr regs2 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)) ->
0 <= b < 2 ^ 32 -> Sem.reg_get (@fp_regs fx) (Z_to_bv 5 10) = Sem.nan_box (Z_to_bv 32 b) ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3,
  rl_fxk [15] fx fx3 ->
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  getr regs3 (Z_to_bv 5 10) = w64 (rl_near_rc (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX)) ->
  match Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX with
  | Some r => val_mem rsegs (mrestrict (w_H W3) mem3) (e_R (x_e rsegs cx) + 0x178) 8 (r mod 2 ^ 64)
  | None => True
  end ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_nearest_STK <= a < e_R (x_e rsegs cx)) ->
   ~ (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\
      e_R (x_e rsegs cx) + 0x178 <= a < e_R (x_e rsegs cx) + 0x178 + 8) ->
   aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W3 (@cfg_at fx3 rsegs 0x824d4 regs3 mem3 md3) POST) ->
SRr rsegs W2 (@cfg_at fx rsegs 0x824cc regs2 mem2 md2) POST.
Proof using MTL LAWS HGOT HSC.
intros cx POST ly2 S2 W2 regs2 mem2 md2 b Hpre Hcore Hpod H9 Hb HF10 Hfrm KN.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
assert (Hsp : spZ regs2 = e_R (x_e rsegs cx)).
{ rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
assert (E9 : ew (Ereg regs2 []) 9 = Z_to_bv 64 (e_R (x_e rsegs cx)))
by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
pose proof (m2_entry (fx := fx) 0x824cc [] [] (mkFacts [] [] []) W2 regs2 [] mem2 (Forall_nil _) eq_refl
  (Forall_nil _) I ltac:(repeat split)) as HS.
remember (Ereg regs2 []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 0x824cc) with (Z_to_bv 64 0x824cc).
(* 0x824cc addi a0,s1,0x178; 0x824d0 jal pod_nearest: stop at 0x82eb4 *)
m2_run m2_awr. ck_keep m2_kwr.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msT end.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H msT), HAE : env_agree 32 _ ?E |- _ =>
  assert (G10 : getr (ms_regs msT) (Z_to_bv 5 10) = w64 (e_R (x_e rsegs cx) + 0x178))
  by (rewrite (st_ok_restrict_reg rsegs H E ss msT (Z_to_bv 5 10) HS);
      replace (sr_get (ss_regs ss) (Z_to_bv 5 10)) with (SOff 9 0x178) by (vm_compute; reflexivity);
      apply m2k_denot_of_U; apply U_atom_off; [exact E9 | lia | lia]);
  assert (G1 : getr (ms_regs msT) 1 = w64 0x824d4)
  by (rewrite (st_ok_restrict_reg rsegs H E ss msT 1%bv HS);
      replace (sr_get (ss_regs ss) 1%bv) with (SLit 0x824d4) by (vm_compute; reflexivity);
      reflexivity);
  assert (Hpr : aregs_preserved regs2 (ms_regs msT))
  by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
  rewrite (st_ok_restrict_mkst rsegs H E ss msT HS eq_refl);
  replace (ss_pc ss) with M2_A_NEAREST by (vm_compute; reflexivity)
end.
assert (HspT : spZ (ms_regs msT) = e_R (x_e rsegs cx)) by (rewrite (m2_sp_pres _ _ Hpr); exact Hsp).
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msT) ?mdT _ |- _ =>
assert (HcoreT : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 (ms_regs msT) (ms_mem msT) mdT)
by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msT) (ms_mem msT) mdT Hcore HJ);
    [ intros r Hr; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | m2_io
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ])
end.
assert (HEc : forall a, (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\
  e_R (x_e rsegs cx) + 0x178 <= a < e_R (x_e rsegs cx) + 0x178 + 8) -> rs_E2 rsegs cx a).
{ intros a (_ & Ha). left. unfold rl_inw. cbn [hi_w2 role_himg_B].
  rewrite !Exists_cons. cbn [rl_xv fst snd].
  right. right. right. right. left. lia. }
eapply SRr_bind.
{ apply (RPgNearA.rl_pod_nearest_B (fx := fx) B MT MTL LAWS HGOT HSC (x_STK rsegs cx) (x_sp0 rsegs cx)
    (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem msT) _ (x_k rsegs cx) (ms_regs msT)
    (e_R (x_e rsegs cx) + 0x178) b).
  - apply (m2_pre_call B MT cx _ _ _ _ _ _ _ T_nearest_STK Hpre HcoreT);
    [ rewrite G1; vm_compute; reflexivity
    | unfold raZ; rewrite G1; unfold w64; rewrite unsigned_lit_small by lia; lia
    | exact HspT | unfold T_nearest_STK, T_SEG_STK, ASTACK; lia ].
  - exact G10.
  - exact Hb.
  - exact HF10.
  - unfold rl_wcell. rewrite HspT. unfold T_SEG_STK, ASTACK in *. split; [left; split; lia | left; lia].
  - pose proof (Z.div_mod (e_R (x_e rsegs cx)) 16 ltac:(lia)) as D. rewrite Hal in D.
    replace (e_R (x_e rsegs cx) + 0x178) with ((2 * (e_R (x_e rsegs cx) / 16) + 47) * 8) by lia.
    apply Z_mod_mult.
  - exact (m2kf_ra_out cx ly2 S2 W2 (ms_regs msT) (ms_mem msT) _ Hpre Hpod HcoreT).
  - exact (m2_rom_at B MT LAWS cx ly2 S2 W2 (ms_regs msT) (ms_mem msT) _ Hpre Hpod HcoreT).
  - exact Hfrm. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx
  (fun x => Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\
     e_R (x_e rsegs cx) + 0x178 <= x < e_R (x_e rsegs cx) + 0x178 + 8) T_nearest_STK ly2 S2 W2 (ms_regs msT)
  (ms_mem msT) _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_nearest_STK, T_SEG_STK, ASTACK; lia) HEc Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & Hrc3).
subst c3. rewrite G1. destruct Hrc3 as (H10' & Hval').
apply (KN fx3 ly3 S3 W3 regs3 mem3 md3 Hfx3 Hcore3 (aregs_preserved_trans _ _ _ Hpr Hpres3) H10' Hval').
intros a Ha Hs Hn. rewrite (Hkept3 a Ha Hs Hn). exact (KE a Ha (fun x => x)).
Qed.

(* 0x824d4 beqz a0 -> MAL; 0x824d8 ld a2,0x178(s1); to JN 0x824dc *)
Lemma m2kf_walk3 : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2
  (o : option Z),
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)) ->
getr regs2 (Z_to_bv 5 10) = w64 (rl_near_rc o) ->
match o with
| Some r => val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x178) 8 (r mod 2 ^ 64)
| None => True
end ->
(o = None -> forall regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W2 (@cfg_at fx rsegs M2_MAL regs3 mem3 md3) POST) ->
(forall r, o = Some r -> forall regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  getr regs3 (Z_to_bv 5 12) = w64 (r mod 2 ^ 64) ->
  SRr rsegs W2 (@cfg_at fx rsegs M2K_JN regs3 mem3 md3) POST) ->
SRr rsegs W2 (@cfg_at fx rsegs 0x824d4 regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST ly2 S2 W2 regs2 mem2 md2 o Hpre Hcore H9 H10 Hval KN KS.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
pose proof (proj1 Hcore) as HJ.
destruct o as [r|].
- (* Some r: the `beqz` is not taken; a2 = the 8 bytes at R + 0x178 *)
  assert (Hr64 : 0 <= r mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (E9 : ew (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 64)]) 9 = Z_to_bv 64 (e_R (x_e rsegs cx)))
  by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
  assert (E32 : ew (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 64)]) 32 = Z_to_bv 64 (r mod 2 ^ 64))
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  pose proof (m2_entry (fx := fx) 0x824d4 [((10%bv : bv 5), SLit 1)]
    [m2_frame 0x178 0x180 0 0 [YP09.mkChunk 0x178 (CVal 8 (SOff 32 0))]] m2_facts W2 regs2
    [Z_to_bv 64 (r mod 2 ^ 64)] mem2) as HS.
  specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
    [ intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
    | rewrite ck_lit; symmetry; exact H10 ]) eq_refl).
  specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; unfold m2_frame;
    apply (rm_ro_region rsegs _ (w_H W2) mem2 9 (e_R (x_e rsegs cx)) 0x178 0x180);
    [ rewrite E9; apply unsigned_lit_small; lia | lia | lia |
      apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val rsegs _ _ (e_R (x_e rsegs cx)) 0x178 8 (SOff 32 0) (r mod 2 ^ 64));
      [ apply m2k_denot_of_U; apply U_atom; [exact E32 | lia]
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hr64 | cbn; lia | exact Hval ] ])).
  specialize (HS ltac:(cbn; tauto)
    (m2_facts_ok (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 64)]) (e_R (x_e rsegs cx))
      ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal)).
  remember (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 64)]) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 64)]) E) by (subst E; apply env_agree_refl).
  assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
  unfold cfg_at. change (w64 0x824d4) with (Z_to_bv 64 0x824d4).
  m2_run_to m2_awr M2K_JN. ck_keep m2_kwr.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    assert (G12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (r mod 2 ^ 64))
    by (rewrite (st_ok_restrict_reg rsegs H E ss ms (Z_to_bv 5 12) HS);
        replace (sr_get (ss_regs ss) (Z_to_bv 5 12)) with (SOff 32 0) by (vm_compute; reflexivity);
        apply m2k_denot_of_U; apply (U_atom E 32 (r mod 2 ^ 64) E32 Hr64));
    assert (Hpr : aregs_preserved regs2 (ms_regs ms))
    by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with M2K_JN by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KS r eq_refl (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ);
    [ intros q Hq; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | m2_io
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
  | exact Hpr
  | intros a Ha; exact (KE a Ha (fun x => x))
  | exact G12 ]
  end.
- (* None: the `beqz` is taken, to MAL (pod_nearest's failure arm) *)
  pose proof (m2_entry (fx := fx) 0x824d4 [((10%bv : bv 5), SLit 0)] [] (mkFacts [] [] []) W2 regs2 [] mem2) as HS.
  specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
    [ intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
    | rewrite ck_lit; symmetry; exact H10 ]) eq_refl (Forall_nil _) I ltac:(repeat split)).
  remember (Ereg regs2 []) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl).
  assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
  unfold cfg_at. change (w64 0x824d4) with (Z_to_bv 64 0x824d4).
  m2_run_to m2_awr M2_MAL. ck_keep m2_kwr.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    assert (Hpr : aregs_preserved regs2 (ms_regs ms))
    by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with M2_MAL by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KN eq_refl (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ);
    [ intros q Hq; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | m2_io
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
Hypothesis LAWS : AR_laws rsegs B.
(* the two symbol-record cells the pod_nearest lift reads *)
Hypothesis HGOT : as_got_shadow B = 0x9aad0.
Hypothesis HSC : as_shadow_cell B = 0xa3678.

Lemma rl_m02_key_float_B : m2k_float_stmt B MT.
Proof using MTL LAWS HGOT HSC.
unfold m2k_float_stmt, m2k_K_float.
intros cx POST rec Hpre HMAL HJOIN fx3 ly3 S3 W3 regs3 mem3 md3 e v HT HL Hv Hent Hty Hm.
pose proof HT as (Hbase & Hat & Hro).
pose proof Hbase as (Hcore & Hfxk & _ & _ & _ & _ & _ & _ & Hpod & _).
destruct Hent as (Hewf & _ & Hvs & Hvb & Hra & Ha1 & Ha2 & Happ).
pose proof Hewf as (Hwt & Hwb & Hws).
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & _).
pose proof (m2k_apart B LAWS cx Hpre) as (Hp0 & _).
(* T's cut: rs_L_chk, then s9 = the code, s6 = pp, s8 = the flags byte, s10 = F, R+0x38 = F, R+0x140 = pp *)
pose proof Hat as Hat'. unfold rs_at_cx, rs_at, rs_L_chk in Hat'.
rewrite Forall_app, !Forall_cons_iff in Hat'.
destruct Hat' as ((A8 & A9 & A19 & A27 & A18 & A20 & AC20 & AC40 & _) &
                  (A25 & A22 & A24 & A26 & AC38 & AC140 & _)).
cbn [rl_at rl_xv fst snd] in A9, A27, A25, A22, A24, A26.
assert (HatA : rs_at_cx rsegs cx W3 mem3 regs3 (rs_L_chk rsegs cx ++ m2k_L_FP cx)).
{ unfold rs_at_cx, rs_at in Hat |- *. rewrite Forall_app in Hat |- *. destruct Hat as (HL1 & HL2).
  split; [exact HL1|]. rewrite !Forall_cons_iff in HL2. destruct HL2 as (_ & _ & _ & _ & X38 & X140 & _).
  unfold m2k_L_FP. apply Forall_cons; [exact X38|]. apply Forall_cons; [exact X140 | apply Forall_nil]. }
(* FLT's own values: a0 = &ent[v], a7 = pp + 0x4018, s7 = 104 v, R+0x120 = 0x4018 *)
pose proof HL as HL'. unfold rs_at_cx, rs_at, m2k_L_flt in HL'. rewrite !Forall_cons_iff in HL'.
destruct HL' as (L10 & L17 & L23 & LC120 & _). cbn [rl_at rl_xv fst snd] in L10, L17, L23, LC120.
replace (0x4018 mod 2 ^ 64) with 0x4018 in LC120 by reflexivity.
unfold m2k_ea in Ha1, Ha2, Happ, Hra, Hvs, Hvb, L10.
assert (HPA : rs_PA rsegs cx rec = Role.expect_value e).
{ destruct Hm as (HE0 & HPs & HPf).
  rewrite <- HE0, (surjective_pairing (rs_PA rsegs cx rec)), HPf, HPs. symmetry. apply surjective_pairing. }
(* the exit to T's cut, from the cut at FLT, at a state whose registers m2kf_L are kept, whose memory agrees outside
   m2k_wz and whose float state keeps fx outside fa0, fa3, fa4, fa5 *)
assert (XT : forall (fx5 : YK11.FPState) ly5 S5 W5 regs5 mem5 md5,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly5 S5 W5 regs5 mem5 md5 -> cs_eq m2kf_L regs3 regs5 ->
  rl_fxk [10; 13; 14; 15] fx fx5 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ m2k_wz cx a -> aview rsegs (w_H W5) mem5 a = aview rsegs (w_H W3) mem3 a) ->
  rs_cut_T (fx := fx) rsegs B MT cx fx5 rec ly5 S5 W5 regs5 mem5 md5).
{ intros fx5 ly5 S5 W5 regs5 mem5 md5 Hcore5 Hcs5 Hfxk5 K5.
  apply (m2k_cut_T B MT LAWS cx fx3 fx5 rec ly3 S3 W3 regs3 mem3 md3 ly5 S5 W5 regs5 mem5 md5 Hpre Hbase Hro HatA
    Hcore5 Hfxk5 (m2k_cs_sub _ _ _ _ m2kf_L5_sub Hcs5)).
  - rewrite (Hcs5 (Z_to_bv 5 25) ltac:(m2kf_inL)). exact A25.
  - rewrite (Hcs5 (Z_to_bv 5 22) ltac:(m2kf_inL)). exact A22.
  - rewrite (Hcs5 (Z_to_bv 5 24) ltac:(m2kf_inL)). exact A24.
  - rewrite (Hcs5 (Z_to_bv 5 26) ltac:(m2kf_inL)). exact A26.
  - exact K5. }
apply (m2kf_walk1 (fx := fx3) B MT MTL LAWS cx POST ly3 S3 W3 regs3 mem3 md3
  (e_pp (x_e rsegs cx) + 0x4014 + 104 * Z.of_nat v) (e_pp (x_e rsegs cx)) (104 * Z.of_nat v) (e_size e) (m2k_bw e)
  Hpre Hcore A9 A27 L10 L17 L23 A22 eq_refl ltac:(lia) ltac:(lia) Ha1 Ha2 Happ Hra LC120 Hvs ltac:(lia) Hvb
  (m2k_bw_range e Hewf)).
- (* the size is below 4: MAL *)
  intros Hlt regs4 mem4 md4 Hcore4 Hcs4 K4.
  apply (HMAL fx3 ly3 S3 W3 regs4 mem4 md4 rec).
  apply m2k_mal_of_T.
  + apply (XT fx3 ly3 S3 W3 regs4 mem4 md4 Hcore4 Hcs4 Hfxk). intros a Ha _. exact (K4 a Ha).
  + rewrite HPA, m2k_expect_none; [reflexivity | right; exact Hlt].
  + rewrite HPA, m2k_expect_none; [reflexivity | right; exact Hlt].
- (* the body word in fa0, then pod_nearest *)
  intros Hge regs4 mem4 md4 Hcore4 Hcs4 K4.
  assert (Hfxk4 : rl_fxk [10; 13; 14; 15] fx (m2kf_fx4 fx3 (m2k_bw e)))
  by (apply m2kf_fxk_set; [left; reflexivity | exact Hfxk]).
  apply (m2kf_walk2 (fx := m2kf_fx4 fx3 (m2k_bw e)) B MT MTL LAWS HGOT HSC cx POST ly3 S3 W3 regs4 mem4 md4 (m2k_bw e)
    Hpre Hcore4 Hpod ltac:(rewrite (Hcs4 (Z_to_bv 5 9) ltac:(m2kf_inL)); exact A9) (m2k_bw_range e Hewf)
    (m2kf_f10 fx3 (m2k_bw e)) (proj2 Hfxk)).
  intros fx5 ly5 S5 W5 regs5 mem5 md5 Hfx5 Hcore5 Hpr5 H10' Hval' K5.
  assert (Hfxk5 : rl_fxk [10; 13; 14; 15] fx fx5)
  by (apply (m2kf_fxk_trans _ _ _ _ _ Hfxk4 Hfx5); intros z Hz; cbn in Hz |- *; tauto).
  assert (Hcs35 : cs_eq m2kf_L regs3 regs5)
  by exact (cs_eq_trans _ _ _ _ Hcs4 (cs_eq_of_pres _ _ _ m2kf_L_cs Hpr5)).
  apply (m2kf_walk3 (fx := fx5) B MT MTL LAWS cx POST ly5 S5 W5 regs5 mem5 md5
    (Nearest.nearest (m2k_bw e) Nearest.INT32_MIN Nearest.INT32_MAX) Hpre Hcore5
    ltac:(rewrite (Hcs35 (Z_to_bv 5 9) ltac:(m2kf_inL)); exact A9) H10' Hval').
  + (* None: MAL *)
    intros Hn regs6 mem6 md6 Hcore6 Hpr6 K6.
    apply (HMAL fx5 ly5 S5 W5 regs6 mem6 md6 rec).
    assert (HPA' : rs_PA rsegs cx rec = (None, -1)).
    { rewrite HPA, (m2k_expect_float e Hty Hge), <- (m2k_bw_rd32 e Hewf Hge), Hn. reflexivity. }
    apply m2k_mal_of_T; [| rewrite HPA'; reflexivity | rewrite HPA'; reflexivity].
    apply (XT fx5 ly5 S5 W5 regs6 mem6 md6 Hcore6 (cs_eq_trans _ _ _ _ Hcs35 (cs_eq_of_pres _ _ _ m2kf_L_cs Hpr6))
      Hfxk5).
    intros a Ha Hw. unfold m2k_wz in Hw.
    rewrite (K6 a Ha), (K5 a Ha ltac:(unfold T_nearest_STK, T_SEG_STK, ASTACK in *; lia)
      ltac:(intros (Hne & _); exact (Hne Hn))).
    exact (K4 a Ha).
  + (* Some r: the join, with a2 = r mod 2^64 *)
    intros r Hr regs6 mem6 md6 Hcore6 Hpr6 K6 H12.
    assert (HPA' : rs_PA rsegs cx rec = Role.flag_rc r).
    { rewrite HPA, (m2k_expect_float e Hty Hge), <- (m2k_bw_rd32 e Hewf Hge), Hr. reflexivity. }
    pose proof (m2k_nearest_range _ _ Hr) as Hrr.
    apply (HJOIN fx5 ly5 S5 W5 regs6 mem6 md6 (r mod 2 ^ 64)).
    * apply (XT fx5 ly5 S5 W5 regs6 mem6 md6 Hcore6 (cs_eq_trans _ _ _ _ Hcs35 (cs_eq_of_pres _ _ _ m2kf_L_cs Hpr6))
        Hfxk5).
      intros a Ha Hw. unfold m2k_wz in Hw.
      rewrite (K6 a Ha), (K5 a Ha ltac:(unfold T_nearest_STK, T_SEG_STK, ASTACK in *; lia)
        ltac:(intros (_ & Hx); lia)).
      exact (K4 a Ha).
    * exact H12.
    * apply Z.mod_pos_bound. lia.
    * (* a word below 2: the answer is a role, whose role_z is the word *)
      intros Hlt. pose proof (proj1 (m2kf_mod_small r Hrr) Hlt) as H01.
      destruct (m2k_flag_small r ltac:(lia)) as (Hs1 & w & Hw & Hz).
      rewrite HPA'. split; [exact Hs1|].
      rewrite Hw. cbn [rs_rcell]. rewrite Hz. symmetry. apply Z.mod_small. lia.
    * (* a word of 2 or more: no role *)
      intros Hge2.
      assert (Hn01 : ~ (r = 0 \/ r = 1)) by (intros Hc; apply (m2kf_mod_small r Hrr) in Hc; lia).
      rewrite HPA', (m2k_flag_big r ltac:(lia)). split; reflexivity.
Qed.
End t.
