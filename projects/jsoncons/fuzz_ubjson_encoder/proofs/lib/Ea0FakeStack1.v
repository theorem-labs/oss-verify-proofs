(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib Ea0RegionPoisoned Ea0AsanMemset Ea0AsanMemcpy Ea0StrlenIcpt Ea0TlsGetAddr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r48448_48dd8 Ea0_code_r4dae8_4daec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import OtfKit.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_encoder.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_encoder.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_encoder.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_encoder.images.Asan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma memtoshadow47_run : forall regs (M rom : word -> option byte) (ret : word) (p : Z),
  rt_layout_globs M -> in_app p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 1 = ret -> ret_ok ret ->
  exists regs',
    msteps ASEGS (mkst regs (0x5ed20 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 (p / 8 + SB) /\ keeps_cs regs regs'.
Proof. intros regs M rom ret p.
intros (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) Hp H10 H1 Hret.
unfold in_app, LOWEND, HIGHBEG, HIGHEND in Hp. unfold SB in *.
pose proof (Z.div_mod p 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hmd.
destruct Hp as [Hlow|Hhigh].
- eexists. split.
+ stepn (ltac:(oF' 0x5ed20%Z)) (ltac:(oD' 0x5ed20%Z)).
mld (ltac:(oF' 0x5ed24%Z)) (ltac:(oD' 0x5ed24%Z)) (0x1391b8 : word) G1.
mld (ltac:(oF' 0x5ed28%Z)) (ltac:(oD' 0x5ed28%Z)) (0x1419f8 : word) G2.
stepn (ltac:(oF' 0x5ed2c%Z)) (ltac:(oD' 0x5ed2c%Z)).
stepn (ltac:(oF' 0x5ed30%Z)) (ltac:(oD' 0x5ed30%Z)).
stepn (ltac:(oF' 0x5ed34%Z)) (ltac:(oD' 0x5ed34%Z)).
stepn (ltac:(oF' 0x5ed38%Z)) (ltac:(oD' 0x5ed38%Z)).
stepb_tk (ltac:(oF' 0x5ed3c%Z)) (ltac:(oD' 0x5ed3c%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x5ed80%Z)) (ltac:(oD' 0x5ed80%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x5ed84%Z)) (ltac:(oD' 0x5ed84%Z)) (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).
stepret (ltac:(oF' 0x5ed88%Z)) (ltac:(oD' 0x5ed88%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
+ split; [gres; reflexivity | solve_keeps_cs].
- eexists. split.
+ stepn (ltac:(oF' 0x5ed20%Z)) (ltac:(oD' 0x5ed20%Z)).
mld (ltac:(oF' 0x5ed24%Z)) (ltac:(oD' 0x5ed24%Z)) (0x1391b8 : word) G1.
mld (ltac:(oF' 0x5ed28%Z)) (ltac:(oD' 0x5ed28%Z)) (0x1419f8 : word) G2.
stepn (ltac:(oF' 0x5ed2c%Z)) (ltac:(oD' 0x5ed2c%Z)).
stepn (ltac:(oF' 0x5ed30%Z)) (ltac:(oD' 0x5ed30%Z)).
stepn (ltac:(oF' 0x5ed34%Z)) (ltac:(oD' 0x5ed34%Z)).
stepn (ltac:(oF' 0x5ed38%Z)) (ltac:(oD' 0x5ed38%Z)).
stepb_ft (ltac:(oF' 0x5ed3c%Z)) (ltac:(oD' 0x5ed3c%Z)) ltac:(cond).
stepn (ltac:(oF' 0x5ed40%Z)) (ltac:(oD' 0x5ed40%Z)).
mld (ltac:(oF' 0x5ed44%Z)) (ltac:(oD' 0x5ed44%Z)) (0x1391c0 : word) G3.
stepn (ltac:(oF' 0x5ed48%Z)) (ltac:(oD' 0x5ed48%Z)).
mld (ltac:(oF' 0x5ed4c%Z)) (ltac:(oD' 0x5ed4c%Z)) (0x1391c8 : word) G5.
mld (ltac:(oF' 0x5ed50%Z)) (ltac:(oD' 0x5ed50%Z)) (0x1426e8 : word) G4.
mld (ltac:(oF' 0x5ed54%Z)) (ltac:(oD' 0x5ed54%Z)) (0x1426f0 : word) G6.
stepn (ltac:(oF' 0x5ed58%Z)) (ltac:(oD' 0x5ed58%Z)).
stepb_tk (ltac:(oF' 0x5ed5c%Z)) (ltac:(oD' 0x5ed5c%Z)) ltac:(cond).
stepn (ltac:(oF' 0x5ed64%Z)) (ltac:(oD' 0x5ed64%Z)).
mld (ltac:(oF' 0x5ed68%Z)) (ltac:(oD' 0x5ed68%Z)) (0x1391d0 : word) G7.
mld (ltac:(oF' 0x5ed6c%Z)) (ltac:(oD' 0x5ed6c%Z)) (0x1426e0 : word) G8.
stepn (ltac:(oF' 0x5ed70%Z)) (ltac:(oD' 0x5ed70%Z)).
stepn (ltac:(oF' 0x5ed74%Z)) (ltac:(oD' 0x5ed74%Z)).
stepb_ft (ltac:(oF' 0x5ed78%Z)) (ltac:(oD' 0x5ed78%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x5ed7c%Z)) (ltac:(oD' 0x5ed7c%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x5ed80%Z)) (ltac:(oD' 0x5ed80%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x5ed84%Z)) (ltac:(oD' 0x5ed84%Z)) (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).
stepret (ltac:(oF' 0x5ed88%Z)) (ltac:(oD' 0x5ed88%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
+ split; [gres; reflexivity | solve_keeps_cs].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_8191 : forall a, Z.land a 8191 = (a mod 8192)%Z.
Proof. intros a. change 8191%Z with (Z.ones 13). rewrite Z.land_ones by lia. reflexivity. Qed.

Section FSM1.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra a0v : word.
  (* [comment removed for export] *)
  Variables s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec : Z.
  (* [comment removed for export] *)
  Variables fs h pos ff : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hs : (0x1000000 <= s - 208)%Z /\ (s < 2 ^ 64)%Z.          (* [comment removed for export] *)
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 208)) 208%nat = true.
  Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hmd : (0 <= md < 255)%Z.
  Hypothesis Hoff : (0 <= off < 2 ^ 64)%Z.
  Hypothesis Hdtv : (0 <= dtv /\ dtv + 8 * md + 8 <= 2 ^ 64)%Z.
  Hypothesis Hent : (0 <= ent < 2 ^ 64)%Z.
  Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
  Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
  Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
  Hypothesis Hth : (0 < th /\ th + 64 <= 2 ^ 64)%Z.
  Hypothesis Htbe : (0 <= tb < 2 ^ 64)%Z /\ (0 <= te < 2 ^ 64)%Z.
  Hypothesis HF : (0 <= F /\ F + 256 <= 2 ^ 64)%Z.
  Hypothesis HV : (0 <= V /\ V + 4 <= 2 ^ 64)%Z.
  Hypothesis Hverb : (0 <= verb < 3)%Z.
  Hypothesis Hdto : (0 <= dto /\ 0 <= dto + tpv /\ dto + tpv + 8 <= 2 ^ 64)%Z.
  Hypothesis Hblk : (0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z.
  Hypothesis Hrec : (0 < rec < 2 ^ 64)%Z.
  Hypothesis HC0 : forall M', (forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) ->
    tls_cells tpv 0x139fb0 md off dtv ent key tsd ctx th tb te F V verb dto blk rec M'.
  (* [comment removed for export] *)
  Hypothesis Hfs : (0x698000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 208 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Hh : (0 <= h < 2 ^ 62)%Z.
  Hypothesis Hpos_def : pos = (h mod 8192)%Z.
  Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 2 ^ 20 + 128 * pos)%Z.
  Definition tls_r : Z := tls_res off ent.
  Hypothesis Hr : (0 <= tls_r /\ tls_r + 8 < 2 ^ 64)%Z /\ (tls_r + 8 <= s - 208 \/ s <= tls_r)%Z /\ (tls_r + 8 <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= tls_r)%Z.
  Hypothesis HRfs : rdn ASEGS mem0 (Z_to_bv 64 tls_r) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fs)).
  Hypothesis Hng : rdn ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 0].                     (* [comment removed for export] *)
  Hypothesis Hssl : rdn ASEGS mem0 (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).   (* [comment removed for export] *)
  Hypothesis Hhint : rdn ASEGS mem0 (Z_to_bv 64 (fs + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h)). (* [comment removed for export] *)
  Hypothesis Hflag : rdn ASEGS mem0 (Z_to_bv 64 (fs + 4096 + 16384 + pos)) 1%nat = Some [Z_to_bv 8 0].      (* [comment removed for export] *)
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.   (* [comment removed for export] *)
  Hypothesis HG : rt_layout_globs mem0.
  Hypothesis Happ : in_app ff.
  Hypothesis Hshadow_ok : store_ok ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) 16%nat = true.
  Hypothesis Hshadow_dj : (SB + ff / 8 + 16 <= s - 208 \/ s <= SB + ff / 8)%Z /\ (SB + ff / 8 + 16 <= 0x1391b8 \/ 0x1426f8 <= SB + ff / 8)%Z.

  #[local] Ltac hide_dj := try hide Hfs; try hide Hr; try hide Hshadow_dj.

  (* [comment removed for export] *)
  Definition F4 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
           (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)).

  (* [comment removed for export] *)
  Definition fsm1_mem (Mj : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes Mj
      (Z_to_bv 64 (fs + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (h + 1))))                 (* [comment removed for export] *)
      (Z_to_bv 64 (fs + 4096 + 16384 + pos)) [Z_to_bv 8 1])                             (* [comment removed for export] *)
      (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s)))                      (* [comment removed for export] *)
      (Z_to_bv 64 (ff + 120)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 16384 + pos))))   (* [comment removed for export] *)
      (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))                   (* [comment removed for export] *)
      (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).                (* [comment removed for export] *)

  Lemma sp_s1 : sp = Z_to_bv 64 s.
Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
End FSM1.
End FPX_1.
