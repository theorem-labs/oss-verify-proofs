(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr ITree Nodes SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages SysStepA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AI_shadow AI_globals2 AM_syscalls AI_region_is_poisoned.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition read_icp_entry : Z := 0x44e1c.
End RC__1.
Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition read_icp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B count SB : Z) (junk ws : list byte) (errv : word) (lo : Z) (m : mem) (a : read_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp); (B, B + count); (errno_addr tp, errno_addr tp + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells asegs m' B [CB (Z.to_nat count) junk]
                    /\ rw_cells asegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ 1 <= e <= 4095
       | RdData bs => rw_cells asegs m' B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)]
                      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ (length bs <= Z.to_nat count)%nat
       end
    /\ icp_globals asegs m' SB /\ icp_globals2 asegs m' /\ shadow_window asegs m' SB B count ws.

Section Walk.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (fd B count SB : Z) (junk ws : list byte) (errv : word) (lo : Z).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 2208.
Hypothesis HFD : 3 <= fd < 2^32.
Hypothesis HCNT : 0 < count <= 65536.
Hypothesis RIM : range_in_mem SB B count.
Hypothesis HBN : B + count < 2^47.
Hypothesis HTP : 0x13fdd0 <= errno_addr tp /\ errno_addr tp + 4 <= 0x603000.
Hypothesis HDISJ : B + count <= lo \/ bv_unsigned sp <= B.
Hypothesis HBE : B + count <= errno_addr tp \/ errno_addr tp + 4 <= B.
Hypothesis HGL : B + count <= 0xa4000 \/ 0x13fdd0 <= B.
Hypothesis SHL : Z.of_nat (length ws) = shw_hi SB B count - shw_lo SB B.
Hypothesis RC : range_clean SB B count ws.
Hypothesis HSWD : shw_hi SB B count <= B \/ B + count <= shw_lo SB B.
Hypothesis SBR : 2^24 <= SB < 2^32.
Hypothesis G20 : icp_globals2 asegs m.                      (* [comment removed for export] *)
Hypothesis SHB0 : bytes_at asegs m (shw_lo SB B) ws.
Hypothesis PSH : forall a k, shw_lo SB B <= a -> a + Z.of_nat k <= shw_hi SB B count -> P (Z_to_bv 64 a, k).
Hypothesis PERR : forall a k, errno_addr tp <= a -> a + Z.of_nat k <= errno_addr tp + 4 -> P (Z_to_bv 64 a, k).
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PBUF : forall a k, B <= a -> a + Z.of_nat k <= B + count -> P (Z_to_bv 64 a, k).
Hypothesis PSTK : forall a k, bv_unsigned sp - 2208 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).

Notation POST := (read_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B count SB junk ws errv lo m).
Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -2128)).
Ltac hideD := hideH HDISJ; hideH HBE; hideH HGL; hideH HSWD; hideH RIM.
Ltac unhideD := unfold hidden in HDISJ, HBE, HGL, HSWD, RIM.
Lemma BNDS : 0 < B /\ B + count < 2^47.
Proof. unfold range_in_mem in RIM. lia. Qed.
Lemma GEOC :
  shw_lo SB B <= SB + Z.shiftr B 3 /\ shw_hi SB B count <= SB + Z.shiftr (B + count + -1) 3 + 8 /\
  0 <= Z.shiftr B 3 /\ 8 * Z.shiftr (B + count + -1) 3 <= B + count + -1.
Proof. pose proof BNDS. pose proof (shw_geom SB B count ltac:(lia) ltac:(lia) ltac:(lia)) as G. cbv zeta in G. lia. Qed.

(* [comment removed for export] *)
Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31 :=
  (MS (mkR x1 SP' gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 fd) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Section Data.
Variable bs : list byte.
Variable ws' : list byte.     (* [comment removed for export] *)
Notation res := (Z.of_nat (length bs)).
Hypothesis HRES : 1 <= res <= count.
Hypothesis SHL' : Z.of_nat (length ws') = shw_hi SB B res - shw_lo SB B.
Hypothesis RC' : range_clean SB B res ws'.
Hypothesis HLE : shw_hi SB B res <= shw_hi SB B count.
Notation g1 := (Z.shiftr B 3).
Notation g2 := (Z.shiftr (B + res + -1) 3).

(* [comment removed for export] *)
Definition MINVD (m0 : mem) : Prop :=
  mem_inv asegs m0 /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp); (B, B + count); (errno_addr tp, errno_addr tp + 4)] m m0 /\
  wmono asegs m m0 /\ stk asegs m0 lo (bv_unsigned sp + -48) /\
  rw_cells asegs m0 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  rw_cells asegs m0 B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)] /\
  rw_cells asegs m0 (errno_addr tp) [C4 errv] /\
  icp_globals asegs m0 SB /\ bytes_at asegs m0 (shw_lo SB B) ws'.
Ltac open_minv H := destruct H as (MI & MU & WM & SK & FR & DST & ERR & G & SHB).

Lemma PSH' : forall a k, shw_lo SB B <= a -> a + Z.of_nat k <= shw_hi SB B res -> P (Z_to_bv 64 a, k).
Proof. intros a k H1 H2. apply PSH; lia. Qed.

Lemma GEO :
  0 <= g1 /\ g1 <= g2 /\ 8 * g1 <= B < 8 * g1 + 8 /\ 8 * g2 <= B + res + -1 < 8 * g2 + 8 /\
  shw_lo SB B <= SB + g1 /\ SB + g1 < shw_lo SB B + 8 /\ shw_lo SB B mod 8 = 0 /\
  shw_hi SB B res - 8 <= SB + g2 /\ SB + g2 < shw_hi SB B res /\ shw_hi SB B res mod 8 = 0 /\
  shw_lo SB B + 8 <= shw_hi SB B res.
Proof. pose proof BNDS. exact (shw_geom SB B res ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

Notation POSTD := (POST (RdData bs)).

(* [comment removed for export] *)
Lemma rdi_tail : forall m0 x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31,
  MINVD m0 ->
  evtA asegs P POSTD (ST 0x44ecc m0 x1 x5 x6 x7 x9 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. open_minv IV. hideD.
  stepA. (* [comment removed for export] *) do 6 stepA. (* [comment removed for export] *) stepA. stepA. (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp).
  unhideD. pose proof GEOC as GC. pose proof BNDS as BN.
  pose proof G20 as G2. eapply (icp_globals2_transport asegs) in G2; [ | exact MU | exact WM | cbn; lia | cbn; lia ].
  pose proof GEO as GE. pose proof SHB0 as SHF. eapply (bytes_at_transport asegs) in SHF; [ | exact MU | cbn; lia ].
  apply evtA_done. unfold read_icp_post.
  do 15 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
  split; [exact SHF | exact SHL].
Qed.

(* [comment removed for export] *)
Lemma rdi_loop : forall k (Q : machine_state -> Prop) m0 j x1 x5 x6 x7 x10 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31,
  Z.to_nat (g2 - j) = k -> g1 <= j < g2 ->
  bytes_at asegs m0 (shw_lo SB B) ws' ->
  evtA asegs P Q (ST 0x45040 m0 x1 x5 x6 x7 (Z_to_bv 64 B) x10 (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 0) (Z_to_bv 64 0) x15 x16 x17 x18 x20 x28 x29 x30 x31) ->
  evtA asegs P Q (ST 0x45030 m0 x1 x5 x6 x7 (Z_to_bv 64 B) x10 (Z_to_bv 64 (SB + j)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 0) x14 x15 x16 x17 x18 x20 x28 x29 x30 x31).
Proof.
  induction k as [|k IH]; intros until x31; intros Hk Hj SHB CONT; pose proof GEO as GE; [lia|]. hideD.
  pose proof PSH' as PSW.
  pose proof (range_clean_inner SB B res ws' j RC' ltac:(lia)) as Hb.
  pose proof (u8ro_read asegs m0 (shw_lo SB B) ws' (SB + j - shw_lo SB B) _ (Z_to_bv 64 (SB + j)) SHB Hb ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K; zify_cond K.
  - replace (SB + j + 1) with (SB + (j + 1)) by lia. eapply (IH Q m0 (j + 1)); try lia; try assumption.
  - replace (SB + j + 1) with (SB + g2) by lia. exact CONT.
Qed.

(* [comment removed for export] *)
Lemma rdi_join : forall m0 x1 x5 x6 x7 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31,
  MINVD m0 ->
  evtA asegs P POSTD (ST 0x45040 m0 x1 x5 x6 x7 (Z_to_bv 64 B) (Z_to_bv 64 res) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 0) x14 x15 x16 x17 x18 x20 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. hideD.
  zstepA. zstepA. (* [comment removed for export] *)
  eapply rdi_tail; exact IV.
Qed.

(* [comment removed for export] *)
Lemma rdi_slow : forall m0 x1 x5 x6 x7 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31,
  MINVD m0 ->
  evtA asegs P POSTD (ST 0x45014 m0 x1 x5 x6 x7 (Z_to_bv 64 B) (Z_to_bv 64 res) (Z_to_bv 64 (SB + g1)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (B + res + -1)) x14 x15 x16 x17 x18 x20 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. pose proof IV as IV'. open_minv IV.
  pose proof GEO as GE. pose proof PSH' as PSW. hideD.
  destruct (RC' g2 ltac:(lia)) as (k2 & Hk2 & K2).
  pose proof (u8ro_read asegs m0 (shw_lo SB B) ws' (SB + g2 - shw_lo SB B) _ (Z_to_bv 64 (SB + g2)) SHB Hk2 ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  lazymatch goal with |- context [Z_to_bv 64 (Z.land (Z.b2z ?t) ?u)] =>
    change (Z.land (Z.b2z t) u) with (aip_expr (bv_unsigned (sxb k2)) (Z.land (B + res + -1) 7)) end.
  rewrite (aip_last_clean k2 (B + res + -1)) by (first [lia | destruct K2 as [K2|[_ K2]]; [left; exact K2| right; lia]]).
  zstepA. (* [comment removed for export] *)
  clear MI MU WM SK FR DST ERR G.
  if_cases KG; zify_cond KG.
  - replace (SB + g1) with (SB + g2) by lia. eapply rdi_join; exact IV'.
  - eapply (rdi_loop (Z.to_nat (g2 - g1)) _ m0 g1); [reflexivity | lia | exact SHB |].
    eapply rdi_join; exact IV'.
Qed.

(* [comment removed for export] *)
Lemma rdi_small : forall m0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31,
  MINVD m0 -> res <= 64 ->
  evtA asegs P POSTD (ST 0x44e90 m0 x1 x5 x6 x7 (Z_to_bv 64 B) (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV Hr64. pose proof IV as IV'. open_minv IV.
  pose proof GEO as GE. pose proof PSH' as PSW. pose proof BNDS as BN. hideD.
  icp_globals_open G.
  stepA. stepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  rewrite ?land_m8, ?land_m8' by lia.
  change (al8 (SB + B ≫ 3)) with (shw_lo SB B).
  replace (al8 (SB + (B + res + -1) ≫ 3)) with (shw_hi SB B res - 8) by (unfold shw_hi; lia).
  pose proof (bytes_at_read asegs _ _ _ 0 8 SHB ltac:(lia) ltac:(lia)) as RD1. rewrite Z.add_0_r in RD1.
  stepA. clear RD1.
  pose proof (bytes_at_read asegs _ _ _ (shw_hi SB B res - 8 - shw_lo SB B) 8 SHB ltac:(lia) ltac:(lia)) as RD2.
  replace (shw_lo SB B + (shw_hi SB B res - 8 - shw_lo SB B)) with (shw_hi SB B res - 8) in RD2 by lia.
  stepA. clear RD2.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  clear MI MU WM SK FR DST ERR SHB GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI.
  if_cases KW.
  - eapply rdi_slow; exact IV'.
  - eapply rdi_tail; exact IV'.
Qed.

(* [comment removed for export] *)
Lemma rdi_big : forall m0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31,
  MINVD m0 -> 65 <= res ->
  evtA asegs P POSTD (ST 0x44f68 m0 x1 x5 x6 x7 (Z_to_bv 64 B) (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV Hr65. open_minv IV.
  pose proof GEO as GE. pose proof BNDS as BN. pose proof PSH' as PSW.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR. hideD.
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2128)) = bv_unsigned sp + -2128) by (apply unsigned_lit; lia).
  destruct (stk_split asegs m0 lo (bv_unsigned sp + -2128) (bv_unsigned sp + -48) SK ltac:(lia)) as [SKlo SKhi]. clear SK.
  pose proof G as Gc. icp_globals_open Gc.
  unhideH HDISJ. unhideH HBE.
  callA (region_is_poisoned_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B res SB ws' lo P).
  1:{ rewrite USP. exact SKlo. }
  1:{ unfold alloc_ceiling, sp_window_lo, stack_max_size. lia. }
  1:{ rewrite USP. lia. }
  1:{ exact MI. }
  1:{ reflexivity. } 1:{ reflexivity. }
  1:{ lia. } 1:{ lia. }
  1:{ unhideD. unfold range_in_mem in RIM |- *. lia. }
  1:{ exact G. }
  1:{ split; [exact SHB | exact SHL']. } 1:{ exact RC'. }
  1:{ intros a k H1 H2. rewrite USP in H1, H2. apply PSTK; lia. }
  1:{ exact PIMG. } 1:{ exact PSW. }
  ret_pc_lit. hideD.
  lazymatch goal with H : stk asegs ?mx lo _ |- _ => rename H into SKlo2; rewrite USP in SKlo2 end.
  lazymatch goal with H : stk asegs ?mx _ (bv_unsigned sp + -48) |- _ =>
    pose proof (stk_merge asegs _ _ _ _ SKlo2 H ltac:(lia)) as SK2; clear H SKlo2 end.
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  eapply rdi_tail. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact SK2|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split. { unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
             A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL.
           repeat (split; [assumption|]). lia. }
  eassumption.
Qed.

(* [comment removed for export] *)
Lemma rdi_check : forall m0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31,
  MINVD m0 ->
  evtA asegs P POSTD (ST 0x44e74 m0 x1 x5 x6 x7 (Z_to_bv 64 B) (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 1) x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. pose proof BNDS as BN. hideD.
  zstepA. (* [comment removed for export] *) rewrite not64 by lia.
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) if_cases K1; zify_cond K1. { exfalso. lia. }
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K2; zify_cond K2.
  - assert (65 <= res). { destruct (Z.leb_spec 65 res); [assumption|]. exfalso. revert K2. rewrite mod64_neg_small by lia. lia. }
    eapply rdi_big; [exact IV | lia].
  - assert (res <= 64). { destruct (Z.leb_spec res 64); [assumption|]. exfalso. revert K2. rewrite Z.mod_small by lia. lia. }
    eapply rdi_small; [exact IV | lia].
Qed.
End Data.

(* [comment removed for export] *)
Lemma read_icp_body : forall x10 x11 x12,
  stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
  x10 = Z_to_bv 64 fd -> x11 = Z_to_bv 64 B -> x12 = Z_to_bv 64 count ->
  rw_cells asegs m B [CB (Z.to_nat count) junk] -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
  icp_globals asegs m SB ->
  implA asegs (at_nodeA asegs) P (enode (NRead fd B count) (dec_read B count)) (epost POST)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 read_icp_entry) fc None m (seg_rom asegs)).
Proof.
  intros x10 x11 x12 SK MI -> -> -> DST ERR G. unfold read_icp_entry. pose proof G20 as G2. pose proof SHB0 as SHB. hideH SHB0.
  pose proof GEOC as GC.
  pose proof BNDS as BN.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  assert (MU : munch [(bv_unsigned sp - 2208, bv_unsigned sp); (B, B + count); (errno_addr tp, errno_addr tp + 4)] m m) by apply munch_refl.
  assert (MU0 : munch [(bv_unsigned sp - 2208, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  pose proof (conj DST (conj ERR SHB)) as RO. clear DST ERR SHB.
  iprefixA.
  hideD. carve_frame 48%nat SK.
  do 9 stepA.   (* [comment removed for export] *)
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (icp_globals_transport asegs) in G; [ | exact MU0 | exact WM | cbn; lia ];
    eapply (icp_globals2_transport asegs) in G2; [ | exact MU0 | exact WM | cbn; lia | cbn; lia ]
  end.
  pose proof G as G'. icp_globals_open G. pose proof (ig2_read asegs _ G2) as GRR.
  (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  destruct (stk_split asegs _ lo (bv_unsigned sp + -2128) (bv_unsigned sp + -48) SK ltac:(lia)) as [SKlo SKhi]. clear SK.
  carve_frame 16%nat SKlo.
  stepA. stepA. stepA. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
  cbv beta. stepA. (* [comment removed for export] *) if_false.
  stepA. stepA. stepA. stepA. (* [comment removed for export] *)
  lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -2144) _ |- _ => release_frame H SKlo (bv_unsigned sp + -2128) end.
  stepA. stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (UB : bv_unsigned (Z_to_bv 64 B) = B) by (apply unsigned_lit; lia).
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2128)) = bv_unsigned sp + -2128) by (apply unsigned_lit; lia).
  unhideD. destruct RO as (DST & ERR & SHB).
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (rw_cells_transport asegs) in DST; [ | exact MU0 | exact WM | cbn; lia ];
    eapply (rw_cells_transport asegs) in ERR; [ | exact MU0 | exact WM | cbn; lia ];
    eapply (bytes_at_transport asegs) in SHB; [ | exact MU0 | cbn; lia ] end.
  clear MU0.
  icallxA (read_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fd B count junk errv lo P).
  1:{ exact PBUF. }
  1:{ exact PERR. }
  1:{ intros a k H1 H2. rewrite USP in H1, H2. apply PSTK; lia. }
  1:{ rewrite USP. lazymatch goal with H : stk asegs _ lo (bv_unsigned sp + -2128) |- _ => exact H end. }
  1:{ exact DST. }
  1:{ exact ERR. }
  1:{ assumption. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  1:{ lia. } 1:{ exact HFD. } 1:{ exact HCNT. } 1:{ unfold TASK_SIZE; lia. }
  1:{ rewrite USP. lia. }
  1:{ rewrite USP. lia. } 1:{ rewrite USP. lia. } 1:{ lia. } 1:{ lia. }
  (* [comment removed for export] *)
  intros a ms' RP. unfold read_post in RP. rewrite ?UB, ?USP in RP.
  destruct RP as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & -> & MUc & WMc & MIc & SKc & RA).
  rewrite Z2Nat.id in MUc by lia.
  pose proof GEOC as GC'. clear DST ERR.
  transport_after_call asegs m2 m3 MUc WMc. clear MUc WMc MI.
  ret_pc_lit. hideD.
  lazymatch goal with H : stk asegs m3 (bv_unsigned sp + -2128) (bv_unsigned sp + -48) |- _ =>
    pose proof (stk_merge asegs _ _ _ _ SKc H ltac:(lia)) as SK; clear H SKc end.
  (* [comment removed for export] *)
  assert (TAIL0 : forall r mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    mem_inv asegs mm ->
    munch [(bv_unsigned sp - 2208, bv_unsigned sp); (B, B + count); (errno_addr tp, errno_addr tp + 4)] m mm ->
    wmono asegs m mm -> stk asegs mm lo (bv_unsigned sp + -48) ->
    rw_cells asegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    icp_globals asegs mm SB ->
    (read_ret a = r) ->
    match a with
    | RdErr e => rw_cells asegs mm B [CB (Z.to_nat count) junk] /\ rw_cells asegs mm (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ 1 <= e <= 4095
    | RdData bs => rw_cells asegs mm B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)]
                   /\ rw_cells asegs mm (errno_addr tp) [C4 errv] /\ (length bs <= Z.to_nat count)%nat end ->
    evtA asegs P (POST a)
      (MS (mkR x1 SP' gp tp x5 x6 x7 sp (Z_to_bv 64 B) r x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x44ecc) fc None mm (seg_rom asegs))).
  { intros until x31. intros MI' MU' WM' SK' FR' GG RR RA'.
    stepA. do 6 stepA. stepA. stepA. (* [comment removed for export] *)
    release_frame FR' SK' (bv_unsigned sp).
    unhideD.
    pose proof G20 as G2'. eapply (icp_globals2_transport asegs) in G2'; [ | exact MU' | exact WM' | cbn; lia | cbn; lia ].
    pose proof SHB0 as SHF. unhideH SHF. pose proof BNDS as BN'.
    assert (GX : SB + Z.shiftr B 3 < shw_lo SB B + 8) by (unfold shw_lo; pose proof (al8_gt (SB + Z.shiftr B 3)); lia).
    eapply (bytes_at_transport asegs) in SHF; [ | exact MU' | cbn; lia ].
    apply evtA_done. unfold read_icp_post. rewrite <- RR.
    do 15 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
    split; [exact SHF | exact SHL]. }
  assert (GG : icp_globals asegs m3 SB).
  { unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
      A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL.
    repeat (split; [assumption|]). lia. }
  clear GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI GRR.
  stepA. (* [comment removed for export] *) if_false.
  destruct a as [e|bs].
  - (* [comment removed for export] *)
    cbn [read_ret]. zstepA. (* [comment removed for export] *) if_true.
    eapply TAIL0; try eassumption. reflexivity.
  - destruct RA as (DST & ERR & HLEN). cbn [read_ret].
    destruct bs as [|b0 bs'] eqn:EBS.
    + (* [comment removed for export] *)
      cbn [length Z.of_nat] in *. zstepA. (* [comment removed for export] *) if_true.
      eapply TAIL0; try eassumption; try reflexivity. split; [exact DST| split; [exact ERR| exact HLEN]].
    + assert (HRES : 1 <= Z.of_nat (length (b0 :: bs')) <= count) by (cbn [length] in *; lia).
      rewrite <- EBS in *. clear EBS b0 bs'.
      zstepA. (* [comment removed for export] *) if_cases KZ; zify_cond KZ. { exfalso. revert KZ. rewrite ?signed_small64 by lia. lia. }
      (* [comment removed for export] *)
      set (res := Z.of_nat (length bs)) in *.
      pose proof SHB0 as SHm. unhideH SHm.
      destruct (shadow_window_shrink asegs m SB B count res ws ltac:(lia) ltac:(lia) ltac:(lia) (conj SHm SHL) RC) as [[W1 W2] W3].
      set (ws' := firstn (Z.to_nat (shw_hi SB B res - shw_lo SB B)) ws) in *.
      assert (HLE : shw_hi SB B res <= shw_hi SB B count).
      { unfold shw_hi. apply Z.add_le_mono_r. apply al8_mono. rewrite !Z.shiftr_div_pow2 by lia.
        apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
      assert (GX : SB + Z.shiftr B 3 < shw_lo SB B + 8) by (unfold shw_lo; pose proof (al8_gt (SB + Z.shiftr B 3)); lia).
      unhideD. eapply (bytes_at_transport asegs) in W1; [ | exact MU | cbn; rewrite W2; lia ]. hideD.
      eapply (rdi_check bs ws' HRES W2 W3 HLE).
      split; [assumption|]. split; [exact MU|]. split; [assumption|]. split; [exact SK|].
      split; [assumption|]. split; [exact DST|]. split; [exact ERR|]. split; [exact GG| exact W1].
Qed.
End Walk.

(* [comment removed for export] *)
Lemma read_icp_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (fd B count SB : Z) (junk ws : list byte) (errv : word) (lo : Z) (P : acc -> Prop),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 2208 -> mem_inv asegs m ->
  a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 count ->
  3 <= fd < 2^32 -> 0 < count <= 65536 -> range_in_mem SB B count -> B + count < 2^47 ->
  0x13fdd0 <= errno_addr tp /\ errno_addr tp + 4 <= 0x603000 ->
  (B + count <= lo \/ bv_unsigned sp <= B) -> (B + count <= errno_addr tp \/ errno_addr tp + 4 <= B) ->
  (B + count <= 0xa4000 \/ 0x13fdd0 <= B) ->
  rw_cells asegs m B [CB (Z.to_nat count) junk] -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
  icp_globals asegs m SB -> icp_globals2 asegs m ->
  shadow_window asegs m SB B count ws -> range_clean SB B count ws -> (shw_hi SB B count <= B \/ B + count <= shw_lo SB B) ->
  (forall a k, shw_lo SB B <= a -> a + Z.of_nat k <= shw_hi SB B count -> P (Z_to_bv 64 a, k)) ->
  (forall a k, errno_addr tp <= a -> a + Z.of_nat k <= errno_addr tp + 4 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, B <= a -> a + Z.of_nat k <= B + count -> P (Z_to_bv 64 a, k)) ->
  (forall a k, bv_unsigned sp - 2208 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  implA asegs (at_nodeA asegs) P (enode (NRead fd B count) (dec_read B count))
    (epost (read_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B count SB junk ws errv lo m))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 read_icp_entry) fc None m (seg_rom asegs)).
Proof.
  intros until P. intros SK LOC LO MI HA0 HA1 HA2 HFD HCNT RIM HBN HTP HDISJ HBE HGL DST ERR G G2 SHW RC HSWD PSH PERR PIMG PBUF PSTK.
  unfold alloc_ceiling, sp_window_lo, stack_max_size in LOC.
  assert (SBR : 2^24 <= SB < 2^32) by (unfold icp_globals in G; tauto).
  destruct SHW as [SHB SHL].
  eapply read_icp_body; eassumption.
Qed.
End RC__2.
