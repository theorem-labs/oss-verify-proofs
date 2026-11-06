(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 262 of its 291 lines of code are new or changed and 367 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F10.v, with its module paths and module names changed; 151 of its 339 lines of code are new or changed and 103 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F10.v blob b66c500e3881 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: F10.v states no named run lemma - seg_F10 applies Tac_slot.sl_run to its two runs inline (F10.v:202 and
   F10.v:294), so there is no F10.<r> for a constr_eq pin. Each seg_F10_runN here states that inline run with
   flen g j := L and t_g (g_in g) j := G, and seg_F10_runN re-derives the UL Exec.evt premise sl_run takes from
   seg_F10_runN_F at ExecF.RNG_all. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (ExecF.evtF) form of the two runs of seg_F10 (F10.v), from the entry cut at 0x81ff4.
   seg_F10_run1_F: the reply result a0 = 1 arm (0x81ff4-0x82068, falls through to 0x8206c). It reads the frame spills
   [s1+280] = sum_ok, [s1+272] = pp, [s1+264] = pn, the reply cells [pp] = phi+38 and [pn] = ir_s - 13, the shadow
   byte at ((phi+26) >> 3) + ASAN_K (the instrumented check 0x82038-0x82048: a load of the shadow byte and a compare;
   the byte is 0, so the slow path 0x829a8 and the error path 0x82cc4 are not reached) and the record byte phi+26.
   It writes no memory. seg_F10_run2_F: the reply result a0 = 0 arm (`bne a0,a1` at 0x81ffc taken to 0x820fc); it
   reads and writes no memory. Each Q is the Q the segment proof gives sl_run, with flen g j := L and
   t_g (g_in g) j := G. seg_F10_run1 / seg_F10_run2 re-derive the old form (the UL engine's Exec.evt, the premise of
   Tac_slot.sl_run) from the footprint form with RNG := RNG_all. The runs are re-stepped with lib.Lib StepF on the
   lib.Lib machine state; F10.v's UL read lemmas (ULMem.wa, UL bytes_at) and its register expansion (UL mkR) do not
   match the lib.Lib tactics, so their lib.Lib forms are restated here. F10.v itself is unchanged. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcParse RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 F10.
(* Last: StepF's step / if_false / finish (evtF goals) shadow the UL engine's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* After StepF: getr and FPState are YK11's, as in F10.v (the K of the runs states its register equalities over it). *)
Import YK11.
Open Scope Z_scope.

Module F10LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module F10UE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.
Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.

(* The UL engine's evt from the lib.Lib one: both are msteps of `ms_svc_pending ms = None /\ step = MachineOk ms'`. *)
Lemma f10F_ul_of_lib : forall Q ms, F10LE.evt rsegs Q ms -> F10UE.evt rsegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [clear HQ|exact HQ].
  induction H as [s|s s1 s2 Hs _ IH]; [apply F10UE.msteps_refl|].
  eapply F10UE.msteps_cons; [exact Hs | exact IH].
Qed.

(* F10.v's f10_rd1 / f10_rd8 / f10_rdk over lib.Lib wa / bytes_at, the HR form lib.Lib solve_load consumes. *)
Lemma f10F_rd1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.
Lemma f10F_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.
Lemma f10F_rdk : forall m a (bs : list byte) k, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [nth k bs cp_z].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_ov_read rsegs m a bs k 1 H ltac:(lia)). f_equal.
  clear H. revert k Hk. induction bs as [|b bs IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hk. lia.
Qed.
Lemma f10F_zxb_eq : forall (b : byte) x, x = bv_unsigned b -> zxb b = Z_to_bv 64 x.
Proof. intros b x ->. reflexivity. Qed.

(* The address bounds a carried 8-byte / 1-byte read gives (for the rng_all premises of the corollaries). *)
Lemma f10F_q64_bounds : forall m a v, q64 m a v -> 0 <= a /\ a + 8 <= 2 ^ 64.
Proof. intros m a v (H0 & H1 & _). rewrite length_le8 in H1. change (Z.of_nat 8) with 8 in H1. lia. Qed.
Lemma f10F_b1_bounds : forall m a (b : byte), bytes_at rsegs m a [b] -> 0 <= a /\ a + 1 <= 2 ^ 64.
Proof. intros m a b (H0 & H1 & _). cbn [length] in H1. change (Z.of_nat 1) with 1 in H1. lia. Qed.

(* F10.v's f10_mkR_of_expand over the lib.Lib register map (the one StepF's simp_regs reads). *)
Lemma f10F_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.mkR
  (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* F10.v's f10_subst_slot (a section-local tactic there). *)
Ltac f10F_subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

Section S.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

(* Run 1 (the reply result a0 = 1): 0x81ff4 to 0x8206c. Premises: the registers a0 = 1, s1 = A, s7 = phi, s2 = L,
   s6 = phi+18, s10 = ASAN_K; the bounds; the spills [A+280] = 1, [A+272] = fr+272, [A+264] = fr+304; the reply
   cells [fr+272] = phi+38, [fr+304] = ir_s G - 13; the record bytes G at phi; the shadow byte 0 of phi+26; and one rng
   per cell read. *)
Lemma seg_F10_run1_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (RNG : footprint)
    (A fr phi L : Z) (G : list byte),
  rg regs 10 1 -> rg regs 9 A -> rg regs 23 phi -> rg regs 18 L -> rg regs 22 (phi + 18) -> rg regs 26 ASAN_K ->
  0 < phi -> phi + L <= 2 ^ 64 -> 50 <= L -> 14 <= ir_s G <= 23 -> (26 < length G)%nat ->
  q64 mem (A + 280) 1 -> q64 mem (A + 272) (fr + 272) -> q64 mem (A + 264) (fr + 304) ->
  q64 mem (fr + 272) (phi + 38) -> q64 mem (fr + 304) (ir_s G - 13) ->
  bytes_at rsegs mem phi G -> bytes_at rsegs mem (Z.shiftr (phi + 26) 3 + ASAN_K) [Z_to_bv 8 0] ->
  rng RNG (A + 280) 8 -> rng RNG (A + 272) 8 -> rng RNG (A + 264) 8 ->
  rng RNG (fr + 272) 8 -> rng RNG (fr + 304) 8 ->
  rng RNG (Z.shiftr (phi + 26) 3 + ASAN_K) 1 -> rng RNG (phi + 26) 1 ->
  evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x8206c /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\
       getr R 21 = getr regs 21 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 9 = Z_to_bv 64 A /\ getr R 26 = Z_to_bv 64 ASAN_K /\ getr R 18 = Z_to_bv 64 L /\
       getr R 22 = Z_to_bv 64 (phi + 18) /\ getr R 23 = Z_to_bv 64 phi /\
       getr R 10 = Z_to_bv 64 (phi + 34) /\ getr R 11 = Z_to_bv 64 (ir_s G - 13 + 5) /\
       getr R 12 = Z_to_bv 64 (phi + 38) /\ getr R 13 = Z_to_bv 64 (ir_s G - 13) /\
       getr R 14 = Z_to_bv 64 0 /\ getr R 15 = Z_to_bv 64 (phi + 34))
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81ff4) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem RNG A fr phi L G Ha0 H9 Hs7 Hs2 Hs6 Hr26 Hphi0 HL HL50 Hsr HGl Hq280 Hq272 Hq264 Hpp Hpn HG Hsh
    R280 R272 R264 Rpp Rpn Rsh R26.
  pose proof HG as (Hp0 & _ & _).
  pose proof (f10F_rdk mem phi G 26 HG HGl) as RD26.
  change (Z.of_nat 26) with 26 in RD26.
  assert (Hb26 : bv_unsigned (nth 26 G cp_z) = ir_s G) by reflexivity.
  revert RD26 Hb26. generalize (nth 26 G cp_z) as b26. intros b26 RD26 Hb26.
  pose proof (f10F_rd1 mem _ _ Hsh) as RDsh.
  pose proof (f10F_rd8 mem _ _ Hq280 ltac:(apply length_le8)) as RD280.
  pose proof (f10F_rd8 mem _ _ Hq272 ltac:(apply length_le8)) as RD272.
  pose proof (f10F_rd8 mem _ _ Hq264 ltac:(apply length_le8)) as RD264.
  pose proof (f10F_rd8 mem _ _ Hpp ltac:(apply length_le8)) as RDpp.
  pose proof (f10F_rd8 mem _ _ Hpn ltac:(apply length_le8)) as RDpn.
  rewrite f10F_mkR_of_expand.
  f10F_subst_slot Ha0. f10F_subst_slot H9. f10F_subst_slot Hs7. f10F_subst_slot Hs2. f10F_subst_slot Hs6.
  f10F_subst_slot Hr26.
  (* 0x81ff4 bltz a0 (a0 = 1) not taken ; 0x81ff8 li a1,1 ; 0x81ffc bne a0,a1 not taken *)
  step. if_false. step. step. if_false.
  (* 0x82000 ld a0,280(s1) = sum_ok = 1 ; 0x82004 beqz a0 not taken *)
  step. step. if_false.
  (* 0x82008 ld a0,272(s1) = pp ; 0x8200c ld a2,0(a0) = phi+38 ; 0x82010 bltu a2,s7 not taken *)
  step. step. step. rewrite (f10_ltu_false (phi + 38) phi) by lia. cbv_concl_iota.
  (* 0x82014 sub a0,a2,s7 = 38 ; 0x82018 bltu s2,a0 not taken (len >= 50) *)
  step. rewrite (f10_sub_lit (phi + 38) phi) by lia. replace (phi + 38 - phi) with 38 by lia.
  step. rewrite (f10_ltu_false L 38) by lia. cbv_concl_iota.
  (* 0x8201c ld a1,264(s1) = pn ; 0x82020 ld a3,0(a1) = ir_s-13 ; 0x82024 addi a1,a3,2 ;
     0x82028 sub a0,s2,a0 = len-38 ; 0x8202c bltu a0,a1 not taken *)
  step. step. step. step. rewrite (MState.unsigned_lit L) by lia.
  step. rewrite (f10_ltu_false (L - 38) (ir_s G - 13 + 2)) by lia. cbv_concl_iota.
  (* 0x82030 addi a0,s6,20 = phi+38 ; 0x82034 bne a2,a0 not taken *)
  step. step. rewrite bv_eqb_refl; cbn [negb]; cbv_concl_iota.
  (* 0x82038 addi a0,s6,8 ; srli ; add ; lb a1 = shadow byte of phi+26 = 0 ; 0x82048 bnez a1 not taken *)
  step. step. step. rewrite (MState.unsigned_lit (phi + 26)) by lia.
  step. step. if_false.
  (* 0x8204c lbu a0,0(a0) = b26 = ir_s ; 0x82050 addi a1,a3,13 ; 0x82054 bne a1,a0 not taken *)
  step. step. step.
  rewrite (f10F_zxb_eq b26 (ir_s G - 13 + 13)) by lia.
  rewrite bv_eqb_refl; cbn [negb]; cbv_concl_iota.
  (* 0x82058 addi a1,a3,5 ; 0x8205c beqz a1 not taken (a1 = ir_s - 8 in [6, 15]) *)
  step. step. rewrite (f10_eqb0_false (ir_s G - 13 + 5)) by lia. cbv_concl_iota.
  (* 0x82060 li a4,0 ; 0x82064 addi a5,s6,16 ; 0x82068 addi a0,s6,16 ; land at 0x8206c *)
  step. step. step. finish. all: simp_regs; try reflexivity.
Qed.

(* The old form of run 1 (the premise sl_run takes in seg_F10), from seg_F10_run1_F with RNG := RNG_all. *)
Lemma seg_F10_run1 : forall (regs : bvmap 5 word) (mem : word -> option byte) (A fr phi L : Z) (G : list byte),
  rg regs 10 1 -> rg regs 9 A -> rg regs 23 phi -> rg regs 18 L -> rg regs 22 (phi + 18) -> rg regs 26 ASAN_K ->
  0 < phi -> phi + L <= 2 ^ 64 -> 50 <= L -> 14 <= ir_s G <= 23 -> (26 < length G)%nat ->
  q64 mem (A + 280) 1 -> q64 mem (A + 272) (fr + 272) -> q64 mem (A + 264) (fr + 304) ->
  q64 mem (fr + 272) (phi + 38) -> q64 mem (fr + 304) (ir_s G - 13) ->
  bytes_at rsegs mem phi G -> bytes_at rsegs mem (Z.shiftr (phi + 26) 3 + ASAN_K) [Z_to_bv 8 0] ->
  F10UE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x8206c /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\
       getr R 21 = getr regs 21 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 9 = Z_to_bv 64 A /\ getr R 26 = Z_to_bv 64 ASAN_K /\ getr R 18 = Z_to_bv 64 L /\
       getr R 22 = Z_to_bv 64 (phi + 18) /\ getr R 23 = Z_to_bv 64 phi /\
       getr R 10 = Z_to_bv 64 (phi + 34) /\ getr R 11 = Z_to_bv 64 (ir_s G - 13 + 5) /\
       getr R 12 = Z_to_bv 64 (phi + 38) /\ getr R 13 = Z_to_bv 64 (ir_s G - 13) /\
       getr R 14 = Z_to_bv 64 0 /\ getr R 15 = Z_to_bv 64 (phi + 34))
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81ff4) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem A fr phi L G Ha0 H9 Hs7 Hs2 Hs6 Hr26 Hphi0 HL HL50 Hsr HGl Hq280 Hq272 Hq264 Hpp Hpn HG Hsh.
  pose proof (f10F_q64_bounds _ _ _ Hq280) as B1. pose proof (f10F_q64_bounds _ _ _ Hq272) as B2.
  pose proof (f10F_q64_bounds _ _ _ Hq264) as B3. pose proof (f10F_q64_bounds _ _ _ Hpp) as B4.
  pose proof (f10F_q64_bounds _ _ _ Hpn) as B5. pose proof (f10F_b1_bounds _ _ _ Hsh) as B6.
  pose proof HG as (B7 & B8 & _).
  apply f10F_ul_of_lib, (evtF_evt rsegs RNG_all).
  apply (seg_F10_run1_F regs mem RNG_all A fr phi L G); try assumption; apply rng_all; lia.
Qed.

(* Run 2 (the reply result a0 = 0): 0x81ff4 to 0x820fc. No memory access. *)
Lemma seg_F10_run2_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (RNG : footprint),
  rg regs 10 0 ->
  evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x820fc /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
       getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26)
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81ff4) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem RNG Ha0.
  rewrite f10F_mkR_of_expand. f10F_subst_slot Ha0.
  (* 0x81ff4 bltz a0 (a0 = 0) not taken ; 0x81ff8 li a1,1 ; 0x81ffc bne a0,a1 taken *)
  step. if_false. step. step. if_true.
  finish. all: simp_regs; try reflexivity.
Qed.

(* The old form of run 2 (the premise sl_run takes in seg_F10), from seg_F10_run2_F with RNG := RNG_all. *)
Lemma seg_F10_run2 : forall (regs : bvmap 5 word) (mem : word -> option byte),
  rg regs 10 0 ->
  F10UE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x820fc /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
       getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26)
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81ff4) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem Ha0.
  apply f10F_ul_of_lib, (evtF_evt rsegs RNG_all), (seg_F10_run2_F regs mem RNG_all Ha0).
Qed.

End S.

(* ===== COMPILED SOURCE TIE (a Theorem Labs lane 04:24Z, a Theorem Labs lane's condition) =====
   F10.v states no run lemma: its cut lemma F10.seg_F10 (F10.v:147-343) applies Tac_slot.sl_run to its two runs
   inline, at F10.v:202 (the a0 = 1 arm, 0x81ff4 -> 0x8206c) and F10.v:294 (the a0 = 0 arm, 0x81ff4 -> 0x820fc),
   so neither extracted run has a constr_eq pin. seg_F10_src closes that gap: its TYPE is F10.seg_F10's own closed
   type, and its proof is F10.seg_F10's script line for line with the two inline run bullets replaced by
   seg_F10_run1 / seg_F10_run2 (the RNG_all old forms of seg_F10_run1_F / seg_F10_run2_F). It compiles only if
   those old forms are exactly the runs the cut lemma consumes.
   Source cut lemma for both runs: F10.seg_F10 (F10.v:147).
   Generalisations of the extracted runs (header above): flen g j := L, t_g (g_in g) j := G, and the cut's A / fr /
   phi as the run binders A / fr / phi; the byte nth 26 G is generalised inside seg_F10_run1_F, as the source does
   before its sl_run. No address bound was added: the cut carries every bound the runs ask for. *)
(* `@` so the cut lemma's implicit section binders ({fx} {LS} {rc} {SH} {SK}) stay in the type instead of
   becoming unresolved evars; the type is F10.seg_F10's own, term for term. *)
Lemma seg_F10_src : ltac:(let T := type of @F10.seg_F10 in exact T).
Proof.
  intros fx LS rc B APIf SH SK ra empty FF j Hx1 Hx2 Hx3 g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    Hgn & Hj & HHB & HFLSI & HLK & HbC & HbK & HbRC & Ha0 & Hpost & HID & H17 & H240 & HPF).
  subst c. rewrite SEGS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Af & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hrest).
  pose proof HbC as HbC2.
  destruct HbC2 as (Hs7 & Hs2 & (A & H9 & HA & HSP & Hq232) & HPH & HFR & HFS & HbKN & HFGj & HFSj).
  destruct HSP as (Hq248 & Hq256 & Hq144 & Hq184 & Hq208 & Hq64 & Hq72 & Hq80 & Hq272 & Hq264).
  pose proof HbK as HbK2.
  destruct HbK2 as (Hs4 & Hs6 & Hs8 & Hs9 & Hsp280 & Hu32 & Hargs).
  destruct HPH as (HGb & HPHp & HPHf).
  destruct HHB as (Hphi0 & HAd).
  pose proof HAd as (Hp0 & _ & Hpe & _). unfold AC.a_size, APPMEM_END in Hpe.
  (* the [A+280] spill base is the cut's own A *)
  assert (Hq280 : q64 mem (A + 280) (b2z (t_sum_ok (g_in g) j))).
  { destruct Hsp280 as (A' & HA' & HA'b & Hq').
    assert (EA' : A' = A).
    { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in HA', H9; rewrite <- HA'; exact H9).
      apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit in E by lia. exact E. }
    subst A'. exact Hq'. }
  destruct (ir (flen g j) (t_g (g_in g) j)) eqn:Hir.
  - (* ---- reply result a0 = 1 (reply_ok): fall through to 0x8206c ---- *)
    assert (Hok : reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = true)
      by (unfold reply_ok; rewrite Hargs, Hir; reflexivity).
    assert (Hr1 : reply_ret phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = 1)
      by (unfold reply_ret; rewrite Hargs, Hir; reflexivity).
    rewrite Hr1 in Ha0.
    pose proof (Hpost Hok) as HRP.
    pose proof HRP as (RWa & RWp & RWn).
    destruct (ir_bytes _ _ Hir) as (H50 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsr & _ & _ & Hbs & _).
    assert (Hbig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; exact H50).
    assert (Hsum : t_sum_ok (g_in g) j = true)
      by (unfold t_sum_ok; rewrite Hbig; unfold ir_blk in Hbs; rewrite Hbs; reflexivity).
    assert (Hs6' : rg regs 22 (phi + 18)) by (rewrite Hbig in Hs6; exact Hs6).
    assert (Hq280' : q64 mem (A + 280) 1) by (rewrite Hsum in Hq280; exact Hq280).
    pose proof (HGb H50) as HG.
    rewrite Z.max_l in Hpe by lia.
    pose proof (f10_sh26 mem phi (flen g j) HAd H50) as Hsh.
    apply (sl_run regs (Z_to_bv 64 0x81ff4) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x8206c /\ mem' = mem /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\
         getr R 21 = getr regs 21 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
         getr R 9 = Z_to_bv 64 A /\ getr R 26 = Z_to_bv 64 ASAN_K /\ getr R 18 = Z_to_bv 64 (flen g j) /\
         getr R 22 = Z_to_bv 64 (phi + 18) /\ getr R 23 = Z_to_bv 64 phi /\
         getr R 10 = Z_to_bv 64 (phi + 34) /\ getr R 11 = Z_to_bv 64 (ir_s (t_g (g_in g) j) - 13 + 5) /\
         getr R 12 = Z_to_bv 64 (phi + 38) /\ getr R 13 = Z_to_bv 64 (ir_s (t_g (g_in g) j) - 13) /\
         getr R 14 = Z_to_bv 64 0 /\ getr R 15 = Z_to_bv 64 (phi + 34))
      (Post B APIf ra g)).
    + exact Hhalt.
    + (* the run the cut consumes, from the RNG_all old form of seg_F10_run1_F *)
      exact (seg_F10_run1 regs mem A fr phi (flen g j) (t_g (g_in g) j) Ha0 H9 Hs7 Hs2 Hs6' Hr26
               ltac:(lia) ltac:(lia) H50 ltac:(lia)
               ltac:(unfold t_g; rewrite fr50_length; lia)
               Hq280' Hq272 Hq264 (f10_lrw8 _ _ _ RWp) (f10_lrw8 _ _ _ RWn) HG Hsh).
    + (* continuation: rebuild the exit cut Inv_A8206c_at and apply it *)
      intros R pc' mem' regs'' md'
        (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR19 & HR20 & HR21 & HR24 & HR25 & HR9 & HR26 & HR18 &
         HR22 & HR23 & HR10 & HR11 & HR12 & HR13 & HR14 & HR15) Hreg Hmat.
      subst pc' mem'. rewrite <- SEGS. apply Hx1.
      assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
      assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg, HR9; unfold rg in H9; symmetry; exact H9).
      assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg, HR18; unfold rg in Hs2; symmetry; exact Hs2).
      assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact HR20).
      assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact HR21).
      assert (E22 : getr regs'' 22 = getr regs 22)
        by (rewrite Hreg, HR22; unfold rg in Hs6'; symmetry; exact Hs6').
      assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg, HR23; unfold rg in Hs7; symmetry; exact Hs7).
      assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact HR24).
      assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact HR25).
      destruct (f10_keep g j phi fr regs regs'' mem E2 E9 E18 E20 E21 E22 E23 E24 E25 HFLSI HLK HbC HbK
                  H17 H240 HPF)
        as (HFLSI' & HLK' & HbC' & HbK' & H17' & H240' & HPF').
      exists phi, regs'', mem, md', fr.
      split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs'' mem md md' HFRA);
          [ exact E2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
          | rewrite Hreg; exact HR8 | exact E9 | rewrite Hreg; exact HR19
          | rewrite Hreg, HR26; unfold rg in Hr26; symmetry; exact Hr26
          | exact Hmat ]. }
      split; [ eapply ent_mat; [ exact HENT | exact Hmat ] |].
      split; [exact Hgn|].
      split; [exact Hj|].
      split; [split; [exact Hphi0 | exact HAd]|].
      split; [exact HFLSI'|].
      split; [exact HLK'|].
      split; [exact HbC'|].
      split; [exact HbK'|].
      split; [exact HbRC|].
      split; [exact H50|].
      split; [exact Hsum|].
      split; [exact Hok|].
      split; [exact HRP|].
      split; [ unfold rg; rewrite Hreg; exact HR10 |].
      split; [ unfold rg; rewrite Hreg, HR11; f_equal; lia |].
      split; [ unfold rg; rewrite Hreg; exact HR12 |].
      split; [ unfold rg; rewrite Hreg; exact HR13 |].
      split; [ unfold rg; rewrite Hreg; exact HR14 |].
      split; [ unfold rg; rewrite Hreg; exact HR15 |].
      split; [exact HID|].
      split; [exact H17'|]. split; [exact H240' | exact HPF'].
  - (* ---- reply result a0 = 0 (reply_args, ir false): `bne a0,a1` taken to 0x820fc ---- *)
    assert (Hr0 : reply_ret phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = 0)
      by (unfold reply_ret; rewrite Hargs, Hir; reflexivity).
    rewrite Hr0 in Ha0.
    apply (sl_run regs (Z_to_bv 64 0x81ff4) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x820fc /\ mem' = mem /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
         getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
         getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
         getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26)
      (Post B APIf ra g)).
    + exact Hhalt.
    + (* the run the cut consumes, from the RNG_all old form of seg_F10_run2_F *)
      exact (seg_F10_run2 regs mem Ha0).
    + intros R pc' mem' regs'' md'
        (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR18 & HR19 & HR20 & HR21 & HR22 & HR23 & HR24 &
         HR25 & HR26) Hreg Hmat.
      subst pc' mem'. rewrite <- SEGS. apply Hx3.
      assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
      assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact HR9).
      assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact HR18).
      assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact HR20).
      assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact HR21).
      assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact HR22).
      assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact HR23).
      assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact HR24).
      assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact HR25).
      destruct (f10_keep g j phi fr regs regs'' mem E2 E9 E18 E20 E21 E22 E23 E24 E25 HFLSI HLK HbC HbK
                  H17 H240 HPF)
        as (HFLSI' & HLK' & HbC' & HbK' & H17' & H240' & HPF').
      exists phi, regs'', mem, md', fr.
      split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs'' mem md md' HFRA);
          [ exact E2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
          | rewrite Hreg; exact HR8 | exact E9 | rewrite Hreg; exact HR19
          | rewrite Hreg; exact HR26 | exact Hmat ]. }
      split; [ eapply ent_mat; [ exact HENT | exact Hmat ] |].
      split; [exact Hgn|].
      split; [exact Hj|].
      split; [split; [exact Hphi0 | exact HAd]|].
      split; [exact HFLSI'|].
      split; [exact HLK'|].
      split; [exact HbC'|].
      split; [exact HbK'|].
      split; [exact HbRC|].
      split; [exact Hir|].
      (* IDb1: on the ir = false edge the stage-2 record ID1 g j is the carried t_ID j *)
      split; [ unfold IDb1, ID1, rp_id; rewrite Hir; exact HID |].
      split; [exact H17'|]. split; [exact H240' | exact HPF'].
Qed.
