(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its numbers changed; 891 of its 928 lines of code are new or changed and 359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/X12.v, with its addresses changed; 235 of its 412 lines of code are new or changed and 751 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/X12.v a0b6ac9aa84d (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives X12.v's <r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its
   type is the type of X12.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (ExecF.evtF) forms of the four instruction runs of Seg/X12.v (segments X1 / X2 of fuzz_ctrl
   LLVMFuzzerTestOneInput, asan image A, libreac v1.9.0). Each x12_<run>_F is X12.v's x12_<run> with a footprint
   binder RNG FIRST, the same binders and premises in the same order, plain ExecF.rng premises appended, and the
   run an ExecF.evtF under RNG. The regions, per run:
   - x12_store_evt_F (0x82b24-0x82b80): writes the 20 shadow bytes inside [Sh + 328, Sh + 365), reads the two
     spill words [A + 24] and [A + 16];
   - x12_b_evt_F (0x82b04-0x82b24, taken branch): reads the spill word [A + 144] and the record byte fr + 2708;
   - x12_x2_evt_F (0x82b20-0x82b24): no memory access;
   - x12_a_evt_F (0x82b04-0x82b20, the memchr wrapper call): reads [A + 144] and fr + 2708, and the call needs
     the wrapper's footprint at this site (memchr_wrap_F below): the image, the wrapper's stack window
     [sp - MEMCHR_WRAP_K, sp), the 17 buffer bytes [fr + 2691, fr + 2708) and the aligned 8-byte shadow words of
     that buffer.
   No access of these runs is instrumented (0x82b04 `ld a1,144(s1)` is a frame spill reload, 0x82b08 `lbu a0,20(a1)`
   has no shadow check before it, and the 20 `sb` write the frame's shadow bytes themselves), so no shadow premise
   of an instrumented access is needed.
   memchr_wrap_F RNG is memchr_wrap_c.v's memchr_wrap_contract with the run an evtF under RNG and one rng premise
   per region the wrapper touches (the form of bcmp_wrap_c.v's bcmp_wrap_contract_F). Two differences from the bcmp
   text, both making the statement weaker: the buffer range is the whole buffer buf, not the checked length N (the
   plain memchr may read past the matching byte up to the next 8-byte boundary inside buf, memchr_ok), and the
   shadow words are those of the whole buffer. memchr_wrap_F_all proves it at RNG_all from the in-tree
   memchr_wrap_holds, which is how x12_a_evt_of_F discharges it. The call runs on the normalized memory, as in
   X12.v, through MemNormF.evtF_normalize_ro (the evtF form of MemNorm.evt_normalize). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require memchr_c memchr_wrap_c memchr_wrap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs X12.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF_all RngBytes.
(* LAST: StepF's step / store_done / finish match evtF goals and shadow the evt engine's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* After StepF: the image-A YK11 by full path, as in X12.v, to restore getr. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module EFA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF_all.
Module RB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Module SX12 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.X12.

(* ---------------------------------------------------------------- helpers *)

(* The address bounds a carried read gives (for the rng_all premises of the corollaries). *)
Lemma x12f_ba_bounds : forall m a bs, bytes_at rsegs m a bs -> 0 <= a /\ a + Z.of_nat (length bs) <= 2 ^ 64.
Proof. intros m a bs (H0 & H1 & _). lia. Qed.

(* X12.v's x12_br and x12_st, on evtF goals. *)
Ltac x12f_br b H :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (symmetry; exact H); cbv iota
  end.

Ltac x12f_st ST Sh off :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa (Sh + off)) 1 = true)
        by (apply (x12_stk_store_ok _ _ _ _ ST); lia)
  end.

(* ---------------------------------------------------------------- the memchr wrapper's footprint need *)

Definition memchr_wrap_F (RNG : ExecF.footprint) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  let P := bv_unsigned a0 in let N := MW.memchr_n P (bv_unsigned a1 mod 256) (bv_unsigned a2) buf in
  bytes_at rsegs m P buf ->
  SF.memchr_ok P (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
  mem_inv rsegs m ->
  N <= 2 ^ 40 -> addressable m P N -> end_in_app P N -> (N = 0 \/ app_mem (P + 7)) ->
  (P + Z.of_nat (length buf) <= bv_unsigned sp - MW.MEMCHR_WRAP_K \/ bv_unsigned sp <= P) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + MW.MEMCHR_WRAP_K <= bv_unsigned sp ->
  HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
  asan_cells m -> shadow_rw m ->
  bytes_at rsegs m MW.REAL_MEMCHR (le8 (wa MC.MEMCHR)) ->
  RB.rng_bytes RNG ->
  ExecF.rng RNG 0x10000 0x5ee000 ->
  ExecF.rng RNG (bv_unsigned sp - MW.MEMCHR_WRAP_K) MW.MEMCHR_WRAP_K ->
  ExecF.rng RNG P (Z.of_nat (length buf)) ->
  (length buf = 0%nat \/
   ExecF.rng RNG (8 * (shadow_addr P / 8))
     (8 * (shadow_addr (P + Z.of_nat (length buf) - 1) / 8) + 8 - 8 * (shadow_addr P / 8))) ->
  ExecF.evtF rsegs RNG (MW.memchr_wrap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MW.MEMCHR_WRAP) fc None m (seg_rom rsegs)).

(* At RNG_all it is the proved contract. *)
Lemma memchr_wrap_F_all : memchr_wrap_F ExecF.RNG_all.
Proof.
  unfold memchr_wrap_F. cbv zeta.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf lo
    BUF OK HMI HN AD EA A7 SEP HST HK HLO HSP HC HSR HRM _ _ _ _ _.
  apply EFA.evt_evtF_all.
  pose proof MWH.memchr_wrap_holds as HM. unfold MW.memchr_wrap_contract in HM. cbv zeta in HM.
  exact (HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf lo
           BUF OK HMI HN AD EA A7 SEP HST HK HLO HSP HC HSR HRM).
Qed.

(* ---------------------------------------------------------------- the footprint runs *)

(* 0x82b24 - 0x82b80: li a0,-8; twenty sb a0,off(s3) (offsets 352 353 354 360 361 362 363 364 348 349 350 351 339
   340 346 347 328 336 337 338, all inside [328, 365) of the frame's 392 shadow bytes); ld s5,24(s1) (the
   selector, vS); ld s6,16(s1) (the frame base, vF). *)
Lemma x12_store_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A Sh vS vF : Z),
    s1v = Z_to_bv 64 A -> s3v = Z_to_bv 64 Sh ->
    stk rsegs m Sh (Sh + 392) ->
    bytes_at rsegs m (A + 24) (le8 (Z_to_bv 64 vS)) ->
    bytes_at rsegs m (A + 16) (le8 (Z_to_bv 64 vF)) ->
    0 <= Sh -> Sh + 392 <= 2 ^ 64 -> Sh + 392 <= A -> A + 32 <= 2 ^ 64 ->
    (* the 20 shadow stores *)
    ExecF.rng RNG (Sh + 328) 37 ->
    (* the two spill reloads *)
    ExecF.rng RNG (A + 24) 8 -> ExecF.rng RNG (A + 16) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (-8)) a1 a2 a3 a4 a5 a6 a7
                       s2 s3v s4 (Z_to_bv 64 vS) (Z_to_bv 64 vF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x82b80) fc None m' (seg_rom rsegs)
         /\ munch [(Sh + 328, Sh + 365)] m m'
         /\ wmono rsegs m m' /\ stk rsegs m' Sh (Sh + 392))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82b24) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A Sh vS vF -> -> ST H24 H16 HSh0 HSh1 HShA HAb RSh R24 R16.
  pose proof (munch_refl [(Sh + 328, Sh + 365)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  x12f_st ST Sh 352. step. store_done.
  x12f_st ST Sh 353. step. store_done.
  x12f_st ST Sh 354. step. store_done.
  x12f_st ST Sh 360. step. store_done.
  x12f_st ST Sh 361. step. store_done.
  x12f_st ST Sh 362. step. store_done.
  x12f_st ST Sh 363. step. store_done.
  x12f_st ST Sh 364. step. store_done.
  x12f_st ST Sh 348. step. store_done.
  x12f_st ST Sh 349. step. store_done.
  x12f_st ST Sh 350. step. store_done.
  x12f_st ST Sh 351. step. store_done.
  x12f_st ST Sh 339. step. store_done.
  x12f_st ST Sh 340. step. store_done.
  x12f_st ST Sh 346. step. store_done.
  x12f_st ST Sh 347. step. store_done.
  x12f_st ST Sh 328. step. store_done.
  x12f_st ST Sh 336. step. store_done.
  x12f_st ST Sh 337. step. store_done.
  x12f_st ST Sh 338. step. store_done.
  pose proof (x12_rd_le8 _ _ _ H24) as HR24.
  step.
  clear HR24.
  pose proof (x12_rd_le8 _ _ _ H16) as HR16.
  step.
  clear HR16.
  apply ExecF.evtF_done. cbv beta. eexists _.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact ST].
Qed.

Lemma x12_store_evt_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A Sh vS vF : Z),
    s1v = Z_to_bv 64 A -> s3v = Z_to_bv 64 Sh ->
    stk rsegs m Sh (Sh + 392) ->
    bytes_at rsegs m (A + 24) (le8 (Z_to_bv 64 vS)) ->
    bytes_at rsegs m (A + 16) (le8 (Z_to_bv 64 vF)) ->
    0 <= Sh -> Sh + 392 <= 2 ^ 64 -> Sh + 392 <= A -> A + 32 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (-8)) a1 a2 a3 a4 a5 a6 a7
                       s2 s3v s4 (Z_to_bv 64 vS) (Z_to_bv 64 vF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x82b80) fc None m' (seg_rom rsegs)
         /\ munch [(Sh + 328, Sh + 365)] m m'
         /\ wmono rsegs m m' /\ stk rsegs m' Sh (Sh + 392))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82b24) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply ExecF.evtF_evt, (x12_store_evt_F ExecF.RNG_all); try eassumption; apply ExecF.rng_all; lia.
Qed.

Lemma x12_store_evt_of_F_verbatim : True.
Proof.
  let A := type of SX12.x12_store_evt in let B := type of x12_store_evt_of_F in constr_eq A B; exact I.
Qed.

(* 0x82b04 - 0x82b24, taken branch (byte 20 of the identity record is 0). *)
Lemma x12_b_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr : Z) (b20 : byte),
    s1v = Z_to_bv 64 A ->
    bytes_at rsegs m (A + 144) (le8 (Z_to_bv 64 (fr + 2688))) ->
    bytes_at rsegs m (fr + 2708) [b20] -> bv_unsigned b20 = 0 ->
    (* the spill reload 0x82b04 and the record byte 0x82b08 *)
    ExecF.rng RNG (A + 144) 8 -> ExecF.rng RNG (fr + 2708) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 0) (Z_to_bv 64 (fr + 2688))
                               a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 0x82b24) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82b04) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A fr b20 -> H144 H20 Hb0 R144 R20.
  assert (HBz : zxb b20 = Z_to_bv 64 0).
  { apply bv_eq. rewrite kb_unsigned_zxb, Hb0. symmetry. apply LMS.unsigned_lit. lia. }
  assert (HB : bv_eqb (zxb b20) (Z_to_bv 64 0) = true) by (rewrite HBz; unfold bv_eqb; apply Z.eqb_refl).
  pose proof (x12_rd_le8 _ _ _ H144) as HR144.
  step.
  pose proof (x12_rd_b1 _ _ _ H20) as HR20.
  replace (fr + 2688 + 20) with (fr + 2708) in HR20 by lia.
  step.
  step.
  x12f_br true HB.
  apply ExecF.evtF_done. cbv beta. rewrite HBz. reflexivity.
Qed.

Lemma x12_b_evt_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr : Z) (b20 : byte),
    s1v = Z_to_bv 64 A ->
    bytes_at rsegs m (A + 144) (le8 (Z_to_bv 64 (fr + 2688))) ->
    bytes_at rsegs m (fr + 2708) [b20] -> bv_unsigned b20 = 0 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 0) (Z_to_bv 64 (fr + 2688))
                               a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 0x82b24) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82b04) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A fr b20 Hs1 H144 H20 Hb0.
  pose proof (x12f_ba_bounds _ _ _ H144) as B144. rewrite length_le8 in B144.
  pose proof (x12f_ba_bounds _ _ _ H20) as B20. cbn [length] in B20.
  eapply ExecF.evtF_evt, (x12_b_evt_F ExecF.RNG_all); try eassumption; apply ExecF.rng_all; lia.
Qed.

Lemma x12_b_evt_of_F_verbatim : True.
Proof.
  let A := type of SX12.x12_b_evt in let B := type of x12_b_evt_of_F in constr_eq A B; exact I.
Qed.

(* 0x82b20 - 0x82b24: beqz a0,0x82bf4 (the failure exit) shown not taken, a0 <> 0. No memory access. *)
Lemma x12_x2_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z),
    a0w = Z_to_bv 64 q -> 0 < q < 2 ^ 64 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7
                               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 0x82b24) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82b20) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m q -> Hq.
  assert (HB : bv_eqb (Z_to_bv 64 q) (Z_to_bv 64 0) = false).
  { apply bv_eqb_neq. intro E. apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite !LMS.unsigned_lit in E by lia. lia. }
  step.
  x12f_br false HB.
  apply ExecF.evtF_done. cbv beta. reflexivity.
Qed.

Lemma x12_x2_evt_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z),
    a0w = Z_to_bv 64 q -> 0 < q < 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7
                               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 0x82b24) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82b20) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply ExecF.evtF_evt, (x12_x2_evt_F ExecF.RNG_all); eassumption.
Qed.

Lemma x12_x2_evt_of_F_verbatim : True.
Proof.
  let A := type of SX12.x12_x2_evt in let B := type of x12_x2_evt_of_F in constr_eq A B; exact I.
Qed.

(* 0x82b04 - 0x82b20: the memchr wrapper (jal 0x42974) on [fr+2691, fr+2708). *)
Lemma x12_a_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr lo spZ : Z) (buf : list byte) (b20 : byte) (j : nat),
    s1v = Z_to_bv 64 A -> bv_unsigned sp = spZ ->
    bytes_at rsegs m (A + 144) (le8 (Z_to_bv 64 (fr + 2688))) ->
    0 <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
    bytes_at rsegs m (fr + 2708) [b20] -> bv_unsigned b20 <> 0 ->
    bytes_at rsegs m (fr + 2691) buf -> length buf = 17%nat -> SF.find_byte 0 buf = Some j ->
    ro_agree rsegs m -> addressable m (fr + 2691) 17 ->
    (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    (fr + FRAME_BYTES <= spZ - 2208 \/ spZ <= fr) ->
    stk rsegs m lo spZ -> lo + 2208 <= spZ ->
    HIGHMEM_BEG <= lo -> spZ <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m MW.REAL_MEMCHR (le8 (wa MC.MEMCHR)) ->
    (* the spill reload 0x82b04 and the record byte 0x82b08 *)
    ExecF.rng RNG (A + 144) 8 -> ExecF.rng RNG (fr + 2708) 1 ->
    (* the memchr wrapper's footprint at 0x82b1c: the image, its stack window, the buffer, the buffer's shadow
       words *)
    RB.rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (spZ - 2208) 2208 ->
    ExecF.rng RNG (fr + 2691) 17 ->
    ExecF.rng RNG (8 * (shadow_addr (fr + 2691) / 8))
      (8 * (shadow_addr (fr + 2707) / 8) + 8 - 8 * (shadow_addr (fr + 2691) / 8)) ->
    memchr_wrap_F RNG ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (x1 a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR x1 sp gp tp t0' t1' t2' s0 s1v (Z_to_bv 64 (fr + 2691 + Z.of_nat j))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x82b20) fc None m' (seg_rom rsegs)
         /\ munch [(spZ - 2208, spZ)] m m'
         /\ wmono rsegs m m' /\ ro_same rsegs m m' /\ stk rsegs m' lo spZ
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82b04) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A fr lo spZ buf b20 j -> Esp H144 Hfr0 HfrA H20 Hb20 Hbuf HbufL HFB HRO Hadr Happ Hdisj
    HST Hlo1 Hlo2 Hspa HAC HSW HRM R144 R20 RBY RIMG RSTK RBUF RSHW HMF.
  subst spZ. pose proof FRAME_BYTES_val as HFBv.
  unfold APPMEM_END in HfrA.
  assert (HPb : 0 <= fr + 2691 < 2 ^ 64) by lia.
  pose proof (SF.find_byte_Some 0 buf j HFB) as (Hjl & _ & _).
  assert (HFF : SF.find_byte 0 (firstn (Z.to_nat 17) buf) = Some j).
  { rewrite firstn_all2 by (rewrite HbufL; cbn [Z.to_nat]; lia). exact HFB. }
  assert (HRES : SF.memchr_res (fr + 2691) 0 17 buf = fr + 2691 + Z.of_nat j)
    by (unfold SF.memchr_res; rewrite HFF; reflexivity).
  assert (HN : MW.memchr_n (fr + 2691) 0 17 buf = Z.of_nat j + 1).
  { unfold MW.memchr_n. rewrite HRES.
    replace (fr + 2691 + Z.of_nat j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
  assert (HOK : SF.memchr_ok (fr + 2691) 0 17 buf).
  { unfold SF.memchr_ok. rewrite HFF. left. rewrite HbufL. cbn [Z.of_nat]. lia. }
  assert (HB : bv_eqb (zxb b20) (Z_to_bv 64 0) = false).
  { apply bv_eqb_neq. intro E. apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite kb_unsigned_zxb in E. rewrite LMS.unsigned_lit in E by lia. exact (Hb20 E). }
  pose proof (x12_rd_le8 _ _ _ H144) as HR144.
  step.
  pose proof (x12_rd_b1 _ _ _ H20) as HR20.
  replace (fr + 2688 + 20) with (fr + 2708) in HR20 by lia.
  step.
  step.
  x12f_br false HB.
  step. step. step. step.
  pose proof HMF as HM. unfold memchr_wrap_F, MW.MEMCHR_WRAP_K in HM. cbv zeta in HM.
  assert (EP : bv_unsigned (Z_to_bv 64 (fr + 2691)) = fr + 2691) by (apply LMS.unsigned_lit; lia).
  assert (E0 : bv_unsigned (Z_to_bv 64 0) = 0) by (vm_compute; reflexivity).
  assert (E17 : bv_unsigned (Z_to_bv 64 17) = 17) by (vm_compute; reflexivity).
  eapply ExecF.evtF_cut.
  { (* the wrapper's footprint contract needs mem_inv, which FRA does not give (it gives ro_agree): run the call
       on the normalized memory, where mem_inv_normalize supplies it, and carry the post back over mem_rel /
       ro_same (MemNormF.evtF_normalize_ro keeps the footprint RNG). *)
    eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m (seg_rom rsegs) HRO).
    pose proof (mem_rel_normalize rsegs m HRO) as REL.
    eapply HM with (buf := buf) (lo := lo).
    all: rewrite ?EP, ?E0, ?E17, ?Zmod_0_l, ?HN.
    - exact (bytes_at_normalize rsegs m (fr + 2691) buf HRO Hbuf).
    - exact HOK.
    - apply mem_inv_normalize.
    - lia.
    - apply (x12_addr_rel m (normalize rsegs m) (fr + 2691) (Z.of_nat j + 1) REL).
      pose proof (addressable_sub m (fr + 2691) 17 0 (Z.of_nat j + 1) Hadr ltac:(lia) ltac:(lia) ltac:(lia)) as HA2.
      rewrite Z.add_0_r in HA2. exact HA2.
    - right. apply Happ. lia.
    - right. apply Happ. lia.
    - rewrite HbufL. cbn [Z.of_nat]. destruct Hdisj as [Hd|Hd]; lia.
    - exact (x12_stk_rel m (normalize rsegs m) lo (bv_unsigned sp) REL Hlo2 Hspa HST).
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact (x12_ac_rel m (normalize rsegs m) REL HAC).
    - exact (x12_sw_rel m (normalize rsegs m) REL HSW).
    - exact (bytes_at_normalize rsegs m MW.REAL_MEMCHR (le8 (wa MC.MEMCHR)) HRO HRM).
    - exact RBY.
    - exact RIMG.
    - exact RSTK.
    - rewrite HbufL. exact RBUF.
    - right. rewrite HbufL. change (Z.of_nat 17) with 17.
      replace (fr + 2691 + 17 - 1) with (fr + 2707) by lia. exact RSHW. }
  intros ms' (s0' & HP & HMS & HRS).
  destruct HP as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6''
              & m0' & E & MU0 & WM0 & MI0 & ST0 & AC0 & SW0 & HB0).
  subst s0'.
  destruct HMS as (HRg & HFg & HPc & HSvc & HRes & HFc & HRom & HMR).
  destruct ms' as [regs2 fregs2 pc2 svc2 resv2 fcsr2 mem2 rom2].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HRg, HFg, HPc, HSvc, HRes, HFc, HRom, HMR, HRS.
  subst regs2 fregs2 pc2 svc2 resv2 fcsr2 rom2.
  rewrite EP, E0, E17, Zmod_0_l, HRES.
  replace (ret_pc (Z_to_bv 64 0x82b20)) with (Z_to_bv 64 0x82b20)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply ExecF.evtF_done. cbv beta.
  exists (Z_to_bv 64 0x82b20), a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'',
         mem2.
  split; [reflexivity|].
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) mem2 m0' REL HMR HRS MU0)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) mem2 m0' REL HMR HRS WM0)|].
  split; [exact HRS|].
  split; [exact (x12_stk_rel_back mem2 m0' lo (bv_unsigned sp) HMR Hlo2 Hspa ST0)|].
  split; [exact (x12_ac_rel_back mem2 m0' HMR AC0) | exact (x12_sw_rel_back mem2 m0' HMR SW0)].
Qed.

Lemma x12_a_evt_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr lo spZ : Z) (buf : list byte) (b20 : byte) (j : nat),
    s1v = Z_to_bv 64 A -> bv_unsigned sp = spZ ->
    bytes_at rsegs m (A + 144) (le8 (Z_to_bv 64 (fr + 2688))) ->
    0 <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
    bytes_at rsegs m (fr + 2708) [b20] -> bv_unsigned b20 <> 0 ->
    bytes_at rsegs m (fr + 2691) buf -> length buf = 17%nat -> SF.find_byte 0 buf = Some j ->
    ro_agree rsegs m -> addressable m (fr + 2691) 17 ->
    (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    (fr + FRAME_BYTES <= spZ - 2208 \/ spZ <= fr) ->
    stk rsegs m lo spZ -> lo + 2208 <= spZ ->
    HIGHMEM_BEG <= lo -> spZ <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m MW.REAL_MEMCHR (le8 (wa MC.MEMCHR)) ->
    LE.evt rsegs
      (fun ms' => exists (x1 a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR x1 sp gp tp t0' t1' t2' s0 s1v (Z_to_bv 64 (fr + 2691 + Z.of_nat j))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x82b20) fc None m' (seg_rom rsegs)
         /\ munch [(spZ - 2208, spZ)] m m'
         /\ wmono rsegs m m' /\ ro_same rsegs m m' /\ stk rsegs m' lo spZ
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82b04) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A fr lo spZ buf b20 j Hs1 Esp H144 Hfr0 HfrA H20 Hb20 Hbuf HbufL HFB HRO Hadr Happ Hdisj
    HST Hlo1 Hlo2 Hspa HAC HSW HRM.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof (x12f_ba_bounds _ _ _ H144) as B144. rewrite length_le8 in B144.
  eapply ExecF.evtF_evt, (x12_a_evt_F ExecF.RNG_all); try eassumption; try exact memchr_wrap_F_all;
    try (intros ? ? ? ? ?; exact I); apply ExecF.rng_all;
    unfold HIGHMEM_BEG, APPMEM_END, shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia.
Qed.

Lemma x12_a_evt_of_F_verbatim : True.
Proof.
  let A := type of SX12.x12_a_evt in let B := type of x12_a_evt_of_F in constr_eq A B; exact I.
Qed.
