(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 1288 of its 1531 lines of code are new or changed and 2314 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F1.v, with its module names changed; 152 of its 311 lines of code are new or changed and 1372 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F1.v f1_body (:149), f1_tail2 (:207), f1_tail1 (:240), f1_evt (:294)
     at a working branch 3803efccea0 (blob 6a2f153491ebcd6e34e470638bff36784c98bd32);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f1_body_of_F, f1_tail2_of_F, f1_tail1_of_F, f1_evt_of_F (evtF_evt + rng_all) re-derive the source
     statements. *)
(* rule 24: no function proved. *)
(* The run 0x81ec4 -> 0x534b8 ends AT the allocator entry (jal 0x534b8), so no `_F` here steps through a callee
   and the runs are not split.  Regions: the input bytes at q (and at q + 1 when left >= 2), their shadow bytes
   at (q >> 3) + ASAN_K and ((q + 1) >> 3) + ASAN_K (the two instrumented checks, whose slow arms read no further
   memory), and the two spill stores [A + 232, A + 248). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YI08.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcIdentModel RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import F1.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

(* The instrumented check of the byte at q, with the StepF step (F1.v:115-124 verbatim otherwise). *)
Ltac f1_shadowF q k Hsh :=
  step; rewrite (unsigned_lit q) by lia; step; step; step;
  let E0 := fresh "E0" in let N0 := fresh "N0" in
  destruct (Z.eq_dec (bv_signed k) 0) as [E0|N0];
  [ rewrite (f1_sxb_z k E0); cbv iota
  | rewrite (f1_sxb_nz k N0); cbv iota; step; step;
    rewrite (unsigned_lit q) by lia; rewrite (land7 q ltac:(lia));
    rewrite (lts_sxb (q mod 8) k ltac:(pose proof (Z.mod_pos_bound q 8 ltac:(lia)); lia));
    rewrite (proj2 (Z.ltb_lt (q mod 8) (bv_signed k))) by (unfold shadow_ok in Hsh; lia);
    cbn [negb]; cbv iota; step ].

(* ---- 0x81f28 .. the allocator entry (F1.f1_body) ---- *)
Lemma f1_body_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 a2 a4 a5 a6 a7 s2 s3 s4 s6 s8 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q left j h len lo hi L : Z),
    0 <= q -> q + left <= 2 ^ 47 -> 1 <= left -> 0 <= j <= 255 ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    0 <= lo < 2 ^ 64 -> 0 <= hi < 2 ^ 64 -> Z.lor hi lo = L -> 0 <= L < 2 ^ 17 ->
    1 <= h <= 2 -> h <= left -> len = Z.min L (left - h) ->
    wr_at rsegs m (A + 232) 16 ->
    rng RNG (A + 232) 16 ->
    evtF rsegs RNG
      (f1_post sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 s6 s8 s11 t3 t4 t5 t6 Fr fc m A q left j h len)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 lo) (Z_to_bv 64 hi) a2
               (Z_to_bv 64 j) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (q + h)) s6 (Z_to_bv 64 q) s8
               (Z_to_bv 64 (left - h)) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f28) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 a2 a4 a5 a6 a7 s2 s3 s4 s6 s8 s11 t3 t4 t5 t6 Fr fc m
    A q left j h len lo hi L Hq Hql Hl Hj HA0 HA1 Hlo Hhi EL HL Hh Hhl Elen HW Rsp.
  pose proof (munch_refl [(A + 232, A + 248)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* 0x81f28 or s4,a1,a0 ; 0x81f2c bltu s4,s9 *)
  step. rewrite (unsigned_lit hi) by lia. rewrite (unsigned_lit lo) by lia. rewrite EL.
  step. rewrite (bv_ltu_lit L (left - h)) by lia.
  destruct (Z.ltb_spec L (left - h)) as [Hlt|Hge]; cbv iota;
    [ assert (EE : len = L) by lia; rewrite EE; step; step
    | assert (EE : len = left - h) by lia; rewrite EE; step; step; step ].
  all: rewrite (f1_not_ge (q + h)) by lia; cbn [negb]; cbv iota.
  (* 0x81f40 sd s9,232(s1) *)
  all: pose proof (wr_at_store_ok rsegs m (A + 232) 16 0 8 HW ltac:(lia) ltac:(lia)) as HS1.
  all: replace (A + 232 + 0) with (A + 232) in HS1 by lia.
  all: step.
  (* 0x81f44 sd a3,240(s1) *)
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           pose proof (wr_at_store_ok rsegs mm (A + 232) 16 8 8
                         (wr_at_write rsegs m (A + 232) 16 _ _ HW) ltac:(lia) ltac:(lia)) as HS2
       end.
  all: replace (A + 232 + 8) with (A + 240) in HS2 by lia.
  all: step.
  (* 0x81f48 mv a0,s4 ; 0x81f4c jal 0x534b8 *)
  all: step; step.
  all: apply evtF_done; unfold f1_post; do 3 eexists; split; [reflexivity|].
  all: split;
       [ apply munch_write;
         [ apply munch_write; [exact MU | lia | rewrite length_le8; lia
                              | cbn [inside]; rewrite length_le8; lia]
         | lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia] |].
  all: split; [apply wmono_write; apply wmono_write; exact WM|].
  all: split;
       [ apply bytes_at_write_other;
         [ apply bytes_at_write_same; [lia | rewrite length_le8; lia]
         | lia | rewrite length_le8; lia | rewrite !length_le8; lia] |].
  all: apply bytes_at_write_same; [lia | rewrite length_le8; lia].
Qed.

(* ---- 0x81f18 .. the allocator entry (F1.f1_tail2) ---- *)
Lemma f1_tail2_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s6 s8 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q left j len : Z) (b0 b1 : byte),
    4096 <= q -> q + left <= 2 ^ 47 -> 2 <= left -> 0 <= j <= 255 ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1] ->
    wr_at rsegs m (A + 232) 16 ->
    len = Z.min (bv_unsigned b0 + 256 * bv_unsigned b1) (left - 2) ->
    rng RNG (q + 1) 1 ->
    rng RNG (A + 232) 16 ->
    evtF rsegs RNG
      (f1_post sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 s6 s8 s11 t3 t4 t5 t6 Fr fc m A q left j 2 len)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (zxb b0) a1 a2
               (Z_to_bv 64 j) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (q + 1)) s6 (Z_to_bv 64 q) s8
               (Z_to_bv 64 left) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f18) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s6 s8 s11 t3 t4 t5 t6 Fr fc m
    A q left j len b0 b1 Hq Hql Hl Hj HA0 HA1 HR1 HW Elen Rq1 Rsp.
  pose proof (f1_byte_rng b0) as Hb0. pose proof (f1_byte_rng b1) as Hb1.
  (* 0x81f18 lbu a1,0(s5) ; 0x81f1c addi s9,s9,-2 ; 0x81f20 addi s5,s7,2 ; 0x81f24 slli a1,a1,8 *)
  step. step. step. step.
  rewrite RcIdentLib.zxb_u.
  replace (left + -2) with (left - 2) by lia.
  unfold zxb at 1.
  apply (f1_body_F RNG _ sp gp tp t0 t1 t2 s0 a2 a4 a5 a6 a7 s2 s3 s4 s6 s8 s11 t3 t4 t5 t6 Fr fc m
           A q left j 2 len (bv_unsigned b0) (Z.shiftl (bv_unsigned b1) 8)
           (bv_unsigned b0 + 256 * bv_unsigned b1));
    try lia.
  - rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia.
  - apply f1_lor_shl8; lia.
  - exact HW.
  - exact Rsp.
Qed.

(* ---- 0x81ee8 .. the allocator entry (F1.f1_tail1) ---- *)
Lemma f1_tail1_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s8 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q left j h len : Z) (b0 b1 k1 : byte),
    4096 <= q -> q + left <= 2 ^ 47 -> 1 <= left -> 0 <= j <= 255 ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b0] ->
    (2 <= left -> ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1]) ->
    (2 <= left -> ov_read_bytes rsegs m (wa (Z.shiftr (q + 1) 3 + ASAN_K)) 1 = Some [k1]) ->
    (2 <= left -> shadow_ok (q + 1) (bv_signed k1)) ->
    wr_at rsegs m (A + 232) 16 ->
    h = Z.min 2 left ->
    len = Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0)) (left - h) ->
    rng RNG q 1 ->
    (2 <= left -> rng RNG (q + 1) 1) ->
    (2 <= left -> rng RNG (Z.shiftr (q + 1) 3 + ASAN_K) 1) ->
    rng RNG (A + 232) 16 ->
    evtF rsegs RNG
      (f1_post sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 1) s8 s11 t3 t4 t5 t6 Fr fc m
                 A q left j h len)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2
               (Z_to_bv 64 j) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (q + 1)) (Z_to_bv 64 1) (Z_to_bv 64 q) s8
               (Z_to_bv 64 left) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ee8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s8 s11 t3 t4 t5 t6 Fr fc m
    A q left j h len b0 b1 k1 Hq Hql Hl Hj HA0 HA1 HR0 HR1 HK1 HS1 HW Eh Elen Rq Rq1 Rsh1 Rsp.
  pose proof (f1_byte_rng b0) as Hb0. pose proof (f1_byte_rng b1) as Hb1.
  (* 0x81ee8 lbu a0,0(s7) ; 0x81eec bne s9,s6 *)
  step. step.
  destruct (Z.eq_dec left 1) as [E1|N1].
  - (* left = 1: h = 1, the header is the single byte in[c] *)
    subst left. rewrite (f1_beq 1 1 ltac:(lia) ltac:(lia) eq_refl). cbv iota.
    assert (Eh1 : h = 1) by lia. subst h.
    (* 0x81ef0 li s9,0 ; 0x81ef4 li a1,0 ; 0x81ef8 j 0x81f28 *)
    step. step. step.
    unfold zxb at 1.
    apply (f1_body_F RNG _ sp gp tp t0 t1 t2 s0 a2 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 1) s8 s11 t3 t4 t5 t6 Fr fc m
             A q 1 j 1 len (bv_unsigned b0) 0 (bv_unsigned b0)); try lia.
    all: try (apply Z.lor_0_l); try exact HW; try exact Rsp.
    change (2 <=? 1) with false in Elen. rewrite Elen. lia.
  - (* left >= 2: the second header byte *)
    rewrite (f1_bne left 1 ltac:(lia) ltac:(lia) N1). cbv iota.
    assert (Hl2 : 2 <= left) by lia.
    assert (Eh2 : h = 2) by lia. subst h.
    rewrite (proj2 (Z.leb_le 2 left) Hl2) in Elen.
    pose proof (Rq1 Hl2) as Rq1'. pose proof (Rsh1 Hl2) as Rsh1'.
    (* 0x81efc addi a1,s5,1 ; 0x81f00 bltu s6,a1 (taken) *)
    step. step.
    rewrite (bv_ltu_lit 1 (q + 2)) by lia.
    rewrite (proj2 (Z.ltb_lt 1 (q + 2)) ltac:(lia)). cbv iota.
    pose proof (HS1 Hl2) as HSk. pose proof (HK1 Hl2) as HKk. pose proof (HR1 Hl2) as HRk.
    (* 0x81f08-0x81f14: the second instrumented check, on the byte at q + 1 (slow arm 0x82d44) *)
    f1_shadowF (q + 1) k1 HSk.
    all: replace (Z.min 2 left) with 2 by lia.
    all: apply (f1_tail2_F RNG _ sp gp tp t0 t1 t2 s0 _ _ a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 1) s8 s11 t3 t4 t5 t6
                  Fr fc m A q left j len b0 b1); try lia; try assumption.
Qed.

(* ---- the whole run from the frame-loop head (F1.f1_evt) ---- *)
Lemma f1_evt_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s8 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q left j h len : Z) (b0 b1 k0 k1 : byte),
    4096 <= q -> q + left <= 2 ^ 47 -> 1 <= left -> 0 <= j <= 255 ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k0] ->
    shadow_ok q (bv_signed k0) ->
    (2 <= left -> ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1]) ->
    (2 <= left -> ov_read_bytes rsegs m (wa (Z.shiftr (q + 1) 3 + ASAN_K)) 1 = Some [k1]) ->
    (2 <= left -> shadow_ok (q + 1) (bv_signed k1)) ->
    wr_at rsegs m (A + 232) 16 ->
    h = Z.min 2 left ->
    len = Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0)) (left - h) ->
    rng RNG q 1 ->
    rng RNG (Z.shiftr q 3 + ASAN_K) 1 ->
    (2 <= left -> rng RNG (q + 1) 1) ->
    (2 <= left -> rng RNG (Z.shiftr (q + 1) 3 + ASAN_K) 1) ->
    rng RNG (A + 232) 16 ->
    evtF rsegs RNG
      (f1_post sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 1) s8 s11 t3 t4 t5 t6 Fr fc m
                 A q left j h len)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 (Z_to_bv 64 j) a4 a5 a6 a7 s2 s3 s4
               s5 (Z_to_bv 64 1) (Z_to_bv 64 q) s8 (Z_to_bv 64 left) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ec4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s8 s11 t3 t4 t5 t6 Fr fc m
    A q left j h len b0 b1 k0 k1 Hq Hql Hl Hj HA0 HA1 HR0 HK0 HS0 HR1 HK1 HS1 HW Eh Elen
    Rq Rsh0 Rq1 Rsh1 Rsp.
  (* 0x81ec4 bnez s9 (taken) ; 0x81ecc addi s5,s7,1 ; 0x81ed0 bltu s6,s5 (taken) *)
  step. if_true_by (f1_bne left 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  step. step.
  rewrite (bv_ltu_lit 1 (q + 1)) by lia.
  rewrite (proj2 (Z.ltb_lt 1 (q + 1)) ltac:(lia)). cbv iota.
  (* 0x81ed8-0x81ee4: the instrumented check of the byte at q (slow arm 0x82d2c) *)
  f1_shadowF q k0 HS0.
  all: apply (f1_tail1_F RNG _ sp gp tp t0 t1 t2 s0 _ _ a2 a4 a5 a6 a7 s2 s3 s4 s8 s11 t3 t4 t5 t6 Fr fc m
                A q left j h len b0 b1 k1); try lia; try assumption.
Qed.

(* ---- the compare lemmas: the source statements, re-derived from the _F forms ---- *)

Lemma f1_shad_rng_all : forall x, 0 <= x -> x <= 2 ^ 47 -> rng RNG_all (Z.shiftr x 3 + ASAN_K) 1.
Proof.
  intros x H0 H1. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (HP : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (HD : x / 8 <= x) by (apply Z.div_le_upper_bound; lia).
  apply rng_all; unfold ASAN_K; lia.
Qed.

Lemma f1_body_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 a2 a4 a5 a6 a7 s2 s3 s4 s6 s8 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q left j h len lo hi L : Z),
    0 <= q -> q + left <= 2 ^ 47 -> 1 <= left -> 0 <= j <= 255 ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    0 <= lo < 2 ^ 64 -> 0 <= hi < 2 ^ 64 -> Z.lor hi lo = L -> 0 <= L < 2 ^ 17 ->
    1 <= h <= 2 -> h <= left -> len = Z.min L (left - h) ->
    wr_at rsegs m (A + 232) 16 ->
    evt rsegs (f1_post sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 s6 s8 s11 t3 t4 t5 t6 Fr fc m A q left j h len)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 lo) (Z_to_bv 64 hi) a2
               (Z_to_bv 64 j) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (q + h)) s6 (Z_to_bv 64 q) s8
               (Z_to_bv 64 (left - h)) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f28) fc None m (seg_rom rsegs)).
Proof.
  intros. apply (evtF_evt rsegs RNG_all).
  apply f1_body_F with (lo := lo) (hi := hi) (L := L); try assumption.
  apply rng_all; lia.
Qed.
Definition f1_body_src_check : ltac:(let T := type of F1.f1_body in exact T) := f1_body_of_F.

Lemma f1_tail2_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s6 s8 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q left j len : Z) (b0 b1 : byte),
    4096 <= q -> q + left <= 2 ^ 47 -> 2 <= left -> 0 <= j <= 255 ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1] ->
    wr_at rsegs m (A + 232) 16 ->
    len = Z.min (bv_unsigned b0 + 256 * bv_unsigned b1) (left - 2) ->
    evt rsegs (f1_post sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 s6 s8 s11 t3 t4 t5 t6 Fr fc m A q left j 2 len)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (zxb b0) a1 a2
               (Z_to_bv 64 j) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (q + 1)) s6 (Z_to_bv 64 q) s8
               (Z_to_bv 64 left) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f18) fc None m (seg_rom rsegs)).
Proof.
  intros. apply (evtF_evt rsegs RNG_all).
  apply f1_tail2_F with (b0 := b0) (b1 := b1); try assumption.
  - apply rng_all; lia.
  - apply rng_all; lia.
Qed.
Definition f1_tail2_src_check : ltac:(let T := type of F1.f1_tail2 in exact T) := f1_tail2_of_F.

Lemma f1_tail1_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s8 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q left j h len : Z) (b0 b1 k1 : byte),
    4096 <= q -> q + left <= 2 ^ 47 -> 1 <= left -> 0 <= j <= 255 ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b0] ->
    (2 <= left -> ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1]) ->
    (2 <= left -> ov_read_bytes rsegs m (wa (Z.shiftr (q + 1) 3 + ASAN_K)) 1 = Some [k1]) ->
    (2 <= left -> shadow_ok (q + 1) (bv_signed k1)) ->
    wr_at rsegs m (A + 232) 16 ->
    h = Z.min 2 left ->
    len = Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0)) (left - h) ->
    evt rsegs (f1_post sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 1) s8 s11 t3 t4 t5 t6 Fr fc m
                 A q left j h len)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2
               (Z_to_bv 64 j) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (q + 1)) (Z_to_bv 64 1) (Z_to_bv 64 q) s8
               (Z_to_bv 64 left) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ee8) fc None m (seg_rom rsegs)).
Proof.
  intros. apply (evtF_evt rsegs RNG_all).
  apply f1_tail1_F with (b0 := b0) (b1 := b1) (k1 := k1); try assumption.
  - apply rng_all; lia.
  - intros _. apply rng_all; lia.
  - intros _. apply f1_shad_rng_all; lia.
  - apply rng_all; lia.
Qed.
Definition f1_tail1_src_check : ltac:(let T := type of F1.f1_tail1 in exact T) := f1_tail1_of_F.

Lemma f1_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s8 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A q left j h len : Z) (b0 b1 k0 k1 : byte),
    4096 <= q -> q + left <= 2 ^ 47 -> 1 <= left -> 0 <= j <= 255 ->
    0 <= A -> A + 248 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [k0] ->
    shadow_ok q (bv_signed k0) ->
    (2 <= left -> ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1]) ->
    (2 <= left -> ov_read_bytes rsegs m (wa (Z.shiftr (q + 1) 3 + ASAN_K)) 1 = Some [k1]) ->
    (2 <= left -> shadow_ok (q + 1) (bv_signed k1)) ->
    wr_at rsegs m (A + 232) 16 ->
    h = Z.min 2 left ->
    len = Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0)) (left - h) ->
    evt rsegs (f1_post sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 1) s8 s11 t3 t4 t5 t6 Fr fc m
                 A q left j h len)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 (Z_to_bv 64 j) a4 a5 a6 a7 s2 s3 s4
               s5 (Z_to_bv 64 1) (Z_to_bv 64 q) s8 (Z_to_bv 64 left) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ec4) fc None m (seg_rom rsegs)).
Proof.
  intros. apply (evtF_evt rsegs RNG_all).
  apply f1_evt_F with (b0 := b0) (b1 := b1) (k0 := k0) (k1 := k1); try assumption.
  - apply rng_all; lia.
  - apply f1_shad_rng_all; lia.
  - intros _. apply rng_all; lia.
  - intros _. apply f1_shad_rng_all; lia.
  - apply rng_all; lia.
Qed.
Definition f1_evt_src_check : ltac:(let T := type of F1.f1_evt in exact T) := f1_evt_of_F.
