(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and addresses changed; 2105 of its 2257 lines of code are new or changed and 859 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A5.v; 504 of its 841 lines of code are new or changed and 1920 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/A5.v b_ld_evt :156, b_hd_ld_evt :226, b_z_evt :259, b_tail_evt :304, b_mode_evt :379,
     b_cat_evt :456, b_any_ld_evt :790.  A5.v is not in a working branch 3803efccea0: it is
     a Theorem Labs lane's WIP d574f6c66de (blob 0e65829571e0303b907755eee8035d04c36236c7), taken by path onto 3803efccea0 on
     a working branch f9a9f80d79e (unchanged, same blob) and built there (-s ours type-check rc=0);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
     lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: b_ld_evt_of_F, b_hd_ld_evt_of_F, b_z_evt_of_F, b_tail_evt_of_F, b_mode_evt_of_F, b_any_ld_evt_of_F
     (evtF_evt + rng_all) re-derive the source statements, each checked by conversion against A5's lemma
     (the Definitions named <run>_src_check).  b_cat_evt calls reac_box_catalogue at 0x815f8, so it is split there:
     b_cat_evt_pre_F re-runs
     A5.v lines 486-537 (0x815ec .. the jal, stopping AT the callee entry RBC.REAC_BOX_CATALOGUE with
     ra = 0x815fc), b_cat_evt_post_F lines 553-576 (from the return pc 0x815fc; the run ends there, so it has no
     instruction); b_cat_evt_of_F re-derives the source statement from the pair and the catalogue contract.
   No _F steps through a callee.  This file states no callee contract. *)
(* rule 24: no function proved. *)
(* Route (C) (a Theorem Labs lane 09:38Z, amendment 10:34Z; writer of record a Theorem Labs lane, lane (internal path); consumer a Theorem Labs lane's
   W1 seg_A5 / w1_exit): b_cat_evt_pre_F_on and b_cat_evt_post_F_on carry the proofs; b_cat_evt_pre_F and
   b_cat_evt_post_F keep their statements, as corollaries (b_cat_evt_of_F is unchanged).
   b_cat_evt_pre_F_on: the premise `shadow_rw m` is DROPPED.  Measured from the stretch's proof: its one shadow access,
   the store `sb zero,332(s3)` into Sh + 332, takes store_ok from the rw_cells premise at Sh + 332
   (rng RNG (Sh + 332) 1); the store [c, c + 8) goes through the rw_cells premise at c; the stretch loads nothing;
   `shadow_rw m` only rebuilt the post's `shadow_rw mc`.  The post's `shadow_rw mc` becomes
   `forall P, shadow_rw_on P m -> shadow_rw_on P mc` (every region: the written byte Sh + 332 is present in mc).
   b_cat_evt_post_F_on: the stretch has no instruction, so it reads and stores no shadow byte; the premise
   `shadow_rw mc` (the pre-call fact) is DROPPED (it only rebuilt the post's `shadow_rw m'`).  The post's
   `shadow_rw m'` becomes `forall P, shadow_rw_on P mc -> shadow_rw_on P m'` (the catalogue's write set
   [(spv - 16, spv); (c, c + 8)] is application memory, so it keeps every shadow byte of mc). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require A5.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module RBC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_box_catalogue_c.

(* A5.v's b_br / b_fix / b_sb match Exec.evt goals; the same tactics on ExecF.evtF goals. *)
Ltac bF_br :=
  try (lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first
        [ replace c with true;
          [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_leu; rewrite ?MState.unsigned_lit by lia; solve_cond]
        | replace c with false;
          [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_leu; rewrite ?MState.unsigned_lit by lia; solve_cond] ]
  end).

Ltac bF_fix :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      rewrite (A5.b_le1_lit z) by lia; mem_after_store
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      rewrite (A5.b_le1 v); mem_after_store
  | _ => idtac
  end.
Ltac bF_sb := step; bF_fix.

(* A5.v's b_post, with its rewrite to the byte list optional: StepF's step already writes a literal one-byte
   store le1 (Z_to_bv 64 z) as [Z_to_bv 8 z] (StepF.norm_lit_store_bytes), where b_post's rewrite would fail. *)
Ltac bF_post v :=
  lazymatch goal with
  | |- munch _ ?m (write_to_mem ?m _ ?BS) /\ _ =>
      let EBS := fresh "EBS" in
      assert (EBS : BS = [v])
        by (first [apply le1_zxb | (apply A5.b_le1_lit; lia) | (vm_compute; reflexivity) | reflexivity]);
      try rewrite EBS;
      split; [apply munch_write; [apply munch_refl | lia | cbn [length]; lia | cbn [inside length]; left; lia]|];
      split; [apply wmono_write, wmono_refl|];
      apply bytes_at_write_same; cbn [length]; lia
  end.

(* ---- b_ld_evt (A5.v:156-222): the loop body from the R1 cut 0x81550 (left <> 0).  Accesses: the cursor's shadow
   byte [q / 8 + K] (the instrumented check 0x81560), the input byte [q] (0x81568) and the store our[t] at [d]
   (0x8157c). ---- *)
Lemma b_ld_evt_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d q v K : Z) (b kq : byte),
    a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 d -> a3 = Z_to_bv 64 (q + 1) ->
    s2 = Z_to_bv 64 v -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 -> 1 <= q -> q + 2 < 2 ^ 64 -> 1 <= v -> v + 1 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    store_ok rsegs m (wa d) 1 = true ->
    rng RNG (q / 8 + K) 1 -> rng RNG q 1 -> rng RNG d 1 ->
    evtF rsegs RNG
      (fun ms' => exists (x4 x5 : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 1) (Z_to_bv 64 (d + 1))
                       (Z_to_bv 64 (q + 1)) x4 x5 a6 a7 (Z_to_bv 64 (v - 1)) s3 s4 s5
                       (Z_to_bv 64 (q + 1)) s7 s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81550) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d q v K b kq -> -> -> -> -> -> -> Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq HRb HS Rsh Rq Rd.
  pose proof (rc_byte_signed kq) as KRq.
  lazymatch goal with |- evtF _ _ ?QQ _ => set (Q := QQ) end.
  (* 0x81550 bltu a1,a3 (T01: 1 < q + 1) *)
  step. bF_br.
  (* 0x81558 srli a4,s6,0x3; 0x8155c add a4,a4,s10; 0x81560 lb a4,0(a4); 0x81564 bnez a4,81590 *)
  step. rewrite (MState.unsigned_lit q) by lia. rewrite rc_shr3.
  step. step. step.
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed kq)) by lia.
  enough (KC : forall (x4 x5 : word),
    evtF rsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cnt) (Z_to_bv 64 1) (Z_to_bv 64 d)
                         (Z_to_bv 64 (q + 1)) x4 x5 a6 a7 (Z_to_bv 64 v) s3 s4 s5 (Z_to_bv 64 q) s7 s8 s9
                         (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x81568) fc None m (seg_rom rsegs))).
  { destruct (Z.eqb_spec (bv_signed kq) 0) as [E|E]; cbn [negb]; [apply KC|].
    (* 0x81590 andi a5,s6,7; 0x81594 blt a5,a4,81568 *)
    step. rewrite (MState.unsigned_lit q) by lia. rewrite rc_land7.
    step.
    rewrite (rc_lts_signed (q mod 8) (bv_signed kq)) by lia.
    replace (q mod 8 <? bv_signed kq) with true by (symmetry; apply Z.ltb_lt; lia).
    apply KC. }
  intros x4 x5.
  (* 0x81568 lbu a4,0(s6); 0x8156c addi s2,s2,-1; 0x81570 mv s6,a3; 0x81574 j 8157c *)
  step. step. step. step.
  (* 0x8157c sb a4,0(a2); 0x81580 addi a0,a0,-1; 0x81584 addi a2,a2,1; 0x81588 beqz a0 *)
  step. step. step. step.
  destruct (Z.eq_dec cnt 1) as [E1|N1].
  - subst cnt. bF_br.
    apply evtF_done. unfold Q. cbv beta.
    do 3 eexists. split.
    + replace (Z_to_bv 64 (1 + -1)) with (Z_to_bv 64 (1 - 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (v + -1)) with (Z_to_bv 64 (v - 1)) by (f_equal; lia).
      reflexivity.
    + A5.b_post b.
  - bF_br.
    (* 0x8158c j 81548 *)
    step.
    apply evtF_done. unfold Q. cbv beta.
    rewrite (proj2 (Z.eqb_neq cnt 1) N1).
    do 3 eexists. split.
    + replace (Z_to_bv 64 (cnt + -1)) with (Z_to_bv 64 (cnt - 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (v + -1)) with (Z_to_bv 64 (v - 1)) by (f_equal; lia).
      reflexivity.
    + A5.b_post b.
Qed.

(* ---- b_hd_ld_evt (A5.v:226-256): the same turn from the loop head 0x81548 (left <> 0); the two head
   instructions touch registers only, then b_ld_evt_F. ---- *)
Lemma b_hd_ld_evt_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d q v K : Z) (b kq : byte),
    a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 d ->
    s2 = Z_to_bv 64 v -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 -> 1 <= q -> q + 2 < 2 ^ 64 -> 1 <= v -> v + 1 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    store_ok rsegs m (wa d) 1 = true ->
    rng RNG (q / 8 + K) 1 -> rng RNG q 1 -> rng RNG d 1 ->
    evtF rsegs RNG
      (fun ms' => exists (x4 x5 : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 1) (Z_to_bv 64 (d + 1))
                       (Z_to_bv 64 (q + 1)) x4 x5 a6 a7 (Z_to_bv 64 (v - 1)) s3 s4 s5
                       (Z_to_bv 64 (q + 1)) s7 s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81548) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d q v K b kq -> -> -> -> -> -> Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq HRb HS Rsh Rq Rd.
  (* 0x81548 beqz s2 (not taken); 0x8154c addi a3,s6,1 *)
  step. bF_br.
  step.
  apply (b_ld_evt_F RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cnt) (Z_to_bv 64 1) (Z_to_bv 64 d)
           (Z_to_bv 64 (q + 1)) a4 a5 a6 a7 (Z_to_bv 64 v) s3 s4 s5 (Z_to_bv 64 q) s7 s8 s9 (Z_to_bv 64 K) s11
           t3 t4 t5 t6 F fc m cnt d q v K b kq);
    try reflexivity; try assumption; try lia.
Qed.

(* ---- b_z_evt (A5.v:259-297): the zero arm of a turn (left = 0); the one access is the store our[t] = 0 at [d]
   (0x8157c). ---- *)
Lemma b_z_evt_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d : Z),
    a0 = Z_to_bv 64 cnt -> a2 = Z_to_bv 64 d -> s2 = Z_to_bv 64 0 ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 ->
    store_ok rsegs m (wa d) 1 = true ->
    rng RNG d 1 ->
    evtF rsegs RNG
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) a1 (Z_to_bv 64 (d + 1)) a3
                       (Z_to_bv 64 0) a5 a6 a7 (Z_to_bv 64 0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [Z_to_bv 8 0])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81548) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d -> -> -> Hcnt Hd0 Hd HS Rd.
  lazymatch goal with |- evtF _ _ ?QQ _ => set (Q := QQ) end.
  (* 0x81548 beqz s2 (taken); 0x81578 li a4,0 *)
  step. bF_br.
  step.
  (* 0x8157c sb a4,0(a2); 0x81580 addi a0,a0,-1; 0x81584 addi a2,a2,1; 0x81588 beqz a0 *)
  step. step. step. step.
  destruct (Z.eq_dec cnt 1) as [E1|N1].
  - subst cnt. bF_br.
    apply evtF_done. unfold Q. cbv beta.
    eexists. split.
    + replace (Z_to_bv 64 (1 + -1)) with (Z_to_bv 64 (1 - 1)) by (f_equal; lia).
      reflexivity.
    + bF_post (Z_to_bv 8 0).
  - bF_br.
    step.
    apply evtF_done. unfold Q. cbv beta.
    rewrite (proj2 (Z.eqb_neq cnt 1) N1).
    eexists. split.
    + replace (Z_to_bv 64 (cnt + -1)) with (Z_to_bv 64 (cnt - 1)) by (f_equal; lia).
      reflexivity.
    + bF_post (Z_to_bv 8 0).
Qed.

(* ---- b_tail_evt (A5.v:304-374): the loop exit 0x815a0 .. 0x815b0 and, on left = 0, the stub 0x81af4 to P3.
   Accesses: the four spill stores [Ab + 152, Ab + 168) and [Ab + 40, Ab + 56), and on left = 0 the load of the
   code-byte pointer [Ab + 56] (0x81cac). ---- *)
Lemma b_tail_evt_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Ab q w frv a6v a7v selv v56 : Z) (xs1 xs2 : list byte),
    s1 = Z_to_bv 64 Ab -> s2 = Z_to_bv 64 w -> s6 = Z_to_bv 64 q -> s9 = Z_to_bv 64 frv ->
    a6 = Z_to_bv 64 a6v -> a7 = Z_to_bv 64 a7v -> s8 = Z_to_bv 64 selv ->
    0 <= Ab -> Ab + 168 <= 2 ^ 64 -> 0 <= q < 2 ^ 64 -> 0 <= w -> w + 2 < 2 ^ 64 ->
    0 <= frv < 2 ^ 64 -> 0 <= a6v < 2 ^ 64 -> 0 <= a7v < 2 ^ 64 -> 0 <= selv < 2 ^ 64 ->
    length xs1 = 16%nat -> length xs2 = 16%nat ->
    rw_cells rsegs m (Ab + 40) [CB 16 xs1] -> rw_cells rsegs m (Ab + 152) [CB 16 xs2] ->
    ro_cells rsegs m (Ab + 56) [C8 (Z_to_bv 64 v56)] ->
    rng RNG (Ab + 40) 16 -> rng RNG (Ab + 152) 16 -> rng RNG (Ab + 56) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (m' : word -> option byte),
         munch [(Ab + 40, Ab + 56); (Ab + 152, Ab + 168)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (Ab + 40) (le8 (Z_to_bv 64 frv)) /\
         bytes_at rsegs m' (Ab + 48) (le8 (Z_to_bv 64 selv)) /\
         bytes_at rsegs m' (Ab + 152) (le8 (Z_to_bv 64 a7v)) /\
         bytes_at rsegs m' (Ab + 160) (le8 (Z_to_bv 64 a6v)) /\
         ((w = 0 /\ exists R : bvmap 5 word,
             ms' = MS R F (Z_to_bv 64 0x81cb0) fc None m' (seg_rom rsegs) /\
             getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\
             getr R 9 = Z_to_bv 64 Ab /\ getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
             getr R 23 = Z_to_bv 64 q /\ getr R 25 = Z_to_bv 64 0 /\ getr R 24 = Z_to_bv 64 v56)
          \/
          (w <> 0 /\
             ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab) a0 a1 a2 a3 a4 a5 (Z_to_bv 64 a6v)
                           (Z_to_bv 64 a7v) (Z_to_bv 64 w) s3 s4 s5 (Z_to_bv 64 q) s7 (Z_to_bv 64 selv)
                           (Z_to_bv 64 frv) s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x815b4) fc None m' (seg_rom rsegs))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815a0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab q w frv a6v a7v selv v56 xs1 xs2 -> -> -> -> -> -> ->
    HAb0 HAb Hq Hw0 Hw Hfrv Ha6v Ha7v Hselv Hx1 Hx2 CH1 CH2 RO56 R40 R152 R56.
  lazymatch goal with |- evtF _ _ ?QQ _ => set (Q := QQ) end.
  pose proof (munch_refl [(Ab + 40, Ab + 56); (Ab + 152, Ab + 168)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x815a0 sd a7,152(s1); 0x815a4 sd a6,160(s1); 0x815a8 sd s8,48(s1); 0x815ac sd s9,40(s1) *)
  step. step. step. step.
  destruct CH1 as ((_ & HB1) & _). cbn [cells_bytes cbytes] in HB1. rewrite app_nil_r in HB1.
  apply bytes_at_app in HB1. destruct HB1 as (HB40 & HB48).
  rewrite length_le8 in HB48. change (Z.of_nat 8) with 8 in HB48.
  replace (Ab + 40 + 8) with (Ab + 48) in HB48 by lia.
  destruct CH2 as ((_ & HB2) & _). cbn [cells_bytes cbytes] in HB2. rewrite app_nil_r in HB2.
  apply bytes_at_app in HB2. destruct HB2 as (HB152 & HB160).
  rewrite length_le8 in HB160. change (Z.of_nat 8) with 8 in HB160.
  replace (Ab + 152 + 8) with (Ab + 160) in HB160 by lia.
  (* 0x815b0 beqz s2 *)
  step.
  destruct (Z.eq_dec w 0) as [E0|N0].
  - (* left = 0: 0x81af4 li s9,0; 0x81af8 mv s7,s6; 0x81afc j 81cac; 0x81cac ld s8,56(s1) *)
    subst w. bF_br.
    step. step. step. step.
    apply evtF_done. unfold Q. cbv beta.
    eexists. split; [exact MU|]. split; [exact WM|].
    split; [exact HB40|]. split; [exact HB48|]. split; [exact HB152|]. split; [exact HB160|].
    left. split; [reflexivity|]. eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [first [reflexivity | (f_equal; lia) | (rewrite Z.add_0_r; reflexivity)]|].
    split; [first [reflexivity | (f_equal; lia)]|].
    first [reflexivity | (f_equal; lia)].
  - bF_br.
    apply evtF_done. unfold Q. cbv beta.
    eexists. split; [exact MU|]. split; [exact WM|].
    split; [exact HB40|]. split; [exact HB48|]. split; [exact HB152|]. split; [exact HB160|].
    right. split; [exact N0 | reflexivity].
Qed.

(* ---- b_mode_evt (A5.v:379-451): the mode byte 0x815b4 .. 0x815e8 (no store).  Accesses: the mode byte's shadow
   byte [q / 8 + K] (the instrumented check 0x815cc), the mode byte [q] (0x815d8) and the code-byte pointer
   [Ab + 56] (0x815e4). ---- *)
Lemma b_mode_evt_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Ab q w K v56 : Z) (bm km : byte),
    s1 = Z_to_bv 64 Ab -> s2 = Z_to_bv 64 w -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    0 <= Ab -> Ab + 64 <= 2 ^ 64 ->
    0 < q -> q + 2 < 2 ^ 64 -> 1 <= w -> w + 2 < 2 ^ 64 -> 0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [km] ->
    (bv_signed km = 0 \/ q mod 8 < bv_signed km) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [bm] ->
    ro_cells rsegs m (Ab + 56) [C8 (Z_to_bv 64 v56)] ->
    rng RNG (q / 8 + K) 1 -> rng RNG q 1 -> rng RNG (Ab + 56) 8 ->
    evtF rsegs RNG
      (fun ms' =>
         (bv_unsigned bm mod 2 = 0 /\
          exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81cb0) fc None m (seg_rom rsegs) /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = Z_to_bv 64 Ab /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
            getr R 23 = Z_to_bv 64 (q + 1) /\ getr R 25 = Z_to_bv 64 (w - 1) /\ getr R 24 = Z_to_bv 64 v56)
         \/
         (bv_unsigned bm mod 2 = 1 /\
          exists x0 x1 : word,
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab) x0 x1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) s3 s4 s5
                          (zxb bm) (Z_to_bv 64 (q + 1)) (Z_to_bv 64 v56) (Z_to_bv 64 (w - 1)) s10 s11
                          t3 t4 t5 t6)
                     F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815b4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab q w K v56 bm km -> -> -> -> HAb0 HAb Hq0 Hq Hw0 Hw HK Hsh HRk HOKk HRm RO56 Rsh Rq R56.
  pose proof (rc_byte_signed km) as KRk.
  pose proof (bv_unsigned_in_range 8 bm) as HBM. unfold bv_modulus in HBM. cbn in HBM.
  lazymatch goal with |- evtF _ _ ?QQ _ => set (Q := QQ) end.
  (* 0x815b4 addi s7,s6,1; 0x815b8 li a0,1; 0x815bc bltu a0,s7 (T02) *)
  step. step. step. bF_br.
  (* 0x815c4 srli a0,s6,0x3; 0x815c8 add a0,a0,s10; 0x815cc lb a0,0(a0); 0x815d0 beqz a0 *)
  step. rewrite (MState.unsigned_lit q) by lia. rewrite rc_shr3.
  step. step. step.
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed km)) by lia.
  enough (KC : forall (x0 x1 : word),
    evtF rsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab) x0 x1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) s3 s4 s5
                         (Z_to_bv 64 q) (Z_to_bv 64 (q + 1)) s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x815d8) fc None m (seg_rom rsegs))).
  { destruct (Z.eqb_spec (bv_signed km) 0) as [E|E]; cbn [negb]; [apply KC|].
    (* 0x815d4 j 82fd0; 0x82fd0 andi a1,s6,7; 0x82fd4 bge a1,a0 (not taken) *)
    step. step. rewrite (MState.unsigned_lit q) by lia. rewrite rc_land7.
    step.
    rewrite (rc_lts_signed (q mod 8) (bv_signed km)) by lia.
    replace (q mod 8 <? bv_signed km) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [negb].
    (* 0x82fd8 j 815d8 *)
    step. apply KC. }
  intros x0 x1.
  (* 0x815d8 lbu s6,0(s6); 0x815dc andi a0,s6,1; 0x815e0 addi s9,s2,-1; 0x815e4 ld s8,56(s1); 0x815e8 beqz a0 *)
  step. step. step.
  unfold zxb at 1. rewrite (MState.unsigned_lit (bv_unsigned bm)) by lia. rewrite A5.b_land1 by lia.
  step.
  step.
  destruct (Z.eq_dec (bv_unsigned bm mod 2) 0) as [Ev|Od].
  - rewrite Ev. bF_br.
    apply evtF_done. unfold Q. cbv beta. left. split; [exact Ev|].
    eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [first [reflexivity | (f_equal; lia)]|].
    split; [first [reflexivity | (f_equal; lia)]|].
    first [reflexivity | (f_equal; lia)].
  - bF_br.
    apply evtF_done. unfold Q. cbv beta. right. split; [lia|].
    do 2 eexists.
    replace (Z_to_bv 64 (w + -1)) with (Z_to_bv 64 (w - 1)) by (f_equal; lia).
    reflexivity.
Qed.

(* A5.b_shadow_rw under a region guard P: a munch whose written shadow bytes are present after it keeps every
   shadow_rw_on region. *)
Lemma b_srw_on_munch : forall (P : Z -> Prop) W m m', B.ShadowRwOn.shadow_rw_on P m -> munch W m m' ->
  wmono rsegs m m' -> (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) ->
  B.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P W m m' HS MU WM H a Hp Ha. destruct (HS a Hp Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* ---- b_cat_evt _pre_F, route (C): no shadow premise; the post transports every shadow_rw_on region.
   0x815ec sb zero,332(s3); 0x815f0 sd zero,0(s4); 0x815f4 mv a0,s4; 0x815f8 jal, stopping AT the callee
   entry RBC.REAC_BOX_CATALOGUE with ra = 0x815fc and a0 = s4 = c.  Accesses: the catalogue count cell's shadow
   byte [Sh + 332] and the cell [c, c + 8). ---- *)
Lemma b_cat_evt_pre_F_on :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Sh c spv : Z) (sh1 cs : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s4 = Z_to_bv 64 c ->
    6283264 <= c -> c mod 8 = 0 -> c + 8 <= 140737488355328 ->
    6283264 <= spv - 16 -> spv <= 140737488355328 -> (c + 8 <= spv - 16 \/ spv <= c) ->
    (c + 8 <= Sh + 332 \/ Sh + 333 <= c) -> (spv <= Sh \/ Sh + 333 <= spv - 16) ->
    shadow_addr c = Sh + 332 ->
    (forall i, 0 <= i < 8 -> app_mem (c + i)) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    length sh1 = 1%nat -> length cs = 8%nat ->
    rw_cells rsegs m (Sh + 332) [CB 1 sh1] -> rw_cells rsegs m c [CB 8 cs] ->
    stk rsegs m (spv - 16) spv -> asan_cells m ->
    rng RNG (Sh + 332) 1 -> rng RNG c 8 ->
    evtF rsegs RNG
      (fun ms' => exists (mc : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x815fc) sp gp tp t0 t1 t2 s0 s1 s4 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 RBC.REAC_BOX_CATALOGUE) fc None mc (seg_rom rsegs) /\
         munch [(Sh + 332, Sh + 333); (c, c + 8); (spv - 16, spv)] m mc /\ wmono rsegs m mc /\
         bytes_at rsegs mc (Sh + 332) [Z_to_bv 8 0] /\ bytes_at rsegs mc c (le8 (Z_to_bv 64 0)) /\
         stk rsegs mc (spv - 16) spv /\ asan_cells mc /\
         (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P mc) /\
         wr_at rsegs mc c 8 /\ addressable mc c 8)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh c spv sh1 cs -> -> -> Hc Hc8 Hce Hsp0 Hspe Hsep Hdjc Hdjw Hshc Happc Happw Hsh1 Hcsl CHsh CHc
    ST HAC Rsh Rc.
  unfold RBC.REAC_BOX_CATALOGUE.
  pose proof (rw_cells_bound rsegs m (Sh + 332) _ CHsh) as HBsh.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HBsh.
  pose proof (rw_cells_bound rsegs m c _ CHc) as HBc.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HBc.
  pose proof (munch_refl [(Sh + 332, Sh + 333); (c, c + 8); (spv - 16, spv)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x815ec sb zero,332(s3); 0x815f0 sd zero,0(s4); 0x815f4 mv a0,s4 *)
  bF_sb. step. step.
  lazymatch type of MU with munch _ _ ?mm => set (mc := mm) in * end.
  rename MU into MU1. rename WM into WM1.
  assert (HZsh1 : bytes_at rsegs mc (Sh + 332) [Z_to_bv 8 0]).
  { destruct CHsh as ((_ & HB) & _). cbn [cells_bytes cbytes] in HB. rewrite ?app_nil_r in HB. exact HB. }
  assert (HZc1 : bytes_at rsegs mc c (le8 (Z_to_bv 64 0))).
  { destruct CHc as ((_ & HB) & _). cbn [cells_bytes cbytes] in HB. rewrite ?app_nil_r in HB. exact HB. }
  assert (Happc' : forall x, c <= x < c + 8 -> app_mem x).
  { intros x Hx. replace x with (c + (x - c)) by lia. apply Happc. lia. }
  assert (Hin332 : in_shadow (Sh + 332)).
  { rewrite <- Hshc. apply shadow_of_app.
    replace c with (c + 0) by lia. apply Happc. lia. }
  assert (HShb : 2147450880 <= Sh + 332 < 17592186044416 + 2147450880).
  { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin332. lia. }
  assert (Hshrng : forall a, in_shadow a -> 2147450880 <= a < 17592186044416 + 2147450880).
  { intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. }
  assert (Hcrng : c + 8 <= 2147450880 \/ 17592186044416 + 2147450880 <= c).
  { pose proof (Happc' c ltac:(lia)) as H1. pose proof (Happc' (c + 7) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. lia. }
  assert (Hwrng : spv <= 2147450880 \/ 17592186044416 + 2147450880 <= spv - 16).
  { pose proof (Happw (spv - 16) ltac:(lia)) as H1. pose proof (Happw (spv - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. lia. }
  assert (HAC1 : asan_cells mc).
  { apply (asan_cells_kept _ m mc HAC MU1). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  assert (HSW1 : forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P mc).
  { intros P HP. apply (b_srw_on_munch P _ m mc HP MU1 WM1). intros a Ha.
    destruct (Z.eq_dec a (Sh + 332)) as [->|Hne].
    - right. apply (A5.b_ba_rd mc (Sh + 332) [Z_to_bv 8 0] _ HZsh1). cbn [length]. lia.
    - left. cbn [outside]. pose proof (Hshrng a Ha).
      split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  (* the engine transported the callee window's stk to mc with the stores *)
  pose proof ST as ST1.
  assert (HADc : addressable mc c 8).
  { apply (A5.b_addr_z mc c 1 8); [reflexivity | lia | exact Hc8 | unfold APPMEM_END; lia
      | intros i Hi; apply Happc; lia |].
    rewrite Hshc. cbn [repeat]. exact HZsh1. }
  assert (HWRc : wr_at rsegs mc c 8).
  { destruct CHc as (_ & Hw). cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hw. exact Hw. }
  (* 0x815f8 jal reac_box_catalogue: stop at its entry *)
  step.
  apply evtF_done. exists mc.
  split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|]. split; [exact HZsh1|]. split; [exact HZc1|].
  split; [exact ST1|]. split; [exact HAC1|]. split; [exact HSW1|]. split; [exact HWRc | exact HADc].
Qed.

(* ---- b_cat_evt (A5.v:456-577), split at the call 0x815f8 jal reac_box_catalogue.
   _pre_F: 0x815ec sb zero,332(s3); 0x815f0 sd zero,0(s4); 0x815f4 mv a0,s4; 0x815f8 jal, stopping AT the callee
   entry RBC.REAC_BOX_CATALOGUE with ra = 0x815fc and a0 = s4 = c.  Accesses: the catalogue count cell's shadow
   byte [Sh + 332] and the cell [c, c + 8).  Its post is the state at the jal target with the facts the source run
   proved before the call (A5.v:497-535) and used at the call or after it. ---- *)
Lemma b_cat_evt_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Sh c spv : Z) (sh1 cs : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s4 = Z_to_bv 64 c ->
    6283264 <= c -> c mod 8 = 0 -> c + 8 <= 140737488355328 ->
    6283264 <= spv - 16 -> spv <= 140737488355328 -> (c + 8 <= spv - 16 \/ spv <= c) ->
    (c + 8 <= Sh + 332 \/ Sh + 333 <= c) -> (spv <= Sh \/ Sh + 333 <= spv - 16) ->
    shadow_addr c = Sh + 332 ->
    (forall i, 0 <= i < 8 -> app_mem (c + i)) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    length sh1 = 1%nat -> length cs = 8%nat ->
    rw_cells rsegs m (Sh + 332) [CB 1 sh1] -> rw_cells rsegs m c [CB 8 cs] ->
    stk rsegs m (spv - 16) spv -> asan_cells m -> shadow_rw m ->
    rng RNG (Sh + 332) 1 -> rng RNG c 8 ->
    evtF rsegs RNG
      (fun ms' => exists (mc : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x815fc) sp gp tp t0 t1 t2 s0 s1 s4 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 RBC.REAC_BOX_CATALOGUE) fc None mc (seg_rom rsegs) /\
         munch [(Sh + 332, Sh + 333); (c, c + 8); (spv - 16, spv)] m mc /\ wmono rsegs m mc /\
         bytes_at rsegs mc (Sh + 332) [Z_to_bv 8 0] /\ bytes_at rsegs mc c (le8 (Z_to_bv 64 0)) /\
         stk rsegs mc (spv - 16) spv /\ asan_cells mc /\ shadow_rw mc /\
         wr_at rsegs mc c 8 /\ addressable mc c 8)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh c spv sh1 cs Esp Es3 Es4 Hc Hc8 Hce Hsp0 Hspe Hsep Hdjc Hdjw Hshc Happc Happw Hsh1 Hcsl CHsh CHc
    ST HAC HSW Rsh Rc.
  refine (evtF_mono rsegs RNG _ _ _
            (b_cat_evt_pre_F_on RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
               s11 t3 t4 t5 t6 F fc m Sh c spv sh1 cs Esp Es3 Es4 Hc Hc8 Hce Hsp0 Hspe Hsep Hdjc Hdjw Hshc Happc
               Happw Hsh1 Hcsl CHsh CHc ST HAC Rsh Rc) _).
  intros ms' (mc & E & MU & WM & Z332 & Zc & ST1 & AC1 & SW & K).
  exists mc.
  do 7 (split; [assumption|]).
  split; [exact (B.ShadowRwOn.shadow_rw_of_on_all mc (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW)))|].
  exact K.
Qed.

(* _post_F, route (C): no shadow premise; the post transports every shadow_rw_on region from mc.  From the return pc
   0x815fc, with the catalogue's post facts as A5.v:553-557 uses them (a0 = BOX_CATALOGUE, a1 / a2 changed, the write
   set [(spv - 16, spv); (c, c + 8)], the window's stk, [c] = 11) over the post-call state m2, and the pre-call facts
   on mc the source run carries across the call (the write set and wmono from m, [Sh + 332] = 00).  The run ends at
   0x815fc: no instruction, no access. *)
Lemma b_cat_evt_post_F_on :
  forall (RNG : footprint)
         (sp gp tp t0 t1 t2 s0 s1 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m mc m2 : word -> option byte) (Sh c spv : Z),
    sp = Z_to_bv 64 spv ->
    (c + 8 <= Sh + 332 \/ Sh + 333 <= c) -> (spv <= Sh \/ Sh + 333 <= spv - 16) ->
    (forall i, 0 <= i < 8 -> app_mem (c + i)) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    munch [(Sh + 332, Sh + 333); (c, c + 8); (spv - 16, spv)] m mc -> wmono rsegs m mc ->
    bytes_at rsegs mc (Sh + 332) [Z_to_bv 8 0] ->
    munch [(spv - 16, spv); (c, c + 8)] mc m2 -> wmono rsegs mc m2 ->
    stk rsegs m2 (spv - 16) spv -> bytes_at rsegs m2 c (le8 (Z_to_bv 64 11)) ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x815fc) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         getr R 10 = Z_to_bv 64 RBC.BOX_CATALOGUE /\
         munch [(Sh + 332, Sh + 333); (c, c + 8); (spv - 16, spv)] m m' /\ wmono rsegs m m' /\
         (forall P, B.ShadowRwOn.shadow_rw_on P mc -> B.ShadowRwOn.shadow_rw_on P m') /\
         stk rsegs m' (spv - 16) spv /\
         bytes_at rsegs m' c (le8 (Z_to_bv 64 11)) /\ bytes_at rsegs m' (Sh + 332) [Z_to_bv 8 0])
      (MS (mkR (Z_to_bv 64 0x815fc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 RBC.BOX_CATALOGUE) a1' a2' a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815fc) fc None m2 (seg_rom rsegs)).
Proof.
  intros RNG sp gp tp t0 t1 t2 s0 s1 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m mc m2 Sh c spv -> Hdjc Hdjw Happc Happw MU1 WM1 HZsh1 MU2 WM2 ST2 HZ.
  assert (Hshrng : forall a, in_shadow a -> 2147450880 <= a < 17592186044416 + 2147450880).
  { intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. }
  assert (Hcrng : c + 8 <= 2147450880 \/ 17592186044416 + 2147450880 <= c).
  { pose proof (Happc 0 ltac:(lia)) as H1. pose proof (Happc 7 ltac:(lia)) as H2.
    rewrite Z.add_0_r in H1.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. lia. }
  assert (Hwrng : spv <= 2147450880 \/ 17592186044416 + 2147450880 <= spv - 16).
  { pose proof (Happw (spv - 16) ltac:(lia)) as H1. pose proof (Happw (spv - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. lia. }
  assert (Hsub : sub_fp [(spv - 16, spv); (c, c + 8)]
                   [(Sh + 332, Sh + 333); (c, c + 8); (spv - 16, spv)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  pose proof (munch_trans _ m mc m2 MU1 (munch_weaken _ _ mc m2 Hsub MU2)) as MUf.
  assert (HSW2 : forall P, B.ShadowRwOn.shadow_rw_on P mc -> B.ShadowRwOn.shadow_rw_on P m2).
  { intros P HP. apply (b_srw_on_munch P _ mc m2 HP MU2 WM2). intros a Ha. left. cbn [outside].
    pose proof (Hshrng a Ha). split; [lia|]. split; [lia | exact I]. }
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m mc m2 WM1 WM2)|].
  split; [exact HSW2|]. split; [exact ST2|]. split; [exact HZ|].
  apply (bytes_at_transport rsegs [(spv - 16, spv); (c, c + 8)] mc m2 _ _ HZsh1 MU2).
  cbn [length disjoint_from].
  split; [lia|]. split; [lia | exact I].
Qed.

(* _post_F: from the return pc 0x815fc, with the catalogue's post facts as A5.v:553-557 uses them (a0 =
   BOX_CATALOGUE, a1 / a2 changed, the write set [(spv - 16, spv); (c, c + 8)], the window's stk, [c] = 11) over the
   post-call state m2, and the pre-call facts on mc the source run carries across the call (the write set and
   wmono from m, the shadow map readable, [Sh + 332] = 00).  The run ends at 0x815fc: no instruction, no access. *)
Lemma b_cat_evt_post_F :
  forall (RNG : footprint)
         (sp gp tp t0 t1 t2 s0 s1 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m mc m2 : word -> option byte) (Sh c spv : Z),
    sp = Z_to_bv 64 spv ->
    (c + 8 <= Sh + 332 \/ Sh + 333 <= c) -> (spv <= Sh \/ Sh + 333 <= spv - 16) ->
    (forall i, 0 <= i < 8 -> app_mem (c + i)) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    munch [(Sh + 332, Sh + 333); (c, c + 8); (spv - 16, spv)] m mc -> wmono rsegs m mc ->
    shadow_rw mc -> bytes_at rsegs mc (Sh + 332) [Z_to_bv 8 0] ->
    munch [(spv - 16, spv); (c, c + 8)] mc m2 -> wmono rsegs mc m2 ->
    stk rsegs m2 (spv - 16) spv -> bytes_at rsegs m2 c (le8 (Z_to_bv 64 11)) ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x815fc) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         getr R 10 = Z_to_bv 64 RBC.BOX_CATALOGUE /\
         munch [(Sh + 332, Sh + 333); (c, c + 8); (spv - 16, spv)] m m' /\ wmono rsegs m m' /\
         shadow_rw m' /\ stk rsegs m' (spv - 16) spv /\
         bytes_at rsegs m' c (le8 (Z_to_bv 64 11)) /\ bytes_at rsegs m' (Sh + 332) [Z_to_bv 8 0])
      (MS (mkR (Z_to_bv 64 0x815fc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 RBC.BOX_CATALOGUE) a1' a2' a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815fc) fc None m2 (seg_rom rsegs)).
Proof.
  intros RNG sp gp tp t0 t1 t2 s0 s1 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m mc m2 Sh c spv Esp Hdjc Hdjw Happc Happw MU1 WM1 HSW1 HZsh1 MU2 WM2 ST2 HZ.
  refine (evtF_mono rsegs RNG _ _ _
            (b_cat_evt_post_F_on RNG sp gp tp t0 t1 t2 s0 s1 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6 F fc m mc m2 Sh c spv Esp Hdjc Hdjw Happc Happw MU1 WM1 HZsh1 MU2 WM2 ST2 HZ) _).
  intros ms' (R & m' & E & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G22 & G23 & G24 & G25 & G26 & G27 & G10 &
              MU & WM & SW & K).
  exists R, m'.
  do 18 (split; [assumption|]).
  split; [exact (B.ShadowRwOn.shadow_rw_of_on_all m' (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ mc HSW1)))|].
  exact K.
Qed.

(* ---- b_any_ld_evt (A5.v:790-818): the left <> 0 turn from either start (no instruction of its own). ---- *)
Lemma b_any_ld_evt_F :
  forall (RNG : footprint) (pc0 : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d q v K : Z) (b kq : byte),
    (pc0 = 0x81548 \/ (pc0 = 0x81550 /\ a3 = Z_to_bv 64 (q + 1))) ->
    a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 d ->
    s2 = Z_to_bv 64 v -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 -> 1 <= q -> q + 2 < 2 ^ 64 -> 1 <= v -> v + 1 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    store_ok rsegs m (wa d) 1 = true ->
    rng RNG (q / 8 + K) 1 -> rng RNG q 1 -> rng RNG d 1 ->
    evtF rsegs RNG
      (fun ms' => exists (x4 x5 : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 1) (Z_to_bv 64 (d + 1))
                       (Z_to_bv 64 (q + 1)) x4 x5 a6 a7 (Z_to_bv 64 (v - 1)) s3 s4 s5
                       (Z_to_bv 64 (q + 1)) s7 s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG pc0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d q v K b kq Hpc. intros.
  destruct Hpc as [-> | (-> & Ha3)].
  - eapply b_hd_ld_evt_F; eassumption.
  - eapply b_ld_evt_F; eassumption.
Qed.

(* ======== compare lemmas: the source statements from the _F forms at RNG_all ======== *)

Lemma b_ld_evt_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d q v K : Z) (b kq : byte),
    a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 d -> a3 = Z_to_bv 64 (q + 1) ->
    s2 = Z_to_bv 64 v -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 -> 1 <= q -> q + 2 < 2 ^ 64 -> 1 <= v -> v + 1 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    store_ok rsegs m (wa d) 1 = true ->
    evt rsegs
      (fun ms' => exists (x4 x5 : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 1) (Z_to_bv 64 (d + 1))
                       (Z_to_bv 64 (q + 1)) x4 x5 a6 a7 (Z_to_bv 64 (v - 1)) s3 s4 s5
                       (Z_to_bv 64 (q + 1)) s7 s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81550) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d q v K b kq E0 E1 E2 E3 E4 E5 E6 Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq HRb HS.
  apply (evtF_evt rsegs RNG_all).
  apply (b_ld_evt_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m cnt d q v K b kq E0 E1 E2 E3 E4 E5 E6 Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq HRb HS);
    apply rng_all; pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)); lia.
Qed.
Definition b_ld_evt_src_check : ltac:(let t := type of b_ld_evt_of_F in exact t) := A5.b_ld_evt.

Lemma b_hd_ld_evt_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d q v K : Z) (b kq : byte),
    a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 d ->
    s2 = Z_to_bv 64 v -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 -> 1 <= q -> q + 2 < 2 ^ 64 -> 1 <= v -> v + 1 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    store_ok rsegs m (wa d) 1 = true ->
    evt rsegs
      (fun ms' => exists (x4 x5 : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 1) (Z_to_bv 64 (d + 1))
                       (Z_to_bv 64 (q + 1)) x4 x5 a6 a7 (Z_to_bv 64 (v - 1)) s3 s4 s5
                       (Z_to_bv 64 (q + 1)) s7 s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81548) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d q v K b kq E0 E1 E2 E4 E5 E6 Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq HRb HS.
  apply (evtF_evt rsegs RNG_all).
  apply (b_hd_ld_evt_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m cnt d q v K b kq E0 E1 E2 E4 E5 E6 Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq HRb HS);
    apply rng_all; pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)); lia.
Qed.
Definition b_hd_ld_evt_src_check : ltac:(let t := type of b_hd_ld_evt_of_F in exact t) := A5.b_hd_ld_evt.

Lemma b_z_evt_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d : Z),
    a0 = Z_to_bv 64 cnt -> a2 = Z_to_bv 64 d -> s2 = Z_to_bv 64 0 ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 ->
    store_ok rsegs m (wa d) 1 = true ->
    evt rsegs
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) a1 (Z_to_bv 64 (d + 1)) a3
                       (Z_to_bv 64 0) a5 a6 a7 (Z_to_bv 64 0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [Z_to_bv 8 0])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81548) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d E0 E2 E4 Hcnt Hd0 Hd HS.
  apply (evtF_evt rsegs RNG_all).
  apply (b_z_evt_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m cnt d E0 E2 E4 Hcnt Hd0 Hd HS);
    apply rng_all; lia.
Qed.
Definition b_z_evt_src_check : ltac:(let t := type of b_z_evt_of_F in exact t) := A5.b_z_evt.

Lemma b_tail_evt_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Ab q w frv a6v a7v selv v56 : Z) (xs1 xs2 : list byte),
    s1 = Z_to_bv 64 Ab -> s2 = Z_to_bv 64 w -> s6 = Z_to_bv 64 q -> s9 = Z_to_bv 64 frv ->
    a6 = Z_to_bv 64 a6v -> a7 = Z_to_bv 64 a7v -> s8 = Z_to_bv 64 selv ->
    0 <= Ab -> Ab + 168 <= 2 ^ 64 -> 0 <= q < 2 ^ 64 -> 0 <= w -> w + 2 < 2 ^ 64 ->
    0 <= frv < 2 ^ 64 -> 0 <= a6v < 2 ^ 64 -> 0 <= a7v < 2 ^ 64 -> 0 <= selv < 2 ^ 64 ->
    length xs1 = 16%nat -> length xs2 = 16%nat ->
    rw_cells rsegs m (Ab + 40) [CB 16 xs1] -> rw_cells rsegs m (Ab + 152) [CB 16 xs2] ->
    ro_cells rsegs m (Ab + 56) [C8 (Z_to_bv 64 v56)] ->
    evt rsegs
      (fun ms' => exists (m' : word -> option byte),
         munch [(Ab + 40, Ab + 56); (Ab + 152, Ab + 168)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (Ab + 40) (le8 (Z_to_bv 64 frv)) /\
         bytes_at rsegs m' (Ab + 48) (le8 (Z_to_bv 64 selv)) /\
         bytes_at rsegs m' (Ab + 152) (le8 (Z_to_bv 64 a7v)) /\
         bytes_at rsegs m' (Ab + 160) (le8 (Z_to_bv 64 a6v)) /\
         ((w = 0 /\ exists R : bvmap 5 word,
             ms' = MS R F (Z_to_bv 64 0x81cb0) fc None m' (seg_rom rsegs) /\
             getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\
             getr R 9 = Z_to_bv 64 Ab /\ getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
             getr R 23 = Z_to_bv 64 q /\ getr R 25 = Z_to_bv 64 0 /\ getr R 24 = Z_to_bv 64 v56)
          \/
          (w <> 0 /\
             ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab) a0 a1 a2 a3 a4 a5 (Z_to_bv 64 a6v)
                           (Z_to_bv 64 a7v) (Z_to_bv 64 w) s3 s4 s5 (Z_to_bv 64 q) s7 (Z_to_bv 64 selv)
                           (Z_to_bv 64 frv) s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x815b4) fc None m' (seg_rom rsegs))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab q w frv a6v a7v selv v56 xs1 xs2 E1 E2 E3 E4 E5 E6 E7
    HAb0 HAb Hq Hw0 Hw Hfrv Ha6v Ha7v Hselv Hx1 Hx2 CH1 CH2 RO56.
  apply (evtF_evt rsegs RNG_all).
  apply (b_tail_evt_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m Ab q w frv a6v a7v selv v56 xs1 xs2 E1 E2 E3 E4 E5 E6 E7
           HAb0 HAb Hq Hw0 Hw Hfrv Ha6v Ha7v Hselv Hx1 Hx2 CH1 CH2 RO56);
    apply rng_all; lia.
Qed.
Definition b_tail_evt_src_check : ltac:(let t := type of b_tail_evt_of_F in exact t) := A5.b_tail_evt.

Lemma b_mode_evt_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Ab q w K v56 : Z) (bm km : byte),
    s1 = Z_to_bv 64 Ab -> s2 = Z_to_bv 64 w -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    0 <= Ab -> Ab + 64 <= 2 ^ 64 ->
    0 < q -> q + 2 < 2 ^ 64 -> 1 <= w -> w + 2 < 2 ^ 64 -> 0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [km] ->
    (bv_signed km = 0 \/ q mod 8 < bv_signed km) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [bm] ->
    ro_cells rsegs m (Ab + 56) [C8 (Z_to_bv 64 v56)] ->
    evt rsegs
      (fun ms' =>
         (bv_unsigned bm mod 2 = 0 /\
          exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81cb0) fc None m (seg_rom rsegs) /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = Z_to_bv 64 Ab /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
            getr R 23 = Z_to_bv 64 (q + 1) /\ getr R 25 = Z_to_bv 64 (w - 1) /\ getr R 24 = Z_to_bv 64 v56)
         \/
         (bv_unsigned bm mod 2 = 1 /\
          exists x0 x1 : word,
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab) x0 x1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) s3 s4 s5
                          (zxb bm) (Z_to_bv 64 (q + 1)) (Z_to_bv 64 v56) (Z_to_bv 64 (w - 1)) s10 s11
                          t3 t4 t5 t6)
                     F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815b4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab q w K v56 bm km E1 E2 E3 E4 HAb0 HAb Hq0 Hq Hw0 Hw HK Hsh HRk HOKk HRm RO56.
  apply (evtF_evt rsegs RNG_all).
  apply (b_mode_evt_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m Ab q w K v56 bm km E1 E2 E3 E4 HAb0 HAb Hq0 Hq Hw0 Hw HK Hsh HRk HOKk HRm RO56);
    apply rng_all; pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)); lia.
Qed.
Definition b_mode_evt_src_check : ltac:(let t := type of b_mode_evt_of_F in exact t) := A5.b_mode_evt.

Lemma b_any_ld_evt_of_F :
  forall (pc0 : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d q v K : Z) (b kq : byte),
    (pc0 = 0x81548 \/ (pc0 = 0x81550 /\ a3 = Z_to_bv 64 (q + 1))) ->
    a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 d ->
    s2 = Z_to_bv 64 v -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 -> 1 <= q -> q + 2 < 2 ^ 64 -> 1 <= v -> v + 1 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    store_ok rsegs m (wa d) 1 = true ->
    evt rsegs
      (fun ms' => exists (x4 x5 : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 1) (Z_to_bv 64 (d + 1))
                       (Z_to_bv 64 (q + 1)) x4 x5 a6 a7 (Z_to_bv 64 (v - 1)) s3 s4 s5
                       (Z_to_bv 64 (q + 1)) s7 s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
Proof.
  intros pc0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d q v K b kq Hpc E0 E1 E2 E4 E5 E6 Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq HRb HS.
  apply (evtF_evt rsegs RNG_all).
  apply (b_any_ld_evt_F RNG_all pc0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
           s11 t3 t4 t5 t6 F fc m cnt d q v K b kq Hpc E0 E1 E2 E4 E5 E6 Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq
           HRb HS);
    apply rng_all; pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)); lia.
Qed.
Definition b_any_ld_evt_src_check : ltac:(let t := type of b_any_ld_evt_of_F in exact t) := A5.b_any_ld_evt.

(* b_cat_evt from its two stretches and the catalogue contract taken at the call, as A5.v:538-552 takes it. *)
Lemma b_cat_evt_of_F : RBC.reac_box_catalogue_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Sh c spv : Z) (sh1 cs : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s4 = Z_to_bv 64 c ->
    6283264 <= c -> c mod 8 = 0 -> c + 8 <= 140737488355328 ->
    6283264 <= spv - 16 -> spv <= 140737488355328 -> (c + 8 <= spv - 16 \/ spv <= c) ->
    (c + 8 <= Sh + 332 \/ Sh + 333 <= c) -> (spv <= Sh \/ Sh + 333 <= spv - 16) ->
    shadow_addr c = Sh + 332 ->
    (forall i, 0 <= i < 8 -> app_mem (c + i)) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    length sh1 = 1%nat -> length cs = 8%nat ->
    rw_cells rsegs m (Sh + 332) [CB 1 sh1] -> rw_cells rsegs m c [CB 8 cs] ->
    stk rsegs m (spv - 16) spv -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x815fc) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         getr R 10 = Z_to_bv 64 RBC.BOX_CATALOGUE /\
         munch [(Sh + 332, Sh + 333); (c, c + 8); (spv - 16, spv)] m m' /\ wmono rsegs m m' /\
         shadow_rw m' /\ stk rsegs m' (spv - 16) spv /\
         bytes_at rsegs m' c (le8 (Z_to_bv 64 11)) /\ bytes_at rsegs m' (Sh + 332) [Z_to_bv 8 0])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)).
Proof.
  intros CATC ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh c spv sh1 cs Esp Es3 Es4 Hc Hc8 Hce Hsp0 Hspe Hsep Hdjc Hdjw Hshc Happc Happw Hsh1 Hcsl CHsh CHc
    ST HAC HSW.
  pose proof (rw_cells_bound rsegs m (Sh + 332) _ CHsh) as HBsh.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HBsh.
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    apply (b_cat_evt_pre_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             s11 t3 t4 t5 t6 F fc m Sh c spv sh1 cs Esp Es3 Es4 Hc Hc8 Hce Hsp0 Hspe Hsep Hdjc Hdjw Hshc Happc Happw
             Hsh1 Hcsl CHsh CHc ST HAC HSW);
      apply rng_all; lia. }
  intros ms1 (mc & E1 & MU1 & WM1 & HZsh1 & HZc1 & ST1 & HAC1 & HSW1 & HWRc & HADc).
  subst ms1.
  assert (Hshrng : forall a, in_shadow a -> 2147450880 <= a < 17592186044416 + 2147450880).
  { intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. }
  assert (Hcrng : c + 8 <= 2147450880 \/ 17592186044416 + 2147450880 <= c).
  { pose proof (Happc 0 ltac:(lia)) as H1. pose proof (Happc 7 ltac:(lia)) as H2.
    rewrite Z.add_0_r in H1.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. lia. }
  assert (Hwrng : spv <= 2147450880 \/ 17592186044416 + 2147450880 <= spv - 16).
  { pose proof (Happw (spv - 16) ltac:(lia)) as H1. pose proof (Happw (spv - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. lia. }
  subst sp s4.
  unfold RBC.reac_box_catalogue_contract, RBC.REAC_BOX_CATALOGUE_FRAME in CATC.
  eapply evt_cut.
  { eapply CATC with (c := c) (lo := spv - 16).
    - reflexivity.
    - rewrite (MState.unsigned_lit spv) by lia. exact ST1.
    - rewrite (MState.unsigned_lit spv) by lia. lia.
    - exact HAC1.
    - exact HSW1.
    - rewrite (MState.unsigned_lit spv) by lia.
      intros x [Hx | [Hx | Hx]].
      + cbn [outside]. unfold GOT_CELL_K in Hx. repeat split; (exact I || lia).
      + cbn [outside]. unfold CELL_K in Hx. repeat split; (exact I || lia).
      + cbn [outside]. pose proof (Hshrng x Hx).
        split; [lia|]. split; [lia | exact I].
    - rewrite (MState.unsigned_lit spv) by lia.
      right. split; [exact Hc8|]. split; [exact HWRc|]. split; [lia | exact HADc]. }
  intros ms' PO.
  destruct PO as (a1' & a2' & m2 & E & MU2 & WM2 & MI2 & ST2 & HZ).
  subst ms'.
  rewrite (MState.unsigned_lit spv) in MU2, ST2 by lia.
  rewrite (proj2 (Z.eqb_neq c 0) ltac:(lia)) in HZ.
  replace (ret_pc (Z_to_bv 64 0x815fc)) with (Z_to_bv 64 0x815fc)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (evtF_evt rsegs RNG_all).
  exact (b_cat_evt_post_F RNG_all (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 a1' a2' a3 a4 a5 a6 a7 s2 s3
           (Z_to_bv 64 c) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mc m2 Sh c spv eq_refl Hdjc Hdjw Happc Happw
           MU1 WM1 HSW1 HZsh1 MU2 WM2 ST2 HZ).
Qed.
Definition b_cat_evt_src_check : ltac:(let t := type of b_cat_evt_of_F in exact t) := A5.b_cat_evt.
