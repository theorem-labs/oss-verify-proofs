(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 3124 of its 3235 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F4.v, with its module paths and module names changed; 2763 of its 3239 lines of code are new or changed and 2759 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F9.v, with its addresses changed; 107 of its 220 lines of code are new or changed and 3126 lines of the source are left out. *)
(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17; measured against this image only;
   source runs: lib/B/Prog/Seg/F9.v f9_evtA (:297), f9_evtB_n (:552), f9_evtB (:786) at
     a working branch 3803efccea0 (blob 72e9d4aaf4b6386730fc37f834619c224d530832);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   split (parent 23:50Z: split at EVERY call, never state a callee contract locally):
     - f9_evtA has no call: f9_evtA_F is the whole run 0x82180 -> 0x821e0, same script with StepF `step`;
     - f9_evtB_n and f9_evtB are the SAME run 0x821e0 -> 0x821ec through the one call of
       reac_ctrl_identity_reply at 0x821e8, stated over a mem_inv memory (f9_evtB_n) and over a ro_agree memory
       carried through MemNorm.evt_normalize (f9_evtB).  Their pre stretch (F9.v:593 / F9.v:850, the three steps
       0x821e0 mv a0,s2 ; 0x821e4 mv a1,s4 ; 0x821e8 jal) touches NO memory, so the two coincide and neither the
       contract nor the normalization is needed: ONE lemma f9_evtB_pre_F covers both.  The callee's return pc
       0x821ec IS the exit cut (Inv_B821ec_at), so the post stretch is empty: there is no f9_evtB_post_F, and the
       walk composes reac_ctrl_identity_reply itself and lands on f9_evtB_n's / f9_evtB's own Q.
   compare: f9_evtA_of_F (evtF_evt + rng_all) re-derives the source statement of f9_evtA verbatim. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcReply RcParse RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib RcAsanFP
  asan_stack_malloc_c reac_ctrl_kind_name_c reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs Tac_f9 F9.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Requiring Tac_ro loads lib/Reusable/YK11.v as well, so the short name YK11 is ambiguous: import this unit's
   copy by its path, as F9.v does. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.
(* F9.v's own Local Ltac lia (the v1.9 frame size and its shadow length are the named constants FRAME_BYTES = 3136
   and FRAME_SHADOW = 392 of SlotInv.v); the StepF tactics keep the Lia one, which they bound at their definition. *)
Local Ltac lia := pose proof FRAME_BYTES_val; pose proof FRAME_SHADOW_val; Lia.lia.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module Frame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module MState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.

(* ---- F9.v's local step tactics, re-cut for the footprint goal `evtF segs RNG Q (MS ..)` (4 arguments;
   pilot fix (2)).  The bodies are F9.v's, unchanged. ---- *)

Ltac f9_bjoin_F G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (Sem.reg_get R r)) end.

Ltac f9_until_if_F :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; f9_until_if_F
  | _ => idtac
  end.

(* One instrumented 1-byte check of the byte X (srli; add s10; lb; bnez; slow path andi/bge/j), the error call not
   reached: the register r is generalized at the join. *)
Ltac f9_chk_F X r k RK OK :=
  step; rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
  step; step; clear RK; f9_until_if_F;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (pose proof (rc_byte_signed k); lia);
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if _ then _ else ?Bb) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RNG Q (MS (bvmap_set r rr R) F Bb fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ f9_bjoin_F G r
        | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7;
          step;
          rewrite (rc_lts_signed (X mod 8) (bv_signed k))
            by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); pose proof (rc_byte_signed k); lia);
          replace (X mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia);
          cbn [negb]; cbv iota; step;
          f9_bjoin_F G r ]
      | intros ?; simp_regs; clear OK ]
  end.

(* store_ok for the current memory, from a wr_at of the original memory. *)
Ltac f9_sok_F W a k n :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "HS" in
      assert (H : store_ok rsegs mm (wa (a + k)) n = true)
        by (eapply (wr_at_store_ok rsegs mm a _ k n); [repeat apply wr_at_write; exact W | lia | lia]);
      rewrite ?Z.add_0_r in H
  end.

(* Drop the store_ok hypothesis of the store just done (the stores need no mem_inv). *)
Ltac f9_cl_F :=
  match goal with
  | HS : store_ok rsegs ?m0 _ _ = true
    |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m0 _ _) _) => clear HS
  end.

(* A spill read in the current memory, from a bytes_at of the original memory. *)
Ltac f9_rdcur_F a v H :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let R := fresh "RL" in
      assert (R : ov_read_bytes rsegs mm (wa a) 8 = Some (le8 (Z_to_bv 64 v)))
        by (apply f9_rd8;
            [ repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia]); exact H
            | apply length_le8 ])
  end.

Ltac f9_bw_F :=
  repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia]).

(* ---- The footprint twin of f9_evtA: 0x82180 - 0x821dc, the checked read of the name byte at a0 = X (not '?'),
   then the three frame shadow bytes and the three frame cells.  Regions, in order of use:
     [X/8 + ASAN_K, +1)   read   the shadow byte of X (the instrumented check at 0x82180-0x8218c)
     [X, X+1)             read   the name byte (lbu at 0x82190)
     [S3+32, +1)          write  the shadow store at 0x821bc
     [A+288, +8)          read   the spill of the reply address cell (ld at 0x821c0)
     [fr+256, +2)         write  the reply address cell (sh at 0x821c4)
     [S3+34, +1)          write  the shadow store at 0x821c8
     [A+304, +8)          read   the spill of the reply payload cell (ld at 0x821cc)
     [fr+272, +8)         write  the reply payload cell (sd at 0x821d0)
     [S3+38, +1)          write  the shadow store at 0x821d4
     [A+296, +8)          read   the spill of the reply length cell (ld at 0x821d8)
     [fr+304, +8)         write  the reply length cell (sd at 0x821dc)
   The three shadow stores are direct writes of the shadow map, not instrumented accesses. ---- *)

Lemma f9_evtA_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Q : machine_state -> Prop)
         (X A S3 fr phi len : Z) (b c0 : byte),
    0 <= X < 2 ^ 47 -> 0 <= S3 -> 0 <= fr -> 0 <= A ->
    fr + FRAME_BYTES <= A -> A + 448 <= 2 ^ 64 -> S3 + FRAME_SHADOW <= A ->
    (S3 + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= S3) ->
    ov_read_bytes rsegs m (wa (X / 8 + ASAN_K)) 1 = Some [b] ->
    (bv_signed b = 0 \/ X mod 8 < bv_signed b) ->
    ov_read_bytes rsegs m (wa X) 1 = Some [c0] -> bv_unsigned c0 <> 63 ->
    wr_at rsegs m S3 FRAME_SHADOW ->
    wr_at rsegs m (fr + 256) 2 -> wr_at rsegs m (fr + 272) 8 -> wr_at rsegs m (fr + 304) 8 ->
    bytes_at rsegs m (A + 288) (le8 (Z_to_bv 64 (fr + 256))) ->
    bytes_at rsegs m (A + 304) (le8 (Z_to_bv 64 (fr + 272))) ->
    bytes_at rsegs m (A + 296) (le8 (Z_to_bv 64 (fr + 304))) ->
    rng RNG (X / 8 + ASAN_K) 1 -> rng RNG X 1 ->
    rng RNG (S3 + 32) 1 -> rng RNG (S3 + 34) 1 -> rng RNG (S3 + 38) 1 ->
    rng RNG (A + 288) 8 -> rng RNG (A + 296) 8 -> rng RNG (A + 304) 8 ->
    rng RNG (fr + 256) 2 -> rng RNG (fr + 272) 8 -> rng RNG (fr + 304) 8 ->
    (forall (m1 : word -> option byte),
       munch (f9_WA S3 fr) m m1 -> wmono rsegs m m1 ->
       (forall q, (exists bq, mbyte rsegs m q = Some bq) -> exists bq, mbyte rsegs m1 q = Some bq) ->
       bytes_at rsegs m1 (S3 + 32) (le1 (Z_to_bv 64 2)) ->
       bytes_at rsegs m1 (S3 + 34) (le1 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (S3 + 38) (le1 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (fr + 256) (le2 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (fr + 272) (le8 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (fr + 304) (le8 (Z_to_bv 64 0)) ->
       wr_at rsegs m1 (fr + 256) 2 -> wr_at rsegs m1 (fr + 272) 8 -> wr_at rsegs m1 (fr + 304) 8 ->
       Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 2) (zxb c0) (Z_to_bv 64 (fr + 256))
                  (Z_to_bv 64 (fr + 272)) (Z_to_bv 64 (fr + 304)) a5 a6 a7
                  (Z_to_bv 64 phi) (Z_to_bv 64 S3) (Z_to_bv 64 len) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11
                  t3 t4 t5 t6)
             Fr (Z_to_bv 64 0x821e0) fc None m1 (seg_rom rsegs))) ->
    evtF rsegs RNG Q
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 phi) (Z_to_bv 64 S3) (Z_to_bv 64 len) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11
               t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82180) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
    Fr fc m Q X A S3 fr phi len b c0 HX HS30 Hfr0 HA0 HfrA HA64 HS3A HS3fr
    RK OK RC0 HC0 Wsh Wa Wp Wn Q256 Q272 Q264
    Rsh Rx R32 R34 R38 R288 R296 R304 R256 R272 R304f HQ.
  (* 0x82180-0x8218c the instrumented check of the byte X *)
  f9_chk_F X (Z_to_bv 5 12) b RK OK.
  (* 0x82190 lbu a1,0(a0) ; 0x82194 li a2,63 ; 0x82198 bne a1,a2 taken to 0x821b8 *)
  step. step. step. rewrite (f9_neq63 c0 HC0). cbn [negb]. cbv iota.
  (* 0x821b8 li a0,2 ; 0x821bc sb a0,32(s3) *)
  step.
  f9_sok_F Wsh S3 32 1%nat. step. f9_cl_F.
  (* 0x821c0 ld a2,288(s1) ; 0x821c4 sh zero,0(a2) *)
  f9_rdcur_F (A + 288) (fr + 256) Q256. step.
  f9_sok_F Wa (fr + 256) 0 2%nat. step. f9_cl_F.
  (* 0x821c8 sb zero,34(s3) *)
  f9_sok_F Wsh S3 34 1%nat. step. f9_cl_F.
  (* 0x821cc ld a3,272(s1) ; 0x821d0 sd zero,0(a3) *)
  f9_rdcur_F (A + 304) (fr + 272) Q272. step.
  f9_sok_F Wp (fr + 272) 0 8%nat. step. f9_cl_F.
  (* 0x821d4 sb zero,38(s3) *)
  f9_sok_F Wsh S3 38 1%nat. step. f9_cl_F.
  (* 0x821d8 ld a4,296(s1) ; 0x821dc sd zero,0(a4) *)
  f9_rdcur_F (A + 296) (fr + 304) Q264. step.
  f9_sok_F Wn (fr + 304) 0 8%nat. step. f9_cl_F.
  apply evtF_done. apply HQ.
  - cbv [f9_WA].
    repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
    apply munch_refl.
  - repeat apply wmono_write. apply wmono_refl.
  - intros q Hq. repeat apply f9_pres. exact Hq.
  - f9_bw_F. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw_F. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw_F. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw_F. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw_F. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw_F. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - repeat apply wr_at_write. exact Wa.
  - repeat apply wr_at_write. exact Wp.
  - repeat apply wr_at_write. exact Wn.
Qed.

(* The compare lemma the auditor checks: the SOURCE statement of f9_evtA, verbatim, out of f9_evtA_F at
   RNG := RNG_all (evtF_evt), every rng premise by rng_all. *)
Lemma f9_evtA_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Q : machine_state -> Prop)
         (X A S3 fr phi len : Z) (b c0 : byte),
    0 <= X < 2 ^ 47 -> 0 <= S3 -> 0 <= fr -> 0 <= A ->
    fr + FRAME_BYTES <= A -> A + 448 <= 2 ^ 64 -> S3 + FRAME_SHADOW <= A ->
    (S3 + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= S3) ->
    ov_read_bytes rsegs m (wa (X / 8 + ASAN_K)) 1 = Some [b] ->
    (bv_signed b = 0 \/ X mod 8 < bv_signed b) ->
    ov_read_bytes rsegs m (wa X) 1 = Some [c0] -> bv_unsigned c0 <> 63 ->
    wr_at rsegs m S3 FRAME_SHADOW ->
    wr_at rsegs m (fr + 256) 2 -> wr_at rsegs m (fr + 272) 8 -> wr_at rsegs m (fr + 304) 8 ->
    bytes_at rsegs m (A + 288) (le8 (Z_to_bv 64 (fr + 256))) ->
    bytes_at rsegs m (A + 304) (le8 (Z_to_bv 64 (fr + 272))) ->
    bytes_at rsegs m (A + 296) (le8 (Z_to_bv 64 (fr + 304))) ->
    (forall (m1 : word -> option byte),
       munch (f9_WA S3 fr) m m1 -> wmono rsegs m m1 ->
       (forall q, (exists bq, mbyte rsegs m q = Some bq) -> exists bq, mbyte rsegs m1 q = Some bq) ->
       bytes_at rsegs m1 (S3 + 32) (le1 (Z_to_bv 64 2)) ->
       bytes_at rsegs m1 (S3 + 34) (le1 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (S3 + 38) (le1 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (fr + 256) (le2 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (fr + 272) (le8 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (fr + 304) (le8 (Z_to_bv 64 0)) ->
       wr_at rsegs m1 (fr + 256) 2 -> wr_at rsegs m1 (fr + 272) 8 -> wr_at rsegs m1 (fr + 304) 8 ->
       Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 2) (zxb c0) (Z_to_bv 64 (fr + 256))
                  (Z_to_bv 64 (fr + 272)) (Z_to_bv 64 (fr + 304)) a5 a6 a7
                  (Z_to_bv 64 phi) (Z_to_bv 64 S3) (Z_to_bv 64 len) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11
                  t3 t4 t5 t6)
             Fr (Z_to_bv 64 0x821e0) fc None m1 (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 phi) (Z_to_bv 64 S3) (Z_to_bv 64 len) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11
               t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82180) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
    Fr fc m Q X A S3 fr phi len b c0 HX HS30 Hfr0 HA0 HfrA HA64 HS3A HS3fr
    RK OK RC0 HC0 Wsh Wa Wp Wn Q256 Q272 Q264 HQ.
  assert (HK : ASAN_K = 0x7fff8000) by reflexivity.
  assert (HX8 : 0 <= X / 8 < 2 ^ 44) by (Z.div_mod_to_equations; lia).
  apply (evtF_evt rsegs RNG_all).
  apply (f9_evtA_F RNG_all ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
           Fr fc m Q X A S3 fr phi len b c0 HX HS30 Hfr0 HA0 HfrA HA64 HS3A HS3fr
           RK OK RC0 HC0 Wsh Wa Wp Wn Q256 Q272 Q264);
    try (apply rng_all; lia).
  exact HQ.
Qed.
Definition f9_evtA_src_check : ltac:(let T := type of F9.f9_evtA in exact T) := f9_evtA_of_F.

(* ---- The footprint twin of the pre stretch of f9_evtB_n (F9.v:593) and of f9_evtB (F9.v:850): the two argument
   moves and the call of reac_ctrl_identity_reply (entry 0x848fc, return pc 0x821ec).  The stretch touches no
   memory, so it carries no rng premise, and the mem_inv / ro_agree forms of the two source runs coincide. ---- *)
Lemma f9_evtB_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 a0 a1 s5 s6 s7 s8 s9 s11 a5 a6 a7 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A S3 fr phi len : Z),
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x821ec) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                               (Z_to_bv 64 phi) (Z_to_bv 64 len) (Z_to_bv 64 (fr + 256))
                               (Z_to_bv 64 (fr + 272)) (Z_to_bv 64 (fr + 304)) a5 a6 a7
                               (Z_to_bv 64 phi) (Z_to_bv 64 S3) (Z_to_bv 64 len) s5 s6 s7
                               s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                          Fr (Z_to_bv 64 0x848fc) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 (Z_to_bv 64 (fr + 256)) (Z_to_bv 64 (fr + 272))
               (Z_to_bv 64 (fr + 304)) a5 a6 a7 (Z_to_bv 64 phi) (Z_to_bv 64 S3) (Z_to_bv 64 len) s5 s6 s7
               s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x821e0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 a0 a1 s5 s6 s7 s8 s9 s11 a5 a6 a7 t3 t4 t5 t6 Fr fc m A S3 fr phi len.
  (* 0x821e0 mv a0,s2 ; 0x821e4 mv a1,s4 ; 0x821e8 jal reac_ctrl_identity_reply *)
  step. step. step.
  apply evtF_done. reflexivity.
Qed.
