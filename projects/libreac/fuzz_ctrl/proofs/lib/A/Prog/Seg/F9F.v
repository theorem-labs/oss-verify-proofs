(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 3124 of its 3235 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F4.v, with its module paths and module names changed; 2763 of its 3239 lines of code are new or changed and 2759 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F9.v, with its module paths, addresses and numbers changed; 233 of its 363 lines of code are new or changed and 3109 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F9.v c7c98da8c557 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: f9_evtA_of_F re-derives F9.f9_evtA at ExecF.RNG_all; f9_evtA_of_F_verbatim checks by constr_eq that its
   type is the type of F9.f9_evtA. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) form of F9.v's run lemma f9_evtA (:176), 0x81f88 -> 0x81fe8: the instrumented 1-byte check of
   the name byte at a0 = X (slow path 0x82984, error call 0x82cb4 NOT reached), the read of that byte, the three
   frame shadow bytes S3+32 / +34 / +38 and the three frame cells [fr+256] (2 bytes), [fr+272] (8), [fr+304] (8),
   with the three spill reads [A+256], [A+272], [A+264] that give their addresses. The run is re-stepped with
   lib.Lib StepF as an ExecF.evtF under a universally quantified footprint RNG, with the same binders and premises
   in the same order and the footprint premises appended; the continuation premise HQ is unchanged (it states Q of
   the exit state, not a run). The rng premises are exactly the regions the lemma's own premises name: the shadow
   byte X / 8 + ASAN_K and the byte X (the two ov_read_bytes premises), the frame-shadow window [S3, S3+FRAME_SHADOW)
   and the three frame cells (the four wr_at premises), and the three spill cells (the three bytes_at premises).
   Instruction fetch is not an access, and the slow path makes no memory access (andi / bge / j).

   F9.v's other run lemma, f9_evtB (:602), is NOT re-run here: it calls reac_ctrl_identity_reply through
   reac_ctrl_identity_reply_contract, and no reac_ctrl_identity_reply_contract_F exists in this tree (searched
   proofs/libreac/fuzz_ctrl and a working branch 28b0af0a5b2). Per the spec that run stays plain:
   "blocked: reac_ctrl_identity_reply has no _F".

   F9.v itself is unchanged apart from comment text; its seg_F9 / halts proofs still use f9_evtA. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcReply RcParse RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs F9.
(* Last but YK11: StepF's step / if_false / finish (evtF goals) shadow lib.Lib Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11's register reads (the names F9's statements are written over). *)
Import YK11.
Open Scope Z_scope.

Module F9LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* F9.v's f9_bjoin / f9_until_if / f9_chk / f9_sok / f9_rdcur over evtF goals: the same tactics, with the engine's
   evtF (one more argument, the footprint) in each pattern. This is the one change the template shows must be
   made (F5F.v's f5F_mkR_expand / f5F_subst_slot). *)
Ltac f9F_bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (Sem.reg_get R r)) end.

Ltac f9F_until_if :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; f9F_until_if
  | _ => idtac
  end.

Ltac f9F_chk X r k RK OK :=
  step; rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
  step; step; clear RK; f9F_until_if;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (pose proof (rc_byte_signed k); lia);
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if _ then _ else ?Bb) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RNG Q (MS (bvmap_set r rr R) F Bb fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ f9F_bjoin G r
        | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7;
          step;
          rewrite (rc_lts_signed (X mod 8) (bv_signed k))
            by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); pose proof (rc_byte_signed k); lia);
          replace (X mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia);
          cbn [negb]; cbv iota; step;
          f9F_bjoin G r ]
      | intros ?; simp_regs; clear OK ]
  end.

Ltac f9F_sok W a k n :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "HS" in
      assert (H : store_ok rsegs mm (wa (a + k)) n = true)
        by (eapply (wr_at_store_ok rsegs mm a _ k n); [repeat apply wr_at_write; exact W | lia | lia]);
      rewrite ?Z.add_0_r in H
  end.

Ltac f9F_rdcur a v H :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let R := fresh "RL" in
      assert (R : ov_read_bytes rsegs mm (wa a) 8 = Some (le8 (Z_to_bv 64 v)))
        by (apply f9_rd8;
            [ repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia]); exact H
            | apply length_le8 ])
  end.

Ltac f9F_bw :=
  repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia]).

(* 0x81f88 - 0x81fe4 under a footprint: the checked read of the name byte at a0 = X (not '?'), then the three frame
   shadow bytes and the three frame cells. *)
Lemma f9_evtA_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Q : machine_state -> Prop)
         (X A S3 fr phi len : Z) (b c0 : byte),
    0 <= X < 2 ^ 47 -> 0 <= S3 -> 0 <= fr -> 0 <= A ->
    fr + FRAME_BYTES <= A -> A + 416 <= 2 ^ 64 -> S3 + FRAME_SHADOW <= A ->
    (S3 + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= S3) ->
    ov_read_bytes rsegs m (wa (X / 8 + ASAN_K)) 1 = Some [b] ->
    (bv_signed b = 0 \/ X mod 8 < bv_signed b) ->
    ov_read_bytes rsegs m (wa X) 1 = Some [c0] -> bv_unsigned c0 <> 63 ->
    wr_at rsegs m S3 FRAME_SHADOW ->
    wr_at rsegs m (fr + 256) 2 -> wr_at rsegs m (fr + 272) 8 -> wr_at rsegs m (fr + 304) 8 ->
    bytes_at rsegs m (A + 256) (le8 (Z_to_bv 64 (fr + 256))) ->
    bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 (fr + 272))) ->
    bytes_at rsegs m (A + 264) (le8 (Z_to_bv 64 (fr + 304))) ->
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
                  (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi) s8 s9 (Z_to_bv 64 ASAN_K) s11
                  t3 t4 t5 t6)
             Fr (Z_to_bv 64 0x81fe8) fc None m1 (seg_rom rsegs))) ->
    rng RNG (X / 8 + ASAN_K) 1 ->
    rng RNG X 1 ->
    rng RNG S3 FRAME_SHADOW ->
    rng RNG (fr + 256) 2 ->
    rng RNG (fr + 272) 8 ->
    rng RNG (fr + 304) 8 ->
    rng RNG (A + 256) 8 ->
    rng RNG (A + 272) 8 ->
    rng RNG (A + 264) 8 ->
    evtF rsegs RNG Q
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi) s8 s9 (Z_to_bv 64 ASAN_K) s11
               t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f88) fc None m (seg_rom rsegs)).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6
    Fr fc m Q X A S3 fr phi len b c0 HX HS30 Hfr0 HA0 HfrA HA64 HS3A HS3fr
    RK OK RC0 HC0 Wsh Wa Wp Wn Q256 Q272 Q264 HQ RSH RX RWSH R256 R272 R304 RS256 RS272 RS264.
  (* 0x81f88-0x81f94 the instrumented check of the byte X *)
  f9F_chk X (Z_to_bv 5 12) b RK OK.
  (* 0x81f98 lbu a1,0(a0) ; 0x81f9c li a2,63 ; 0x81fa0 bne a1,a2 taken to 0x81fc0 *)
  step. step. step. rewrite (f9_neq63 c0 HC0). cbn [negb]. cbv iota.
  (* 0x81fc0 li a0,2 ; 0x81fc4 sb a0,32(s3) *)
  step.
  f9F_sok Wsh S3 32 1%nat. step.
  (* 0x81fc8 ld a2,256(s1) ; 0x81fcc sh zero,0(a2) *)
  f9F_rdcur (A + 256) (fr + 256) Q256. step.
  f9F_sok Wa (fr + 256) 0 2%nat. step.
  (* 0x81fd0 sb zero,34(s3) *)
  f9F_sok Wsh S3 34 1%nat. step.
  (* 0x81fd4 ld a3,272(s1) ; 0x81fd8 sd zero,0(a3) *)
  f9F_rdcur (A + 272) (fr + 272) Q272. step.
  f9F_sok Wp (fr + 272) 0 8%nat. step.
  (* 0x81fdc sb zero,38(s3) *)
  f9F_sok Wsh S3 38 1%nat. step.
  (* 0x81fe0 ld a4,264(s1) ; 0x81fe4 sd zero,0(a4) *)
  f9F_rdcur (A + 264) (fr + 304) Q264. step.
  f9F_sok Wn (fr + 304) 0 8%nat. step.
  apply evtF_done. apply HQ.
  - cbv [f9_WA].
    repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
    apply munch_refl.
  - repeat apply wmono_write. apply wmono_refl.
  - intros q Hq. repeat apply f9_pres. exact Hq.
  - f9F_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9F_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9F_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9F_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9F_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9F_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - repeat apply wr_at_write. exact Wa.
  - repeat apply wr_at_write. exact Wp.
  - repeat apply wr_at_write. exact Wn.
Qed.

(* F9.f9_evtA's statement back from f9_evtA_F at RNG_all: each region's bounds come from the lemma's own premises
   (X < 2^47 and ASAN_K for the shadow byte; S3 >= 0 and S3 + FRAME_SHADOW <= A <= 2^64 - 416 for the frame shadow;
   fr >= 0 and fr + FRAME_BYTES <= A for the three frame cells; A >= 0 and A + 416 <= 2^64 for the three spills). *)
Lemma f9_evtA_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Q : machine_state -> Prop)
         (X A S3 fr phi len : Z) (b c0 : byte),
    0 <= X < 2 ^ 47 -> 0 <= S3 -> 0 <= fr -> 0 <= A ->
    fr + FRAME_BYTES <= A -> A + 416 <= 2 ^ 64 -> S3 + FRAME_SHADOW <= A ->
    (S3 + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= S3) ->
    ov_read_bytes rsegs m (wa (X / 8 + ASAN_K)) 1 = Some [b] ->
    (bv_signed b = 0 \/ X mod 8 < bv_signed b) ->
    ov_read_bytes rsegs m (wa X) 1 = Some [c0] -> bv_unsigned c0 <> 63 ->
    wr_at rsegs m S3 FRAME_SHADOW ->
    wr_at rsegs m (fr + 256) 2 -> wr_at rsegs m (fr + 272) 8 -> wr_at rsegs m (fr + 304) 8 ->
    bytes_at rsegs m (A + 256) (le8 (Z_to_bv 64 (fr + 256))) ->
    bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 (fr + 272))) ->
    bytes_at rsegs m (A + 264) (le8 (Z_to_bv 64 (fr + 304))) ->
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
                  (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi) s8 s9 (Z_to_bv 64 ASAN_K) s11
                  t3 t4 t5 t6)
             Fr (Z_to_bv 64 0x81fe8) fc None m1 (seg_rom rsegs))) ->
    F9LE.evt rsegs Q
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi) s8 s9 (Z_to_bv 64 ASAN_K) s11
               t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f88) fc None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6
    Fr fc m Q X A S3 fr phi len b c0 HX HS30 Hfr0 HA0 HfrA HA64 HS3A HS3fr
    RK OK RC0 HC0 Wsh Wa Wp Wn Q256 Q272 Q264 HQ.
  assert (HK : ASAN_K = 2147450880) by reflexivity.
  eapply evtF_evt,
    (f9_evtA_F RNG_all ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6
       Fr fc m Q X A S3 fr phi len b c0);
    try eassumption; apply rng_all; lia.
Qed.

(* The pin: f9_evtA_of_F states F9.f9_evtA's v1.9 text, term for term (constr_eq: syntactic, not up to
   conversion). f9_evtA takes no callee contract, so nothing is stripped. *)
Example f9_evtA_of_F_verbatim : True.
Proof.
  let a := type of F9.f9_evtA in let b := type of f9_evtA_of_F in constr_eq a b.
  exact I.
Qed.

(* ================= SPLIT STRETCHES for f9_evtB (a Theorem Labs lane ruling 00:45Z) =================
   f9_evtB (F9.v:602) calls reac_ctrl_identity_reply at 0x81ff0, and no reac_ctrl_identity_reply_contract_F
   exists in this tree, so the glue splits at the call:
     call pc 0x81ff0, callee REAC_CTRL_IDENTITY_REPLY, return pc 0x81ff4.
   f9_evtB_pre_F  : 0x81fe8 -> the callee entry state (mv a0,s7 ; mv a1,s2 ; jal), as Seg/R15.v rfree_evt ends.
                    The three instructions touch no memory, so no rng premise is appended.
   f9_evtB_post_F : the post stretch is EMPTY - the return pc 0x81ff4 IS f9_evtB's exit (the F10 entry cut), so
                    the stretch runs zero instructions and reads no memory; it is the canonical-register-map
                    statement at the return pc, concluding the source run's post (its CPS predicate Q).
   f9_evtB_of_pre_post : the two stretches at ExecF.RNG_all plus the PLAIN contract re-derive F9.f9_evtB by the
                    source's own script (the normalize lift and the RoAdapt transports are cut from it unchanged).
   The callee contract appears in no _F statement. ================================================== *)

(* ---- the pre stretch: 0x81fe8 -> REAC_CTRL_IDENTITY_REPLY, ra = 0x81ff4 ---- *)
Lemma f9_evtB_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 a0 a1 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S3 fr phi len : Z),
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81ff4) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                                (Z_to_bv 64 phi) (Z_to_bv 64 len)
                                (Z_to_bv 64 (fr + 256)) (Z_to_bv 64 (fr + 272)) (Z_to_bv 64 (fr + 304))
                                a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi)
                                s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 (Z_to_bv 64 (fr + 256)) (Z_to_bv 64 (fr + 272))
               (Z_to_bv 64 (fr + 304)) a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi)
               s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81fe8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 a0 a1 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 Fr fc m A S3 fr phi len.
  (* 0x81fe8 mv a0,s7 ; 0x81fec mv a1,s2 ; 0x81ff0 jal reac_ctrl_identity_reply *)
  step. step. step.
  apply evtF_done. reflexivity.
Qed.

Section SplitF.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

(* ---- the post stretch: zero instructions at the return pc 0x81ff4 (f9_evtB's exit cut) ---- *)
Lemma f9_evtB_post_F :
  forall (RNG : footprint) (regs : bvmap 5 word) (mem : word -> option byte) (Q : machine_state -> Prop),
    Q (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81ff4) fp_csr None mem (seg_rom rsegs)) ->
    evtF rsegs RNG Q
      (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81ff4) fp_csr None mem (seg_rom rsegs)).
Proof. intros RNG regs mem Q HQ. apply evtF_done. exact HQ. Qed.

End SplitF.

(* ---- the two stretches at ExecF.RNG_all plus the PLAIN contract re-derive F9.f9_evtB, by the source's own
   script: the three entry instructions come from f9_evtB_pre_F, the exit from f9_evtB_post_F, and everything
   between (the normalize lift, the contract application and RoAdapt's transports) is F9.v's text unchanged. *)
Lemma f9_evtB_of_pre_post :
  forall (ra0 sp gp tp t0 t1 t2 s0 a0 a1 s4 s5 s6 s8 s9 s11 a5 a6 a7 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
         (A S3 fr phi len S FS TP : Z) (G ja jp jn : list byte),
    reac_ctrl_identity_reply_contract ->
    sp = Z_to_bv 64 S -> tp = Z_to_bv 64 TP -> 0 <= TP < 2 ^ 64 -> 6283264 <= fr ->
    f9_pre phi len (fr + 256) (fr + 272) (fr + 304) S FS TP m G ja jp jn ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       munch (reac_ctrl_identity_reply_fp phi len (fr + 256) (fr + 272) (fr + 304) S G ++
              fp_w [1%nat] FS ++
              [(shadow_addr (S - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr S)]) m m' ->
       wmono rsegs m m' -> ro_agree rsegs m' ->
       stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
       (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G = true ->
          rw_cells rsegs m' (fr + 256) [CB 2 (reply_addr G)] /\
          rw_cells rsegs m' (fr + 272) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
          rw_cells rsegs m' (fr + 304) [CB 8 (le8 (Z_to_bv 64 (ir_s G - 13)))]) ->
       asan_cells m' -> shadow_rw m' ->
       addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
       fp [1%nat] m' TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
         (reac_ctrl_identity_reply_W phi (fr + 256) (fr + 272) (fr + 304) S)
         (reac_ctrl_identity_reply_D phi len (fr + 256) (fr + 272) (fr + 304)) ->
       reac_ctrl_identity_reply_tls m' TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
       Q (MS (mkR (Z_to_bv 64 0x81ff4) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                  (Z_to_bv 64 (reply_ret phi len (fr + 256) (fr + 272) (fr + 304) G))
                  a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi)
                  s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
             Fr (Z_to_bv 64 0x81ff4) fc None m' (seg_rom rsegs))) ->
    F9LE.evt rsegs Q
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 (Z_to_bv 64 (fr + 256)) (Z_to_bv 64 (fr + 272))
               (Z_to_bv 64 (fr + 304)) a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi)
               s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81fe8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a0 a1 s4 s5 s6 s8 s9 s11 a5 a6 a7 t3 t4 t5 t6 Fr fc m Q A S3 fr phi len S0 FS TP
    G ja jp jn HIR Hsp Htp HTP Hfr Hpre HK.
  destruct Hpre as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 &
    P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28).
  assert (HK9 : REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  pose proof (mem_rel_normalize rsegs m P10) as REL.
  (* the contract's premises on the normalized memory *)
  assert (P9n : stk rsegs (normalize rsegs m) (S0 - REAC_CTRL_IDENTITY_REPLY_K) S0)
    by (apply (f9_stk_norm m _ _ _ REL); [lia | exact P9]).
  pose proof (mem_inv_normalize rsegs m) as MIn.
  assert (P12n : reply_args phi (fr + 256) (fr + 272) (fr + 304) = true -> 50 <= len ->
     phi + 50 <= 2 ^ 64 /\ bytes_at rsegs (normalize rsegs m) phi G /\
     (phi + 50 <= S0 - REAC_CTRL_IDENTITY_REPLY_K \/ S0 <= phi)).
  { intros Ha Hl. destruct (P12 Ha Hl) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [|exact Q3].
    exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) Q2). }
  assert (P13n : reply_args phi (fr + 256) (fr + 272) (fr + 304) = true ->
       (fr + 256) mod 2 = 0 /\ (fr + 272) mod 8 = 0 /\ (fr + 304) mod 8 = 0 /\
       rw_cells rsegs (normalize rsegs m) (fr + 256) [CB 2 ja] /\
       rw_cells rsegs (normalize rsegs m) (fr + 272) [CB 8 jp] /\
       rw_cells rsegs (normalize rsegs m) (fr + 304) [CB 8 jn] /\
       (fr + 256 + 2 <= fr + 272 \/ fr + 272 + 8 <= fr + 256) /\
       (fr + 256 + 2 <= fr + 304 \/ fr + 304 + 8 <= fr + 256) /\
       (fr + 272 + 8 <= fr + 304 \/ fr + 304 + 8 <= fr + 272) /\
       (fr + 256 + 2 <= phi \/ phi + 50 <= fr + 256) /\ (fr + 272 + 8 <= phi \/ phi + 50 <= fr + 272) /\
       (fr + 304 + 8 <= phi \/ phi + 50 <= fr + 304) /\
       (fr + 256 + 2 <= S0 - REAC_CTRL_IDENTITY_REPLY_K \/ S0 <= fr + 256) /\
       (fr + 272 + 8 <= S0 - REAC_CTRL_IDENTITY_REPLY_K \/ S0 <= fr + 272) /\
       (fr + 304 + 8 <= S0 - REAC_CTRL_IDENTITY_REPLY_K \/ S0 <= fr + 304)).
  { intros Ha. destruct (P13 Ha) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
    split; [exact (f9_rw_norm m _ (fr + 256) _ REL ltac:(lia) Q4)|].
    split; [exact (f9_rw_norm m _ (fr + 272) _ REL ltac:(lia) Q5)|].
    split; [exact (f9_rw_norm m _ (fr + 304) _ REL ltac:(lia) Q6)|].
    exact Q7. }
  pose proof (rel_ac_norm m _ REL P14) as P14n.
  pose proof (rel_sw_norm m _ REL P15) as P15n.
  pose proof (rel_addr_norm m _ _ _ REL P18) as P18n.
  assert (P19n : reply_args phi (fr + 256) (fr + 272) (fr + 304) = true -> 50 <= len ->
                 addressable (normalize rsegs m) phi 50)
    by (intros Ha Hl; exact (rel_addr_norm m _ _ _ REL (P19 Ha Hl))).
  assert (P20n : reply_args phi (fr + 256) (fr + 272) (fr + 304) = true ->
       addressable (normalize rsegs m) (fr + 256) 2 /\ addressable (normalize rsegs m) (fr + 272) 8 /\
       addressable (normalize rsegs m) (fr + 304) 8 /\
       (fr + 256 + 2 <= RT_LO \/ RT_HI <= fr + 256) /\ (fr + 272 + 8 <= RT_LO \/ RT_HI <= fr + 272) /\
       (fr + 304 + 8 <= RT_LO \/ RT_HI <= fr + 304)).
  { intros Ha. destruct (P20 Ha) as (Q1 & Q2 & Q3 & Q4).
    split; [exact (rel_addr_norm m _ _ _ REL Q1)|]. split; [exact (rel_addr_norm m _ _ _ REL Q2)|].
    split; [exact (rel_addr_norm m _ _ _ REL Q3) | exact Q4]. }
  pose proof (rel_addr_norm m _ _ _ REL P21) as P21n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) P22) as P22n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) P23) as P23n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) P24) as P24n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) P25) as P25n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) P26) as P26n.
  pose proof (proj1 (f9_fp_rel _ m _ _ _ _ _ _ _ REL) P27) as P27n.
  assert (P28n : reac_ctrl_identity_reply_tls (normalize rsegs m) TP FS (S0 - REAC_CTRL_IDENTITY_REPLY_K) S0).
  { intros DT TS C T DB k HT. apply P28. exact (proj2 (f9_tls_rel m _ _ _ _ _ _ _ _ REL) HT). }
  clear P9 P12 P13 P14 P15 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 P28.
  assert (Etp : bv_unsigned tp = TP) by (rewrite Htp; apply MState.unsigned_lit; exact HTP).
  rewrite <- Etp in P27n, P28n.
  pose proof HIR as HC. unfold reac_ctrl_identity_reply_contract, REAC_CTRL_IDENTITY_REPLY in HC.
  (* the PRE stretch: 0x81fe8 mv a0,s7 ; 0x81fec mv a1,s2 ; 0x81ff0 jal reac_ctrl_identity_reply *)
  eapply F9LE.evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    apply (f9_evtB_pre_F RNG_all ra0 sp gp tp t0 t1 t2 s0 a0 a1 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6
             Fr fc m A S3 fr phi len). }
  intros ms0 ->.
  eapply F9LE.evt_cut.
  { eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact P10 |].
    eapply HC with (fr := phi) (len := len) (pa := fr + 256) (pp := fr + 272) (pn := fr + 304) (S := S0)
      (FS := FS) (g := G) (ja := ja) (jp := jp) (jn := jn);
      first [ reflexivity | exact Hsp | assumption ]. }
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    E & MU & WM & MI & ST & HR & HAC' & HSW' & HAD' & HFP' & HTLS') & HREL & HROs).
  subst s0'.
  destruct HREL as (Er & Ef & Epc & Esvc & Erv & Efc & Erom & Hrel).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in Er, Ef, Epc, Esvc, Erv,
    Efc, Erom, Hrel.
  rewrite (f9_ms_eta ms' Esvc), Er, Ef, Epc, Erv, Efc, Erom.
  rewrite Etp in HFP', HTLS'.
  replace (ret_pc (Z_to_bv 64 532468)) with (Z_to_bv 64 532468)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  (* the POST stretch: zero instructions at the return pc 0x81ff4 *)
  apply (evtF_evt rsegs RNG_all).
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS ?R _ _ _ _ ?mm _) =>
      apply (@f9_evtB_post_F (mkFP Fr fc) RNG_all R mm Q)
  end.
  apply HK.
  - exact (munch_rel rsegs _ m (normalize rsegs m) (ms_mem ms') m0' REL Hrel HROs MU).
  - exact (wmono_rel rsegs m (normalize rsegs m) (ms_mem ms') m0' REL Hrel HROs WM).
  - exact (ro_agree_same rsegs m (ms_mem ms') P10 HROs).
  - exact (rel_stk_back _ _ _ _ Hrel ST).
  - intros Hok. destruct (HR Hok) as (R1 & R2 & R3).
    split; [exact (rel_rw_back _ _ _ _ Hrel R1)|].
    split; [exact (rel_rw_back _ _ _ _ Hrel R2) | exact (rel_rw_back _ _ _ _ Hrel R3)].
  - exact (rel_ac_back _ _ Hrel HAC').
  - exact (rel_sw_back _ _ Hrel HSW').
  - exact (rel_addr_back _ _ _ _ Hrel HAD').
  - exact (proj2 (f9_fp_rel _ _ _ _ _ _ _ _ _ Hrel) HFP').
  - intros DT TS C T DB k HT. apply HTLS'. exact (proj1 (f9_tls_rel _ _ _ _ _ _ _ _ _ Hrel) HT).
Qed.

(* The pin: f9_evtB_of_pre_post states F9.f9_evtB's v1.9 text, term for term. *)
Example f9_evtB_of_pre_post_verbatim : True.
Proof.
  let a := type of F9.f9_evtB in let b := type of f9_evtB_of_pre_post in constr_eq a b.
  exact I.
Qed.
