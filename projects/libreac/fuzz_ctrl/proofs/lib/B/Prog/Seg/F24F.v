(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source run: lib/B/Prog/Seg/F24.v (not in this delivery) f24_evt at a working branch 3803efccea0
     (blob 459ef6164a824d5c6838ac95d89284a70c117302);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f24_evt calls reac_ports_parse (jal at 0x82884), so it is split: f24_pre_F re-runs F24.v (not in this delivery)
     (0x82878 -> the callee entry 0x883d0, ra = 0x82888) and f24_post_F re-runs F24.v (not in this delivery) (the return pc
     0x82888 -> the run's end, no step), with the callee post facts as premises. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_f23.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module PPC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ports_parse_c.

(* The pre half of f24_evt: 0x82878 ld s6,312(s1) ; mv a0,s6 ; mv a1,s5 ; jal reac_ports_parse, stopping at the
   callee entry 0x883d0 with ra = 0x82888.  The only access is the spill word [A + 312, A + 320). *)
Lemma f24_pre_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A p q : Z),
    x9 = Z_to_bv 64 A -> x21 = Z_to_bv 64 q ->
    0 <= A -> A + 320 <= 2 ^ 64 -> bytes_at rsegs m (A + 312) (le8 (Z_to_bv 64 p)) ->
    rng RNG (A + 312) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82888) x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 A)
                                (Z_to_bv 64 p) (Z_to_bv 64 q) x12 x13 x14 x15 x16 x17 x18 x19 x20
                                (Z_to_bv 64 q) (Z_to_bv 64 p) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                           Fr (Z_to_bv 64 PPC.REAC_PORTS_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
               x29 x30 x31) Fr (Z_to_bv 64 0x82878) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 Fr fc m A p q -> -> HA0 HA1 H312 R312.
  pose proof (tf_rd8 m (A + 312) _ H312 (length_le8 _)) as RD312.
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* The post half of f24_evt (F24.v:156-174): from the return pc 0x82888 there is no further instruction before
   the run's exit cut, so the post is exactly what f24_evt reads out of the reac_ports_parse post, with the
   else arm's one-range munch weakened to the run's two-range write set. *)
Lemma f24_post_F :
  forall (RNG : footprint)
         (ra' x2 x3 x4 t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x23 x24 x25 x26 x27
          t3' t4' x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte)
         (p q sp lo : Z) (bs : list byte),
    bv_unsigned x2 = sp ->
    wmono rsegs m m' -> stk rsegs m' lo sp ->
    (if RcLeaf.ports_ok p q bs
     then bytes_at rsegs m' q (le4 (Z_to_bv 64 (4 * RcLeaf.n_in bs))) /\
          bytes_at rsegs m' (q + 4) (le4 (Z_to_bv 64 (4 * RcLeaf.n_out bs))) /\
          bytes_at rsegs m' (q + 8) (le4 (Z_to_bv 64 (16 * RcLeaf.bt bs 7))) /\
          munch [(sp - 16, sp); (q, q + 12)] m m'
     else munch [(sp - 16, sp)] m m') ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (pc' : word) m'',
         ms' = MS R Fr pc' fc None m'' (seg_rom rsegs) /\ pc' = Z_to_bv 64 0x82888 /\
         getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9 /\
         getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 21 = x21 /\ getr R 23 = x23 /\
         getr R 24 = x24 /\
         getr R 26 = x26 /\ getr R 27 = x27 /\ getr R 22 = Z_to_bv 64 p /\
         getr R 10 = Z_to_bv 64 (if RcLeaf.ports_ok p q bs then 0 else -1) /\
         munch [(sp - 16, sp); (q, q + 12)] m m'' /\ wmono rsegs m m'' /\ stk rsegs m'' lo sp /\
         (if RcLeaf.ports_ok p q bs
          then bytes_at rsegs m'' q (le4 (Z_to_bv 64 (4 * RcLeaf.n_in bs))) /\
               bytes_at rsegs m'' (q + 4) (le4 (Z_to_bv 64 (4 * RcLeaf.n_out bs))) /\
               bytes_at rsegs m'' (q + 8) (le4 (Z_to_bv 64 (16 * RcLeaf.bt bs 7)))
          else munch [(sp - 16, sp)] m m''))
      (MS (mkR ra' x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 (if RcLeaf.ports_ok p q bs then 0 else -1))
               a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 (Z_to_bv 64 p) x23 x24 x25 x26 x27 t3' t4' x30 x31)
          Fr (Z_to_bv 64 0x82888) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG ra' x2 x3 x4 t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x23 x24 x25 x26 x27
    t3' t4' x30 x31 Fr fc m m' p q sp lo bs Hsp WM' ST' HIF.
  apply evtF_done. cbv beta.
  revert HIF. destruct (RcLeaf.ports_ok p q bs); intros HIF.
  - destruct HIF as (B0 & B1 & B2 & MU').
    do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    do 15 (split; [first [reflexivity | simp_regs; reflexivity]|]).
    split; [exact MU'|]. split; [exact WM'|]. split; [exact ST'|].
    split; [exact B0|]. split; [exact B1 | exact B2].
  - do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    do 15 (split; [first [reflexivity | simp_regs; reflexivity]|]).
    split.
    { eapply munch_weaken; [|exact HIF]. intros x Hx. cbn [outside] in Hx |- *. tauto. }
    split; [exact WM'|]. split; [exact ST' | exact HIF].
Qed.
