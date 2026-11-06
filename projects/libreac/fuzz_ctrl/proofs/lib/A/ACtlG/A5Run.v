(* lib/A/ACtlG/A5Run.v -- the _F run of segment A5 of fuzz_ctrl image A, PROVED: seg_A5_run_F_ok is the Section
   hypothesis seg_A5_run_F of lib/A/ACtlG/A5.v (A5.v:129-152 (an earlier version, blob 6fe66e3de56, not in this delivery); from a working branch 8b0ff2e4e96),
   its statement copied character for character from A5.v:130-152.  rule 24: no function proved (one
   register-only run of a walk segment).  Written by a Theorem Labs lane (brief
   a5run.md (a working note, not in this delivery)).

   THE RUN: segment A5 is 0x81400 -> 0x81414, five register-only instructions (A5.v:9-10):
     0x81400 mv s6,s7   0x81404 add a4,a4,a1   0x81408 addi a1,a1,1   0x8140c mv a0,a4   0x81410 mv s9,s8.
   It reads and writes no memory, so it holds under every footprint RNG.

   ROUTE (brief route 1, re-step): the proof of lib/A/Prog/Seg/Tac_slotF.v's seg_A5_run_F (blob c8a22596a05, lines
   53-58: unfold mkR_of, `do 5 step`, `finish`) at this image's addresses (0x81400, not Tac_slotF's 0x813a8), with
   a5_evt_F's arithmetic (lib/A/Prog/Seg/A5F.v:69-73 on the integ branch) for registers 10 / 11 / 14: the premises
   R11 = t and R14 = ou are rewritten into the start map first, as a5_evt_F substitutes a1 and a4.

   IMPORTS: every Require is qualified.  The stepping needs the StepF tactics (step, finish, simp_regs and the
   Lib.Tac redefinitions of the concrete-map tests), so Section R Imports Lib.StepF (the only Import of a project
   module, made inside the Section after the lemma's Context; the statement names no short name it brings in: its
   project names are the qualified ones of A5.v).  A.ACtlG.A5 is Required only for the Check after the Section,
   which applies A5.v's glue_seg_A5 to this lemma. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require A5.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF Regs6ss StepF.
Import ListNotations.
Local Open Scope Z_scope.

Section R.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}.

(* The StepF tactics, for this Section only (header, IMPORTS); Z_scope back on top, as A5.v has it. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.
Local Open Scope Z_scope.

Lemma seg_A5_run_F_ok :
  forall (RNG : Lib.ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte) (ou t : Z),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 11 = Z_to_bv 64 t -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 14 = Z_to_bv 64 ou ->
  0 <= t -> 0 <= ou -> ou + t + 1 < 2 ^ 64 ->
  Lib.ExecF.evtF A.Img0.rsegs RNG
    (fun ms => exists R pc' mem',
       ms = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS R OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs pc' OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem'
              (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs) /\
       (pc' = Z_to_bv 64 0x81414 /\ mem' = mem /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 2 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 2 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 3 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 3 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 4 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 4 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 8 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 8 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 19 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 19 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 26 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 26 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 1 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 1 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 7 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 7 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 12 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 12 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 13 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 13 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 18 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 18 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 21 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 21 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 27 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 27 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 28 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 28 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 29 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 29 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 30 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 30 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 31 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 31 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 22 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 23 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 25 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 24 /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 10 = Z_to_bv 64 (ou + t) /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 11 = Z_to_bv 64 (t + 1) /\
        OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 14 = Z_to_bv 64 (ou + t)))
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS (Lib.Regs6ss.mkR_of regs) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x81400) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem
       (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs)).
Proof.
  intros RNG regs mem ou t H11 H14 Ht Hou Hb.
  (* The start map: mkR_of's 31 reads, with a1 (x11) and a4 (x14) replaced by the premises' values. *)
  unfold Lib.Regs6ss.mkR_of.
  lazymatch goal with
  | |- context [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.mkR _ _ _ _ _ _ _ _ _ _ ?x11 _ _ ?x14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] =>
      assert (E11 : x11 = Z_to_bv 64 t) by exact H11;
      assert (E14 : x14 = Z_to_bv 64 ou) by exact H14;
      rewrite E11, E14; clear E11 E14
  end.
  (* The five instructions, then the post (StepF.finish instantiates R, pc' and mem' from the end state). *)
  do 5 step. finish.
  (* pc' and mem', and every register the run keeps (getr of the end map reduces to the start map's read). *)
  all: try reflexivity.
  (* Registers 10, 11 and 14: the run's sums, under 0 <= t, 0 <= ou and ou + t + 1 < 2 ^ 64. *)
  all: unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr;
    repeat match goal with
    | |- context [bv_eqb ?a ?b] => let v := eval vm_compute in (bv_eqb a b) in change (bv_eqb a b) with v
    end;
    cbv beta iota; simp_regs;
    rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia;
    first [ reflexivity | f_equal; lia
          | apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
            rewrite ?Z.mod_small by lia; lia ].
Qed.

End R.

Print Assumptions seg_A5_run_F_ok.

(* The statement fits: A5.v's glue_seg_A5 takes this lemma for its Section hypothesis seg_A5_run_F.  Its implicit
   arguments, as About prints them: {fx rc} B MT XM_LIB RLO RHI seg_A5_run_F LAWS (A5.v's Context LS is unused). *)
Check (fun fx rc B MT XM RLO RHI LAWS =>
  @A.ACtlG.A5.glue_seg_A5 fx rc B MT XM RLO RHI (@seg_A5_run_F_ok fx) LAWS).
