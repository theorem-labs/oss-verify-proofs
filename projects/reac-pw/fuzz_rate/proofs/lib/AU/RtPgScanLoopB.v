(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanLoop.v at 45269e15197c for reac-pw/fuzz_rate:
   the cut file is lib/A/RtPgSeg.v, the model facts lib/A/RtPgScanF.v, and the key match's fourth exit is the asked
   set-up A (rs_from_A) where role's was its tail T. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgScanLoop.v at fa28558fbb17 for image B
   (fuzz_rate.asan-ubsan): the cut file is lib/AU/RtPgSegB.v (rs_ -> rsb_), the model facts lib/AU/RtPgScanFB.v
   (rk_ -> rkb_); the closure itself is image A's. *)
(* reac-pw/fuzz_rate, the image-B walk of LLVMFuzzerTestOneInput: THE CLOSURE OF THE TWO SCAN LOOPS of M02, the
   checking segment. Proves no function (kind: invariant lemma): it holds no instruction and no address; it turns the
   three one-step piece statements of lib/AU/RtPgSegB.v into the continuation of every index.

   WHY A CLOSURE IS NEEDED, AND WHY IT IS AN INDUCTION AND NOT A CIRCLE. The inlined expect_rate (fuzz_rate.c:70)
   runs pod_next_pair (pod.h:124-145) until it finds a pair whose key is the rate key. Its control flow is two nested
   loops that pass through each other:
     the outer head O gives the inner scan I at the same index (rsb_piece_W11a_outer_stmt),
     one turn of the inner loop I at m gives I at m + 1 or the key match KM at m (rsb_piece_W11a_inner_stmt),
     the key match, when the key is not the rate key, goes back to the outer head at m + 2
       (rsb_piece_W11b_key_stmt, whose premise is the continuation of O at S (S m)).
   Each of the three is a one-step statement that takes the continuations of the cuts it jumps to, so none of them
   can be closed alone. Taken together they would be circular; they are not, because every step moves the index UP:
   I at m asks I at m + 1 and, through KM at m, O at m + 2, which asks I at m + 2. So the closure is an induction on
   how far the index still is from its bound. (Image B's inner loop is rotated, so its cut I is one instruction after
   the loop's head; the three statements and so the closure are the same as image A's.)

   THE BOUND IS 32, AND IT IS THE MODEL'S. A cut of the inner loop asks `(at0 <= m < length (ents rec))%nat`
   (RtPgSegB.rsb_cut_I) and carries `pod_rec_wf rec` (RtPgSegB.rsb_chk_base); the record the builder makes holds at
   most 32 entries (Model.ents_wf, restated as RtPgScanFB.rkb_nent_le, which is POD_ENT_MAX of pod.h). So the
   continuation of the inner loop at any index 32 or above is VACUOUS - no state satisfies its cut - and the
   induction has a base. The induction itself is on a fuel d with `32 <= m + d`, which is a downward induction on
   the index written so that it needs no well-founded recursion.

   WHAT THIS FILE GIVES THE ASSEMBLY. rkb_I_all: the continuation of the inner scan at every (at0, m). rkb_O_all:
   the continuation of the outer head at every index, which is what the set-up piece (rsb_piece_W11a_setup_stmt, at
   index 0) and the key match ask for. Everything else about M02 is proved in the files that state those pieces; this
   one only closes the loops. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSegB RtPgScanFB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ONE run of the checking segment, and the pieces that are not this file's *)
Variable cx : rsb_scx segs.
Variable POST : world segs -> config -> Prop.
Variable inp : list byte.
Hypothesis HSTART : rsb_start_M02 segs B cx inp.
Hypothesis HABS : rsb_from_ABS segs B MT cx POST.
Hypothesis HMAL : rsb_from_MAL segs B MT cx POST.
Hypothesis HA : rsb_from_A segs B MT cx POST.
Hypothesis HOUT : rsb_piece_W11a_outer_stmt segs B MT.
Hypothesis HINN : rsb_piece_W11a_inner_stmt segs B MT.
Hypothesis HKEY : rsb_piece_W11b_key_stmt segs B MT.

(* The record has at most 32 entries, so the inner scan's cut is unsatisfiable from index 32 on and its continuation
   holds for nothing to do. *)
Lemma rkb_I_vac : forall at0 m, (32 <= m)%nat -> rsb_from_I segs B MT cx POST at0 m.
Proof.
intros at0 m Hm fx2 ly2 S2 W2 regs2 mem2 md2 rec HI.
destruct HI as (HB & _ & _ & _ & _ & Hrng & _).
destruct HB as (_ & _ & _ & _ & _ & Hwf & _).
pose proof (rkb_nent_le rec Hwf) as Hle.
exfalso. lia.
Qed.

(* The induction: with d steps of room left below the bound, the inner scan's continuation holds. One step uses the
   inner turn (which asks the next index), the key match (which asks the outer head two indices up) and the outer
   head (which asks the inner scan at that index); all three indices are strictly above m, so the same fuel d - 1
   covers them. *)
Lemma rkb_I_fuel : forall d at0 m, (32 <= m + d)%nat -> rsb_from_I segs B MT cx POST at0 m.
Proof.
induction d as [|d IH]; intros at0 m Hd.
- apply rkb_I_vac. lia.
- destruct (Compare_dec.le_lt_dec 32 m) as [Hge|Hlt]; [apply rkb_I_vac; exact Hge|].
  apply (HINN cx POST inp at0 m HSTART).
  + apply (IH at0 (S m)). lia.
  + apply (HKEY cx POST inp at0 m HSTART).
    * apply (HOUT cx POST inp (S (S m)) HSTART).
      -- apply (IH (S (S m)) (S (S m))). lia.
      -- exact HABS.
    * exact HABS.
    * exact HMAL.
    * exact HA.
  + exact HABS.
Qed.

(* the two closures the assembly uses *)
Theorem rkb_I_all : forall at0 m, rsb_from_I segs B MT cx POST at0 m.
Proof. intros at0 m. apply (rkb_I_fuel 32). lia. Qed.

Theorem rkb_O_all : forall j, rsb_from_O segs B MT cx POST j.
Proof.
intros j. apply (HOUT cx POST inp j HSTART); [apply rkb_I_all | exact HABS].
Qed.

End d.
End c.
End b.

Print Assumptions rkb_I_all.
Print Assumptions rkb_O_all.
