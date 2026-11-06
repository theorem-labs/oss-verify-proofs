(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanLoop.v at 45269e15197c for image B
   (fuzz_role.asan-ubsan): the cut file is lib/AU/RPgSeg.v and the model facts lib/AU/RPgScanF.v instead of
   lib/A's; the closure itself is image A's. *)
(* reac-pw/fuzz_role, the image-B walk of LLVMFuzzerTestOneInput: THE CLOSURE OF THE TWO SCAN LOOPS of M02, the
   checking segment. Proves no function (kind: invariant lemma): it holds no instruction and no address; it turns
   the three one-step piece statements of lib/AU/RPgSeg.v into the continuation of every index.

   WHY A CLOSURE IS NEEDED, AND WHY IT IS AN INDUCTION AND NOT A CIRCLE. The inlined expect_role
   (fuzz_role.c:47) runs pod_next_pair (pod.h:124-145) until it finds a pair whose key is the role key. Its
   control flow is two nested loops that pass through each other:
     the outer head O gives the inner head I at the same index (rs_piece_W11a_outer_stmt),
     one turn of the inner loop I at m gives I at m + 1 or the key match KM at m (rs_piece_W11a_inner_stmt),
     the key match, when the key is not the role key, goes back to the outer head at m + 2
       (rs_piece_W11b_key_stmt, whose premise is the continuation of O at S (S m)).
   Each of the three is a one-step statement that takes the continuations of the cuts it jumps to, so none of
   them can be closed alone. Taken together they would be circular; they are not, because every step moves the
   index UP: I at m asks I at m + 1 and, through KM at m, O at m + 2, which asks I at m + 2. So the closure is
   an induction on how far the index still is from its bound.

   THE BOUND IS 32, AND IT IS THE MODEL'S. A cut of the inner loop asks `(at0 <= m < length (ents rec))%nat`
   (RPgSeg.rs_cut_I) and carries `pod_rec_wf rec` (RPgSeg.rs_chk_base); the record the builder makes holds at
   most 32 entries (Model.ents_wf, restated as RPgScanF.rk_nent_le, which is POD_ENT_MAX of pod.h:67). So the
   continuation of the inner loop at any index 32 or above is VACUOUS - no state satisfies its cut - and the
   induction has a base. The induction itself is on a fuel d with `32 <= m + d`, which is a downward induction
   on the index written so that it needs no well-founded recursion.

   WHAT THIS FILE GIVES THE ASSEMBLY. rk_I_all: the continuation of the inner head at every (at0, m).
   rk_O_all: the continuation of the outer head at every index, which is what the set-up piece
   (rs_piece_W11a_setup_stmt, at index 0) and the key match ask for. Everything else about M02 - the head, the
   set-up, the two loop bodies, the key match, the two checks and the tail - is proved in the files that state
   those pieces; this one only closes the loops. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa Role Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA RPgSeg RPgScanF.
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
Variable cx : rs_scx segs.
Variable POST : world segs -> config -> Prop.
Variable inp : list byte.
Hypothesis HSTART : rs_start_M02 segs B cx inp.
Hypothesis HABS : rs_from_ABS segs B MT cx POST.
Hypothesis HMAL : rs_from_MAL segs B MT cx POST.
Hypothesis HT : rs_from_T segs B MT cx POST.
Hypothesis HOUT : rs_piece_W11a_outer_stmt segs B MT.
Hypothesis HINN : rs_piece_W11a_inner_stmt segs B MT.
Hypothesis HKEY : rs_piece_W11b_key_stmt segs B MT.

(* The record has at most 32 entries, so the inner head's cut is unsatisfiable from index 32 on and its
   continuation holds for nothing to do. *)
Lemma rk_I_vac : forall at0 m, (32 <= m)%nat -> rs_from_I segs B MT cx POST at0 m.
Proof.
intros at0 m Hm fx2 ly2 S2 W2 regs2 mem2 md2 rec HI.
destruct HI as (HB & _ & _ & _ & _ & Hrng & _).
destruct HB as (_ & _ & _ & _ & _ & Hwf & _).
pose proof (rk_nent_le rec Hwf) as Hle.
exfalso. lia.
Qed.

(* The induction: with d steps of room left below the bound, the inner head's continuation holds. One step uses
   the inner turn (which asks the next index), the key match (which asks the outer head two indices up) and the
   outer head (which asks the inner head at that index); all three indices are strictly above m, so the same
   fuel d - 1 covers them. *)
Lemma rk_I_fuel : forall d at0 m, (32 <= m + d)%nat -> rs_from_I segs B MT cx POST at0 m.
Proof.
induction d as [|d IH]; intros at0 m Hd.
- apply rk_I_vac. lia.
- destruct (Compare_dec.le_lt_dec 32 m) as [Hge|Hlt]; [apply rk_I_vac; exact Hge|].
  apply (HINN cx POST inp at0 m HSTART).
  + apply (IH at0 (S m)). lia.
  + apply (HKEY cx POST inp at0 m HSTART).
    * apply (HOUT cx POST inp (S (S m)) HSTART).
      -- apply (IH (S (S m)) (S (S m))). lia.
      -- exact HABS.
    * exact HABS.
    * exact HMAL.
    * exact HT.
  + exact HABS.
Qed.

(* the two closures the assembly uses *)
Theorem rk_I_all : forall at0 m, rs_from_I segs B MT cx POST at0 m.
Proof. intros at0 m. apply (rk_I_fuel 32). lia. Qed.

Theorem rk_O_all : forall j, rs_from_O segs B MT cx POST j.
Proof.
intros j. apply (HOUT cx POST inp j HSTART); [apply rk_I_all | exact HABS].
Qed.

End d.
End c.
End b.
