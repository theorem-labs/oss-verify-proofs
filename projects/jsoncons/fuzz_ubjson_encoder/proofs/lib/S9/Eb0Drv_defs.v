(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DrvKitA Eb0DrvEntry.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Definition STOPSA : list Z := [0x7a9c4; 0x7a9c0; 0x78e3c; 0x6453c; 0x64540; 0x64558; 0x64568; 0x11eba4; 0xa9150].
Definition FUELA : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Section FPX_1. Context {fx : PropExec.FPState}.
Definition runA (scr : scripts) (ss : sym_state) := sym_exec ASEGS FUELA true STOPSA scr ss [].
End FPX_1.
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition IMG_CLIENT_A : list (Z * Z) :=
  [(0x10000, 0x13f000); (0x141fe8, 0x142a10); (0x668750, 0x67a128); (0x67a130, 0x67a178); (0x67a194, 0x67a1a8); (0x67a1b0, 0x69b638);
   (0x69b640, 0x69c000)].

Definition IMG_W_A : list (Z * Z) :=
  [(0x1420d0, 0x1423c8); (0x668750, 0x67a128); (0x67a130, 0x67a178); (0x67a194, 0x67a1a8); (0x67a1b0, 0x69b638); (0x69b640, 0x69c000)].
Lemma img_client_rng : forall lo hi, In (lo, hi) IMG_CLIENT_A -> 0x10000 <= lo /\ hi <= 0x69c000 /\ lo <= hi.
Proof. intros lo hi Hin. unfold IMG_CLIENT_A in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. Qed.
Lemma img_w_sub : forall lo hi, In (lo, hi) IMG_W_A -> exists lo' hi', In (lo', hi') IMG_CLIENT_A /\ lo' <= lo /\ hi <= hi'.
Proof.
  intros lo hi Hin. unfold IMG_W_A in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-;
    [exists 0x141fe8, 0x142a10 | exists 0x668750, 0x67a128 | exists 0x67a130, 0x67a178 | exists 0x67a194, 0x67a1a8
     | exists 0x67a1b0, 0x69b638 | exists 0x69b640, 0x69c000];
    (split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia]).
Qed.

Definition IMG_RW_A : list (Z * Z) := [(0x668750, 0x678750)].

Definition keep_allocA (so sc : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so sc bls vbnd [] IMG_CLIENT_A IMG_RW_A kn.

Definition MSO : Z := -128.

Definition kn_blkA (v : nat) (n : Z) : list kentry :=
  [KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
   KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) 0x10000) 0x68c000 (SA (EVar v) 0) n].

Lemma asegs_wx : wx_segs_nowrap ASEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Section FPX_2. Context {fx : PropExec.FPState}.

Definition ssA0 : sym_state := SS 0xa8cb0 sr_mainA [] kn_mainA NX_MAIN.
Definition rA := Eval vm_compute in runA scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_mainA.

Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0x130c0c srB0 [] knA NX_MAIN.
Definition rB := Eval vm_compute in runA scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

Definition keepB : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] knB.
Definition knC0 : list kentry := Eval vm_compute in kn_blkA 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

Definition sumA (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
End FPX_2.
