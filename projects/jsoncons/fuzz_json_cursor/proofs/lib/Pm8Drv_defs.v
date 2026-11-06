(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DrvKitA Pm8DrvEntry.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Definition STOPSA : list Z := [0x809f8; 0x809f4; 0x7ee70; 0x6a570; 0x6a574; 0x6a58c; 0x6a59c; 0x133e78; 0xaf184].
Definition FUELA : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Section FPX_1. Context {fx : PropExec.FPState}.
Definition runA (scr : scripts) (ss : sym_state) := sym_exec ASEGS FUELA true STOPSA scr ss [].
End FPX_1.
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition IMG_CLIENT_A : list (Z * Z) :=
  [(0x10000, 0x154000); (0x157870, 0x159300); (0x67f010, 0x6909f8); (0x690a00, 0x690a48); (0x690a64, 0x690a78); (0x690a80, 0x6b1f08);
   (0x6b1f10, 0x6b3000)].

Definition IMG_W_A : list (Z * Z) :=
  [(0x157960, 0x157c60); (0x67f010, 0x6909f8); (0x690a00, 0x690a48); (0x690a64, 0x690a78); (0x690a80, 0x6b1f08); (0x6b1f10, 0x6b3000)].
Lemma img_client_rng : forall lo hi, In (lo, hi) IMG_CLIENT_A -> 0x10000 <= lo /\ hi <= 0x6b3000 /\ lo <= hi.
Proof. intros lo hi Hin. unfold IMG_CLIENT_A in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. Qed.
Lemma img_w_sub : forall lo hi, In (lo, hi) IMG_W_A -> exists lo' hi', In (lo', hi') IMG_CLIENT_A /\ lo' <= lo /\ hi <= hi'.
Proof.
  intros lo hi Hin. unfold IMG_W_A in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-;
    [exists 0x157870, 0x159300 | exists 0x67f010, 0x6909f8 | exists 0x690a00, 0x690a48 | exists 0x690a64, 0x690a78
     | exists 0x690a80, 0x6b1f08 | exists 0x6b1f10, 0x6b3000];
    (split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia]).
Qed.

Definition IMG_RW_A : list (Z * Z) := [(0x67f010, 0x68f010)].

Definition keep_allocA (so sc : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so sc bls vbnd [] IMG_CLIENT_A IMG_RW_A kn.

Definition MSO : Z := -128.

Definition kn_blkA (v : nat) (n : Z) : list kentry :=
  [KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
   KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) 0x10000) 0x6a3000 (SA (EVar v) 0) n].

Lemma asegs_wx : wx_segs_nowrap ASEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Section FPX_2. Context {fx : PropExec.FPState}.

Definition ssA0 : sym_state := SS 0xaece4 sr_mainA [] kn_mainA NX_MAIN.
Definition rA := Eval vm_compute in runA scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_mainA.

Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0x145ee0 srB0 [] knA NX_MAIN.
Definition rB := Eval vm_compute in runA scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

Definition keepB : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] knB.
Definition knC0 : list kentry := Eval vm_compute in kn_blkA 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

Definition sumA (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
End FPX_2.
