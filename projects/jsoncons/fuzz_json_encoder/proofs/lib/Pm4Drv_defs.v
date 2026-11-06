(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DrvKitA Pm4DrvEntry.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Definition STOPSA : list Z := [0x81dc4; 0x81dc0; 0x8023c; 0x6b93c; 0x6b940; 0x6b958; 0x6b968; 0x141a14; 0xb0550].
Definition FUELA : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Section FPX_1. Context {fx : PropExec.FPState}.
Definition runA (scr : scripts) (ss : sym_state) := sym_exec ASEGS FUELA true STOPSA scr ss [].
End FPX_1.
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition IMG_CLIENT_A : list (Z * Z) :=
  [(0x10000, 0x162000); (0x165360, 0x166840); (0x68c550, 0x69df78); (0x69df80, 0x69dfc8); (0x69dfe4, 0x69dff8); (0x69e000, 0x6bf488);
   (0x6bf490, 0x6c0000)].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_W_A : list (Z * Z) :=
  [(0x165448, 0x165740); (0x68c550, 0x69df78); (0x69df80, 0x69dfc8); (0x69dfe4, 0x69dff8); (0x69e000, 0x6bf488); (0x6bf490, 0x6c0000)].
Lemma img_client_rng : forall lo hi, In (lo, hi) IMG_CLIENT_A -> 0x10000 <= lo /\ hi <= 0x6c0000 /\ lo <= hi.
Proof. intros lo hi Hin. unfold IMG_CLIENT_A in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. Qed.
Lemma img_w_sub : forall lo hi, In (lo, hi) IMG_W_A -> exists lo' hi', In (lo', hi') IMG_CLIENT_A /\ lo' <= lo /\ hi <= hi'.
Proof.
  intros lo hi Hin. unfold IMG_W_A in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-;
    [exists 0x165360, 0x166840 | exists 0x68c550, 0x69df78 | exists 0x69df80, 0x69dfc8 | exists 0x69dfe4, 0x69dff8
     | exists 0x69e000, 0x6bf488 | exists 0x6bf490, 0x6c0000];
    (split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia]).
Qed.
(* [comment removed for export] *)
Definition IMG_RW_A : list (Z * Z) := [(0x68c550, 0x69c550)].
(* [comment removed for export] *)
Definition keep_allocA (so sc : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so sc bls vbnd [] IMG_CLIENT_A IMG_RW_A kn.
(* [comment removed for export] *)
Definition MSO : Z := -128.
(* [comment removed for export] *)
Definition kn_blkA (v : nat) (n : Z) : list kentry :=
  [KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
   KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) 0x10000) 0x6b0000 (SA (EVar v) 0) n].

Lemma asegs_wx : wx_segs_nowrap ASEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Section FPX_2. Context {fx : PropExec.FPState}.
(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0xb00b0 sr_mainA [] kn_mainA NX_MAIN.
Definition rA := Eval vm_compute in runA scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_mainA.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0x153a7c srB0 [] knA NX_MAIN.
Definition rB := Eval vm_compute in runA scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

(* [comment removed for export] *)
Definition keepB : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] knB.
Definition knC0 : list kentry := Eval vm_compute in kn_blkA 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

Definition sumA (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
End FPX_2.
