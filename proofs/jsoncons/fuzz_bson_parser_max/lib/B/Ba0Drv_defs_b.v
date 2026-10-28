(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Definition STOPSA : list Z := [0x79818; 0x79814; 0x77c90; 0x63390; 0x63394; 0x633ac; 0x633bc; 0x118878; 0xa7fa4].
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
  [(0x10000, 0x139000); (0x13bbe0, 0x13c580); (0x662290, 0x673ca8); (0x673cb0, 0x673cf8); (0x673d14, 0x673d28); (0x673d30, 0x6951b8);
   (0x6951c0, 0x696000)].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_W_A : list (Z * Z) :=
  [(0x13bcc8, 0x13bfc0); (0x662290, 0x673ca8); (0x673cb0, 0x673cf8); (0x673d14, 0x673d28); (0x673d30, 0x6951b8); (0x6951c0, 0x696000)].
Lemma img_client_rng : forall lo hi, In (lo, hi) IMG_CLIENT_A -> 0x10000 <= lo /\ hi <= 0x696000 /\ lo <= hi.
Proof. intros lo hi Hin. unfold IMG_CLIENT_A in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. Qed.
Lemma img_w_sub : forall lo hi, In (lo, hi) IMG_W_A -> exists lo' hi', In (lo', hi') IMG_CLIENT_A /\ lo' <= lo /\ hi <= hi'.
Proof.
  intros lo hi Hin. unfold IMG_W_A in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-;
    [exists 0x13bbe0, 0x13c580 | exists 0x662290, 0x673ca8 | exists 0x673cb0, 0x673cf8 | exists 0x673d14, 0x673d28
     | exists 0x673d30, 0x6951b8 | exists 0x6951c0, 0x696000];
    (split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia]).
Qed.
(* [comment removed for export] *)
Definition IMG_RW_A : list (Z * Z) := [(0x662290, 0x672290)].
(* [comment removed for export] *)
Definition keep_allocA (so sc : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so sc bls vbnd [] IMG_CLIENT_A IMG_RW_A kn.
(* [comment removed for export] *)
Definition MSO : Z := -128.
(* [comment removed for export] *)
Definition kn_blkA (v : nat) (n : Z) : list kentry :=
  [KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
   KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) 0x10000) 0x686000 (SA (EVar v) 0) n].

Lemma asegs_wx : wx_segs_nowrap ASEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Section FPX_2. Context {fx : PropExec.FPState}.
(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0xa7b04 sr_mainA [] kn_mainA NX_MAIN.
Definition rA := Eval vm_compute in runA scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_mainA.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0x12a8dc srB0 [] knA NX_MAIN.
Definition rB := Eval vm_compute in runA scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

(* [comment removed for export] *)
Definition keepB : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] knB.
Definition knC0 : list kentry := Eval vm_compute in kn_blkA 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

Definition sumA (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
End FPX_2.
