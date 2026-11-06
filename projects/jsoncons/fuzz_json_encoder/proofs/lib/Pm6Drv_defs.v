(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Pm6MainEntry Pm6LibStdioCall DrvKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition STOPS : list Z :=
  [0xba65c; 0xbabdc; 0xbb150; 0xba560; 0xa9fc8; 0xaf1cc; 0xabfac; 0xabe6c; 0x39d90; 0x39d48]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition kn_image_d : list kentry :=
  [KWr (SA (ELit 0) 0xc7000) 0x34000;
   KImg 0x10000 0xc7b48;
   KImg 0xc7b51 0xc7b99; KImg 0xd7b99 0xd9550; KImg 0xf9628 0xf9648;
   KWord (SA (ELit 0) 0xd9558) 8 (ELit 0xd9558);
   KWord (SA (ELit 0) 0xd9578) 4 (EVar 5);
   KImg 0xd9584 0xd95d0; KImg 0xd95d8 0xd95f0; KWord (SA (ELit 0) 0xd95f0) 8 (ELit 0xf98e8); KImg 0xd95f8 0xd9610;
   KBlob (SA (ELit 0) 0xd9610) (ELit 8) 2;
   KImg 0xd9620 0xd9630; KImg 0xd9638 0xf9628; KImg 0xf9660 0xf9890;
   KBlob (SA (ELit 0) 0xf9890) (ELit 8) 2;
   KImg 0xf9898 0xf98a0;
   KImg 0xf98b1 0xf98b8; KWord (SA (ELit 0) 0xf98b8) 8 (EVar 3);
   KImg 0xf98c0 0xf98c8; KImg 0xf98d8 0xf98e0; KWord (SA (ELit 0) 0xf98e0) 8 (ELit 4096);
   KImg 0xf98e8 0xf9918; KBlob (SA (ELit 0) 0xf9918) (ELit 8) 3; KImg 0xf9920 0xf9a28 (* [comment removed for export] *); KImg 0xf9dd0 0xfb000;
   KRange (EVar 5) 1 4194303;
   KImg 0 0x1000].
Definition kn_d0 : list kentry := kn_stack ++ kn_auxv ++ kn_image_d.

Lemma kn_d0_sub : ksubl_b kn_main kn_d0 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x398f0 sr_main [] kn_d0 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_d0.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0xbb608 srB0 [] knA 38.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_CLIENT : list (Z * Z) := [(0x10000, 0xd957c); (0xd9580, 0xf9a28); (0xf9dd0, 0xfb000)]%Z.
(* [comment removed for export] *)
Definition IMG_RW : list (Z * Z) := [(0xc0000, 0xc7000); (0xc7000, 0xfb000)]%Z.
(* [comment removed for export] *)
Definition keep_alloc (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW kn.
(* [comment removed for export] *)
Definition MSO : Z := -128.
Definition keepB : list kentry := Eval vm_compute in keep_alloc MSO [] [] knB.
(* [comment removed for export] *)
Definition kn_blk (v : nat) (n : Z) : list kentry :=
  [KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
   KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) 0x10000) 0xeb000 (SA (EVar v) 0) n].
Definition knC0 : list kentry := Eval vm_compute in kn_blk 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

(* [comment removed for export] *)
Lemma drv_itinerary_ok :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xbb604%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB), s_log (fst (fst rB))) = (0xabfac%Z, [], [])
  /\ (nth 10 srB (ELit 0), nth 21 srB (ELit 0), nth 20 srB (ELit 0), nth 18 srB (ELit 0), nth 2 srB (ELit 0))
     = (ELit 65536, ELit 65536, ELit 3, EVar 2, EAlu ALU_ADD (EVar 0) (ELit MSO)).
Proof. vm_compute. repeat split; reflexivity. Qed.

End FPX_1.
