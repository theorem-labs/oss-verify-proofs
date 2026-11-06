(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Pm10MainEntry Pm10LibStdioCall DrvKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Section FPX_1. Context {fx : PropExec.FPState}.

Definition STOPS : list Z :=
  [0xb5a40; 0xb5fc0; 0xb6534; 0xb5944; 0xa53ac; 0xaa5b0; 0xa7390; 0xa7250; 0x393fc; 0x393b4]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition kn_image_d : list kentry :=
  [KWr (SA (ELit 0) 0xc2000) 0x34000;
   KImg 0x10000 0xc2f20;
   KImg 0xc2f21 0xc2f69; KImg 0xd2f69 0xd48e0; KImg 0xf49b8 0xf49d8;
   KWord (SA (ELit 0) 0xd48e8) 8 (ELit 0xd48e8);
   KWord (SA (ELit 0) 0xd4908) 4 (EVar 5);
   KImg 0xd4914 0xd4960; KImg 0xd4968 0xd4980; KWord (SA (ELit 0) 0xd4980) 8 (ELit 0xf4c78); KImg 0xd4988 0xd49a0;
   KBlob (SA (ELit 0) 0xd49a0) (ELit 8) 2;
   KImg 0xd49b0 0xd49c0; KImg 0xd49c8 0xf49b8; KImg 0xf49f0 0xf4c20;
   KBlob (SA (ELit 0) 0xf4c20) (ELit 8) 2;
   KImg 0xf4c28 0xf4c30;
   KImg 0xf4c41 0xf4c48; KWord (SA (ELit 0) 0xf4c48) 8 (EVar 3);
   KImg 0xf4c50 0xf4c58; KImg 0xf4c68 0xf4c70; KWord (SA (ELit 0) 0xf4c70) 8 (ELit 4096);
   KImg 0xf4c78 0xf4ca8; KBlob (SA (ELit 0) 0xf4ca8) (ELit 8) 3; KImg 0xf4cb0 0xf4db8  ; KImg 0xf5160 0xf6000;
   KRange (EVar 5) 1 4194303;
   KImg 0 0x1000].
Definition kn_d0 : list kentry := kn_stack ++ kn_auxv ++ kn_image_d.

Lemma kn_d0_sub : ksubl_b kn_main kn_d0 = true.
Proof. vmc_refl. Qed.

Definition ssA0 : sym_state := SS 0x38f5c sr_main [] kn_d0 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_d0.

Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0xb69ec srB0 [] knA 38.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

Definition IMG_CLIENT : list (Z * Z) := [(0x10000, 0xd490c); (0xd4910, 0xf4db8); (0xf5160, 0xf6000)]%Z.

Definition IMG_RW : list (Z * Z) := [(0xbb000, 0xc2000); (0xc2000, 0xf6000)]%Z.

Definition keep_alloc (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW kn.

Definition MSO : Z := -128.
Definition keepB : list kentry := Eval vm_compute in keep_alloc MSO [] [] knB.

Definition kn_blk (v : nat) (n : Z) : list kentry :=
  [KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
   KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) 0x10000) 0xe6000 (SA (EVar v) 0) n].
Definition knC0 : list kentry := Eval vm_compute in kn_blk 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

Lemma drv_itinerary_ok :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xb69e8%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB), s_log (fst (fst rB))) = (0xa7390%Z, [], [])
  /\ (nth 10 srB (ELit 0), nth 21 srB (ELit 0), nth 20 srB (ELit 0), nth 18 srB (ELit 0), nth 2 srB (ELit 0))
     = (ELit 65536, ELit 65536, ELit 3, EVar 2, EAlu ALU_ADD (EVar 0) (ELit MSO)).
Proof. vm_compute. repeat split; reflexivity. Qed.

End FPX_1.
