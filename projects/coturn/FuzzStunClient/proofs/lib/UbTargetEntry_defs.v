(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec3 SymPlan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import ItabFast ItabS_ub.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations. Import SX2. Import SP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ITAB : itab := itab_of_string ITAB_UB_S TEXT_LO ITAB_UB_N.

Definition NX0 : N := 46%N.   (* [comment removed for export] *)
Definition sr_T : list expr :=
  [ELit 0;
   ELit 0x13c34;
   EAlu ALU_ADD (EVar 0) (ELit (-128));
   ELit 0x10800;
   ELit 0x36c60;
   EVar 17;
   EVar 18;
   EVar 19;
   EAlu ALU_ADD (EVar 1) (ELit 34);
   EAlu ALU_ADD (EVar 1) (ELit 32);
   EAlu ALU_ADD (EVar 1) (ELit 34);
   EVar 5;
   EAlu ALU_ADD (EAlu ALU_ADD (EVar 1) (EVar 5)) (ELit 38);
   EVar 4;
   EVar 26;
   EVar 27;
   EVar 28;
   EVar 29;
   EVar 5;
   EAlu ALU_ADD (EAlu ALU_ADD (EVar 1) (EVar 5)) (ELit 38);
   EVar 4;
   EExt true 0 1 (EVar 7);
   ELit 0x26b39;
   EVar 35;
   EVar 36;
   EVar 37;
   EVar 38;
   EVar 39;
   EVar 40;
   EVar 41;
   EVar 42;
   EVar 43].

Definition kn_T0 : list kentry :=
  [KAlign (EVar 0) 16;
   KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) (ELit 8388608);
   KWord (SA (EVar 0) (-56)) 8 (ELit 0x1ba3c);
   KWord (SA (EVar 0) (-64)) 8 (EAlu ALU_ADD (EVar 0) (ELit 8));
   KWord (SA (EVar 0) (-72)) 8 (ELit 2);
   KWord (SA (EVar 0) (-80)) 8 (ELit 0x13ac0);
   KWord (SA (EVar 0) (-88)) 8 (EAlu ALU_ADD (EVar 0) (ELit 32));
   KWord (SA (EVar 0) (-96)) 8 (ELit 0);
   KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-112)) 8 (ELit 0);
   KWord (SA (EVar 0) (-120)) 8 (ELit 0);
   KAlign (EVar 2) 4096;
   KRange (EVar 2) 0x2000 0x7fffff7ff000;
   KAlign (EVar 1) 4096;
   KRange (EVar 1) 0x58000 0x7fffff7ef000;
   KWr (SA (EVar 1) (0)) (ELit 69632);
   KWr (SA (EVar 2) (0)) (ELit 4096);
   KDisj (SA (EVar 0) (-8388608)) (ELit 0x80800000) (SA (EVar 1) (0)) (ELit 69632);
   KDisj (SA (EVar 0) (-8388608)) (ELit 0x80800000) (SA (EVar 2) (0)) (ELit 4096);
   KDisj (SA (EVar 2) (0)) (ELit 4096) (SA (EVar 1) (0)) (ELit 69632);
   KDisj (SA (ELit 0) 0x10000) (ELit 0x48000) (SA (EVar 1) (0)) (ELit 69632);
   KDisj (SA (ELit 0) 0x10000) (ELit 0x48000) (SA (EVar 2) (0)) (ELit 4096);
   KWord (SA (EVar 2) (0)) 8 (EVar 45);
   KWord (SA (EVar 2) (8)) 8 (ELit 0);
   KWord (SA (EVar 2) (16)) 8 (ELit 101);
   KWord (SA (EVar 2) (24)) 8 (EAlu ALU_ADD (EVar 2) (ELit 24));
   KWord (SA (EVar 2) (32)) 8 (EAlu ALU_ADD (EVar 2) (ELit 24));
   KWord (SA (EVar 2) (40)) 8 (EVar 1);
   KWord (SA (EVar 2) (48)) 8 (ELit 0);
   KWord (SA (EVar 2) (56)) 8 (ELit 0x11b20);
   KZero (SA (EVar 2) (64)) (ELit 4032);
   KWord (SA (EVar 1) (0)) 8 (EAlu ALU_ADD (EVar 2) (ELit 24));
   KWord (SA (EVar 1) (8)) 1 (ELit 0);
   KZero (SA (EVar 1) (9)) (ELit 4);
   KWord (SA (EVar 1) (13)) 1 (ELit 224);
   KWord (SA (EVar 1) (14)) 2 (ELit 1);
   KWord (SA (EVar 1) (28)) 1 (ELit 0);
   KWord (SA (EVar 1) (29)) 1 (ELit 160);
   KWord (SA (EVar 1) (30)) 2 (ELit 1);
   KWord (SA (EVar 1) (65568)) 1 (ELit 0);
   KWord (SA (EVar 1) (69623)) 1 (ELit 0);
   KWord (SA (EVar 1) (69624)) 4 (ELit 4060);
   KZero (SA (EVar 1) (69628)) (ELit 4);
   KBlob (SA (EVar 1) (32)) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 4) (EVar 5)) (ELit 6)) 0;
   KWr (SA (ELit 0) 0x26000) (ELit 0x32000);
   KImg 0x0 0x1000;
   KImg 0x10000 0x26af0;
   KImg 0x26af1 0x26b39; KImg 0x36b39 0x36b90;
   KImg 0x56c68 0x56c88;
   KWord (SA (ELit 0) (224152)) 8 (ELit 0x36b98);
   KWord (SA (ELit 0) (224184)) 4 (EVar 3);
   KWord (SA (ELit 0) (224188)) 4 (EVar 11);
   KImg 0x36bc4 0x36c10;
   KImg 0x36c18 0x36c30;
   KImg 0x36c38 0x36c50;
   KImg 0x36c60 0x36c70;
   KImg 0x36c78 0x36ce8; KImg 0x56ca8 0x56ed0;
   KWord (SA (ELit 0) (355488)) 8 (EVar 44);
   KImg 0x56ed0 0x56ed8;
   KImg 0x56ee9 0x56ef0;
   KImg 0x56ef8 0x56f00;
   KImg 0x56f10 0x56f18;
   KWord (SA (ELit 0) (356120)) 8 (ELit 4096);
   KImg 0x56f20 0x56f50;
   KImg 0x56f58 0x56f60;
   KWord (SA (ELit 0) (356192)) 8 (EVar 45);
   KWord (SA (ELit 0) (356200)) 4 (ELit 1);
   KWord (SA (ELit 0) (356204)) 4 (ELit 1);
   KWord (SA (ELit 0) (356208)) 8 (ELit 0);
   KWord (SA (ELit 0) (356216)) 8 (EAlu ALU_ADD (EVar 2) (ELit 64));
   KWord (SA (ELit 0) (356224)) 8 (ELit 100);
   KWord (SA (ELit 0) (356232)) 8 (ELit 0);
   KWord (SA (ELit 0) (356240)) 8 (EVar 10);
   KWord (SA (ELit 0) (356248)) 8 (EVar 2);
   KWord (SA (ELit 0) (356256)) 8 (EVar 2);
   KWord (SA (ELit 0) (356264)) 8 (EAlu ALU_ADD (EVar 2) (ELit 4096));
   KImg 0x56fb0 0x57110;
   KWord (SA (ELit 0) (356624)) 8 (EAlu ALU_ADD (EVar 2) (ELit 24));
   KImg 0x57118 0x57130;
   KImg 0x57130 0x57290;
   KWord (SA (ELit 0) (357008)) 8 (ELit 1);
   KImg 0x57298 0x572b0;
   KImg 0x572b0 0x572f0;
   KWord (SA (ELit 0) (357104)) 1 (ELit 1);
   KImg 0x572f1 0x572f8;
   KWord (SA (ELit 0) (357112)) 8 (EVar 9);
   KImg 0x57308 0x58000;
   KRange (EVar 3) 1 4194303;
   KRange (EVar 10) 0 1;
   KRange (EVar 11) 0 4294967295;
   KRange (EVar 5) 0 32767;
   KRange (EVar 6) 0 255;
   KRange (EVar 7) 0 255;
   KRange (EVar 8) 0 255;
   KRange (EAlu ALU_ADD (EAlu ALU_ADD (EVar 4) (EVar 5)) (ELit 6)) 6 65535].

(* [comment removed for export] *)
Definition kn_T (nlo nhi : Z) : list kentry :=
  KRange (EVar 4) nlo nhi :: KRange (EVar 5) 0 (Z.min 32767 (65529 - nlo)) :: kn_T0.

(* [comment removed for export] *)
Definition maps_T : list smap := [SM (EVar 1) (ELit 69632) true; SM (EVar 2) (ELit 4096) false].

(* [comment removed for export] *)
Definition slots_T : list sslot :=
  [SL (EAlu ALU_ADD (EVar 1) (ELit 16)) (ELit 69616) (ELit 65536) (ELit 1) (ELit 0x11b20) 0 (EAlu ALU_ADD (EVar 1) (ELit 32))].

Definition cs_T (nlo nhi : Z) : cstate := CS (SS 0x13d90 sr_T [] (kn_T nlo nhi) NX0) maps_T 4 278528 slots_T.
