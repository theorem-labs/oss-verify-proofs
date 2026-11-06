(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymPlan RefWorldK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SP.
Open Scope Z_scope.

Definition NX0k : nat := 44%nat.
Definition sr_Tk (k : Z) : list expr :=
  [ELit 0;
   ELit 0x326e8;
   EAlu ALU_ADD (EVar 0) (ELit (-128));
   ELit 0x10800;
   ELit 0xc4918;
   EVar 17;
   EVar 18;
   EVar 19;
   EAlu ALU_ADD (EVar 1) (ELit (offk k + 2));
   EAlu ALU_ADD (EVar 1) (ELit (offk k));
   EAlu ALU_ADD (EVar 1) (ELit (offk k + 2));
   EVar 5;
   EAlu ALU_ADD (EAlu ALU_ADD (EVar 1) (EVar 5)) (ELit (offk k + 6));
   EVar 4;
   EVar 26;
   EVar 27;
   EVar 28;
   EVar 29;
   EVar 5;
   EAlu ALU_ADD (EAlu ALU_ADD (EVar 1) (EVar 5)) (ELit (offk k + 6));
   EVar 4;
   EExt true 0 1 (EVar 7);
   ELit 0xb2ee9;
   ELit 0;
   EVar 36;
   EVar 37;
   EVar 38;
   EVar 39;
   EVar 40;
   EVar 41;
   EVar 42;
   EVar 43].

Definition kn_Tk0 (k : Z) : list kentry :=
  [KAlign (EVar 0) 16;
   KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) (ELit 8388608);
   KWord (SA (EVar 0) (-56)) 8 (ELit 0x95a48);
   KWord (SA (EVar 0) (-64)) 8 (EAlu ALU_ADD (EVar 0) (ELit 8));
   KWord (SA (EVar 0) (-72)) 8 (ELit 2);
   KWord (SA (EVar 0) (-80)) 8 (ELit 0x32574);
   KWord (SA (EVar 0) (-88)) 8 (EAlu ALU_ADD (EVar 0) (ELit 32));
   KWord (SA (EVar 0) (-96)) 8 (ELit 0);
   KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-112)) 8 (ELit 0);
   KWord (SA (EVar 0) (-120)) 8 (ELit 0);
   KAlign (EVar 2) 4096;
   KRange (EVar 2) 0x2000 0x7fffff7ff000;
   KDisj (SA (EVar 0) (-8388608)) (ELit 281474976710656) (SA (EVar 2) (0)) (ELit 4096);
   KRange (EAlu ALU_SUB (EVar 0) (EVar 2)) 8392704 0x800000000000;
   KAlign (EVar 1) 4096;
   KRange (EVar 1) 0xe6000 (0x7fffff800000 - nbk k);
   KDisj (SA (EVar 0) (-8388608)) (ELit 281474976710656) (SA (EVar 1) (0)) (ELit (nbk k));
   KRange (EAlu ALU_SUB (EVar 0) (EVar 1)) (8388608 + nbk k) 0x800000000000;
   KWr (SA (EVar 1) (0)) (ELit (nbk k));
   KWr (SA (EVar 2) (0)) (ELit 4096);
   KDisj (SA (EVar 2) (0)) (ELit 4096) (SA (EVar 1) (0)) (ELit (nbk k));
   KDisj (SA (ELit 0) 0x10000) (ELit 0xd6000) (SA (EVar 1) (0)) (ELit (nbk k));
   KDisj (SA (ELit 0) 0x10000) (ELit 0xd6000) (SA (EVar 2) (0)) (ELit 4096);
   KWord (SA (EVar 2) (0)) 8 (EVar 13);
   KWord (SA (EVar 2) (8)) 8 (ELit 0);
   KWord (SA (EVar 2) (16)) 4 (ELit 101);
   KWord (SA (EVar 2) (slotC k 0)) 8 (ELit 0);
   KWord (SA (EVar 2) (slotC k 0 + 8)) 8 (ELit 0);
   KWord (SA (EVar 2) (slotC k 0 + 16)) 8 (EVar 1);
   KWord (SA (EVar 2) (slotC k 0 + 24)) 4 (ELit 0);
   KWord (SA (EVar 2) (slotC k 0 + 28)) 4 (ELit 0);
   KWord (SA (EVar 2) (slotC k 0 + 32)) 8 (ELit (Wk k));
   KWord (SA (EVar 2) (slotF k 0)) 8 (EAlu ALU_ADD (EVar 2) (ELit (slotF k 0)));
   KWord (SA (EVar 2) (slotF k 0 + 8)) 8 (EAlu ALU_ADD (EVar 2) (ELit (slotF k 0)));
   KWord (SA (EVar 2) (slotF k 0 + 16)) 8 (ELit 0);
   KWord (SA (EVar 2) (slotF k 0 + 24)) 8 (ELit 0);
   KWord (SA (EVar 2) (slotF k 0 + 32)) 8 (ELit 0);
   KZero (SA (EVar 2) (104)) (ELit (4096 - 104));
   KWord (SA (EVar 1) (0)) 8 (EAlu ALU_ADD (EVar 2) (ELit (slotC k 0)));
   KWord (SA (EVar 1) (8)) 1 (ELit 0);
   KZero (SA (EVar 1) (9)) (ELit 4);
   KWord (SA (EVar 1) (13)) 1 (ELit 224);
   KWord (SA (EVar 1) (14)) 2 (ELit (k + 1));
   KWord (SA (EVar 1) (offk k - 4)) 1 (ELit 0);
   KWord (SA (EVar 1) (offk k - 3)) 1 (ELit 160);
   KWord (SA (EVar 1) (offk k - 2)) 2 (ELit (k + 1));
   KWord (SA (EVar 1) (offk k + capk k)) 1 (ELit 0);
   KWord (SA (EVar 1) (nbk k - 9)) 1 (ELit 0);
   KWord (SA (EVar 1) (nbk k - 8)) 4 (ELit (resk k));
   KZero (SA (EVar 1) (nbk k - 4)) (ELit 4);
   KBlob (SA (EVar 1) (offk k)) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 4) (EVar 5)) (ELit 6)) 0;
   KWr (SA (ELit 0) 0xb2000) (ELit 0x10f20);
   KWr (SA (ELit 0) 0xc4008) (ELit 0x21ff8);
   KImg 0x0 0x1000;
   KImg 0x10000 0xb2ea0;
   KImg 0xb2ea1 0xb2ee9;
   KImg 0xc2ee9 0xc2f20;
   KImg 0xc4008 0xc4848;
   KImg 0xe4920 0xe4940;
   KWord (SA (ELit 0) (804944)) 8 (ELit 0xc4850);
   KWord (SA (ELit 0) (804976)) 4 (EVar 3);
   KWord (SA (ELit 0) (804980)) 4 (EVar 11);
   KImg 0xc487c 0xc48c8;
   KImg 0xc48d0 0xc48e8;
   KImg 0xc48f0 0xc4908;
   KImg 0xc4918 0xc4928;
   KImg 0xc4930 0xc49a0; KImg 0xe4958 0xe4b88;
   KWord (SA (ELit 0) (936840)) 8 (EVar 12);
   KImg 0xe4b90 0xe4b98;
   KImg 0xe4ba9 0xe4bb0;
   KImg 0xe4bb8 0xe4bc0;
   KImg 0xe4bd0 0xe4bd8;
   KWord (SA (ELit 0) (936920)) 8 (ELit 4096);
   KImg 0xe4be0 0xe4c10;
   KImg 0xe4c18 0xe4d28;
   KWord (SA (ELit 0) (937256)) 8 (EVar 13);
   KWord (SA (ELit 0) (937264)) 4 (ELit 1);
   KWord (SA (ELit 0) (937268)) 4 (ELit (1 + k));
   KWord (SA (ELit 0) (937272)) 8 (EAlu ALU_ADD (EVar 2) (ELit (slotF k 0)));
   KWord (SA (ELit 0) (937280)) 8 (EAlu ALU_ADD (EVar 2) (ELit 104));
   KWord (SA (ELit 0) (937288)) 8 (ELit 99);
   KWord (SA (ELit 0) (937296)) 8 (ELit 0);
   KWord (SA (ELit 0) (937304)) 8 (EVar 10);
   KWord (SA (ELit 0) (937312)) 8 (EVar 2);
   KWord (SA (ELit 0) (937320)) 8 (EVar 2);
   KWord (SA (ELit 0) (937328)) 8 (EAlu ALU_ADD (EVar 2) (ELit 4096));
   KImg 0xe4d78 0xe4ed8;
   KWord (SA (ELit 0) (937688)) 8 (ELit 0);
   KImg 0xe4ee0 0xe4ef8;
   KImg 0xe4ef8 0xe5058;
   KWord (SA (ELit 0) (938072)) 8 (ELit 0);
   KImg 0xe5060 0xe5078;
   KImg 0xe5078 0xe50b8;
   KWord (SA (ELit 0) (938168)) 1 (ELit (1 + 2 * k));
   KImg 0xe50b9 0xe50c0;
   KWord (SA (ELit 0) (938176)) 8 (EVar 9);
   KImg 0xe50c8 0xe6000;
   KRange (EVar 3) 1 4194303;
   KRange (EVar 10) 0 1;
   KRange (EVar 11) 0 4294967295;
   KRange (EVar 5) 0 32767;
   KRange (EVar 6) 0 255;
   KRange (EVar 7) 0 255;
   KRange (EVar 8) 0 255;
   KRange (EAlu ALU_ADD (EAlu ALU_ADD (EVar 4) (EVar 5)) (ELit 6)) (capk (k - 1)) (capk k - 1)].

(* [comment removed for export] *)
Definition kn_Tk (k nlo nhi : Z) : list kentry :=
  KRange (EVar 4) nlo nhi :: KRange (EVar 5) 0 (Z.min 32767 (capk k - 7 - nlo)) :: kn_Tk0 k.

(* [comment removed for export] *)
Definition maps_Tk (k : Z) : list smap := [SM (EVar 1) (ELit (nbk k)) true; SM (EVar 2) (ELit 4096) false].

(* [comment removed for export] *)
Definition slots_Tk (k : Z) : list sslot :=
  [SL (EAlu ALU_ADD (EVar 1) (ELit 16)) (ELit (nbk k - 16)) (ELit (capk k)) (ELit (k + 1)) (ELit (Wk k)) 0 (EAlu ALU_ADD (EVar 1) (ELit (offk k)))].

(* [comment removed for export] *)
Definition cs_Tk (k nlo nhi : Z) : cstate := CS (SS 0x32844 (sr_Tk k) [] (kn_Tk k nlo nhi) NX0k) (maps_Tk k) 9 (nbk k + 2^20 + 8192) (slots_Tk k).
