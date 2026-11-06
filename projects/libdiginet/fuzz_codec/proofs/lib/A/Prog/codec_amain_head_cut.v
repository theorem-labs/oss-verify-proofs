(* The cuts inside the HEAD segment of the image-A walk of LLVMFuzzerTestOneInput (0x80abc-0x80c30,
   lib/A/Prog/codec_amain_inv.v seg_head), in the form of codec_amain_inv.v's mcut: the two calls of the
   runtime's checked memset (0x80b5c of the call record k = F + 176, 0x80c08 of before and out at F + 252),
   the call of diginet_personality_of (0x80bc4) and its return, and the state the switch on the kind starts
   from (0x80c0c). Every cut carries the frame's shadow map with k's 23 bytes 0 (k marked usable), the loop
   counter, the cursor past the op byte (1 <= c) and the bytes of the record at F + 176. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0s YK14 YK15 YK18 YP09 YI00 YI04 YI08 YI09 YI16 YN3v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACeh ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgEncC CodecRo CodecGlobs CPgWalk CPgWalkIntr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the pcs the cuts sit at *)
Definition PC_HDK : Z := 0x80b60.
Definition PC_HDI : Z := 0x80ba0.
Definition PC_HDP : Z := 0x80bc8.
Definition PC_HDQ : Z := 0x80c0c.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Local Notation mcut := (mcut B MT K XM_LIB).

(* the bytes of the record that the first memset leaves 0, from offset lo of k *)
Definition hd_kzero (g : ectx) (pos lo : Z) (W2 : world tfibsegs) (mem2 : word -> option byte) : Prop :=
forall j, lo <= j < 184 -> aview tfibsegs (w_H W2) mem2 (FA g pos + 176 + j) = Some 0.

(* 0x51e34 with a0 = k, a1 = 0, a2 = 184: the memset of the call record (0x80b5c) *)
Definition hd_ms1 (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 CA_MEMSET (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
getr regs2 1 = w64 PC_HDK /\ getr regs2 10 = w64 (FA g pos + 176) /\
getr regs2 11 = w64 0 /\ getr regs2 12 = w64 184 /\
exists c op, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ 0 <= op < 256 /\ getr regs2 23 = w64 op).

(* 0x80b60: the record is 184 zero bytes, the op byte still in s7 *)
Definition hd_mk (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 PC_HDK (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
exists c op, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ 0 <= op < 256 /\ getr regs2 23 = w64 op /\
hd_kzero g pos 0 W2 mem2).

(* 0x80ba0: k.kind written (0x80b94), the desk index i in s8 *)
Definition hd_mi (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 PC_HDI (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
exists c kind i, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ 0 <= kind <= 14 /\ 0 <= i <= 2 /\
getr regs2 24 = w64 i /\
val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 176) 4 kind /\
hd_kzero g pos 4 W2 mem2).

(* 0x84888 with a0 = DESK[i] = i: the call of diginet_personality_of (0x80bc4) *)
Definition hd_mc (g : ectx) (pos sp1 ops i : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 AM_pers_of (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ 0 <= i <= 2 /\
getr regs2 1 = w64 PC_HDP /\ getr regs2 10 = w64 i /\ getr regs2 24 = w64 i /\
exists c kind, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ 0 <= kind <= 14 /\
val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 176) 4 kind /\
hd_kzero g pos 4 W2 mem2).

(* 0x80bc8: the personality of DESK[i] in a0 *)
Definition hd_mc2 (g : ectx) (pos sp1 ops i : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 PC_HDP (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ 0 <= i <= 2 /\
getr regs2 10 = w64 (pers_ofA CA_PERS i) /\ getr regs2 24 = w64 i /\
exists c kind, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ 0 <= kind <= 14 /\
val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 176) 4 kind /\
hd_kzero g pos 4 W2 mem2).

(* 0x51e34 with a0 = F + 252, a1 = 0xa5, a2 = 64: the memset of before and out (0x80c08) *)
Definition hd_mp (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 CA_MEMSET (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
getr regs2 1 = w64 PC_HDQ /\ getr regs2 10 = w64 (FA g pos + 252) /\
getr regs2 11 = w64 165 /\ getr regs2 12 = w64 64 /\
exists c kind pv dv od, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ 0 <= kind <= 14 /\
pd_okA pv dv od /\ getr regs2 23 = w64 pv /\
val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 176) 4 kind /\
val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 184) 8 pv /\
val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 192) 8 dv /\
(forall j, 4 <= j < 8 -> aview tfibsegs (w_H W2) mem2 (FA g pos + 176 + j) = Some 0) /\
hd_kzero g pos 24 W2 mem2).

(* 0x80c0c: the record as HEAD leaves it (k_rdZ kind pv dv), s7 = k.p, the cursor past the op byte.
   The tail of the segment (the kind test at 0x80c14 and the switch table at 0x20eac) runs from here. *)
Definition hd_mq (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut g pos sp1 0 PC_HDQ (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
exists c kind pv dv od, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ 0 <= kind <= 14 /\
pd_okA pv dv od /\ getr regs2 23 = w64 pv /\
k_at g pos (k_rdZ kind pv dv) W2 mem2).
End b.
End a.
