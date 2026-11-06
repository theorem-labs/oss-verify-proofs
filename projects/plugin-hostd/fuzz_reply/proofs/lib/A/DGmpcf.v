(* The reply A twin of the cf layer's DGmpcf.v (field round 3 part 3; a working branch f02099425ace,
   proofs/cgif/cgif_file_fuzzer/lib/DGmpcf.v). rule 24: no function proved (kind: frame corollaries over the Deallocate
   walks' dmem_m frame).

   This file is the cgif file's generic part (its Section a), with reply module paths: the cf instance MPcf of the
   Deallocate walks' memory predicate (part 3c: the read-only bytes alone, arodata_ok_cf over YG0dcf.aro_addr_cf, the
   RELRO range and the report reads; memnorm is no longer part of it), the unit image row zones_miss_relro, and the
   keep law MP_keep_cf (Reusable/YG0dcf.arodata_frame_cf over the four zones). dg_dzone / dg_izone are A/DGif0reply.v's DImg_reply fields (DGgi.DZONE / DGgi.IZONE). Section b gives the row at
   reply A, zones_miss_relro (ci := CfImg_A) B, from A/ReplyRelroGeoA.zones_miss_relro_reply_A (a Theorem Labs lane's, from
   named bounds; its statement is zones_miss_relro's body expanded, so it closes by exact), and MP_keep_cf at it.
   No numeral is introduced here. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG03 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DGbase DGgi DGgm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG AGif2reply DGif0 DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MemnormT MemnormDmid.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyRelroGeoA.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.

(* The cf instance of DGif0.DIface's memory predicate MP: the read-only bytes (RELRO and the report reads), the fact
   acall_pre_cf carries at the call (YG0dcf.arodata_ok_cf). *)
Definition MPcf (B : asyms) (m : word -> option byte) : Prop :=
arodata_ok_cf tfibsegs B m.

(* The unit image row MP_keep_cf needs: at the seed's geometry, no non-owned covered byte (RELRO or a report read)
   lies in the walk's window, the depot zone, the internal allocator's zone or the freed block's shadow.  It is exactly
   arodata_frame_cf's second premise at X := those four zones. *)
Definition zones_miss_relro (B : asyms) : Prop :=
forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU,
DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
forall a, aro_addr_cf a -> ~ Exists (in_zr a) (as_owned_static B) ->
0 <= a < 2 ^ 64 /\ ~ dwin_m ly (bv_unsigned (getr regs0 2)) p a /\ ~ dg_dzone ly a /\ ~ dg_izone a /\
~ dshadow p nn a.

(* The keep law of MP at the cf instance (DGfz.MP_keep / DGg2.MP_keep). *)
Theorem MP_keep_cf : forall B, zones_miss_relro B ->
forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU (mem' : word -> option byte),
DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
(forall x : word, ~ dwin_m ly (bv_unsigned (getr regs0 2)) p (bv_unsigned x) -> ~ dg_dzone ly (bv_unsigned x) ->
  ~ dg_izone (bv_unsigned x) -> ~ dshadow p nn (bv_unsigned x) -> mem' x = mem0 x) ->
MPcf B mem0 -> MPcf B mem'.
Proof.
intros B HZ W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU mem' FH FR HRO.
apply (arodata_frame_cf tfibsegs B
  (fun a => dwin_m ly (bv_unsigned (getr regs0 2)) p a \/ dg_dzone ly a \/ dg_izone a \/ dshadow p nn a)
  mem0 mem').
- intros x NX. apply FR; intros Y; apply NX; tauto.
- intros a Ha NO.
  destruct (HZ W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH a Ha NO) as (R & N1 & N2 & N3 & N4).
  split; [exact R|]. intros [X|[X|[X|X]]]; [exact (N1 X) | exact (N2 X) | exact (N3 X) | exact (N4 X)].
- exact HRO.
Qed.
End a.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* reply A: the row (a Theorem Labs lane's ReplyRelroGeoA) and the keep law at it.                                          *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem zones_miss_relro_A : forall B, zones_miss_relro (ci := CfImg_A) B.
Proof. intros B. exact (ReplyRelroGeoA.zones_miss_relro_reply_A B). Qed.

(* MP_keep_cf at reply A's row: the law reply A's cf instance hands to DGfz / DGg2. *)
Theorem MP_keep_cf_reply_A : forall B,
forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU (mem' : word -> option byte),
DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
(forall x : word, ~ dwin_m ly (bv_unsigned (getr regs0 2)) p (bv_unsigned x) -> ~ dg_dzone ly (bv_unsigned x) ->
  ~ dg_izone (bv_unsigned x) -> ~ dshadow p nn (bv_unsigned x) -> mem' x = mem0 x) ->
MPcf (ci := CfImg_A) B mem0 -> MPcf (ci := CfImg_A) B mem'.
Proof. intros B. exact (MP_keep_cf (ci := CfImg_A) B (zones_miss_relro_A B)). Qed.
End b.
