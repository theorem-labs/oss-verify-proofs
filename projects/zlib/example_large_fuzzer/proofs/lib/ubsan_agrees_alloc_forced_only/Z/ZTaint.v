(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflateInitLib RefDeflSafeI1 RefDeflSafeI5b RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintRel DeflateTaintCall DeflateTaintCore DeflateTaintInit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState Inflate HarnessSmall ZApiInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition dinit_cs : cstrm := cs_init (zc_none zstrm0).

Definition dinit_of (g : N -> Z -> Z) : deflate_state :=
  dFg 0%N 1%N 2%N 3%N 4%N (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) dinit_cs 1 15 8 6 0 8.

(* [comment removed for export] *)
Definition dinit_zr : ZRet := zret_of_cs (ds_strm (dinit_of (fun _ => g0))) Z_OK.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma hs_dpure_eq : @HarnessSmall.dpure = @DeflateSafe.dpure. Proof. reflexivity. Qed.
Lemma hs_dhooks_eq : HarnessSmall.dhooks = DeflateSafe.dhooks. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition DREL (s_a : deflate_state) (x : dstream) : Prop := DCALL s_a (dz_s x).

Lemma dinit_cs_ok : 0 <= cs_avail_in dinit_cs /\ 0 <= cs_avail_out dinit_cs.
Proof. split; vm_compute; discriminate. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

