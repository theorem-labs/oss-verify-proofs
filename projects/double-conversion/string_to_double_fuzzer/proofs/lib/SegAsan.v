(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanPlan.
From Corelib Require Import PrimString.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanStateCodec AsanPlanCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition E_R : expr := (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 36703).
Definition seg_body (ho : plan) : plan :=
  PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [0x5d5b4] (* [comment removed for export] *)
  (PJoin e_sp0 (-2280) 8 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
   (PSpin (* [comment removed for export] *)))
  (PShDisj (escale 4096 (EVar 96)) (ELit 1048576) (ELit 65536) (ELit 6782976) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 96)) (ELit 1048576) e_stklo e_stkn (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
   (PSpin (* [comment removed for export] *)))
  (PShDisj (escale 4096 (EVar 97)) (ELit 8388608) (ELit 65536) (ELit 6782976) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 97)) (ELit 8388608) e_stklo e_stkn (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
   (PSpin (* [comment removed for export] *)))
  (PShDisj (escale 4096 (EVar 114)) (ELit 4096) (ELit 65536) (ELit 6782976) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 114)) (ELit 4096) e_stklo e_stkn (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [0xa40ec] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  ho))))))))))))))))))))))))))))))))))))))))))))).

Definition HO : plan := dec_plan (PE [] [] [] [] [] []) "#9#56?5<8#4#9#40354<#4&9#204148#2#3&9#204160#2#3%5,2<,:,:,13?,;,140,<,=,=,>,>,?,?,10,10,11,11,12,12,13,13,14,14,15,15,16,16,17,17,18,18,19,19,1:,1:,60,1;,61,1<,72,1=,1;,1>,1<,1?,1=,20,1>,21,1?,22,20,23,21,24,22,25,23,26,24,27,25,28,35,29,133,2:,134,2;,135,2<,136,2=,137,2>,138,2?,139,30,13:,31,13;,32,13<,33,13=,34,13>,35#;,88$;,"%pstring.
Definition seg_u : plan :=
  PCase2 E_R 4030 (* [comment removed for export] *)
  (seg_body HO)
  (seg_body HO).

(* [comment removed for export] *)
Definition seg_asan_ranges : list (Z * nat) := [(0x4e000, 2048%nat); (0x5d000, 5120%nat); (0x77000, 3072%nat); (0x7c000, 5120%nat); (0x82000, 4096%nat); (0x87000, 7168%nat); (0x90000, 2048%nat); (0x93000, 6144%nat); (0xa3000, 3072%nat); (0x10a000, 3072%nat); (0x11c000, 2048%nat); (0x11f000, 2048%nat)]%Z.
