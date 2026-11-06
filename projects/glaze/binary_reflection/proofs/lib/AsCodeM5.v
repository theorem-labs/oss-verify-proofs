(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
From OSSVerify.Proofs.glaze.binary_reflection.lib.Common Require InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_70094 : bv 32 := @BV 32 0x00060663%Z I.

Lemma D_70094 : decode_any W_70094 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70098 : bv 32 := @BV 32 0x00747693%Z I.

Lemma D_70098 : decode_any W_70098 = Some (OpImm ALU_AND (@BV 5 13%Z I) (@BV 5 8%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7009c : bv 32 := @BV 32 0x02c6d063%Z I.

Lemma D_7009c : decode_any W_7009c = Some (Branch BC_GE (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 13 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700a0 : bv 32 := @BV 32 0xfff90913%Z I.

Lemma D_700a0 : decode_any W_700a0 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 18%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700a4 : bv 32 := @BV 32 0x00395613%Z I.
Lemma F_700a4 : fetch_word Asan.M.loaded_segments (@BV 64 0x700ac%Z I : word) = Some W_700a4.
Proof. vm_refl. Qed.
Lemma D_700a4 : decode_any W_700a4 = Some (ShiftImm ALU_SRL (@BV 5 12%Z I) (@BV 5 18%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700a8 : bv 32 := @BV 32 0x00c585b3%Z I.
Lemma F_700a8 : fetch_word Asan.M.loaded_segments (@BV 64 0x700b0%Z I : word) = Some W_700a8.
Proof. vm_refl. Qed.
Lemma D_700a8 : decode_any W_700a8 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700ac : bv 32 := @BV 32 0x00058583%Z I.

Lemma D_700ac : decode_any W_700ac = Some (Load SZ1 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700b0 : bv 32 := @BV 32 0x04058263%Z I.

Lemma D_700b0 : decode_any W_700b0 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 68%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700b4 : bv 32 := @BV 32 0x00797613%Z I.

Lemma D_700b4 : decode_any W_700b4 = Some (OpImm ALU_AND (@BV 5 12%Z I) (@BV 5 18%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700b8 : bv 32 := @BV 32 0x02b64e63%Z I.

Lemma D_700b8 : decode_any W_700b8 = Some (Branch BC_LT (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700bc : bv 32 := @BV 32 0x000ab503%Z I.
Lemma F_700bc : fetch_word Asan.M.loaded_segments (@BV 64 0x700c4%Z I : word) = Some W_700bc.
Proof. vm_refl. Qed.
Lemma D_700bc : decode_any W_700bc = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 21%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700c0 : bv 32 := @BV 32 0x00040593%Z I.
Lemma F_700c0 : fetch_word Asan.M.loaded_segments (@BV 64 0x700c8%Z I : word) = Some W_700c0.
Proof. vm_refl. Qed.
Lemma D_700c0 : decode_any W_700c0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700c4 : bv 32 := @BV 32 0x0140006f%Z I.



(* [comment removed for export] *)
Definition W_700c8 : bv 32 := @BV 32 0x00140413%Z I.



(* [comment removed for export] *)
Definition W_700cc : bv 32 := @BV 32 0xfff48493%Z I.



(* [comment removed for export] *)
Definition W_700d0 : bv 32 := @BV 32 0x00158593%Z I.



(* [comment removed for export] *)
Definition W_700d4 : bv 32 := @BV 32 0x1e048063%Z I.



(* [comment removed for export] *)
Definition W_700d8 : bv 32 := @BV 32 0x00345613%Z I.



(* [comment removed for export] *)
Definition W_700dc : bv 32 := @BV 32 0x00c50633%Z I.
Lemma F_700dc : fetch_word Asan.M.loaded_segments (@BV 64 0x700e4%Z I : word) = Some W_700dc.
Proof. vm_refl. Qed.
Lemma D_700dc : decode_any W_700dc = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700e0 : bv 32 := @BV 32 0x00060603%Z I.
Lemma F_700e0 : fetch_word Asan.M.loaded_segments (@BV 64 0x700e8%Z I : word) = Some W_700e0.
Proof. vm_refl. Qed.
Lemma D_700e0 : decode_any W_700e0 = Some (Load SZ1 true (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700e4 : bv 32 := @BV 32 0xfe0602e3%Z I.
Lemma F_700e4 : fetch_word Asan.M.loaded_segments (@BV 64 0x700ec%Z I : word) = Some W_700e4.
Proof. vm_refl. Qed.
Lemma D_700e4 : decode_any W_700e4 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 8164%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700e8 : bv 32 := @BV 32 0x0075f693%Z I.
Lemma F_700e8 : fetch_word Asan.M.loaded_segments (@BV 64 0x700f0%Z I : word) = Some W_700e8.
Proof. vm_refl. Qed.
Lemma D_700e8 : decode_any W_700e8 = Some (OpImm ALU_AND (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700ec : bv 32 := @BV 32 0xfcc6cee3%Z I.



(* [comment removed for export] *)
Definition W_700f0 : bv 32 := @BV 32 0x01c0006f%Z I.



(* [comment removed for export] *)
Definition W_700f4 : bv 32 := @BV 32 0x00a9fa63%Z I.

Lemma D_700f4 : decode_any W_700f4 = Some (Branch BC_GEU (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700f8 : bv 32 := @BV 32 0x413505b3%Z I.

Lemma D_700f8 : decode_any W_700f8 = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 5 19%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_700fc : bv 32 := @BV 32 0x00098513%Z I.

Lemma D_700fc : decode_any W_700fc = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70100 : bv 32 := @BV 32 0x360100ef%Z I.
Lemma F_70100 : fetch_word Asan.M.loaded_segments (@BV 64 0x70108%Z I : word) = Some W_70100.
Proof. vm_refl. Qed.
Lemma D_70100 : decode_any W_70100 = Some (Jal (@BV 5 1%Z I) (@BV 21 66400%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70104 : bv 32 := @BV 32 0xfa050ce3%Z I.
Lemma F_70104 : fetch_word Asan.M.loaded_segments (@BV 64 0x7010c%Z I : word) = Some W_70104.
Proof. vm_refl. Qed.
Lemma D_70104 : decode_any W_70104 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 8120%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70108 : bv 32 := @BV 32 0x00000413%Z I.

Lemma D_70108 : decode_any W_70108 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7010c : bv 32 := @BV 32 0x00040513%Z I.

Lemma D_7010c : decode_any W_7010c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70110 : bv 32 := @BV 32 0x03813083%Z I.

Lemma D_70110 : decode_any W_70110 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70114 : bv 32 := @BV 32 0x03013403%Z I.

Lemma D_70114 : decode_any W_70114 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70118 : bv 32 := @BV 32 0x02813483%Z I.

Lemma D_70118 : decode_any W_70118 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7011c : bv 32 := @BV 32 0x02013903%Z I.

Lemma D_7011c : decode_any W_7011c = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70120 : bv 32 := @BV 32 0x01813983%Z I.

Lemma D_70120 : decode_any W_70120 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70124 : bv 32 := @BV 32 0x01013a03%Z I.

Lemma D_70124 : decode_any W_70124 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70128 : bv 32 := @BV 32 0x00813a83%Z I.

Lemma D_70128 : decode_any W_70128 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7012c : bv 32 := @BV 32 0x04010113%Z I.

Lemma D_7012c : decode_any W_7012c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70130 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_70130 : decode_any W_70130 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702c4 : bv 32 := @BV 32 0x0d000593%Z I.
Lemma F_702c4 : fetch_word Asan.M.loaded_segments (@BV 64 0x702cc%Z I : word) = Some W_702c4.
Proof. vm_refl. Qed.
Lemma D_702c4 : decode_any W_702c4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 208%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702c8 : bv 32 := @BV 32 0x00000693%Z I.
Lemma F_702c8 : fetch_word Asan.M.loaded_segments (@BV 64 0x702d0%Z I : word) = Some W_702c8.
Proof. vm_refl. Qed.
Lemma D_702c8 : decode_any W_702c8 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702cc : bv 32 := @BV 32 0x00000713%Z I.
Lemma F_702cc : fetch_word Asan.M.loaded_segments (@BV 64 0x702d4%Z I : word) = Some W_702cc.
Proof. vm_refl. Qed.
Lemma D_702cc : decode_any W_702cc = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702d0 : bv 32 := @BV 32 0x169170ef%Z I.
Lemma F_702d0 : fetch_word Asan.M.loaded_segments (@BV 64 0x702d8%Z I : word) = Some W_702d0.
Proof. vm_refl. Qed.
Lemma D_702d0 : decode_any W_702d0 = Some (Jal (@BV 5 1%Z I) (@BV 21 96616%Z I), 4%Z).
Proof. vm_refl. Qed.







(* [comment removed for export] *)
Definition W_702e8 : bv 32 := @BV 32 0x00030067%Z I.
Lemma F_702e8 : fetch_word Asan.M.loaded_segments (@BV 64 0x702f0%Z I : word) = Some W_702e8.
Proof. vm_refl. Qed.
Lemma D_702e8 : decode_any W_702e8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 6%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_702ec : bv 32 := @BV 32 0x0008f617%Z I.
Lemma F_702ec : fetch_word Asan.M.loaded_segments (@BV 64 0x702f4%Z I : word) = Some W_702ec.
Proof. vm_refl. Qed.
Lemma D_702ec : decode_any W_702ec = Some (Auipc (@BV 5 12%Z I) (@BV 20 143%Z I), 4%Z).
Proof. vm_refl. Qed.













(* [comment removed for export] *)
Definition W_70304 : bv 32 := @BV 32 0x0008f617%Z I.
Lemma F_70304 : fetch_word Asan.M.loaded_segments (@BV 64 0x7030c%Z I : word) = Some W_70304.
Proof. vm_refl. Qed.
Lemma D_70304 : decode_any W_70304 = Some (Auipc (@BV 5 12%Z I) (@BV 20 143%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70308 : bv 32 := @BV 32 0xf8463603%Z I.
Lemma F_70308 : fetch_word Asan.M.loaded_segments (@BV 64 0x70310%Z I : word) = Some W_70308.
Proof. vm_refl. Qed.
Lemma D_70308 : decode_any W_70308 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 3972%Z I), 4%Z).
Proof. vm_refl. Qed.













(* [comment removed for export] *)
Definition W_7032c : bv 32 := @BV 32 0x00300593%Z I.
Lemma F_7032c : fetch_word Asan.M.loaded_segments (@BV 64 0x70334%Z I : word) = Some W_7032c.
Proof. vm_refl. Qed.
Lemma D_7032c : decode_any W_7032c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70330 : bv 32 := @BV 32 0x00030067%Z I.
Lemma F_70330 : fetch_word Asan.M.loaded_segments (@BV 64 0x70338%Z I : word) = Some W_70330.
Proof. vm_refl. Qed.
Lemma D_70330 : decode_any W_70330 = Some (Jalr (@BV 5 0%Z I) (@BV 5 6%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_703dc : bv 32 := @BV 32 0x0008f617%Z I.
Lemma F_703dc : fetch_word Asan.M.loaded_segments (@BV 64 0x703e4%Z I : word) = Some W_703dc.
Proof. vm_refl. Qed.
Lemma D_703dc : decode_any W_703dc = Some (Auipc (@BV 5 12%Z I) (@BV 20 143%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_703e0 : bv 32 := @BV 32 0xeac63603%Z I.
Lemma F_703e0 : fetch_word Asan.M.loaded_segments (@BV 64 0x703e8%Z I : word) = Some W_703e0.
Proof. vm_refl. Qed.
Lemma D_703e0 : decode_any W_703e0 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 3756%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_703e4 : bv 32 := @BV 32 0x00063303%Z I.

Lemma D_703e4 : decode_any W_703e4 = Some (Load SZ8 true (@BV 5 6%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_703e8 : bv 32 := @BV 32 0x00058613%Z I.

Lemma D_703e8 : decode_any W_703e8 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_703ec : bv 32 := @BV 32 0x0f500593%Z I.
Lemma F_703ec : fetch_word Asan.M.loaded_segments (@BV 64 0x703f4%Z I : word) = Some W_703ec.
Proof. vm_refl. Qed.
Lemma D_703ec : decode_any W_703ec = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 245%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_703f0 : bv 32 := @BV 32 0x00030067%Z I.

Lemma D_703f0 : decode_any W_703f0 = Some (Jalr (@BV 5 0%Z I) (@BV 5 6%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.










(* [comment removed for export] *)
Definition W_7054c : bv 32 := @BV 32 0x81010113%Z I.

Lemma D_7054c : decode_any W_7054c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 2064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70550 : bv 32 := @BV 32 0x7e113423%Z I.

Lemma D_70550 : decode_any W_70550 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 2024%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70554 : bv 32 := @BV 32 0x7e813023%Z I.

Lemma D_70554 : decode_any W_70554 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 2016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70558 : bv 32 := @BV 32 0x7c913c23%Z I.

Lemma D_70558 : decode_any W_70558 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 2008%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7055c : bv 32 := @BV 32 0x7d213823%Z I.

Lemma D_7055c : decode_any W_7055c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 2000%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70560 : bv 32 := @BV 32 0x7d313423%Z I.

Lemma D_70560 : decode_any W_70560 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 1992%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70564 : bv 32 := @BV 32 0x7d413023%Z I.

Lemma D_70564 : decode_any W_70564 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 1984%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70568 : bv 32 := @BV 32 0x7b513c23%Z I.

Lemma D_70568 : decode_any W_70568 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 1976%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7056c : bv 32 := @BV 32 0x7f010413%Z I.

Lemma D_7056c : decode_any W_7056c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 2032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70570 : bv 32 := @BV 32 0xfa010113%Z I.

Lemma D_70570 : decode_any W_70570 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4000%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70574 : bv 32 := @BV 32 0x00058a13%Z I.

Lemma D_70574 : decode_any W_70574 = Some (OpImm ALU_ADD (@BV 5 20%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70578 : bv 32 := @BV 32 0x0008f597%Z I.
Lemma F_70578 : fetch_word Asan.M.loaded_segments (@BV 64 0x70580%Z I : word) = Some W_70578.
Proof. vm_refl. Qed.
Lemma D_70578 : decode_any W_70578 = Some (Auipc (@BV 5 11%Z I) (@BV 20 143%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7057c : bv 32 := @BV 32 0xce85b583%Z I.
Lemma F_7057c : fetch_word Asan.M.loaded_segments (@BV 64 0x70584%Z I : word) = Some W_7057c.
Proof. vm_refl. Qed.
Lemma D_7057c : decode_any W_7057c = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3304%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70580 : bv 32 := @BV 32 0x0605c583%Z I.
Lemma F_70580 : fetch_word Asan.M.loaded_segments (@BV 64 0x70588%Z I : word) = Some W_70580.
Proof. vm_refl. Qed.
Lemma D_70580 : decode_any W_70580 = Some (Load SZ1 false (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70584 : bv 32 := @BV 32 0x22058863%Z I.

Lemma D_70584 : decode_any W_70584 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 560%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70588 : bv 32 := @BV 32 0x00068913%Z I.

Lemma D_70588 : decode_any W_70588 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7058c : bv 32 := @BV 32 0x00060993%Z I.

Lemma D_7058c : decode_any W_7058c = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70590 : bv 32 := @BV 32 0x00050493%Z I.

Lemma D_70590 : decode_any W_70590 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70594 : bv 32 := @BV 32 0x0008f517%Z I.
Lemma F_70594 : fetch_word Asan.M.loaded_segments (@BV 64 0x7059c%Z I : word) = Some W_70594.
Proof. vm_refl. Qed.
Lemma D_70594 : decode_any W_70594 = Some (Auipc (@BV 5 10%Z I) (@BV 20 143%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70598 : bv 32 := @BV 32 0xd2453503%Z I.
Lemma F_70598 : fetch_word Asan.M.loaded_segments (@BV 64 0x705a0%Z I : word) = Some W_70598.
Proof. vm_refl. Qed.
Lemma D_70598 : decode_any W_70598 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3364%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7059c : bv 32 := @BV 32 0x00052503%Z I.
Lemma F_7059c : fetch_word Asan.M.loaded_segments (@BV 64 0x705a4%Z I : word) = Some W_7059c.
Proof. vm_refl. Qed.
Lemma D_7059c : decode_any W_7059c = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_705a0 : bv 32 := @BV 32 0x00300593%Z I.
Lemma F_705a0 : fetch_word Asan.M.loaded_segments (@BV 64 0x705a8%Z I : word) = Some W_705a0.
Proof. vm_refl. Qed.
Lemma D_705a0 : decode_any W_705a0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_705a4 : bv 32 := @BV 32 0x08b57063%Z I.
Lemma F_705a4 : fetch_word Asan.M.loaded_segments (@BV 64 0x705ac%Z I : word) = Some W_705a4.
Proof. vm_refl. Qed.
Lemma D_705a4 : decode_any W_705a4 = Some (Branch BC_GEU (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 13 128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_705a8 : bv 32 := @BV 32 0x0899fe63%Z I.
Lemma F_705a8 : fetch_word Asan.M.loaded_segments (@BV 64 0x705b0%Z I : word) = Some W_705a8.
Proof. vm_refl. Qed.
Lemma D_705a8 : decode_any W_705a8 = Some (Branch BC_GEU (@BV 5 19%Z I) (@BV 5 9%Z I) (@BV 13 156%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_705ac : bv 32 := @BV 32 0x80040513%Z I.



(* [comment removed for export] *)
Definition W_705b0 : bv 32 := @BV 32 0xfb050513%Z I.



(* [comment removed for export] *)
Definition W_705b4 : bv 32 := @BV 32 0x80040593%Z I.



(* [comment removed for export] *)
Definition W_705b8 : bv 32 := @BV 32 0xfc058593%Z I.



(* [comment removed for export] *)
Definition W_705bc : bv 32 := @BV 32 0x80040613%Z I.



(* [comment removed for export] *)
Definition W_705c0 : bv 32 := @BV 32 0xfb060613%Z I.
Lemma F_705c0 : fetch_word Asan.M.loaded_segments (@BV 64 0x705c8%Z I : word) = Some W_705c0.
Proof. vm_refl. Qed.
Lemma D_705c0 : decode_any W_705c0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 4016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_705c4 : bv 32 := @BV 32 0x7ff60a93%Z I.
Lemma F_705c4 : fetch_word Asan.M.loaded_segments (@BV 64 0x705cc%Z I : word) = Some W_705c4.
Proof. vm_refl. Qed.
Lemma D_705c4 : decode_any W_705c4 = Some (OpImm ALU_ADD (@BV 5 21%Z I) (@BV 5 12%Z I) (@BV 12 2047%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_705c8 : bv 32 := @BV 32 0x000ab4a3%Z I.



(* [comment removed for export] *)
Definition W_705cc : bv 32 := @BV 32 0x00b53023%Z I.



(* [comment removed for export] *)
Definition W_705d0 : bv 32 := @BV 32 0x00053423%Z I.



(* [comment removed for export] *)
Definition W_705d4 : bv 32 := @BV 32 0x6291e0ef%Z I.



(* [comment removed for export] *)
Definition W_705d8 : bv 32 := @BV 32 0x00050593%Z I.



(* [comment removed for export] *)
Definition W_705e4 : bv 32 := @BV 32 0x02154703%Z I.



(* [comment removed for export] *)
Definition W_705e8 : bv 32 := @BV 32 0x008ab4a3%Z I.



(* [comment removed for export] *)
Definition W_705ec : bv 32 := @BV 32 0x80040513%Z I.



(* [comment removed for export] *)
Definition W_705f0 : bv 32 := @BV 32 0xfb050513%Z I.



(* [comment removed for export] *)
Definition W_705f4 : bv 32 := @BV 32 0x0ff00793%Z I.



(* [comment removed for export] *)
Definition W_705f8 : bv 32 := @BV 32 0x00040613%Z I.



(* [comment removed for export] *)
Definition W_705fc : bv 32 := @BV 32 0x00000693%Z I.



(* [comment removed for export] *)
Definition W_70600 : bv 32 := @BV 32 0x34c060ef%Z I.



(* [comment removed for export] *)
Definition W_70604 : bv 32 := @BV 32 0x80040713%Z I.



(* [comment removed for export] *)
Definition W_70608 : bv 32 := @BV 32 0xfb070713%Z I.



(* [comment removed for export] *)
Definition W_7060c : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_70610 : bv 32 := @BV 32 0x000a0593%Z I.



(* [comment removed for export] *)
Definition W_70614 : bv 32 := @BV 32 0x00098613%Z I.



(* [comment removed for export] *)
Definition W_70618 : bv 32 := @BV 32 0x00090693%Z I.



(* [comment removed for export] *)
Definition W_7061c : bv 32 := @BV 32 0x0e0030ef%Z I.



(* [comment removed for export] *)
Definition W_70620 : bv 32 := @BV 32 0x0300006f%Z I.



(* [comment removed for export] *)
Definition W_7062c : bv 32 := @BV 32 0x00048593%Z I.



(* [comment removed for export] *)
Definition W_70630 : bv 32 := @BV 32 0x000a0613%Z I.



(* [comment removed for export] *)
Definition W_70634 : bv 32 := @BV 32 0x00098693%Z I.



(* [comment removed for export] *)
Definition W_70638 : bv 32 := @BV 32 0x00090713%Z I.



(* [comment removed for export] *)
Definition W_7063c : bv 32 := @BV 32 0x475120ef%Z I.



(* [comment removed for export] *)
Definition W_70640 : bv 32 := @BV 32 0xf699e6e3%Z I.



(* [comment removed for export] *)
Definition W_70644 : bv 32 := @BV 32 0xf72a64e3%Z I.

Lemma D_70644 : decode_any W_70644 = Some (Branch BC_LTU (@BV 5 20%Z I) (@BV 5 18%Z I) (@BV 13 8040%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70648 : bv 32 := @BV 32 0xf73a62e3%Z I.

Lemma D_70648 : decode_any W_70648 = Some (Branch BC_LTU (@BV 5 20%Z I) (@BV 5 19%Z I) (@BV 13 8036%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7064c : bv 32 := @BV 32 0xf69960e3%Z I.

Lemma D_7064c : decode_any W_7064c = Some (Branch BC_LTU (@BV 5 18%Z I) (@BV 5 9%Z I) (@BV 13 8032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70650 : bv 32 := @BV 32 0x409a06b3%Z I.

Lemma D_70650 : decode_any W_70650 = Some (Op ALU_SUB (@BV 5 13%Z I) (@BV 5 20%Z I) (@BV 5 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70654 : bv 32 := @BV 32 0x00100713%Z I.

Lemma D_70654 : decode_any W_70654 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70658 : bv 32 := @BV 32 0x02871713%Z I.

Lemma D_70658 : decode_any W_70658 = Some (ShiftImm ALU_SLL (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 6 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7065c : bv 32 := @BV 32 0x00170513%Z I.

Lemma D_7065c : decode_any W_7065c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 14%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70660 : bv 32 := @BV 32 0x04a6fa63%Z I.

Lemma D_70660 : decode_any W_70660 = Some (Branch BC_GEU (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 13 84%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70664 : bv 32 := @BV 32 0x15298863%Z I.

Lemma D_70664 : decode_any W_70664 = Some (Branch BC_EQ (@BV 5 19%Z I) (@BV 5 18%Z I) (@BV 13 336%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70668 : bv 32 := @BV 32 0x007a7513%Z I.

Lemma D_70668 : decode_any W_70668 = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 20%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7066c : bv 32 := @BV 32 0x06051063%Z I.

Lemma D_7066c : decode_any W_7066c = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70670 : bv 32 := @BV 32 0x00098a13%Z I.

Lemma D_70670 : decode_any W_70670 = Some (OpImm ALU_ADD (@BV 5 20%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70674 : bv 32 := @BV 32 0x00090a93%Z I.

Lemma D_70674 : decode_any W_70674 = Some (OpImm ALU_ADD (@BV 5 21%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70678 : bv 32 := @BV 32 0x00048513%Z I.

Lemma D_70678 : decode_any W_70678 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7067c : bv 32 := @BV 32 0x0074f993%Z I.

Lemma D_7067c : decode_any W_7067c = Some (OpImm ALU_AND (@BV 5 19%Z I) (@BV 5 9%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70680 : bv 32 := @BV 32 0x08099e63%Z I.

Lemma D_70680 : decode_any W_70680 = Some (Branch BC_NE (@BV 5 19%Z I) (@BV 5 0%Z I) (@BV 13 156%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70684 : bv 32 := @BV 32 0x000a0593%Z I.

Lemma D_70684 : decode_any W_70684 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 20%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70688 : bv 32 := @BV 32 0x000a0513%Z I.

Lemma D_70688 : decode_any W_70688 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 20%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7068c : bv 32 := @BV 32 0x0d5a6863%Z I.

Lemma D_7068c : decode_any W_7068c = Some (Branch BC_LTU (@BV 5 20%Z I) (@BV 5 21%Z I) (@BV 13 208%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70690 : bv 32 := @BV 32 0xff8af513%Z I.

Lemma D_70690 : decode_any W_70690 = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 21%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70694 : bv 32 := @BV 32 0x0cbaf863%Z I.

Lemma D_70694 : decode_any W_70694 = Some (Branch BC_GEU (@BV 5 21%Z I) (@BV 5 11%Z I) (@BV 13 208%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70698 : bv 32 := @BV 32 0xff8af493%Z I.

Lemma D_70698 : decode_any W_70698 = Some (OpImm ALU_AND (@BV 5 9%Z I) (@BV 5 21%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7069c : bv 32 := @BV 32 0x007a8613%Z I.

Lemma D_7069c : decode_any W_7069c = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 21%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706a0 : bv 32 := @BV 32 0xff867913%Z I.

Lemma D_706a0 : decode_any W_706a0 = Some (OpImm ALU_AND (@BV 5 18%Z I) (@BV 5 12%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706a4 : bv 32 := @BV 32 0x0c957a63%Z I.

Lemma D_706a4 : decode_any W_706a4 = Some (Branch BC_GEU (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 13 212%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706a8 : bv 32 := @BV 32 0x40a485b3%Z I.

Lemma D_706a8 : decode_any W_706a8 = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706ac : bv 32 := @BV 32 0x00000613%Z I.

Lemma D_706ac : decode_any W_706ac = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706b0 : bv 32 := @BV 32 0x0e00006f%Z I.

Lemma D_706b0 : decode_any W_706b0 = Some (Jal (@BV 5 0%Z I) (@BV 21 224%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706b4 : bv 32 := @BV 32 0xfffb0517%Z I.



(* [comment removed for export] *)
Definition W_706c4 : bv 32 := @BV 32 0x1b600593%Z I.



(* [comment removed for export] *)
Definition W_706c8 : bv 32 := @BV 32 0x570170ef%Z I.



(* [comment removed for export] *)
Definition W_706cc : bv 32 := @BV 32 0xff8a7a93%Z I.

Lemma D_706cc : decode_any W_706cc = Some (OpImm ALU_AND (@BV 5 21%Z I) (@BV 5 20%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706d0 : bv 32 := @BV 32 0x00098593%Z I.

Lemma D_706d0 : decode_any W_706d0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706d4 : bv 32 := @BV 32 0x01396463%Z I.

Lemma D_706d4 : decode_any W_706d4 = Some (Branch BC_LTU (@BV 5 18%Z I) (@BV 5 19%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706d8 : bv 32 := @BV 32 0x00090593%Z I.

Lemma D_706d8 : decode_any W_706d8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706dc : bv 32 := @BV 32 0xf8bafae3%Z I.

Lemma D_706dc : decode_any W_706dc = Some (Branch BC_GEU (@BV 5 21%Z I) (@BV 5 11%Z I) (@BV 13 8084%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706e0 : bv 32 := @BV 32 0x0008f597%Z I.
Lemma F_706e0 : fetch_word Asan.M.loaded_segments (@BV 64 0x706e8%Z I : word) = Some W_706e0.
Proof. vm_refl. Qed.
Lemma D_706e0 : decode_any W_706e0 = Some (Auipc (@BV 5 11%Z I) (@BV 20 143%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706e4 : bv 32 := @BV 32 0xb885b583%Z I.
Lemma F_706e4 : fetch_word Asan.M.loaded_segments (@BV 64 0x706ec%Z I : word) = Some W_706e4.
Proof. vm_refl. Qed.
Lemma D_706e4 : decode_any W_706e4 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 2952%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706e8 : bv 32 := @BV 32 0x0005b583%Z I.

Lemma D_706e8 : decode_any W_706e8 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706ec : bv 32 := @BV 32 0x003a5613%Z I.

Lemma D_706ec : decode_any W_706ec = Some (ShiftImm ALU_SRL (@BV 5 12%Z I) (@BV 5 20%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706f0 : bv 32 := @BV 32 0x00c585b3%Z I.

Lemma D_706f0 : decode_any W_706f0 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706f4 : bv 32 := @BV 32 0x00058583%Z I.

Lemma D_706f4 : decode_any W_706f4 = Some (Load SZ1 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706f8 : bv 32 := @BV 32 0x00058463%Z I.

Lemma D_706f8 : decode_any W_706f8 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_706fc : bv 32 := @BV 32 0xf6b55ae3%Z I.

Lemma D_706fc : decode_any W_706fc = Some (Branch BC_GE (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 13 8052%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70700 : bv 32 := @BV 32 0x000a8513%Z I.



(* [comment removed for export] *)
Definition W_70704 : bv 32 := @BV 32 0x0e9aea63%Z I.



(* [comment removed for export] *)
Definition W_70708 : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_7070c : bv 32 := @BV 32 0x000a8a13%Z I.



(* [comment removed for export] *)
Definition W_70710 : bv 32 := @BV 32 0x0f3af863%Z I.



(* [comment removed for export] *)
Definition W_70714 : bv 32 := @BV 32 0xf72ae4e3%Z I.



(* [comment removed for export] *)
Definition W_70718 : bv 32 := @BV 32 0x0f00006f%Z I.



(* [comment removed for export] *)
Definition W_7071c : bv 32 := @BV 32 0xf74504e3%Z I.



(* [comment removed for export] *)
Definition W_70720 : bv 32 := @BV 32 0xf75512e3%Z I.



(* [comment removed for export] *)
Definition W_70724 : bv 32 := @BV 32 0x00748593%Z I.



(* [comment removed for export] *)
Definition W_70728 : bv 32 := @BV 32 0xff85f913%Z I.



(* [comment removed for export] *)
Definition W_7072c : bv 32 := @BV 32 0xf5257ce3%Z I.



(* [comment removed for export] *)
Definition W_70730 : bv 32 := @BV 32 0xff84f513%Z I.



(* [comment removed for export] *)
Definition W_70734 : bv 32 := @BV 32 0xbd0ff0ef%Z I.



(* [comment removed for export] *)
Definition W_70738 : bv 32 := @BV 32 0x01350023%Z I.



(* [comment removed for export] *)
Definition W_7073c : bv 32 := @BV 32 0x00090593%Z I.



(* [comment removed for export] *)
Definition W_70740 : bv 32 := @BV 32 0x012a6463%Z I.



(* [comment removed for export] *)
Definition W_70744 : bv 32 := @BV 32 0x000a0593%Z I.



(* [comment removed for export] *)
Definition W_70748 : bv 32 := @BV 32 0x012ae463%Z I.



(* [comment removed for export] *)
Definition W_7074c : bv 32 := @BV 32 0x000a8913%Z I.



(* [comment removed for export] *)
Definition W_70750 : bv 32 := @BV 32 0x00090a93%Z I.



(* [comment removed for export] *)
Definition W_70754 : bv 32 := @BV 32 0x00058513%Z I.



(* [comment removed for export] *)
Definition W_70758 : bv 32 := @BV 32 0xf325fce3%Z I.



(* [comment removed for export] *)
Definition W_7075c : bv 32 := @BV 32 0xff857513%Z I.

Lemma D_7075c : decode_any W_7075c = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70760 : bv 32 := @BV 32 0xf2baece3%Z I.

Lemma D_70760 : decode_any W_70760 = Some (Branch BC_LTU (@BV 5 21%Z I) (@BV 5 11%Z I) (@BV 13 7992%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70764 : bv 32 := @BV 32 0x000a8593%Z I.

Lemma D_70764 : decode_any W_70764 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 21%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70768 : bv 32 := @BV 32 0xff8af493%Z I.

Lemma D_70768 : decode_any W_70768 = Some (OpImm ALU_AND (@BV 5 9%Z I) (@BV 5 21%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7076c : bv 32 := @BV 32 0x007a8613%Z I.

Lemma D_7076c : decode_any W_7076c = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 21%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70770 : bv 32 := @BV 32 0xff867913%Z I.

Lemma D_70770 : decode_any W_70770 = Some (OpImm ALU_AND (@BV 5 18%Z I) (@BV 5 12%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70774 : bv 32 := @BV 32 0xf2956ae3%Z I.

Lemma D_70774 : decode_any W_70774 = Some (Branch BC_LTU (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 13 7988%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70778 : bv 32 := @BV 32 0x00758513%Z I.

Lemma D_70778 : decode_any W_70778 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7077c : bv 32 := @BV 32 0xff857513%Z I.

Lemma D_7077c : decode_any W_7077c = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70780 : bv 32 := @BV 32 0x00a97a63%Z I.

Lemma D_70780 : decode_any W_70780 = Some (Branch BC_GEU (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70784 : bv 32 := @BV 32 0x412505b3%Z I.

Lemma D_70784 : decode_any W_70784 = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 5 18%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70788 : bv 32 := @BV 32 0x0fc00613%Z I.

Lemma D_70788 : decode_any W_70788 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 252%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7078c : bv 32 := @BV 32 0x00090513%Z I.

Lemma D_7078c : decode_any W_7078c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70790 : bv 32 := @BV 32 0xe79fe0ef%Z I.

Lemma D_70790 : decode_any W_70790 = Some (Jal (@BV 5 1%Z I) (@BV 21 2092664%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70794 : bv 32 := @BV 32 0x02990063%Z I.

Lemma D_70794 : decode_any W_70794 = Some (Branch BC_EQ (@BV 5 18%Z I) (@BV 5 9%Z I) (@BV 13 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70798 : bv 32 := @BV 32 0x409906b3%Z I.

Lemma D_70798 : decode_any W_70798 = Some (Op ALU_SUB (@BV 5 13%Z I) (@BV 5 18%Z I) (@BV 5 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7079c : bv 32 := @BV 32 0x00800513%Z I.

Lemma D_7079c : decode_any W_7079c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707a0 : bv 32 := @BV 32 0x02a69e63%Z I.

Lemma D_707a0 : decode_any W_707a0 = Some (Branch BC_NE (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707a4 : bv 32 := @BV 32 0x007af913%Z I.

Lemma D_707a4 : decode_any W_707a4 = Some (OpImm ALU_AND (@BV 5 18%Z I) (@BV 5 21%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707a8 : bv 32 := @BV 32 0x00048513%Z I.

Lemma D_707a8 : decode_any W_707a8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707ac : bv 32 := @BV 32 0xb58ff0ef%Z I.

Lemma D_707ac : decode_any W_707ac = Some (Jal (@BV 5 1%Z I) (@BV 21 2093912%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707b0 : bv 32 := @BV 32 0x01250023%Z I.

Lemma D_707b0 : decode_any W_707b0 = Some (Store SZ1 (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707b4 : bv 32 := @BV 32 0x06010113%Z I.

Lemma D_707b4 : decode_any W_707b4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707b8 : bv 32 := @BV 32 0x7e813083%Z I.

Lemma D_707b8 : decode_any W_707b8 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 2024%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707bc : bv 32 := @BV 32 0x7e013403%Z I.

Lemma D_707bc : decode_any W_707bc = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 2016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707c0 : bv 32 := @BV 32 0x7d813483%Z I.

Lemma D_707c0 : decode_any W_707c0 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 2008%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707c4 : bv 32 := @BV 32 0x7d013903%Z I.

Lemma D_707c4 : decode_any W_707c4 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 2000%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707c8 : bv 32 := @BV 32 0x7c813983%Z I.

Lemma D_707c8 : decode_any W_707c8 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 1992%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707cc : bv 32 := @BV 32 0x7c013a03%Z I.

Lemma D_707cc : decode_any W_707cc = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 1984%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707d0 : bv 32 := @BV 32 0x7b813a83%Z I.

Lemma D_707d0 : decode_any W_707d0 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 1976%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707d4 : bv 32 := @BV 32 0x7f010113%Z I.

Lemma D_707d4 : decode_any W_707d4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 2032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_707d8 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_707d8 : decode_any W_707d8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a34 : bv 32 := @BV 32 0x00096517%Z I.
Lemma F_70a34 : fetch_word Asan.M.loaded_segments (@BV 64 0x70a3c%Z I : word) = Some W_70a34.
Proof. vm_refl. Qed.
Lemma D_70a34 : decode_any W_70a34 = Some (Auipc (@BV 5 10%Z I) (@BV 20 150%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a38 : bv 32 := @BV 32 0x3a450513%Z I.
Lemma F_70a38 : fetch_word Asan.M.loaded_segments (@BV 64 0x70a40%Z I : word) = Some W_70a38.
Proof. vm_refl. Qed.
Lemma D_70a38 : decode_any W_70a38 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 932%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a3c : bv 32 := @BV 32 0x00054583%Z I.
Lemma F_70a3c : fetch_word Asan.M.loaded_segments (@BV 64 0x70a44%Z I : word) = Some W_70a3c.
Proof. vm_refl. Qed.
Lemma D_70a3c : decode_any W_70a3c = Some (Load SZ1 false (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a40 : bv 32 := @BV 32 0x00058663%Z I.
Lemma F_70a40 : fetch_word Asan.M.loaded_segments (@BV 64 0x70a48%Z I : word) = Some W_70a40.
Proof. vm_refl. Qed.
Lemma D_70a40 : decode_any W_70a40 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a44 : bv 32 := @BV 32 0x00452503%Z I.
Lemma F_70a44 : fetch_word Asan.M.loaded_segments (@BV 64 0x70a4c%Z I : word) = Some W_70a44.
Proof. vm_refl. Qed.
Lemma D_70a44 : decode_any W_70a44 = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a48 : bv 32 := @BV 32 0x6208606f%Z I.
Lemma F_70a48 : fetch_word Asan.M.loaded_segments (@BV 64 0x70a50%Z I : word) = Some W_70a48.
Proof. vm_refl. Qed.
Lemma D_70a48 : decode_any W_70a48 = Some (Jal (@BV 5 0%Z I) (@BV 21 550432%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a54 : bv 32 := @BV 32 0xfffab517%Z I.
Lemma F_70a54 : fetch_word Asan.M.loaded_segments (@BV 64 0x70a5c%Z I : word) = Some W_70a54.
Proof. vm_refl. Qed.
Lemma D_70a54 : decode_any W_70a54 = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048491%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a58 : bv 32 := @BV 32 0xfffa1597%Z I.
Lemma F_70a58 : fetch_word Asan.M.loaded_segments (@BV 64 0x70a60%Z I : word) = Some W_70a58.
Proof. vm_refl. Qed.
Lemma D_70a58 : decode_any W_70a58 = Some (Auipc (@BV 5 11%Z I) (@BV 20 1048481%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a5c : bv 32 := @BV 32 0x1bf50513%Z I.
Lemma F_70a5c : fetch_word Asan.M.loaded_segments (@BV 64 0x70a64%Z I : word) = Some W_70a5c.
Proof. vm_refl. Qed.
Lemma D_70a5c : decode_any W_70a5c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 447%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a60 : bv 32 := @BV 32 0xfe258613%Z I.
Lemma F_70a60 : fetch_word Asan.M.loaded_segments (@BV 64 0x70a68%Z I : word) = Some W_70a60.
Proof. vm_refl. Qed.
Lemma D_70a60 : decode_any W_70a60 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 12 4066%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a78 : bv 32 := @BV 32 0x36458613%Z I.
Lemma F_70a78 : fetch_word Asan.M.loaded_segments (@BV 64 0x70a80%Z I : word) = Some W_70a78.
Proof. vm_refl. Qed.
Lemma D_70a78 : decode_any W_70a78 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 12 868%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a7c : bv 32 := @BV 32 0x00064683%Z I.
Lemma F_70a7c : fetch_word Asan.M.loaded_segments (@BV 64 0x70a84%Z I : word) = Some W_70a7c.
Proof. vm_refl. Qed.
Lemma D_70a7c : decode_any W_70a7c = Some (Load SZ1 false (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70a9c : bv 32 := @BV 32 0xfffa1597%Z I.
Lemma F_70a9c : fetch_word Asan.M.loaded_segments (@BV 64 0x70aa4%Z I : word) = Some W_70a9c.
Proof. vm_refl. Qed.
Lemma D_70a9c : decode_any W_70a9c = Some (Auipc (@BV 5 11%Z I) (@BV 20 1048481%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70aa0 : bv 32 := @BV 32 0x17b50513%Z I.
Lemma F_70aa0 : fetch_word Asan.M.loaded_segments (@BV 64 0x70aa8%Z I : word) = Some W_70aa0.
Proof. vm_refl. Qed.
Lemma D_70aa0 : decode_any W_70aa0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 379%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70aa4 : bv 32 := @BV 32 0xf9e58613%Z I.
Lemma F_70aa4 : fetch_word Asan.M.loaded_segments (@BV 64 0x70aac%Z I : word) = Some W_70aa4.
Proof. vm_refl. Qed.
Lemma D_70aa4 : decode_any W_70aa4 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 12 3998%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70aa8 : bv 32 := @BV 32 0x08b00593%Z I.
Lemma F_70aa8 : fetch_word Asan.M.loaded_segments (@BV 64 0x70ab0%Z I : word) = Some W_70aa8.
Proof. vm_refl. Qed.
Lemma D_70aa8 : decode_any W_70aa8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 139%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70ac0 : bv 32 := @BV 32 0x00050413%Z I.
Lemma F_70ac0 : fetch_word Asan.M.loaded_segments (@BV 64 0x70ac8%Z I : word) = Some W_70ac0.
Proof. vm_refl. Qed.
Lemma D_70ac0 : decode_any W_70ac0 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_70ac4 : bv 32 := @BV 32 0x09554583%Z I.
Lemma F_70ac4 : fetch_word Asan.M.loaded_segments (@BV 64 0x70acc%Z I : word) = Some W_70ac4.
Proof. vm_refl. Qed.
Lemma D_70ac4 : decode_any W_70ac4 = Some (Load SZ1 false (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 149%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ca4 : bv 32 := @BV 32 0x00093517%Z I.
Lemma F_74ca4 : fetch_word Asan.M.loaded_segments (@BV 64 0x74cac%Z I : word) = Some W_74ca4.
Proof. vm_refl. Qed.
Lemma D_74ca4 : decode_any W_74ca4 = Some (Auipc (@BV 5 10%Z I) (@BV 20 147%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ca8 : bv 32 := @BV 32 0x5ac50503%Z I.
Lemma F_74ca8 : fetch_word Asan.M.loaded_segments (@BV 64 0x74cb0%Z I : word) = Some W_74ca8.
Proof. vm_refl. Qed.
Lemma D_74ca8 : decode_any W_74ca8 = Some (Load SZ1 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1452%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74cac : bv 32 := @BV 32 0x0230000f%Z I.
Lemma F_74cac : fetch_word Asan.M.loaded_segments (@BV 64 0x74cb4%Z I : word) = Some W_74cac.
Proof. vm_refl. Qed.
Lemma D_74cac : decode_any W_74cac = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74cb0 : bv 32 := @BV 32 0xfff50513%Z I.
Lemma F_74cb0 : fetch_word Asan.M.loaded_segments (@BV 64 0x74cb8%Z I : word) = Some W_74cb0.
Proof. vm_refl. Qed.
Lemma D_74cb0 : decode_any W_74cb0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74cb4 : bv 32 := @BV 32 0x00153513%Z I.
Lemma F_74cb4 : fetch_word Asan.M.loaded_segments (@BV 64 0x74cbc%Z I : word) = Some W_74cb4.
Proof. vm_refl. Qed.
Lemma D_74cb4 : decode_any W_74cb4 = Some (OpImm ALU_SLTU (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74cb8 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_74cb8 : fetch_word Asan.M.loaded_segments (@BV 64 0x74cc0%Z I : word) = Some W_74cb8.
Proof. vm_refl. Qed.
Lemma D_74cb8 : decode_any W_74cb8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7571c : bv 32 := @BV 32 0x0035d593%Z I.
Lemma F_7571c : fetch_word Asan.M.loaded_segments (@BV 64 0x75724%Z I : word) = Some W_7571c.
Proof. vm_refl. Qed.
Lemma D_7571c : decode_any W_7571c = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75720 : bv 32 := @BV 32 0x00355513%Z I.
Lemma F_75720 : fetch_word Asan.M.loaded_segments (@BV 64 0x75728%Z I : word) = Some W_75720.
Proof. vm_refl. Qed.
Lemma D_75720 : decode_any W_75720 = Some (ShiftImm ALU_SRL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75724 : bv 32 := @BV 32 0x00c586b3%Z I.
Lemma F_75724 : fetch_word Asan.M.loaded_segments (@BV 64 0x7572c%Z I : word) = Some W_75724.
Proof. vm_refl. Qed.
Lemma D_75724 : decode_any W_75724 = Some (Op ALU_ADD (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75728 : bv 32 := @BV 32 0x00c505b3%Z I.
Lemma F_75728 : fetch_word Asan.M.loaded_segments (@BV 64 0x75730%Z I : word) = Some W_75728.
Proof. vm_refl. Qed.
Lemma D_75728 : decode_any W_75728 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7572c : bv 32 := @BV 32 0x0036d693%Z I.
Lemma F_7572c : fetch_word Asan.M.loaded_segments (@BV 64 0x75734%Z I : word) = Some W_7572c.
Proof. vm_refl. Qed.
Lemma D_7572c : decode_any W_7572c = Some (ShiftImm ALU_SRL (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75730 : bv 32 := @BV 32 0x00c68633%Z I.
Lemma F_75730 : fetch_word Asan.M.loaded_segments (@BV 64 0x75738%Z I : word) = Some W_75730.
Proof. vm_refl. Qed.
Lemma D_75730 : decode_any W_75730 = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 13%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bb4 : bv 32 := @BV 32 0xff010113%Z I.
Lemma F_75bb4 : fetch_word Asan.M.loaded_segments (@BV 64 0x75bbc%Z I : word) = Some W_75bb4.
Proof. vm_refl. Qed.
Lemma D_75bb4 : decode_any W_75bb4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bb8 : bv 32 := @BV 32 0x00113423%Z I.
Lemma F_75bb8 : fetch_word Asan.M.loaded_segments (@BV 64 0x75bc0%Z I : word) = Some W_75bb8.
Proof. vm_refl. Qed.
Lemma D_75bb8 : decode_any W_75bb8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bbc : bv 32 := @BV 32 0x00813023%Z I.
Lemma F_75bbc : fetch_word Asan.M.loaded_segments (@BV 64 0x75bc4%Z I : word) = Some W_75bbc.
Proof. vm_refl. Qed.
Lemma D_75bbc : decode_any W_75bbc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bc0 : bv 32 := @BV 32 0x00092517%Z I.
Lemma F_75bc0 : fetch_word Asan.M.loaded_segments (@BV 64 0x75bc8%Z I : word) = Some W_75bc0.
Proof. vm_refl. Qed.
Lemma D_75bc0 : decode_any W_75bc0 = Some (Auipc (@BV 5 10%Z I) (@BV 20 146%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bc4 : bv 32 := @BV 32 0x69050413%Z I.
Lemma F_75bc4 : fetch_word Asan.M.loaded_segments (@BV 64 0x75bcc%Z I : word) = Some W_75bc4.
Proof. vm_refl. Qed.
Lemma D_75bc4 : decode_any W_75bc4 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 1680%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bc8 : bv 32 := @BV 32 0x00040583%Z I.
Lemma F_75bc8 : fetch_word Asan.M.loaded_segments (@BV 64 0x75bd0%Z I : word) = Some W_75bc8.
Proof. vm_refl. Qed.
Lemma D_75bc8 : decode_any W_75bc8 = Some (Load SZ1 true (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bcc : bv 32 := @BV 32 0x00100513%Z I.
Lemma F_75bcc : fetch_word Asan.M.loaded_segments (@BV 64 0x75bd4%Z I : word) = Some W_75bcc.
Proof. vm_refl. Qed.
Lemma D_75bcc : decode_any W_75bcc = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bd0 : bv 32 := @BV 32 0x0230000f%Z I.
Lemma F_75bd0 : fetch_word Asan.M.loaded_segments (@BV 64 0x75bd8%Z I : word) = Some W_75bd0.
Proof. vm_refl. Qed.
Lemma D_75bd0 : decode_any W_75bd0 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bd4 : bv 32 := @BV 32 0x00a59a63%Z I.
Lemma F_75bd4 : fetch_word Asan.M.loaded_segments (@BV 64 0x75bdc%Z I : word) = Some W_75bd4.
Proof. vm_refl. Qed.
Lemma D_75bd4 : decode_any W_75bd4 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bd8 : bv 32 := @BV 32 0x00813083%Z I.
Lemma F_75bd8 : fetch_word Asan.M.loaded_segments (@BV 64 0x75be0%Z I : word) = Some W_75bd8.
Proof. vm_refl. Qed.
Lemma D_75bd8 : decode_any W_75bd8 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bdc : bv 32 := @BV 32 0x00013403%Z I.
Lemma F_75bdc : fetch_word Asan.M.loaded_segments (@BV 64 0x75be4%Z I : word) = Some W_75bdc.
Proof. vm_refl. Qed.
Lemma D_75bdc : decode_any W_75bdc = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75be0 : bv 32 := @BV 32 0x01010113%Z I.
Lemma F_75be0 : fetch_word Asan.M.loaded_segments (@BV 64 0x75be8%Z I : word) = Some W_75be0.
Proof. vm_refl. Qed.
Lemma D_75be0 : decode_any W_75be0 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75be4 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_75be4 : fetch_word Asan.M.loaded_segments (@BV 64 0x75bec%Z I : word) = Some W_75be4.
Proof. vm_refl. Qed.
Lemma D_75be4 : decode_any W_75be4 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7662c : bv 32 := @BV 32 0x04813023%Z I.
Lemma F_7662c : fetch_word Asan.M.loaded_segments (@BV 64 0x76634%Z I : word) = Some W_7662c.
Proof. vm_refl. Qed.
Lemma D_7662c : decode_any W_7662c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76630 : bv 32 := @BV 32 0x02913c23%Z I.
Lemma F_76630 : fetch_word Asan.M.loaded_segments (@BV 64 0x76638%Z I : word) = Some W_76630.
Proof. vm_refl. Qed.
Lemma D_76630 : decode_any W_76630 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76634 : bv 32 := @BV 32 0x03213823%Z I.
Lemma F_76634 : fetch_word Asan.M.loaded_segments (@BV 64 0x7663c%Z I : word) = Some W_76634.
Proof. vm_refl. Qed.
Lemma D_76634 : decode_any W_76634 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76638 : bv 32 := @BV 32 0x03313423%Z I.
Lemma F_76638 : fetch_word Asan.M.loaded_segments (@BV 64 0x76640%Z I : word) = Some W_76638.
Proof. vm_refl. Qed.
Lemma D_76638 : decode_any W_76638 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7663c : bv 32 := @BV 32 0x03413023%Z I.
Lemma F_7663c : fetch_word Asan.M.loaded_segments (@BV 64 0x76644%Z I : word) = Some W_7663c.
Proof. vm_refl. Qed.
Lemma D_7663c : decode_any W_7663c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76640 : bv 32 := @BV 32 0x01513c23%Z I.
Lemma F_76640 : fetch_word Asan.M.loaded_segments (@BV 64 0x76648%Z I : word) = Some W_76640.
Proof. vm_refl. Qed.
Lemma D_76640 : decode_any W_76640 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76644 : bv 32 := @BV 32 0x01613823%Z I.
Lemma F_76644 : fetch_word Asan.M.loaded_segments (@BV 64 0x7664c%Z I : word) = Some W_76644.
Proof. vm_refl. Qed.
Lemma D_76644 : decode_any W_76644 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 22%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76648 : bv 32 := @BV 32 0x01713423%Z I.
Lemma F_76648 : fetch_word Asan.M.loaded_segments (@BV 64 0x76650%Z I : word) = Some W_76648.
Proof. vm_refl. Qed.
Lemma D_76648 : decode_any W_76648 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 23%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7664c : bv 32 := @BV 32 0x01813023%Z I.
Lemma F_7664c : fetch_word Asan.M.loaded_segments (@BV 64 0x76654%Z I : word) = Some W_7664c.
Proof. vm_refl. Qed.
Lemma D_7664c : decode_any W_7664c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 24%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76650 : bv 32 := @BV 32 0x00089517%Z I.
Lemma F_76650 : fetch_word Asan.M.loaded_segments (@BV 64 0x76658%Z I : word) = Some W_76650.
Proof. vm_refl. Qed.
Lemma D_76650 : decode_any W_76650 = Some (Auipc (@BV 5 10%Z I) (@BV 20 137%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76654 : bv 32 := @BV 32 0xc1853983%Z I.
Lemma F_76654 : fetch_word Asan.M.loaded_segments (@BV 64 0x7665c%Z I : word) = Some W_76654.
Proof. vm_refl. Qed.
Lemma D_76654 : decode_any W_76654 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 3096%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76658 : bv 32 := @BV 32 0xfff00513%Z I.
Lemma F_76658 : fetch_word Asan.M.loaded_segments (@BV 64 0x76660%Z I : word) = Some W_76658.
Proof. vm_refl. Qed.
Lemma D_76658 : decode_any W_76658 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7665c : bv 32 := @BV 32 0x00a9b023%Z I.
Lemma F_7665c : fetch_word Asan.M.loaded_segments (@BV 64 0x76664%Z I : word) = Some W_7665c.
Proof. vm_refl. Qed.
Lemma D_7665c : decode_any W_7665c = Some (Store SZ8 (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7693c : bv 32 := @BV 32 0x00092517%Z I.
Lemma F_7693c : fetch_word Asan.M.loaded_segments (@BV 64 0x76944%Z I : word) = Some W_7693c.
Proof. vm_refl. Qed.
Lemma D_7693c : decode_any W_7693c = Some (Auipc (@BV 5 10%Z I) (@BV 20 146%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76940 : bv 32 := @BV 32 0x93852503%Z I.
Lemma F_76940 : fetch_word Asan.M.loaded_segments (@BV 64 0x76948%Z I : word) = Some W_76940.
Proof. vm_refl. Qed.
Lemma D_76940 : decode_any W_76940 = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2360%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76944 : bv 32 := @BV 32 0x0230000f%Z I.
Lemma F_76944 : fetch_word Asan.M.loaded_segments (@BV 64 0x7694c%Z I : word) = Some W_76944.
Proof. vm_refl. Qed.
Lemma D_76944 : decode_any W_76944 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76948 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_76948 : fetch_word Asan.M.loaded_segments (@BV 64 0x76950%Z I : word) = Some W_76948.
Proof. vm_refl. Qed.
Lemma D_76948 : decode_any W_76948 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7694c : bv 32 := @BV 32 0xfb010113%Z I.

Lemma D_7694c : decode_any W_7694c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76950 : bv 32 := @BV 32 0x04113423%Z I.

Lemma D_76950 : decode_any W_76950 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76954 : bv 32 := @BV 32 0x04813023%Z I.

Lemma D_76954 : decode_any W_76954 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76958 : bv 32 := @BV 32 0x02913c23%Z I.

Lemma D_76958 : decode_any W_76958 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7695c : bv 32 := @BV 32 0x03213823%Z I.

Lemma D_7695c : decode_any W_7695c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76960 : bv 32 := @BV 32 0x03313423%Z I.

Lemma D_76960 : decode_any W_76960 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76964 : bv 32 := @BV 32 0x03413023%Z I.

Lemma D_76964 : decode_any W_76964 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76968 : bv 32 := @BV 32 0x01513c23%Z I.

Lemma D_76968 : decode_any W_76968 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7696c : bv 32 := @BV 32 0x01613823%Z I.

Lemma D_7696c : decode_any W_7696c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 22%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76970 : bv 32 := @BV 32 0x01713423%Z I.

Lemma D_76970 : decode_any W_76970 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 23%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76974 : bv 32 := @BV 32 0x01813023%Z I.

Lemma D_76974 : decode_any W_76974 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 24%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76978 : bv 32 := @BV 32 0x00078493%Z I.

Lemma D_76978 : decode_any W_76978 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 15%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7697c : bv 32 := @BV 32 0x00070a93%Z I.

Lemma D_7697c : decode_any W_7697c = Some (OpImm ALU_ADD (@BV 5 21%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76980 : bv 32 := @BV 32 0x00068a13%Z I.

Lemma D_76980 : decode_any W_76980 = Some (OpImm ALU_ADD (@BV 5 20%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76984 : bv 32 := @BV 32 0x00060413%Z I.

Lemma D_76984 : decode_any W_76984 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76988 : bv 32 := @BV 32 0x00058913%Z I.

Lemma D_76988 : decode_any W_76988 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7698c : bv 32 := @BV 32 0x00050993%Z I.

Lemma D_7698c : decode_any W_7698c = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76990 : bv 32 := @BV 32 0x00052423%Z I.

Lemma D_76990 : decode_any W_76990 = Some (Store SZ4 (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76994 : bv 32 := @BV 32 0xb10fe0ef%Z I.

Lemma D_76994 : decode_any W_76994 = Some (Jal (@BV 5 1%Z I) (@BV 21 2089744%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76998 : bv 32 := @BV 32 0x0c050a63%Z I.

Lemma D_76998 : decode_any W_76998 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 212%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7699c : bv 32 := @BV 32 0x219010ef%Z I.

Lemma D_7699c : decode_any W_7699c = Some (Jal (@BV 5 1%Z I) (@BV 21 6680%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769a0 : bv 32 := @BV 32 0x04050a63%Z I.

Lemma D_769a0 : decode_any W_769a0 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 84%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769a4 : bv 32 := @BV 32 0x7ff50c13%Z I.

Lemma D_769a4 : decode_any W_769a4 = Some (OpImm ALU_ADD (@BV 5 24%Z I) (@BV 5 10%Z I) (@BV 12 2047%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769a8 : bv 32 := @BV 32 0x461c4583%Z I.

Lemma D_769a8 : decode_any W_769a8 = Some (Load SZ1 false (@BV 5 11%Z I) (@BV 5 24%Z I) (@BV 12 1121%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769ac : bv 32 := @BV 32 0x00100613%Z I.

Lemma D_769ac : decode_any W_769ac = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769b0 : bv 32 := @BV 32 0x46cc00a3%Z I.

Lemma D_769b0 : decode_any W_769b0 = Some (Store SZ1 (@BV 5 24%Z I) (@BV 5 12%Z I) (@BV 12 1121%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769b4 : bv 32 := @BV 32 0x0a059a63%Z I.

Lemma D_769b4 : decode_any W_769b4 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769b8 : bv 32 := @BV 32 0x00050b93%Z I.

Lemma D_769b8 : decode_any W_769b8 = Some (OpImm ALU_ADD (@BV 5 23%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769bc : bv 32 := @BV 32 0x3bd010ef%Z I.

Lemma D_769bc : decode_any W_769bc = Some (Jal (@BV 5 1%Z I) (@BV 21 7100%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769c0 : bv 32 := @BV 32 0x00050b13%Z I.

Lemma D_769c0 : decode_any W_769c0 = Some (OpImm ALU_ADD (@BV 5 22%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769c4 : bv 32 := @BV 32 0x000b8513%Z I.

Lemma D_769c4 : decode_any W_769c4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 23%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769c8 : bv 32 := @BV 32 0x409010ef%Z I.

Lemma D_769c8 : decode_any W_769c8 = Some (Jal (@BV 5 1%Z I) (@BV 21 7176%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769cc : bv 32 := @BV 32 0x00050813%Z I.

Lemma D_769cc : decode_any W_769cc = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769d0 : bv 32 := @BV 32 0x060a8c63%Z I.

Lemma D_769d0 : decode_any W_769d0 = Some (Branch BC_EQ (@BV 5 21%Z I) (@BV 5 0%Z I) (@BV 13 120%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769d4 : bv 32 := @BV 32 0x00100893%Z I.

Lemma D_769d4 : decode_any W_769d4 = Some (OpImm ALU_ADD (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769d8 : bv 32 := @BV 32 0x00098513%Z I.

Lemma D_769d8 : decode_any W_769d8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769dc : bv 32 := @BV 32 0x00048593%Z I.

Lemma D_769dc : decode_any W_769dc = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769e0 : bv 32 := @BV 32 0x00090613%Z I.

Lemma D_769e0 : decode_any W_769e0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769e4 : bv 32 := @BV 32 0x00040693%Z I.

Lemma D_769e4 : decode_any W_769e4 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769e8 : bv 32 := @BV 32 0x00000713%Z I.

Lemma D_769e8 : decode_any W_769e8 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769ec : bv 32 := @BV 32 0x000b0793%Z I.

Lemma D_769ec : decode_any W_769ec = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 22%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769f0 : bv 32 := @BV 32 0x0740006f%Z I.

Lemma D_769f0 : decode_any W_769f0 = Some (Jal (@BV 5 0%Z I) (@BV 21 116%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_769f4 : bv 32 := @BV 32 0x060a9c63%Z I.



(* [comment removed for export] *)
Definition W_769f8 : bv 32 := @BV 32 0x00098513%Z I.



(* [comment removed for export] *)
Definition W_769fc : bv 32 := @BV 32 0x00048593%Z I.



(* [comment removed for export] *)
Definition W_76a00 : bv 32 := @BV 32 0x00090613%Z I.



(* [comment removed for export] *)
Definition W_76a04 : bv 32 := @BV 32 0x00040693%Z I.



(* [comment removed for export] *)
Definition W_76a08 : bv 32 := @BV 32 0x000a0713%Z I.



(* [comment removed for export] *)
Definition W_76a0c : bv 32 := @BV 32 0x00000793%Z I.



(* [comment removed for export] *)
Definition W_76a10 : bv 32 := @BV 32 0x00000813%Z I.



(* [comment removed for export] *)
Definition W_76a14 : bv 32 := @BV 32 0x00000893%Z I.



(* [comment removed for export] *)
Definition W_76a18 : bv 32 := @BV 32 0x04813083%Z I.



(* [comment removed for export] *)
Definition W_76a1c : bv 32 := @BV 32 0x04013403%Z I.



(* [comment removed for export] *)
Definition W_76a20 : bv 32 := @BV 32 0x03813483%Z I.



(* [comment removed for export] *)
Definition W_76a24 : bv 32 := @BV 32 0x03013903%Z I.



(* [comment removed for export] *)
Definition W_76a28 : bv 32 := @BV 32 0x02813983%Z I.



(* [comment removed for export] *)
Definition W_76a2c : bv 32 := @BV 32 0x02013a03%Z I.



(* [comment removed for export] *)
Definition W_76a30 : bv 32 := @BV 32 0x01813a83%Z I.



(* [comment removed for export] *)
Definition W_76a34 : bv 32 := @BV 32 0x01013b03%Z I.



(* [comment removed for export] *)
Definition W_76a38 : bv 32 := @BV 32 0x00813b83%Z I.



(* [comment removed for export] *)
Definition W_76a3c : bv 32 := @BV 32 0x00013c03%Z I.



(* [comment removed for export] *)
Definition W_76a40 : bv 32 := @BV 32 0x05010113%Z I.



(* [comment removed for export] *)
Definition W_76a44 : bv 32 := @BV 32 0x01c1906f%Z I.



(* [comment removed for export] *)
Definition W_76a48 : bv 32 := @BV 32 0x00098513%Z I.



(* [comment removed for export] *)
Definition W_76a4c : bv 32 := @BV 32 0x00048593%Z I.



(* [comment removed for export] *)
Definition W_76a50 : bv 32 := @BV 32 0x00090613%Z I.



(* [comment removed for export] *)
Definition W_76a54 : bv 32 := @BV 32 0x00040693%Z I.



(* [comment removed for export] *)
Definition W_76a58 : bv 32 := @BV 32 0x000a0713%Z I.



(* [comment removed for export] *)
Definition W_76a5c : bv 32 := @BV 32 0x000b0793%Z I.



(* [comment removed for export] *)
Definition W_76a60 : bv 32 := @BV 32 0x00000893%Z I.



(* [comment removed for export] *)
Definition W_76a64 : bv 32 := @BV 32 0x7fd180ef%Z I.

Lemma D_76a64 : decode_any W_76a64 = Some (Jal (@BV 5 1%Z I) (@BV 21 102396%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76a68 : bv 32 := @BV 32 0x460c00a3%Z I.

Lemma D_76a68 : decode_any W_76a68 = Some (Store SZ1 (@BV 5 24%Z I) (@BV 5 0%Z I) (@BV 12 1121%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76a6c : bv 32 := @BV 32 0x04813083%Z I.

Lemma D_76a6c : decode_any W_76a6c = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76a70 : bv 32 := @BV 32 0x04013403%Z I.

Lemma D_76a70 : decode_any W_76a70 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76a74 : bv 32 := @BV 32 0x03813483%Z I.

Lemma D_76a74 : decode_any W_76a74 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76a78 : bv 32 := @BV 32 0x03013903%Z I.

Lemma D_76a78 : decode_any W_76a78 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76a7c : bv 32 := @BV 32 0x02813983%Z I.

Lemma D_76a7c : decode_any W_76a7c = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76a80 : bv 32 := @BV 32 0x02013a03%Z I.

Lemma D_76a80 : decode_any W_76a80 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76a84 : bv 32 := @BV 32 0x01813a83%Z I.

Lemma D_76a84 : decode_any W_76a84 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76a88 : bv 32 := @BV 32 0x01013b03%Z I.

Lemma D_76a88 : decode_any W_76a88 = Some (Load SZ8 true (@BV 5 22%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76a8c : bv 32 := @BV 32 0x00813b83%Z I.

Lemma D_76a8c : decode_any W_76a8c = Some (Load SZ8 true (@BV 5 23%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76a90 : bv 32 := @BV 32 0x00013c03%Z I.

Lemma D_76a90 : decode_any W_76a90 = Some (Load SZ8 true (@BV 5 24%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76a94 : bv 32 := @BV 32 0x05010113%Z I.

Lemma D_76a94 : decode_any W_76a94 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76a98 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_76a98 : decode_any W_76a98 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77580 : bv 32 := @BV 32 0xff010113%Z I.
Lemma F_77580 : fetch_word Asan.M.loaded_segments (@BV 64 0x77588%Z I : word) = Some W_77580.
Proof. vm_refl. Qed.
Lemma D_77580 : decode_any W_77580 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77584 : bv 32 := @BV 32 0x00113423%Z I.
Lemma F_77584 : fetch_word Asan.M.loaded_segments (@BV 64 0x7758c%Z I : word) = Some W_77584.
Proof. vm_refl. Qed.
Lemma D_77584 : decode_any W_77584 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77588 : bv 32 := @BV 32 0x62d000ef%Z I.
Lemma F_77588 : fetch_word Asan.M.loaded_segments (@BV 64 0x77590%Z I : word) = Some W_77588.
Proof. vm_refl. Qed.
Lemma D_77588 : decode_any W_77588 = Some (Jal (@BV 5 1%Z I) (@BV 21 3628%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7758c : bv 32 := @BV 32 0x00050c63%Z I.
Lemma F_7758c : fetch_word Asan.M.loaded_segments (@BV 64 0x77594%Z I : word) = Some W_7758c.
Proof. vm_refl. Qed.
Lemma D_7758c : decode_any W_7758c = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77590 : bv 32 := @BV 32 0x7ff50513%Z I.
Lemma F_77590 : fetch_word Asan.M.loaded_segments (@BV 64 0x77598%Z I : word) = Some W_77590.
Proof. vm_refl. Qed.
Lemma D_77590 : decode_any W_77590 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2047%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77594 : bv 32 := @BV 32 0x2f150513%Z I.
Lemma F_77594 : fetch_word Asan.M.loaded_segments (@BV 64 0x7759c%Z I : word) = Some W_77594.
Proof. vm_refl. Qed.
Lemma D_77594 : decode_any W_77594 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 753%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77598 : bv 32 := @BV 32 0x00813083%Z I.
Lemma F_77598 : fetch_word Asan.M.loaded_segments (@BV 64 0x775a0%Z I : word) = Some W_77598.
Proof. vm_refl. Qed.
Lemma D_77598 : decode_any W_77598 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7759c : bv 32 := @BV 32 0x01010113%Z I.
Lemma F_7759c : fetch_word Asan.M.loaded_segments (@BV 64 0x775a4%Z I : word) = Some W_7759c.
Proof. vm_refl. Qed.
Lemma D_7759c : decode_any W_7759c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_775a0 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_775a0 : fetch_word Asan.M.loaded_segments (@BV 64 0x775a8%Z I : word) = Some W_775a0.
Proof. vm_refl. Qed.
Lemma D_775a0 : decode_any W_775a0 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ff8 : bv 32 := @BV 32 0xfff58513%Z I.
Lemma F_77ff8 : fetch_word Asan.M.loaded_segments (@BV 64 0x78000%Z I : word) = Some W_77ff8.
Proof. vm_refl. Qed.
Lemma D_77ff8 : decode_any W_77ff8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ffc : bv 32 := @BV 32 0x00a5f533%Z I.
Lemma F_77ffc : fetch_word Asan.M.loaded_segments (@BV 64 0x78004%Z I : word) = Some W_77ffc.
Proof. vm_refl. Qed.
Lemma D_77ffc : decode_any W_77ffc = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78000 : bv 32 := @BV 32 0x06051e63%Z I.
Lemma F_78000 : fetch_word Asan.M.loaded_segments (@BV 64 0x78008%Z I : word) = Some W_78000.
Proof. vm_refl. Qed.
Lemma D_78000 : decode_any W_78000 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78004 : bv 32 := @BV 32 0x7ff58513%Z I.
Lemma F_78004 : fetch_word Asan.M.loaded_segments (@BV 64 0x7800c%Z I : word) = Some W_78004.
Proof. vm_refl. Qed.
Lemma D_78004 : decode_any W_78004 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 2047%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78008 : bv 32 := @BV 32 0x47050513%Z I.
Lemma F_78008 : fetch_word Asan.M.loaded_segments (@BV 64 0x78010%Z I : word) = Some W_78008.
Proof. vm_refl. Qed.
Lemma D_78008 : decode_any W_78008 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1136%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7800c : bv 32 := @BV 32 0x40b005b3%Z I.
Lemma F_7800c : fetch_word Asan.M.loaded_segments (@BV 64 0x78014%Z I : word) = Some W_7800c.
Proof. vm_refl. Qed.
Lemma D_7800c : decode_any W_7800c = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78010 : bv 32 := @BV 32 0x00b57b33%Z I.
Lemma F_78010 : fetch_word Asan.M.loaded_segments (@BV 64 0x78018%Z I : word) = Some W_78010.
Proof. vm_refl. Qed.
Lemma D_78010 : decode_any W_78010 = Some (Op ALU_AND (@BV 5 22%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78014 : bv 32 := @BV 32 0xfffa8517%Z I.
Lemma F_78014 : fetch_word Asan.M.loaded_segments (@BV 64 0x7801c%Z I : word) = Some W_78014.
Proof. vm_refl. Qed.
Lemma D_78014 : decode_any W_78014 = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048488%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78018 : bv 32 := @BV 32 0x9ac50593%Z I.
Lemma F_78018 : fetch_word Asan.M.loaded_segments (@BV 64 0x78020%Z I : word) = Some W_78018.
Proof. vm_refl. Qed.
Lemma D_78018 : decode_any W_78018 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 2476%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_783b4 : bv 32 := @BV 32 0xff010113%Z I.
Lemma F_783b4 : fetch_word Asan.M.loaded_segments (@BV 64 0x783bc%Z I : word) = Some W_783b4.
Proof. vm_refl. Qed.
Lemma D_783b4 : decode_any W_783b4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_783b8 : bv 32 := @BV 32 0x00113423%Z I.
Lemma F_783b8 : fetch_word Asan.M.loaded_segments (@BV 64 0x783c0%Z I : word) = Some W_783b8.
Proof. vm_refl. Qed.
Lemma D_783b8 : decode_any W_783b8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_783bc : bv 32 := @BV 32 0xe78f80ef%Z I.
Lemma F_783bc : fetch_word Asan.M.loaded_segments (@BV 64 0x783c4%Z I : word) = Some W_783bc.
Proof. vm_refl. Qed.
Lemma D_783bc : decode_any W_783bc = Some (Jal (@BV 5 1%Z I) (@BV 21 2066040%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_783c0 : bv 32 := @BV 32 0x00050463%Z I.
Lemma F_783c0 : fetch_word Asan.M.loaded_segments (@BV 64 0x783c8%Z I : word) = Some W_783c0.
Proof. vm_refl. Qed.
Lemma D_783c0 : decode_any W_783c0 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_783c4 : bv 32 := @BV 32 0x09853503%Z I.
Lemma F_783c4 : fetch_word Asan.M.loaded_segments (@BV 64 0x783cc%Z I : word) = Some W_783c4.
Proof. vm_refl. Qed.
Lemma D_783c4 : decode_any W_783c4 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_783c8 : bv 32 := @BV 32 0x00813083%Z I.
Lemma F_783c8 : fetch_word Asan.M.loaded_segments (@BV 64 0x783d0%Z I : word) = Some W_783c8.
Proof. vm_refl. Qed.
Lemma D_783c8 : decode_any W_783c8 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_783cc : bv 32 := @BV 32 0x01010113%Z I.
Lemma F_783cc : fetch_word Asan.M.loaded_segments (@BV 64 0x783d4%Z I : word) = Some W_783cc.
Proof. vm_refl. Qed.
Lemma D_783cc : decode_any W_783cc = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_783d0 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_783d0 : fetch_word Asan.M.loaded_segments (@BV 64 0x783d8%Z I : word) = Some W_783d0.
Proof. vm_refl. Qed.
Lemma D_783d0 : decode_any W_783d0 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78578 : bv 32 := @BV 32 0x02850583%Z I.

Lemma D_78578 : decode_any W_78578 = Some (Load SZ1 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7857c : bv 32 := @BV 32 0x0230000f%Z I.

Lemma D_7857c : decode_any W_7857c = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78580 : bv 32 := @BV 32 0x02058c63%Z I.

Lemma D_78580 : decode_any W_78580 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785b8 : bv 32 := @BV 32 0x00853583%Z I.

Lemma D_785b8 : decode_any W_785b8 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785bc : bv 32 := @BV 32 0x01053503%Z I.

Lemma D_785bc : decode_any W_785bc = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785c0 : bv 32 := @BV 32 0x00b53533%Z I.

Lemma D_785c0 : decode_any W_785c0 = Some (Op ALU_SLTU (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785c4 : bv 32 := @BV 32 0x40a00533%Z I.

Lemma D_785c4 : decode_any W_785c4 = Some (Op ALU_SUB (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785c8 : bv 32 := @BV 32 0x00b57533%Z I.

Lemma D_785c8 : decode_any W_785c8 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785cc : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_785cc : decode_any W_785cc = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785d0 : bv 32 := @BV 32 0x02850583%Z I.

Lemma D_785d0 : decode_any W_785d0 = Some (Load SZ1 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785d4 : bv 32 := @BV 32 0x0230000f%Z I.

Lemma D_785d4 : decode_any W_785d4 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_785d8 : bv 32 := @BV 32 0x02058c63%Z I.

Lemma D_785d8 : decode_any W_785d8 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78610 : bv 32 := @BV 32 0x00853583%Z I.

Lemma D_78610 : decode_any W_78610 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78614 : bv 32 := @BV 32 0x01053503%Z I.

Lemma D_78614 : decode_any W_78614 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78618 : bv 32 := @BV 32 0x00b535b3%Z I.

Lemma D_78618 : decode_any W_78618 = Some (Op ALU_SLTU (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7861c : bv 32 := @BV 32 0x40b005b3%Z I.

Lemma D_7861c : decode_any W_7861c = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78620 : bv 32 := @BV 32 0x00a5f533%Z I.

Lemma D_78620 : decode_any W_78620 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78624 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_78624 : decode_any W_78624 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

















































(* [comment removed for export] *)
Definition W_7a430 : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_7a430 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a438%Z I : word) = Some W_7a430.
Proof. vm_refl. Qed.
Lemma D_7a430 : decode_any W_7a430 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a434 : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_7a434 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a43c%Z I : word) = Some W_7a434.
Proof. vm_refl. Qed.
Lemma D_7a434 : decode_any W_7a434 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a438 : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_7a438 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a440%Z I : word) = Some W_7a438.
Proof. vm_refl. Qed.
Lemma D_7a438 : decode_any W_7a438 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a43c : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_7a43c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a444%Z I : word) = Some W_7a43c.
Proof. vm_refl. Qed.
Lemma D_7a43c : decode_any W_7a43c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a440 : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_7a440 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a448%Z I : word) = Some W_7a440.
Proof. vm_refl. Qed.
Lemma D_7a440 : decode_any W_7a440 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a444 : bv 32 := @BV 32 0x01313423%Z I.
Lemma F_7a444 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a44c%Z I : word) = Some W_7a444.
Proof. vm_refl. Qed.
Lemma D_7a444 : decode_any W_7a444 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a448 : bv 32 := @BV 32 0x0011d517%Z I.
Lemma F_7a448 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a450%Z I : word) = Some W_7a448.
Proof. vm_refl. Qed.
Lemma D_7a448 : decode_any W_7a448 = Some (Auipc (@BV 5 10%Z I) (@BV 20 285%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a44c : bv 32 := @BV 32 0xbb850413%Z I.
Lemma F_7a44c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a454%Z I : word) = Some W_7a44c.
Proof. vm_refl. Qed.
Lemma D_7a44c : decode_any W_7a44c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 3000%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a450 : bv 32 := @BV 32 0x00040503%Z I.
Lemma F_7a450 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a458%Z I : word) = Some W_7a450.
Proof. vm_refl. Qed.
Lemma D_7a450 : decode_any W_7a450 = Some (Load SZ1 true (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a454 : bv 32 := @BV 32 0x0230000f%Z I.
Lemma F_7a454 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a45c%Z I : word) = Some W_7a454.
Proof. vm_refl. Qed.
Lemma D_7a454 : decode_any W_7a454 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a458 : bv 32 := @BV 32 0x0e051e63%Z I.
Lemma F_7a458 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a460%Z I : word) = Some W_7a458.
Proof. vm_refl. Qed.
Lemma D_7a458 : decode_any W_7a458 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 252%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a45c : bv 32 := @BV 32 0x00140513%Z I.
Lemma F_7a45c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a464%Z I : word) = Some W_7a45c.
Proof. vm_refl. Qed.
Lemma D_7a45c : decode_any W_7a45c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a460 : bv 32 := @BV 32 0x0ff00593%Z I.
Lemma F_7a460 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a468%Z I : word) = Some W_7a460.
Proof. vm_refl. Qed.
Lemma D_7a460 : decode_any W_7a460 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 255%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a464 : bv 32 := @BV 32 0x00100613%Z I.
Lemma F_7a464 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a46c%Z I : word) = Some W_7a464.
Proof. vm_refl. Qed.
Lemma D_7a464 : decode_any W_7a464 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a468 : bv 32 := @BV 32 0xffc57693%Z I.
Lemma F_7a468 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a470%Z I : word) = Some W_7a468.
Proof. vm_refl. Qed.
Lemma D_7a468 : decode_any W_7a468 = Some (OpImm ALU_AND (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 4092%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a46c : bv 32 := @BV 32 0x00357713%Z I.
Lemma F_7a46c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a474%Z I : word) = Some W_7a46c.
Proof. vm_refl. Qed.
Lemma D_7a46c : decode_any W_7a46c = Some (OpImm ALU_AND (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a470 : bv 32 := @BV 32 0x00371713%Z I.
Lemma F_7a470 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a478%Z I : word) = Some W_7a470.
Proof. vm_refl. Qed.
Lemma D_7a470 : decode_any W_7a470 = Some (ShiftImm ALU_SLL (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a474 : bv 32 := @BV 32 0x00e595bb%Z I.
Lemma F_7a474 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a47c%Z I : word) = Some W_7a474.
Proof. vm_refl. Qed.
Lemma D_7a474 : decode_any W_7a474 = Some (Op32 ALU_SLL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a478 : bv 32 := @BV 32 0x00e6163b%Z I.
Lemma F_7a478 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a480%Z I : word) = Some W_7a478.
Proof. vm_refl. Qed.
Lemma D_7a478 : decode_any W_7a478 = Some (Op32 ALU_SLL (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a47c : bv 32 := @BV 32 0x1406a7af%Z I.
Lemma F_7a47c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a484%Z I : word) = Some W_7a47c.
Proof. vm_refl. Qed.
Lemma D_7a47c : decode_any W_7a47c = Some (Lr AW true false (@BV 5 15%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a480 : bv 32 := @BV 32 0x00060813%Z I.
Lemma F_7a480 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a488%Z I : word) = Some W_7a480.
Proof. vm_refl. Qed.
Lemma D_7a480 : decode_any W_7a480 = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a484 : bv 32 := @BV 32 0x0107c833%Z I.
Lemma F_7a484 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a48c%Z I : word) = Some W_7a484.
Proof. vm_refl. Qed.
Lemma D_7a484 : decode_any W_7a484 = Some (Op ALU_XOR (@BV 5 16%Z I) (@BV 5 15%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a488 : bv 32 := @BV 32 0x00b87833%Z I.
Lemma F_7a488 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a490%Z I : word) = Some W_7a488.
Proof. vm_refl. Qed.
Lemma D_7a488 : decode_any W_7a488 = Some (Op ALU_AND (@BV 5 16%Z I) (@BV 5 16%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a48c : bv 32 := @BV 32 0x0107c833%Z I.
Lemma F_7a48c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a494%Z I : word) = Some W_7a48c.
Proof. vm_refl. Qed.
Lemma D_7a48c : decode_any W_7a48c = Some (Op ALU_XOR (@BV 5 16%Z I) (@BV 5 15%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a490 : bv 32 := @BV 32 0x1906a82f%Z I.
Lemma F_7a490 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a498%Z I : word) = Some W_7a490.
Proof. vm_refl. Qed.
Lemma D_7a490 : decode_any W_7a490 = Some (Sc AW false false (@BV 5 16%Z I) (@BV 5 13%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a494 : bv 32 := @BV 32 0xfe0814e3%Z I.
Lemma F_7a494 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a49c%Z I : word) = Some W_7a494.
Proof. vm_refl. Qed.
Lemma D_7a494 : decode_any W_7a494 = Some (Branch BC_NE (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 13 8168%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a498 : bv 32 := @BV 32 0x00e7d5bb%Z I.
Lemma F_7a498 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4a0%Z I : word) = Some W_7a498.
Proof. vm_refl. Qed.
Lemma D_7a498 : decode_any W_7a498 = Some (Op32 ALU_SRL (@BV 5 11%Z I) (@BV 5 15%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a49c : bv 32 := @BV 32 0x0ff5f593%Z I.
Lemma F_7a49c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4a4%Z I : word) = Some W_7a49c.
Proof. vm_refl. Qed.
Lemma D_7a49c : decode_any W_7a49c = Some (OpImm ALU_AND (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 255%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4a0 : bv 32 := @BV 32 0x0c059c63%Z I.
Lemma F_7a4a0 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4a8%Z I : word) = Some W_7a4a0.
Proof. vm_refl. Qed.
Lemma D_7a4a0 : decode_any W_7a4a0 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 216%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4a4 : bv 32 := @BV 32 0x00040503%Z I.
Lemma F_7a4a4 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4ac%Z I : word) = Some W_7a4a4.
Proof. vm_refl. Qed.
Lemma D_7a4a4 : decode_any W_7a4a4 = Some (Load SZ1 true (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4a8 : bv 32 := @BV 32 0x0a051263%Z I.
Lemma F_7a4a8 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4b0%Z I : word) = Some W_7a4a8.
Proof. vm_refl. Qed.
Lemma D_7a4a8 : decode_any W_7a4a8 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 164%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4ac : bv 32 := @BV 32 0x0008e517%Z I.
Lemma F_7a4ac : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4b4%Z I : word) = Some W_7a4ac.
Proof. vm_refl. Qed.
Lemma D_7a4ac : decode_any W_7a4ac = Some (Auipc (@BV 5 10%Z I) (@BV 20 142%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4b0 : bv 32 := @BV 32 0x000815b7%Z I.
Lemma F_7a4b0 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4b8%Z I : word) = Some W_7a4b0.
Proof. vm_refl. Qed.
Lemma D_7a4b0 : decode_any W_7a4b0 = Some (Lui (@BV 5 11%Z I) (@BV 20 129%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4b4 : bv 32 := @BV 32 0x2cc50493%Z I.
Lemma F_7a4b4 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4bc%Z I : word) = Some W_7a4b4.
Proof. vm_refl. Qed.
Lemma D_7a4b4 : decode_any W_7a4b4 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 716%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4b8 : bv 32 := @BV 32 0x0085851b%Z I.
Lemma F_7a4b8 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4c0%Z I : word) = Some W_7a4b8.
Proof. vm_refl. Qed.
Lemma D_7a4b8 : decode_any W_7a4b8 = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4bc : bv 32 := @BV 32 0x00a48533%Z I.
Lemma F_7a4bc : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4c4%Z I : word) = Some W_7a4bc.
Proof. vm_refl. Qed.
Lemma D_7a4bc : decode_any W_7a4bc = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4c0 : bv 32 := @BV 32 0x02800613%Z I.
Lemma F_7a4c0 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4c8%Z I : word) = Some W_7a4c0.
Proof. vm_refl. Qed.
Lemma D_7a4c0 : decode_any W_7a4c0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4c4 : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_7a4c4 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4cc%Z I : word) = Some W_7a4c4.
Proof. vm_refl. Qed.
Lemma D_7a4c4 : decode_any W_7a4c4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4c8 : bv 32 := @BV 32 0x269050ef%Z I.
Lemma F_7a4c8 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4d0%Z I : word) = Some W_7a4c8.
Proof. vm_refl. Qed.
Lemma D_7a4c8 : decode_any W_7a4c8 = Some (Jal (@BV 5 1%Z I) (@BV 21 23144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4cc : bv 32 := @BV 32 0x00048023%Z I.
Lemma F_7a4cc : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4d4%Z I : word) = Some W_7a4cc.
Proof. vm_refl. Qed.
Lemma D_7a4cc : decode_any W_7a4cc = Some (Store SZ1 (@BV 5 9%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4d0 : bv 32 := @BV 32 0x00848513%Z I.
Lemma F_7a4d0 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4d8%Z I : word) = Some W_7a4d0.
Proof. vm_refl. Qed.
Lemma D_7a4d0 : decode_any W_7a4d0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4d4 : bv 32 := @BV 32 0x00040637%Z I.
Lemma F_7a4d4 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4dc%Z I : word) = Some W_7a4d4.
Proof. vm_refl. Qed.
Lemma D_7a4d4 : decode_any W_7a4d4 = Some (Lui (@BV 5 12%Z I) (@BV 20 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4d8 : bv 32 := @BV 32 0x000409b7%Z I.
Lemma F_7a4d8 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4e0%Z I : word) = Some W_7a4d8.
Proof. vm_refl. Qed.
Lemma D_7a4d8 : decode_any W_7a4d8 = Some (Lui (@BV 5 19%Z I) (@BV 20 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4dc : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_7a4dc : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4e4%Z I : word) = Some W_7a4dc.
Proof. vm_refl. Qed.
Lemma D_7a4dc : decode_any W_7a4dc = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4e0 : bv 32 := @BV 32 0x251050ef%Z I.
Lemma F_7a4e0 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4e8%Z I : word) = Some W_7a4e0.
Proof. vm_refl. Qed.
Lemma D_7a4e0 : decode_any W_7a4e0 = Some (Jal (@BV 5 1%Z I) (@BV 21 23120%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4e4 : bv 32 := @BV 32 0x0409851b%Z I.
Lemma F_7a4e4 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4ec%Z I : word) = Some W_7a4e4.
Proof. vm_refl. Qed.
Lemma D_7a4e4 : decode_any W_7a4e4 = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4e8 : bv 32 := @BV 32 0x00a48533%Z I.
Lemma F_7a4e8 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4f0%Z I : word) = Some W_7a4e8.
Proof. vm_refl. Qed.
Lemma D_7a4e8 : decode_any W_7a4e8 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4ec : bv 32 := @BV 32 0x01b00613%Z I.
Lemma F_7a4ec : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4f4%Z I : word) = Some W_7a4ec.
Proof. vm_refl. Qed.
Lemma D_7a4ec : decode_any W_7a4ec = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 27%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4f0 : bv 32 := @BV 32 0x00761613%Z I.
Lemma F_7a4f0 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4f8%Z I : word) = Some W_7a4f0.
Proof. vm_refl. Qed.
Lemma D_7a4f0 : decode_any W_7a4f0 = Some (ShiftImm ALU_SLL (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 6 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4f4 : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_7a4f4 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a4fc%Z I : word) = Some W_7a4f4.
Proof. vm_refl. Qed.
Lemma D_7a4f4 : decode_any W_7a4f4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4f8 : bv 32 := @BV 32 0x239050ef%Z I.
Lemma F_7a4f8 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a500%Z I : word) = Some W_7a4f8.
Proof. vm_refl. Qed.
Lemma D_7a4f8 : decode_any W_7a4f8 = Some (Jal (@BV 5 1%Z I) (@BV 21 23096%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4fc : bv 32 := @BV 32 0x00041937%Z I.
Lemma F_7a4fc : fetch_word Asan.M.loaded_segments (@BV 64 0x7a504%Z I : word) = Some W_7a4fc.
Proof. vm_refl. Qed.
Lemma D_7a4fc : decode_any W_7a4fc = Some (Lui (@BV 5 18%Z I) (@BV 20 65%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a500 : bv 32 := @BV 32 0xdc09051b%Z I.
Lemma F_7a500 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a508%Z I : word) = Some W_7a500.
Proof. vm_refl. Qed.
Lemma D_7a500 : decode_any W_7a500 = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 3520%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a504 : bv 32 := @BV 32 0x00a48533%Z I.
Lemma F_7a504 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a50c%Z I : word) = Some W_7a504.
Proof. vm_refl. Qed.
Lemma D_7a504 : decode_any W_7a504 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a508 : bv 32 := @BV 32 0x2489861b%Z I.
Lemma F_7a508 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a510%Z I : word) = Some W_7a508.
Proof. vm_refl. Qed.
Lemma D_7a508 : decode_any W_7a508 = Some (OpImm32 (@BV 5 12%Z I) (@BV 5 19%Z I) (@BV 12 584%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a50c : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_7a50c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a514%Z I : word) = Some W_7a50c.
Proof. vm_refl. Qed.
Lemma D_7a50c : decode_any W_7a50c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a510 : bv 32 := @BV 32 0x221050ef%Z I.
Lemma F_7a510 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a518%Z I : word) = Some W_7a510.
Proof. vm_refl. Qed.
Lemma D_7a510 : decode_any W_7a510 = Some (Jal (@BV 5 1%Z I) (@BV 21 23072%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a514 : bv 32 := @BV 32 0x00085517%Z I.
Lemma F_7a514 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a51c%Z I : word) = Some W_7a514.
Proof. vm_refl. Qed.
Lemma D_7a514 : decode_any W_7a514 = Some (Auipc (@BV 5 10%Z I) (@BV 20 133%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a518 : bv 32 := @BV 32 0xd3453983%Z I.
Lemma F_7a518 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a520%Z I : word) = Some W_7a518.
Proof. vm_refl. Qed.
Lemma D_7a518 : decode_any W_7a518 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 3380%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a51c : bv 32 := @BV 32 0x0009b503%Z I.
Lemma F_7a51c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a524%Z I : word) = Some W_7a51c.
Proof. vm_refl. Qed.
Lemma D_7a51c : decode_any W_7a51c = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a520 : bv 32 := @BV 32 0x00051663%Z I.
Lemma F_7a520 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a528%Z I : word) = Some W_7a520.
Proof. vm_refl. Qed.
Lemma D_7a520 : decode_any W_7a520 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a52c : bv 32 := @BV 32 0x012485b3%Z I.
Lemma F_7a52c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a534%Z I : word) = Some W_7a52c.
Proof. vm_refl. Qed.
Lemma D_7a52c : decode_any W_7a52c = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 5 18%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a530 : bv 32 := @BV 32 0xdd09061b%Z I.
Lemma F_7a530 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a538%Z I : word) = Some W_7a530.
Proof. vm_refl. Qed.
Lemma D_7a530 : decode_any W_7a530 = Some (OpImm32 (@BV 5 12%Z I) (@BV 5 18%Z I) (@BV 12 3536%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a534 : bv 32 := @BV 32 0x00c48633%Z I.
Lemma F_7a534 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a53c%Z I : word) = Some W_7a534.
Proof. vm_refl. Qed.
Lemma D_7a534 : decode_any W_7a534 = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 9%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a538 : bv 32 := @BV 32 0x00100693%Z I.
Lemma F_7a538 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a540%Z I : word) = Some W_7a538.
Proof. vm_refl. Qed.
Lemma D_7a538 : decode_any W_7a538 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a53c : bv 32 := @BV 32 0xdca5b023%Z I.
Lemma F_7a53c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a544%Z I : word) = Some W_7a53c.
Proof. vm_refl. Qed.
Lemma D_7a53c : decode_any W_7a53c = Some (Store SZ8 (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 3520%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a540 : bv 32 := @BV 32 0xdcc5b423%Z I.
Lemma F_7a540 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a548%Z I : word) = Some W_7a540.
Proof. vm_refl. Qed.
Lemma D_7a540 : decode_any W_7a540 = Some (Store SZ8 (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 12 3528%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a544 : bv 32 := @BV 32 0x0310000f%Z I.
Lemma F_7a544 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a54c%Z I : word) = Some W_7a544.
Proof. vm_refl. Qed.
Lemma D_7a544 : decode_any W_7a544 = Some (Fence (@BV 4 0%Z I) (@BV 4 3%Z I) (@BV 4 1%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a548 : bv 32 := @BV 32 0x00d40023%Z I.
Lemma F_7a548 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a550%Z I : word) = Some W_7a548.
Proof. vm_refl. Qed.
Lemma D_7a548 : decode_any W_7a548 = Some (Store SZ1 (@BV 5 8%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a54c : bv 32 := @BV 32 0x0310000f%Z I.
Lemma F_7a54c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a554%Z I : word) = Some W_7a54c.
Proof. vm_refl. Qed.
Lemma D_7a54c : decode_any W_7a54c = Some (Fence (@BV 4 0%Z I) (@BV 4 3%Z I) (@BV 4 1%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a550 : bv 32 := @BV 32 0x000400a3%Z I.
Lemma F_7a550 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a558%Z I : word) = Some W_7a550.
Proof. vm_refl. Qed.
Lemma D_7a550 : decode_any W_7a550 = Some (Store SZ1 (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a554 : bv 32 := @BV 32 0x0008e517%Z I.
Lemma F_7a554 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a55c%Z I : word) = Some W_7a554.
Proof. vm_refl. Qed.
Lemma D_7a554 : decode_any W_7a554 = Some (Auipc (@BV 5 10%Z I) (@BV 20 142%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a558 : bv 32 := @BV 32 0x22450513%Z I.
Lemma F_7a558 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a560%Z I : word) = Some W_7a558.
Proof. vm_refl. Qed.
Lemma D_7a558 : decode_any W_7a558 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 548%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a55c : bv 32 := @BV 32 0x02813083%Z I.
Lemma F_7a55c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a564%Z I : word) = Some W_7a55c.
Proof. vm_refl. Qed.
Lemma D_7a55c : decode_any W_7a55c = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a560 : bv 32 := @BV 32 0x02013403%Z I.
Lemma F_7a560 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a568%Z I : word) = Some W_7a560.
Proof. vm_refl. Qed.
Lemma D_7a560 : decode_any W_7a560 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a564 : bv 32 := @BV 32 0x01813483%Z I.
Lemma F_7a564 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a56c%Z I : word) = Some W_7a564.
Proof. vm_refl. Qed.
Lemma D_7a564 : decode_any W_7a564 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a568 : bv 32 := @BV 32 0x01013903%Z I.
Lemma F_7a568 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a570%Z I : word) = Some W_7a568.
Proof. vm_refl. Qed.
Lemma D_7a568 : decode_any W_7a568 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a56c : bv 32 := @BV 32 0x00813983%Z I.
Lemma F_7a56c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a574%Z I : word) = Some W_7a56c.
Proof. vm_refl. Qed.
Lemma D_7a56c : decode_any W_7a56c = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a570 : bv 32 := @BV 32 0x03010113%Z I.
Lemma F_7a570 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a578%Z I : word) = Some W_7a570.
Proof. vm_refl. Qed.
Lemma D_7a570 : decode_any W_7a570 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a574 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7a574 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a57c%Z I : word) = Some W_7a574.
Proof. vm_refl. Qed.
Lemma D_7a574 : decode_any W_7a574 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a934 : bv 32 := @BV 32 0x0010f517%Z I.
Lemma F_7a934 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a93c%Z I : word) = Some W_7a934.
Proof. vm_refl. Qed.
Lemma D_7a934 : decode_any W_7a934 = Some (Auipc (@BV 5 10%Z I) (@BV 20 271%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a938 : bv 32 := @BV 32 0x00100593%Z I.
Lemma F_7a938 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a940%Z I : word) = Some W_7a938.
Proof. vm_refl. Qed.
Lemma D_7a938 : decode_any W_7a938 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a93c : bv 32 := @BV 32 0xeab50223%Z I.
Lemma F_7a93c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a944%Z I : word) = Some W_7a93c.
Proof. vm_refl. Qed.
Lemma D_7a93c : decode_any W_7a93c = Some (Store SZ1 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 3748%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a940 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7a940 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a948%Z I : word) = Some W_7a940.
Proof. vm_refl. Qed.
Lemma D_7a940 : decode_any W_7a940 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a944 : bv 32 := @BV 32 0x0010f517%Z I.
Lemma F_7a944 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a94c%Z I : word) = Some W_7a944.
Proof. vm_refl. Qed.
Lemma D_7a944 : decode_any W_7a944 = Some (Auipc (@BV 5 10%Z I) (@BV 20 271%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a948 : bv 32 := @BV 32 0xe9550503%Z I.
Lemma F_7a948 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a950%Z I : word) = Some W_7a948.
Proof. vm_refl. Qed.
Lemma D_7a948 : decode_any W_7a948 = Some (Load SZ1 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3733%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a94c : bv 32 := @BV 32 0x00a03533%Z I.
Lemma F_7a94c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a954%Z I : word) = Some W_7a94c.
Proof. vm_refl. Qed.
Lemma D_7a94c : decode_any W_7a94c = Some (Op ALU_SLTU (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a950 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7a950 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a958%Z I : word) = Some W_7a950.
Proof. vm_refl. Qed.
Lemma D_7a950 : decode_any W_7a950 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a96c : bv 32 := @BV 32 0x0010f517%Z I.
Lemma F_7a96c : fetch_word Asan.M.loaded_segments (@BV 64 0x7a974%Z I : word) = Some W_7a96c.
Proof. vm_refl. Qed.
Lemma D_7a96c : decode_any W_7a96c = Some (Auipc (@BV 5 10%Z I) (@BV 20 271%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a970 : bv 32 := @BV 32 0xe6e50503%Z I.
Lemma F_7a970 : fetch_word Asan.M.loaded_segments (@BV 64 0x7a978%Z I : word) = Some W_7a970.
Proof. vm_refl. Qed.
Lemma D_7a970 : decode_any W_7a970 = Some (Load SZ1 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3694%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a974 : bv 32 := @BV 32 0x00a03533%Z I.

Lemma D_7a974 : decode_any W_7a974 = Some (Op ALU_SLTU (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a978 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_7a978 : decode_any W_7a978 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf7c : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_7bf7c : fetch_word Asan.M.loaded_segments (@BV 64 0x7bf84%Z I : word) = Some W_7bf7c.
Proof. vm_refl. Qed.
Lemma D_7bf7c : decode_any W_7bf7c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf80 : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_7bf80 : fetch_word Asan.M.loaded_segments (@BV 64 0x7bf88%Z I : word) = Some W_7bf80.
Proof. vm_refl. Qed.
Lemma D_7bf80 : decode_any W_7bf80 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf84 : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_7bf84 : fetch_word Asan.M.loaded_segments (@BV 64 0x7bf8c%Z I : word) = Some W_7bf84.
Proof. vm_refl. Qed.
Lemma D_7bf84 : decode_any W_7bf84 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf88 : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_7bf88 : fetch_word Asan.M.loaded_segments (@BV 64 0x7bf90%Z I : word) = Some W_7bf88.
Proof. vm_refl. Qed.
Lemma D_7bf88 : decode_any W_7bf88 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf8c : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_7bf8c : fetch_word Asan.M.loaded_segments (@BV 64 0x7bf94%Z I : word) = Some W_7bf8c.
Proof. vm_refl. Qed.
Lemma D_7bf8c : decode_any W_7bf8c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf90 : bv 32 := @BV 32 0x01313423%Z I.
Lemma F_7bf90 : fetch_word Asan.M.loaded_segments (@BV 64 0x7bf98%Z I : word) = Some W_7bf90.
Proof. vm_refl. Qed.
Lemma D_7bf90 : decode_any W_7bf90 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf94 : bv 32 := @BV 32 0x00083797%Z I.
Lemma F_7bf94 : fetch_word Asan.M.loaded_segments (@BV 64 0x7bf9c%Z I : word) = Some W_7bf94.
Proof. vm_refl. Qed.
Lemma D_7bf94 : decode_any W_7bf94 = Some (Auipc (@BV 5 15%Z I) (@BV 20 131%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf98 : bv 32 := @BV 32 0x3147b783%Z I.
Lemma F_7bf98 : fetch_word Asan.M.loaded_segments (@BV 64 0x7bfa0%Z I : word) = Some W_7bf98.
Proof. vm_refl. Qed.
Lemma D_7bf98 : decode_any W_7bf98 = Some (Load SZ8 true (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 788%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf9c : bv 32 := @BV 32 0x00078a63%Z I.
Lemma F_7bf9c : fetch_word Asan.M.loaded_segments (@BV 64 0x7bfa4%Z I : word) = Some W_7bf9c.
Proof. vm_refl. Qed.
Lemma D_7bf9c : decode_any W_7bf9c = Some (Branch BC_EQ (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bfa0 : bv 32 := @BV 32 0x0011d517%Z I.
Lemma F_7bfa0 : fetch_word Asan.M.loaded_segments (@BV 64 0x7bfa8%Z I : word) = Some W_7bfa0.
Proof. vm_refl. Qed.
Lemma D_7bfa0 : decode_any W_7bfa0 = Some (Auipc (@BV 5 10%Z I) (@BV 20 285%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bfa4 : bv 32 := @BV 32 0x0f452503%Z I.
Lemma F_7bfa4 : fetch_word Asan.M.loaded_segments (@BV 64 0x7bfac%Z I : word) = Some W_7bfa4.
Proof. vm_refl. Qed.
Lemma D_7bfa4 : decode_any W_7bfa4 = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 244%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bfa8 : bv 32 := @BV 32 0x04051a63%Z I.
Lemma F_7bfa8 : fetch_word Asan.M.loaded_segments (@BV 64 0x7bfb0%Z I : word) = Some W_7bfa8.
Proof. vm_refl. Qed.
Lemma D_7bfa8 : decode_any W_7bfa8 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 84%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bfac : bv 32 := @BV 32 0x0000006f%Z I.
Lemma F_7bfac : fetch_word Asan.M.loaded_segments (@BV 64 0x7bfb4%Z I : word) = Some W_7bfac.
Proof. vm_refl. Qed.
Lemma D_7bfac : decode_any W_7bfac = Some (Jal (@BV 5 0%Z I) (@BV 21 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c614 : bv 32 := @BV 32 0x00083597%Z I.
Lemma F_7c614 : fetch_word Asan.M.loaded_segments (@BV 64 0x7c61c%Z I : word) = Some W_7c614.
Proof. vm_refl. Qed.
Lemma D_7c614 : decode_any W_7c614 = Some (Auipc (@BV 5 11%Z I) (@BV 20 131%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c618 : bv 32 := @BV 32 0xc445b583%Z I.
Lemma F_7c618 : fetch_word Asan.M.loaded_segments (@BV 64 0x7c620%Z I : word) = Some W_7c618.
Proof. vm_refl. Qed.
Lemma D_7c618 : decode_any W_7c618 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3140%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c61c : bv 32 := @BV 32 0x0905b583%Z I.
Lemma F_7c61c : fetch_word Asan.M.loaded_segments (@BV 64 0x7c624%Z I : word) = Some W_7c61c.
Proof. vm_refl. Qed.
Lemma D_7c61c : decode_any W_7c61c = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c620 : bv 32 := @BV 32 0x00058e63%Z I.
Lemma F_7c620 : fetch_word Asan.M.loaded_segments (@BV 64 0x7c628%Z I : word) = Some W_7c620.
Proof. vm_refl. Qed.
Lemma D_7c620 : decode_any W_7c620 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c63c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7c63c : fetch_word Asan.M.loaded_segments (@BV 64 0x7c644%Z I : word) = Some W_7c63c.
Proof. vm_refl. Qed.
Lemma D_7c63c : decode_any W_7c63c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c658 : bv 32 := @BV 32 0x00083597%Z I.
Lemma F_7c658 : fetch_word Asan.M.loaded_segments (@BV 64 0x7c660%Z I : word) = Some W_7c658.
Proof. vm_refl. Qed.
Lemma D_7c658 : decode_any W_7c658 = Some (Auipc (@BV 5 11%Z I) (@BV 20 131%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c65c : bv 32 := @BV 32 0xc005b583%Z I.
Lemma F_7c65c : fetch_word Asan.M.loaded_segments (@BV 64 0x7c664%Z I : word) = Some W_7c65c.
Proof. vm_refl. Qed.
Lemma D_7c65c : decode_any W_7c65c = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3072%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c660 : bv 32 := @BV 32 0x0905b583%Z I.
Lemma F_7c660 : fetch_word Asan.M.loaded_segments (@BV 64 0x7c668%Z I : word) = Some W_7c660.
Proof. vm_refl. Qed.
Lemma D_7c660 : decode_any W_7c660 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c664 : bv 32 := @BV 32 0x00058a63%Z I.
Lemma F_7c664 : fetch_word Asan.M.loaded_segments (@BV 64 0x7c66c%Z I : word) = Some W_7c664.
Proof. vm_refl. Qed.
Lemma D_7c664 : decode_any W_7c664 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c678 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7c678 : fetch_word Asan.M.loaded_segments (@BV 64 0x7c680%Z I : word) = Some W_7c678.
Proof. vm_refl. Qed.
Lemma D_7c678 : decode_any W_7c678 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c9f4 : bv 32 := @BV 32 0x01213023%Z I.
Lemma F_7c9f4 : fetch_word Asan.M.loaded_segments (@BV 64 0x7c9fc%Z I : word) = Some W_7c9f4.
Proof. vm_refl. Qed.
Lemma D_7c9f4 : decode_any W_7c9f4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c9f8 : bv 32 := @BV 32 0x00058913%Z I.
Lemma F_7c9f8 : fetch_word Asan.M.loaded_segments (@BV 64 0x7ca00%Z I : word) = Some W_7c9f8.
Proof. vm_refl. Qed.
Lemma D_7c9f8 : decode_any W_7c9f8 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c9fc : bv 32 := @BV 32 0x00050413%Z I.
Lemma F_7c9fc : fetch_word Asan.M.loaded_segments (@BV 64 0x7ca04%Z I : word) = Some W_7c9fc.
Proof. vm_refl. Qed.
Lemma D_7c9fc : decode_any W_7c9fc = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca00 : bv 32 := @BV 32 0xed1ff0ef%Z I.
Lemma F_7ca00 : fetch_word Asan.M.loaded_segments (@BV 64 0x7ca08%Z I : word) = Some W_7ca00.
Proof. vm_refl. Qed.
Lemma D_7ca00 : decode_any W_7ca00 = Some (Jal (@BV 5 1%Z I) (@BV 21 2096848%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca04 : bv 32 := @BV 32 0x0011b517%Z I.
Lemma F_7ca04 : fetch_word Asan.M.loaded_segments (@BV 64 0x7ca0c%Z I : word) = Some W_7ca04.
Proof. vm_refl. Qed.
Lemma D_7ca04 : decode_any W_7ca04 = Some (Auipc (@BV 5 10%Z I) (@BV 20 283%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca08 : bv 32 := @BV 32 0x63450513%Z I.
Lemma F_7ca08 : fetch_word Asan.M.loaded_segments (@BV 64 0x7ca10%Z I : word) = Some W_7ca08.
Proof. vm_refl. Qed.
Lemma D_7ca08 : decode_any W_7ca08 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1588%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca0c : bv 32 := @BV 32 0x678030ef%Z I.
Lemma F_7ca0c : fetch_word Asan.M.loaded_segments (@BV 64 0x7ca14%Z I : word) = Some W_7ca0c.
Proof. vm_refl. Qed.
Lemma D_7ca0c : decode_any W_7ca0c = Some (Jal (@BV 5 1%Z I) (@BV 21 13944%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca10 : bv 32 := @BV 32 0x02090a63%Z I.
Lemma F_7ca10 : fetch_word Asan.M.loaded_segments (@BV 64 0x7ca18%Z I : word) = Some W_7ca10.
Proof. vm_refl. Qed.
Lemma D_7ca10 : decode_any W_7ca10 = Some (Branch BC_EQ (@BV 5 18%Z I) (@BV 5 0%Z I) (@BV 13 52%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca14 : bv 32 := @BV 32 0x00050493%Z I.
Lemma F_7ca14 : fetch_word Asan.M.loaded_segments (@BV 64 0x7ca1c%Z I : word) = Some W_7ca14.
Proof. vm_refl. Qed.
Lemma D_7ca14 : decode_any W_7ca14 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca18 : bv 32 := @BV 32 0xfff90913%Z I.
Lemma F_7ca18 : fetch_word Asan.M.loaded_segments (@BV 64 0x7ca20%Z I : word) = Some W_7ca18.
Proof. vm_refl. Qed.
Lemma D_7ca18 : decode_any W_7ca18 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 18%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca1c : bv 32 := @BV 32 0x01256463%Z I.
Lemma F_7ca1c : fetch_word Asan.M.loaded_segments (@BV 64 0x7ca24%Z I : word) = Some W_7ca1c.
Proof. vm_refl. Qed.
Lemma D_7ca1c : decode_any W_7ca1c = Some (Branch BC_LTU (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 13 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca20 : bv 32 := @BV 32 0x00090493%Z I.
Lemma F_7ca20 : fetch_word Asan.M.loaded_segments (@BV 64 0x7ca28%Z I : word) = Some W_7ca20.
Proof. vm_refl. Qed.
Lemma D_7ca20 : decode_any W_7ca20 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ca24 : bv 32 := @BV 32 0x0011b517%Z I.
Lemma F_7ca24 : fetch_word Asan.M.loaded_segments (@BV 64 0x7ca2c%Z I : word) = Some W_7ca24.
Proof. vm_refl. Qed.
Lemma D_7ca24 : decode_any W_7ca24 = Some (Auipc (@BV 5 10%Z I) (@BV 20 283%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb88 : bv 32 := @BV 32 0xfe010113%Z I.

Lemma D_7cb88 : decode_any W_7cb88 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb8c : bv 32 := @BV 32 0x00113c23%Z I.

Lemma D_7cb8c : decode_any W_7cb8c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb90 : bv 32 := @BV 32 0x00813823%Z I.

Lemma D_7cb90 : decode_any W_7cb90 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb94 : bv 32 := @BV 32 0x00913423%Z I.

Lemma D_7cb94 : decode_any W_7cb94 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb98 : bv 32 := @BV 32 0x01213023%Z I.

Lemma D_7cb98 : decode_any W_7cb98 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb9c : bv 32 := @BV 32 0x00058413%Z I.

Lemma D_7cb9c : decode_any W_7cb9c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cba0 : bv 32 := @BV 32 0x00050493%Z I.

Lemma D_7cba0 : decode_any W_7cba0 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cba4 : bv 32 := @BV 32 0x09c000ef%Z I.

Lemma D_7cba4 : decode_any W_7cba4 = Some (Jal (@BV 5 1%Z I) (@BV 21 156%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cba8 : bv 32 := @BV 32 0x0011c517%Z I.
Lemma F_7cba8 : fetch_word Asan.M.loaded_segments (@BV 64 0x7cbb0%Z I : word) = Some W_7cba8.
Proof. vm_refl. Qed.
Lemma D_7cba8 : decode_any W_7cba8 = Some (Auipc (@BV 5 10%Z I) (@BV 20 284%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbac : bv 32 := @BV 32 0x49050913%Z I.
Lemma F_7cbac : fetch_word Asan.M.loaded_segments (@BV 64 0x7cbb4%Z I : word) = Some W_7cbac.
Proof. vm_refl. Qed.
Lemma D_7cbac : decode_any W_7cbac = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 1168%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbb0 : bv 32 := @BV 32 0x00093603%Z I.

Lemma D_7cbb0 : decode_any W_7cbb0 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbb4 : bv 32 := @BV 32 0x06060a63%Z I.

Lemma D_7cbb4 : decode_any W_7cbb4 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 116%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbb8 : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_7cbbc : bv 32 := @BV 32 0x00040593%Z I.



(* [comment removed for export] *)
Definition W_7cbc0 : bv 32 := @BV 32 0x000600e7%Z I.



(* [comment removed for export] *)
Definition W_7cbc4 : bv 32 := @BV 32 0x01093603%Z I.



(* [comment removed for export] *)
Definition W_7cbc8 : bv 32 := @BV 32 0x06060063%Z I.



(* [comment removed for export] *)
Definition W_7cbcc : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_7cbd0 : bv 32 := @BV 32 0x00040593%Z I.



(* [comment removed for export] *)
Definition W_7cbd4 : bv 32 := @BV 32 0x000600e7%Z I.



(* [comment removed for export] *)
Definition W_7cbd8 : bv 32 := @BV 32 0x02093603%Z I.



(* [comment removed for export] *)
Definition W_7cbdc : bv 32 := @BV 32 0x04060663%Z I.



(* [comment removed for export] *)
Definition W_7cbe0 : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_7cbe4 : bv 32 := @BV 32 0x00040593%Z I.



(* [comment removed for export] *)
Definition W_7cbe8 : bv 32 := @BV 32 0x000600e7%Z I.



(* [comment removed for export] *)
Definition W_7cbec : bv 32 := @BV 32 0x03093603%Z I.



(* [comment removed for export] *)
Definition W_7cbf0 : bv 32 := @BV 32 0x02060c63%Z I.



(* [comment removed for export] *)
Definition W_7cbf4 : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_7cbf8 : bv 32 := @BV 32 0x00040593%Z I.



(* [comment removed for export] *)
Definition W_7cbfc : bv 32 := @BV 32 0x000600e7%Z I.



(* [comment removed for export] *)
Definition W_7cc00 : bv 32 := @BV 32 0x04093303%Z I.



(* [comment removed for export] *)
Definition W_7cc04 : bv 32 := @BV 32 0x02030263%Z I.



(* [comment removed for export] *)
Definition W_7cc08 : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_7cc0c : bv 32 := @BV 32 0x00040593%Z I.



(* [comment removed for export] *)
Definition W_7cc10 : bv 32 := @BV 32 0x01813083%Z I.



(* [comment removed for export] *)
Definition W_7cc14 : bv 32 := @BV 32 0x01013403%Z I.



(* [comment removed for export] *)
Definition W_7cc18 : bv 32 := @BV 32 0x00813483%Z I.



(* [comment removed for export] *)
Definition W_7cc1c : bv 32 := @BV 32 0x00013903%Z I.



(* [comment removed for export] *)
Definition W_7cc20 : bv 32 := @BV 32 0x02010113%Z I.



(* [comment removed for export] *)
Definition W_7cc24 : bv 32 := @BV 32 0x00030067%Z I.



(* [comment removed for export] *)
Definition W_7cc28 : bv 32 := @BV 32 0x01813083%Z I.

Lemma D_7cc28 : decode_any W_7cc28 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc2c : bv 32 := @BV 32 0x01013403%Z I.

Lemma D_7cc2c : decode_any W_7cc2c = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc30 : bv 32 := @BV 32 0x00813483%Z I.

Lemma D_7cc30 : decode_any W_7cc30 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc34 : bv 32 := @BV 32 0x00013903%Z I.

Lemma D_7cc34 : decode_any W_7cc34 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc38 : bv 32 := @BV 32 0x02010113%Z I.

Lemma D_7cc38 : decode_any W_7cc38 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc3c : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_7cc3c : decode_any W_7cc3c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc40 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_7cc40 : decode_any W_7cc40 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc44 : bv 32 := @BV 32 0xfe010113%Z I.
Lemma F_7cc44 : fetch_word Asan.M.loaded_segments (@BV 64 0x7cc4c%Z I : word) = Some W_7cc44.
Proof. vm_refl. Qed.
Lemma D_7cc44 : decode_any W_7cc44 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc48 : bv 32 := @BV 32 0x00113c23%Z I.
Lemma F_7cc48 : fetch_word Asan.M.loaded_segments (@BV 64 0x7cc50%Z I : word) = Some W_7cc48.
Proof. vm_refl. Qed.
Lemma D_7cc48 : decode_any W_7cc48 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc4c : bv 32 := @BV 32 0x00813823%Z I.
Lemma F_7cc4c : fetch_word Asan.M.loaded_segments (@BV 64 0x7cc54%Z I : word) = Some W_7cc4c.
Proof. vm_refl. Qed.
Lemma D_7cc4c : decode_any W_7cc4c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc50 : bv 32 := @BV 32 0x00913423%Z I.
Lemma F_7cc50 : fetch_word Asan.M.loaded_segments (@BV 64 0x7cc58%Z I : word) = Some W_7cc50.
Proof. vm_refl. Qed.
Lemma D_7cc50 : decode_any W_7cc50 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc54 : bv 32 := @BV 32 0x00050413%Z I.
Lemma F_7cc54 : fetch_word Asan.M.loaded_segments (@BV 64 0x7cc5c%Z I : word) = Some W_7cc54.
Proof. vm_refl. Qed.
Lemma D_7cc54 : decode_any W_7cc54 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc58 : bv 32 := @BV 32 0x098000ef%Z I.
Lemma F_7cc58 : fetch_word Asan.M.loaded_segments (@BV 64 0x7cc60%Z I : word) = Some W_7cc58.
Proof. vm_refl. Qed.
Lemma D_7cc58 : decode_any W_7cc58 = Some (Jal (@BV 5 1%Z I) (@BV 21 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc5c : bv 32 := @BV 32 0x00050e63%Z I.
Lemma F_7cc5c : fetch_word Asan.M.loaded_segments (@BV 64 0x7cc64%Z I : word) = Some W_7cc5c.
Proof. vm_refl. Qed.
Lemma D_7cc5c : decode_any W_7cc5c = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc78 : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_7cc78 : fetch_word Asan.M.loaded_segments (@BV 64 0x7cc80%Z I : word) = Some W_7cc78.
Proof. vm_refl. Qed.
Lemma D_7cc78 : decode_any W_7cc78 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc7c : bv 32 := @BV 32 0x07c000ef%Z I.
Lemma F_7cc7c : fetch_word Asan.M.loaded_segments (@BV 64 0x7cc84%Z I : word) = Some W_7cc7c.
Proof. vm_refl. Qed.
Lemma D_7cc7c : decode_any W_7cc7c = Some (Jal (@BV 5 1%Z I) (@BV 21 124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc80 : bv 32 := @BV 32 0x0011c517%Z I.
Lemma F_7cc80 : fetch_word Asan.M.loaded_segments (@BV 64 0x7cc88%Z I : word) = Some W_7cc80.
Proof. vm_refl. Qed.
Lemma D_7cc80 : decode_any W_7cc80 = Some (Auipc (@BV 5 10%Z I) (@BV 20 284%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc84 : bv 32 := @BV 32 0x3b850493%Z I.
Lemma F_7cc84 : fetch_word Asan.M.loaded_segments (@BV 64 0x7cc8c%Z I : word) = Some W_7cc84.
Proof. vm_refl. Qed.
Lemma D_7cc84 : decode_any W_7cc84 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 952%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc88 : bv 32 := @BV 32 0x0084b583%Z I.
Lemma F_7cc88 : fetch_word Asan.M.loaded_segments (@BV 64 0x7cc90%Z I : word) = Some W_7cc88.
Proof. vm_refl. Qed.
Lemma D_7cc88 : decode_any W_7cc88 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc8c : bv 32 := @BV 32 0x04058663%Z I.
Lemma F_7cc8c : fetch_word Asan.M.loaded_segments (@BV 64 0x7cc94%Z I : word) = Some W_7cc8c.
Proof. vm_refl. Qed.
Lemma D_7cc8c : decode_any W_7cc8c = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 76%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccd8 : bv 32 := @BV 32 0x00000513%Z I.
Lemma F_7ccd8 : fetch_word Asan.M.loaded_segments (@BV 64 0x7cce0%Z I : word) = Some W_7ccd8.
Proof. vm_refl. Qed.
Lemma D_7ccd8 : decode_any W_7ccd8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccdc : bv 32 := @BV 32 0x01813083%Z I.
Lemma F_7ccdc : fetch_word Asan.M.loaded_segments (@BV 64 0x7cce4%Z I : word) = Some W_7ccdc.
Proof. vm_refl. Qed.
Lemma D_7ccdc : decode_any W_7ccdc = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cce0 : bv 32 := @BV 32 0x01013403%Z I.
Lemma F_7cce0 : fetch_word Asan.M.loaded_segments (@BV 64 0x7cce8%Z I : word) = Some W_7cce0.
Proof. vm_refl. Qed.
Lemma D_7cce0 : decode_any W_7cce0 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cce4 : bv 32 := @BV 32 0x00813483%Z I.
Lemma F_7cce4 : fetch_word Asan.M.loaded_segments (@BV 64 0x7ccec%Z I : word) = Some W_7cce4.
Proof. vm_refl. Qed.
Lemma D_7cce4 : decode_any W_7cce4 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cce8 : bv 32 := @BV 32 0x02010113%Z I.
Lemma F_7cce8 : fetch_word Asan.M.loaded_segments (@BV 64 0x7ccf0%Z I : word) = Some W_7cce8.
Proof. vm_refl. Qed.
Lemma D_7cce8 : decode_any W_7cce8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccec : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7ccec : fetch_word Asan.M.loaded_segments (@BV 64 0x7ccf4%Z I : word) = Some W_7ccec.
Proof. vm_refl. Qed.
Lemma D_7ccec : decode_any W_7ccec = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccf0 : bv 32 := @BV 32 0x00000513%Z I.
Lemma F_7ccf0 : fetch_word Asan.M.loaded_segments (@BV 64 0x7ccf8%Z I : word) = Some W_7ccf0.
Proof. vm_refl. Qed.
Lemma D_7ccf0 : decode_any W_7ccf0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccf4 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7ccf4 : fetch_word Asan.M.loaded_segments (@BV 64 0x7ccfc%Z I : word) = Some W_7ccf4.
Proof. vm_refl. Qed.
Lemma D_7ccf4 : decode_any W_7ccf4 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccf8 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_7ccf8 : fetch_word Asan.M.loaded_segments (@BV 64 0x7cd00%Z I : word) = Some W_7ccf8.
Proof. vm_refl. Qed.
Lemma D_7ccf8 : decode_any W_7ccf8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d08c : bv 32 := @BV 32 0x1406272f%Z I.
Lemma F_7d08c : fetch_word Asan.M.loaded_segments (@BV 64 0x7d094%Z I : word) = Some W_7d08c.
Proof. vm_refl. Qed.
Lemma D_7d08c : decode_any W_7d08c = Some (Lr AW true false (@BV 5 14%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7d090 : bv 32 := @BV 32 0x00058793%Z I.
Lemma F_7d090 : fetch_word Asan.M.loaded_segments (@BV 64 0x7d098%Z I : word) = Some W_7d090.
Proof. vm_refl. Qed.
Lemma D_7d090 : decode_any W_7d090 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7feb4 : bv 32 := @BV 32 0x02060063%Z I.

Lemma D_7feb4 : decode_any W_7feb4 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7feb8 : bv 32 := @BV 32 0x00c50633%Z I.

Lemma D_7feb8 : decode_any W_7feb8 = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7febc : bv 32 := @BV 32 0x00050693%Z I.

Lemma D_7febc : decode_any W_7febc = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fec0 : bv 32 := @BV 32 0x0005c703%Z I.

Lemma D_7fec0 : decode_any W_7fec0 = Some (Load SZ1 false (@BV 5 14%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fec4 : bv 32 := @BV 32 0x00e68023%Z I.

Lemma D_7fec4 : decode_any W_7fec4 = Some (Store SZ1 (@BV 5 13%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fec8 : bv 32 := @BV 32 0x00168693%Z I.

Lemma D_7fec8 : decode_any W_7fec8 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fecc : bv 32 := @BV 32 0x00158593%Z I.

Lemma D_7fecc : decode_any W_7fecc = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fed0 : bv 32 := @BV 32 0xfec698e3%Z I.

Lemma D_7fed0 : decode_any W_7fed0 = Some (Branch BC_NE (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 13 8176%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fed4 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_7fed4 : decode_any W_7fed4 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fed8 : bv 32 := @BV 32 0x02b57463%Z I.

Lemma D_7fed8 : decode_any W_7fed8 = Some (Branch BC_GEU (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 13 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fedc : bv 32 := @BV 32 0x04c05863%Z I.

Lemma D_7fedc : decode_any W_7fedc = Some (Branch BC_GE (@BV 5 0%Z I) (@BV 5 12%Z I) (@BV 13 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fee0 : bv 32 := @BV 32 0x00c50633%Z I.

Lemma D_7fee0 : decode_any W_7fee0 = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fee4 : bv 32 := @BV 32 0x00050693%Z I.

Lemma D_7fee4 : decode_any W_7fee4 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fee8 : bv 32 := @BV 32 0x0005c703%Z I.

Lemma D_7fee8 : decode_any W_7fee8 = Some (Load SZ1 false (@BV 5 14%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7feec : bv 32 := @BV 32 0x00e68023%Z I.

Lemma D_7feec : decode_any W_7feec = Some (Store SZ1 (@BV 5 13%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fef0 : bv 32 := @BV 32 0x00168693%Z I.

Lemma D_7fef0 : decode_any W_7fef0 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fef4 : bv 32 := @BV 32 0x00158593%Z I.

Lemma D_7fef4 : decode_any W_7fef4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fef8 : bv 32 := @BV 32 0xfec698e3%Z I.

Lemma D_7fef8 : decode_any W_7fef8 = Some (Branch BC_NE (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 13 8176%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7fefc : bv 32 := @BV 32 0x0300006f%Z I.

Lemma D_7fefc : decode_any W_7fefc = Some (Jal (@BV 5 0%Z I) (@BV 21 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff00 : bv 32 := @BV 32 0x02a5f663%Z I.

Lemma D_7ff00 : decode_any W_7ff00 = Some (Branch BC_GEU (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 13 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff04 : bv 32 := @BV 32 0x02c05463%Z I.

Lemma D_7ff04 : decode_any W_7ff04 = Some (Branch BC_GE (@BV 5 0%Z I) (@BV 5 12%Z I) (@BV 13 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff08 : bv 32 := @BV 32 0xfff60693%Z I.

Lemma D_7ff08 : decode_any W_7ff08 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff0c : bv 32 := @BV 32 0x00100613%Z I.

Lemma D_7ff0c : decode_any W_7ff0c = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff10 : bv 32 := @BV 32 0x00d58733%Z I.

Lemma D_7ff10 : decode_any W_7ff10 = Some (Op ALU_ADD (@BV 5 14%Z I) (@BV 5 11%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff14 : bv 32 := @BV 32 0x00074703%Z I.

Lemma D_7ff14 : decode_any W_7ff14 = Some (Load SZ1 false (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff18 : bv 32 := @BV 32 0x00d507b3%Z I.

Lemma D_7ff18 : decode_any W_7ff18 = Some (Op ALU_ADD (@BV 5 15%Z I) (@BV 5 10%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff1c : bv 32 := @BV 32 0x00168813%Z I.

Lemma D_7ff1c : decode_any W_7ff1c = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 13%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff20 : bv 32 := @BV 32 0xfff68693%Z I.

Lemma D_7ff20 : decode_any W_7ff20 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff24 : bv 32 := @BV 32 0x00e78023%Z I.

Lemma D_7ff24 : decode_any W_7ff24 = Some (Store SZ1 (@BV 5 15%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff28 : bv 32 := @BV 32 0xff0664e3%Z I.

Lemma D_7ff28 : decode_any W_7ff28 = Some (Branch BC_LTU (@BV 5 12%Z I) (@BV 5 16%Z I) (@BV 13 8168%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff2c : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_7ff2c : decode_any W_7ff2c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff30 : bv 32 := @BV 32 0x00a666b3%Z I.

Lemma D_7ff30 : decode_any W_7ff30 = Some (Op ALU_OR (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff34 : bv 32 := @BV 32 0x00f6f693%Z I.

Lemma D_7ff34 : decode_any W_7ff34 = Some (OpImm ALU_AND (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff38 : bv 32 := @BV 32 0x02068063%Z I.

Lemma D_7ff38 : decode_any W_7ff38 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff3c : bv 32 := @BV 32 0x04060863%Z I.

Lemma D_7ff3c : decode_any W_7ff3c = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff40 : bv 32 := @BV 32 0x00c50633%Z I.

Lemma D_7ff40 : decode_any W_7ff40 = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff44 : bv 32 := @BV 32 0x00050693%Z I.

Lemma D_7ff44 : decode_any W_7ff44 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff48 : bv 32 := @BV 32 0x00b68023%Z I.

Lemma D_7ff48 : decode_any W_7ff48 = Some (Store SZ1 (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff4c : bv 32 := @BV 32 0x00168693%Z I.

Lemma D_7ff4c : decode_any W_7ff4c = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff50 : bv 32 := @BV 32 0xfec69ce3%Z I.

Lemma D_7ff50 : decode_any W_7ff50 = Some (Branch BC_NE (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 13 8184%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff54 : bv 32 := @BV 32 0x0380006f%Z I.

Lemma D_7ff54 : decode_any W_7ff54 = Some (Jal (@BV 5 0%Z I) (@BV 21 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff58 : bv 32 := @BV 32 0x02060a63%Z I.

Lemma D_7ff58 : decode_any W_7ff58 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 52%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff5c : bv 32 := @BV 32 0x00c50633%Z I.

Lemma D_7ff5c : decode_any W_7ff5c = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff60 : bv 32 := @BV 32 0x00859693%Z I.

Lemma D_7ff60 : decode_any W_7ff60 = Some (ShiftImm ALU_SLL (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 6 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff64 : bv 32 := @BV 32 0x00b6e5b3%Z I.

Lemma D_7ff64 : decode_any W_7ff64 = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff68 : bv 32 := @BV 32 0x01059693%Z I.

Lemma D_7ff68 : decode_any W_7ff68 = Some (ShiftImm ALU_SLL (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 6 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff6c : bv 32 := @BV 32 0x00b6e5b3%Z I.

Lemma D_7ff6c : decode_any W_7ff6c = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff70 : bv 32 := @BV 32 0x02059693%Z I.

Lemma D_7ff70 : decode_any W_7ff70 = Some (ShiftImm ALU_SLL (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff74 : bv 32 := @BV 32 0x00b6e5b3%Z I.

Lemma D_7ff74 : decode_any W_7ff74 = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff78 : bv 32 := @BV 32 0x00050693%Z I.

Lemma D_7ff78 : decode_any W_7ff78 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff7c : bv 32 := @BV 32 0x00b6b023%Z I.

Lemma D_7ff7c : decode_any W_7ff7c = Some (Store SZ8 (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff80 : bv 32 := @BV 32 0x00b6b423%Z I.

Lemma D_7ff80 : decode_any W_7ff80 = Some (Store SZ8 (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff84 : bv 32 := @BV 32 0x01068693%Z I.

Lemma D_7ff84 : decode_any W_7ff84 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff88 : bv 32 := @BV 32 0xfec6eae3%Z I.

Lemma D_7ff88 : decode_any W_7ff88 = Some (Branch BC_LTU (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 13 8180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ff8c : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_7ff8c : decode_any W_7ff8c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80084 : bv 32 := @BV 32 0x00000593%Z I.

Lemma D_80084 : decode_any W_80084 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80088 : bv 32 := @BV 32 0x00b50633%Z I.

Lemma D_80088 : decode_any W_80088 = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8008c : bv 32 := @BV 32 0x00064603%Z I.

Lemma D_8008c : decode_any W_8008c = Some (Load SZ1 false (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80090 : bv 32 := @BV 32 0x00158593%Z I.

Lemma D_80090 : decode_any W_80090 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80094 : bv 32 := @BV 32 0xfe061ae3%Z I.

Lemma D_80094 : decode_any W_80094 = Some (Branch BC_NE (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 8180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80098 : bv 32 := @BV 32 0xfff58513%Z I.

Lemma D_80098 : decode_any W_80098 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8009c : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_8009c : decode_any W_8009c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8035c : bv 32 := @BV 32 0x06060663%Z I.

Lemma D_8035c : decode_any W_8035c = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 108%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80360 : bv 32 := @BV 32 0x00000693%Z I.

Lemma D_80360 : decode_any W_80360 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80364 : bv 32 := @BV 32 0x00d58733%Z I.

Lemma D_80364 : decode_any W_80364 = Some (Op ALU_ADD (@BV 5 14%Z I) (@BV 5 11%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80368 : bv 32 := @BV 32 0x00074703%Z I.

Lemma D_80368 : decode_any W_80368 = Some (Load SZ1 false (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8036c : bv 32 := @BV 32 0x00070c63%Z I.

Lemma D_8036c : decode_any W_8036c = Some (Branch BC_EQ (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 13 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80370 : bv 32 := @BV 32 0x00d507b3%Z I.

Lemma D_80370 : decode_any W_80370 = Some (Op ALU_ADD (@BV 5 15%Z I) (@BV 5 10%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80374 : bv 32 := @BV 32 0x00168693%Z I.

Lemma D_80374 : decode_any W_80374 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80378 : bv 32 := @BV 32 0x00e78023%Z I.

Lemma D_80378 : decode_any W_80378 = Some (Store SZ1 (@BV 5 15%Z I) (@BV 5 14%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8037c : bv 32 := @BV 32 0xfed614e3%Z I.

Lemma D_8037c : decode_any W_8037c = Some (Branch BC_NE (@BV 5 12%Z I) (@BV 5 13%Z I) (@BV 13 8168%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80380 : bv 32 := @BV 32 0x00060693%Z I.



(* [comment removed for export] *)
Definition W_80384 : bv 32 := @BV 32 0x00d505b3%Z I.

Lemma D_80384 : decode_any W_80384 = Some (Op ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80388 : bv 32 := @BV 32 0x40d6073b%Z I.

Lemma D_80388 : decode_any W_80388 = Some (Op32 ALU_SUB (@BV 5 14%Z I) (@BV 5 12%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8038c : bv 32 := @BV 32 0x00b76733%Z I.

Lemma D_8038c : decode_any W_8038c = Some (Op ALU_OR (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80390 : bv 32 := @BV 32 0x00f77713%Z I.

Lemma D_80390 : decode_any W_80390 = Some (OpImm ALU_AND (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 15%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80394 : bv 32 := @BV 32 0x00070e63%Z I.

Lemma D_80394 : decode_any W_80394 = Some (Branch BC_EQ (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80398 : bv 32 := @BV 32 0x02d60863%Z I.

Lemma D_80398 : decode_any W_80398 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 13%Z I) (@BV 13 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8039c : bv 32 := @BV 32 0x00c50633%Z I.

Lemma D_8039c : decode_any W_8039c = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_803a0 : bv 32 := @BV 32 0x00058023%Z I.

Lemma D_803a0 : decode_any W_803a0 = Some (Store SZ1 (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_803a4 : bv 32 := @BV 32 0x00158593%Z I.

Lemma D_803a4 : decode_any W_803a4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_803a8 : bv 32 := @BV 32 0xfec59ce3%Z I.

Lemma D_803a8 : decode_any W_803a8 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 13 8184%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_803ac : bv 32 := @BV 32 0x01c0006f%Z I.

Lemma D_803ac : decode_any W_803ac = Some (Jal (@BV 5 0%Z I) (@BV 21 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_803b0 : bv 32 := @BV 32 0x00d60c63%Z I.



(* [comment removed for export] *)
Definition W_803b4 : bv 32 := @BV 32 0x00c50633%Z I.



(* [comment removed for export] *)
Definition W_803b8 : bv 32 := @BV 32 0x0005b023%Z I.



(* [comment removed for export] *)
Definition W_803bc : bv 32 := @BV 32 0x0005b423%Z I.



(* [comment removed for export] *)
Definition W_803c0 : bv 32 := @BV 32 0x01058593%Z I.



(* [comment removed for export] *)
Definition W_803c4 : bv 32 := @BV 32 0xfec5eae3%Z I.



(* [comment removed for export] *)
Definition W_803c8 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_803c8 : decode_any W_803c8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80460 : bv 32 := @BV 32 0xff010113%Z I.

Lemma D_80460 : decode_any W_80460 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80464 : bv 32 := @BV 32 0x00113423%Z I.

Lemma D_80464 : decode_any W_80464 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80468 : bv 32 := @BV 32 0x00058693%Z I.

Lemma D_80468 : decode_any W_80468 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8046c : bv 32 := @BV 32 0x00100713%Z I.

Lemma D_8046c : decode_any W_8046c = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80470 : bv 32 := @BV 32 0x02871713%Z I.

Lemma D_80470 : decode_any W_80470 = Some (ShiftImm ALU_SLL (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 6 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80474 : bv 32 := @BV 32 0x00170593%Z I.

Lemma D_80474 : decode_any W_80474 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 14%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80478 : bv 32 := @BV 32 0x08b6f263%Z I.

Lemma D_80478 : decode_any W_80478 = Some (Branch BC_GEU (@BV 5 13%Z I) (@BV 5 11%Z I) (@BV 13 132%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8047c : bv 32 := @BV 32 0x00000593%Z I.

Lemma D_8047c : decode_any W_8047c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80480 : bv 32 := @BV 32 0x00d50733%Z I.

Lemma D_80480 : decode_any W_80480 = Some (Op ALU_ADD (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80484 : bv 32 := @BV 32 0x00750793%Z I.

Lemma D_80484 : decode_any W_80484 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 10%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80488 : bv 32 := @BV 32 0xff87f793%Z I.

Lemma D_80488 : decode_any W_80488 = Some (OpImm ALU_AND (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8048c : bv 32 := @BV 32 0xff877613%Z I.

Lemma D_8048c : decode_any W_8048c = Some (OpImm ALU_AND (@BV 5 12%Z I) (@BV 5 14%Z I) (@BV 12 4088%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80490 : bv 32 := @BV 32 0x02f57463%Z I.

Lemma D_80490 : decode_any W_80490 = Some (Branch BC_GEU (@BV 5 10%Z I) (@BV 5 15%Z I) (@BV 13 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80494 : bv 32 := @BV 32 0x02068263%Z I.

Lemma D_80494 : decode_any W_80494 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 36%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80498 : bv 32 := @BV 32 0x00000593%Z I.

Lemma D_80498 : decode_any W_80498 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8049c : bv 32 := @BV 32 0x00150693%Z I.

Lemma D_8049c : decode_any W_8049c = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804a0 : bv 32 := @BV 32 0x00068813%Z I.

Lemma D_804a0 : decode_any W_804a0 = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804a4 : bv 32 := @BV 32 0xfff6c683%Z I.

Lemma D_804a4 : decode_any W_804a4 = Some (Load SZ1 false (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804a8 : bv 32 := @BV 32 0x00d5e5b3%Z I.

Lemma D_804a8 : decode_any W_804a8 = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804ac : bv 32 := @BV 32 0x00f87663%Z I.

Lemma D_804ac : decode_any W_804ac = Some (Branch BC_GEU (@BV 5 16%Z I) (@BV 5 15%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804b0 : bv 32 := @BV 32 0x00180693%Z I.

Lemma D_804b0 : decode_any W_804b0 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 16%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804b4 : bv 32 := @BV 32 0xfee866e3%Z I.

Lemma D_804b4 : decode_any W_804b4 = Some (Branch BC_LTU (@BV 5 16%Z I) (@BV 5 14%Z I) (@BV 13 8172%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804b8 : bv 32 := @BV 32 0x00c7fa63%Z I.

Lemma D_804b8 : decode_any W_804b8 = Some (Branch BC_GEU (@BV 5 15%Z I) (@BV 5 12%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804bc : bv 32 := @BV 32 0x0007b683%Z I.

Lemma D_804bc : decode_any W_804bc = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 15%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804c0 : bv 32 := @BV 32 0x00878793%Z I.

Lemma D_804c0 : decode_any W_804c0 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 15%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804c4 : bv 32 := @BV 32 0x00b6e5b3%Z I.

Lemma D_804c4 : decode_any W_804c4 = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804c8 : bv 32 := @BV 32 0xfec7eae3%Z I.

Lemma D_804c8 : decode_any W_804c8 = Some (Branch BC_LTU (@BV 5 15%Z I) (@BV 5 12%Z I) (@BV 13 8180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804cc : bv 32 := @BV 32 0x02a66063%Z I.

Lemma D_804cc : decode_any W_804cc = Some (Branch BC_LTU (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 13 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804d0 : bv 32 := @BV 32 0x00e67e63%Z I.

Lemma D_804d0 : decode_any W_804d0 = Some (Branch BC_GEU (@BV 5 12%Z I) (@BV 5 14%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804d4 : bv 32 := @BV 32 0x40c70733%Z I.

Lemma D_804d4 : decode_any W_804d4 = Some (Op ALU_SUB (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804d8 : bv 32 := @BV 32 0x00064503%Z I.

Lemma D_804d8 : decode_any W_804d8 = Some (Load SZ1 false (@BV 5 10%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804dc : bv 32 := @BV 32 0xfff70713%Z I.

Lemma D_804dc : decode_any W_804dc = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804e0 : bv 32 := @BV 32 0x00a5e5b3%Z I.

Lemma D_804e0 : decode_any W_804e0 = Some (Op ALU_OR (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804e4 : bv 32 := @BV 32 0x00160613%Z I.

Lemma D_804e4 : decode_any W_804e4 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804e8 : bv 32 := @BV 32 0xfe0718e3%Z I.

Lemma D_804e8 : decode_any W_804e8 = Some (Branch BC_NE (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 13 8176%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804ec : bv 32 := @BV 32 0x0015b513%Z I.

Lemma D_804ec : decode_any W_804ec = Some (OpImm ALU_SLTU (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804f0 : bv 32 := @BV 32 0x00813083%Z I.

Lemma D_804f0 : decode_any W_804f0 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804f4 : bv 32 := @BV 32 0x01010113%Z I.

Lemma D_804f4 : decode_any W_804f4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_804f8 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_804f8 : decode_any W_804f8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80710 : bv 32 := @BV 32 0xfffff637%Z I.
Lemma F_80710 : fetch_word Asan.M.loaded_segments (@BV 64 0x80718%Z I : word) = Some W_80710.
Proof. vm_refl. Qed.
Lemma D_80710 : decode_any W_80710 = Some (Lui (@BV 5 12%Z I) (@BV 20 1048575%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80714 : bv 32 := @BV 32 0x0016069b%Z I.
Lemma F_80714 : fetch_word Asan.M.loaded_segments (@BV 64 0x8071c%Z I : word) = Some W_80714.
Proof. vm_refl. Qed.
Lemma D_80714 : decode_any W_80714 = Some (OpImm32 (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80718 : bv 32 := @BV 32 0x00d56863%Z I.
Lemma F_80718 : fetch_word Asan.M.loaded_segments (@BV 64 0x80720%Z I : word) = Some W_80718.
Proof. vm_refl. Qed.
Lemma D_80718 : decode_any W_80718 = Some (Branch BC_LTU (@BV 5 10%Z I) (@BV 5 13%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8071c : bv 32 := @BV 32 0x00058663%Z I.
Lemma F_8071c : fetch_word Asan.M.loaded_segments (@BV 64 0x80724%Z I : word) = Some W_8071c.
Proof. vm_refl. Qed.
Lemma D_8071c : decode_any W_8071c = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80720 : bv 32 := @BV 32 0x40a006bb%Z I.
Lemma F_80720 : fetch_word Asan.M.loaded_segments (@BV 64 0x80728%Z I : word) = Some W_80720.
Proof. vm_refl. Qed.
Lemma D_80720 : decode_any W_80720 = Some (Op32 ALU_SUB (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80724 : bv 32 := @BV 32 0x00d5a023%Z I.
Lemma F_80724 : fetch_word Asan.M.loaded_segments (@BV 64 0x8072c%Z I : word) = Some W_80724.
Proof. vm_refl. Qed.
Lemma D_80724 : decode_any W_80724 = Some (Store SZ4 (@BV 5 11%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80728 : bv 32 := @BV 32 0x00a63533%Z I.
Lemma F_80728 : fetch_word Asan.M.loaded_segments (@BV 64 0x80730%Z I : word) = Some W_80728.
Proof. vm_refl. Qed.
Lemma D_80728 : decode_any W_80728 = Some (Op ALU_SLTU (@BV 5 10%Z I) (@BV 5 12%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8072c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8072c : fetch_word Asan.M.loaded_segments (@BV 64 0x80734%Z I : word) = Some W_8072c.
Proof. vm_refl. Qed.
Lemma D_8072c : decode_any W_8072c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80730 : bv 32 := @BV 32 0x0de00893%Z I.
Lemma F_80730 : fetch_word Asan.M.loaded_segments (@BV 64 0x80738%Z I : word) = Some W_80730.
Proof. vm_refl. Qed.
Lemma D_80730 : decode_any W_80730 = Some (OpImm ALU_ADD (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 12 222%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80734 : bv 32 := @BV 32 0x00000073%Z I.
Lemma F_80734 : fetch_word Asan.M.loaded_segments (@BV 64 0x8073c%Z I : word) = Some W_80734.
Proof. vm_refl. Qed.

Lemma E_80734 : is_ecall W_80734 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_80738 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_80738 : fetch_word Asan.M.loaded_segments (@BV 64 0x80740%Z I : word) = Some W_80738.
Proof. vm_refl. Qed.
Lemma D_80738 : decode_any W_80738 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8073c : bv 32 := @BV 32 0x0d700893%Z I.
Lemma F_8073c : fetch_word Asan.M.loaded_segments (@BV 64 0x80744%Z I : word) = Some W_8073c.
Proof. vm_refl. Qed.
Lemma D_8073c : decode_any W_8073c = Some (OpImm ALU_ADD (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 12 215%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80740 : bv 32 := @BV 32 0x00000073%Z I.
Lemma F_80740 : fetch_word Asan.M.loaded_segments (@BV 64 0x80748%Z I : word) = Some W_80740.
Proof. vm_refl. Qed.

Lemma E_80740 : is_ecall W_80740 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_80744 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_80744 : fetch_word Asan.M.loaded_segments (@BV 64 0x8074c%Z I : word) = Some W_80744.
Proof. vm_refl. Qed.
Lemma D_80744 : decode_any W_80744 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80758 : bv 32 := @BV 32 0x0007f697%Z I.
Lemma F_80758 : fetch_word Asan.M.loaded_segments (@BV 64 0x80760%Z I : word) = Some W_80758.
Proof. vm_refl. Qed.
Lemma D_80758 : decode_any W_80758 = Some (Auipc (@BV 5 13%Z I) (@BV 20 127%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8075c : bv 32 := @BV 32 0xb506b683%Z I.
Lemma F_8075c : fetch_word Asan.M.loaded_segments (@BV 64 0x80764%Z I : word) = Some W_8075c.
Proof. vm_refl. Qed.
Lemma D_8075c : decode_any W_8075c = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 2896%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80760 : bv 32 := @BV 32 0x00068a63%Z I.
Lemma F_80760 : fetch_word Asan.M.loaded_segments (@BV 64 0x80768%Z I : word) = Some W_80760.
Proof. vm_refl. Qed.
Lemma D_80760 : decode_any W_80760 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80764 : bv 32 := @BV 32 0x00400693%Z I.
Lemma F_80764 : fetch_word Asan.M.loaded_segments (@BV 64 0x8076c%Z I : word) = Some W_80764.
Proof. vm_refl. Qed.
Lemma D_80764 : decode_any W_80764 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80768 : bv 32 := @BV 32 0x00d60663%Z I.
Lemma F_80768 : fetch_word Asan.M.loaded_segments (@BV 64 0x80770%Z I : word) = Some W_80768.
Proof. vm_refl. Qed.
Lemma D_80768 : decode_any W_80768 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 13%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8076c : bv 32 := @BV 32 0x0000051b%Z I.



(* [comment removed for export] *)
Definition W_80770 : bv 32 := @BV 32 0x00008067%Z I.



(* [comment removed for export] *)
Definition W_80774 : bv 32 := @BV 32 0x0e900893%Z I.
Lemma F_80774 : fetch_word Asan.M.loaded_segments (@BV 64 0x8077c%Z I : word) = Some W_80774.
Proof. vm_refl. Qed.
Lemma D_80774 : decode_any W_80774 = Some (OpImm ALU_ADD (@BV 5 17%Z I) (@BV 5 0%Z I) (@BV 12 233%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80778 : bv 32 := @BV 32 0x00000073%Z I.


Lemma E_80778 : is_ecall W_80778 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_8077c : bv 32 := @BV 32 0x0005051b%Z I.

Lemma D_8077c : decode_any W_8077c = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80780 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_80780 : decode_any W_80780 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.






















(* [comment removed for export] *)
Definition W_81e00 : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_81e00 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e08%Z I : word) = Some W_81e00.
Proof. vm_refl. Qed.
Lemma D_81e00 : decode_any W_81e00 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e04 : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_81e04 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e0c%Z I : word) = Some W_81e04.
Proof. vm_refl. Qed.
Lemma D_81e04 : decode_any W_81e04 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e08 : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_81e08 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e10%Z I : word) = Some W_81e08.
Proof. vm_refl. Qed.
Lemma D_81e08 : decode_any W_81e08 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e0c : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_81e0c : fetch_word Asan.M.loaded_segments (@BV 64 0x81e14%Z I : word) = Some W_81e0c.
Proof. vm_refl. Qed.
Lemma D_81e0c : decode_any W_81e0c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e10 : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_81e10 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e18%Z I : word) = Some W_81e10.
Proof. vm_refl. Qed.
Lemma D_81e10 : decode_any W_81e10 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e14 : bv 32 := @BV 32 0x01313423%Z I.
Lemma F_81e14 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e1c%Z I : word) = Some W_81e14.
Proof. vm_refl. Qed.
Lemma D_81e14 : decode_any W_81e14 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e18 : bv 32 := @BV 32 0x00060413%Z I.
Lemma F_81e18 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e20%Z I : word) = Some W_81e18.
Proof. vm_refl. Qed.
Lemma D_81e18 : decode_any W_81e18 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e1c : bv 32 := @BV 32 0x00058493%Z I.
Lemma F_81e1c : fetch_word Asan.M.loaded_segments (@BV 64 0x81e24%Z I : word) = Some W_81e1c.
Proof. vm_refl. Qed.
Lemma D_81e1c : decode_any W_81e1c = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e20 : bv 32 := @BV 32 0x0007d597%Z I.
Lemma F_81e20 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e28%Z I : word) = Some W_81e20.
Proof. vm_refl. Qed.
Lemma D_81e20 : decode_any W_81e20 = Some (Auipc (@BV 5 11%Z I) (@BV 20 125%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e24 : bv 32 := @BV 32 0x4285b983%Z I.
Lemma F_81e24 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e2c%Z I : word) = Some W_81e24.
Proof. vm_refl. Qed.
Lemma D_81e24 : decode_any W_81e24 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 11%Z I) (@BV 12 1064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e28 : bv 32 := @BV 32 0x0009b583%Z I.
Lemma F_81e28 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e30%Z I : word) = Some W_81e28.
Proof. vm_refl. Qed.
Lemma D_81e28 : decode_any W_81e28 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e2c : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_81e2c : fetch_word Asan.M.loaded_segments (@BV 64 0x81e34%Z I : word) = Some W_81e2c.
Proof. vm_refl. Qed.
Lemma D_81e2c : decode_any W_81e2c = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e30 : bv 32 := @BV 32 0x00059863%Z I.
Lemma F_81e30 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e38%Z I : word) = Some W_81e30.
Proof. vm_refl. Qed.
Lemma D_81e30 : decode_any W_81e30 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e40 : bv 32 := @BV 32 0xfff58513%Z I.
Lemma F_81e40 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e48%Z I : word) = Some W_81e40.
Proof. vm_refl. Qed.
Lemma D_81e40 : decode_any W_81e40 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e44 : bv 32 := @BV 32 0x00a5f533%Z I.
Lemma F_81e44 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e4c%Z I : word) = Some W_81e44.
Proof. vm_refl. Qed.
Lemma D_81e44 : decode_any W_81e44 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e48 : bv 32 := @BV 32 0x08051c63%Z I.
Lemma F_81e48 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e50%Z I : word) = Some W_81e48.
Proof. vm_refl. Qed.
Lemma D_81e48 : decode_any W_81e48 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e4c : bv 32 := @BV 32 0x00b90933%Z I.
Lemma F_81e4c : fetch_word Asan.M.loaded_segments (@BV 64 0x81e54%Z I : word) = Some W_81e4c.
Proof. vm_refl. Qed.
Lemma D_81e4c : decode_any W_81e4c = Some (Op ALU_ADD (@BV 5 18%Z I) (@BV 5 18%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e50 : bv 32 := @BV 32 0x40b00533%Z I.
Lemma F_81e50 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e58%Z I : word) = Some W_81e50.
Proof. vm_refl. Qed.
Lemma D_81e50 : decode_any W_81e50 = Some (Op ALU_SUB (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e54 : bv 32 := @BV 32 0xfff90913%Z I.
Lemma F_81e54 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e5c%Z I : word) = Some W_81e54.
Proof. vm_refl. Qed.
Lemma D_81e54 : decode_any W_81e54 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 18%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e58 : bv 32 := @BV 32 0x00a97933%Z I.
Lemma F_81e58 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e60%Z I : word) = Some W_81e58.
Proof. vm_refl. Qed.
Lemma D_81e58 : decode_any W_81e58 = Some (Op ALU_AND (@BV 5 18%Z I) (@BV 5 18%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e5c : bv 32 := @BV 32 0x02200513%Z I.
Lemma F_81e5c : fetch_word Asan.M.loaded_segments (@BV 64 0x81e64%Z I : word) = Some W_81e5c.
Proof. vm_refl. Qed.
Lemma D_81e5c : decode_any W_81e5c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 34%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e60 : bv 32 := @BV 32 0x00a12223%Z I.
Lemma F_81e60 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e68%Z I : word) = Some W_81e60.
Proof. vm_refl. Qed.
Lemma D_81e60 : decode_any W_81e60 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e64 : bv 32 := @BV 32 0x00410613%Z I.
Lemma F_81e64 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e6c%Z I : word) = Some W_81e64.
Proof. vm_refl. Qed.
Lemma D_81e64 : decode_any W_81e64 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e68 : bv 32 := @BV 32 0x00048513%Z I.
Lemma F_81e68 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e70%Z I : word) = Some W_81e68.
Proof. vm_refl. Qed.
Lemma D_81e68 : decode_any W_81e68 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e6c : bv 32 := @BV 32 0x00090593%Z I.
Lemma F_81e6c : fetch_word Asan.M.loaded_segments (@BV 64 0x81e74%Z I : word) = Some W_81e6c.
Proof. vm_refl. Qed.
Lemma D_81e6c : decode_any W_81e6c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e70 : bv 32 := @BV 32 0x46d000ef%Z I.
Lemma F_81e70 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e78%Z I : word) = Some W_81e70.
Proof. vm_refl. Qed.
Lemma D_81e70 : decode_any W_81e70 = Some (Jal (@BV 5 1%Z I) (@BV 21 3180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e74 : bv 32 := @BV 32 0x00412683%Z I.
Lemma F_81e74 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e7c%Z I : word) = Some W_81e74.
Proof. vm_refl. Qed.
Lemma D_81e74 : decode_any W_81e74 = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e78 : bv 32 := @BV 32 0x00050713%Z I.
Lemma F_81e78 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e80%Z I : word) = Some W_81e78.
Proof. vm_refl. Qed.
Lemma D_81e78 : decode_any W_81e78 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e7c : bv 32 := @BV 32 0x00300613%Z I.
Lemma F_81e7c : fetch_word Asan.M.loaded_segments (@BV 64 0x81e84%Z I : word) = Some W_81e7c.
Proof. vm_refl. Qed.
Lemma D_81e7c : decode_any W_81e7c = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e80 : bv 32 := @BV 32 0x00000513%Z I.
Lemma F_81e80 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e88%Z I : word) = Some W_81e80.
Proof. vm_refl. Qed.
Lemma D_81e80 : decode_any W_81e80 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e84 : bv 32 := @BV 32 0x00090593%Z I.
Lemma F_81e84 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e8c%Z I : word) = Some W_81e84.
Proof. vm_refl. Qed.
Lemma D_81e84 : decode_any W_81e84 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e88 : bv 32 := @BV 32 0x00000793%Z I.
Lemma F_81e88 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e90%Z I : word) = Some W_81e88.
Proof. vm_refl. Qed.
Lemma D_81e88 : decode_any W_81e88 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e8c : bv 32 := @BV 32 0x8a5fe0ef%Z I.
Lemma F_81e8c : fetch_word Asan.M.loaded_segments (@BV 64 0x81e94%Z I : word) = Some W_81e8c.
Proof. vm_refl. Qed.
Lemma D_81e8c : decode_any W_81e8c = Some (Jal (@BV 5 1%Z I) (@BV 21 2091172%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e90 : bv 32 := @BV 32 0x00050993%Z I.
Lemma F_81e90 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e98%Z I : word) = Some W_81e90.
Proof. vm_refl. Qed.
Lemma D_81e90 : decode_any W_81e90 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e94 : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_81e94 : fetch_word Asan.M.loaded_segments (@BV 64 0x81e9c%Z I : word) = Some W_81e94.
Proof. vm_refl. Qed.
Lemma D_81e94 : decode_any W_81e94 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e98 : bv 32 := @BV 32 0x879fe0ef%Z I.
Lemma F_81e98 : fetch_word Asan.M.loaded_segments (@BV 64 0x81ea0%Z I : word) = Some W_81e98.
Proof. vm_refl. Qed.
Lemma D_81e98 : decode_any W_81e98 = Some (Jal (@BV 5 1%Z I) (@BV 21 2091128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e9c : bv 32 := @BV 32 0xaaaab537%Z I.
Lemma F_81e9c : fetch_word Asan.M.loaded_segments (@BV 64 0x81ea4%Z I : word) = Some W_81e9c.
Proof. vm_refl. Qed.
Lemma D_81e9c : decode_any W_81e9c = Some (Lui (@BV 5 10%Z I) (@BV 20 699051%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ea0 : bv 32 := @BV 32 0xaaa50513%Z I.
Lemma F_81ea0 : fetch_word Asan.M.loaded_segments (@BV 64 0x81ea8%Z I : word) = Some W_81ea0.
Proof. vm_refl. Qed.
Lemma D_81ea0 : decode_any W_81ea0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2730%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ea4 : bv 32 := @BV 32 0x00a12023%Z I.
Lemma F_81ea4 : fetch_word Asan.M.loaded_segments (@BV 64 0x81eac%Z I : word) = Some W_81ea4.
Proof. vm_refl. Qed.
Lemma D_81ea4 : decode_any W_81ea4 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ea8 : bv 32 := @BV 32 0x00010593%Z I.
Lemma F_81ea8 : fetch_word Asan.M.loaded_segments (@BV 64 0x81eb0%Z I : word) = Some W_81ea8.
Proof. vm_refl. Qed.
Lemma D_81ea8 : decode_any W_81ea8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81eac : bv 32 := @BV 32 0x00098513%Z I.
Lemma F_81eac : fetch_word Asan.M.loaded_segments (@BV 64 0x81eb4%Z I : word) = Some W_81eac.
Proof. vm_refl. Qed.
Lemma D_81eac : decode_any W_81eac = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81eb0 : bv 32 := @BV 32 0x861fe0ef%Z I.
Lemma F_81eb0 : fetch_word Asan.M.loaded_segments (@BV 64 0x81eb8%Z I : word) = Some W_81eb0.
Proof. vm_refl. Qed.
Lemma D_81eb0 : decode_any W_81eb0 = Some (Jal (@BV 5 1%Z I) (@BV 21 2091104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81eb4 : bv 32 := @BV 32 0x02051e63%Z I.
Lemma F_81eb4 : fetch_word Asan.M.loaded_segments (@BV 64 0x81ebc%Z I : word) = Some W_81eb4.
Proof. vm_refl. Qed.
Lemma D_81eb4 : decode_any W_81eb4 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81eb8 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_81eb8 : fetch_word Asan.M.loaded_segments (@BV 64 0x81ec0%Z I : word) = Some W_81eb8.
Proof. vm_refl. Qed.
Lemma D_81eb8 : decode_any W_81eb8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ebc : bv 32 := @BV 32 0xf58fa0ef%Z I.
Lemma F_81ebc : fetch_word Asan.M.loaded_segments (@BV 64 0x81ec4%Z I : word) = Some W_81ebc.
Proof. vm_refl. Qed.
Lemma D_81ebc : decode_any W_81ebc = Some (Jal (@BV 5 1%Z I) (@BV 21 2074456%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ec0 : bv 32 := @BV 32 0x00098513%Z I.
Lemma F_81ec0 : fetch_word Asan.M.loaded_segments (@BV 64 0x81ec8%Z I : word) = Some W_81ec0.
Proof. vm_refl. Qed.
Lemma D_81ec0 : decode_any W_81ec0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ec4 : bv 32 := @BV 32 0x02813083%Z I.
Lemma F_81ec4 : fetch_word Asan.M.loaded_segments (@BV 64 0x81ecc%Z I : word) = Some W_81ec4.
Proof. vm_refl. Qed.
Lemma D_81ec4 : decode_any W_81ec4 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ec8 : bv 32 := @BV 32 0x02013403%Z I.
Lemma F_81ec8 : fetch_word Asan.M.loaded_segments (@BV 64 0x81ed0%Z I : word) = Some W_81ec8.
Proof. vm_refl. Qed.
Lemma D_81ec8 : decode_any W_81ec8 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ecc : bv 32 := @BV 32 0x01813483%Z I.
Lemma F_81ecc : fetch_word Asan.M.loaded_segments (@BV 64 0x81ed4%Z I : word) = Some W_81ecc.
Proof. vm_refl. Qed.
Lemma D_81ecc : decode_any W_81ecc = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ed0 : bv 32 := @BV 32 0x01013903%Z I.
Lemma F_81ed0 : fetch_word Asan.M.loaded_segments (@BV 64 0x81ed8%Z I : word) = Some W_81ed0.
Proof. vm_refl. Qed.
Lemma D_81ed0 : decode_any W_81ed0 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ed4 : bv 32 := @BV 32 0x00813983%Z I.
Lemma F_81ed4 : fetch_word Asan.M.loaded_segments (@BV 64 0x81edc%Z I : word) = Some W_81ed4.
Proof. vm_refl. Qed.
Lemma D_81ed4 : decode_any W_81ed4 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ed8 : bv 32 := @BV 32 0x03010113%Z I.
Lemma F_81ed8 : fetch_word Asan.M.loaded_segments (@BV 64 0x81ee0%Z I : word) = Some W_81ed8.
Proof. vm_refl. Qed.
Lemma D_81ed8 : decode_any W_81ed8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81edc : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_81edc : fetch_word Asan.M.loaded_segments (@BV 64 0x81ee4%Z I : word) = Some W_81edc.
Proof. vm_refl. Qed.
Lemma D_81edc : decode_any W_81edc = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ef0 : bv 32 := @BV 32 0x00012683%Z I.
Lemma F_81ef0 : fetch_word Asan.M.loaded_segments (@BV 64 0x81ef8%Z I : word) = Some W_81ef0.
Proof. vm_refl. Qed.
Lemma D_81ef0 : decode_any W_81ef0 = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ef4 : bv 32 := @BV 32 0xfff99517%Z I.
Lemma F_81ef4 : fetch_word Asan.M.loaded_segments (@BV 64 0x81efc%Z I : word) = Some W_81ef4.
Proof. vm_refl. Qed.
Lemma D_81ef4 : decode_any W_81ef4 = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048473%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ef8 : bv 32 := @BV 32 0xe4b50613%Z I.
Lemma F_81ef8 : fetch_word Asan.M.loaded_segments (@BV 64 0x81f00%Z I : word) = Some W_81ef8.
Proof. vm_refl. Qed.
Lemma D_81ef8 : decode_any W_81ef8 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 3659%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81efc : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_81efc : fetch_word Asan.M.loaded_segments (@BV 64 0x81f04%Z I : word) = Some W_81efc.
Proof. vm_refl. Qed.
Lemma D_81efc : decode_any W_81efc = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f00 : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_81f00 : fetch_word Asan.M.loaded_segments (@BV 64 0x81f08%Z I : word) = Some W_81f00.
Proof. vm_refl. Qed.
Lemma D_81f00 : decode_any W_81f00 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f04 : bv 32 := @BV 32 0x00040713%Z I.
Lemma F_81f04 : fetch_word Asan.M.loaded_segments (@BV 64 0x81f0c%Z I : word) = Some W_81f04.
Proof. vm_refl. Qed.
Lemma D_81f04 : decode_any W_81f04 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f08 : bv 32 := @BV 32 0x874fa0ef%Z I.
Lemma F_81f08 : fetch_word Asan.M.loaded_segments (@BV 64 0x81f10%Z I : word) = Some W_81f08.
Proof. vm_refl. Qed.
Lemma D_81f08 : decode_any W_81f08 = Some (Jal (@BV 5 1%Z I) (@BV 21 2072692%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f80 : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_81f80 : fetch_word Asan.M.loaded_segments (@BV 64 0x81f88%Z I : word) = Some W_81f80.
Proof. vm_refl. Qed.
Lemma D_81f80 : decode_any W_81f80 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f84 : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_81f84 : fetch_word Asan.M.loaded_segments (@BV 64 0x81f8c%Z I : word) = Some W_81f84.
Proof. vm_refl. Qed.
Lemma D_81f84 : decode_any W_81f84 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f88 : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_81f88 : fetch_word Asan.M.loaded_segments (@BV 64 0x81f90%Z I : word) = Some W_81f88.
Proof. vm_refl. Qed.
Lemma D_81f88 : decode_any W_81f88 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f8c : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_81f8c : fetch_word Asan.M.loaded_segments (@BV 64 0x81f94%Z I : word) = Some W_81f8c.
Proof. vm_refl. Qed.
Lemma D_81f8c : decode_any W_81f8c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f90 : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_81f90 : fetch_word Asan.M.loaded_segments (@BV 64 0x81f98%Z I : word) = Some W_81f90.
Proof. vm_refl. Qed.
Lemma D_81f90 : decode_any W_81f90 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f94 : bv 32 := @BV 32 0x02050e63%Z I.
Lemma F_81f94 : fetch_word Asan.M.loaded_segments (@BV 64 0x81f9c%Z I : word) = Some W_81f94.
Proof. vm_refl. Qed.
Lemma D_81f94 : decode_any W_81f94 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f98 : bv 32 := @BV 32 0x00058413%Z I.
Lemma F_81f98 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fa0%Z I : word) = Some W_81f98.
Proof. vm_refl. Qed.
Lemma D_81f98 : decode_any W_81f98 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f9c : bv 32 := @BV 32 0x02058a63%Z I.
Lemma F_81f9c : fetch_word Asan.M.loaded_segments (@BV 64 0x81fa4%Z I : word) = Some W_81f9c.
Proof. vm_refl. Qed.
Lemma D_81f9c : decode_any W_81f9c = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 52%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fa0 : bv 32 := @BV 32 0x00060493%Z I.
Lemma F_81fa0 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fa8%Z I : word) = Some W_81fa0.
Proof. vm_refl. Qed.
Lemma D_81fa0 : decode_any W_81fa0 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fa4 : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_81fa4 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fac%Z I : word) = Some W_81fa4.
Proof. vm_refl. Qed.
Lemma D_81fa4 : decode_any W_81fa4 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fa8 : bv 32 := @BV 32 0x00040593%Z I.
Lemma F_81fa8 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fb0%Z I : word) = Some W_81fa8.
Proof. vm_refl. Qed.
Lemma D_81fa8 : decode_any W_81fa8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fac : bv 32 := @BV 32 0xf90fe0ef%Z I.
Lemma F_81fac : fetch_word Asan.M.loaded_segments (@BV 64 0x81fb4%Z I : word) = Some W_81fac.
Proof. vm_refl. Qed.
Lemma D_81fac : decode_any W_81fac = Some (Jal (@BV 5 1%Z I) (@BV 21 2090896%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fb0 : bv 32 := @BV 32 0xaaaab5b7%Z I.
Lemma F_81fb0 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fb8%Z I : word) = Some W_81fb0.
Proof. vm_refl. Qed.
Lemma D_81fb0 : decode_any W_81fb0 = Some (Lui (@BV 5 11%Z I) (@BV 20 699051%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fb4 : bv 32 := @BV 32 0xaaa58593%Z I.
Lemma F_81fb4 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fbc%Z I : word) = Some W_81fb4.
Proof. vm_refl. Qed.
Lemma D_81fb4 : decode_any W_81fb4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 2730%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fb8 : bv 32 := @BV 32 0x00b12623%Z I.
Lemma F_81fb8 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fc0%Z I : word) = Some W_81fb8.
Proof. vm_refl. Qed.
Lemma D_81fb8 : decode_any W_81fb8 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 11%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fbc : bv 32 := @BV 32 0x00c10593%Z I.
Lemma F_81fbc : fetch_word Asan.M.loaded_segments (@BV 64 0x81fc4%Z I : word) = Some W_81fbc.
Proof. vm_refl. Qed.
Lemma D_81fbc : decode_any W_81fbc = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fc0 : bv 32 := @BV 32 0xf50fe0ef%Z I.
Lemma F_81fc0 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fc8%Z I : word) = Some W_81fc0.
Proof. vm_refl. Qed.
Lemma D_81fc0 : decode_any W_81fc0 = Some (Jal (@BV 5 1%Z I) (@BV 21 2090832%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fc4 : bv 32 := @BV 32 0x02051263%Z I.
Lemma F_81fc4 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fcc%Z I : word) = Some W_81fc4.
Proof. vm_refl. Qed.
Lemma D_81fc4 : decode_any W_81fc4 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 36%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fc8 : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_81fc8 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fd0%Z I : word) = Some W_81fc8.
Proof. vm_refl. Qed.
Lemma D_81fc8 : decode_any W_81fc8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fcc : bv 32 := @BV 32 0xe8cfa0ef%Z I.
Lemma F_81fcc : fetch_word Asan.M.loaded_segments (@BV 64 0x81fd4%Z I : word) = Some W_81fcc.
Proof. vm_refl. Qed.
Lemma D_81fcc : decode_any W_81fcc = Some (Jal (@BV 5 1%Z I) (@BV 21 2074252%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fd0 : bv 32 := @BV 32 0x02813083%Z I.
Lemma F_81fd0 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fd8%Z I : word) = Some W_81fd0.
Proof. vm_refl. Qed.
Lemma D_81fd0 : decode_any W_81fd0 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fd4 : bv 32 := @BV 32 0x02013403%Z I.
Lemma F_81fd4 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fdc%Z I : word) = Some W_81fd4.
Proof. vm_refl. Qed.
Lemma D_81fd4 : decode_any W_81fd4 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fd8 : bv 32 := @BV 32 0x01813483%Z I.
Lemma F_81fd8 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fe0%Z I : word) = Some W_81fd8.
Proof. vm_refl. Qed.
Lemma D_81fd8 : decode_any W_81fd8 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fdc : bv 32 := @BV 32 0x01013903%Z I.
Lemma F_81fdc : fetch_word Asan.M.loaded_segments (@BV 64 0x81fe4%Z I : word) = Some W_81fdc.
Proof. vm_refl. Qed.
Lemma D_81fdc : decode_any W_81fdc = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fe0 : bv 32 := @BV 32 0x03010113%Z I.
Lemma F_81fe0 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fe8%Z I : word) = Some W_81fe0.
Proof. vm_refl. Qed.
Lemma D_81fe0 : decode_any W_81fe0 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fe4 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_81fe4 : fetch_word Asan.M.loaded_segments (@BV 64 0x81fec%Z I : word) = Some W_81fe4.
Proof. vm_refl. Qed.
Lemma D_81fe4 : decode_any W_81fe4 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ffc : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_81ffc : fetch_word Asan.M.loaded_segments (@BV 64 0x82004%Z I : word) = Some W_81ffc.
Proof. vm_refl. Qed.
Lemma D_81ffc : decode_any W_81ffc = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82000 : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_82000 : fetch_word Asan.M.loaded_segments (@BV 64 0x82008%Z I : word) = Some W_82000.
Proof. vm_refl. Qed.
Lemma D_82000 : decode_any W_82000 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82004 : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_82004 : fetch_word Asan.M.loaded_segments (@BV 64 0x8200c%Z I : word) = Some W_82004.
Proof. vm_refl. Qed.
Lemma D_82004 : decode_any W_82004 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82008 : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_82008 : fetch_word Asan.M.loaded_segments (@BV 64 0x82010%Z I : word) = Some W_82008.
Proof. vm_refl. Qed.
Lemma D_82008 : decode_any W_82008 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8200c : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_8200c : fetch_word Asan.M.loaded_segments (@BV 64 0x82014%Z I : word) = Some W_8200c.
Proof. vm_refl. Qed.
Lemma D_8200c : decode_any W_8200c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82010 : bv 32 := @BV 32 0x00058413%Z I.
Lemma F_82010 : fetch_word Asan.M.loaded_segments (@BV 64 0x82018%Z I : word) = Some W_82010.
Proof. vm_refl. Qed.
Lemma D_82010 : decode_any W_82010 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82014 : bv 32 := @BV 32 0x0007d597%Z I.
Lemma F_82014 : fetch_word Asan.M.loaded_segments (@BV 64 0x8201c%Z I : word) = Some W_82014.
Proof. vm_refl. Qed.
Lemma D_82014 : decode_any W_82014 = Some (Auipc (@BV 5 11%Z I) (@BV 20 125%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82018 : bv 32 := @BV 32 0x2345b903%Z I.
Lemma F_82018 : fetch_word Asan.M.loaded_segments (@BV 64 0x82020%Z I : word) = Some W_82018.
Proof. vm_refl. Qed.
Lemma D_82018 : decode_any W_82018 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 11%Z I) (@BV 12 564%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8201c : bv 32 := @BV 32 0x00093583%Z I.
Lemma F_8201c : fetch_word Asan.M.loaded_segments (@BV 64 0x82024%Z I : word) = Some W_8201c.
Proof. vm_refl. Qed.
Lemma D_8201c : decode_any W_8201c = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82020 : bv 32 := @BV 32 0x00050493%Z I.
Lemma F_82020 : fetch_word Asan.M.loaded_segments (@BV 64 0x82028%Z I : word) = Some W_82020.
Proof. vm_refl. Qed.
Lemma D_82020 : decode_any W_82020 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82024 : bv 32 := @BV 32 0x00059863%Z I.
Lemma F_82024 : fetch_word Asan.M.loaded_segments (@BV 64 0x8202c%Z I : word) = Some W_82024.
Proof. vm_refl. Qed.
Lemma D_82024 : decode_any W_82024 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82034 : bv 32 := @BV 32 0xfff58513%Z I.
Lemma F_82034 : fetch_word Asan.M.loaded_segments (@BV 64 0x8203c%Z I : word) = Some W_82034.
Proof. vm_refl. Qed.
Lemma D_82034 : decode_any W_82034 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82038 : bv 32 := @BV 32 0x00a5f533%Z I.
Lemma F_82038 : fetch_word Asan.M.loaded_segments (@BV 64 0x82040%Z I : word) = Some W_82038.
Proof. vm_refl. Qed.
Lemma D_82038 : decode_any W_82038 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8203c : bv 32 := @BV 32 0x08051a63%Z I.
Lemma F_8203c : fetch_word Asan.M.loaded_segments (@BV 64 0x82044%Z I : word) = Some W_8203c.
Proof. vm_refl. Qed.
Lemma D_8203c : decode_any W_8203c = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 148%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82040 : bv 32 := @BV 32 0x00b484b3%Z I.
Lemma F_82040 : fetch_word Asan.M.loaded_segments (@BV 64 0x82048%Z I : word) = Some W_82040.
Proof. vm_refl. Qed.
Lemma D_82040 : decode_any W_82040 = Some (Op ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82044 : bv 32 := @BV 32 0x40b00533%Z I.
Lemma F_82044 : fetch_word Asan.M.loaded_segments (@BV 64 0x8204c%Z I : word) = Some W_82044.
Proof. vm_refl. Qed.
Lemma D_82044 : decode_any W_82044 = Some (Op ALU_SUB (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82048 : bv 32 := @BV 32 0xfff48493%Z I.
Lemma F_82048 : fetch_word Asan.M.loaded_segments (@BV 64 0x82050%Z I : word) = Some W_82048.
Proof. vm_refl. Qed.
Lemma D_82048 : decode_any W_82048 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8204c : bv 32 := @BV 32 0x00a4f4b3%Z I.
Lemma F_8204c : fetch_word Asan.M.loaded_segments (@BV 64 0x82054%Z I : word) = Some W_8204c.
Proof. vm_refl. Qed.
Lemma D_8204c : decode_any W_8204c = Some (Op ALU_AND (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82050 : bv 32 := @BV 32 0x02200513%Z I.
Lemma F_82050 : fetch_word Asan.M.loaded_segments (@BV 64 0x82058%Z I : word) = Some W_82050.
Proof. vm_refl. Qed.
Lemma D_82050 : decode_any W_82050 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 34%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82054 : bv 32 := @BV 32 0x00a12623%Z I.
Lemma F_82054 : fetch_word Asan.M.loaded_segments (@BV 64 0x8205c%Z I : word) = Some W_82054.
Proof. vm_refl. Qed.
Lemma D_82054 : decode_any W_82054 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82058 : bv 32 := @BV 32 0x00c10613%Z I.
Lemma F_82058 : fetch_word Asan.M.loaded_segments (@BV 64 0x82060%Z I : word) = Some W_82058.
Proof. vm_refl. Qed.
Lemma D_82058 : decode_any W_82058 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8205c : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_8205c : fetch_word Asan.M.loaded_segments (@BV 64 0x82064%Z I : word) = Some W_8205c.
Proof. vm_refl. Qed.
Lemma D_8205c : decode_any W_8205c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82060 : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_82060 : fetch_word Asan.M.loaded_segments (@BV 64 0x82068%Z I : word) = Some W_82060.
Proof. vm_refl. Qed.
Lemma D_82060 : decode_any W_82060 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82064 : bv 32 := @BV 32 0x279000ef%Z I.
Lemma F_82064 : fetch_word Asan.M.loaded_segments (@BV 64 0x8206c%Z I : word) = Some W_82064.
Proof. vm_refl. Qed.
Lemma D_82064 : decode_any W_82064 = Some (Jal (@BV 5 1%Z I) (@BV 21 2680%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82068 : bv 32 := @BV 32 0x00c12683%Z I.
Lemma F_82068 : fetch_word Asan.M.loaded_segments (@BV 64 0x82070%Z I : word) = Some W_82068.
Proof. vm_refl. Qed.
Lemma D_82068 : decode_any W_82068 = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8206c : bv 32 := @BV 32 0x00050713%Z I.
Lemma F_8206c : fetch_word Asan.M.loaded_segments (@BV 64 0x82074%Z I : word) = Some W_8206c.
Proof. vm_refl. Qed.
Lemma D_8206c : decode_any W_8206c = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82070 : bv 32 := @BV 32 0x00300613%Z I.
Lemma F_82070 : fetch_word Asan.M.loaded_segments (@BV 64 0x82078%Z I : word) = Some W_82070.
Proof. vm_refl. Qed.
Lemma D_82070 : decode_any W_82070 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82074 : bv 32 := @BV 32 0x00000513%Z I.
Lemma F_82074 : fetch_word Asan.M.loaded_segments (@BV 64 0x8207c%Z I : word) = Some W_82074.
Proof. vm_refl. Qed.
Lemma D_82074 : decode_any W_82074 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82078 : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_82078 : fetch_word Asan.M.loaded_segments (@BV 64 0x82080%Z I : word) = Some W_82078.
Proof. vm_refl. Qed.
Lemma D_82078 : decode_any W_82078 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8207c : bv 32 := @BV 32 0x00000793%Z I.
Lemma F_8207c : fetch_word Asan.M.loaded_segments (@BV 64 0x82084%Z I : word) = Some W_8207c.
Proof. vm_refl. Qed.
Lemma D_8207c : decode_any W_8207c = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82080 : bv 32 := @BV 32 0xeb0fe0ef%Z I.
Lemma F_82080 : fetch_word Asan.M.loaded_segments (@BV 64 0x82088%Z I : word) = Some W_82080.
Proof. vm_refl. Qed.
Lemma D_82080 : decode_any W_82080 = Some (Jal (@BV 5 1%Z I) (@BV 21 2090672%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82084 : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_82084 : fetch_word Asan.M.loaded_segments (@BV 64 0x8208c%Z I : word) = Some W_82084.
Proof. vm_refl. Qed.
Lemma D_82084 : decode_any W_82084 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82088 : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_82088 : fetch_word Asan.M.loaded_segments (@BV 64 0x82090%Z I : word) = Some W_82088.
Proof. vm_refl. Qed.
Lemma D_82088 : decode_any W_82088 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8208c : bv 32 := @BV 32 0xe84fe0ef%Z I.
Lemma F_8208c : fetch_word Asan.M.loaded_segments (@BV 64 0x82094%Z I : word) = Some W_8208c.
Proof. vm_refl. Qed.
Lemma D_8208c : decode_any W_8208c = Some (Jal (@BV 5 1%Z I) (@BV 21 2090628%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82090 : bv 32 := @BV 32 0xaaaab537%Z I.
Lemma F_82090 : fetch_word Asan.M.loaded_segments (@BV 64 0x82098%Z I : word) = Some W_82090.
Proof. vm_refl. Qed.
Lemma D_82090 : decode_any W_82090 = Some (Lui (@BV 5 10%Z I) (@BV 20 699051%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82094 : bv 32 := @BV 32 0xaaa50513%Z I.
Lemma F_82094 : fetch_word Asan.M.loaded_segments (@BV 64 0x8209c%Z I : word) = Some W_82094.
Proof. vm_refl. Qed.
Lemma D_82094 : decode_any W_82094 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2730%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82098 : bv 32 := @BV 32 0x00a12423%Z I.
Lemma F_82098 : fetch_word Asan.M.loaded_segments (@BV 64 0x820a0%Z I : word) = Some W_82098.
Proof. vm_refl. Qed.
Lemma D_82098 : decode_any W_82098 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8209c : bv 32 := @BV 32 0x00810593%Z I.
Lemma F_8209c : fetch_word Asan.M.loaded_segments (@BV 64 0x820a4%Z I : word) = Some W_8209c.
Proof. vm_refl. Qed.
Lemma D_8209c : decode_any W_8209c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820a0 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_820a0 : fetch_word Asan.M.loaded_segments (@BV 64 0x820a8%Z I : word) = Some W_820a0.
Proof. vm_refl. Qed.
Lemma D_820a0 : decode_any W_820a0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820a4 : bv 32 := @BV 32 0xe6cfe0ef%Z I.
Lemma F_820a4 : fetch_word Asan.M.loaded_segments (@BV 64 0x820ac%Z I : word) = Some W_820a4.
Proof. vm_refl. Qed.
Lemma D_820a4 : decode_any W_820a4 = Some (Jal (@BV 5 1%Z I) (@BV 21 2090604%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820a8 : bv 32 := @BV 32 0x02051c63%Z I.
Lemma F_820a8 : fetch_word Asan.M.loaded_segments (@BV 64 0x820b0%Z I : word) = Some W_820a8.
Proof. vm_refl. Qed.
Lemma D_820a8 : decode_any W_820a8 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820ac : bv 32 := @BV 32 0x00048513%Z I.
Lemma F_820ac : fetch_word Asan.M.loaded_segments (@BV 64 0x820b4%Z I : word) = Some W_820ac.
Proof. vm_refl. Qed.
Lemma D_820ac : decode_any W_820ac = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820b0 : bv 32 := @BV 32 0xd64fa0ef%Z I.
Lemma F_820b0 : fetch_word Asan.M.loaded_segments (@BV 64 0x820b8%Z I : word) = Some W_820b0.
Proof. vm_refl. Qed.
Lemma D_820b0 : decode_any W_820b0 = Some (Jal (@BV 5 1%Z I) (@BV 21 2073956%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820b4 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_820b4 : fetch_word Asan.M.loaded_segments (@BV 64 0x820bc%Z I : word) = Some W_820b4.
Proof. vm_refl. Qed.
Lemma D_820b4 : decode_any W_820b4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820b8 : bv 32 := @BV 32 0x02813083%Z I.
Lemma F_820b8 : fetch_word Asan.M.loaded_segments (@BV 64 0x820c0%Z I : word) = Some W_820b8.
Proof. vm_refl. Qed.
Lemma D_820b8 : decode_any W_820b8 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820bc : bv 32 := @BV 32 0x02013403%Z I.
Lemma F_820bc : fetch_word Asan.M.loaded_segments (@BV 64 0x820c4%Z I : word) = Some W_820bc.
Proof. vm_refl. Qed.
Lemma D_820bc : decode_any W_820bc = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820c0 : bv 32 := @BV 32 0x01813483%Z I.
Lemma F_820c0 : fetch_word Asan.M.loaded_segments (@BV 64 0x820c8%Z I : word) = Some W_820c0.
Proof. vm_refl. Qed.
Lemma D_820c0 : decode_any W_820c0 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820c4 : bv 32 := @BV 32 0x01013903%Z I.
Lemma F_820c4 : fetch_word Asan.M.loaded_segments (@BV 64 0x820cc%Z I : word) = Some W_820c4.
Proof. vm_refl. Qed.
Lemma D_820c4 : decode_any W_820c4 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820c8 : bv 32 := @BV 32 0x03010113%Z I.
Lemma F_820c8 : fetch_word Asan.M.loaded_segments (@BV 64 0x820d0%Z I : word) = Some W_820c8.
Proof. vm_refl. Qed.
Lemma D_820c8 : decode_any W_820c8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820cc : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_820cc : fetch_word Asan.M.loaded_segments (@BV 64 0x820d4%Z I : word) = Some W_820cc.
Proof. vm_refl. Qed.
Lemma D_820cc : decode_any W_820cc = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820e0 : bv 32 := @BV 32 0x00812683%Z I.
Lemma F_820e0 : fetch_word Asan.M.loaded_segments (@BV 64 0x820e8%Z I : word) = Some W_820e0.
Proof. vm_refl. Qed.
Lemma D_820e0 : decode_any W_820e0 = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820e4 : bv 32 := @BV 32 0x00c00513%Z I.
Lemma F_820e4 : fetch_word Asan.M.loaded_segments (@BV 64 0x820ec%Z I : word) = Some W_820e4.
Proof. vm_refl. Qed.
Lemma D_820e4 : decode_any W_820e4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820e8 : bv 32 := @BV 32 0x00a69663%Z I.
Lemma F_820e8 : fetch_word Asan.M.loaded_segments (@BV 64 0x820f0%Z I : word) = Some W_820e8.
Proof. vm_refl. Qed.
Lemma D_820e8 : decode_any W_820e8 = Some (Branch BC_NE (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820ec : bv 32 := @BV 32 0x00000913%Z I.
Lemma F_820ec : fetch_word Asan.M.loaded_segments (@BV 64 0x820f4%Z I : word) = Some W_820ec.
Proof. vm_refl. Qed.
Lemma D_820ec : decode_any W_820ec = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820f0 : bv 32 := @BV 32 0xfc5ff06f%Z I.
Lemma F_820f0 : fetch_word Asan.M.loaded_segments (@BV 64 0x820f8%Z I : word) = Some W_820f0.
Proof. vm_refl. Qed.
Lemma D_820f0 : decode_any W_820f0 = Some (Jal (@BV 5 0%Z I) (@BV 21 2097092%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82338 : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_82338 : fetch_word Asan.M.loaded_segments (@BV 64 0x82340%Z I : word) = Some W_82338.
Proof. vm_refl. Qed.
Lemma D_82338 : decode_any W_82338 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8233c : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_8233c : fetch_word Asan.M.loaded_segments (@BV 64 0x82344%Z I : word) = Some W_8233c.
Proof. vm_refl. Qed.
Lemma D_8233c : decode_any W_8233c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82340 : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_82340 : fetch_word Asan.M.loaded_segments (@BV 64 0x82348%Z I : word) = Some W_82340.
Proof. vm_refl. Qed.
Lemma D_82340 : decode_any W_82340 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82344 : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_82344 : fetch_word Asan.M.loaded_segments (@BV 64 0x8234c%Z I : word) = Some W_82344.
Proof. vm_refl. Qed.
Lemma D_82344 : decode_any W_82344 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82348 : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_82348 : fetch_word Asan.M.loaded_segments (@BV 64 0x82350%Z I : word) = Some W_82348.
Proof. vm_refl. Qed.
Lemma D_82348 : decode_any W_82348 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8234c : bv 32 := @BV 32 0x00058413%Z I.
Lemma F_8234c : fetch_word Asan.M.loaded_segments (@BV 64 0x82354%Z I : word) = Some W_8234c.
Proof. vm_refl. Qed.
Lemma D_8234c : decode_any W_8234c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82350 : bv 32 := @BV 32 0x0007d597%Z I.
Lemma F_82350 : fetch_word Asan.M.loaded_segments (@BV 64 0x82358%Z I : word) = Some W_82350.
Proof. vm_refl. Qed.
Lemma D_82350 : decode_any W_82350 = Some (Auipc (@BV 5 11%Z I) (@BV 20 125%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82354 : bv 32 := @BV 32 0xef85b903%Z I.
Lemma F_82354 : fetch_word Asan.M.loaded_segments (@BV 64 0x8235c%Z I : word) = Some W_82354.
Proof. vm_refl. Qed.
Lemma D_82354 : decode_any W_82354 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 11%Z I) (@BV 12 3832%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82358 : bv 32 := @BV 32 0x00093583%Z I.
Lemma F_82358 : fetch_word Asan.M.loaded_segments (@BV 64 0x82360%Z I : word) = Some W_82358.
Proof. vm_refl. Qed.
Lemma D_82358 : decode_any W_82358 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8235c : bv 32 := @BV 32 0x00050493%Z I.
Lemma F_8235c : fetch_word Asan.M.loaded_segments (@BV 64 0x82364%Z I : word) = Some W_8235c.
Proof. vm_refl. Qed.
Lemma D_8235c : decode_any W_8235c = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82360 : bv 32 := @BV 32 0x00059863%Z I.
Lemma F_82360 : fetch_word Asan.M.loaded_segments (@BV 64 0x82368%Z I : word) = Some W_82360.
Proof. vm_refl. Qed.
Lemma D_82360 : decode_any W_82360 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82370 : bv 32 := @BV 32 0xfff58513%Z I.
Lemma F_82370 : fetch_word Asan.M.loaded_segments (@BV 64 0x82378%Z I : word) = Some W_82370.
Proof. vm_refl. Qed.
Lemma D_82370 : decode_any W_82370 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82374 : bv 32 := @BV 32 0x00a5f533%Z I.
Lemma F_82374 : fetch_word Asan.M.loaded_segments (@BV 64 0x8237c%Z I : word) = Some W_82374.
Proof. vm_refl. Qed.
Lemma D_82374 : decode_any W_82374 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82378 : bv 32 := @BV 32 0x08051c63%Z I.
Lemma F_82378 : fetch_word Asan.M.loaded_segments (@BV 64 0x82380%Z I : word) = Some W_82378.
Proof. vm_refl. Qed.
Lemma D_82378 : decode_any W_82378 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8237c : bv 32 := @BV 32 0x00b484b3%Z I.
Lemma F_8237c : fetch_word Asan.M.loaded_segments (@BV 64 0x82384%Z I : word) = Some W_8237c.
Proof. vm_refl. Qed.
Lemma D_8237c : decode_any W_8237c = Some (Op ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82380 : bv 32 := @BV 32 0x40b00533%Z I.
Lemma F_82380 : fetch_word Asan.M.loaded_segments (@BV 64 0x82388%Z I : word) = Some W_82380.
Proof. vm_refl. Qed.
Lemma D_82380 : decode_any W_82380 = Some (Op ALU_SUB (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82384 : bv 32 := @BV 32 0xfff48493%Z I.
Lemma F_82384 : fetch_word Asan.M.loaded_segments (@BV 64 0x8238c%Z I : word) = Some W_82384.
Proof. vm_refl. Qed.
Lemma D_82384 : decode_any W_82384 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82388 : bv 32 := @BV 32 0x00a4f4b3%Z I.
Lemma F_82388 : fetch_word Asan.M.loaded_segments (@BV 64 0x82390%Z I : word) = Some W_82388.
Proof. vm_refl. Qed.
Lemma D_82388 : decode_any W_82388 = Some (Op ALU_AND (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8238c : bv 32 := @BV 32 0x00004537%Z I.
Lemma F_8238c : fetch_word Asan.M.loaded_segments (@BV 64 0x82394%Z I : word) = Some W_8238c.
Proof. vm_refl. Qed.
Lemma D_8238c : decode_any W_8238c = Some (Lui (@BV 5 10%Z I) (@BV 20 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82390 : bv 32 := @BV 32 0x02250513%Z I.
Lemma F_82390 : fetch_word Asan.M.loaded_segments (@BV 64 0x82398%Z I : word) = Some W_82390.
Proof. vm_refl. Qed.
Lemma D_82390 : decode_any W_82390 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 34%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82394 : bv 32 := @BV 32 0x00a12623%Z I.
Lemma F_82394 : fetch_word Asan.M.loaded_segments (@BV 64 0x8239c%Z I : word) = Some W_82394.
Proof. vm_refl. Qed.
Lemma D_82394 : decode_any W_82394 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82398 : bv 32 := @BV 32 0x00c10613%Z I.
Lemma F_82398 : fetch_word Asan.M.loaded_segments (@BV 64 0x823a0%Z I : word) = Some W_82398.
Proof. vm_refl. Qed.
Lemma D_82398 : decode_any W_82398 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8239c : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_8239c : fetch_word Asan.M.loaded_segments (@BV 64 0x823a4%Z I : word) = Some W_8239c.
Proof. vm_refl. Qed.
Lemma D_8239c : decode_any W_8239c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823a0 : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_823a0 : fetch_word Asan.M.loaded_segments (@BV 64 0x823a8%Z I : word) = Some W_823a0.
Proof. vm_refl. Qed.
Lemma D_823a0 : decode_any W_823a0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823a4 : bv 32 := @BV 32 0x738000ef%Z I.
Lemma F_823a4 : fetch_word Asan.M.loaded_segments (@BV 64 0x823ac%Z I : word) = Some W_823a4.
Proof. vm_refl. Qed.
Lemma D_823a4 : decode_any W_823a4 = Some (Jal (@BV 5 1%Z I) (@BV 21 1848%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823a8 : bv 32 := @BV 32 0x00c12683%Z I.
Lemma F_823a8 : fetch_word Asan.M.loaded_segments (@BV 64 0x823b0%Z I : word) = Some W_823a8.
Proof. vm_refl. Qed.
Lemma D_823a8 : decode_any W_823a8 = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823ac : bv 32 := @BV 32 0x00050713%Z I.
Lemma F_823ac : fetch_word Asan.M.loaded_segments (@BV 64 0x823b4%Z I : word) = Some W_823ac.
Proof. vm_refl. Qed.
Lemma D_823ac : decode_any W_823ac = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823b0 : bv 32 := @BV 32 0x00300613%Z I.
Lemma F_823b0 : fetch_word Asan.M.loaded_segments (@BV 64 0x823b8%Z I : word) = Some W_823b0.
Proof. vm_refl. Qed.
Lemma D_823b0 : decode_any W_823b0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823b4 : bv 32 := @BV 32 0x00000513%Z I.
Lemma F_823b4 : fetch_word Asan.M.loaded_segments (@BV 64 0x823bc%Z I : word) = Some W_823b4.
Proof. vm_refl. Qed.
Lemma D_823b4 : decode_any W_823b4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823b8 : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_823b8 : fetch_word Asan.M.loaded_segments (@BV 64 0x823c0%Z I : word) = Some W_823b8.
Proof. vm_refl. Qed.
Lemma D_823b8 : decode_any W_823b8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823bc : bv 32 := @BV 32 0x00000793%Z I.
Lemma F_823bc : fetch_word Asan.M.loaded_segments (@BV 64 0x823c4%Z I : word) = Some W_823bc.
Proof. vm_refl. Qed.
Lemma D_823bc : decode_any W_823bc = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823c0 : bv 32 := @BV 32 0xb70fe0ef%Z I.
Lemma F_823c0 : fetch_word Asan.M.loaded_segments (@BV 64 0x823c8%Z I : word) = Some W_823c0.
Proof. vm_refl. Qed.
Lemma D_823c0 : decode_any W_823c0 = Some (Jal (@BV 5 1%Z I) (@BV 21 2089840%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823c4 : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_823c4 : fetch_word Asan.M.loaded_segments (@BV 64 0x823cc%Z I : word) = Some W_823c4.
Proof. vm_refl. Qed.
Lemma D_823c4 : decode_any W_823c4 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823c8 : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_823c8 : fetch_word Asan.M.loaded_segments (@BV 64 0x823d0%Z I : word) = Some W_823c8.
Proof. vm_refl. Qed.
Lemma D_823c8 : decode_any W_823c8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823cc : bv 32 := @BV 32 0xb44fe0ef%Z I.
Lemma F_823cc : fetch_word Asan.M.loaded_segments (@BV 64 0x823d4%Z I : word) = Some W_823cc.
Proof. vm_refl. Qed.
Lemma D_823cc : decode_any W_823cc = Some (Jal (@BV 5 1%Z I) (@BV 21 2089796%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823d0 : bv 32 := @BV 32 0xaaaab537%Z I.
Lemma F_823d0 : fetch_word Asan.M.loaded_segments (@BV 64 0x823d8%Z I : word) = Some W_823d0.
Proof. vm_refl. Qed.
Lemma D_823d0 : decode_any W_823d0 = Some (Lui (@BV 5 10%Z I) (@BV 20 699051%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823d4 : bv 32 := @BV 32 0xaaa50513%Z I.
Lemma F_823d4 : fetch_word Asan.M.loaded_segments (@BV 64 0x823dc%Z I : word) = Some W_823d4.
Proof. vm_refl. Qed.
Lemma D_823d4 : decode_any W_823d4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2730%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823d8 : bv 32 := @BV 32 0x00a12423%Z I.
Lemma F_823d8 : fetch_word Asan.M.loaded_segments (@BV 64 0x823e0%Z I : word) = Some W_823d8.
Proof. vm_refl. Qed.
Lemma D_823d8 : decode_any W_823d8 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823dc : bv 32 := @BV 32 0x00810593%Z I.
Lemma F_823dc : fetch_word Asan.M.loaded_segments (@BV 64 0x823e4%Z I : word) = Some W_823dc.
Proof. vm_refl. Qed.
Lemma D_823dc : decode_any W_823dc = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823e0 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_823e0 : fetch_word Asan.M.loaded_segments (@BV 64 0x823e8%Z I : word) = Some W_823e0.
Proof. vm_refl. Qed.
Lemma D_823e0 : decode_any W_823e0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823e4 : bv 32 := @BV 32 0xb2cfe0ef%Z I.
Lemma F_823e4 : fetch_word Asan.M.loaded_segments (@BV 64 0x823ec%Z I : word) = Some W_823e4.
Proof. vm_refl. Qed.
Lemma D_823e4 : decode_any W_823e4 = Some (Jal (@BV 5 1%Z I) (@BV 21 2089772%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823e8 : bv 32 := @BV 32 0x02051c63%Z I.
Lemma F_823e8 : fetch_word Asan.M.loaded_segments (@BV 64 0x823f0%Z I : word) = Some W_823e8.
Proof. vm_refl. Qed.
Lemma D_823e8 : decode_any W_823e8 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823ec : bv 32 := @BV 32 0x00048513%Z I.
Lemma F_823ec : fetch_word Asan.M.loaded_segments (@BV 64 0x823f4%Z I : word) = Some W_823ec.
Proof. vm_refl. Qed.
Lemma D_823ec : decode_any W_823ec = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823f0 : bv 32 := @BV 32 0xa24fa0ef%Z I.
Lemma F_823f0 : fetch_word Asan.M.loaded_segments (@BV 64 0x823f8%Z I : word) = Some W_823f0.
Proof. vm_refl. Qed.
Lemma D_823f0 : decode_any W_823f0 = Some (Jal (@BV 5 1%Z I) (@BV 21 2073124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823f4 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_823f4 : fetch_word Asan.M.loaded_segments (@BV 64 0x823fc%Z I : word) = Some W_823f4.
Proof. vm_refl. Qed.
Lemma D_823f4 : decode_any W_823f4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823f8 : bv 32 := @BV 32 0x02813083%Z I.
Lemma F_823f8 : fetch_word Asan.M.loaded_segments (@BV 64 0x82400%Z I : word) = Some W_823f8.
Proof. vm_refl. Qed.
Lemma D_823f8 : decode_any W_823f8 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823fc : bv 32 := @BV 32 0x02013403%Z I.
Lemma F_823fc : fetch_word Asan.M.loaded_segments (@BV 64 0x82404%Z I : word) = Some W_823fc.
Proof. vm_refl. Qed.
Lemma D_823fc : decode_any W_823fc = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82400 : bv 32 := @BV 32 0x01813483%Z I.
Lemma F_82400 : fetch_word Asan.M.loaded_segments (@BV 64 0x82408%Z I : word) = Some W_82400.
Proof. vm_refl. Qed.
Lemma D_82400 : decode_any W_82400 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82404 : bv 32 := @BV 32 0x01013903%Z I.
Lemma F_82404 : fetch_word Asan.M.loaded_segments (@BV 64 0x8240c%Z I : word) = Some W_82404.
Proof. vm_refl. Qed.
Lemma D_82404 : decode_any W_82404 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82408 : bv 32 := @BV 32 0x03010113%Z I.
Lemma F_82408 : fetch_word Asan.M.loaded_segments (@BV 64 0x82410%Z I : word) = Some W_82408.
Proof. vm_refl. Qed.
Lemma D_82408 : decode_any W_82408 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8240c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8240c : fetch_word Asan.M.loaded_segments (@BV 64 0x82414%Z I : word) = Some W_8240c.
Proof. vm_refl. Qed.
Lemma D_8240c : decode_any W_8240c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82420 : bv 32 := @BV 32 0x00812683%Z I.
Lemma F_82420 : fetch_word Asan.M.loaded_segments (@BV 64 0x82428%Z I : word) = Some W_82420.
Proof. vm_refl. Qed.
Lemma D_82420 : decode_any W_82420 = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82424 : bv 32 := @BV 32 0xfff9c517%Z I.
Lemma F_82424 : fetch_word Asan.M.loaded_segments (@BV 64 0x8242c%Z I : word) = Some W_82424.
Proof. vm_refl. Qed.
Lemma D_82424 : decode_any W_82424 = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048476%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82428 : bv 32 := @BV 32 0xdfd50613%Z I.
Lemma F_82428 : fetch_word Asan.M.loaded_segments (@BV 64 0x82430%Z I : word) = Some W_82428.
Proof. vm_refl. Qed.
Lemma D_82428 : decode_any W_82428 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 3581%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8242c : bv 32 := @BV 32 0x00048513%Z I.
Lemma F_8242c : fetch_word Asan.M.loaded_segments (@BV 64 0x82434%Z I : word) = Some W_8242c.
Proof. vm_refl. Qed.
Lemma D_8242c : decode_any W_8242c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82430 : bv 32 := @BV 32 0x00040593%Z I.
Lemma F_82430 : fetch_word Asan.M.loaded_segments (@BV 64 0x82438%Z I : word) = Some W_82430.
Proof. vm_refl. Qed.
Lemma D_82430 : decode_any W_82430 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82434 : bv 32 := @BV 32 0x00000713%Z I.
Lemma F_82434 : fetch_word Asan.M.loaded_segments (@BV 64 0x8243c%Z I : word) = Some W_82434.
Proof. vm_refl. Qed.
Lemma D_82434 : decode_any W_82434 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82438 : bv 32 := @BV 32 0xb45f90ef%Z I.
Lemma F_82438 : fetch_word Asan.M.loaded_segments (@BV 64 0x82440%Z I : word) = Some W_82438.
Proof. vm_refl. Qed.
Lemma D_82438 : decode_any W_82438 = Some (Jal (@BV 5 1%Z I) (@BV 21 2071364%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8243c : bv 32 := @BV 32 0x00060693%Z I.
Lemma F_8243c : fetch_word Asan.M.loaded_segments (@BV 64 0x82444%Z I : word) = Some W_8243c.
Proof. vm_refl. Qed.
Lemma D_8243c : decode_any W_8243c = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82440 : bv 32 := @BV 32 0x00000613%Z I.
Lemma F_82440 : fetch_word Asan.M.loaded_segments (@BV 64 0x82448%Z I : word) = Some W_82440.
Proof. vm_refl. Qed.
Lemma D_82440 : decode_any W_82440 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82444 : bv 32 := @BV 32 0x0040006f%Z I.
Lemma F_82444 : fetch_word Asan.M.loaded_segments (@BV 64 0x8244c%Z I : word) = Some W_82444.
Proof. vm_refl. Qed.
Lemma D_82444 : decode_any W_82444 = Some (Jal (@BV 5 0%Z I) (@BV 21 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82448 : bv 32 := @BV 32 0xfa010113%Z I.
Lemma F_82448 : fetch_word Asan.M.loaded_segments (@BV 64 0x82450%Z I : word) = Some W_82448.
Proof. vm_refl. Qed.
Lemma D_82448 : decode_any W_82448 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4000%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8244c : bv 32 := @BV 32 0x04113c23%Z I.
Lemma F_8244c : fetch_word Asan.M.loaded_segments (@BV 64 0x82454%Z I : word) = Some W_8244c.
Proof. vm_refl. Qed.
Lemma D_8244c : decode_any W_8244c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82450 : bv 32 := @BV 32 0x04813823%Z I.
Lemma F_82450 : fetch_word Asan.M.loaded_segments (@BV 64 0x82458%Z I : word) = Some W_82450.
Proof. vm_refl. Qed.
Lemma D_82450 : decode_any W_82450 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82454 : bv 32 := @BV 32 0x04913423%Z I.
Lemma F_82454 : fetch_word Asan.M.loaded_segments (@BV 64 0x8245c%Z I : word) = Some W_82454.
Proof. vm_refl. Qed.
Lemma D_82454 : decode_any W_82454 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82458 : bv 32 := @BV 32 0x05213023%Z I.
Lemma F_82458 : fetch_word Asan.M.loaded_segments (@BV 64 0x82460%Z I : word) = Some W_82458.
Proof. vm_refl. Qed.
Lemma D_82458 : decode_any W_82458 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8245c : bv 32 := @BV 32 0x03313c23%Z I.
Lemma F_8245c : fetch_word Asan.M.loaded_segments (@BV 64 0x82464%Z I : word) = Some W_8245c.
Proof. vm_refl. Qed.
Lemma D_8245c : decode_any W_8245c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82460 : bv 32 := @BV 32 0x03413823%Z I.
Lemma F_82460 : fetch_word Asan.M.loaded_segments (@BV 64 0x82468%Z I : word) = Some W_82460.
Proof. vm_refl. Qed.
Lemma D_82460 : decode_any W_82460 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82464 : bv 32 := @BV 32 0x00068993%Z I.
Lemma F_82464 : fetch_word Asan.M.loaded_segments (@BV 64 0x8246c%Z I : word) = Some W_82464.
Proof. vm_refl. Qed.
Lemma D_82464 : decode_any W_82464 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82468 : bv 32 := @BV 32 0x00060493%Z I.
Lemma F_82468 : fetch_word Asan.M.loaded_segments (@BV 64 0x82470%Z I : word) = Some W_82468.
Proof. vm_refl. Qed.
Lemma D_82468 : decode_any W_82468 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8246c : bv 32 := @BV 32 0x00058413%Z I.
Lemma F_8246c : fetch_word Asan.M.loaded_segments (@BV 64 0x82474%Z I : word) = Some W_8246c.
Proof. vm_refl. Qed.
Lemma D_8246c : decode_any W_8246c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82470 : bv 32 := @BV 32 0x0007d597%Z I.
Lemma F_82470 : fetch_word Asan.M.loaded_segments (@BV 64 0x82478%Z I : word) = Some W_82470.
Proof. vm_refl. Qed.
Lemma D_82470 : decode_any W_82470 = Some (Auipc (@BV 5 11%Z I) (@BV 20 125%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82474 : bv 32 := @BV 32 0xdd85ba03%Z I.
Lemma F_82474 : fetch_word Asan.M.loaded_segments (@BV 64 0x8247c%Z I : word) = Some W_82474.
Proof. vm_refl. Qed.
Lemma D_82474 : decode_any W_82474 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 11%Z I) (@BV 12 3544%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82478 : bv 32 := @BV 32 0x000a3583%Z I.
Lemma F_82478 : fetch_word Asan.M.loaded_segments (@BV 64 0x82480%Z I : word) = Some W_82478.
Proof. vm_refl. Qed.
Lemma D_82478 : decode_any W_82478 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 20%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8247c : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_8247c : fetch_word Asan.M.loaded_segments (@BV 64 0x82484%Z I : word) = Some W_8247c.
Proof. vm_refl. Qed.
Lemma D_8247c : decode_any W_8247c = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82480 : bv 32 := @BV 32 0x00059863%Z I.
Lemma F_82480 : fetch_word Asan.M.loaded_segments (@BV 64 0x82488%Z I : word) = Some W_82480.
Proof. vm_refl. Qed.
Lemma D_82480 : decode_any W_82480 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82490 : bv 32 := @BV 32 0xfff58513%Z I.
Lemma F_82490 : fetch_word Asan.M.loaded_segments (@BV 64 0x82498%Z I : word) = Some W_82490.
Proof. vm_refl. Qed.
Lemma D_82490 : decode_any W_82490 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82494 : bv 32 := @BV 32 0x00a5f533%Z I.
Lemma F_82494 : fetch_word Asan.M.loaded_segments (@BV 64 0x8249c%Z I : word) = Some W_82494.
Proof. vm_refl. Qed.
Lemma D_82494 : decode_any W_82494 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82498 : bv 32 := @BV 32 0x0a051863%Z I.
Lemma F_82498 : fetch_word Asan.M.loaded_segments (@BV 64 0x824a0%Z I : word) = Some W_82498.
Proof. vm_refl. Qed.
Lemma D_82498 : decode_any W_82498 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 176%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8249c : bv 32 := @BV 32 0x00b40433%Z I.
Lemma F_8249c : fetch_word Asan.M.loaded_segments (@BV 64 0x824a4%Z I : word) = Some W_8249c.
Proof. vm_refl. Qed.
Lemma D_8249c : decode_any W_8249c = Some (Op ALU_ADD (@BV 5 8%Z I) (@BV 5 8%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824a0 : bv 32 := @BV 32 0xfff40413%Z I.
Lemma F_824a0 : fetch_word Asan.M.loaded_segments (@BV 64 0x824a8%Z I : word) = Some W_824a0.
Proof. vm_refl. Qed.
Lemma D_824a0 : decode_any W_824a0 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 8%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824a4 : bv 32 := @BV 32 0x40b00533%Z I.
Lemma F_824a4 : fetch_word Asan.M.loaded_segments (@BV 64 0x824ac%Z I : word) = Some W_824a4.
Proof. vm_refl. Qed.
Lemma D_824a4 : decode_any W_824a4 = Some (Op ALU_SUB (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824a8 : bv 32 := @BV 32 0x00a47433%Z I.
Lemma F_824a8 : fetch_word Asan.M.loaded_segments (@BV 64 0x824b0%Z I : word) = Some W_824a8.
Proof. vm_refl. Qed.
Lemma D_824a8 : decode_any W_824a8 = Some (Op ALU_AND (@BV 5 8%Z I) (@BV 5 8%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824ac : bv 32 := @BV 32 0x00059863%Z I.
Lemma F_824ac : fetch_word Asan.M.loaded_segments (@BV 64 0x824b4%Z I : word) = Some W_824ac.
Proof. vm_refl. Qed.
Lemma D_824ac : decode_any W_824ac = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824bc : bv 32 := @BV 32 0x00a97933%Z I.
Lemma F_824bc : fetch_word Asan.M.loaded_segments (@BV 64 0x824c4%Z I : word) = Some W_824bc.
Proof. vm_refl. Qed.
Lemma D_824bc : decode_any W_824bc = Some (Op ALU_AND (@BV 5 18%Z I) (@BV 5 18%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824c0 : bv 32 := @BV 32 0x03200513%Z I.
Lemma F_824c0 : fetch_word Asan.M.loaded_segments (@BV 64 0x824c8%Z I : word) = Some W_824c0.
Proof. vm_refl. Qed.
Lemma D_824c0 : decode_any W_824c0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 50%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824c4 : bv 32 := @BV 32 0x00a12023%Z I.
Lemma F_824c4 : fetch_word Asan.M.loaded_segments (@BV 64 0x824cc%Z I : word) = Some W_824c4.
Proof. vm_refl. Qed.
Lemma D_824c4 : decode_any W_824c4 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824c8 : bv 32 := @BV 32 0x00010613%Z I.
Lemma F_824c8 : fetch_word Asan.M.loaded_segments (@BV 64 0x824d0%Z I : word) = Some W_824c8.
Proof. vm_refl. Qed.
Lemma D_824c8 : decode_any W_824c8 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824cc : bv 32 := @BV 32 0x00098513%Z I.
Lemma F_824cc : fetch_word Asan.M.loaded_segments (@BV 64 0x824d4%Z I : word) = Some W_824cc.
Proof. vm_refl. Qed.
Lemma D_824cc : decode_any W_824cc = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824d0 : bv 32 := @BV 32 0x00040593%Z I.
Lemma F_824d0 : fetch_word Asan.M.loaded_segments (@BV 64 0x824d8%Z I : word) = Some W_824d0.
Proof. vm_refl. Qed.
Lemma D_824d0 : decode_any W_824d0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824d4 : bv 32 := @BV 32 0x608000ef%Z I.
Lemma F_824d4 : fetch_word Asan.M.loaded_segments (@BV 64 0x824dc%Z I : word) = Some W_824d4.
Proof. vm_refl. Qed.
Lemma D_824d4 : decode_any W_824d4 = Some (Jal (@BV 5 1%Z I) (@BV 21 1544%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824d8 : bv 32 := @BV 32 0x00012683%Z I.
Lemma F_824d8 : fetch_word Asan.M.loaded_segments (@BV 64 0x824e0%Z I : word) = Some W_824d8.
Proof. vm_refl. Qed.
Lemma D_824d8 : decode_any W_824d8 = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824dc : bv 32 := @BV 32 0x00050713%Z I.
Lemma F_824dc : fetch_word Asan.M.loaded_segments (@BV 64 0x824e4%Z I : word) = Some W_824dc.
Proof. vm_refl. Qed.
Lemma D_824dc : decode_any W_824dc = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824e0 : bv 32 := @BV 32 0x00300613%Z I.
Lemma F_824e0 : fetch_word Asan.M.loaded_segments (@BV 64 0x824e8%Z I : word) = Some W_824e0.
Proof. vm_refl. Qed.
Lemma D_824e0 : decode_any W_824e0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824e4 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_824e4 : fetch_word Asan.M.loaded_segments (@BV 64 0x824ec%Z I : word) = Some W_824e4.
Proof. vm_refl. Qed.
Lemma D_824e4 : decode_any W_824e4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824e8 : bv 32 := @BV 32 0x00040593%Z I.
Lemma F_824e8 : fetch_word Asan.M.loaded_segments (@BV 64 0x824f0%Z I : word) = Some W_824e8.
Proof. vm_refl. Qed.
Lemma D_824e8 : decode_any W_824e8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824ec : bv 32 := @BV 32 0x00000793%Z I.
Lemma F_824ec : fetch_word Asan.M.loaded_segments (@BV 64 0x824f4%Z I : word) = Some W_824ec.
Proof. vm_refl. Qed.
Lemma D_824ec : decode_any W_824ec = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824f0 : bv 32 := @BV 32 0xa40fe0ef%Z I.
Lemma F_824f0 : fetch_word Asan.M.loaded_segments (@BV 64 0x824f8%Z I : word) = Some W_824f0.
Proof. vm_refl. Qed.
Lemma D_824f0 : decode_any W_824f0 = Some (Jal (@BV 5 1%Z I) (@BV 21 2089536%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824f4 : bv 32 := @BV 32 0x00050993%Z I.
Lemma F_824f4 : fetch_word Asan.M.loaded_segments (@BV 64 0x824fc%Z I : word) = Some W_824f4.
Proof. vm_refl. Qed.
Lemma D_824f4 : decode_any W_824f4 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824f8 : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_824f8 : fetch_word Asan.M.loaded_segments (@BV 64 0x82500%Z I : word) = Some W_824f8.
Proof. vm_refl. Qed.
Lemma D_824f8 : decode_any W_824f8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824fc : bv 32 := @BV 32 0xa14fe0ef%Z I.
Lemma F_824fc : fetch_word Asan.M.loaded_segments (@BV 64 0x82504%Z I : word) = Some W_824fc.
Proof. vm_refl. Qed.
Lemma D_824fc : decode_any W_824fc = Some (Jal (@BV 5 1%Z I) (@BV 21 2089492%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82500 : bv 32 := @BV 32 0xaaaab537%Z I.
Lemma F_82500 : fetch_word Asan.M.loaded_segments (@BV 64 0x82508%Z I : word) = Some W_82500.
Proof. vm_refl. Qed.
Lemma D_82500 : decode_any W_82500 = Some (Lui (@BV 5 10%Z I) (@BV 20 699051%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82504 : bv 32 := @BV 32 0xaaa50513%Z I.
Lemma F_82504 : fetch_word Asan.M.loaded_segments (@BV 64 0x8250c%Z I : word) = Some W_82504.
Proof. vm_refl. Qed.
Lemma D_82504 : decode_any W_82504 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2730%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82508 : bv 32 := @BV 32 0x02a12623%Z I.
Lemma F_82508 : fetch_word Asan.M.loaded_segments (@BV 64 0x82510%Z I : word) = Some W_82508.
Proof. vm_refl. Qed.
Lemma D_82508 : decode_any W_82508 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8250c : bv 32 := @BV 32 0x02c10593%Z I.
Lemma F_8250c : fetch_word Asan.M.loaded_segments (@BV 64 0x82514%Z I : word) = Some W_8250c.
Proof. vm_refl. Qed.
Lemma D_8250c : decode_any W_8250c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82510 : bv 32 := @BV 32 0x00098513%Z I.
Lemma F_82510 : fetch_word Asan.M.loaded_segments (@BV 64 0x82518%Z I : word) = Some W_82510.
Proof. vm_refl. Qed.
Lemma D_82510 : decode_any W_82510 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82514 : bv 32 := @BV 32 0x9fcfe0ef%Z I.
Lemma F_82514 : fetch_word Asan.M.loaded_segments (@BV 64 0x8251c%Z I : word) = Some W_82514.
Proof. vm_refl. Qed.
Lemma D_82514 : decode_any W_82514 = Some (Jal (@BV 5 1%Z I) (@BV 21 2089468%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82518 : bv 32 := @BV 32 0x04051063%Z I.
Lemma F_82518 : fetch_word Asan.M.loaded_segments (@BV 64 0x82520%Z I : word) = Some W_82518.
Proof. vm_refl. Qed.
Lemma D_82518 : decode_any W_82518 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8251c : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_8251c : fetch_word Asan.M.loaded_segments (@BV 64 0x82524%Z I : word) = Some W_8251c.
Proof. vm_refl. Qed.
Lemma D_8251c : decode_any W_8251c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82520 : bv 32 := @BV 32 0x8f4fa0ef%Z I.
Lemma F_82520 : fetch_word Asan.M.loaded_segments (@BV 64 0x82528%Z I : word) = Some W_82520.
Proof. vm_refl. Qed.
Lemma D_82520 : decode_any W_82520 = Some (Jal (@BV 5 1%Z I) (@BV 21 2072820%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82524 : bv 32 := @BV 32 0x00098513%Z I.
Lemma F_82524 : fetch_word Asan.M.loaded_segments (@BV 64 0x8252c%Z I : word) = Some W_82524.
Proof. vm_refl. Qed.
Lemma D_82524 : decode_any W_82524 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82528 : bv 32 := @BV 32 0x05813083%Z I.
Lemma F_82528 : fetch_word Asan.M.loaded_segments (@BV 64 0x82530%Z I : word) = Some W_82528.
Proof. vm_refl. Qed.
Lemma D_82528 : decode_any W_82528 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8252c : bv 32 := @BV 32 0x05013403%Z I.
Lemma F_8252c : fetch_word Asan.M.loaded_segments (@BV 64 0x82534%Z I : word) = Some W_8252c.
Proof. vm_refl. Qed.
Lemma D_8252c : decode_any W_8252c = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82530 : bv 32 := @BV 32 0x04813483%Z I.
Lemma F_82530 : fetch_word Asan.M.loaded_segments (@BV 64 0x82538%Z I : word) = Some W_82530.
Proof. vm_refl. Qed.
Lemma D_82530 : decode_any W_82530 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82534 : bv 32 := @BV 32 0x04013903%Z I.
Lemma F_82534 : fetch_word Asan.M.loaded_segments (@BV 64 0x8253c%Z I : word) = Some W_82534.
Proof. vm_refl. Qed.
Lemma D_82534 : decode_any W_82534 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82538 : bv 32 := @BV 32 0x03813983%Z I.
Lemma F_82538 : fetch_word Asan.M.loaded_segments (@BV 64 0x82540%Z I : word) = Some W_82538.
Proof. vm_refl. Qed.
Lemma D_82538 : decode_any W_82538 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8253c : bv 32 := @BV 32 0x03013a03%Z I.
Lemma F_8253c : fetch_word Asan.M.loaded_segments (@BV 64 0x82544%Z I : word) = Some W_8253c.
Proof. vm_refl. Qed.
Lemma D_8253c : decode_any W_8253c = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82540 : bv 32 := @BV 32 0x06010113%Z I.
Lemma F_82540 : fetch_word Asan.M.loaded_segments (@BV 64 0x82548%Z I : word) = Some W_82540.
Proof. vm_refl. Qed.
Lemma D_82540 : decode_any W_82540 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82544 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_82544 : fetch_word Asan.M.loaded_segments (@BV 64 0x8254c%Z I : word) = Some W_82544.
Proof. vm_refl. Qed.
Lemma D_82544 : decode_any W_82544 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82558 : bv 32 := @BV 32 0x00048c63%Z I.
Lemma F_82558 : fetch_word Asan.M.loaded_segments (@BV 64 0x82560%Z I : word) = Some W_82558.
Proof. vm_refl. Qed.
Lemma D_82558 : decode_any W_82558 = Some (Branch BC_EQ (@BV 5 9%Z I) (@BV 5 0%Z I) (@BV 13 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825c0 : bv 32 := @BV 32 0x00060693%Z I.
Lemma F_825c0 : fetch_word Asan.M.loaded_segments (@BV 64 0x825c8%Z I : word) = Some W_825c0.
Proof. vm_refl. Qed.
Lemma D_825c0 : decode_any W_825c0 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825c4 : bv 32 := @BV 32 0x00100613%Z I.
Lemma F_825c4 : fetch_word Asan.M.loaded_segments (@BV 64 0x825cc%Z I : word) = Some W_825c4.
Proof. vm_refl. Qed.
Lemma D_825c4 : decode_any W_825c4 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825c8 : bv 32 := @BV 32 0xe81ff06f%Z I.
Lemma F_825c8 : fetch_word Asan.M.loaded_segments (@BV 64 0x825d0%Z I : word) = Some W_825c8.
Proof. vm_refl. Qed.
Lemma D_825c8 : decode_any W_825c8 = Some (Jal (@BV 5 0%Z I) (@BV 21 2096768%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82878 : bv 32 := @BV 32 0xc3453503%Z I.
Lemma F_82878 : fetch_word Asan.M.loaded_segments (@BV 64 0x82880%Z I : word) = Some W_82878.
Proof. vm_refl. Qed.
Lemma D_82878 : decode_any W_82878 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 3124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8287c : bv 32 := @BV 32 0x06a13423%Z I.
Lemma F_8287c : fetch_word Asan.M.loaded_segments (@BV 64 0x82884%Z I : word) = Some W_8287c.
Proof. vm_refl. Qed.
Lemma D_8287c : decode_any W_8287c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82880 : bv 32 := @BV 32 0x06a13823%Z I.
Lemma F_82880 : fetch_word Asan.M.loaded_segments (@BV 64 0x82888%Z I : word) = Some W_82880.
Proof. vm_refl. Qed.
Lemma D_82880 : decode_any W_82880 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 112%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82884 : bv 32 := @BV 32 0x06a13c23%Z I.
Lemma F_82884 : fetch_word Asan.M.loaded_segments (@BV 64 0x8288c%Z I : word) = Some W_82884.
Proof. vm_refl. Qed.
Lemma D_82884 : decode_any W_82884 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 120%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82888 : bv 32 := @BV 32 0x08a13023%Z I.
Lemma F_82888 : fetch_word Asan.M.loaded_segments (@BV 64 0x82890%Z I : word) = Some W_82888.
Proof. vm_refl. Qed.
Lemma D_82888 : decode_any W_82888 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8288c : bv 32 := @BV 32 0x08a13423%Z I.
Lemma F_8288c : fetch_word Asan.M.loaded_segments (@BV 64 0x82894%Z I : word) = Some W_8288c.
Proof. vm_refl. Qed.
Lemma D_8288c : decode_any W_8288c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 136%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82890 : bv 32 := @BV 32 0x06810513%Z I.
Lemma F_82890 : fetch_word Asan.M.loaded_segments (@BV 64 0x82898%Z I : word) = Some W_82890.
Proof. vm_refl. Qed.
Lemma D_82890 : decode_any W_82890 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82894 : bv 32 := @BV 32 0x00100593%Z I.
Lemma F_82894 : fetch_word Asan.M.loaded_segments (@BV 64 0x8289c%Z I : word) = Some W_82894.
Proof. vm_refl. Qed.
Lemma D_82894 : decode_any W_82894 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82898 : bv 32 := @BV 32 0x398010ef%Z I.
Lemma F_82898 : fetch_word Asan.M.loaded_segments (@BV 64 0x828a0%Z I : word) = Some W_82898.
Proof. vm_refl. Qed.
Lemma D_82898 : decode_any W_82898 = Some (Jal (@BV 5 1%Z I) (@BV 21 5016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8289c : bv 32 := @BV 32 0xfff91517%Z I.
Lemma F_8289c : fetch_word Asan.M.loaded_segments (@BV 64 0x828a4%Z I : word) = Some W_8289c.
Proof. vm_refl. Qed.
Lemma D_8289c : decode_any W_8289c = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048465%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828a0 : bv 32 := @BV 32 0x000014b7%Z I.
Lemma F_828a0 : fetch_word Asan.M.loaded_segments (@BV 64 0x828a8%Z I : word) = Some W_828a0.
Proof. vm_refl. Qed.
Lemma D_828a0 : decode_any W_828a0 = Some (Lui (@BV 5 9%Z I) (@BV 20 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828a4 : bv 32 := @BV 32 0x76950593%Z I.
Lemma F_828a4 : fetch_word Asan.M.loaded_segments (@BV 64 0x828ac%Z I : word) = Some W_828a4.
Proof. vm_refl. Qed.
Lemma D_828a4 : decode_any W_828a4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 12 1897%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828a8 : bv 32 := @BV 32 0xfff4849b%Z I.
Lemma F_828a8 : fetch_word Asan.M.loaded_segments (@BV 64 0x828b0%Z I : word) = Some W_828a8.
Proof. vm_refl. Qed.
Lemma D_828a8 : decode_any W_828a8 = Some (OpImm32 (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828b8 : bv 32 := @BV 32 0x00050413%Z I.
Lemma F_828b8 : fetch_word Asan.M.loaded_segments (@BV 64 0x828c0%Z I : word) = Some W_828b8.
Proof. vm_refl. Qed.
Lemma D_828b8 : decode_any W_828b8 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828bc : bv 32 := @BV 32 0x00810513%Z I.
Lemma F_828bc : fetch_word Asan.M.loaded_segments (@BV 64 0x828c4%Z I : word) = Some W_828bc.
Proof. vm_refl. Qed.
Lemma D_828bc : decode_any W_828bc = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828c0 : bv 32 := @BV 32 0x0aa00593%Z I.
Lemma F_828c0 : fetch_word Asan.M.loaded_segments (@BV 64 0x828c8%Z I : word) = Some W_828c0.
Proof. vm_refl. Qed.
Lemma D_828c0 : decode_any W_828c0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 170%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828c4 : bv 32 := @BV 32 0x05800613%Z I.
Lemma F_828c4 : fetch_word Asan.M.loaded_segments (@BV 64 0x828cc%Z I : word) = Some W_828c4.
Proof. vm_refl. Qed.
Lemma D_828c4 : decode_any W_828c4 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828c8 : bv 32 := @BV 32 0xe68fd0ef%Z I.
Lemma F_828c8 : fetch_word Asan.M.loaded_segments (@BV 64 0x828d0%Z I : word) = Some W_828c8.
Proof. vm_refl. Qed.
Lemma D_828c8 : decode_any W_828c8 = Some (Jal (@BV 5 1%Z I) (@BV 21 2086504%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828cc : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_828cc : fetch_word Asan.M.loaded_segments (@BV 64 0x828d4%Z I : word) = Some W_828cc.
Proof. vm_refl. Qed.
Lemma D_828cc : decode_any W_828cc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828d0 : bv 32 := @BV 32 0x02913423%Z I.
Lemma F_828d0 : fetch_word Asan.M.loaded_segments (@BV 64 0x828d8%Z I : word) = Some W_828d0.
Proof. vm_refl. Qed.
Lemma D_828d0 : decode_any W_828d0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828d4 : bv 32 := @BV 32 0x06013023%Z I.
Lemma F_828d4 : fetch_word Asan.M.loaded_segments (@BV 64 0x828dc%Z I : word) = Some W_828d4.
Proof. vm_refl. Qed.
Lemma D_828d4 : decode_any W_828d4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 0%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828d8 : bv 32 := @BV 32 0xfff92517%Z I.
Lemma F_828d8 : fetch_word Asan.M.loaded_segments (@BV 64 0x828e0%Z I : word) = Some W_828d8.
Proof. vm_refl. Qed.
Lemma D_828d8 : decode_any W_828d8 = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048466%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828dc : bv 32 := @BV 32 0x11150513%Z I.
Lemma F_828dc : fetch_word Asan.M.loaded_segments (@BV 64 0x828e4%Z I : word) = Some W_828dc.
Proof. vm_refl. Qed.
Lemma D_828dc : decode_any W_828dc = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 273%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828e0 : bv 32 := @BV 32 0x279000ef%Z I.
Lemma F_828e0 : fetch_word Asan.M.loaded_segments (@BV 64 0x828e8%Z I : word) = Some W_828e0.
Proof. vm_refl. Qed.
Lemma D_828e0 : decode_any W_828e0 = Some (Jal (@BV 5 1%Z I) (@BV 21 2680%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828e4 : bv 32 := @BV 32 0x06810513%Z I.
Lemma F_828e4 : fetch_word Asan.M.loaded_segments (@BV 64 0x828ec%Z I : word) = Some W_828e4.
Proof. vm_refl. Qed.
Lemma D_828e4 : decode_any W_828e4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828e8 : bv 32 := @BV 32 0x00810593%Z I.
Lemma F_828e8 : fetch_word Asan.M.loaded_segments (@BV 64 0x828f0%Z I : word) = Some W_828e8.
Proof. vm_refl. Qed.
Lemma D_828e8 : decode_any W_828e8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828ec : bv 32 := @BV 32 0x3cd010ef%Z I.
Lemma F_828ec : fetch_word Asan.M.loaded_segments (@BV 64 0x828f4%Z I : word) = Some W_828ec.
Proof. vm_refl. Qed.
Lemma D_828ec : decode_any W_828ec = Some (Jal (@BV 5 1%Z I) (@BV 21 7116%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828f0 : bv 32 := @BV 32 0x02050863%Z I.
Lemma F_828f0 : fetch_word Asan.M.loaded_segments (@BV 64 0x828f8%Z I : word) = Some W_828f0.
Proof. vm_refl. Qed.
Lemma D_828f0 : decode_any W_828f0 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828f4 : bv 32 := @BV 32 0xfff8f517%Z I.
Lemma F_828f4 : fetch_word Asan.M.loaded_segments (@BV 64 0x828fc%Z I : word) = Some W_828f4.
Proof. vm_refl. Qed.
Lemma D_828f4 : decode_any W_828f4 = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048463%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828f8 : bv 32 := @BV 32 0xa4f50493%Z I.
Lemma F_828f8 : fetch_word Asan.M.loaded_segments (@BV 64 0x82900%Z I : word) = Some W_828f8.
Proof. vm_refl. Qed.
Lemma D_828f8 : decode_any W_828f8 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 2639%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828fc : bv 32 := @BV 32 0x00813583%Z I.
Lemma F_828fc : fetch_word Asan.M.loaded_segments (@BV 64 0x82904%Z I : word) = Some W_828fc.
Proof. vm_refl. Qed.
Lemma D_828fc : decode_any W_828fc = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82900 : bv 32 := @BV 32 0x01013603%Z I.
Lemma F_82900 : fetch_word Asan.M.loaded_segments (@BV 64 0x82908%Z I : word) = Some W_82900.
Proof. vm_refl. Qed.
Lemma D_82900 : decode_any W_82900 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82904 : bv 32 := @BV 32 0x02013683%Z I.
Lemma F_82904 : fetch_word Asan.M.loaded_segments (@BV 64 0x8290c%Z I : word) = Some W_82904.
Proof. vm_refl. Qed.
Lemma D_82904 : decode_any W_82904 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82908 : bv 32 := @BV 32 0x00048513%Z I.
Lemma F_82908 : fetch_word Asan.M.loaded_segments (@BV 64 0x82910%Z I : word) = Some W_82908.
Proof. vm_refl. Qed.
Lemma D_82908 : decode_any W_82908 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8290c : bv 32 := @BV 32 0x1a5000ef%Z I.
Lemma F_8290c : fetch_word Asan.M.loaded_segments (@BV 64 0x82914%Z I : word) = Some W_8290c.
Proof. vm_refl. Qed.
Lemma D_8290c : decode_any W_8290c = Some (Jal (@BV 5 1%Z I) (@BV 21 2468%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82910 : bv 32 := @BV 32 0x06810513%Z I.
Lemma F_82910 : fetch_word Asan.M.loaded_segments (@BV 64 0x82918%Z I : word) = Some W_82910.
Proof. vm_refl. Qed.
Lemma D_82910 : decode_any W_82910 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82914 : bv 32 := @BV 32 0x00810593%Z I.
Lemma F_82914 : fetch_word Asan.M.loaded_segments (@BV 64 0x8291c%Z I : word) = Some W_82914.
Proof. vm_refl. Qed.
Lemma D_82914 : decode_any W_82914 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82918 : bv 32 := @BV 32 0x3a1010ef%Z I.
Lemma F_82918 : fetch_word Asan.M.loaded_segments (@BV 64 0x82920%Z I : word) = Some W_82918.
Proof. vm_refl. Qed.
Lemma D_82918 : decode_any W_82918 = Some (Jal (@BV 5 1%Z I) (@BV 21 7072%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8291c : bv 32 := @BV 32 0xfe0510e3%Z I.
Lemma F_8291c : fetch_word Asan.M.loaded_segments (@BV 64 0x82924%Z I : word) = Some W_8291c.
Proof. vm_refl. Qed.
Lemma D_8291c : decode_any W_8291c = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 8160%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82920 : bv 32 := @BV 32 0xfff94517%Z I.
Lemma F_82920 : fetch_word Asan.M.loaded_segments (@BV 64 0x82928%Z I : word) = Some W_82920.
Proof. vm_refl. Qed.
Lemma D_82920 : decode_any W_82920 = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048468%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82924 : bv 32 := @BV 32 0x3bb50513%Z I.
Lemma F_82924 : fetch_word Asan.M.loaded_segments (@BV 64 0x8292c%Z I : word) = Some W_82924.
Proof. vm_refl. Qed.
Lemma D_82924 : decode_any W_82924 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 955%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82928 : bv 32 := @BV 32 0x231000ef%Z I.
Lemma F_82928 : fetch_word Asan.M.loaded_segments (@BV 64 0x82930%Z I : word) = Some W_82928.
Proof. vm_refl. Qed.
Lemma D_82928 : decode_any W_82928 = Some (Jal (@BV 5 1%Z I) (@BV 21 2608%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8292c : bv 32 := @BV 32 0x02040c63%Z I.
Lemma F_8292c : fetch_word Asan.M.loaded_segments (@BV 64 0x82934%Z I : word) = Some W_8292c.
Proof. vm_refl. Qed.
Lemma D_8292c : decode_any W_8292c = Some (Branch BC_EQ (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82930 : bv 32 := @BV 32 0x000014b7%Z I.
Lemma F_82930 : fetch_word Asan.M.loaded_segments (@BV 64 0x82938%Z I : word) = Some W_82930.
Proof. vm_refl. Qed.
Lemma D_82930 : decode_any W_82930 = Some (Lui (@BV 5 9%Z I) (@BV 20 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82934 : bv 32 := @BV 32 0xfff4849b%Z I.
Lemma F_82934 : fetch_word Asan.M.loaded_segments (@BV 64 0x8293c%Z I : word) = Some W_82934.
Proof. vm_refl. Qed.
Lemma D_82934 : decode_any W_82934 = Some (OpImm32 (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82938 : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_82938 : fetch_word Asan.M.loaded_segments (@BV 64 0x82940%Z I : word) = Some W_82938.
Proof. vm_refl. Qed.
Lemma D_82938 : decode_any W_82938 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8293c : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_8293c : fetch_word Asan.M.loaded_segments (@BV 64 0x82944%Z I : word) = Some W_8293c.
Proof. vm_refl. Qed.
Lemma D_8293c : decode_any W_8293c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82940 : bv 32 := @BV 32 0xdfdfd0ef%Z I.
Lemma F_82940 : fetch_word Asan.M.loaded_segments (@BV 64 0x82948%Z I : word) = Some W_82940.
Proof. vm_refl. Qed.
Lemma D_82940 : decode_any W_82940 = Some (Jal (@BV 5 1%Z I) (@BV 21 2088444%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82944 : bv 32 := @BV 32 0xaaaab5b7%Z I.
Lemma F_82944 : fetch_word Asan.M.loaded_segments (@BV 64 0x8294c%Z I : word) = Some W_82944.
Proof. vm_refl. Qed.
Lemma D_82944 : decode_any W_82944 = Some (Lui (@BV 5 11%Z I) (@BV 20 699051%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82948 : bv 32 := @BV 32 0xaaa58593%Z I.
Lemma F_82948 : fetch_word Asan.M.loaded_segments (@BV 64 0x82950%Z I : word) = Some W_82948.
Proof. vm_refl. Qed.
Lemma D_82948 : decode_any W_82948 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 2730%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8294c : bv 32 := @BV 32 0x08b12a23%Z I.
Lemma F_8294c : fetch_word Asan.M.loaded_segments (@BV 64 0x82954%Z I : word) = Some W_8294c.
Proof. vm_refl. Qed.
Lemma D_8294c : decode_any W_8294c = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 11%Z I) (@BV 12 148%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82950 : bv 32 := @BV 32 0x09410593%Z I.
Lemma F_82950 : fetch_word Asan.M.loaded_segments (@BV 64 0x82958%Z I : word) = Some W_82950.
Proof. vm_refl. Qed.
Lemma D_82950 : decode_any W_82950 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 148%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82954 : bv 32 := @BV 32 0xdbdfd0ef%Z I.
Lemma F_82954 : fetch_word Asan.M.loaded_segments (@BV 64 0x8295c%Z I : word) = Some W_82954.
Proof. vm_refl. Qed.
Lemma D_82954 : decode_any W_82954 = Some (Jal (@BV 5 1%Z I) (@BV 21 2088380%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82968 : bv 32 := @BV 32 0x460010ef%Z I.
Lemma F_82968 : fetch_word Asan.M.loaded_segments (@BV 64 0x82970%Z I : word) = Some W_82968.
Proof. vm_refl. Qed.
Lemma D_82968 : decode_any W_82968 = Some (Jal (@BV 5 1%Z I) (@BV 21 5216%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8296c : bv 32 := @BV 32 0x0a813083%Z I.
Lemma F_8296c : fetch_word Asan.M.loaded_segments (@BV 64 0x82974%Z I : word) = Some W_8296c.
Proof. vm_refl. Qed.
Lemma D_8296c : decode_any W_8296c = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 168%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82970 : bv 32 := @BV 32 0x0a013403%Z I.
Lemma F_82970 : fetch_word Asan.M.loaded_segments (@BV 64 0x82978%Z I : word) = Some W_82970.
Proof. vm_refl. Qed.
Lemma D_82970 : decode_any W_82970 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 160%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82974 : bv 32 := @BV 32 0x09813483%Z I.
Lemma F_82974 : fetch_word Asan.M.loaded_segments (@BV 64 0x8297c%Z I : word) = Some W_82974.
Proof. vm_refl. Qed.
Lemma D_82974 : decode_any W_82974 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82978 : bv 32 := @BV 32 0x0b010113%Z I.
Lemma F_82978 : fetch_word Asan.M.loaded_segments (@BV 64 0x82980%Z I : word) = Some W_82978.
Proof. vm_refl. Qed.
Lemma D_82978 : decode_any W_82978 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 176%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8297c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8297c : fetch_word Asan.M.loaded_segments (@BV 64 0x82984%Z I : word) = Some W_8297c.
Proof. vm_refl. Qed.
Lemma D_8297c : decode_any W_8297c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82980 : bv 32 := @BV 32 0x09412603%Z I.
Lemma F_82980 : fetch_word Asan.M.loaded_segments (@BV 64 0x82988%Z I : word) = Some W_82980.
Proof. vm_refl. Qed.
Lemma D_82980 : decode_any W_82980 = Some (Load SZ4 true (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 148%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_829f8 : bv 32 := @BV 32 0x00371713%Z I.
Lemma F_829f8 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a00%Z I : word) = Some W_829f8.
Proof. vm_refl. Qed.
Lemma D_829f8 : decode_any W_829f8 = Some (ShiftImm ALU_SLL (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_829fc : bv 32 := @BV 32 0x00e595bb%Z I.
Lemma F_829fc : fetch_word Asan.M.loaded_segments (@BV 64 0x82a04%Z I : word) = Some W_829fc.
Proof. vm_refl. Qed.
Lemma D_829fc : decode_any W_829fc = Some (Op32 ALU_SLL (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a00 : bv 32 := @BV 32 0x00e6163b%Z I.
Lemma F_82a00 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a08%Z I : word) = Some W_82a00.
Proof. vm_refl. Qed.
Lemma D_82a00 : decode_any W_82a00 = Some (Op32 ALU_SLL (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a04 : bv 32 := @BV 32 0x1406a7af%Z I.
Lemma F_82a04 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a0c%Z I : word) = Some W_82a04.
Proof. vm_refl. Qed.
Lemma D_82a04 : decode_any W_82a04 = Some (Lr AW true false (@BV 5 15%Z I) (@BV 5 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a08 : bv 32 := @BV 32 0x00060813%Z I.
Lemma F_82a08 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a10%Z I : word) = Some W_82a08.
Proof. vm_refl. Qed.
Lemma D_82a08 : decode_any W_82a08 = Some (OpImm ALU_ADD (@BV 5 16%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a0c : bv 32 := @BV 32 0x0107c833%Z I.
Lemma F_82a0c : fetch_word Asan.M.loaded_segments (@BV 64 0x82a14%Z I : word) = Some W_82a0c.
Proof. vm_refl. Qed.
Lemma D_82a0c : decode_any W_82a0c = Some (Op ALU_XOR (@BV 5 16%Z I) (@BV 5 15%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a10 : bv 32 := @BV 32 0x00b87833%Z I.
Lemma F_82a10 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a18%Z I : word) = Some W_82a10.
Proof. vm_refl. Qed.
Lemma D_82a10 : decode_any W_82a10 = Some (Op ALU_AND (@BV 5 16%Z I) (@BV 5 16%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a14 : bv 32 := @BV 32 0x0107c833%Z I.
Lemma F_82a14 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a1c%Z I : word) = Some W_82a14.
Proof. vm_refl. Qed.
Lemma D_82a14 : decode_any W_82a14 = Some (Op ALU_XOR (@BV 5 16%Z I) (@BV 5 15%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a18 : bv 32 := @BV 32 0x1906a82f%Z I.
Lemma F_82a18 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a20%Z I : word) = Some W_82a18.
Proof. vm_refl. Qed.
Lemma D_82a18 : decode_any W_82a18 = Some (Sc AW false false (@BV 5 16%Z I) (@BV 5 13%Z I) (@BV 5 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a1c : bv 32 := @BV 32 0xfe0814e3%Z I.
Lemma F_82a1c : fetch_word Asan.M.loaded_segments (@BV 64 0x82a24%Z I : word) = Some W_82a1c.
Proof. vm_refl. Qed.
Lemma D_82a1c : decode_any W_82a1c = Some (Branch BC_NE (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 13 8168%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a20 : bv 32 := @BV 32 0x00e7d5bb%Z I.
Lemma F_82a20 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a28%Z I : word) = Some W_82a20.
Proof. vm_refl. Qed.
Lemma D_82a20 : decode_any W_82a20 = Some (Op32 ALU_SRL (@BV 5 11%Z I) (@BV 5 15%Z I) (@BV 5 14%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a24 : bv 32 := @BV 32 0x0ff5f593%Z I.
Lemma F_82a24 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a2c%Z I : word) = Some W_82a24.
Proof. vm_refl. Qed.
Lemma D_82a24 : decode_any W_82a24 = Some (OpImm ALU_AND (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 255%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a28 : bv 32 := @BV 32 0x04059063%Z I.
Lemma F_82a28 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a30%Z I : word) = Some W_82a28.
Proof. vm_refl. Qed.
Lemma D_82a28 : decode_any W_82a28 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a2c : bv 32 := @BV 32 0x00050993%Z I.
Lemma F_82a2c : fetch_word Asan.M.loaded_segments (@BV 64 0x82a34%Z I : word) = Some W_82a2c.
Proof. vm_refl. Qed.
Lemma D_82a2c : decode_any W_82a2c = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a30 : bv 32 := @BV 32 0xbecfa0ef%Z I.
Lemma F_82a30 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a38%Z I : word) = Some W_82a30.
Proof. vm_refl. Qed.
Lemma D_82a30 : decode_any W_82a30 = Some (Jal (@BV 5 1%Z I) (@BV 21 2073580%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a34 : bv 32 := @BV 32 0x0089a503%Z I.
Lemma F_82a34 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a3c%Z I : word) = Some W_82a34.
Proof. vm_refl. Qed.
Lemma D_82a34 : decode_any W_82a34 = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a38 : bv 32 := @BV 32 0x00090593%Z I.
Lemma F_82a38 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a40%Z I : word) = Some W_82a38.
Proof. vm_refl. Qed.
Lemma D_82a38 : decode_any W_82a38 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a3c : bv 32 := @BV 32 0x00048613%Z I.
Lemma F_82a3c : fetch_word Asan.M.loaded_segments (@BV 64 0x82a44%Z I : word) = Some W_82a3c.
Proof. vm_refl. Qed.
Lemma D_82a3c : decode_any W_82a3c = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a40 : bv 32 := @BV 32 0xdadfd0ef%Z I.
Lemma F_82a40 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a48%Z I : word) = Some W_82a40.
Proof. vm_refl. Qed.
Lemma D_82a40 : decode_any W_82a40 = Some (Jal (@BV 5 1%Z I) (@BV 21 2088364%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a44 : bv 32 := @BV 32 0x0310000f%Z I.
Lemma F_82a44 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a4c%Z I : word) = Some W_82a44.
Proof. vm_refl. Qed.
Lemma D_82a44 : decode_any W_82a44 = Some (Fence (@BV 4 0%Z I) (@BV 4 3%Z I) (@BV 4 1%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a48 : bv 32 := @BV 32 0x00040023%Z I.
Lemma F_82a48 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a50%Z I : word) = Some W_82a48.
Proof. vm_refl. Qed.
Lemma D_82a48 : decode_any W_82a48 = Some (Store SZ1 (@BV 5 8%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a4c : bv 32 := @BV 32 0x02813083%Z I.
Lemma F_82a4c : fetch_word Asan.M.loaded_segments (@BV 64 0x82a54%Z I : word) = Some W_82a4c.
Proof. vm_refl. Qed.
Lemma D_82a4c : decode_any W_82a4c = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a50 : bv 32 := @BV 32 0x02013403%Z I.
Lemma F_82a50 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a58%Z I : word) = Some W_82a50.
Proof. vm_refl. Qed.
Lemma D_82a50 : decode_any W_82a50 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a54 : bv 32 := @BV 32 0x01813483%Z I.
Lemma F_82a54 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a5c%Z I : word) = Some W_82a54.
Proof. vm_refl. Qed.
Lemma D_82a54 : decode_any W_82a54 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a58 : bv 32 := @BV 32 0x01013903%Z I.
Lemma F_82a58 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a60%Z I : word) = Some W_82a58.
Proof. vm_refl. Qed.
Lemma D_82a58 : decode_any W_82a58 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a5c : bv 32 := @BV 32 0x00813983%Z I.
Lemma F_82a5c : fetch_word Asan.M.loaded_segments (@BV 64 0x82a64%Z I : word) = Some W_82a5c.
Proof. vm_refl. Qed.
Lemma D_82a5c : decode_any W_82a5c = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a74 : bv 32 := @BV 32 0x00098513%Z I.
Lemma F_82a74 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a7c%Z I : word) = Some W_82a74.
Proof. vm_refl. Qed.
Lemma D_82a74 : decode_any W_82a74 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a78 : bv 32 := @BV 32 0xfb5ff06f%Z I.
Lemma F_82a78 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a80%Z I : word) = Some W_82a78.
Proof. vm_refl. Qed.
Lemma D_82a78 : decode_any W_82a78 = Some (Jal (@BV 5 0%Z I) (@BV 21 2097076%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a7c : bv 32 := @BV 32 0x00053503%Z I.
Lemma F_82a7c : fetch_word Asan.M.loaded_segments (@BV 64 0x82a84%Z I : word) = Some W_82a7c.
Proof. vm_refl. Qed.
Lemma D_82a7c : decode_any W_82a7c = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a80 : bv 32 := @BV 32 0x01053503%Z I.
Lemma F_82a80 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a88%Z I : word) = Some W_82a80.
Proof. vm_refl. Qed.
Lemma D_82a80 : decode_any W_82a80 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a84 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_82a84 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a8c%Z I : word) = Some W_82a84.
Proof. vm_refl. Qed.
Lemma D_82a84 : decode_any W_82a84 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a88 : bv 32 := @BV 32 0x00053503%Z I.
Lemma F_82a88 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a90%Z I : word) = Some W_82a88.
Proof. vm_refl. Qed.
Lemma D_82a88 : decode_any W_82a88 = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a8c : bv 32 := @BV 32 0x00052503%Z I.
Lemma F_82a8c : fetch_word Asan.M.loaded_segments (@BV 64 0x82a94%Z I : word) = Some W_82a8c.
Proof. vm_refl. Qed.
Lemma D_82a8c : decode_any W_82a8c = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a90 : bv 32 := @BV 32 0xff95051b%Z I.
Lemma F_82a90 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a98%Z I : word) = Some W_82a90.
Proof. vm_refl. Qed.
Lemma D_82a90 : decode_any W_82a90 = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4089%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a94 : bv 32 := @BV 32 0xffb57513%Z I.
Lemma F_82a94 : fetch_word Asan.M.loaded_segments (@BV 64 0x82a9c%Z I : word) = Some W_82a94.
Proof. vm_refl. Qed.
Lemma D_82a94 : decode_any W_82a94 = Some (OpImm ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4091%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a98 : bv 32 := @BV 32 0x00153513%Z I.
Lemma F_82a98 : fetch_word Asan.M.loaded_segments (@BV 64 0x82aa0%Z I : word) = Some W_82a98.
Proof. vm_refl. Qed.
Lemma D_82a98 : decode_any W_82a98 = Some (OpImm ALU_SLTU (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a9c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_82a9c : fetch_word Asan.M.loaded_segments (@BV 64 0x82aa4%Z I : word) = Some W_82a9c.
Proof. vm_refl. Qed.
Lemma D_82a9c : decode_any W_82a9c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82aac : bv 32 := @BV 32 0x00700593%Z I.
Lemma F_82aac : fetch_word Asan.M.loaded_segments (@BV 64 0x82ab4%Z I : word) = Some W_82aac.
Proof. vm_refl. Qed.
Lemma D_82aac : decode_any W_82aac = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 7%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ab0 : bv 32 := @BV 32 0x02a5e063%Z I.
Lemma F_82ab0 : fetch_word Asan.M.loaded_segments (@BV 64 0x82ab8%Z I : word) = Some W_82ab0.
Proof. vm_refl. Qed.
Lemma D_82ab0 : decode_any W_82ab0 = Some (Branch BC_LTU (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 13 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ab4 : bv 32 := @BV 32 0x00251513%Z I.
Lemma F_82ab4 : fetch_word Asan.M.loaded_segments (@BV 64 0x82abc%Z I : word) = Some W_82ab4.
Proof. vm_refl. Qed.
Lemma D_82ab4 : decode_any W_82ab4 = Some (ShiftImm ALU_SLL (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 6 2%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ab8 : bv 32 := @BV 32 0xfffa0597%Z I.
Lemma F_82ab8 : fetch_word Asan.M.loaded_segments (@BV 64 0x82ac0%Z I : word) = Some W_82ab8.
Proof. vm_refl. Qed.
Lemma D_82ab8 : decode_any W_82ab8 = Some (Auipc (@BV 5 11%Z I) (@BV 20 1048480%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82abc : bv 32 := @BV 32 0xc2058593%Z I.
Lemma F_82abc : fetch_word Asan.M.loaded_segments (@BV 64 0x82ac4%Z I : word) = Some W_82abc.
Proof. vm_refl. Qed.
Lemma D_82abc : decode_any W_82abc = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ac0 : bv 32 := @BV 32 0x00a58533%Z I.
Lemma F_82ac0 : fetch_word Asan.M.loaded_segments (@BV 64 0x82ac8%Z I : word) = Some W_82ac0.
Proof. vm_refl. Qed.
Lemma D_82ac0 : decode_any W_82ac0 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ac4 : bv 32 := @BV 32 0x00052503%Z I.
Lemma F_82ac4 : fetch_word Asan.M.loaded_segments (@BV 64 0x82acc%Z I : word) = Some W_82ac4.
Proof. vm_refl. Qed.
Lemma D_82ac4 : decode_any W_82ac4 = Some (Load SZ4 true (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ac8 : bv 32 := @BV 32 0x00a58533%Z I.
Lemma F_82ac8 : fetch_word Asan.M.loaded_segments (@BV 64 0x82ad0%Z I : word) = Some W_82ac8.
Proof. vm_refl. Qed.
Lemma D_82ac8 : decode_any W_82ac8 = Some (Op ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82acc : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_82acc : fetch_word Asan.M.loaded_segments (@BV 64 0x82ad4%Z I : word) = Some W_82acc.
Proof. vm_refl. Qed.
Lemma D_82acc : decode_any W_82acc = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ad0 : bv 32 := @BV 32 0xfff94517%Z I.
Lemma F_82ad0 : fetch_word Asan.M.loaded_segments (@BV 64 0x82ad8%Z I : word) = Some W_82ad0.
Proof. vm_refl. Qed.
Lemma D_82ad0 : decode_any W_82ad0 = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048468%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ad4 : bv 32 := @BV 32 0xa6650513%Z I.
Lemma F_82ad4 : fetch_word Asan.M.loaded_segments (@BV 64 0x82adc%Z I : word) = Some W_82ad4.
Proof. vm_refl. Qed.
Lemma D_82ad4 : decode_any W_82ad4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2662%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ad8 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_82ad8 : fetch_word Asan.M.loaded_segments (@BV 64 0x82ae0%Z I : word) = Some W_82ad8.
Proof. vm_refl. Qed.
Lemma D_82ad8 : decode_any W_82ad8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82adc : bv 32 := @BV 32 0xef010113%Z I.
Lemma F_82adc : fetch_word Asan.M.loaded_segments (@BV 64 0x82ae4%Z I : word) = Some W_82adc.
Proof. vm_refl. Qed.
Lemma D_82adc : decode_any W_82adc = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 3824%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ae0 : bv 32 := @BV 32 0x10113423%Z I.
Lemma F_82ae0 : fetch_word Asan.M.loaded_segments (@BV 64 0x82ae8%Z I : word) = Some W_82ae0.
Proof. vm_refl. Qed.
Lemma D_82ae0 : decode_any W_82ae0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 264%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ae4 : bv 32 := @BV 32 0x10813023%Z I.
Lemma F_82ae4 : fetch_word Asan.M.loaded_segments (@BV 64 0x82aec%Z I : word) = Some W_82ae4.
Proof. vm_refl. Qed.
Lemma D_82ae4 : decode_any W_82ae4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 256%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ae8 : bv 32 := @BV 32 0x0e913c23%Z I.
Lemma F_82ae8 : fetch_word Asan.M.loaded_segments (@BV 64 0x82af0%Z I : word) = Some W_82ae8.
Proof. vm_refl. Qed.
Lemma D_82ae8 : decode_any W_82ae8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 248%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82aec : bv 32 := @BV 32 0x0f213823%Z I.
Lemma F_82aec : fetch_word Asan.M.loaded_segments (@BV 64 0x82af4%Z I : word) = Some W_82aec.
Proof. vm_refl. Qed.
Lemma D_82aec : decode_any W_82aec = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 240%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82af0 : bv 32 := @BV 32 0x0f313423%Z I.
Lemma F_82af0 : fetch_word Asan.M.loaded_segments (@BV 64 0x82af8%Z I : word) = Some W_82af0.
Proof. vm_refl. Qed.
Lemma D_82af0 : decode_any W_82af0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 232%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82af4 : bv 32 := @BV 32 0x0f413023%Z I.
Lemma F_82af4 : fetch_word Asan.M.loaded_segments (@BV 64 0x82afc%Z I : word) = Some W_82af4.
Proof. vm_refl. Qed.
Lemma D_82af4 : decode_any W_82af4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 224%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82af8 : bv 32 := @BV 32 0x0d513c23%Z I.
Lemma F_82af8 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b00%Z I : word) = Some W_82af8.
Proof. vm_refl. Qed.
Lemma D_82af8 : decode_any W_82af8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 216%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82afc : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_82afc : fetch_word Asan.M.loaded_segments (@BV 64 0x82b04%Z I : word) = Some W_82afc.
Proof. vm_refl. Qed.
Lemma D_82afc : decode_any W_82afc = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b00 : bv 32 := @BV 32 0xfff00513%Z I.
Lemma F_82b00 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b08%Z I : word) = Some W_82b00.
Proof. vm_refl. Qed.
Lemma D_82b00 : decode_any W_82b00 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b04 : bv 32 := @BV 32 0x12090463%Z I.
Lemma F_82b04 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b0c%Z I : word) = Some W_82b04.
Proof. vm_refl. Qed.
Lemma D_82b04 : decode_any W_82b04 = Some (Branch BC_EQ (@BV 5 18%Z I) (@BV 5 0%Z I) (@BV 13 296%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b08 : bv 32 := @BV 32 0x00060413%Z I.
Lemma F_82b08 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b10%Z I : word) = Some W_82b08.
Proof. vm_refl. Qed.
Lemma D_82b08 : decode_any W_82b08 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b0c : bv 32 := @BV 32 0x0007c617%Z I.
Lemma F_82b0c : fetch_word Asan.M.loaded_segments (@BV 64 0x82b14%Z I : word) = Some W_82b0c.
Proof. vm_refl. Qed.
Lemma D_82b0c : decode_any W_82b0c = Some (Auipc (@BV 5 12%Z I) (@BV 20 124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b10 : bv 32 := @BV 32 0x74c63603%Z I.
Lemma F_82b10 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b18%Z I : word) = Some W_82b10.
Proof. vm_refl. Qed.
Lemma D_82b10 : decode_any W_82b10 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 1868%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b14 : bv 32 := @BV 32 0x10464603%Z I.
Lemma F_82b14 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b1c%Z I : word) = Some W_82b14.
Proof. vm_refl. Qed.
Lemma D_82b14 : decode_any W_82b14 = Some (Load SZ1 false (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 260%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b18 : bv 32 := @BV 32 0x00167613%Z I.
Lemma F_82b18 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b20%Z I : word) = Some W_82b18.
Proof. vm_refl. Qed.
Lemma D_82b18 : decode_any W_82b18 = Some (OpImm ALU_AND (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b1c : bv 32 := @BV 32 0x10060863%Z I.
Lemma F_82b1c : fetch_word Asan.M.loaded_segments (@BV 64 0x82b24%Z I : word) = Some W_82b1c.
Proof. vm_refl. Qed.
Lemma D_82b1c : decode_any W_82b1c = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 272%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b20 : bv 32 := @BV 32 0x00058493%Z I.
Lemma F_82b20 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b28%Z I : word) = Some W_82b20.
Proof. vm_refl. Qed.
Lemma D_82b20 : decode_any W_82b20 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b24 : bv 32 := @BV 32 0x00d10513%Z I.
Lemma F_82b24 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b2c%Z I : word) = Some W_82b24.
Proof. vm_refl. Qed.
Lemma D_82b24 : decode_any W_82b24 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b28 : bv 32 := @BV 32 0x0aa00593%Z I.
Lemma F_82b28 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b30%Z I : word) = Some W_82b28.
Proof. vm_refl. Qed.
Lemma D_82b28 : decode_any W_82b28 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 170%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b2c : bv 32 := @BV 32 0x0c800613%Z I.
Lemma F_82b2c : fetch_word Asan.M.loaded_segments (@BV 64 0x82b34%Z I : word) = Some W_82b2c.
Proof. vm_refl. Qed.
Lemma D_82b2c : decode_any W_82b2c = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 200%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b30 : bv 32 := @BV 32 0xc00fd0ef%Z I.
Lemma F_82b30 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b38%Z I : word) = Some W_82b30.
Proof. vm_refl. Qed.
Lemma D_82b30 : decode_any W_82b30 = Some (Jal (@BV 5 1%Z I) (@BV 21 2085888%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b34 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_82b34 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b3c%Z I : word) = Some W_82b34.
Proof. vm_refl. Qed.
Lemma D_82b34 : decode_any W_82b34 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b38 : bv 32 := @BV 32 0xd4cfd0ef%Z I.
Lemma F_82b38 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b40%Z I : word) = Some W_82b38.
Proof. vm_refl. Qed.
Lemma D_82b38 : decode_any W_82b38 = Some (Jal (@BV 5 1%Z I) (@BV 21 2086220%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b3c : bv 32 := @BV 32 0x0be00593%Z I.
Lemma F_82b3c : fetch_word Asan.M.loaded_segments (@BV 64 0x82b44%Z I : word) = Some W_82b3c.
Proof. vm_refl. Qed.
Lemma D_82b3c : decode_any W_82b3c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 190%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b40 : bv 32 := @BV 32 0x14b57463%Z I.
Lemma F_82b40 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b48%Z I : word) = Some W_82b40.
Proof. vm_refl. Qed.
Lemma D_82b40 : decode_any W_82b40 = Some (Branch BC_GEU (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 13 328%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b44 : bv 32 := @BV 32 0x94cfe0ef%Z I.
Lemma F_82b44 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b4c%Z I : word) = Some W_82b44.
Proof. vm_refl. Qed.
Lemma D_82b44 : decode_any W_82b44 = Some (Jal (@BV 5 1%Z I) (@BV 21 2089292%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b58 : bv 32 := @BV 32 0x0c800593%Z I.
Lemma F_82b58 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b60%Z I : word) = Some W_82b58.
Proof. vm_refl. Qed.
Lemma D_82b58 : decode_any W_82b58 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 200%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b5c : bv 32 := @BV 32 0x00090713%Z I.
Lemma F_82b5c : fetch_word Asan.M.loaded_segments (@BV 64 0x82b64%Z I : word) = Some W_82b5c.
Proof. vm_refl. Qed.
Lemma D_82b5c : decode_any W_82b5c = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b60 : bv 32 := @BV 32 0x045000ef%Z I.
Lemma F_82b60 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b68%Z I : word) = Some W_82b60.
Proof. vm_refl. Qed.
Lemma D_82b60 : decode_any W_82b60 = Some (Jal (@BV 5 1%Z I) (@BV 21 2116%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b64 : bv 32 := @BV 32 0x000805b7%Z I.
Lemma F_82b64 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b6c%Z I : word) = Some W_82b64.
Proof. vm_refl. Qed.
Lemma D_82b64 : decode_any W_82b64 = Some (Lui (@BV 5 11%Z I) (@BV 20 128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b68 : bv 32 := @BV 32 0x00d10513%Z I.
Lemma F_82b68 : fetch_word Asan.M.loaded_segments (@BV 64 0x82b70%Z I : word) = Some W_82b68.
Proof. vm_refl. Qed.
Lemma D_82b68 : decode_any W_82b68 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 2%Z I) (@BV 12 13%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82c2c : bv 32 := @BV 32 0x0005051b%Z I.
Lemma F_82c2c : fetch_word Asan.M.loaded_segments (@BV 64 0x82c34%Z I : word) = Some W_82c2c.
Proof. vm_refl. Qed.
Lemma D_82c2c : decode_any W_82c2c = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82c30 : bv 32 := @BV 32 0x10813083%Z I.
Lemma F_82c30 : fetch_word Asan.M.loaded_segments (@BV 64 0x82c38%Z I : word) = Some W_82c30.
Proof. vm_refl. Qed.
Lemma D_82c30 : decode_any W_82c30 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 264%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82c34 : bv 32 := @BV 32 0x10013403%Z I.
Lemma F_82c34 : fetch_word Asan.M.loaded_segments (@BV 64 0x82c3c%Z I : word) = Some W_82c34.
Proof. vm_refl. Qed.
Lemma D_82c34 : decode_any W_82c34 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 256%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82c38 : bv 32 := @BV 32 0x0f813483%Z I.
Lemma F_82c38 : fetch_word Asan.M.loaded_segments (@BV 64 0x82c40%Z I : word) = Some W_82c38.
Proof. vm_refl. Qed.
Lemma D_82c38 : decode_any W_82c38 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 248%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82c3c : bv 32 := @BV 32 0x0f013903%Z I.
Lemma F_82c3c : fetch_word Asan.M.loaded_segments (@BV 64 0x82c44%Z I : word) = Some W_82c3c.
Proof. vm_refl. Qed.
Lemma D_82c3c : decode_any W_82c3c = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 240%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82c40 : bv 32 := @BV 32 0x0e813983%Z I.
Lemma F_82c40 : fetch_word Asan.M.loaded_segments (@BV 64 0x82c48%Z I : word) = Some W_82c40.
Proof. vm_refl. Qed.
Lemma D_82c40 : decode_any W_82c40 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 232%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82c44 : bv 32 := @BV 32 0x0e013a03%Z I.
Lemma F_82c44 : fetch_word Asan.M.loaded_segments (@BV 64 0x82c4c%Z I : word) = Some W_82c44.
Proof. vm_refl. Qed.
Lemma D_82c44 : decode_any W_82c44 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 224%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82c48 : bv 32 := @BV 32 0x0d813a83%Z I.
Lemma F_82c48 : fetch_word Asan.M.loaded_segments (@BV 64 0x82c50%Z I : word) = Some W_82c48.
Proof. vm_refl. Qed.
Lemma D_82c48 : decode_any W_82c48 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 216%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82c4c : bv 32 := @BV 32 0x11010113%Z I.
Lemma F_82c4c : fetch_word Asan.M.loaded_segments (@BV 64 0x82c54%Z I : word) = Some W_82c4c.
Proof. vm_refl. Qed.
Lemma D_82c4c : decode_any W_82c4c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 272%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82c50 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_82c50 : fetch_word Asan.M.loaded_segments (@BV 64 0x82c58%Z I : word) = Some W_82c50.
Proof. vm_refl. Qed.
Lemma D_82c50 : decode_any W_82c50 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85ac8 : bv 32 := @BV 32 0xf7010113%Z I.
Lemma F_85ac8 : fetch_word Asan.M.loaded_segments (@BV 64 0x85ad0%Z I : word) = Some W_85ac8.
Proof. vm_refl. Qed.
Lemma D_85ac8 : decode_any W_85ac8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 3952%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85acc : bv 32 := @BV 32 0x08113423%Z I.
Lemma F_85acc : fetch_word Asan.M.loaded_segments (@BV 64 0x85ad4%Z I : word) = Some W_85acc.
Proof. vm_refl. Qed.
Lemma D_85acc : decode_any W_85acc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 136%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85ad0 : bv 32 := @BV 32 0x08813023%Z I.
Lemma F_85ad0 : fetch_word Asan.M.loaded_segments (@BV 64 0x85ad8%Z I : word) = Some W_85ad0.
Proof. vm_refl. Qed.
Lemma D_85ad0 : decode_any W_85ad0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85ad4 : bv 32 := @BV 32 0x06913c23%Z I.
Lemma F_85ad4 : fetch_word Asan.M.loaded_segments (@BV 64 0x85adc%Z I : word) = Some W_85ad4.
Proof. vm_refl. Qed.
Lemma D_85ad4 : decode_any W_85ad4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 120%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85ad8 : bv 32 := @BV 32 0x07213823%Z I.
Lemma F_85ad8 : fetch_word Asan.M.loaded_segments (@BV 64 0x85ae0%Z I : word) = Some W_85ad8.
Proof. vm_refl. Qed.
Lemma D_85ad8 : decode_any W_85ad8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 112%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85adc : bv 32 := @BV 32 0x07313423%Z I.
Lemma F_85adc : fetch_word Asan.M.loaded_segments (@BV 64 0x85ae4%Z I : word) = Some W_85adc.
Proof. vm_refl. Qed.
Lemma D_85adc : decode_any W_85adc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85ae0 : bv 32 := @BV 32 0x07413023%Z I.
Lemma F_85ae0 : fetch_word Asan.M.loaded_segments (@BV 64 0x85ae8%Z I : word) = Some W_85ae0.
Proof. vm_refl. Qed.
Lemma D_85ae0 : decode_any W_85ae0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85ae4 : bv 32 := @BV 32 0x05513c23%Z I.
Lemma F_85ae4 : fetch_word Asan.M.loaded_segments (@BV 64 0x85aec%Z I : word) = Some W_85ae4.
Proof. vm_refl. Qed.
Lemma D_85ae4 : decode_any W_85ae4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85ae8 : bv 32 := @BV 32 0x05613823%Z I.
Lemma F_85ae8 : fetch_word Asan.M.loaded_segments (@BV 64 0x85af0%Z I : word) = Some W_85ae8.
Proof. vm_refl. Qed.
Lemma D_85ae8 : decode_any W_85ae8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 22%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85aec : bv 32 := @BV 32 0x05713423%Z I.
Lemma F_85aec : fetch_word Asan.M.loaded_segments (@BV 64 0x85af4%Z I : word) = Some W_85aec.
Proof. vm_refl. Qed.
Lemma D_85aec : decode_any W_85aec = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 23%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85af0 : bv 32 := @BV 32 0x05813023%Z I.
Lemma F_85af0 : fetch_word Asan.M.loaded_segments (@BV 64 0x85af8%Z I : word) = Some W_85af0.
Proof. vm_refl. Qed.
Lemma D_85af0 : decode_any W_85af0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 24%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85af4 : bv 32 := @BV 32 0x03913c23%Z I.
Lemma F_85af4 : fetch_word Asan.M.loaded_segments (@BV 64 0x85afc%Z I : word) = Some W_85af4.
Proof. vm_refl. Qed.
Lemma D_85af4 : decode_any W_85af4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 25%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85af8 : bv 32 := @BV 32 0x03a13823%Z I.
Lemma F_85af8 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b00%Z I : word) = Some W_85af8.
Proof. vm_refl. Qed.
Lemma D_85af8 : decode_any W_85af8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 26%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85afc : bv 32 := @BV 32 0x03b13423%Z I.
Lemma F_85afc : fetch_word Asan.M.loaded_segments (@BV 64 0x85b04%Z I : word) = Some W_85afc.
Proof. vm_refl. Qed.
Lemma D_85afc : decode_any W_85afc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 27%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b00 : bv 32 := @BV 32 0x00058913%Z I.
Lemma F_85b00 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b08%Z I : word) = Some W_85b00.
Proof. vm_refl. Qed.
Lemma D_85b00 : decode_any W_85b00 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b04 : bv 32 := @BV 32 0x00079597%Z I.
Lemma F_85b04 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b0c%Z I : word) = Some W_85b04.
Proof. vm_refl. Qed.
Lemma D_85b04 : decode_any W_85b04 = Some (Auipc (@BV 5 11%Z I) (@BV 20 121%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b08 : bv 32 := @BV 32 0x7545b583%Z I.
Lemma F_85b08 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b10%Z I : word) = Some W_85b08.
Proof. vm_refl. Qed.
Lemma D_85b08 : decode_any W_85b08 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1876%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b0c : bv 32 := @BV 32 0x0895c583%Z I.
Lemma F_85b0c : fetch_word Asan.M.loaded_segments (@BV 64 0x85b14%Z I : word) = Some W_85b0c.
Proof. vm_refl. Qed.
Lemma D_85b0c : decode_any W_85b0c = Some (Load SZ1 false (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 137%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b10 : bv 32 := @BV 32 0x18058a63%Z I.
Lemma F_85b10 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b18%Z I : word) = Some W_85b10.
Proof. vm_refl. Qed.
Lemma D_85b10 : decode_any W_85b10 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 404%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b14 : bv 32 := @BV 32 0x00050993%Z I.
Lemma F_85b14 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b1c%Z I : word) = Some W_85b14.
Proof. vm_refl. Qed.
Lemma D_85b14 : decode_any W_85b14 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b18 : bv 32 := @BV 32 0x00079517%Z I.
Lemma F_85b18 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b20%Z I : word) = Some W_85b18.
Proof. vm_refl. Qed.
Lemma D_85b18 : decode_any W_85b18 = Some (Auipc (@BV 5 10%Z I) (@BV 20 121%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b1c : bv 32 := @BV 32 0x7a053d03%Z I.
Lemma F_85b1c : fetch_word Asan.M.loaded_segments (@BV 64 0x85b24%Z I : word) = Some W_85b1c.
Proof. vm_refl. Qed.
Lemma D_85b1c : decode_any W_85b1c = Some (Load SZ8 true (@BV 5 26%Z I) (@BV 5 10%Z I) (@BV 12 1952%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b20 : bv 32 := @BV 32 0x0009ba03%Z I.
Lemma F_85b20 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b28%Z I : word) = Some W_85b20.
Proof. vm_refl. Qed.
Lemma D_85b20 : decode_any W_85b20 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b24 : bv 32 := @BV 32 0x0007a517%Z I.
Lemma F_85b24 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b2c%Z I : word) = Some W_85b24.
Proof. vm_refl. Qed.
Lemma D_85b24 : decode_any W_85b24 = Some (Auipc (@BV 5 10%Z I) (@BV 20 122%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b28 : bv 32 := @BV 32 0x000d2583%Z I.
Lemma F_85b28 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b30%Z I : word) = Some W_85b28.
Proof. vm_refl. Qed.
Lemma D_85b28 : decode_any W_85b28 = Some (Load SZ4 true (@BV 5 11%Z I) (@BV 5 26%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b2c : bv 32 := @BV 32 0x4f453a83%Z I.
Lemma F_85b2c : fetch_word Asan.M.loaded_segments (@BV 64 0x85b34%Z I : word) = Some W_85b2c.
Proof. vm_refl. Qed.
Lemma D_85b2c : decode_any W_85b2c = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 10%Z I) (@BV 12 1268%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b30 : bv 32 := @BV 32 0x00300513%Z I.
Lemma F_85b30 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b38%Z I : word) = Some W_85b30.
Proof. vm_refl. Qed.
Lemma D_85b30 : decode_any W_85b30 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b34 : bv 32 := @BV 32 0x004a8ab3%Z I.
Lemma F_85b34 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b3c%Z I : word) = Some W_85b34.
Proof. vm_refl. Qed.
Lemma D_85b34 : decode_any W_85b34 = Some (Op ALU_ADD (@BV 5 21%Z I) (@BV 5 21%Z I) (@BV 5 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b38 : bv 32 := @BV 32 0x1ea5fa63%Z I.
Lemma F_85b38 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b40%Z I : word) = Some W_85b38.
Proof. vm_refl. Qed.
Lemma D_85b38 : decode_any W_85b38 = Some (Branch BC_GEU (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 13 500%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b3c : bv 32 := @BV 32 0x000abb03%Z I.
Lemma F_85b3c : fetch_word Asan.M.loaded_segments (@BV 64 0x85b44%Z I : word) = Some W_85b3c.
Proof. vm_refl. Qed.
Lemma D_85b3c : decode_any W_85b3c = Some (Load SZ8 true (@BV 5 22%Z I) (@BV 5 21%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b40 : bv 32 := @BV 32 0xfff00513%Z I.
Lemma F_85b40 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b48%Z I : word) = Some W_85b40.
Proof. vm_refl. Qed.
Lemma D_85b40 : decode_any W_85b40 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b44 : bv 32 := @BV 32 0x0230000f%Z I.
Lemma F_85b44 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b4c%Z I : word) = Some W_85b44.
Proof. vm_refl. Qed.
Lemma D_85b44 : decode_any W_85b44 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b48 : bv 32 := @BV 32 0x14ab0e63%Z I.
Lemma F_85b48 : fetch_word Asan.M.loaded_segments (@BV 64 0x85b50%Z I : word) = Some W_85b48.
Proof. vm_refl. Qed.
Lemma D_85b48 : decode_any W_85b48 = Some (Branch BC_EQ (@BV 5 22%Z I) (@BV 5 10%Z I) (@BV 13 348%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b4c : bv 32 := @BV 32 0x080b1263%Z I.
Lemma F_85b4c : fetch_word Asan.M.loaded_segments (@BV 64 0x85b54%Z I : word) = Some W_85b4c.
Proof. vm_refl. Qed.
Lemma D_85b4c : decode_any W_85b4c = Some (Branch BC_NE (@BV 5 22%Z I) (@BV 5 0%Z I) (@BV 13 132%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85b50 : bv 32 := @BV 32 0x00060c13%Z I.



(* [comment removed for export] *)
Definition W_85b54 : bv 32 := @BV 32 0x00068493%Z I.



(* [comment removed for export] *)
Definition W_85b58 : bv 32 := @BV 32 0xfff8e517%Z I.



(* [comment removed for export] *)
Definition W_85b5c : bv 32 := @BV 32 0x00001bb7%Z I.






(* [comment removed for export] *)
Definition W_85b64 : bv 32 := @BV 32 0xff8b8b9b%Z I.



(* [comment removed for export] *)
Definition W_85b68 : bv 32 := @BV 32 0x000b8513%Z I.



(* [comment removed for export] *)
Definition W_85b6c : bv 32 := @BV 32 0x00000613%Z I.



(* [comment removed for export] *)
Definition W_85b70 : bv 32 := @BV 32 0xa90fc0ef%Z I.



(* [comment removed for export] *)
Definition W_85b74 : bv 32 := @BV 32 0x00050b13%Z I.



(* [comment removed for export] *)
Definition W_85b78 : bv 32 := @BV 32 0x160ab42f%Z I.



(* [comment removed for export] *)
Definition W_85b7c : bv 32 := @BV 32 0x02041c63%Z I.



(* [comment removed for export] *)
Definition W_85b80 : bv 32 := @BV 32 0x1b6ab52f%Z I.



(* [comment removed for export] *)
Definition W_85b84 : bv 32 := @BV 32 0xfe051ae3%Z I.









(* [comment removed for export] *)
Definition W_85b90 : bv 32 := @BV 32 0x00100593%Z I.



(* [comment removed for export] *)
Definition W_85b94 : bv 32 := @BV 32 0x00b5362f%Z I.



(* [comment removed for export] *)
Definition W_85b98 : bv 32 := @BV 32 0x000d2503%Z I.



(* [comment removed for export] *)
Definition W_85b9c : bv 32 := @BV 32 0x02a5f663%Z I.



(* [comment removed for export] *)
Definition W_85ba0 : bv 32 := @BV 32 0xfff8e517%Z I.






(* [comment removed for export] *)
Definition W_85ba8 : bv 32 := @BV 32 0x000a8593%Z I.



(* [comment removed for export] *)
Definition W_85bac : bv 32 := @BV 32 0xfacfd0ef%Z I.



(* [comment removed for export] *)
Definition W_85bb0 : bv 32 := @BV 32 0x0180006f%Z I.



(* [comment removed for export] *)
Definition W_85bb4 : bv 32 := @BV 32 0x000b0513%Z I.



(* [comment removed for export] *)
Definition W_85bb8 : bv 32 := @BV 32 0x000b8593%Z I.



(* [comment removed for export] *)
Definition W_85bbc : bv 32 := @BV 32 0x00000613%Z I.



(* [comment removed for export] *)
Definition W_85bc0 : bv 32 := @BV 32 0xbc0fc0ef%Z I.



(* [comment removed for export] *)
Definition W_85bc4 : bv 32 := @BV 32 0x00040b13%Z I.



(* [comment removed for export] *)
Definition W_85bc8 : bv 32 := @BV 32 0x00048693%Z I.



(* [comment removed for export] *)
Definition W_85bcc : bv 32 := @BV 32 0x000c0613%Z I.



(* [comment removed for export] *)
Definition W_85bd0 : bv 32 := @BV 32 0x0c0b0a63%Z I.
Lemma F_85bd0 : fetch_word Asan.M.loaded_segments (@BV 64 0x85bd8%Z I : word) = Some W_85bd0.
Proof. vm_refl. Qed.
Lemma D_85bd0 : decode_any W_85bd0 = Some (Branch BC_EQ (@BV 5 22%Z I) (@BV 5 0%Z I) (@BV 13 212%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85bd4 : bv 32 := @BV 32 0x00c13823%Z I.
Lemma F_85bd4 : fetch_word Asan.M.loaded_segments (@BV 64 0x85bdc%Z I : word) = Some W_85bd4.
Proof. vm_refl. Qed.
Lemma D_85bd4 : decode_any W_85bd4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 12%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85bd8 : bv 32 := @BV 32 0x00d13c23%Z I.
Lemma F_85bd8 : fetch_word Asan.M.loaded_segments (@BV 64 0x85be0%Z I : word) = Some W_85bd8.
Proof. vm_refl. Qed.
Lemma D_85bd8 : decode_any W_85bd8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 13%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85bdc : bv 32 := @BV 32 0x0ff00513%Z I.
Lemma F_85bdc : fetch_word Asan.M.loaded_segments (@BV 64 0x85be4%Z I : word) = Some W_85bdc.
Proof. vm_refl. Qed.
Lemma D_85bdc : decode_any W_85bdc = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 255%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85be0 : bv 32 := @BV 32 0x0aaa6863%Z I.
Lemma F_85be0 : fetch_word Asan.M.loaded_segments (@BV 64 0x85be8%Z I : word) = Some W_85be0.
Proof. vm_refl. Qed.
Lemma D_85be0 : decode_any W_85be0 = Some (Branch BC_LTU (@BV 5 20%Z I) (@BV 5 10%Z I) (@BV 13 176%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85be4 : bv 32 := @BV 32 0xfff00d93%Z I.



(* [comment removed for export] *)
Definition W_85be8 : bv 32 := @BV 32 0x0fe00c93%Z I.



(* [comment removed for export] *)
Definition W_85bec : bv 32 := @BV 32 0xfff8e517%Z I.



(* [comment removed for export] *)
Definition W_85bf0 : bv 32 := @BV 32 0x00001c37%Z I.






(* [comment removed for export] *)
Definition W_85bf8 : bv 32 := @BV 32 0xfff8e617%Z I.






(* [comment removed for export] *)
Definition W_85c00 : bv 32 := @BV 32 0xff8c0c1b%Z I.









(* [comment removed for export] *)
Definition W_85c0c : bv 32 := @BV 32 0x00a13423%Z I.



(* [comment removed for export] *)
Definition W_85c10 : bv 32 := @BV 32 0x0140006f%Z I.



(* [comment removed for export] *)
Definition W_85c14 : bv 32 := @BV 32 0x00000513%Z I.



(* [comment removed for export] *)
Definition W_85c18 : bv 32 := @BV 32 0xf01a0a13%Z I.



(* [comment removed for export] *)
Definition W_85c1c : bv 32 := @BV 32 0x00050b13%Z I.



(* [comment removed for export] *)
Definition W_85c20 : bv 32 := @BV 32 0x074cfa63%Z I.



(* [comment removed for export] *)
Definition W_85c24 : bv 32 := @BV 32 0x000b3503%Z I.



(* [comment removed for export] *)
Definition W_85c28 : bv 32 := @BV 32 0x0230000f%Z I.



(* [comment removed for export] *)
Definition W_85c2c : bv 32 := @BV 32 0xffb504e3%Z I.



(* [comment removed for export] *)
Definition W_85c30 : bv 32 := @BV 32 0xfe0514e3%Z I.



(* [comment removed for export] *)
Definition W_85c34 : bv 32 := @BV 32 0x000c0513%Z I.



(* [comment removed for export] *)
Definition W_85c38 : bv 32 := @BV 32 0x000b8593%Z I.



(* [comment removed for export] *)
Definition W_85c3c : bv 32 := @BV 32 0x00000613%Z I.



(* [comment removed for export] *)
Definition W_85c40 : bv 32 := @BV 32 0x9c0fc0ef%Z I.



(* [comment removed for export] *)
Definition W_85c44 : bv 32 := @BV 32 0x160b34af%Z I.



(* [comment removed for export] *)
Definition W_85c48 : bv 32 := @BV 32 0x02049a63%Z I.



(* [comment removed for export] *)
Definition W_85c4c : bv 32 := @BV 32 0x1aab35af%Z I.



(* [comment removed for export] *)
Definition W_85c50 : bv 32 := @BV 32 0xfe059ae3%Z I.



(* [comment removed for export] *)
Definition W_85c54 : bv 32 := @BV 32 0x00100593%Z I.



(* [comment removed for export] *)
Definition W_85c58 : bv 32 := @BV 32 0x00b4362f%Z I.



(* [comment removed for export] *)
Definition W_85c5c : bv 32 := @BV 32 0x000d2583%Z I.



(* [comment removed for export] *)
Definition W_85c60 : bv 32 := @BV 32 0x00200693%Z I.



(* [comment removed for export] *)
Definition W_85c64 : bv 32 := @BV 32 0xfad5eae3%Z I.



(* [comment removed for export] *)
Definition W_85c68 : bv 32 := @BV 32 0x00050493%Z I.



(* [comment removed for export] *)
Definition W_85c6c : bv 32 := @BV 32 0x00813503%Z I.



(* [comment removed for export] *)
Definition W_85c70 : bv 32 := @BV 32 0x000a8593%Z I.



(* [comment removed for export] *)
Definition W_85c74 : bv 32 := @BV 32 0xee4fd0ef%Z I.



(* [comment removed for export] *)
Definition W_85c78 : bv 32 := @BV 32 0x0100006f%Z I.



(* [comment removed for export] *)
Definition W_85c7c : bv 32 := @BV 32 0x000c0593%Z I.



(* [comment removed for export] *)
Definition W_85c80 : bv 32 := @BV 32 0x00000613%Z I.



(* [comment removed for export] *)
Definition W_85c84 : bv 32 := @BV 32 0xafcfc0ef%Z I.



(* [comment removed for export] *)
Definition W_85c88 : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_85c8c : bv 32 := @BV 32 0xf8dff06f%Z I.



(* [comment removed for export] *)
Definition W_85c90 : bv 32 := @BV 32 0x000b0513%Z I.
Lemma F_85c90 : fetch_word Asan.M.loaded_segments (@BV 64 0x85c98%Z I : word) = Some W_85c90.
Proof. vm_refl. Qed.
Lemma D_85c90 : decode_any W_85c90 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 22%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85c94 : bv 32 := @BV 32 0x004a1413%Z I.
Lemma F_85c94 : fetch_word Asan.M.loaded_segments (@BV 64 0x85c9c%Z I : word) = Some W_85c94.
Proof. vm_refl. Qed.
Lemma D_85c94 : decode_any W_85c94 = Some (ShiftImm ALU_SLL (@BV 5 8%Z I) (@BV 5 20%Z I) (@BV 6 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85c98 : bv 32 := @BV 32 0x00850433%Z I.
Lemma F_85c98 : fetch_word Asan.M.loaded_segments (@BV 64 0x85ca0%Z I : word) = Some W_85c98.
Proof. vm_refl. Qed.
Lemma D_85c98 : decode_any W_85c98 = Some (Op ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85c9c : bv 32 := @BV 32 0x00843503%Z I.
Lemma F_85c9c : fetch_word Asan.M.loaded_segments (@BV 64 0x85ca4%Z I : word) = Some W_85c9c.
Proof. vm_refl. Qed.
Lemma D_85c9c : decode_any W_85c9c = Some (Load SZ8 true (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85ca0 : bv 32 := @BV 32 0x04050263%Z I.
Lemma F_85ca0 : fetch_word Asan.M.loaded_segments (@BV 64 0x85ca8%Z I : word) = Some W_85ca0.
Proof. vm_refl. Qed.
Lemma D_85ca0 : decode_any W_85ca0 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 68%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85ca4 : bv 32 := @BV 32 0x00000513%Z I.
Lemma F_85ca4 : fetch_word Asan.M.loaded_segments (@BV 64 0x85cac%Z I : word) = Some W_85ca4.
Proof. vm_refl. Qed.
Lemma D_85ca4 : decode_any W_85ca4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85ca8 : bv 32 := @BV 32 0x08813083%Z I.
Lemma F_85ca8 : fetch_word Asan.M.loaded_segments (@BV 64 0x85cb0%Z I : word) = Some W_85ca8.
Proof. vm_refl. Qed.
Lemma D_85ca8 : decode_any W_85ca8 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 136%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85cac : bv 32 := @BV 32 0x08013403%Z I.
Lemma F_85cac : fetch_word Asan.M.loaded_segments (@BV 64 0x85cb4%Z I : word) = Some W_85cac.
Proof. vm_refl. Qed.
Lemma D_85cac : decode_any W_85cac = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85cb0 : bv 32 := @BV 32 0x07813483%Z I.
Lemma F_85cb0 : fetch_word Asan.M.loaded_segments (@BV 64 0x85cb8%Z I : word) = Some W_85cb0.
Proof. vm_refl. Qed.
Lemma D_85cb0 : decode_any W_85cb0 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 120%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85cb4 : bv 32 := @BV 32 0x07013903%Z I.
Lemma F_85cb4 : fetch_word Asan.M.loaded_segments (@BV 64 0x85cbc%Z I : word) = Some W_85cb4.
Proof. vm_refl. Qed.
Lemma D_85cb4 : decode_any W_85cb4 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 112%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85cb8 : bv 32 := @BV 32 0x06813983%Z I.
Lemma F_85cb8 : fetch_word Asan.M.loaded_segments (@BV 64 0x85cc0%Z I : word) = Some W_85cb8.
Proof. vm_refl. Qed.
Lemma D_85cb8 : decode_any W_85cb8 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85cbc : bv 32 := @BV 32 0x06013a03%Z I.
Lemma F_85cbc : fetch_word Asan.M.loaded_segments (@BV 64 0x85cc4%Z I : word) = Some W_85cbc.
Proof. vm_refl. Qed.
Lemma D_85cbc : decode_any W_85cbc = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85cc0 : bv 32 := @BV 32 0x05813a83%Z I.
Lemma F_85cc0 : fetch_word Asan.M.loaded_segments (@BV 64 0x85cc8%Z I : word) = Some W_85cc0.
Proof. vm_refl. Qed.
Lemma D_85cc0 : decode_any W_85cc0 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85cc4 : bv 32 := @BV 32 0x05013b03%Z I.
Lemma F_85cc4 : fetch_word Asan.M.loaded_segments (@BV 64 0x85ccc%Z I : word) = Some W_85cc4.
Proof. vm_refl. Qed.
Lemma D_85cc4 : decode_any W_85cc4 = Some (Load SZ8 true (@BV 5 22%Z I) (@BV 5 2%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85cc8 : bv 32 := @BV 32 0x04813b83%Z I.
Lemma F_85cc8 : fetch_word Asan.M.loaded_segments (@BV 64 0x85cd0%Z I : word) = Some W_85cc8.
Proof. vm_refl. Qed.
Lemma D_85cc8 : decode_any W_85cc8 = Some (Load SZ8 true (@BV 5 23%Z I) (@BV 5 2%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85ccc : bv 32 := @BV 32 0x04013c03%Z I.
Lemma F_85ccc : fetch_word Asan.M.loaded_segments (@BV 64 0x85cd4%Z I : word) = Some W_85ccc.
Proof. vm_refl. Qed.
Lemma D_85ccc : decode_any W_85ccc = Some (Load SZ8 true (@BV 5 24%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85cd0 : bv 32 := @BV 32 0x03813c83%Z I.
Lemma F_85cd0 : fetch_word Asan.M.loaded_segments (@BV 64 0x85cd8%Z I : word) = Some W_85cd0.
Proof. vm_refl. Qed.
Lemma D_85cd0 : decode_any W_85cd0 = Some (Load SZ8 true (@BV 5 25%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85cd4 : bv 32 := @BV 32 0x03013d03%Z I.
Lemma F_85cd4 : fetch_word Asan.M.loaded_segments (@BV 64 0x85cdc%Z I : word) = Some W_85cd4.
Proof. vm_refl. Qed.
Lemma D_85cd4 : decode_any W_85cd4 = Some (Load SZ8 true (@BV 5 26%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85cd8 : bv 32 := @BV 32 0x02813d83%Z I.
Lemma F_85cd8 : fetch_word Asan.M.loaded_segments (@BV 64 0x85ce0%Z I : word) = Some W_85cd8.
Proof. vm_refl. Qed.
Lemma D_85cd8 : decode_any W_85cd8 = Some (Load SZ8 true (@BV 5 27%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85cdc : bv 32 := @BV 32 0x09010113%Z I.
Lemma F_85cdc : fetch_word Asan.M.loaded_segments (@BV 64 0x85ce4%Z I : word) = Some W_85cdc.
Proof. vm_refl. Qed.
Lemma D_85cdc : decode_any W_85cdc = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85ce0 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_85ce0 : fetch_word Asan.M.loaded_segments (@BV 64 0x85ce8%Z I : word) = Some W_85ce0.
Proof. vm_refl. Qed.
Lemma D_85ce0 : decode_any W_85ce0 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88810 : bv 32 := @BV 32 0xff010113%Z I.
Lemma F_88810 : fetch_word Asan.M.loaded_segments (@BV 64 0x88818%Z I : word) = Some W_88810.
Proof. vm_refl. Qed.
Lemma D_88810 : decode_any W_88810 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88814 : bv 32 := @BV 32 0x00113423%Z I.
Lemma F_88814 : fetch_word Asan.M.loaded_segments (@BV 64 0x8881c%Z I : word) = Some W_88814.
Proof. vm_refl. Qed.
Lemma D_88814 : decode_any W_88814 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88818 : bv 32 := @BV 32 0x4f05e0ef%Z I.
Lemma F_88818 : fetch_word Asan.M.loaded_segments (@BV 64 0x88820%Z I : word) = Some W_88818.
Proof. vm_refl. Qed.
Lemma D_88818 : decode_any W_88818 = Some (Jal (@BV 5 1%Z I) (@BV 21 386288%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8881c : bv 32 := @BV 32 0x00c00593%Z I.
Lemma F_8881c : fetch_word Asan.M.loaded_segments (@BV 64 0x88824%Z I : word) = Some W_8881c.
Proof. vm_refl. Qed.
Lemma D_8881c : decode_any W_8881c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88820 : bv 32 := @BV 32 0x00b52023%Z I.
Lemma F_88820 : fetch_word Asan.M.loaded_segments (@BV 64 0x88828%Z I : word) = Some W_88820.
Proof. vm_refl. Qed.
Lemma D_88820 : decode_any W_88820 = Some (Store SZ4 (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88824 : bv 32 := @BV 32 0x00813083%Z I.
Lemma F_88824 : fetch_word Asan.M.loaded_segments (@BV 64 0x8882c%Z I : word) = Some W_88824.
Proof. vm_refl. Qed.
Lemma D_88824 : decode_any W_88824 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88828 : bv 32 := @BV 32 0x01010113%Z I.
Lemma F_88828 : fetch_word Asan.M.loaded_segments (@BV 64 0x88830%Z I : word) = Some W_88828.
Proof. vm_refl. Qed.
Lemma D_88828 : decode_any W_88828 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8882c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8882c : fetch_word Asan.M.loaded_segments (@BV 64 0x88834%Z I : word) = Some W_8882c.
Proof. vm_refl. Qed.
Lemma D_8882c : decode_any W_8882c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b30 : bv 32 := @BV 32 0xfe010113%Z I.
Lemma F_89b30 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b38%Z I : word) = Some W_89b30.
Proof. vm_refl. Qed.
Lemma D_89b30 : decode_any W_89b30 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b34 : bv 32 := @BV 32 0x00113c23%Z I.
Lemma F_89b34 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b3c%Z I : word) = Some W_89b34.
Proof. vm_refl. Qed.
Lemma D_89b34 : decode_any W_89b34 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b38 : bv 32 := @BV 32 0x00813823%Z I.
Lemma F_89b38 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b40%Z I : word) = Some W_89b38.
Proof. vm_refl. Qed.
Lemma D_89b38 : decode_any W_89b38 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b3c : bv 32 := @BV 32 0x00913423%Z I.
Lemma F_89b3c : fetch_word Asan.M.loaded_segments (@BV 64 0x89b44%Z I : word) = Some W_89b3c.
Proof. vm_refl. Qed.
Lemma D_89b3c : decode_any W_89b3c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b40 : bv 32 := @BV 32 0x01213023%Z I.
Lemma F_89b40 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b48%Z I : word) = Some W_89b40.
Proof. vm_refl. Qed.
Lemma D_89b40 : decode_any W_89b40 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b44 : bv 32 := @BV 32 0x00058413%Z I.
Lemma F_89b44 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b4c%Z I : word) = Some W_89b44.
Proof. vm_refl. Qed.
Lemma D_89b44 : decode_any W_89b44 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b48 : bv 32 := @BV 32 0x00075597%Z I.
Lemma F_89b48 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b50%Z I : word) = Some W_89b48.
Proof. vm_refl. Qed.
Lemma D_89b48 : decode_any W_89b48 = Some (Auipc (@BV 5 11%Z I) (@BV 20 117%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b4c : bv 32 := @BV 32 0x7005b903%Z I.
Lemma F_89b4c : fetch_word Asan.M.loaded_segments (@BV 64 0x89b54%Z I : word) = Some W_89b4c.
Proof. vm_refl. Qed.
Lemma D_89b4c : decode_any W_89b4c = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 11%Z I) (@BV 12 1792%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b50 : bv 32 := @BV 32 0x00093583%Z I.
Lemma F_89b50 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b58%Z I : word) = Some W_89b50.
Proof. vm_refl. Qed.
Lemma D_89b50 : decode_any W_89b50 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b54 : bv 32 := @BV 32 0x00050493%Z I.
Lemma F_89b54 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b5c%Z I : word) = Some W_89b54.
Proof. vm_refl. Qed.
Lemma D_89b54 : decode_any W_89b54 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b58 : bv 32 := @BV 32 0x00059863%Z I.
Lemma F_89b58 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b60%Z I : word) = Some W_89b58.
Proof. vm_refl. Qed.
Lemma D_89b58 : decode_any W_89b58 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b5c : bv 32 := @BV 32 0xb01f70ef%Z I.



(* [comment removed for export] *)
Definition W_89b60 : bv 32 := @BV 32 0x00050593%Z I.



(* [comment removed for export] *)
Definition W_89b64 : bv 32 := @BV 32 0x00a93023%Z I.



(* [comment removed for export] *)
Definition W_89b68 : bv 32 := @BV 32 0xfff58513%Z I.
Lemma F_89b68 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b70%Z I : word) = Some W_89b68.
Proof. vm_refl. Qed.
Lemma D_89b68 : decode_any W_89b68 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b6c : bv 32 := @BV 32 0x00a5f533%Z I.
Lemma F_89b6c : fetch_word Asan.M.loaded_segments (@BV 64 0x89b74%Z I : word) = Some W_89b6c.
Proof. vm_refl. Qed.
Lemma D_89b6c : decode_any W_89b6c = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b70 : bv 32 := @BV 32 0x04051a63%Z I.
Lemma F_89b70 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b78%Z I : word) = Some W_89b70.
Proof. vm_refl. Qed.
Lemma D_89b70 : decode_any W_89b70 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 84%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b74 : bv 32 := @BV 32 0x00b484b3%Z I.
Lemma F_89b74 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b7c%Z I : word) = Some W_89b74.
Proof. vm_refl. Qed.
Lemma D_89b74 : decode_any W_89b74 = Some (Op ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b78 : bv 32 := @BV 32 0x40b005b3%Z I.
Lemma F_89b78 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b80%Z I : word) = Some W_89b78.
Proof. vm_refl. Qed.
Lemma D_89b78 : decode_any W_89b78 = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b7c : bv 32 := @BV 32 0xfff48513%Z I.
Lemma F_89b7c : fetch_word Asan.M.loaded_segments (@BV 64 0x89b84%Z I : word) = Some W_89b7c.
Proof. vm_refl. Qed.
Lemma D_89b7c : decode_any W_89b7c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b80 : bv 32 := @BV 32 0x00b57533%Z I.
Lemma F_89b80 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b88%Z I : word) = Some W_89b80.
Proof. vm_refl. Qed.
Lemma D_89b80 : decode_any W_89b80 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b84 : bv 32 := @BV 32 0x00b475b3%Z I.
Lemma F_89b84 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b8c%Z I : word) = Some W_89b84.
Proof. vm_refl. Qed.
Lemma D_89b84 : decode_any W_89b84 = Some (Op ALU_AND (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b88 : bv 32 := @BV 32 0x02b57263%Z I.
Lemma F_89b88 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b90%Z I : word) = Some W_89b88.
Proof. vm_refl. Qed.
Lemma D_89b88 : decode_any W_89b88 = Some (Branch BC_GEU (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 13 36%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b8c : bv 32 := @BV 32 0x40a585b3%Z I.
Lemma F_89b8c : fetch_word Asan.M.loaded_segments (@BV 64 0x89b94%Z I : word) = Some W_89b8c.
Proof. vm_refl. Qed.
Lemma D_89b8c : decode_any W_89b8c = Some (Op ALU_SUB (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b90 : bv 32 := @BV 32 0x00400613%Z I.
Lemma F_89b90 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b98%Z I : word) = Some W_89b90.
Proof. vm_refl. Qed.
Lemma D_89b90 : decode_any W_89b90 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b94 : bv 32 := @BV 32 0x01813083%Z I.
Lemma F_89b94 : fetch_word Asan.M.loaded_segments (@BV 64 0x89b9c%Z I : word) = Some W_89b94.
Proof. vm_refl. Qed.
Lemma D_89b94 : decode_any W_89b94 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b98 : bv 32 := @BV 32 0x01013403%Z I.
Lemma F_89b98 : fetch_word Asan.M.loaded_segments (@BV 64 0x89ba0%Z I : word) = Some W_89b98.
Proof. vm_refl. Qed.
Lemma D_89b98 : decode_any W_89b98 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89b9c : bv 32 := @BV 32 0x00813483%Z I.
Lemma F_89b9c : fetch_word Asan.M.loaded_segments (@BV 64 0x89ba4%Z I : word) = Some W_89b9c.
Proof. vm_refl. Qed.
Lemma D_89b9c : decode_any W_89b9c = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89ba0 : bv 32 := @BV 32 0x00013903%Z I.
Lemma F_89ba0 : fetch_word Asan.M.loaded_segments (@BV 64 0x89ba8%Z I : word) = Some W_89ba0.
Proof. vm_refl. Qed.
Lemma D_89ba0 : decode_any W_89ba0 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89ba4 : bv 32 := @BV 32 0x02010113%Z I.
Lemma F_89ba4 : fetch_word Asan.M.loaded_segments (@BV 64 0x89bac%Z I : word) = Some W_89ba4.
Proof. vm_refl. Qed.
Lemma D_89ba4 : decode_any W_89ba4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89ba8 : bv 32 := @BV 32 0xbb1f606f%Z I.
Lemma F_89ba8 : fetch_word Asan.M.loaded_segments (@BV 64 0x89bb0%Z I : word) = Some W_89ba8.
Proof. vm_refl. Qed.
Lemma D_89ba8 : decode_any W_89ba8 = Some (Jal (@BV 5 0%Z I) (@BV 21 2059184%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89bac : bv 32 := @BV 32 0x01813083%Z I.
Lemma F_89bac : fetch_word Asan.M.loaded_segments (@BV 64 0x89bb4%Z I : word) = Some W_89bac.
Proof. vm_refl. Qed.
Lemma D_89bac : decode_any W_89bac = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89bb0 : bv 32 := @BV 32 0x01013403%Z I.
Lemma F_89bb0 : fetch_word Asan.M.loaded_segments (@BV 64 0x89bb8%Z I : word) = Some W_89bb0.
Proof. vm_refl. Qed.
Lemma D_89bb0 : decode_any W_89bb0 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89bb4 : bv 32 := @BV 32 0x00813483%Z I.
Lemma F_89bb4 : fetch_word Asan.M.loaded_segments (@BV 64 0x89bbc%Z I : word) = Some W_89bb4.
Proof. vm_refl. Qed.
Lemma D_89bb4 : decode_any W_89bb4 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89bb8 : bv 32 := @BV 32 0x00013903%Z I.
Lemma F_89bb8 : fetch_word Asan.M.loaded_segments (@BV 64 0x89bc0%Z I : word) = Some W_89bb8.
Proof. vm_refl. Qed.
Lemma D_89bb8 : decode_any W_89bb8 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89bbc : bv 32 := @BV 32 0x02010113%Z I.
Lemma F_89bbc : fetch_word Asan.M.loaded_segments (@BV 64 0x89bc4%Z I : word) = Some W_89bbc.
Proof. vm_refl. Qed.
Lemma D_89bbc : decode_any W_89bbc = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89bc0 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_89bc0 : fetch_word Asan.M.loaded_segments (@BV 64 0x89bc8%Z I : word) = Some W_89bc0.
Proof. vm_refl. Qed.
Lemma D_89bc0 : decode_any W_89bc0 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a5c0 : bv 32 := @BV 32 0x94df70ef%Z I.
Lemma F_8a5c0 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a5c8%Z I : word) = Some W_8a5c0.
Proof. vm_refl. Qed.
Lemma D_8a5c0 : decode_any W_8a5c0 = Some (Jal (@BV 5 1%Z I) (@BV 21 2062668%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a5c4 : bv 32 := @BV 32 0x00a4b023%Z I.
Lemma F_8a5c4 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a5cc%Z I : word) = Some W_8a5c4.
Proof. vm_refl. Qed.
Lemma D_8a5c4 : decode_any W_8a5c4 = Some (Store SZ8 (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a680 : bv 32 := @BV 32 0xfe010113%Z I.
Lemma F_8a680 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a688%Z I : word) = Some W_8a680.
Proof. vm_refl. Qed.
Lemma D_8a680 : decode_any W_8a680 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a684 : bv 32 := @BV 32 0x00113c23%Z I.
Lemma F_8a684 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a68c%Z I : word) = Some W_8a684.
Proof. vm_refl. Qed.
Lemma D_8a684 : decode_any W_8a684 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a688 : bv 32 := @BV 32 0x00813823%Z I.
Lemma F_8a688 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a690%Z I : word) = Some W_8a688.
Proof. vm_refl. Qed.
Lemma D_8a688 : decode_any W_8a688 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a68c : bv 32 := @BV 32 0x00913423%Z I.
Lemma F_8a68c : fetch_word Asan.M.loaded_segments (@BV 64 0x8a694%Z I : word) = Some W_8a68c.
Proof. vm_refl. Qed.
Lemma D_8a68c : decode_any W_8a68c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a690 : bv 32 := @BV 32 0x01213023%Z I.
Lemma F_8a690 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a698%Z I : word) = Some W_8a690.
Proof. vm_refl. Qed.
Lemma D_8a690 : decode_any W_8a690 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a694 : bv 32 := @BV 32 0x00060413%Z I.
Lemma F_8a694 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a69c%Z I : word) = Some W_8a694.
Proof. vm_refl. Qed.
Lemma D_8a694 : decode_any W_8a694 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a698 : bv 32 := @BV 32 0x00058493%Z I.
Lemma F_8a698 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a6a0%Z I : word) = Some W_8a698.
Proof. vm_refl. Qed.
Lemma D_8a698 : decode_any W_8a698 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a69c : bv 32 := @BV 32 0x00058513%Z I.
Lemma F_8a69c : fetch_word Asan.M.loaded_segments (@BV 64 0x8a6a4%Z I : word) = Some W_8a69c.
Proof. vm_refl. Qed.
Lemma D_8a69c : decode_any W_8a69c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a6a0 : bv 32 := @BV 32 0x00060593%Z I.
Lemma F_8a6a0 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a6a8%Z I : word) = Some W_8a6a0.
Proof. vm_refl. Qed.
Lemma D_8a6a0 : decode_any W_8a6a0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a6a4 : bv 32 := @BV 32 0x00068613%Z I.
Lemma F_8a6a4 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a6ac%Z I : word) = Some W_8a6a4.
Proof. vm_refl. Qed.
Lemma D_8a6a4 : decode_any W_8a6a4 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a6a8 : bv 32 := @BV 32 0xf19f70ef%Z I.
Lemma F_8a6a8 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a6b0%Z I : word) = Some W_8a6a8.
Proof. vm_refl. Qed.
Lemma D_8a6a8 : decode_any W_8a6a8 = Some (Jal (@BV 5 1%Z I) (@BV 21 2064152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a6ac : bv 32 := @BV 32 0x00050e63%Z I.
Lemma F_8a6ac : fetch_word Asan.M.loaded_segments (@BV 64 0x8a6b4%Z I : word) = Some W_8a6ac.
Proof. vm_refl. Qed.
Lemma D_8a6ac : decode_any W_8a6ac = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 28%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a6b0 : bv 32 := @BV 32 0x01813083%Z I.
Lemma F_8a6b0 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a6b8%Z I : word) = Some W_8a6b0.
Proof. vm_refl. Qed.
Lemma D_8a6b0 : decode_any W_8a6b0 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a6b4 : bv 32 := @BV 32 0x01013403%Z I.
Lemma F_8a6b4 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a6bc%Z I : word) = Some W_8a6b4.
Proof. vm_refl. Qed.
Lemma D_8a6b4 : decode_any W_8a6b4 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a6b8 : bv 32 := @BV 32 0x00813483%Z I.
Lemma F_8a6b8 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a6c0%Z I : word) = Some W_8a6b8.
Proof. vm_refl. Qed.
Lemma D_8a6b8 : decode_any W_8a6b8 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a6bc : bv 32 := @BV 32 0x00013903%Z I.
Lemma F_8a6bc : fetch_word Asan.M.loaded_segments (@BV 64 0x8a6c4%Z I : word) = Some W_8a6bc.
Proof. vm_refl. Qed.
Lemma D_8a6bc : decode_any W_8a6bc = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a6c0 : bv 32 := @BV 32 0x02010113%Z I.
Lemma F_8a6c0 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a6c8%Z I : word) = Some W_8a6c0.
Proof. vm_refl. Qed.
Lemma D_8a6c0 : decode_any W_8a6c0 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a6c4 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_8a6c4 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a6cc%Z I : word) = Some W_8a6c4.
Proof. vm_refl. Qed.
Lemma D_8a6c4 : decode_any W_8a6c4 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a7cc : bv 32 := @BV 32 0x00058513%Z I.
Lemma F_8a7cc : fetch_word Asan.M.loaded_segments (@BV 64 0x8a7d4%Z I : word) = Some W_8a7cc.
Proof. vm_refl. Qed.
Lemma D_8a7cc : decode_any W_8a7cc = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a7d0 : bv 32 := @BV 32 0x00060593%Z I.
Lemma F_8a7d0 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a7d8%Z I : word) = Some W_8a7d0.
Proof. vm_refl. Qed.
Lemma D_8a7d0 : decode_any W_8a7d0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a7d4 : bv 32 := @BV 32 0x00068613%Z I.
Lemma F_8a7d4 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a7dc%Z I : word) = Some W_8a7d4.
Proof. vm_refl. Qed.
Lemma D_8a7d4 : decode_any W_8a7d4 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a7d8 : bv 32 := @BV 32 0xc65f706f%Z I.
Lemma F_8a7d8 : fetch_word Asan.M.loaded_segments (@BV 64 0x8a7e0%Z I : word) = Some W_8a7d8.
Proof. vm_refl. Qed.
Lemma D_8a7d8 : decode_any W_8a7d8 = Some (Jal (@BV 5 0%Z I) (@BV 21 2063460%Z I), 4%Z).
Proof. vm_refl. Qed.
