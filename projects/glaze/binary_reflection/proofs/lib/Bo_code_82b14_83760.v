(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
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
Definition W_82b14 : bv 32 := @BV 32 0x00810593%Z I.
Lemma F_82b14 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b14%Z I : word) = Some W_82b14.
Proof. vm_refl. Qed.
Lemma D_82b14 : decode_any W_82b14 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b18 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_82b18 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b18%Z I : word) = Some W_82b18.
Proof. vm_refl. Qed.
Lemma D_82b18 : decode_any W_82b18 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b1c : bv 32 := @BV 32 0xe6cfe0ef%Z I.
Lemma F_82b1c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b1c%Z I : word) = Some W_82b1c.
Proof. vm_refl. Qed.
Lemma D_82b1c : decode_any W_82b1c = Some (Jal (@BV 5 1%Z I) (@BV 21 2090604%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b20 : bv 32 := @BV 32 0x02051c63%Z I.
Lemma F_82b20 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b20%Z I : word) = Some W_82b20.
Proof. vm_refl. Qed.
Lemma D_82b20 : decode_any W_82b20 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b24 : bv 32 := @BV 32 0x00048513%Z I.
Lemma F_82b24 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b24%Z I : word) = Some W_82b24.
Proof. vm_refl. Qed.
Lemma D_82b24 : decode_any W_82b24 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b28 : bv 32 := @BV 32 0xd64fa0ef%Z I.
Lemma F_82b28 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b28%Z I : word) = Some W_82b28.
Proof. vm_refl. Qed.
Lemma D_82b28 : decode_any W_82b28 = Some (Jal (@BV 5 1%Z I) (@BV 21 2073956%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b2c : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_82b2c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b2c%Z I : word) = Some W_82b2c.
Proof. vm_refl. Qed.
Lemma D_82b2c : decode_any W_82b2c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b30 : bv 32 := @BV 32 0x02813083%Z I.
Lemma F_82b30 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b30%Z I : word) = Some W_82b30.
Proof. vm_refl. Qed.
Lemma D_82b30 : decode_any W_82b30 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b34 : bv 32 := @BV 32 0x02013403%Z I.
Lemma F_82b34 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b34%Z I : word) = Some W_82b34.
Proof. vm_refl. Qed.
Lemma D_82b34 : decode_any W_82b34 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b38 : bv 32 := @BV 32 0x01813483%Z I.
Lemma F_82b38 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b38%Z I : word) = Some W_82b38.
Proof. vm_refl. Qed.
Lemma D_82b38 : decode_any W_82b38 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b3c : bv 32 := @BV 32 0x01013903%Z I.
Lemma F_82b3c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b3c%Z I : word) = Some W_82b3c.
Proof. vm_refl. Qed.
Lemma D_82b3c : decode_any W_82b3c = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b40 : bv 32 := @BV 32 0x03010113%Z I.
Lemma F_82b40 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b40%Z I : word) = Some W_82b40.
Proof. vm_refl. Qed.
Lemma D_82b40 : decode_any W_82b40 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b44 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_82b44 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b44%Z I : word) = Some W_82b44.
Proof. vm_refl. Qed.
Lemma D_82b44 : decode_any W_82b44 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b58 : bv 32 := @BV 32 0x00812683%Z I.
Lemma F_82b58 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b58%Z I : word) = Some W_82b58.
Proof. vm_refl. Qed.
Lemma D_82b58 : decode_any W_82b58 = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b5c : bv 32 := @BV 32 0x00c00513%Z I.
Lemma F_82b5c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b5c%Z I : word) = Some W_82b5c.
Proof. vm_refl. Qed.
Lemma D_82b5c : decode_any W_82b5c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b60 : bv 32 := @BV 32 0x00a69663%Z I.
Lemma F_82b60 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b60%Z I : word) = Some W_82b60.
Proof. vm_refl. Qed.
Lemma D_82b60 : decode_any W_82b60 = Some (Branch BC_NE (@BV 5 13%Z I) (@BV 5 10%Z I) (@BV 13 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b64 : bv 32 := @BV 32 0x00000913%Z I.
Lemma F_82b64 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b64%Z I : word) = Some W_82b64.
Proof. vm_refl. Qed.
Lemma D_82b64 : decode_any W_82b64 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b68 : bv 32 := @BV 32 0xfc5ff06f%Z I.
Lemma F_82b68 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b68%Z I : word) = Some W_82b68.
Proof. vm_refl. Qed.
Lemma D_82b68 : decode_any W_82b68 = Some (Jal (@BV 5 0%Z I) (@BV 21 2097092%Z I), 4%Z).
Proof. vm_refl. Qed.































(* [comment removed for export] *)
Definition W_82db0 : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_82db0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82db0%Z I : word) = Some W_82db0.
Proof. vm_refl. Qed.
Lemma D_82db0 : decode_any W_82db0 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82db4 : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_82db4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82db4%Z I : word) = Some W_82db4.
Proof. vm_refl. Qed.
Lemma D_82db4 : decode_any W_82db4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82db8 : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_82db8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82db8%Z I : word) = Some W_82db8.
Proof. vm_refl. Qed.
Lemma D_82db8 : decode_any W_82db8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dbc : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_82dbc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82dbc%Z I : word) = Some W_82dbc.
Proof. vm_refl. Qed.
Lemma D_82dbc : decode_any W_82dbc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dc0 : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_82dc0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82dc0%Z I : word) = Some W_82dc0.
Proof. vm_refl. Qed.
Lemma D_82dc0 : decode_any W_82dc0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dc4 : bv 32 := @BV 32 0x00058413%Z I.
Lemma F_82dc4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82dc4%Z I : word) = Some W_82dc4.
Proof. vm_refl. Qed.
Lemma D_82dc4 : decode_any W_82dc4 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dc8 : bv 32 := @BV 32 0x00083597%Z I.
Lemma F_82dc8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82dc8%Z I : word) = Some W_82dc8.
Proof. vm_refl. Qed.
Lemma D_82dc8 : decode_any W_82dc8 = Some (Auipc (@BV 5 11%Z I) (@BV 20 131%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dcc : bv 32 := @BV 32 0x1305b903%Z I.
Lemma F_82dcc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82dcc%Z I : word) = Some W_82dcc.
Proof. vm_refl. Qed.
Lemma D_82dcc : decode_any W_82dcc = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 11%Z I) (@BV 12 304%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dd0 : bv 32 := @BV 32 0x00093583%Z I.
Lemma F_82dd0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82dd0%Z I : word) = Some W_82dd0.
Proof. vm_refl. Qed.
Lemma D_82dd0 : decode_any W_82dd0 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dd4 : bv 32 := @BV 32 0x00050493%Z I.
Lemma F_82dd4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82dd4%Z I : word) = Some W_82dd4.
Proof. vm_refl. Qed.
Lemma D_82dd4 : decode_any W_82dd4 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dd8 : bv 32 := @BV 32 0x00059863%Z I.
Lemma F_82dd8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82dd8%Z I : word) = Some W_82dd8.
Proof. vm_refl. Qed.
Lemma D_82dd8 : decode_any W_82dd8 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82de8 : bv 32 := @BV 32 0xfff58513%Z I.
Lemma F_82de8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82de8%Z I : word) = Some W_82de8.
Proof. vm_refl. Qed.
Lemma D_82de8 : decode_any W_82de8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dec : bv 32 := @BV 32 0x00a5f533%Z I.
Lemma F_82dec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82dec%Z I : word) = Some W_82dec.
Proof. vm_refl. Qed.
Lemma D_82dec : decode_any W_82dec = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82df0 : bv 32 := @BV 32 0x08051c63%Z I.
Lemma F_82df0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82df0%Z I : word) = Some W_82df0.
Proof. vm_refl. Qed.
Lemma D_82df0 : decode_any W_82df0 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82df4 : bv 32 := @BV 32 0x00b484b3%Z I.
Lemma F_82df4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82df4%Z I : word) = Some W_82df4.
Proof. vm_refl. Qed.
Lemma D_82df4 : decode_any W_82df4 = Some (Op ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82df8 : bv 32 := @BV 32 0x40b00533%Z I.
Lemma F_82df8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82df8%Z I : word) = Some W_82df8.
Proof. vm_refl. Qed.
Lemma D_82df8 : decode_any W_82df8 = Some (Op ALU_SUB (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dfc : bv 32 := @BV 32 0xfff48493%Z I.
Lemma F_82dfc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82dfc%Z I : word) = Some W_82dfc.
Proof. vm_refl. Qed.
Lemma D_82dfc : decode_any W_82dfc = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e00 : bv 32 := @BV 32 0x00a4f4b3%Z I.
Lemma F_82e00 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e00%Z I : word) = Some W_82e00.
Proof. vm_refl. Qed.
Lemma D_82e00 : decode_any W_82e00 = Some (Op ALU_AND (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e04 : bv 32 := @BV 32 0x00004537%Z I.
Lemma F_82e04 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e04%Z I : word) = Some W_82e04.
Proof. vm_refl. Qed.
Lemma D_82e04 : decode_any W_82e04 = Some (Lui (@BV 5 10%Z I) (@BV 20 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e08 : bv 32 := @BV 32 0x02250513%Z I.
Lemma F_82e08 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e08%Z I : word) = Some W_82e08.
Proof. vm_refl. Qed.
Lemma D_82e08 : decode_any W_82e08 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 34%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e0c : bv 32 := @BV 32 0x00a12623%Z I.
Lemma F_82e0c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e0c%Z I : word) = Some W_82e0c.
Proof. vm_refl. Qed.
Lemma D_82e0c : decode_any W_82e0c = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e10 : bv 32 := @BV 32 0x00c10613%Z I.
Lemma F_82e10 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e10%Z I : word) = Some W_82e10.
Proof. vm_refl. Qed.
Lemma D_82e10 : decode_any W_82e10 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e14 : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_82e14 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e14%Z I : word) = Some W_82e14.
Proof. vm_refl. Qed.
Lemma D_82e14 : decode_any W_82e14 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e18 : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_82e18 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e18%Z I : word) = Some W_82e18.
Proof. vm_refl. Qed.
Lemma D_82e18 : decode_any W_82e18 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e1c : bv 32 := @BV 32 0x738000ef%Z I.
Lemma F_82e1c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e1c%Z I : word) = Some W_82e1c.
Proof. vm_refl. Qed.
Lemma D_82e1c : decode_any W_82e1c = Some (Jal (@BV 5 1%Z I) (@BV 21 1848%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e20 : bv 32 := @BV 32 0x00c12683%Z I.
Lemma F_82e20 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e20%Z I : word) = Some W_82e20.
Proof. vm_refl. Qed.
Lemma D_82e20 : decode_any W_82e20 = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e24 : bv 32 := @BV 32 0x00050713%Z I.
Lemma F_82e24 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e24%Z I : word) = Some W_82e24.
Proof. vm_refl. Qed.
Lemma D_82e24 : decode_any W_82e24 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e28 : bv 32 := @BV 32 0x00300613%Z I.
Lemma F_82e28 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e28%Z I : word) = Some W_82e28.
Proof. vm_refl. Qed.
Lemma D_82e28 : decode_any W_82e28 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e2c : bv 32 := @BV 32 0x00000513%Z I.
Lemma F_82e2c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e2c%Z I : word) = Some W_82e2c.
Proof. vm_refl. Qed.
Lemma D_82e2c : decode_any W_82e2c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e30 : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_82e30 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e30%Z I : word) = Some W_82e30.
Proof. vm_refl. Qed.
Lemma D_82e30 : decode_any W_82e30 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e34 : bv 32 := @BV 32 0x00000793%Z I.
Lemma F_82e34 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e34%Z I : word) = Some W_82e34.
Proof. vm_refl. Qed.
Lemma D_82e34 : decode_any W_82e34 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e38 : bv 32 := @BV 32 0xb70fe0ef%Z I.
Lemma F_82e38 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e38%Z I : word) = Some W_82e38.
Proof. vm_refl. Qed.
Lemma D_82e38 : decode_any W_82e38 = Some (Jal (@BV 5 1%Z I) (@BV 21 2089840%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e3c : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_82e3c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e3c%Z I : word) = Some W_82e3c.
Proof. vm_refl. Qed.
Lemma D_82e3c : decode_any W_82e3c = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e40 : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_82e40 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e40%Z I : word) = Some W_82e40.
Proof. vm_refl. Qed.
Lemma D_82e40 : decode_any W_82e40 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e44 : bv 32 := @BV 32 0xb44fe0ef%Z I.
Lemma F_82e44 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e44%Z I : word) = Some W_82e44.
Proof. vm_refl. Qed.
Lemma D_82e44 : decode_any W_82e44 = Some (Jal (@BV 5 1%Z I) (@BV 21 2089796%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e48 : bv 32 := @BV 32 0xaaaab537%Z I.
Lemma F_82e48 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e48%Z I : word) = Some W_82e48.
Proof. vm_refl. Qed.
Lemma D_82e48 : decode_any W_82e48 = Some (Lui (@BV 5 10%Z I) (@BV 20 699051%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e4c : bv 32 := @BV 32 0xaaa50513%Z I.
Lemma F_82e4c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e4c%Z I : word) = Some W_82e4c.
Proof. vm_refl. Qed.
Lemma D_82e4c : decode_any W_82e4c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2730%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e50 : bv 32 := @BV 32 0x00a12423%Z I.
Lemma F_82e50 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e50%Z I : word) = Some W_82e50.
Proof. vm_refl. Qed.
Lemma D_82e50 : decode_any W_82e50 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e54 : bv 32 := @BV 32 0x00810593%Z I.
Lemma F_82e54 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e54%Z I : word) = Some W_82e54.
Proof. vm_refl. Qed.
Lemma D_82e54 : decode_any W_82e54 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e58 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_82e58 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e58%Z I : word) = Some W_82e58.
Proof. vm_refl. Qed.
Lemma D_82e58 : decode_any W_82e58 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e5c : bv 32 := @BV 32 0xb2cfe0ef%Z I.
Lemma F_82e5c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e5c%Z I : word) = Some W_82e5c.
Proof. vm_refl. Qed.
Lemma D_82e5c : decode_any W_82e5c = Some (Jal (@BV 5 1%Z I) (@BV 21 2089772%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e60 : bv 32 := @BV 32 0x02051c63%Z I.
Lemma F_82e60 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e60%Z I : word) = Some W_82e60.
Proof. vm_refl. Qed.
Lemma D_82e60 : decode_any W_82e60 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e64 : bv 32 := @BV 32 0x00048513%Z I.
Lemma F_82e64 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e64%Z I : word) = Some W_82e64.
Proof. vm_refl. Qed.
Lemma D_82e64 : decode_any W_82e64 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e68 : bv 32 := @BV 32 0xa24fa0ef%Z I.
Lemma F_82e68 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e68%Z I : word) = Some W_82e68.
Proof. vm_refl. Qed.
Lemma D_82e68 : decode_any W_82e68 = Some (Jal (@BV 5 1%Z I) (@BV 21 2073124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e6c : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_82e6c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e6c%Z I : word) = Some W_82e6c.
Proof. vm_refl. Qed.
Lemma D_82e6c : decode_any W_82e6c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e70 : bv 32 := @BV 32 0x02813083%Z I.
Lemma F_82e70 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e70%Z I : word) = Some W_82e70.
Proof. vm_refl. Qed.
Lemma D_82e70 : decode_any W_82e70 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e74 : bv 32 := @BV 32 0x02013403%Z I.
Lemma F_82e74 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e74%Z I : word) = Some W_82e74.
Proof. vm_refl. Qed.
Lemma D_82e74 : decode_any W_82e74 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e78 : bv 32 := @BV 32 0x01813483%Z I.
Lemma F_82e78 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e78%Z I : word) = Some W_82e78.
Proof. vm_refl. Qed.
Lemma D_82e78 : decode_any W_82e78 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e7c : bv 32 := @BV 32 0x01013903%Z I.
Lemma F_82e7c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e7c%Z I : word) = Some W_82e7c.
Proof. vm_refl. Qed.
Lemma D_82e7c : decode_any W_82e7c = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e80 : bv 32 := @BV 32 0x03010113%Z I.
Lemma F_82e80 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e80%Z I : word) = Some W_82e80.
Proof. vm_refl. Qed.
Lemma D_82e80 : decode_any W_82e80 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e84 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_82e84 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e84%Z I : word) = Some W_82e84.
Proof. vm_refl. Qed.
Lemma D_82e84 : decode_any W_82e84 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e98 : bv 32 := @BV 32 0x00812683%Z I.
Lemma F_82e98 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e98%Z I : word) = Some W_82e98.
Proof. vm_refl. Qed.
Lemma D_82e98 : decode_any W_82e98 = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e9c : bv 32 := @BV 32 0xfff9b517%Z I.
Lemma F_82e9c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82e9c%Z I : word) = Some W_82e9c.
Proof. vm_refl. Qed.
Lemma D_82e9c : decode_any W_82e9c = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048475%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ea0 : bv 32 := @BV 32 0x32650613%Z I.
Lemma F_82ea0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ea0%Z I : word) = Some W_82ea0.
Proof. vm_refl. Qed.
Lemma D_82ea0 : decode_any W_82ea0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 806%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ea4 : bv 32 := @BV 32 0x00048513%Z I.
Lemma F_82ea4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ea4%Z I : word) = Some W_82ea4.
Proof. vm_refl. Qed.
Lemma D_82ea4 : decode_any W_82ea4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ea8 : bv 32 := @BV 32 0x00040593%Z I.
Lemma F_82ea8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ea8%Z I : word) = Some W_82ea8.
Proof. vm_refl. Qed.
Lemma D_82ea8 : decode_any W_82ea8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82eac : bv 32 := @BV 32 0x00000713%Z I.
Lemma F_82eac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82eac%Z I : word) = Some W_82eac.
Proof. vm_refl. Qed.
Lemma D_82eac : decode_any W_82eac = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82eb0 : bv 32 := @BV 32 0xb45f90ef%Z I.
Lemma F_82eb0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82eb0%Z I : word) = Some W_82eb0.
Proof. vm_refl. Qed.
Lemma D_82eb0 : decode_any W_82eb0 = Some (Jal (@BV 5 1%Z I) (@BV 21 2071364%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82eb4 : bv 32 := @BV 32 0x00060693%Z I.
Lemma F_82eb4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82eb4%Z I : word) = Some W_82eb4.
Proof. vm_refl. Qed.
Lemma D_82eb4 : decode_any W_82eb4 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82eb8 : bv 32 := @BV 32 0x00000613%Z I.
Lemma F_82eb8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82eb8%Z I : word) = Some W_82eb8.
Proof. vm_refl. Qed.
Lemma D_82eb8 : decode_any W_82eb8 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ebc : bv 32 := @BV 32 0x0040006f%Z I.
Lemma F_82ebc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ebc%Z I : word) = Some W_82ebc.
Proof. vm_refl. Qed.
Lemma D_82ebc : decode_any W_82ebc = Some (Jal (@BV 5 0%Z I) (@BV 21 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ec0 : bv 32 := @BV 32 0xfa010113%Z I.
Lemma F_82ec0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ec0%Z I : word) = Some W_82ec0.
Proof. vm_refl. Qed.
Lemma D_82ec0 : decode_any W_82ec0 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4000%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ec4 : bv 32 := @BV 32 0x04113c23%Z I.
Lemma F_82ec4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ec4%Z I : word) = Some W_82ec4.
Proof. vm_refl. Qed.
Lemma D_82ec4 : decode_any W_82ec4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ec8 : bv 32 := @BV 32 0x04813823%Z I.
Lemma F_82ec8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ec8%Z I : word) = Some W_82ec8.
Proof. vm_refl. Qed.
Lemma D_82ec8 : decode_any W_82ec8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ecc : bv 32 := @BV 32 0x04913423%Z I.
Lemma F_82ecc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ecc%Z I : word) = Some W_82ecc.
Proof. vm_refl. Qed.
Lemma D_82ecc : decode_any W_82ecc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ed0 : bv 32 := @BV 32 0x05213023%Z I.
Lemma F_82ed0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ed0%Z I : word) = Some W_82ed0.
Proof. vm_refl. Qed.
Lemma D_82ed0 : decode_any W_82ed0 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ed4 : bv 32 := @BV 32 0x03313c23%Z I.
Lemma F_82ed4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ed4%Z I : word) = Some W_82ed4.
Proof. vm_refl. Qed.
Lemma D_82ed4 : decode_any W_82ed4 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ed8 : bv 32 := @BV 32 0x03413823%Z I.
Lemma F_82ed8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ed8%Z I : word) = Some W_82ed8.
Proof. vm_refl. Qed.
Lemma D_82ed8 : decode_any W_82ed8 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82edc : bv 32 := @BV 32 0x00068993%Z I.
Lemma F_82edc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82edc%Z I : word) = Some W_82edc.
Proof. vm_refl. Qed.
Lemma D_82edc : decode_any W_82edc = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 13%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ee0 : bv 32 := @BV 32 0x00060493%Z I.
Lemma F_82ee0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ee0%Z I : word) = Some W_82ee0.
Proof. vm_refl. Qed.
Lemma D_82ee0 : decode_any W_82ee0 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ee4 : bv 32 := @BV 32 0x00058413%Z I.
Lemma F_82ee4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ee4%Z I : word) = Some W_82ee4.
Proof. vm_refl. Qed.
Lemma D_82ee4 : decode_any W_82ee4 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ee8 : bv 32 := @BV 32 0x00083597%Z I.
Lemma F_82ee8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ee8%Z I : word) = Some W_82ee8.
Proof. vm_refl. Qed.
Lemma D_82ee8 : decode_any W_82ee8 = Some (Auipc (@BV 5 11%Z I) (@BV 20 131%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82eec : bv 32 := @BV 32 0x0105ba03%Z I.
Lemma F_82eec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82eec%Z I : word) = Some W_82eec.
Proof. vm_refl. Qed.
Lemma D_82eec : decode_any W_82eec = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 11%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ef0 : bv 32 := @BV 32 0x000a3583%Z I.
Lemma F_82ef0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ef0%Z I : word) = Some W_82ef0.
Proof. vm_refl. Qed.
Lemma D_82ef0 : decode_any W_82ef0 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 20%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ef4 : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_82ef4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ef4%Z I : word) = Some W_82ef4.
Proof. vm_refl. Qed.
Lemma D_82ef4 : decode_any W_82ef4 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ef8 : bv 32 := @BV 32 0x00059863%Z I.
Lemma F_82ef8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ef8%Z I : word) = Some W_82ef8.
Proof. vm_refl. Qed.
Lemma D_82ef8 : decode_any W_82ef8 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f08 : bv 32 := @BV 32 0xfff58513%Z I.
Lemma F_82f08 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f08%Z I : word) = Some W_82f08.
Proof. vm_refl. Qed.
Lemma D_82f08 : decode_any W_82f08 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f0c : bv 32 := @BV 32 0x00a5f533%Z I.
Lemma F_82f0c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f0c%Z I : word) = Some W_82f0c.
Proof. vm_refl. Qed.
Lemma D_82f0c : decode_any W_82f0c = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f10 : bv 32 := @BV 32 0x0a051863%Z I.
Lemma F_82f10 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f10%Z I : word) = Some W_82f10.
Proof. vm_refl. Qed.
Lemma D_82f10 : decode_any W_82f10 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 176%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f14 : bv 32 := @BV 32 0x00b40433%Z I.
Lemma F_82f14 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f14%Z I : word) = Some W_82f14.
Proof. vm_refl. Qed.
Lemma D_82f14 : decode_any W_82f14 = Some (Op ALU_ADD (@BV 5 8%Z I) (@BV 5 8%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f18 : bv 32 := @BV 32 0xfff40413%Z I.
Lemma F_82f18 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f18%Z I : word) = Some W_82f18.
Proof. vm_refl. Qed.
Lemma D_82f18 : decode_any W_82f18 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 8%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f1c : bv 32 := @BV 32 0x40b00533%Z I.
Lemma F_82f1c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f1c%Z I : word) = Some W_82f1c.
Proof. vm_refl. Qed.
Lemma D_82f1c : decode_any W_82f1c = Some (Op ALU_SUB (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f20 : bv 32 := @BV 32 0x00a47433%Z I.
Lemma F_82f20 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f20%Z I : word) = Some W_82f20.
Proof. vm_refl. Qed.
Lemma D_82f20 : decode_any W_82f20 = Some (Op ALU_AND (@BV 5 8%Z I) (@BV 5 8%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f24 : bv 32 := @BV 32 0x00059863%Z I.
Lemma F_82f24 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f24%Z I : word) = Some W_82f24.
Proof. vm_refl. Qed.
Lemma D_82f24 : decode_any W_82f24 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f34 : bv 32 := @BV 32 0x00a97933%Z I.
Lemma F_82f34 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f34%Z I : word) = Some W_82f34.
Proof. vm_refl. Qed.
Lemma D_82f34 : decode_any W_82f34 = Some (Op ALU_AND (@BV 5 18%Z I) (@BV 5 18%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f38 : bv 32 := @BV 32 0x03200513%Z I.
Lemma F_82f38 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f38%Z I : word) = Some W_82f38.
Proof. vm_refl. Qed.
Lemma D_82f38 : decode_any W_82f38 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 50%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f3c : bv 32 := @BV 32 0x00a12023%Z I.
Lemma F_82f3c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f3c%Z I : word) = Some W_82f3c.
Proof. vm_refl. Qed.
Lemma D_82f3c : decode_any W_82f3c = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f40 : bv 32 := @BV 32 0x00010613%Z I.
Lemma F_82f40 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f40%Z I : word) = Some W_82f40.
Proof. vm_refl. Qed.
Lemma D_82f40 : decode_any W_82f40 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f44 : bv 32 := @BV 32 0x00098513%Z I.
Lemma F_82f44 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f44%Z I : word) = Some W_82f44.
Proof. vm_refl. Qed.
Lemma D_82f44 : decode_any W_82f44 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f48 : bv 32 := @BV 32 0x00040593%Z I.
Lemma F_82f48 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f48%Z I : word) = Some W_82f48.
Proof. vm_refl. Qed.
Lemma D_82f48 : decode_any W_82f48 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f4c : bv 32 := @BV 32 0x608000ef%Z I.
Lemma F_82f4c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f4c%Z I : word) = Some W_82f4c.
Proof. vm_refl. Qed.
Lemma D_82f4c : decode_any W_82f4c = Some (Jal (@BV 5 1%Z I) (@BV 21 1544%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f50 : bv 32 := @BV 32 0x00012683%Z I.
Lemma F_82f50 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f50%Z I : word) = Some W_82f50.
Proof. vm_refl. Qed.
Lemma D_82f50 : decode_any W_82f50 = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f54 : bv 32 := @BV 32 0x00050713%Z I.
Lemma F_82f54 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f54%Z I : word) = Some W_82f54.
Proof. vm_refl. Qed.
Lemma D_82f54 : decode_any W_82f54 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f58 : bv 32 := @BV 32 0x00300613%Z I.
Lemma F_82f58 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f58%Z I : word) = Some W_82f58.
Proof. vm_refl. Qed.
Lemma D_82f58 : decode_any W_82f58 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f5c : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_82f5c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f5c%Z I : word) = Some W_82f5c.
Proof. vm_refl. Qed.
Lemma D_82f5c : decode_any W_82f5c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f60 : bv 32 := @BV 32 0x00040593%Z I.
Lemma F_82f60 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f60%Z I : word) = Some W_82f60.
Proof. vm_refl. Qed.
Lemma D_82f60 : decode_any W_82f60 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f64 : bv 32 := @BV 32 0x00000793%Z I.
Lemma F_82f64 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f64%Z I : word) = Some W_82f64.
Proof. vm_refl. Qed.
Lemma D_82f64 : decode_any W_82f64 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f68 : bv 32 := @BV 32 0xa40fe0ef%Z I.
Lemma F_82f68 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f68%Z I : word) = Some W_82f68.
Proof. vm_refl. Qed.
Lemma D_82f68 : decode_any W_82f68 = Some (Jal (@BV 5 1%Z I) (@BV 21 2089536%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f6c : bv 32 := @BV 32 0x00050993%Z I.
Lemma F_82f6c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f6c%Z I : word) = Some W_82f6c.
Proof. vm_refl. Qed.
Lemma D_82f6c : decode_any W_82f6c = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f70 : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_82f70 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f70%Z I : word) = Some W_82f70.
Proof. vm_refl. Qed.
Lemma D_82f70 : decode_any W_82f70 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f74 : bv 32 := @BV 32 0xa14fe0ef%Z I.
Lemma F_82f74 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f74%Z I : word) = Some W_82f74.
Proof. vm_refl. Qed.
Lemma D_82f74 : decode_any W_82f74 = Some (Jal (@BV 5 1%Z I) (@BV 21 2089492%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f78 : bv 32 := @BV 32 0xaaaab537%Z I.
Lemma F_82f78 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f78%Z I : word) = Some W_82f78.
Proof. vm_refl. Qed.
Lemma D_82f78 : decode_any W_82f78 = Some (Lui (@BV 5 10%Z I) (@BV 20 699051%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f7c : bv 32 := @BV 32 0xaaa50513%Z I.
Lemma F_82f7c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f7c%Z I : word) = Some W_82f7c.
Proof. vm_refl. Qed.
Lemma D_82f7c : decode_any W_82f7c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2730%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f80 : bv 32 := @BV 32 0x02a12623%Z I.
Lemma F_82f80 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f80%Z I : word) = Some W_82f80.
Proof. vm_refl. Qed.
Lemma D_82f80 : decode_any W_82f80 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f84 : bv 32 := @BV 32 0x02c10593%Z I.
Lemma F_82f84 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f84%Z I : word) = Some W_82f84.
Proof. vm_refl. Qed.
Lemma D_82f84 : decode_any W_82f84 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 44%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f88 : bv 32 := @BV 32 0x00098513%Z I.
Lemma F_82f88 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f88%Z I : word) = Some W_82f88.
Proof. vm_refl. Qed.
Lemma D_82f88 : decode_any W_82f88 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f8c : bv 32 := @BV 32 0x9fcfe0ef%Z I.
Lemma F_82f8c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f8c%Z I : word) = Some W_82f8c.
Proof. vm_refl. Qed.
Lemma D_82f8c : decode_any W_82f8c = Some (Jal (@BV 5 1%Z I) (@BV 21 2089468%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f90 : bv 32 := @BV 32 0x04051063%Z I.
Lemma F_82f90 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f90%Z I : word) = Some W_82f90.
Proof. vm_refl. Qed.
Lemma D_82f90 : decode_any W_82f90 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f94 : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_82f94 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f94%Z I : word) = Some W_82f94.
Proof. vm_refl. Qed.
Lemma D_82f94 : decode_any W_82f94 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f98 : bv 32 := @BV 32 0x8f4fa0ef%Z I.
Lemma F_82f98 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f98%Z I : word) = Some W_82f98.
Proof. vm_refl. Qed.
Lemma D_82f98 : decode_any W_82f98 = Some (Jal (@BV 5 1%Z I) (@BV 21 2072820%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f9c : bv 32 := @BV 32 0x00098513%Z I.
Lemma F_82f9c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82f9c%Z I : word) = Some W_82f9c.
Proof. vm_refl. Qed.
Lemma D_82f9c : decode_any W_82f9c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82fa0 : bv 32 := @BV 32 0x05813083%Z I.
Lemma F_82fa0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82fa0%Z I : word) = Some W_82fa0.
Proof. vm_refl. Qed.
Lemma D_82fa0 : decode_any W_82fa0 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 88%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82fa4 : bv 32 := @BV 32 0x05013403%Z I.
Lemma F_82fa4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82fa4%Z I : word) = Some W_82fa4.
Proof. vm_refl. Qed.
Lemma D_82fa4 : decode_any W_82fa4 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 80%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82fa8 : bv 32 := @BV 32 0x04813483%Z I.
Lemma F_82fa8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82fa8%Z I : word) = Some W_82fa8.
Proof. vm_refl. Qed.
Lemma D_82fa8 : decode_any W_82fa8 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 72%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82fac : bv 32 := @BV 32 0x04013903%Z I.
Lemma F_82fac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82fac%Z I : word) = Some W_82fac.
Proof. vm_refl. Qed.
Lemma D_82fac : decode_any W_82fac = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 64%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82fb0 : bv 32 := @BV 32 0x03813983%Z I.
Lemma F_82fb0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82fb0%Z I : word) = Some W_82fb0.
Proof. vm_refl. Qed.
Lemma D_82fb0 : decode_any W_82fb0 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 56%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82fb4 : bv 32 := @BV 32 0x03013a03%Z I.
Lemma F_82fb4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82fb4%Z I : word) = Some W_82fb4.
Proof. vm_refl. Qed.
Lemma D_82fb4 : decode_any W_82fb4 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82fb8 : bv 32 := @BV 32 0x06010113%Z I.
Lemma F_82fb8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82fb8%Z I : word) = Some W_82fb8.
Proof. vm_refl. Qed.
Lemma D_82fb8 : decode_any W_82fb8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82fbc : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_82fbc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82fbc%Z I : word) = Some W_82fbc.
Proof. vm_refl. Qed.
Lemma D_82fbc : decode_any W_82fbc = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82fd0 : bv 32 := @BV 32 0x00048c63%Z I.
Lemma F_82fd0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82fd0%Z I : word) = Some W_82fd0.
Proof. vm_refl. Qed.
Lemma D_82fd0 : decode_any W_82fd0 = Some (Branch BC_EQ (@BV 5 9%Z I) (@BV 5 0%Z I) (@BV 13 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83038 : bv 32 := @BV 32 0x00060693%Z I.
Lemma F_83038 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83038%Z I : word) = Some W_83038.
Proof. vm_refl. Qed.
Lemma D_83038 : decode_any W_83038 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8303c : bv 32 := @BV 32 0x00100613%Z I.
Lemma F_8303c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8303c%Z I : word) = Some W_8303c.
Proof. vm_refl. Qed.
Lemma D_8303c : decode_any W_8303c = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83040 : bv 32 := @BV 32 0xe81ff06f%Z I.
Lemma F_83040 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83040%Z I : word) = Some W_83040.
Proof. vm_refl. Qed.
Lemma D_83040 : decode_any W_83040 = Some (Jal (@BV 5 0%Z I) (@BV 21 2096768%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83554 : bv 32 := @BV 32 0xef010113%Z I.
Lemma F_83554 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83554%Z I : word) = Some W_83554.
Proof. vm_refl. Qed.
Lemma D_83554 : decode_any W_83554 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 3824%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83558 : bv 32 := @BV 32 0x10113423%Z I.
Lemma F_83558 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83558%Z I : word) = Some W_83558.
Proof. vm_refl. Qed.
Lemma D_83558 : decode_any W_83558 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 264%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8355c : bv 32 := @BV 32 0x10813023%Z I.
Lemma F_8355c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8355c%Z I : word) = Some W_8355c.
Proof. vm_refl. Qed.
Lemma D_8355c : decode_any W_8355c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 256%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83560 : bv 32 := @BV 32 0x0e913c23%Z I.
Lemma F_83560 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83560%Z I : word) = Some W_83560.
Proof. vm_refl. Qed.
Lemma D_83560 : decode_any W_83560 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 248%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83564 : bv 32 := @BV 32 0x0f213823%Z I.
Lemma F_83564 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83564%Z I : word) = Some W_83564.
Proof. vm_refl. Qed.
Lemma D_83564 : decode_any W_83564 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 240%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83568 : bv 32 := @BV 32 0x0f313423%Z I.
Lemma F_83568 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83568%Z I : word) = Some W_83568.
Proof. vm_refl. Qed.
Lemma D_83568 : decode_any W_83568 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 232%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8356c : bv 32 := @BV 32 0x0f413023%Z I.
Lemma F_8356c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8356c%Z I : word) = Some W_8356c.
Proof. vm_refl. Qed.
Lemma D_8356c : decode_any W_8356c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 224%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83570 : bv 32 := @BV 32 0x0d513c23%Z I.
Lemma F_83570 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83570%Z I : word) = Some W_83570.
Proof. vm_refl. Qed.
Lemma D_83570 : decode_any W_83570 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 216%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83574 : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_83574 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83574%Z I : word) = Some W_83574.
Proof. vm_refl. Qed.
Lemma D_83574 : decode_any W_83574 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83578 : bv 32 := @BV 32 0xfff00513%Z I.
Lemma F_83578 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83578%Z I : word) = Some W_83578.
Proof. vm_refl. Qed.
Lemma D_83578 : decode_any W_83578 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8357c : bv 32 := @BV 32 0x12090463%Z I.
Lemma F_8357c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8357c%Z I : word) = Some W_8357c.
Proof. vm_refl. Qed.
Lemma D_8357c : decode_any W_8357c = Some (Branch BC_EQ (@BV 5 18%Z I) (@BV 5 0%Z I) (@BV 13 296%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83580 : bv 32 := @BV 32 0x00060413%Z I.
Lemma F_83580 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83580%Z I : word) = Some W_83580.
Proof. vm_refl. Qed.
Lemma D_83580 : decode_any W_83580 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83584 : bv 32 := @BV 32 0x00083617%Z I.
Lemma F_83584 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83584%Z I : word) = Some W_83584.
Proof. vm_refl. Qed.
Lemma D_83584 : decode_any W_83584 = Some (Auipc (@BV 5 12%Z I) (@BV 20 131%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83588 : bv 32 := @BV 32 0x98463603%Z I.
Lemma F_83588 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83588%Z I : word) = Some W_83588.
Proof. vm_refl. Qed.
Lemma D_83588 : decode_any W_83588 = Some (Load SZ8 true (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 2436%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8358c : bv 32 := @BV 32 0x10464603%Z I.
Lemma F_8358c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8358c%Z I : word) = Some W_8358c.
Proof. vm_refl. Qed.
Lemma D_8358c : decode_any W_8358c = Some (Load SZ1 false (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 260%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83590 : bv 32 := @BV 32 0x00167613%Z I.
Lemma F_83590 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83590%Z I : word) = Some W_83590.
Proof. vm_refl. Qed.
Lemma D_83590 : decode_any W_83590 = Some (OpImm ALU_AND (@BV 5 12%Z I) (@BV 5 12%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83594 : bv 32 := @BV 32 0x10060863%Z I.
Lemma F_83594 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x83594%Z I : word) = Some W_83594.
Proof. vm_refl. Qed.
Lemma D_83594 : decode_any W_83594 = Some (Branch BC_EQ (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 13 272%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836a4 : bv 32 := @BV 32 0x0005051b%Z I.
Lemma F_836a4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x836a4%Z I : word) = Some W_836a4.
Proof. vm_refl. Qed.
Lemma D_836a4 : decode_any W_836a4 = Some (OpImm32 (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836a8 : bv 32 := @BV 32 0x10813083%Z I.
Lemma F_836a8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x836a8%Z I : word) = Some W_836a8.
Proof. vm_refl. Qed.
Lemma D_836a8 : decode_any W_836a8 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 264%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836ac : bv 32 := @BV 32 0x10013403%Z I.
Lemma F_836ac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x836ac%Z I : word) = Some W_836ac.
Proof. vm_refl. Qed.
Lemma D_836ac : decode_any W_836ac = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 256%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836b0 : bv 32 := @BV 32 0x0f813483%Z I.
Lemma F_836b0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x836b0%Z I : word) = Some W_836b0.
Proof. vm_refl. Qed.
Lemma D_836b0 : decode_any W_836b0 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 248%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836b4 : bv 32 := @BV 32 0x0f013903%Z I.
Lemma F_836b4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x836b4%Z I : word) = Some W_836b4.
Proof. vm_refl. Qed.
Lemma D_836b4 : decode_any W_836b4 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 240%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836b8 : bv 32 := @BV 32 0x0e813983%Z I.
Lemma F_836b8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x836b8%Z I : word) = Some W_836b8.
Proof. vm_refl. Qed.
Lemma D_836b8 : decode_any W_836b8 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 232%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836bc : bv 32 := @BV 32 0x0e013a03%Z I.
Lemma F_836bc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x836bc%Z I : word) = Some W_836bc.
Proof. vm_refl. Qed.
Lemma D_836bc : decode_any W_836bc = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 224%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836c0 : bv 32 := @BV 32 0x0d813a83%Z I.
Lemma F_836c0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x836c0%Z I : word) = Some W_836c0.
Proof. vm_refl. Qed.
Lemma D_836c0 : decode_any W_836c0 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 216%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836c4 : bv 32 := @BV 32 0x11010113%Z I.
Lemma F_836c4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x836c4%Z I : word) = Some W_836c4.
Proof. vm_refl. Qed.
Lemma D_836c4 : decode_any W_836c4 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 272%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_836c8 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_836c8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x836c8%Z I : word) = Some W_836c8.
Proof. vm_refl. Qed.
Lemma D_836c8 : decode_any W_836c8 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
