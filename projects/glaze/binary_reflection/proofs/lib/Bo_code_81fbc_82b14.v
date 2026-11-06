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
Definition W_82878 : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_82878 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82878%Z I : word) = Some W_82878.
Proof. vm_refl. Qed.
Lemma D_82878 : decode_any W_82878 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8287c : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_8287c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8287c%Z I : word) = Some W_8287c.
Proof. vm_refl. Qed.
Lemma D_8287c : decode_any W_8287c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82880 : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_82880 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82880%Z I : word) = Some W_82880.
Proof. vm_refl. Qed.
Lemma D_82880 : decode_any W_82880 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82884 : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_82884 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82884%Z I : word) = Some W_82884.
Proof. vm_refl. Qed.
Lemma D_82884 : decode_any W_82884 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82888 : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_82888 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82888%Z I : word) = Some W_82888.
Proof. vm_refl. Qed.
Lemma D_82888 : decode_any W_82888 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8288c : bv 32 := @BV 32 0x01313423%Z I.
Lemma F_8288c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8288c%Z I : word) = Some W_8288c.
Proof. vm_refl. Qed.
Lemma D_8288c : decode_any W_8288c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82890 : bv 32 := @BV 32 0x00060413%Z I.
Lemma F_82890 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82890%Z I : word) = Some W_82890.
Proof. vm_refl. Qed.
Lemma D_82890 : decode_any W_82890 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82894 : bv 32 := @BV 32 0x00058493%Z I.
Lemma F_82894 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82894%Z I : word) = Some W_82894.
Proof. vm_refl. Qed.
Lemma D_82894 : decode_any W_82894 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82898 : bv 32 := @BV 32 0x00083597%Z I.
Lemma F_82898 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82898%Z I : word) = Some W_82898.
Proof. vm_refl. Qed.
Lemma D_82898 : decode_any W_82898 = Some (Auipc (@BV 5 11%Z I) (@BV 20 131%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8289c : bv 32 := @BV 32 0x6605b983%Z I.
Lemma F_8289c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8289c%Z I : word) = Some W_8289c.
Proof. vm_refl. Qed.
Lemma D_8289c : decode_any W_8289c = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 11%Z I) (@BV 12 1632%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828a0 : bv 32 := @BV 32 0x0009b583%Z I.
Lemma F_828a0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828a0%Z I : word) = Some W_828a0.
Proof. vm_refl. Qed.
Lemma D_828a0 : decode_any W_828a0 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828a4 : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_828a4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828a4%Z I : word) = Some W_828a4.
Proof. vm_refl. Qed.
Lemma D_828a4 : decode_any W_828a4 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828a8 : bv 32 := @BV 32 0x00059863%Z I.
Lemma F_828a8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828a8%Z I : word) = Some W_828a8.
Proof. vm_refl. Qed.
Lemma D_828a8 : decode_any W_828a8 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828b8 : bv 32 := @BV 32 0xfff58513%Z I.
Lemma F_828b8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828b8%Z I : word) = Some W_828b8.
Proof. vm_refl. Qed.
Lemma D_828b8 : decode_any W_828b8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828bc : bv 32 := @BV 32 0x00a5f533%Z I.
Lemma F_828bc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828bc%Z I : word) = Some W_828bc.
Proof. vm_refl. Qed.
Lemma D_828bc : decode_any W_828bc = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828c0 : bv 32 := @BV 32 0x08051c63%Z I.
Lemma F_828c0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828c0%Z I : word) = Some W_828c0.
Proof. vm_refl. Qed.
Lemma D_828c0 : decode_any W_828c0 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828c4 : bv 32 := @BV 32 0x00b90933%Z I.
Lemma F_828c4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828c4%Z I : word) = Some W_828c4.
Proof. vm_refl. Qed.
Lemma D_828c4 : decode_any W_828c4 = Some (Op ALU_ADD (@BV 5 18%Z I) (@BV 5 18%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828c8 : bv 32 := @BV 32 0x40b00533%Z I.
Lemma F_828c8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828c8%Z I : word) = Some W_828c8.
Proof. vm_refl. Qed.
Lemma D_828c8 : decode_any W_828c8 = Some (Op ALU_SUB (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828cc : bv 32 := @BV 32 0xfff90913%Z I.
Lemma F_828cc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828cc%Z I : word) = Some W_828cc.
Proof. vm_refl. Qed.
Lemma D_828cc : decode_any W_828cc = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 18%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828d0 : bv 32 := @BV 32 0x00a97933%Z I.
Lemma F_828d0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828d0%Z I : word) = Some W_828d0.
Proof. vm_refl. Qed.
Lemma D_828d0 : decode_any W_828d0 = Some (Op ALU_AND (@BV 5 18%Z I) (@BV 5 18%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828d4 : bv 32 := @BV 32 0x02200513%Z I.
Lemma F_828d4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828d4%Z I : word) = Some W_828d4.
Proof. vm_refl. Qed.
Lemma D_828d4 : decode_any W_828d4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 34%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828d8 : bv 32 := @BV 32 0x00a12223%Z I.
Lemma F_828d8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828d8%Z I : word) = Some W_828d8.
Proof. vm_refl. Qed.
Lemma D_828d8 : decode_any W_828d8 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828dc : bv 32 := @BV 32 0x00410613%Z I.
Lemma F_828dc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828dc%Z I : word) = Some W_828dc.
Proof. vm_refl. Qed.
Lemma D_828dc : decode_any W_828dc = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828e0 : bv 32 := @BV 32 0x00048513%Z I.
Lemma F_828e0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828e0%Z I : word) = Some W_828e0.
Proof. vm_refl. Qed.
Lemma D_828e0 : decode_any W_828e0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828e4 : bv 32 := @BV 32 0x00090593%Z I.
Lemma F_828e4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828e4%Z I : word) = Some W_828e4.
Proof. vm_refl. Qed.
Lemma D_828e4 : decode_any W_828e4 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828e8 : bv 32 := @BV 32 0x46d000ef%Z I.
Lemma F_828e8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828e8%Z I : word) = Some W_828e8.
Proof. vm_refl. Qed.
Lemma D_828e8 : decode_any W_828e8 = Some (Jal (@BV 5 1%Z I) (@BV 21 3180%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828ec : bv 32 := @BV 32 0x00412683%Z I.
Lemma F_828ec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828ec%Z I : word) = Some W_828ec.
Proof. vm_refl. Qed.
Lemma D_828ec : decode_any W_828ec = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 4%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828f0 : bv 32 := @BV 32 0x00050713%Z I.
Lemma F_828f0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828f0%Z I : word) = Some W_828f0.
Proof. vm_refl. Qed.
Lemma D_828f0 : decode_any W_828f0 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828f4 : bv 32 := @BV 32 0x00300613%Z I.
Lemma F_828f4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828f4%Z I : word) = Some W_828f4.
Proof. vm_refl. Qed.
Lemma D_828f4 : decode_any W_828f4 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828f8 : bv 32 := @BV 32 0x00000513%Z I.
Lemma F_828f8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828f8%Z I : word) = Some W_828f8.
Proof. vm_refl. Qed.
Lemma D_828f8 : decode_any W_828f8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828fc : bv 32 := @BV 32 0x00090593%Z I.
Lemma F_828fc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x828fc%Z I : word) = Some W_828fc.
Proof. vm_refl. Qed.
Lemma D_828fc : decode_any W_828fc = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82900 : bv 32 := @BV 32 0x00000793%Z I.
Lemma F_82900 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82900%Z I : word) = Some W_82900.
Proof. vm_refl. Qed.
Lemma D_82900 : decode_any W_82900 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82904 : bv 32 := @BV 32 0x8a5fe0ef%Z I.
Lemma F_82904 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82904%Z I : word) = Some W_82904.
Proof. vm_refl. Qed.
Lemma D_82904 : decode_any W_82904 = Some (Jal (@BV 5 1%Z I) (@BV 21 2091172%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82908 : bv 32 := @BV 32 0x00050993%Z I.
Lemma F_82908 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82908%Z I : word) = Some W_82908.
Proof. vm_refl. Qed.
Lemma D_82908 : decode_any W_82908 = Some (OpImm ALU_ADD (@BV 5 19%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8290c : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_8290c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8290c%Z I : word) = Some W_8290c.
Proof. vm_refl. Qed.
Lemma D_8290c : decode_any W_8290c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82910 : bv 32 := @BV 32 0x879fe0ef%Z I.
Lemma F_82910 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82910%Z I : word) = Some W_82910.
Proof. vm_refl. Qed.
Lemma D_82910 : decode_any W_82910 = Some (Jal (@BV 5 1%Z I) (@BV 21 2091128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82914 : bv 32 := @BV 32 0xaaaab537%Z I.
Lemma F_82914 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82914%Z I : word) = Some W_82914.
Proof. vm_refl. Qed.
Lemma D_82914 : decode_any W_82914 = Some (Lui (@BV 5 10%Z I) (@BV 20 699051%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82918 : bv 32 := @BV 32 0xaaa50513%Z I.
Lemma F_82918 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82918%Z I : word) = Some W_82918.
Proof. vm_refl. Qed.
Lemma D_82918 : decode_any W_82918 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2730%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8291c : bv 32 := @BV 32 0x00a12023%Z I.
Lemma F_8291c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8291c%Z I : word) = Some W_8291c.
Proof. vm_refl. Qed.
Lemma D_8291c : decode_any W_8291c = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82920 : bv 32 := @BV 32 0x00010593%Z I.
Lemma F_82920 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82920%Z I : word) = Some W_82920.
Proof. vm_refl. Qed.
Lemma D_82920 : decode_any W_82920 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82924 : bv 32 := @BV 32 0x00098513%Z I.
Lemma F_82924 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82924%Z I : word) = Some W_82924.
Proof. vm_refl. Qed.
Lemma D_82924 : decode_any W_82924 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82928 : bv 32 := @BV 32 0x861fe0ef%Z I.
Lemma F_82928 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82928%Z I : word) = Some W_82928.
Proof. vm_refl. Qed.
Lemma D_82928 : decode_any W_82928 = Some (Jal (@BV 5 1%Z I) (@BV 21 2091104%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8292c : bv 32 := @BV 32 0x02051e63%Z I.
Lemma F_8292c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8292c%Z I : word) = Some W_8292c.
Proof. vm_refl. Qed.
Lemma D_8292c : decode_any W_8292c = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82930 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_82930 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82930%Z I : word) = Some W_82930.
Proof. vm_refl. Qed.
Lemma D_82930 : decode_any W_82930 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82934 : bv 32 := @BV 32 0xf58fa0ef%Z I.
Lemma F_82934 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82934%Z I : word) = Some W_82934.
Proof. vm_refl. Qed.
Lemma D_82934 : decode_any W_82934 = Some (Jal (@BV 5 1%Z I) (@BV 21 2074456%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82938 : bv 32 := @BV 32 0x00098513%Z I.
Lemma F_82938 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82938%Z I : word) = Some W_82938.
Proof. vm_refl. Qed.
Lemma D_82938 : decode_any W_82938 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8293c : bv 32 := @BV 32 0x02813083%Z I.
Lemma F_8293c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8293c%Z I : word) = Some W_8293c.
Proof. vm_refl. Qed.
Lemma D_8293c : decode_any W_8293c = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82940 : bv 32 := @BV 32 0x02013403%Z I.
Lemma F_82940 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82940%Z I : word) = Some W_82940.
Proof. vm_refl. Qed.
Lemma D_82940 : decode_any W_82940 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82944 : bv 32 := @BV 32 0x01813483%Z I.
Lemma F_82944 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82944%Z I : word) = Some W_82944.
Proof. vm_refl. Qed.
Lemma D_82944 : decode_any W_82944 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82948 : bv 32 := @BV 32 0x01013903%Z I.
Lemma F_82948 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82948%Z I : word) = Some W_82948.
Proof. vm_refl. Qed.
Lemma D_82948 : decode_any W_82948 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8294c : bv 32 := @BV 32 0x00813983%Z I.
Lemma F_8294c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8294c%Z I : word) = Some W_8294c.
Proof. vm_refl. Qed.
Lemma D_8294c : decode_any W_8294c = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82950 : bv 32 := @BV 32 0x03010113%Z I.
Lemma F_82950 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82950%Z I : word) = Some W_82950.
Proof. vm_refl. Qed.
Lemma D_82950 : decode_any W_82950 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82954 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_82954 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82954%Z I : word) = Some W_82954.
Proof. vm_refl. Qed.
Lemma D_82954 : decode_any W_82954 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82968 : bv 32 := @BV 32 0x00012683%Z I.
Lemma F_82968 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82968%Z I : word) = Some W_82968.
Proof. vm_refl. Qed.
Lemma D_82968 : decode_any W_82968 = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8296c : bv 32 := @BV 32 0xfff98517%Z I.
Lemma F_8296c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8296c%Z I : word) = Some W_8296c.
Proof. vm_refl. Qed.
Lemma D_8296c : decode_any W_8296c = Some (Auipc (@BV 5 10%Z I) (@BV 20 1048472%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82970 : bv 32 := @BV 32 0x3bd50613%Z I.
Lemma F_82970 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82970%Z I : word) = Some W_82970.
Proof. vm_refl. Qed.
Lemma D_82970 : decode_any W_82970 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 12 957%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82974 : bv 32 := @BV 32 0x00090513%Z I.
Lemma F_82974 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82974%Z I : word) = Some W_82974.
Proof. vm_refl. Qed.
Lemma D_82974 : decode_any W_82974 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82978 : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_82978 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82978%Z I : word) = Some W_82978.
Proof. vm_refl. Qed.
Lemma D_82978 : decode_any W_82978 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8297c : bv 32 := @BV 32 0x00040713%Z I.
Lemma F_8297c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8297c%Z I : word) = Some W_8297c.
Proof. vm_refl. Qed.
Lemma D_8297c : decode_any W_8297c = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82980 : bv 32 := @BV 32 0x874fa0ef%Z I.
Lemma F_82980 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82980%Z I : word) = Some W_82980.
Proof. vm_refl. Qed.
Lemma D_82980 : decode_any W_82980 = Some (Jal (@BV 5 1%Z I) (@BV 21 2072692%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_829f8 : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_829f8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x829f8%Z I : word) = Some W_829f8.
Proof. vm_refl. Qed.
Lemma D_829f8 : decode_any W_829f8 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_829fc : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_829fc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x829fc%Z I : word) = Some W_829fc.
Proof. vm_refl. Qed.
Lemma D_829fc : decode_any W_829fc = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a00 : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_82a00 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a00%Z I : word) = Some W_82a00.
Proof. vm_refl. Qed.
Lemma D_82a00 : decode_any W_82a00 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a04 : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_82a04 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a04%Z I : word) = Some W_82a04.
Proof. vm_refl. Qed.
Lemma D_82a04 : decode_any W_82a04 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a08 : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_82a08 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a08%Z I : word) = Some W_82a08.
Proof. vm_refl. Qed.
Lemma D_82a08 : decode_any W_82a08 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a0c : bv 32 := @BV 32 0x02050e63%Z I.
Lemma F_82a0c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a0c%Z I : word) = Some W_82a0c.
Proof. vm_refl. Qed.
Lemma D_82a0c : decode_any W_82a0c = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 60%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a10 : bv 32 := @BV 32 0x00058413%Z I.
Lemma F_82a10 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a10%Z I : word) = Some W_82a10.
Proof. vm_refl. Qed.
Lemma D_82a10 : decode_any W_82a10 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a14 : bv 32 := @BV 32 0x02058a63%Z I.
Lemma F_82a14 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a14%Z I : word) = Some W_82a14.
Proof. vm_refl. Qed.
Lemma D_82a14 : decode_any W_82a14 = Some (Branch BC_EQ (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 52%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a18 : bv 32 := @BV 32 0x00060493%Z I.
Lemma F_82a18 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a18%Z I : word) = Some W_82a18.
Proof. vm_refl. Qed.
Lemma D_82a18 : decode_any W_82a18 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 12%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a1c : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_82a1c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a1c%Z I : word) = Some W_82a1c.
Proof. vm_refl. Qed.
Lemma D_82a1c : decode_any W_82a1c = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a20 : bv 32 := @BV 32 0x00040593%Z I.
Lemma F_82a20 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a20%Z I : word) = Some W_82a20.
Proof. vm_refl. Qed.
Lemma D_82a20 : decode_any W_82a20 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a24 : bv 32 := @BV 32 0xf90fe0ef%Z I.
Lemma F_82a24 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a24%Z I : word) = Some W_82a24.
Proof. vm_refl. Qed.
Lemma D_82a24 : decode_any W_82a24 = Some (Jal (@BV 5 1%Z I) (@BV 21 2090896%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a28 : bv 32 := @BV 32 0xaaaab5b7%Z I.
Lemma F_82a28 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a28%Z I : word) = Some W_82a28.
Proof. vm_refl. Qed.
Lemma D_82a28 : decode_any W_82a28 = Some (Lui (@BV 5 11%Z I) (@BV 20 699051%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a2c : bv 32 := @BV 32 0xaaa58593%Z I.
Lemma F_82a2c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a2c%Z I : word) = Some W_82a2c.
Proof. vm_refl. Qed.
Lemma D_82a2c : decode_any W_82a2c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 2730%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a30 : bv 32 := @BV 32 0x00b12623%Z I.
Lemma F_82a30 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a30%Z I : word) = Some W_82a30.
Proof. vm_refl. Qed.
Lemma D_82a30 : decode_any W_82a30 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 11%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a34 : bv 32 := @BV 32 0x00c10593%Z I.
Lemma F_82a34 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a34%Z I : word) = Some W_82a34.
Proof. vm_refl. Qed.
Lemma D_82a34 : decode_any W_82a34 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 2%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a38 : bv 32 := @BV 32 0xf50fe0ef%Z I.
Lemma F_82a38 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a38%Z I : word) = Some W_82a38.
Proof. vm_refl. Qed.
Lemma D_82a38 : decode_any W_82a38 = Some (Jal (@BV 5 1%Z I) (@BV 21 2090832%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a3c : bv 32 := @BV 32 0x02051263%Z I.
Lemma F_82a3c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a3c%Z I : word) = Some W_82a3c.
Proof. vm_refl. Qed.
Lemma D_82a3c : decode_any W_82a3c = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 36%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a40 : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_82a40 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a40%Z I : word) = Some W_82a40.
Proof. vm_refl. Qed.
Lemma D_82a40 : decode_any W_82a40 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a44 : bv 32 := @BV 32 0xe8cfa0ef%Z I.
Lemma F_82a44 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a44%Z I : word) = Some W_82a44.
Proof. vm_refl. Qed.
Lemma D_82a44 : decode_any W_82a44 = Some (Jal (@BV 5 1%Z I) (@BV 21 2074252%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a48 : bv 32 := @BV 32 0x02813083%Z I.
Lemma F_82a48 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a48%Z I : word) = Some W_82a48.
Proof. vm_refl. Qed.
Lemma D_82a48 : decode_any W_82a48 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a4c : bv 32 := @BV 32 0x02013403%Z I.
Lemma F_82a4c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a4c%Z I : word) = Some W_82a4c.
Proof. vm_refl. Qed.
Lemma D_82a4c : decode_any W_82a4c = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a50 : bv 32 := @BV 32 0x01813483%Z I.
Lemma F_82a50 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a50%Z I : word) = Some W_82a50.
Proof. vm_refl. Qed.
Lemma D_82a50 : decode_any W_82a50 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a54 : bv 32 := @BV 32 0x01013903%Z I.
Lemma F_82a54 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a54%Z I : word) = Some W_82a54.
Proof. vm_refl. Qed.
Lemma D_82a54 : decode_any W_82a54 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a58 : bv 32 := @BV 32 0x03010113%Z I.
Lemma F_82a58 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a58%Z I : word) = Some W_82a58.
Proof. vm_refl. Qed.
Lemma D_82a58 : decode_any W_82a58 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 48%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a5c : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_82a5c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a5c%Z I : word) = Some W_82a5c.
Proof. vm_refl. Qed.
Lemma D_82a5c : decode_any W_82a5c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a74 : bv 32 := @BV 32 0xfd010113%Z I.
Lemma F_82a74 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a74%Z I : word) = Some W_82a74.
Proof. vm_refl. Qed.
Lemma D_82a74 : decode_any W_82a74 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a78 : bv 32 := @BV 32 0x02113423%Z I.
Lemma F_82a78 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a78%Z I : word) = Some W_82a78.
Proof. vm_refl. Qed.
Lemma D_82a78 : decode_any W_82a78 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 40%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a7c : bv 32 := @BV 32 0x02813023%Z I.
Lemma F_82a7c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a7c%Z I : word) = Some W_82a7c.
Proof. vm_refl. Qed.
Lemma D_82a7c : decode_any W_82a7c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a80 : bv 32 := @BV 32 0x00913c23%Z I.
Lemma F_82a80 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a80%Z I : word) = Some W_82a80.
Proof. vm_refl. Qed.
Lemma D_82a80 : decode_any W_82a80 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 24%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a84 : bv 32 := @BV 32 0x01213823%Z I.
Lemma F_82a84 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a84%Z I : word) = Some W_82a84.
Proof. vm_refl. Qed.
Lemma D_82a84 : decode_any W_82a84 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a88 : bv 32 := @BV 32 0x00058413%Z I.
Lemma F_82a88 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a88%Z I : word) = Some W_82a88.
Proof. vm_refl. Qed.
Lemma D_82a88 : decode_any W_82a88 = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 11%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a8c : bv 32 := @BV 32 0x00083597%Z I.
Lemma F_82a8c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a8c%Z I : word) = Some W_82a8c.
Proof. vm_refl. Qed.
Lemma D_82a8c : decode_any W_82a8c = Some (Auipc (@BV 5 11%Z I) (@BV 20 131%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a90 : bv 32 := @BV 32 0x46c5b903%Z I.
Lemma F_82a90 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a90%Z I : word) = Some W_82a90.
Proof. vm_refl. Qed.
Lemma D_82a90 : decode_any W_82a90 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 11%Z I) (@BV 12 1132%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a94 : bv 32 := @BV 32 0x00093583%Z I.
Lemma F_82a94 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a94%Z I : word) = Some W_82a94.
Proof. vm_refl. Qed.
Lemma D_82a94 : decode_any W_82a94 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a98 : bv 32 := @BV 32 0x00050493%Z I.
Lemma F_82a98 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a98%Z I : word) = Some W_82a98.
Proof. vm_refl. Qed.
Lemma D_82a98 : decode_any W_82a98 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82a9c : bv 32 := @BV 32 0x00059863%Z I.
Lemma F_82a9c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82a9c%Z I : word) = Some W_82a9c.
Proof. vm_refl. Qed.
Lemma D_82a9c : decode_any W_82a9c = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82aac : bv 32 := @BV 32 0xfff58513%Z I.
Lemma F_82aac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82aac%Z I : word) = Some W_82aac.
Proof. vm_refl. Qed.
Lemma D_82aac : decode_any W_82aac = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ab0 : bv 32 := @BV 32 0x00a5f533%Z I.
Lemma F_82ab0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ab0%Z I : word) = Some W_82ab0.
Proof. vm_refl. Qed.
Lemma D_82ab0 : decode_any W_82ab0 = Some (Op ALU_AND (@BV 5 10%Z I) (@BV 5 11%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ab4 : bv 32 := @BV 32 0x08051a63%Z I.
Lemma F_82ab4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ab4%Z I : word) = Some W_82ab4.
Proof. vm_refl. Qed.
Lemma D_82ab4 : decode_any W_82ab4 = Some (Branch BC_NE (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 148%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ab8 : bv 32 := @BV 32 0x00b484b3%Z I.
Lemma F_82ab8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ab8%Z I : word) = Some W_82ab8.
Proof. vm_refl. Qed.
Lemma D_82ab8 : decode_any W_82ab8 = Some (Op ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82abc : bv 32 := @BV 32 0x40b00533%Z I.
Lemma F_82abc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82abc%Z I : word) = Some W_82abc.
Proof. vm_refl. Qed.
Lemma D_82abc : decode_any W_82abc = Some (Op ALU_SUB (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 5 11%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ac0 : bv 32 := @BV 32 0xfff48493%Z I.
Lemma F_82ac0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ac0%Z I : word) = Some W_82ac0.
Proof. vm_refl. Qed.
Lemma D_82ac0 : decode_any W_82ac0 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ac4 : bv 32 := @BV 32 0x00a4f4b3%Z I.
Lemma F_82ac4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ac4%Z I : word) = Some W_82ac4.
Proof. vm_refl. Qed.
Lemma D_82ac4 : decode_any W_82ac4 = Some (Op ALU_AND (@BV 5 9%Z I) (@BV 5 9%Z I) (@BV 5 10%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ac8 : bv 32 := @BV 32 0x02200513%Z I.
Lemma F_82ac8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ac8%Z I : word) = Some W_82ac8.
Proof. vm_refl. Qed.
Lemma D_82ac8 : decode_any W_82ac8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 34%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82acc : bv 32 := @BV 32 0x00a12623%Z I.
Lemma F_82acc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82acc%Z I : word) = Some W_82acc.
Proof. vm_refl. Qed.
Lemma D_82acc : decode_any W_82acc = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ad0 : bv 32 := @BV 32 0x00c10613%Z I.
Lemma F_82ad0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ad0%Z I : word) = Some W_82ad0.
Proof. vm_refl. Qed.
Lemma D_82ad0 : decode_any W_82ad0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 2%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ad4 : bv 32 := @BV 32 0x00040513%Z I.
Lemma F_82ad4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ad4%Z I : word) = Some W_82ad4.
Proof. vm_refl. Qed.
Lemma D_82ad4 : decode_any W_82ad4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ad8 : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_82ad8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ad8%Z I : word) = Some W_82ad8.
Proof. vm_refl. Qed.
Lemma D_82ad8 : decode_any W_82ad8 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82adc : bv 32 := @BV 32 0x279000ef%Z I.
Lemma F_82adc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82adc%Z I : word) = Some W_82adc.
Proof. vm_refl. Qed.
Lemma D_82adc : decode_any W_82adc = Some (Jal (@BV 5 1%Z I) (@BV 21 2680%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ae0 : bv 32 := @BV 32 0x00c12683%Z I.
Lemma F_82ae0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ae0%Z I : word) = Some W_82ae0.
Proof. vm_refl. Qed.
Lemma D_82ae0 : decode_any W_82ae0 = Some (Load SZ4 true (@BV 5 13%Z I) (@BV 5 2%Z I) (@BV 12 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ae4 : bv 32 := @BV 32 0x00050713%Z I.
Lemma F_82ae4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ae4%Z I : word) = Some W_82ae4.
Proof. vm_refl. Qed.
Lemma D_82ae4 : decode_any W_82ae4 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ae8 : bv 32 := @BV 32 0x00300613%Z I.
Lemma F_82ae8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82ae8%Z I : word) = Some W_82ae8.
Proof. vm_refl. Qed.
Lemma D_82ae8 : decode_any W_82ae8 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82aec : bv 32 := @BV 32 0x00000513%Z I.
Lemma F_82aec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82aec%Z I : word) = Some W_82aec.
Proof. vm_refl. Qed.
Lemma D_82aec : decode_any W_82aec = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82af0 : bv 32 := @BV 32 0x00048593%Z I.
Lemma F_82af0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82af0%Z I : word) = Some W_82af0.
Proof. vm_refl. Qed.
Lemma D_82af0 : decode_any W_82af0 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82af4 : bv 32 := @BV 32 0x00000793%Z I.
Lemma F_82af4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82af4%Z I : word) = Some W_82af4.
Proof. vm_refl. Qed.
Lemma D_82af4 : decode_any W_82af4 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82af8 : bv 32 := @BV 32 0xeb0fe0ef%Z I.
Lemma F_82af8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82af8%Z I : word) = Some W_82af8.
Proof. vm_refl. Qed.
Lemma D_82af8 : decode_any W_82af8 = Some (Jal (@BV 5 1%Z I) (@BV 21 2090672%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82afc : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_82afc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82afc%Z I : word) = Some W_82afc.
Proof. vm_refl. Qed.
Lemma D_82afc : decode_any W_82afc = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b00 : bv 32 := @BV 32 0x00000593%Z I.
Lemma F_82b00 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b00%Z I : word) = Some W_82b00.
Proof. vm_refl. Qed.
Lemma D_82b00 : decode_any W_82b00 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b04 : bv 32 := @BV 32 0xe84fe0ef%Z I.
Lemma F_82b04 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b04%Z I : word) = Some W_82b04.
Proof. vm_refl. Qed.
Lemma D_82b04 : decode_any W_82b04 = Some (Jal (@BV 5 1%Z I) (@BV 21 2090628%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b08 : bv 32 := @BV 32 0xaaaab537%Z I.
Lemma F_82b08 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b08%Z I : word) = Some W_82b08.
Proof. vm_refl. Qed.
Lemma D_82b08 : decode_any W_82b08 = Some (Lui (@BV 5 10%Z I) (@BV 20 699051%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b0c : bv 32 := @BV 32 0xaaa50513%Z I.
Lemma F_82b0c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b0c%Z I : word) = Some W_82b0c.
Proof. vm_refl. Qed.
Lemma D_82b0c : decode_any W_82b0c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 2730%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82b10 : bv 32 := @BV 32 0x00a12423%Z I.
Lemma F_82b10 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x82b10%Z I : word) = Some W_82b10.
Proof. vm_refl. Qed.
Lemma D_82b10 : decode_any W_82b10 = Some (Store SZ4 (@BV 5 2%Z I) (@BV 5 10%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.
