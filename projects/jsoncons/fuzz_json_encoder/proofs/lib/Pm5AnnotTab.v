(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition Wx_848b0 : bv 32 := 0x81010113.
Lemma Fx_848b0 : fetch_word AsanUbsan.M.loaded_segments (0x848f8 : word) = Some Wx_848b0.
Proof. vm_refl. Qed.
Lemma Dx_848b0 : decode_any Wx_848b0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848b4 : bv 32 := 0x7e113423.
Lemma Fx_848b4 : fetch_word AsanUbsan.M.loaded_segments (0x848fc : word) = Some Wx_848b4.
Proof. vm_refl. Qed.
Lemma Dx_848b4 : decode_any Wx_848b4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848b8 : bv 32 := 0x7e813023.
Lemma Fx_848b8 : fetch_word AsanUbsan.M.loaded_segments (0x84900 : word) = Some Wx_848b8.
Proof. vm_refl. Qed.
Lemma Dx_848b8 : decode_any Wx_848b8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848bc : bv 32 := 0x7c913c23.
Lemma Fx_848bc : fetch_word AsanUbsan.M.loaded_segments (0x84904 : word) = Some Wx_848bc.
Proof. vm_refl. Qed.
Lemma Dx_848bc : decode_any Wx_848bc = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848c0 : bv 32 := 0x7d213823.
Lemma Fx_848c0 : fetch_word AsanUbsan.M.loaded_segments (0x84908 : word) = Some Wx_848c0.
Proof. vm_refl. Qed.
Lemma Dx_848c0 : decode_any Wx_848c0 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848c4 : bv 32 := 0x7d313423.
Lemma Fx_848c4 : fetch_word AsanUbsan.M.loaded_segments (0x8490c : word) = Some Wx_848c4.
Proof. vm_refl. Qed.
Lemma Dx_848c4 : decode_any Wx_848c4 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848c8 : bv 32 := 0x7d413023.
Lemma Fx_848c8 : fetch_word AsanUbsan.M.loaded_segments (0x84910 : word) = Some Wx_848c8.
Proof. vm_refl. Qed.
Lemma Dx_848c8 : decode_any Wx_848c8 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848cc : bv 32 := 0x7b513c23.
Lemma Fx_848cc : fetch_word AsanUbsan.M.loaded_segments (0x84914 : word) = Some Wx_848cc.
Proof. vm_refl. Qed.
Lemma Dx_848cc : decode_any Wx_848cc = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848d0 : bv 32 := 0x7f010413.
Lemma Fx_848d0 : fetch_word AsanUbsan.M.loaded_segments (0x84918 : word) = Some Wx_848d0.
Proof. vm_refl. Qed.
Lemma Dx_848d0 : decode_any Wx_848d0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848d4 : bv 32 := 0xfa010113.
Lemma Fx_848d4 : fetch_word AsanUbsan.M.loaded_segments (0x8491c : word) = Some Wx_848d4.
Proof. vm_refl. Qed.
Lemma Dx_848d4 : decode_any Wx_848d4 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848d8 : bv 32 := 0x00058a13.
Lemma Fx_848d8 : fetch_word AsanUbsan.M.loaded_segments (0x84920 : word) = Some Wx_848d8.
Proof. vm_refl. Qed.
Lemma Dx_848d8 : decode_any Wx_848d8 = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848dc : bv 32 := 0x000e0597.
Lemma Fx_848dc : fetch_word AsanUbsan.M.loaded_segments (0x84924 : word) = Some Wx_848dc.
Proof. vm_refl. Qed.
Lemma Dx_848dc : decode_any Wx_848dc = Some (Auipc 11 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848e0 : bv 32 := 0xbec5b583.
Lemma Fx_848e0 : fetch_word AsanUbsan.M.loaded_segments (0x84928 : word) = Some Wx_848e0.
Proof. vm_refl. Qed.
Lemma Dx_848e0 : decode_any Wx_848e0 = Some (Load SZ8 true 11 11 3052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848e4 : bv 32 := 0x0605c583.
Lemma Fx_848e4 : fetch_word AsanUbsan.M.loaded_segments (0x8492c : word) = Some Wx_848e4.
Proof. vm_refl. Qed.
Lemma Dx_848e4 : decode_any Wx_848e4 = Some (Load SZ1 false 11 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848e8 : bv 32 := 0x22058863.
Lemma Fx_848e8 : fetch_word AsanUbsan.M.loaded_segments (0x84930 : word) = Some Wx_848e8.
Proof. vm_refl. Qed.
Lemma Dx_848e8 : decode_any Wx_848e8 = Some (Branch BC_EQ 11 0 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848ec : bv 32 := 0x00068913.
Lemma Fx_848ec : fetch_word AsanUbsan.M.loaded_segments (0x84934 : word) = Some Wx_848ec.
Proof. vm_refl. Qed.
Lemma Dx_848ec : decode_any Wx_848ec = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848f0 : bv 32 := 0x00060993.
Lemma Fx_848f0 : fetch_word AsanUbsan.M.loaded_segments (0x84938 : word) = Some Wx_848f0.
Proof. vm_refl. Qed.
Lemma Dx_848f0 : decode_any Wx_848f0 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848f4 : bv 32 := 0x00050493.
Lemma Fx_848f4 : fetch_word AsanUbsan.M.loaded_segments (0x8493c : word) = Some Wx_848f4.
Proof. vm_refl. Qed.
Lemma Dx_848f4 : decode_any Wx_848f4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848f8 : bv 32 := 0x000e0517.
Lemma Fx_848f8 : fetch_word AsanUbsan.M.loaded_segments (0x84940 : word) = Some Wx_848f8.
Proof. vm_refl. Qed.
Lemma Dx_848f8 : decode_any Wx_848f8 = Some (Auipc 10 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_848fc : bv 32 := 0xc2853503.
Lemma Fx_848fc : fetch_word AsanUbsan.M.loaded_segments (0x84944 : word) = Some Wx_848fc.
Proof. vm_refl. Qed.
Lemma Dx_848fc : decode_any Wx_848fc = Some (Load SZ8 true 10 10 3112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84900 : bv 32 := 0x00052503.
Lemma Fx_84900 : fetch_word AsanUbsan.M.loaded_segments (0x84948 : word) = Some Wx_84900.
Proof. vm_refl. Qed.
Lemma Dx_84900 : decode_any Wx_84900 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84904 : bv 32 := 0x00300593.
Lemma Fx_84904 : fetch_word AsanUbsan.M.loaded_segments (0x8494c : word) = Some Wx_84904.
Proof. vm_refl. Qed.
Lemma Dx_84904 : decode_any Wx_84904 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84908 : bv 32 := 0x08b57063.
Lemma Fx_84908 : fetch_word AsanUbsan.M.loaded_segments (0x84950 : word) = Some Wx_84908.
Proof. vm_refl. Qed.
Lemma Dx_84908 : decode_any Wx_84908 = Some (Branch BC_GEU 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8490c : bv 32 := 0x0899fe63.
Lemma Fx_8490c : fetch_word AsanUbsan.M.loaded_segments (0x84954 : word) = Some Wx_8490c.
Proof. vm_refl. Qed.
Lemma Dx_8490c : decode_any Wx_8490c = Some (Branch BC_GEU 19 9 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84910 : bv 32 := 0x80040513.
Lemma Fx_84910 : fetch_word AsanUbsan.M.loaded_segments (0x84958 : word) = Some Wx_84910.
Proof. vm_refl. Qed.
Lemma Dx_84910 : decode_any Wx_84910 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84914 : bv 32 := 0xfb050513.
Lemma Fx_84914 : fetch_word AsanUbsan.M.loaded_segments (0x8495c : word) = Some Wx_84914.
Proof. vm_refl. Qed.
Lemma Dx_84914 : decode_any Wx_84914 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84918 : bv 32 := 0x80040593.
Lemma Fx_84918 : fetch_word AsanUbsan.M.loaded_segments (0x84960 : word) = Some Wx_84918.
Proof. vm_refl. Qed.
Lemma Dx_84918 : decode_any Wx_84918 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8491c : bv 32 := 0xfc058593.
Lemma Fx_8491c : fetch_word AsanUbsan.M.loaded_segments (0x84964 : word) = Some Wx_8491c.
Proof. vm_refl. Qed.
Lemma Dx_8491c : decode_any Wx_8491c = Some (OpImm ALU_ADD 11 11 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84920 : bv 32 := 0x80040613.
Lemma Fx_84920 : fetch_word AsanUbsan.M.loaded_segments (0x84968 : word) = Some Wx_84920.
Proof. vm_refl. Qed.
Lemma Dx_84920 : decode_any Wx_84920 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84924 : bv 32 := 0xfb060613.
Lemma Fx_84924 : fetch_word AsanUbsan.M.loaded_segments (0x8496c : word) = Some Wx_84924.
Proof. vm_refl. Qed.
Lemma Dx_84924 : decode_any Wx_84924 = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84928 : bv 32 := 0x7ff60a93.
Lemma Fx_84928 : fetch_word AsanUbsan.M.loaded_segments (0x84970 : word) = Some Wx_84928.
Proof. vm_refl. Qed.
Lemma Dx_84928 : decode_any Wx_84928 = Some (OpImm ALU_ADD 21 12 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8492c : bv 32 := 0x000ab4a3.
Lemma Fx_8492c : fetch_word AsanUbsan.M.loaded_segments (0x84974 : word) = Some Wx_8492c.
Proof. vm_refl. Qed.
Lemma Dx_8492c : decode_any Wx_8492c = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84930 : bv 32 := 0x00b53023.
Lemma Fx_84930 : fetch_word AsanUbsan.M.loaded_segments (0x84978 : word) = Some Wx_84930.
Proof. vm_refl. Qed.
Lemma Dx_84930 : decode_any Wx_84930 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84934 : bv 32 := 0x00053423.
Lemma Fx_84934 : fetch_word AsanUbsan.M.loaded_segments (0x8497c : word) = Some Wx_84934.
Proof. vm_refl. Qed.
Lemma Dx_84934 : decode_any Wx_84934 = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84938 : bv 32 := 0x6451e0ef.
Lemma Fx_84938 : fetch_word AsanUbsan.M.loaded_segments (0x84980 : word) = Some Wx_84938.
Proof. vm_refl. Qed.
Lemma Dx_84938 : decode_any Wx_84938 = Some (Jal 1 126532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8493c : bv 32 := 0x00050593.
Lemma Fx_8493c : fetch_word AsanUbsan.M.loaded_segments (0x84984 : word) = Some Wx_8493c.
Proof. vm_refl. Qed.
Lemma Dx_8493c : decode_any Wx_8493c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84940 : bv 32 := 0x000e0517.
Lemma Fx_84940 : fetch_word AsanUbsan.M.loaded_segments (0x84988 : word) = Some Wx_84940.
Proof. vm_refl. Qed.
Lemma Dx_84940 : decode_any Wx_84940 = Some (Auipc 10 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84944 : bv 32 := 0xb8053503.
Lemma Fx_84944 : fetch_word AsanUbsan.M.loaded_segments (0x8498c : word) = Some Wx_84944.
Proof. vm_refl. Qed.
Lemma Dx_84944 : decode_any Wx_84944 = Some (Load SZ8 true 10 10 2944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84948 : bv 32 := 0x02154703.
Lemma Fx_84948 : fetch_word AsanUbsan.M.loaded_segments (0x84990 : word) = Some Wx_84948.
Proof. vm_refl. Qed.
Lemma Dx_84948 : decode_any Wx_84948 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8494c : bv 32 := 0x008ab4a3.
Lemma Fx_8494c : fetch_word AsanUbsan.M.loaded_segments (0x84994 : word) = Some Wx_8494c.
Proof. vm_refl. Qed.
Lemma Dx_8494c : decode_any Wx_8494c = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84950 : bv 32 := 0x80040513.
Lemma Fx_84950 : fetch_word AsanUbsan.M.loaded_segments (0x84998 : word) = Some Wx_84950.
Proof. vm_refl. Qed.
Lemma Dx_84950 : decode_any Wx_84950 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84954 : bv 32 := 0xfb050513.
Lemma Fx_84954 : fetch_word AsanUbsan.M.loaded_segments (0x8499c : word) = Some Wx_84954.
Proof. vm_refl. Qed.
Lemma Dx_84954 : decode_any Wx_84954 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84958 : bv 32 := 0x0ff00793.
Lemma Fx_84958 : fetch_word AsanUbsan.M.loaded_segments (0x849a0 : word) = Some Wx_84958.
Proof. vm_refl. Qed.
Lemma Dx_84958 : decode_any Wx_84958 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8495c : bv 32 := 0x00040613.
Lemma Fx_8495c : fetch_word AsanUbsan.M.loaded_segments (0x849a4 : word) = Some Wx_8495c.
Proof. vm_refl. Qed.
Lemma Dx_8495c : decode_any Wx_8495c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84960 : bv 32 := 0x00000693.
Lemma Fx_84960 : fetch_word AsanUbsan.M.loaded_segments (0x849a8 : word) = Some Wx_84960.
Proof. vm_refl. Qed.
Lemma Dx_84960 : decode_any Wx_84960 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84964 : bv 32 := 0x34c060ef.
Lemma Fx_84964 : fetch_word AsanUbsan.M.loaded_segments (0x849ac : word) = Some Wx_84964.
Proof. vm_refl. Qed.
Lemma Dx_84964 : decode_any Wx_84964 = Some (Jal 1 25420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84968 : bv 32 := 0x80040713.
Lemma Fx_84968 : fetch_word AsanUbsan.M.loaded_segments (0x849b0 : word) = Some Wx_84968.
Proof. vm_refl. Qed.
Lemma Dx_84968 : decode_any Wx_84968 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8496c : bv 32 := 0xfb070713.
Lemma Fx_8496c : fetch_word AsanUbsan.M.loaded_segments (0x849b4 : word) = Some Wx_8496c.
Proof. vm_refl. Qed.
Lemma Dx_8496c : decode_any Wx_8496c = Some (OpImm ALU_ADD 14 14 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84970 : bv 32 := 0x00048513.
Lemma Fx_84970 : fetch_word AsanUbsan.M.loaded_segments (0x849b8 : word) = Some Wx_84970.
Proof. vm_refl. Qed.
Lemma Dx_84970 : decode_any Wx_84970 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84974 : bv 32 := 0x000a0593.
Lemma Fx_84974 : fetch_word AsanUbsan.M.loaded_segments (0x849bc : word) = Some Wx_84974.
Proof. vm_refl. Qed.
Lemma Dx_84974 : decode_any Wx_84974 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84978 : bv 32 := 0x00098613.
Lemma Fx_84978 : fetch_word AsanUbsan.M.loaded_segments (0x849c0 : word) = Some Wx_84978.
Proof. vm_refl. Qed.
Lemma Dx_84978 : decode_any Wx_84978 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8497c : bv 32 := 0x00090693.
Lemma Fx_8497c : fetch_word AsanUbsan.M.loaded_segments (0x849c4 : word) = Some Wx_8497c.
Proof. vm_refl. Qed.
Lemma Dx_8497c : decode_any Wx_8497c = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84980 : bv 32 := 0x0e0030ef.
Lemma Fx_84980 : fetch_word AsanUbsan.M.loaded_segments (0x849c8 : word) = Some Wx_84980.
Proof. vm_refl. Qed.
Lemma Dx_84980 : decode_any Wx_84980 = Some (Jal 1 12512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84984 : bv 32 := 0x0300006f.
Lemma Fx_84984 : fetch_word AsanUbsan.M.loaded_segments (0x849cc : word) = Some Wx_84984.
Proof. vm_refl. Qed.
Lemma Dx_84984 : decode_any Wx_84984 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84988 : bv 32 := 0xfff95517.
Lemma Fx_84988 : fetch_word AsanUbsan.M.loaded_segments (0x849d0 : word) = Some Wx_84988.
Proof. vm_refl. Qed.
Lemma Dx_84988 : decode_any Wx_84988 = Some (Auipc 10 1048469, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8498c : bv 32 := 0x45250513.
Lemma Fx_8498c : fetch_word AsanUbsan.M.loaded_segments (0x849d4 : word) = Some Wx_8498c.
Proof. vm_refl. Qed.
Lemma Dx_8498c : decode_any Wx_8498c = Some (OpImm ALU_ADD 10 10 1106, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84990 : bv 32 := 0x00048593.
Lemma Fx_84990 : fetch_word AsanUbsan.M.loaded_segments (0x849d8 : word) = Some Wx_84990.
Proof. vm_refl. Qed.
Lemma Dx_84990 : decode_any Wx_84990 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84994 : bv 32 := 0x000a0613.
Lemma Fx_84994 : fetch_word AsanUbsan.M.loaded_segments (0x849dc : word) = Some Wx_84994.
Proof. vm_refl. Qed.
Lemma Dx_84994 : decode_any Wx_84994 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84998 : bv 32 := 0x00098693.
Lemma Fx_84998 : fetch_word AsanUbsan.M.loaded_segments (0x849e0 : word) = Some Wx_84998.
Proof. vm_refl. Qed.
Lemma Dx_84998 : decode_any Wx_84998 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8499c : bv 32 := 0x00090713.
Lemma Fx_8499c : fetch_word AsanUbsan.M.loaded_segments (0x849e4 : word) = Some Wx_8499c.
Proof. vm_refl. Qed.
Lemma Dx_8499c : decode_any Wx_8499c = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849a0 : bv 32 := 0x491120ef.
Lemma Fx_849a0 : fetch_word AsanUbsan.M.loaded_segments (0x849e8 : word) = Some Wx_849a0.
Proof. vm_refl. Qed.
Lemma Dx_849a0 : decode_any Wx_849a0 = Some (Jal 1 76944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849a4 : bv 32 := 0xf699e6e3.
Lemma Fx_849a4 : fetch_word AsanUbsan.M.loaded_segments (0x849ec : word) = Some Wx_849a4.
Proof. vm_refl. Qed.
Lemma Dx_849a4 : decode_any Wx_849a4 = Some (Branch BC_LTU 19 9 8044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849a8 : bv 32 := 0xf72a64e3.
Lemma Fx_849a8 : fetch_word AsanUbsan.M.loaded_segments (0x849f0 : word) = Some Wx_849a8.
Proof. vm_refl. Qed.
Lemma Dx_849a8 : decode_any Wx_849a8 = Some (Branch BC_LTU 20 18 8040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849ac : bv 32 := 0xf73a62e3.
Lemma Fx_849ac : fetch_word AsanUbsan.M.loaded_segments (0x849f4 : word) = Some Wx_849ac.
Proof. vm_refl. Qed.
Lemma Dx_849ac : decode_any Wx_849ac = Some (Branch BC_LTU 20 19 8036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849b0 : bv 32 := 0xf69960e3.
Lemma Fx_849b0 : fetch_word AsanUbsan.M.loaded_segments (0x849f8 : word) = Some Wx_849b0.
Proof. vm_refl. Qed.
Lemma Dx_849b0 : decode_any Wx_849b0 = Some (Branch BC_LTU 18 9 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849b4 : bv 32 := 0x409a06b3.
Lemma Fx_849b4 : fetch_word AsanUbsan.M.loaded_segments (0x849fc : word) = Some Wx_849b4.
Proof. vm_refl. Qed.
Lemma Dx_849b4 : decode_any Wx_849b4 = Some (Op ALU_SUB 13 20 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849b8 : bv 32 := 0x00100713.
Lemma Fx_849b8 : fetch_word AsanUbsan.M.loaded_segments (0x84a00 : word) = Some Wx_849b8.
Proof. vm_refl. Qed.
Lemma Dx_849b8 : decode_any Wx_849b8 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849bc : bv 32 := 0x02871713.
Lemma Fx_849bc : fetch_word AsanUbsan.M.loaded_segments (0x84a04 : word) = Some Wx_849bc.
Proof. vm_refl. Qed.
Lemma Dx_849bc : decode_any Wx_849bc = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849c0 : bv 32 := 0x00170513.
Lemma Fx_849c0 : fetch_word AsanUbsan.M.loaded_segments (0x84a08 : word) = Some Wx_849c0.
Proof. vm_refl. Qed.
Lemma Dx_849c0 : decode_any Wx_849c0 = Some (OpImm ALU_ADD 10 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849c4 : bv 32 := 0x04a6fa63.
Lemma Fx_849c4 : fetch_word AsanUbsan.M.loaded_segments (0x84a0c : word) = Some Wx_849c4.
Proof. vm_refl. Qed.
Lemma Dx_849c4 : decode_any Wx_849c4 = Some (Branch BC_GEU 13 10 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849c8 : bv 32 := 0x15298863.
Lemma Fx_849c8 : fetch_word AsanUbsan.M.loaded_segments (0x84a10 : word) = Some Wx_849c8.
Proof. vm_refl. Qed.
Lemma Dx_849c8 : decode_any Wx_849c8 = Some (Branch BC_EQ 19 18 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849cc : bv 32 := 0x007a7513.
Lemma Fx_849cc : fetch_word AsanUbsan.M.loaded_segments (0x84a14 : word) = Some Wx_849cc.
Proof. vm_refl. Qed.
Lemma Dx_849cc : decode_any Wx_849cc = Some (OpImm ALU_AND 10 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849d0 : bv 32 := 0x06051063.
Lemma Fx_849d0 : fetch_word AsanUbsan.M.loaded_segments (0x84a18 : word) = Some Wx_849d0.
Proof. vm_refl. Qed.
Lemma Dx_849d0 : decode_any Wx_849d0 = Some (Branch BC_NE 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849d4 : bv 32 := 0x00098a13.
Lemma Fx_849d4 : fetch_word AsanUbsan.M.loaded_segments (0x84a1c : word) = Some Wx_849d4.
Proof. vm_refl. Qed.
Lemma Dx_849d4 : decode_any Wx_849d4 = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849d8 : bv 32 := 0x00090a93.
Lemma Fx_849d8 : fetch_word AsanUbsan.M.loaded_segments (0x84a20 : word) = Some Wx_849d8.
Proof. vm_refl. Qed.
Lemma Dx_849d8 : decode_any Wx_849d8 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849dc : bv 32 := 0x00048513.
Lemma Fx_849dc : fetch_word AsanUbsan.M.loaded_segments (0x84a24 : word) = Some Wx_849dc.
Proof. vm_refl. Qed.
Lemma Dx_849dc : decode_any Wx_849dc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849e0 : bv 32 := 0x0074f993.
Lemma Fx_849e0 : fetch_word AsanUbsan.M.loaded_segments (0x84a28 : word) = Some Wx_849e0.
Proof. vm_refl. Qed.
Lemma Dx_849e0 : decode_any Wx_849e0 = Some (OpImm ALU_AND 19 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849e4 : bv 32 := 0x08099e63.
Lemma Fx_849e4 : fetch_word AsanUbsan.M.loaded_segments (0x84a2c : word) = Some Wx_849e4.
Proof. vm_refl. Qed.
Lemma Dx_849e4 : decode_any Wx_849e4 = Some (Branch BC_NE 19 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849e8 : bv 32 := 0x000a0593.
Lemma Fx_849e8 : fetch_word AsanUbsan.M.loaded_segments (0x84a30 : word) = Some Wx_849e8.
Proof. vm_refl. Qed.
Lemma Dx_849e8 : decode_any Wx_849e8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849ec : bv 32 := 0x000a0513.
Lemma Fx_849ec : fetch_word AsanUbsan.M.loaded_segments (0x84a34 : word) = Some Wx_849ec.
Proof. vm_refl. Qed.
Lemma Dx_849ec : decode_any Wx_849ec = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849f0 : bv 32 := 0x0d5a6863.
Lemma Fx_849f0 : fetch_word AsanUbsan.M.loaded_segments (0x84a38 : word) = Some Wx_849f0.
Proof. vm_refl. Qed.
Lemma Dx_849f0 : decode_any Wx_849f0 = Some (Branch BC_LTU 20 21 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849f4 : bv 32 := 0xff8af513.
Lemma Fx_849f4 : fetch_word AsanUbsan.M.loaded_segments (0x84a3c : word) = Some Wx_849f4.
Proof. vm_refl. Qed.
Lemma Dx_849f4 : decode_any Wx_849f4 = Some (OpImm ALU_AND 10 21 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849f8 : bv 32 := 0x0cbaf863.
Lemma Fx_849f8 : fetch_word AsanUbsan.M.loaded_segments (0x84a40 : word) = Some Wx_849f8.
Proof. vm_refl. Qed.
Lemma Dx_849f8 : decode_any Wx_849f8 = Some (Branch BC_GEU 21 11 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_849fc : bv 32 := 0xff8af493.
Lemma Fx_849fc : fetch_word AsanUbsan.M.loaded_segments (0x84a44 : word) = Some Wx_849fc.
Proof. vm_refl. Qed.
Lemma Dx_849fc : decode_any Wx_849fc = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a00 : bv 32 := 0x007a8613.
Lemma Fx_84a00 : fetch_word AsanUbsan.M.loaded_segments (0x84a48 : word) = Some Wx_84a00.
Proof. vm_refl. Qed.
Lemma Dx_84a00 : decode_any Wx_84a00 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a04 : bv 32 := 0xff867913.
Lemma Fx_84a04 : fetch_word AsanUbsan.M.loaded_segments (0x84a4c : word) = Some Wx_84a04.
Proof. vm_refl. Qed.
Lemma Dx_84a04 : decode_any Wx_84a04 = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a08 : bv 32 := 0x0c957a63.
Lemma Fx_84a08 : fetch_word AsanUbsan.M.loaded_segments (0x84a50 : word) = Some Wx_84a08.
Proof. vm_refl. Qed.
Lemma Dx_84a08 : decode_any Wx_84a08 = Some (Branch BC_GEU 10 9 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a0c : bv 32 := 0x40a485b3.
Lemma Fx_84a0c : fetch_word AsanUbsan.M.loaded_segments (0x84a54 : word) = Some Wx_84a0c.
Proof. vm_refl. Qed.
Lemma Dx_84a0c : decode_any Wx_84a0c = Some (Op ALU_SUB 11 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a10 : bv 32 := 0x00000613.
Lemma Fx_84a10 : fetch_word AsanUbsan.M.loaded_segments (0x84a58 : word) = Some Wx_84a10.
Proof. vm_refl. Qed.
Lemma Dx_84a10 : decode_any Wx_84a10 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a14 : bv 32 := 0x0e00006f.
Lemma Fx_84a14 : fetch_word AsanUbsan.M.loaded_segments (0x84a5c : word) = Some Wx_84a14.
Proof. vm_refl. Qed.
Lemma Dx_84a14 : decode_any Wx_84a14 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a18 : bv 32 := 0xfff9d517.
Lemma Fx_84a18 : fetch_word AsanUbsan.M.loaded_segments (0x84a60 : word) = Some Wx_84a18.
Proof. vm_refl. Qed.
Lemma Dx_84a18 : decode_any Wx_84a18 = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a1c : bv 32 := 0xfff9f597.
Lemma Fx_84a1c : fetch_word AsanUbsan.M.loaded_segments (0x84a64 : word) = Some Wx_84a1c.
Proof. vm_refl. Qed.
Lemma Dx_84a1c : decode_any Wx_84a1c = Some (Auipc 11 1048479, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a20 : bv 32 := 0x7f950513.
Lemma Fx_84a20 : fetch_word AsanUbsan.M.loaded_segments (0x84a68 : word) = Some Wx_84a20.
Proof. vm_refl. Qed.
Lemma Dx_84a20 : decode_any Wx_84a20 = Some (OpImm ALU_ADD 10 10 2041, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a24 : bv 32 := 0x96f58613.
Lemma Fx_84a24 : fetch_word AsanUbsan.M.loaded_segments (0x84a6c : word) = Some Wx_84a24.
Proof. vm_refl. Qed.
Lemma Dx_84a24 : decode_any Wx_84a24 = Some (OpImm ALU_ADD 12 11 2415, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a28 : bv 32 := 0x1b600593.
Lemma Fx_84a28 : fetch_word AsanUbsan.M.loaded_segments (0x84a70 : word) = Some Wx_84a28.
Proof. vm_refl. Qed.
Lemma Dx_84a28 : decode_any Wx_84a28 = Some (OpImm ALU_ADD 11 0 438, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a2c : bv 32 := 0x58c170ef.
Lemma Fx_84a2c : fetch_word AsanUbsan.M.loaded_segments (0x84a74 : word) = Some Wx_84a2c.
Proof. vm_refl. Qed.
Lemma Dx_84a2c : decode_any Wx_84a2c = Some (Jal 1 95628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a30 : bv 32 := 0xff8a7a93.
Lemma Fx_84a30 : fetch_word AsanUbsan.M.loaded_segments (0x84a78 : word) = Some Wx_84a30.
Proof. vm_refl. Qed.
Lemma Dx_84a30 : decode_any Wx_84a30 = Some (OpImm ALU_AND 21 20 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a34 : bv 32 := 0x00098593.
Lemma Fx_84a34 : fetch_word AsanUbsan.M.loaded_segments (0x84a7c : word) = Some Wx_84a34.
Proof. vm_refl. Qed.
Lemma Dx_84a34 : decode_any Wx_84a34 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a38 : bv 32 := 0x01396463.
Lemma Fx_84a38 : fetch_word AsanUbsan.M.loaded_segments (0x84a80 : word) = Some Wx_84a38.
Proof. vm_refl. Qed.
Lemma Dx_84a38 : decode_any Wx_84a38 = Some (Branch BC_LTU 18 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a3c : bv 32 := 0x00090593.
Lemma Fx_84a3c : fetch_word AsanUbsan.M.loaded_segments (0x84a84 : word) = Some Wx_84a3c.
Proof. vm_refl. Qed.
Lemma Dx_84a3c : decode_any Wx_84a3c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a40 : bv 32 := 0xf8bafae3.
Lemma Fx_84a40 : fetch_word AsanUbsan.M.loaded_segments (0x84a88 : word) = Some Wx_84a40.
Proof. vm_refl. Qed.
Lemma Dx_84a40 : decode_any Wx_84a40 = Some (Branch BC_GEU 21 11 8084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a44 : bv 32 := 0x000e0597.
Lemma Fx_84a44 : fetch_word AsanUbsan.M.loaded_segments (0x84a8c : word) = Some Wx_84a44.
Proof. vm_refl. Qed.
Lemma Dx_84a44 : decode_any Wx_84a44 = Some (Auipc 11 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a48 : bv 32 := 0xa8c5b583.
Lemma Fx_84a48 : fetch_word AsanUbsan.M.loaded_segments (0x84a90 : word) = Some Wx_84a48.
Proof. vm_refl. Qed.
Lemma Dx_84a48 : decode_any Wx_84a48 = Some (Load SZ8 true 11 11 2700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a4c : bv 32 := 0x0005b583.
Lemma Fx_84a4c : fetch_word AsanUbsan.M.loaded_segments (0x84a94 : word) = Some Wx_84a4c.
Proof. vm_refl. Qed.
Lemma Dx_84a4c : decode_any Wx_84a4c = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a50 : bv 32 := 0x003a5613.
Lemma Fx_84a50 : fetch_word AsanUbsan.M.loaded_segments (0x84a98 : word) = Some Wx_84a50.
Proof. vm_refl. Qed.
Lemma Dx_84a50 : decode_any Wx_84a50 = Some (ShiftImm ALU_SRL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a54 : bv 32 := 0x00c585b3.
Lemma Fx_84a54 : fetch_word AsanUbsan.M.loaded_segments (0x84a9c : word) = Some Wx_84a54.
Proof. vm_refl. Qed.
Lemma Dx_84a54 : decode_any Wx_84a54 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a58 : bv 32 := 0x00058583.
Lemma Fx_84a58 : fetch_word AsanUbsan.M.loaded_segments (0x84aa0 : word) = Some Wx_84a58.
Proof. vm_refl. Qed.
Lemma Dx_84a58 : decode_any Wx_84a58 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a5c : bv 32 := 0x00058463.
Lemma Fx_84a5c : fetch_word AsanUbsan.M.loaded_segments (0x84aa4 : word) = Some Wx_84a5c.
Proof. vm_refl. Qed.
Lemma Dx_84a5c : decode_any Wx_84a5c = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a60 : bv 32 := 0xf6b55ae3.
Lemma Fx_84a60 : fetch_word AsanUbsan.M.loaded_segments (0x84aa8 : word) = Some Wx_84a60.
Proof. vm_refl. Qed.
Lemma Dx_84a60 : decode_any Wx_84a60 = Some (Branch BC_GE 10 11 8052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a64 : bv 32 := 0x000a8513.
Lemma Fx_84a64 : fetch_word AsanUbsan.M.loaded_segments (0x84aac : word) = Some Wx_84a64.
Proof. vm_refl. Qed.
Lemma Dx_84a64 : decode_any Wx_84a64 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a68 : bv 32 := 0x0e9aea63.
Lemma Fx_84a68 : fetch_word AsanUbsan.M.loaded_segments (0x84ab0 : word) = Some Wx_84a68.
Proof. vm_refl. Qed.
Lemma Dx_84a68 : decode_any Wx_84a68 = Some (Branch BC_LTU 21 9 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a6c : bv 32 := 0x00048513.
Lemma Fx_84a6c : fetch_word AsanUbsan.M.loaded_segments (0x84ab4 : word) = Some Wx_84a6c.
Proof. vm_refl. Qed.
Lemma Dx_84a6c : decode_any Wx_84a6c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a70 : bv 32 := 0x000a8a13.
Lemma Fx_84a70 : fetch_word AsanUbsan.M.loaded_segments (0x84ab8 : word) = Some Wx_84a70.
Proof. vm_refl. Qed.
Lemma Dx_84a70 : decode_any Wx_84a70 = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a74 : bv 32 := 0x0f3af863.
Lemma Fx_84a74 : fetch_word AsanUbsan.M.loaded_segments (0x84abc : word) = Some Wx_84a74.
Proof. vm_refl. Qed.
Lemma Dx_84a74 : decode_any Wx_84a74 = Some (Branch BC_GEU 21 19 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a78 : bv 32 := 0xf72ae4e3.
Lemma Fx_84a78 : fetch_word AsanUbsan.M.loaded_segments (0x84ac0 : word) = Some Wx_84a78.
Proof. vm_refl. Qed.
Lemma Dx_84a78 : decode_any Wx_84a78 = Some (Branch BC_LTU 21 18 8040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a7c : bv 32 := 0x0f00006f.
Lemma Fx_84a7c : fetch_word AsanUbsan.M.loaded_segments (0x84ac4 : word) = Some Wx_84a7c.
Proof. vm_refl. Qed.
Lemma Dx_84a7c : decode_any Wx_84a7c = Some (Jal 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a80 : bv 32 := 0xf74504e3.
Lemma Fx_84a80 : fetch_word AsanUbsan.M.loaded_segments (0x84ac8 : word) = Some Wx_84a80.
Proof. vm_refl. Qed.
Lemma Dx_84a80 : decode_any Wx_84a80 = Some (Branch BC_EQ 10 20 8040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a84 : bv 32 := 0xf75512e3.
Lemma Fx_84a84 : fetch_word AsanUbsan.M.loaded_segments (0x84acc : word) = Some Wx_84a84.
Proof. vm_refl. Qed.
Lemma Dx_84a84 : decode_any Wx_84a84 = Some (Branch BC_NE 10 21 8036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a88 : bv 32 := 0x00748593.
Lemma Fx_84a88 : fetch_word AsanUbsan.M.loaded_segments (0x84ad0 : word) = Some Wx_84a88.
Proof. vm_refl. Qed.
Lemma Dx_84a88 : decode_any Wx_84a88 = Some (OpImm ALU_ADD 11 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a8c : bv 32 := 0xff85f913.
Lemma Fx_84a8c : fetch_word AsanUbsan.M.loaded_segments (0x84ad4 : word) = Some Wx_84a8c.
Proof. vm_refl. Qed.
Lemma Dx_84a8c : decode_any Wx_84a8c = Some (OpImm ALU_AND 18 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a90 : bv 32 := 0xf5257ce3.
Lemma Fx_84a90 : fetch_word AsanUbsan.M.loaded_segments (0x84ad8 : word) = Some Wx_84a90.
Proof. vm_refl. Qed.
Lemma Dx_84a90 : decode_any Wx_84a90 = Some (Branch BC_GEU 10 18 8024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a94 : bv 32 := 0xff84f513.
Lemma Fx_84a94 : fetch_word AsanUbsan.M.loaded_segments (0x84adc : word) = Some Wx_84a94.
Proof. vm_refl. Qed.
Lemma Dx_84a94 : decode_any Wx_84a94 = Some (OpImm ALU_AND 10 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a98 : bv 32 := 0xbd0ff0ef.
Lemma Fx_84a98 : fetch_word AsanUbsan.M.loaded_segments (0x84ae0 : word) = Some Wx_84a98.
Proof. vm_refl. Qed.
Lemma Dx_84a98 : decode_any Wx_84a98 = Some (Jal 1 2094032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84a9c : bv 32 := 0x01350023.
Lemma Fx_84a9c : fetch_word AsanUbsan.M.loaded_segments (0x84ae4 : word) = Some Wx_84a9c.
Proof. vm_refl. Qed.
Lemma Dx_84a9c : decode_any Wx_84a9c = Some (Store SZ1 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84aa0 : bv 32 := 0x00090593.
Lemma Fx_84aa0 : fetch_word AsanUbsan.M.loaded_segments (0x84ae8 : word) = Some Wx_84aa0.
Proof. vm_refl. Qed.
Lemma Dx_84aa0 : decode_any Wx_84aa0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84aa4 : bv 32 := 0x012a6463.
Lemma Fx_84aa4 : fetch_word AsanUbsan.M.loaded_segments (0x84aec : word) = Some Wx_84aa4.
Proof. vm_refl. Qed.
Lemma Dx_84aa4 : decode_any Wx_84aa4 = Some (Branch BC_LTU 20 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84aa8 : bv 32 := 0x000a0593.
Lemma Fx_84aa8 : fetch_word AsanUbsan.M.loaded_segments (0x84af0 : word) = Some Wx_84aa8.
Proof. vm_refl. Qed.
Lemma Dx_84aa8 : decode_any Wx_84aa8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84aac : bv 32 := 0x012ae463.
Lemma Fx_84aac : fetch_word AsanUbsan.M.loaded_segments (0x84af4 : word) = Some Wx_84aac.
Proof. vm_refl. Qed.
Lemma Dx_84aac : decode_any Wx_84aac = Some (Branch BC_LTU 21 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84ab0 : bv 32 := 0x000a8913.
Lemma Fx_84ab0 : fetch_word AsanUbsan.M.loaded_segments (0x84af8 : word) = Some Wx_84ab0.
Proof. vm_refl. Qed.
Lemma Dx_84ab0 : decode_any Wx_84ab0 = Some (OpImm ALU_ADD 18 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84ab4 : bv 32 := 0x00090a93.
Lemma Fx_84ab4 : fetch_word AsanUbsan.M.loaded_segments (0x84afc : word) = Some Wx_84ab4.
Proof. vm_refl. Qed.
Lemma Dx_84ab4 : decode_any Wx_84ab4 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84ab8 : bv 32 := 0x00058513.
Lemma Fx_84ab8 : fetch_word AsanUbsan.M.loaded_segments (0x84b00 : word) = Some Wx_84ab8.
Proof. vm_refl. Qed.
Lemma Dx_84ab8 : decode_any Wx_84ab8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84abc : bv 32 := 0xf325fce3.
Lemma Fx_84abc : fetch_word AsanUbsan.M.loaded_segments (0x84b04 : word) = Some Wx_84abc.
Proof. vm_refl. Qed.
Lemma Dx_84abc : decode_any Wx_84abc = Some (Branch BC_GEU 11 18 7992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84ac0 : bv 32 := 0xff857513.
Lemma Fx_84ac0 : fetch_word AsanUbsan.M.loaded_segments (0x84b08 : word) = Some Wx_84ac0.
Proof. vm_refl. Qed.
Lemma Dx_84ac0 : decode_any Wx_84ac0 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84ac4 : bv 32 := 0xf2baece3.
Lemma Fx_84ac4 : fetch_word AsanUbsan.M.loaded_segments (0x84b0c : word) = Some Wx_84ac4.
Proof. vm_refl. Qed.
Lemma Dx_84ac4 : decode_any Wx_84ac4 = Some (Branch BC_LTU 21 11 7992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84ac8 : bv 32 := 0x000a8593.
Lemma Fx_84ac8 : fetch_word AsanUbsan.M.loaded_segments (0x84b10 : word) = Some Wx_84ac8.
Proof. vm_refl. Qed.
Lemma Dx_84ac8 : decode_any Wx_84ac8 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84acc : bv 32 := 0xff8af493.
Lemma Fx_84acc : fetch_word AsanUbsan.M.loaded_segments (0x84b14 : word) = Some Wx_84acc.
Proof. vm_refl. Qed.
Lemma Dx_84acc : decode_any Wx_84acc = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84ad0 : bv 32 := 0x007a8613.
Lemma Fx_84ad0 : fetch_word AsanUbsan.M.loaded_segments (0x84b18 : word) = Some Wx_84ad0.
Proof. vm_refl. Qed.
Lemma Dx_84ad0 : decode_any Wx_84ad0 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84ad4 : bv 32 := 0xff867913.
Lemma Fx_84ad4 : fetch_word AsanUbsan.M.loaded_segments (0x84b1c : word) = Some Wx_84ad4.
Proof. vm_refl. Qed.
Lemma Dx_84ad4 : decode_any Wx_84ad4 = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84ad8 : bv 32 := 0xf2956ae3.
Lemma Fx_84ad8 : fetch_word AsanUbsan.M.loaded_segments (0x84b20 : word) = Some Wx_84ad8.
Proof. vm_refl. Qed.
Lemma Dx_84ad8 : decode_any Wx_84ad8 = Some (Branch BC_LTU 10 9 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84adc : bv 32 := 0x00758513.
Lemma Fx_84adc : fetch_word AsanUbsan.M.loaded_segments (0x84b24 : word) = Some Wx_84adc.
Proof. vm_refl. Qed.
Lemma Dx_84adc : decode_any Wx_84adc = Some (OpImm ALU_ADD 10 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84ae0 : bv 32 := 0xff857513.
Lemma Fx_84ae0 : fetch_word AsanUbsan.M.loaded_segments (0x84b28 : word) = Some Wx_84ae0.
Proof. vm_refl. Qed.
Lemma Dx_84ae0 : decode_any Wx_84ae0 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84ae4 : bv 32 := 0x00a97a63.
Lemma Fx_84ae4 : fetch_word AsanUbsan.M.loaded_segments (0x84b2c : word) = Some Wx_84ae4.
Proof. vm_refl. Qed.
Lemma Dx_84ae4 : decode_any Wx_84ae4 = Some (Branch BC_GEU 18 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84ae8 : bv 32 := 0x412505b3.
Lemma Fx_84ae8 : fetch_word AsanUbsan.M.loaded_segments (0x84b30 : word) = Some Wx_84ae8.
Proof. vm_refl. Qed.
Lemma Dx_84ae8 : decode_any Wx_84ae8 = Some (Op ALU_SUB 11 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84aec : bv 32 := 0x0fc00613.
Lemma Fx_84aec : fetch_word AsanUbsan.M.loaded_segments (0x84b34 : word) = Some Wx_84aec.
Proof. vm_refl. Qed.
Lemma Dx_84aec : decode_any Wx_84aec = Some (OpImm ALU_ADD 12 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84af0 : bv 32 := 0x00090513.
Lemma Fx_84af0 : fetch_word AsanUbsan.M.loaded_segments (0x84b38 : word) = Some Wx_84af0.
Proof. vm_refl. Qed.
Lemma Dx_84af0 : decode_any Wx_84af0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84af4 : bv 32 := 0xe79fe0ef.
Lemma Fx_84af4 : fetch_word AsanUbsan.M.loaded_segments (0x84b3c : word) = Some Wx_84af4.
Proof. vm_refl. Qed.
Lemma Dx_84af4 : decode_any Wx_84af4 = Some (Jal 1 2092664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84af8 : bv 32 := 0x02990063.
Lemma Fx_84af8 : fetch_word AsanUbsan.M.loaded_segments (0x84b40 : word) = Some Wx_84af8.
Proof. vm_refl. Qed.
Lemma Dx_84af8 : decode_any Wx_84af8 = Some (Branch BC_EQ 18 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84afc : bv 32 := 0x409906b3.
Lemma Fx_84afc : fetch_word AsanUbsan.M.loaded_segments (0x84b44 : word) = Some Wx_84afc.
Proof. vm_refl. Qed.
Lemma Dx_84afc : decode_any Wx_84afc = Some (Op ALU_SUB 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b00 : bv 32 := 0x00800513.
Lemma Fx_84b00 : fetch_word AsanUbsan.M.loaded_segments (0x84b48 : word) = Some Wx_84b00.
Proof. vm_refl. Qed.
Lemma Dx_84b00 : decode_any Wx_84b00 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b04 : bv 32 := 0x02a69e63.
Lemma Fx_84b04 : fetch_word AsanUbsan.M.loaded_segments (0x84b4c : word) = Some Wx_84b04.
Proof. vm_refl. Qed.
Lemma Dx_84b04 : decode_any Wx_84b04 = Some (Branch BC_NE 13 10 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b08 : bv 32 := 0x007af913.
Lemma Fx_84b08 : fetch_word AsanUbsan.M.loaded_segments (0x84b50 : word) = Some Wx_84b08.
Proof. vm_refl. Qed.
Lemma Dx_84b08 : decode_any Wx_84b08 = Some (OpImm ALU_AND 18 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b0c : bv 32 := 0x00048513.
Lemma Fx_84b0c : fetch_word AsanUbsan.M.loaded_segments (0x84b54 : word) = Some Wx_84b0c.
Proof. vm_refl. Qed.
Lemma Dx_84b0c : decode_any Wx_84b0c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b10 : bv 32 := 0xb58ff0ef.
Lemma Fx_84b10 : fetch_word AsanUbsan.M.loaded_segments (0x84b58 : word) = Some Wx_84b10.
Proof. vm_refl. Qed.
Lemma Dx_84b10 : decode_any Wx_84b10 = Some (Jal 1 2093912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b14 : bv 32 := 0x01250023.
Lemma Fx_84b14 : fetch_word AsanUbsan.M.loaded_segments (0x84b5c : word) = Some Wx_84b14.
Proof. vm_refl. Qed.
Lemma Dx_84b14 : decode_any Wx_84b14 = Some (Store SZ1 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b18 : bv 32 := 0x06010113.
Lemma Fx_84b18 : fetch_word AsanUbsan.M.loaded_segments (0x84b60 : word) = Some Wx_84b18.
Proof. vm_refl. Qed.
Lemma Dx_84b18 : decode_any Wx_84b18 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b1c : bv 32 := 0x7e813083.
Lemma Fx_84b1c : fetch_word AsanUbsan.M.loaded_segments (0x84b64 : word) = Some Wx_84b1c.
Proof. vm_refl. Qed.
Lemma Dx_84b1c : decode_any Wx_84b1c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b20 : bv 32 := 0x7e013403.
Lemma Fx_84b20 : fetch_word AsanUbsan.M.loaded_segments (0x84b68 : word) = Some Wx_84b20.
Proof. vm_refl. Qed.
Lemma Dx_84b20 : decode_any Wx_84b20 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b24 : bv 32 := 0x7d813483.
Lemma Fx_84b24 : fetch_word AsanUbsan.M.loaded_segments (0x84b6c : word) = Some Wx_84b24.
Proof. vm_refl. Qed.
Lemma Dx_84b24 : decode_any Wx_84b24 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b28 : bv 32 := 0x7d013903.
Lemma Fx_84b28 : fetch_word AsanUbsan.M.loaded_segments (0x84b70 : word) = Some Wx_84b28.
Proof. vm_refl. Qed.
Lemma Dx_84b28 : decode_any Wx_84b28 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b2c : bv 32 := 0x7c813983.
Lemma Fx_84b2c : fetch_word AsanUbsan.M.loaded_segments (0x84b74 : word) = Some Wx_84b2c.
Proof. vm_refl. Qed.
Lemma Dx_84b2c : decode_any Wx_84b2c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b30 : bv 32 := 0x7c013a03.
Lemma Fx_84b30 : fetch_word AsanUbsan.M.loaded_segments (0x84b78 : word) = Some Wx_84b30.
Proof. vm_refl. Qed.
Lemma Dx_84b30 : decode_any Wx_84b30 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b34 : bv 32 := 0x7b813a83.
Lemma Fx_84b34 : fetch_word AsanUbsan.M.loaded_segments (0x84b7c : word) = Some Wx_84b34.
Proof. vm_refl. Qed.
Lemma Dx_84b34 : decode_any Wx_84b34 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b38 : bv 32 := 0x7f010113.
Lemma Fx_84b38 : fetch_word AsanUbsan.M.loaded_segments (0x84b80 : word) = Some Wx_84b38.
Proof. vm_refl. Qed.
Lemma Dx_84b38 : decode_any Wx_84b38 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b3c : bv 32 := 0x00008067.
Lemma Fx_84b3c : fetch_word AsanUbsan.M.loaded_segments (0x84b84 : word) = Some Wx_84b3c.
Proof. vm_refl. Qed.
Lemma Dx_84b3c : decode_any Wx_84b3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b40 : bv 32 := 0xfff9d517.
Lemma Fx_84b40 : fetch_word AsanUbsan.M.loaded_segments (0x84b88 : word) = Some Wx_84b40.
Proof. vm_refl. Qed.
Lemma Dx_84b40 : decode_any Wx_84b40 = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b44 : bv 32 := 0xfff94617.
Lemma Fx_84b44 : fetch_word AsanUbsan.M.loaded_segments (0x84b8c : word) = Some Wx_84b44.
Proof. vm_refl. Qed.
Lemma Dx_84b44 : decode_any Wx_84b44 = Some (Auipc 12 1048468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b48 : bv 32 := 0x1dc00593.
Lemma Fx_84b48 : fetch_word AsanUbsan.M.loaded_segments (0x84b90 : word) = Some Wx_84b48.
Proof. vm_refl. Qed.
Lemma Dx_84b48 : decode_any Wx_84b48 = Some (OpImm ALU_ADD 11 0 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b4c : bv 32 := 0x6d150513.
Lemma Fx_84b4c : fetch_word AsanUbsan.M.loaded_segments (0x84b94 : word) = Some Wx_84b4c.
Proof. vm_refl. Qed.
Lemma Dx_84b4c : decode_any Wx_84b4c = Some (OpImm ALU_ADD 10 10 1745, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b50 : bv 32 := 0x70d60613.
Lemma Fx_84b50 : fetch_word AsanUbsan.M.loaded_segments (0x84b98 : word) = Some Wx_84b50.
Proof. vm_refl. Qed.
Lemma Dx_84b50 : decode_any Wx_84b50 = Some (OpImm ALU_ADD 12 12 1805, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b54 : bv 32 := 0x00800713.
Lemma Fx_84b54 : fetch_word AsanUbsan.M.loaded_segments (0x84b9c : word) = Some Wx_84b54.
Proof. vm_refl. Qed.
Lemma Dx_84b54 : decode_any Wx_84b54 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b58 : bv 32 := 0x460170ef.
Lemma Fx_84b58 : fetch_word AsanUbsan.M.loaded_segments (0x84ba0 : word) = Some Wx_84b58.
Proof. vm_refl. Qed.
Lemma Dx_84b58 : decode_any Wx_84b58 = Some (Jal 1 95328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b5c : bv 32 := 0x000a8a13.
Lemma Fx_84b5c : fetch_word AsanUbsan.M.loaded_segments (0x84ba4 : word) = Some Wx_84b5c.
Proof. vm_refl. Qed.
Lemma Dx_84b5c : decode_any Wx_84b5c = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b60 : bv 32 := 0xf13aece3.
Lemma Fx_84b60 : fetch_word AsanUbsan.M.loaded_segments (0x84ba8 : word) = Some Wx_84b60.
Proof. vm_refl. Qed.
Lemma Dx_84b60 : decode_any Wx_84b60 = Some (Branch BC_LTU 21 19 7960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b64 : bv 32 := 0x00098a13.
Lemma Fx_84b64 : fetch_word AsanUbsan.M.loaded_segments (0x84bac : word) = Some Wx_84b64.
Proof. vm_refl. Qed.
Lemma Dx_84b64 : decode_any Wx_84b64 = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b68 : bv 32 := 0xe72aece3.
Lemma Fx_84b68 : fetch_word AsanUbsan.M.loaded_segments (0x84bb0 : word) = Some Wx_84b68.
Proof. vm_refl. Qed.
Lemma Dx_84b68 : decode_any Wx_84b68 = Some (Branch BC_LTU 21 18 7800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b6c : bv 32 := 0x00090a93.
Lemma Fx_84b6c : fetch_word AsanUbsan.M.loaded_segments (0x84bb4 : word) = Some Wx_84b6c.
Proof. vm_refl. Qed.
Lemma Dx_84b6c : decode_any Wx_84b6c = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84b70 : bv 32 := 0xe71ff06f.
Lemma Fx_84b70 : fetch_word AsanUbsan.M.loaded_segments (0x84bb8 : word) = Some Wx_84b70.
Proof. vm_refl. Qed.
Lemma Dx_84b70 : decode_any Wx_84b70 = Some (Jal 0 2096752, 4%Z).
Proof. vm_refl. Qed.

