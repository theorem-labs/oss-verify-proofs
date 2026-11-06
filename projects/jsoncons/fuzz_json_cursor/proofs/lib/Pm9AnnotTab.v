(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition Wx_82fd4 : bv 32 := 0x81010113.
Lemma Fx_82fd4 : fetch_word AsanUbsan.M.loaded_segments (0x8301c : word) = Some Wx_82fd4.
Proof. vm_refl. Qed.
Lemma Dx_82fd4 : decode_any Wx_82fd4 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82fd8 : bv 32 := 0x7e113423.
Lemma Fx_82fd8 : fetch_word AsanUbsan.M.loaded_segments (0x83020 : word) = Some Wx_82fd8.
Proof. vm_refl. Qed.
Lemma Dx_82fd8 : decode_any Wx_82fd8 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82fdc : bv 32 := 0x7e813023.
Lemma Fx_82fdc : fetch_word AsanUbsan.M.loaded_segments (0x83024 : word) = Some Wx_82fdc.
Proof. vm_refl. Qed.
Lemma Dx_82fdc : decode_any Wx_82fdc = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82fe0 : bv 32 := 0x7c913c23.
Lemma Fx_82fe0 : fetch_word AsanUbsan.M.loaded_segments (0x83028 : word) = Some Wx_82fe0.
Proof. vm_refl. Qed.
Lemma Dx_82fe0 : decode_any Wx_82fe0 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82fe4 : bv 32 := 0x7d213823.
Lemma Fx_82fe4 : fetch_word AsanUbsan.M.loaded_segments (0x8302c : word) = Some Wx_82fe4.
Proof. vm_refl. Qed.
Lemma Dx_82fe4 : decode_any Wx_82fe4 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82fe8 : bv 32 := 0x7d313423.
Lemma Fx_82fe8 : fetch_word AsanUbsan.M.loaded_segments (0x83030 : word) = Some Wx_82fe8.
Proof. vm_refl. Qed.
Lemma Dx_82fe8 : decode_any Wx_82fe8 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82fec : bv 32 := 0x7d413023.
Lemma Fx_82fec : fetch_word AsanUbsan.M.loaded_segments (0x83034 : word) = Some Wx_82fec.
Proof. vm_refl. Qed.
Lemma Dx_82fec : decode_any Wx_82fec = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ff0 : bv 32 := 0x7b513c23.
Lemma Fx_82ff0 : fetch_word AsanUbsan.M.loaded_segments (0x83038 : word) = Some Wx_82ff0.
Proof. vm_refl. Qed.
Lemma Dx_82ff0 : decode_any Wx_82ff0 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ff4 : bv 32 := 0x7f010413.
Lemma Fx_82ff4 : fetch_word AsanUbsan.M.loaded_segments (0x8303c : word) = Some Wx_82ff4.
Proof. vm_refl. Qed.
Lemma Dx_82ff4 : decode_any Wx_82ff4 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ff8 : bv 32 := 0xfa010113.
Lemma Fx_82ff8 : fetch_word AsanUbsan.M.loaded_segments (0x83040 : word) = Some Wx_82ff8.
Proof. vm_refl. Qed.
Lemma Dx_82ff8 : decode_any Wx_82ff8 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ffc : bv 32 := 0x00058a13.
Lemma Fx_82ffc : fetch_word AsanUbsan.M.loaded_segments (0x83044 : word) = Some Wx_82ffc.
Proof. vm_refl. Qed.
Lemma Dx_82ffc : decode_any Wx_82ffc = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83000 : bv 32 := 0x000d1597.
Lemma Fx_83000 : fetch_word AsanUbsan.M.loaded_segments (0x83048 : word) = Some Wx_83000.
Proof. vm_refl. Qed.
Lemma Dx_83000 : decode_any Wx_83000 = Some (Auipc 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83004 : bv 32 := 0x4b05b583.
Lemma Fx_83004 : fetch_word AsanUbsan.M.loaded_segments (0x8304c : word) = Some Wx_83004.
Proof. vm_refl. Qed.
Lemma Dx_83004 : decode_any Wx_83004 = Some (Load SZ8 true 11 11 1200, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83008 : bv 32 := 0x0605c583.
Lemma Fx_83008 : fetch_word AsanUbsan.M.loaded_segments (0x83050 : word) = Some Wx_83008.
Proof. vm_refl. Qed.
Lemma Dx_83008 : decode_any Wx_83008 = Some (Load SZ1 false 11 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8300c : bv 32 := 0x22058863.
Lemma Fx_8300c : fetch_word AsanUbsan.M.loaded_segments (0x83054 : word) = Some Wx_8300c.
Proof. vm_refl. Qed.
Lemma Dx_8300c : decode_any Wx_8300c = Some (Branch BC_EQ 11 0 560, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83010 : bv 32 := 0x00068913.
Lemma Fx_83010 : fetch_word AsanUbsan.M.loaded_segments (0x83058 : word) = Some Wx_83010.
Proof. vm_refl. Qed.
Lemma Dx_83010 : decode_any Wx_83010 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83014 : bv 32 := 0x00060993.
Lemma Fx_83014 : fetch_word AsanUbsan.M.loaded_segments (0x8305c : word) = Some Wx_83014.
Proof. vm_refl. Qed.
Lemma Dx_83014 : decode_any Wx_83014 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83018 : bv 32 := 0x00050493.
Lemma Fx_83018 : fetch_word AsanUbsan.M.loaded_segments (0x83060 : word) = Some Wx_83018.
Proof. vm_refl. Qed.
Lemma Dx_83018 : decode_any Wx_83018 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8301c : bv 32 := 0x000d1517.
Lemma Fx_8301c : fetch_word AsanUbsan.M.loaded_segments (0x83064 : word) = Some Wx_8301c.
Proof. vm_refl. Qed.
Lemma Dx_8301c : decode_any Wx_8301c = Some (Auipc 10 209, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83020 : bv 32 := 0x4ec53503.
Lemma Fx_83020 : fetch_word AsanUbsan.M.loaded_segments (0x83068 : word) = Some Wx_83020.
Proof. vm_refl. Qed.
Lemma Dx_83020 : decode_any Wx_83020 = Some (Load SZ8 true 10 10 1260, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83024 : bv 32 := 0x00052503.
Lemma Fx_83024 : fetch_word AsanUbsan.M.loaded_segments (0x8306c : word) = Some Wx_83024.
Proof. vm_refl. Qed.
Lemma Dx_83024 : decode_any Wx_83024 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83028 : bv 32 := 0x00300593.
Lemma Fx_83028 : fetch_word AsanUbsan.M.loaded_segments (0x83070 : word) = Some Wx_83028.
Proof. vm_refl. Qed.
Lemma Dx_83028 : decode_any Wx_83028 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8302c : bv 32 := 0x08b57063.
Lemma Fx_8302c : fetch_word AsanUbsan.M.loaded_segments (0x83074 : word) = Some Wx_8302c.
Proof. vm_refl. Qed.
Lemma Dx_8302c : decode_any Wx_8302c = Some (Branch BC_GEU 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83030 : bv 32 := 0x0899fe63.
Lemma Fx_83030 : fetch_word AsanUbsan.M.loaded_segments (0x83078 : word) = Some Wx_83030.
Proof. vm_refl. Qed.
Lemma Dx_83030 : decode_any Wx_83030 = Some (Branch BC_GEU 19 9 156, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83034 : bv 32 := 0x80040513.
Lemma Fx_83034 : fetch_word AsanUbsan.M.loaded_segments (0x8307c : word) = Some Wx_83034.
Proof. vm_refl. Qed.
Lemma Dx_83034 : decode_any Wx_83034 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83038 : bv 32 := 0xfb050513.
Lemma Fx_83038 : fetch_word AsanUbsan.M.loaded_segments (0x83080 : word) = Some Wx_83038.
Proof. vm_refl. Qed.
Lemma Dx_83038 : decode_any Wx_83038 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8303c : bv 32 := 0x80040593.
Lemma Fx_8303c : fetch_word AsanUbsan.M.loaded_segments (0x83084 : word) = Some Wx_8303c.
Proof. vm_refl. Qed.
Lemma Dx_8303c : decode_any Wx_8303c = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83040 : bv 32 := 0xfc058593.
Lemma Fx_83040 : fetch_word AsanUbsan.M.loaded_segments (0x83088 : word) = Some Wx_83040.
Proof. vm_refl. Qed.
Lemma Dx_83040 : decode_any Wx_83040 = Some (OpImm ALU_ADD 11 11 4032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83044 : bv 32 := 0x80040613.
Lemma Fx_83044 : fetch_word AsanUbsan.M.loaded_segments (0x8308c : word) = Some Wx_83044.
Proof. vm_refl. Qed.
Lemma Dx_83044 : decode_any Wx_83044 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83048 : bv 32 := 0xfb060613.
Lemma Fx_83048 : fetch_word AsanUbsan.M.loaded_segments (0x83090 : word) = Some Wx_83048.
Proof. vm_refl. Qed.
Lemma Dx_83048 : decode_any Wx_83048 = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8304c : bv 32 := 0x7ff60a93.
Lemma Fx_8304c : fetch_word AsanUbsan.M.loaded_segments (0x83094 : word) = Some Wx_8304c.
Proof. vm_refl. Qed.
Lemma Dx_8304c : decode_any Wx_8304c = Some (OpImm ALU_ADD 21 12 2047, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83050 : bv 32 := 0x000ab4a3.
Lemma Fx_83050 : fetch_word AsanUbsan.M.loaded_segments (0x83098 : word) = Some Wx_83050.
Proof. vm_refl. Qed.
Lemma Dx_83050 : decode_any Wx_83050 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83054 : bv 32 := 0x00b53023.
Lemma Fx_83054 : fetch_word AsanUbsan.M.loaded_segments (0x8309c : word) = Some Wx_83054.
Proof. vm_refl. Qed.
Lemma Dx_83054 : decode_any Wx_83054 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83058 : bv 32 := 0x00053423.
Lemma Fx_83058 : fetch_word AsanUbsan.M.loaded_segments (0x830a0 : word) = Some Wx_83058.
Proof. vm_refl. Qed.
Lemma Dx_83058 : decode_any Wx_83058 = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8305c : bv 32 := 0x6451e0ef.
Lemma Fx_8305c : fetch_word AsanUbsan.M.loaded_segments (0x830a4 : word) = Some Wx_8305c.
Proof. vm_refl. Qed.
Lemma Dx_8305c : decode_any Wx_8305c = Some (Jal 1 126532, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83060 : bv 32 := 0x00050593.
Lemma Fx_83060 : fetch_word AsanUbsan.M.loaded_segments (0x830a8 : word) = Some Wx_83060.
Proof. vm_refl. Qed.
Lemma Dx_83060 : decode_any Wx_83060 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83064 : bv 32 := 0x000d1517.
Lemma Fx_83064 : fetch_word AsanUbsan.M.loaded_segments (0x830ac : word) = Some Wx_83064.
Proof. vm_refl. Qed.
Lemma Dx_83064 : decode_any Wx_83064 = Some (Auipc 10 209, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83068 : bv 32 := 0x44453503.
Lemma Fx_83068 : fetch_word AsanUbsan.M.loaded_segments (0x830b0 : word) = Some Wx_83068.
Proof. vm_refl. Qed.
Lemma Dx_83068 : decode_any Wx_83068 = Some (Load SZ8 true 10 10 1092, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8306c : bv 32 := 0x02154703.
Lemma Fx_8306c : fetch_word AsanUbsan.M.loaded_segments (0x830b4 : word) = Some Wx_8306c.
Proof. vm_refl. Qed.
Lemma Dx_8306c : decode_any Wx_8306c = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83070 : bv 32 := 0x008ab4a3.
Lemma Fx_83070 : fetch_word AsanUbsan.M.loaded_segments (0x830b8 : word) = Some Wx_83070.
Proof. vm_refl. Qed.
Lemma Dx_83070 : decode_any Wx_83070 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83074 : bv 32 := 0x80040513.
Lemma Fx_83074 : fetch_word AsanUbsan.M.loaded_segments (0x830bc : word) = Some Wx_83074.
Proof. vm_refl. Qed.
Lemma Dx_83074 : decode_any Wx_83074 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83078 : bv 32 := 0xfb050513.
Lemma Fx_83078 : fetch_word AsanUbsan.M.loaded_segments (0x830c0 : word) = Some Wx_83078.
Proof. vm_refl. Qed.
Lemma Dx_83078 : decode_any Wx_83078 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8307c : bv 32 := 0x0ff00793.
Lemma Fx_8307c : fetch_word AsanUbsan.M.loaded_segments (0x830c4 : word) = Some Wx_8307c.
Proof. vm_refl. Qed.
Lemma Dx_8307c : decode_any Wx_8307c = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83080 : bv 32 := 0x00040613.
Lemma Fx_83080 : fetch_word AsanUbsan.M.loaded_segments (0x830c8 : word) = Some Wx_83080.
Proof. vm_refl. Qed.
Lemma Dx_83080 : decode_any Wx_83080 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83084 : bv 32 := 0x00000693.
Lemma Fx_83084 : fetch_word AsanUbsan.M.loaded_segments (0x830cc : word) = Some Wx_83084.
Proof. vm_refl. Qed.
Lemma Dx_83084 : decode_any Wx_83084 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83088 : bv 32 := 0x34c060ef.
Lemma Fx_83088 : fetch_word AsanUbsan.M.loaded_segments (0x830d0 : word) = Some Wx_83088.
Proof. vm_refl. Qed.
Lemma Dx_83088 : decode_any Wx_83088 = Some (Jal 1 25420, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8308c : bv 32 := 0x80040713.
Lemma Fx_8308c : fetch_word AsanUbsan.M.loaded_segments (0x830d4 : word) = Some Wx_8308c.
Proof. vm_refl. Qed.
Lemma Dx_8308c : decode_any Wx_8308c = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83090 : bv 32 := 0xfb070713.
Lemma Fx_83090 : fetch_word AsanUbsan.M.loaded_segments (0x830d8 : word) = Some Wx_83090.
Proof. vm_refl. Qed.
Lemma Dx_83090 : decode_any Wx_83090 = Some (OpImm ALU_ADD 14 14 4016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83094 : bv 32 := 0x00048513.
Lemma Fx_83094 : fetch_word AsanUbsan.M.loaded_segments (0x830dc : word) = Some Wx_83094.
Proof. vm_refl. Qed.
Lemma Dx_83094 : decode_any Wx_83094 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83098 : bv 32 := 0x000a0593.
Lemma Fx_83098 : fetch_word AsanUbsan.M.loaded_segments (0x830e0 : word) = Some Wx_83098.
Proof. vm_refl. Qed.
Lemma Dx_83098 : decode_any Wx_83098 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8309c : bv 32 := 0x00098613.
Lemma Fx_8309c : fetch_word AsanUbsan.M.loaded_segments (0x830e4 : word) = Some Wx_8309c.
Proof. vm_refl. Qed.
Lemma Dx_8309c : decode_any Wx_8309c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830a0 : bv 32 := 0x00090693.
Lemma Fx_830a0 : fetch_word AsanUbsan.M.loaded_segments (0x830e8 : word) = Some Wx_830a0.
Proof. vm_refl. Qed.
Lemma Dx_830a0 : decode_any Wx_830a0 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830a4 : bv 32 := 0x0e0030ef.
Lemma Fx_830a4 : fetch_word AsanUbsan.M.loaded_segments (0x830ec : word) = Some Wx_830a4.
Proof. vm_refl. Qed.
Lemma Dx_830a4 : decode_any Wx_830a4 = Some (Jal 1 12512, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830a8 : bv 32 := 0x0300006f.
Lemma Fx_830a8 : fetch_word AsanUbsan.M.loaded_segments (0x830f0 : word) = Some Wx_830a8.
Proof. vm_refl. Qed.
Lemma Dx_830a8 : decode_any Wx_830a8 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830ac : bv 32 := 0xfff97517.
Lemma Fx_830ac : fetch_word AsanUbsan.M.loaded_segments (0x830f4 : word) = Some Wx_830ac.
Proof. vm_refl. Qed.
Lemma Dx_830ac : decode_any Wx_830ac = Some (Auipc 10 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830b0 : bv 32 := 0x98c50513.
Lemma Fx_830b0 : fetch_word AsanUbsan.M.loaded_segments (0x830f8 : word) = Some Wx_830b0.
Proof. vm_refl. Qed.
Lemma Dx_830b0 : decode_any Wx_830b0 = Some (OpImm ALU_ADD 10 10 2444, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830b4 : bv 32 := 0x00048593.
Lemma Fx_830b4 : fetch_word AsanUbsan.M.loaded_segments (0x830fc : word) = Some Wx_830b4.
Proof. vm_refl. Qed.
Lemma Dx_830b4 : decode_any Wx_830b4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830b8 : bv 32 := 0x000a0613.
Lemma Fx_830b8 : fetch_word AsanUbsan.M.loaded_segments (0x83100 : word) = Some Wx_830b8.
Proof. vm_refl. Qed.
Lemma Dx_830b8 : decode_any Wx_830b8 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830bc : bv 32 := 0x00098693.
Lemma Fx_830bc : fetch_word AsanUbsan.M.loaded_segments (0x83104 : word) = Some Wx_830bc.
Proof. vm_refl. Qed.
Lemma Dx_830bc : decode_any Wx_830bc = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830c0 : bv 32 := 0x00090713.
Lemma Fx_830c0 : fetch_word AsanUbsan.M.loaded_segments (0x83108 : word) = Some Wx_830c0.
Proof. vm_refl. Qed.
Lemma Dx_830c0 : decode_any Wx_830c0 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830c4 : bv 32 := 0x491120ef.
Lemma Fx_830c4 : fetch_word AsanUbsan.M.loaded_segments (0x8310c : word) = Some Wx_830c4.
Proof. vm_refl. Qed.
Lemma Dx_830c4 : decode_any Wx_830c4 = Some (Jal 1 76944, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830c8 : bv 32 := 0xf699e6e3.
Lemma Fx_830c8 : fetch_word AsanUbsan.M.loaded_segments (0x83110 : word) = Some Wx_830c8.
Proof. vm_refl. Qed.
Lemma Dx_830c8 : decode_any Wx_830c8 = Some (Branch BC_LTU 19 9 8044, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830cc : bv 32 := 0xf72a64e3.
Lemma Fx_830cc : fetch_word AsanUbsan.M.loaded_segments (0x83114 : word) = Some Wx_830cc.
Proof. vm_refl. Qed.
Lemma Dx_830cc : decode_any Wx_830cc = Some (Branch BC_LTU 20 18 8040, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830d0 : bv 32 := 0xf73a62e3.
Lemma Fx_830d0 : fetch_word AsanUbsan.M.loaded_segments (0x83118 : word) = Some Wx_830d0.
Proof. vm_refl. Qed.
Lemma Dx_830d0 : decode_any Wx_830d0 = Some (Branch BC_LTU 20 19 8036, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830d4 : bv 32 := 0xf69960e3.
Lemma Fx_830d4 : fetch_word AsanUbsan.M.loaded_segments (0x8311c : word) = Some Wx_830d4.
Proof. vm_refl. Qed.
Lemma Dx_830d4 : decode_any Wx_830d4 = Some (Branch BC_LTU 18 9 8032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830d8 : bv 32 := 0x409a06b3.
Lemma Fx_830d8 : fetch_word AsanUbsan.M.loaded_segments (0x83120 : word) = Some Wx_830d8.
Proof. vm_refl. Qed.
Lemma Dx_830d8 : decode_any Wx_830d8 = Some (Op ALU_SUB 13 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830dc : bv 32 := 0x00100713.
Lemma Fx_830dc : fetch_word AsanUbsan.M.loaded_segments (0x83124 : word) = Some Wx_830dc.
Proof. vm_refl. Qed.
Lemma Dx_830dc : decode_any Wx_830dc = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830e0 : bv 32 := 0x02871713.
Lemma Fx_830e0 : fetch_word AsanUbsan.M.loaded_segments (0x83128 : word) = Some Wx_830e0.
Proof. vm_refl. Qed.
Lemma Dx_830e0 : decode_any Wx_830e0 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830e4 : bv 32 := 0x00170513.
Lemma Fx_830e4 : fetch_word AsanUbsan.M.loaded_segments (0x8312c : word) = Some Wx_830e4.
Proof. vm_refl. Qed.
Lemma Dx_830e4 : decode_any Wx_830e4 = Some (OpImm ALU_ADD 10 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830e8 : bv 32 := 0x04a6fa63.
Lemma Fx_830e8 : fetch_word AsanUbsan.M.loaded_segments (0x83130 : word) = Some Wx_830e8.
Proof. vm_refl. Qed.
Lemma Dx_830e8 : decode_any Wx_830e8 = Some (Branch BC_GEU 13 10 84, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830ec : bv 32 := 0x15298863.
Lemma Fx_830ec : fetch_word AsanUbsan.M.loaded_segments (0x83134 : word) = Some Wx_830ec.
Proof. vm_refl. Qed.
Lemma Dx_830ec : decode_any Wx_830ec = Some (Branch BC_EQ 19 18 336, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830f0 : bv 32 := 0x007a7513.
Lemma Fx_830f0 : fetch_word AsanUbsan.M.loaded_segments (0x83138 : word) = Some Wx_830f0.
Proof. vm_refl. Qed.
Lemma Dx_830f0 : decode_any Wx_830f0 = Some (OpImm ALU_AND 10 20 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830f4 : bv 32 := 0x06051063.
Lemma Fx_830f4 : fetch_word AsanUbsan.M.loaded_segments (0x8313c : word) = Some Wx_830f4.
Proof. vm_refl. Qed.
Lemma Dx_830f4 : decode_any Wx_830f4 = Some (Branch BC_NE 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830f8 : bv 32 := 0x00098a13.
Lemma Fx_830f8 : fetch_word AsanUbsan.M.loaded_segments (0x83140 : word) = Some Wx_830f8.
Proof. vm_refl. Qed.
Lemma Dx_830f8 : decode_any Wx_830f8 = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_830fc : bv 32 := 0x00090a93.
Lemma Fx_830fc : fetch_word AsanUbsan.M.loaded_segments (0x83144 : word) = Some Wx_830fc.
Proof. vm_refl. Qed.
Lemma Dx_830fc : decode_any Wx_830fc = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83100 : bv 32 := 0x00048513.
Lemma Fx_83100 : fetch_word AsanUbsan.M.loaded_segments (0x83148 : word) = Some Wx_83100.
Proof. vm_refl. Qed.
Lemma Dx_83100 : decode_any Wx_83100 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83104 : bv 32 := 0x0074f993.
Lemma Fx_83104 : fetch_word AsanUbsan.M.loaded_segments (0x8314c : word) = Some Wx_83104.
Proof. vm_refl. Qed.
Lemma Dx_83104 : decode_any Wx_83104 = Some (OpImm ALU_AND 19 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83108 : bv 32 := 0x08099e63.
Lemma Fx_83108 : fetch_word AsanUbsan.M.loaded_segments (0x83150 : word) = Some Wx_83108.
Proof. vm_refl. Qed.
Lemma Dx_83108 : decode_any Wx_83108 = Some (Branch BC_NE 19 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8310c : bv 32 := 0x000a0593.
Lemma Fx_8310c : fetch_word AsanUbsan.M.loaded_segments (0x83154 : word) = Some Wx_8310c.
Proof. vm_refl. Qed.
Lemma Dx_8310c : decode_any Wx_8310c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83110 : bv 32 := 0x000a0513.
Lemma Fx_83110 : fetch_word AsanUbsan.M.loaded_segments (0x83158 : word) = Some Wx_83110.
Proof. vm_refl. Qed.
Lemma Dx_83110 : decode_any Wx_83110 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83114 : bv 32 := 0x0d5a6863.
Lemma Fx_83114 : fetch_word AsanUbsan.M.loaded_segments (0x8315c : word) = Some Wx_83114.
Proof. vm_refl. Qed.
Lemma Dx_83114 : decode_any Wx_83114 = Some (Branch BC_LTU 20 21 208, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83118 : bv 32 := 0xff8af513.
Lemma Fx_83118 : fetch_word AsanUbsan.M.loaded_segments (0x83160 : word) = Some Wx_83118.
Proof. vm_refl. Qed.
Lemma Dx_83118 : decode_any Wx_83118 = Some (OpImm ALU_AND 10 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8311c : bv 32 := 0x0cbaf863.
Lemma Fx_8311c : fetch_word AsanUbsan.M.loaded_segments (0x83164 : word) = Some Wx_8311c.
Proof. vm_refl. Qed.
Lemma Dx_8311c : decode_any Wx_8311c = Some (Branch BC_GEU 21 11 208, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83120 : bv 32 := 0xff8af493.
Lemma Fx_83120 : fetch_word AsanUbsan.M.loaded_segments (0x83168 : word) = Some Wx_83120.
Proof. vm_refl. Qed.
Lemma Dx_83120 : decode_any Wx_83120 = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83124 : bv 32 := 0x007a8613.
Lemma Fx_83124 : fetch_word AsanUbsan.M.loaded_segments (0x8316c : word) = Some Wx_83124.
Proof. vm_refl. Qed.
Lemma Dx_83124 : decode_any Wx_83124 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83128 : bv 32 := 0xff867913.
Lemma Fx_83128 : fetch_word AsanUbsan.M.loaded_segments (0x83170 : word) = Some Wx_83128.
Proof. vm_refl. Qed.
Lemma Dx_83128 : decode_any Wx_83128 = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8312c : bv 32 := 0x0c957a63.
Lemma Fx_8312c : fetch_word AsanUbsan.M.loaded_segments (0x83174 : word) = Some Wx_8312c.
Proof. vm_refl. Qed.
Lemma Dx_8312c : decode_any Wx_8312c = Some (Branch BC_GEU 10 9 212, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83130 : bv 32 := 0x40a485b3.
Lemma Fx_83130 : fetch_word AsanUbsan.M.loaded_segments (0x83178 : word) = Some Wx_83130.
Proof. vm_refl. Qed.
Lemma Dx_83130 : decode_any Wx_83130 = Some (Op ALU_SUB 11 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83134 : bv 32 := 0x00000613.
Lemma Fx_83134 : fetch_word AsanUbsan.M.loaded_segments (0x8317c : word) = Some Wx_83134.
Proof. vm_refl. Qed.
Lemma Dx_83134 : decode_any Wx_83134 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83138 : bv 32 := 0x0e00006f.
Lemma Fx_83138 : fetch_word AsanUbsan.M.loaded_segments (0x83180 : word) = Some Wx_83138.
Proof. vm_refl. Qed.
Lemma Dx_83138 : decode_any Wx_83138 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8313c : bv 32 := 0xfff9f517.
Lemma Fx_8313c : fetch_word AsanUbsan.M.loaded_segments (0x83184 : word) = Some Wx_8313c.
Proof. vm_refl. Qed.
Lemma Dx_8313c : decode_any Wx_8313c = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83140 : bv 32 := 0xfffa0597.
Lemma Fx_83140 : fetch_word AsanUbsan.M.loaded_segments (0x83188 : word) = Some Wx_83140.
Proof. vm_refl. Qed.
Lemma Dx_83140 : decode_any Wx_83140 = Some (Auipc 11 1048480, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83144 : bv 32 := 0xb4b50513.
Lemma Fx_83144 : fetch_word AsanUbsan.M.loaded_segments (0x8318c : word) = Some Wx_83144.
Proof. vm_refl. Qed.
Lemma Dx_83144 : decode_any Wx_83144 = Some (OpImm ALU_ADD 10 10 2891, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83148 : bv 32 := 0xd0358613.
Lemma Fx_83148 : fetch_word AsanUbsan.M.loaded_segments (0x83190 : word) = Some Wx_83148.
Proof. vm_refl. Qed.
Lemma Dx_83148 : decode_any Wx_83148 = Some (OpImm ALU_ADD 12 11 3331, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8314c : bv 32 := 0x1b600593.
Lemma Fx_8314c : fetch_word AsanUbsan.M.loaded_segments (0x83194 : word) = Some Wx_8314c.
Proof. vm_refl. Qed.
Lemma Dx_8314c : decode_any Wx_8314c = Some (OpImm ALU_ADD 11 0 438, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83150 : bv 32 := 0x58c170ef.
Lemma Fx_83150 : fetch_word AsanUbsan.M.loaded_segments (0x83198 : word) = Some Wx_83150.
Proof. vm_refl. Qed.
Lemma Dx_83150 : decode_any Wx_83150 = Some (Jal 1 95628, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83154 : bv 32 := 0xff8a7a93.
Lemma Fx_83154 : fetch_word AsanUbsan.M.loaded_segments (0x8319c : word) = Some Wx_83154.
Proof. vm_refl. Qed.
Lemma Dx_83154 : decode_any Wx_83154 = Some (OpImm ALU_AND 21 20 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83158 : bv 32 := 0x00098593.
Lemma Fx_83158 : fetch_word AsanUbsan.M.loaded_segments (0x831a0 : word) = Some Wx_83158.
Proof. vm_refl. Qed.
Lemma Dx_83158 : decode_any Wx_83158 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8315c : bv 32 := 0x01396463.
Lemma Fx_8315c : fetch_word AsanUbsan.M.loaded_segments (0x831a4 : word) = Some Wx_8315c.
Proof. vm_refl. Qed.
Lemma Dx_8315c : decode_any Wx_8315c = Some (Branch BC_LTU 18 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83160 : bv 32 := 0x00090593.
Lemma Fx_83160 : fetch_word AsanUbsan.M.loaded_segments (0x831a8 : word) = Some Wx_83160.
Proof. vm_refl. Qed.
Lemma Dx_83160 : decode_any Wx_83160 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83164 : bv 32 := 0xf8bafae3.
Lemma Fx_83164 : fetch_word AsanUbsan.M.loaded_segments (0x831ac : word) = Some Wx_83164.
Proof. vm_refl. Qed.
Lemma Dx_83164 : decode_any Wx_83164 = Some (Branch BC_GEU 21 11 8084, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83168 : bv 32 := 0x000d1597.
Lemma Fx_83168 : fetch_word AsanUbsan.M.loaded_segments (0x831b0 : word) = Some Wx_83168.
Proof. vm_refl. Qed.
Lemma Dx_83168 : decode_any Wx_83168 = Some (Auipc 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8316c : bv 32 := 0x3505b583.
Lemma Fx_8316c : fetch_word AsanUbsan.M.loaded_segments (0x831b4 : word) = Some Wx_8316c.
Proof. vm_refl. Qed.
Lemma Dx_8316c : decode_any Wx_8316c = Some (Load SZ8 true 11 11 848, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83170 : bv 32 := 0x0005b583.
Lemma Fx_83170 : fetch_word AsanUbsan.M.loaded_segments (0x831b8 : word) = Some Wx_83170.
Proof. vm_refl. Qed.
Lemma Dx_83170 : decode_any Wx_83170 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83174 : bv 32 := 0x003a5613.
Lemma Fx_83174 : fetch_word AsanUbsan.M.loaded_segments (0x831bc : word) = Some Wx_83174.
Proof. vm_refl. Qed.
Lemma Dx_83174 : decode_any Wx_83174 = Some (ShiftImm ALU_SRL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83178 : bv 32 := 0x00c585b3.
Lemma Fx_83178 : fetch_word AsanUbsan.M.loaded_segments (0x831c0 : word) = Some Wx_83178.
Proof. vm_refl. Qed.
Lemma Dx_83178 : decode_any Wx_83178 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8317c : bv 32 := 0x00058583.
Lemma Fx_8317c : fetch_word AsanUbsan.M.loaded_segments (0x831c4 : word) = Some Wx_8317c.
Proof. vm_refl. Qed.
Lemma Dx_8317c : decode_any Wx_8317c = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83180 : bv 32 := 0x00058463.
Lemma Fx_83180 : fetch_word AsanUbsan.M.loaded_segments (0x831c8 : word) = Some Wx_83180.
Proof. vm_refl. Qed.
Lemma Dx_83180 : decode_any Wx_83180 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83184 : bv 32 := 0xf6b55ae3.
Lemma Fx_83184 : fetch_word AsanUbsan.M.loaded_segments (0x831cc : word) = Some Wx_83184.
Proof. vm_refl. Qed.
Lemma Dx_83184 : decode_any Wx_83184 = Some (Branch BC_GE 10 11 8052, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83188 : bv 32 := 0x000a8513.
Lemma Fx_83188 : fetch_word AsanUbsan.M.loaded_segments (0x831d0 : word) = Some Wx_83188.
Proof. vm_refl. Qed.
Lemma Dx_83188 : decode_any Wx_83188 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8318c : bv 32 := 0x0e9aea63.
Lemma Fx_8318c : fetch_word AsanUbsan.M.loaded_segments (0x831d4 : word) = Some Wx_8318c.
Proof. vm_refl. Qed.
Lemma Dx_8318c : decode_any Wx_8318c = Some (Branch BC_LTU 21 9 244, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83190 : bv 32 := 0x00048513.
Lemma Fx_83190 : fetch_word AsanUbsan.M.loaded_segments (0x831d8 : word) = Some Wx_83190.
Proof. vm_refl. Qed.
Lemma Dx_83190 : decode_any Wx_83190 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83194 : bv 32 := 0x000a8a13.
Lemma Fx_83194 : fetch_word AsanUbsan.M.loaded_segments (0x831dc : word) = Some Wx_83194.
Proof. vm_refl. Qed.
Lemma Dx_83194 : decode_any Wx_83194 = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83198 : bv 32 := 0x0f3af863.
Lemma Fx_83198 : fetch_word AsanUbsan.M.loaded_segments (0x831e0 : word) = Some Wx_83198.
Proof. vm_refl. Qed.
Lemma Dx_83198 : decode_any Wx_83198 = Some (Branch BC_GEU 21 19 240, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8319c : bv 32 := 0xf72ae4e3.
Lemma Fx_8319c : fetch_word AsanUbsan.M.loaded_segments (0x831e4 : word) = Some Wx_8319c.
Proof. vm_refl. Qed.
Lemma Dx_8319c : decode_any Wx_8319c = Some (Branch BC_LTU 21 18 8040, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831a0 : bv 32 := 0x0f00006f.
Lemma Fx_831a0 : fetch_word AsanUbsan.M.loaded_segments (0x831e8 : word) = Some Wx_831a0.
Proof. vm_refl. Qed.
Lemma Dx_831a0 : decode_any Wx_831a0 = Some (Jal 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831a4 : bv 32 := 0xf74504e3.
Lemma Fx_831a4 : fetch_word AsanUbsan.M.loaded_segments (0x831ec : word) = Some Wx_831a4.
Proof. vm_refl. Qed.
Lemma Dx_831a4 : decode_any Wx_831a4 = Some (Branch BC_EQ 10 20 8040, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831a8 : bv 32 := 0xf75512e3.
Lemma Fx_831a8 : fetch_word AsanUbsan.M.loaded_segments (0x831f0 : word) = Some Wx_831a8.
Proof. vm_refl. Qed.
Lemma Dx_831a8 : decode_any Wx_831a8 = Some (Branch BC_NE 10 21 8036, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831ac : bv 32 := 0x00748593.
Lemma Fx_831ac : fetch_word AsanUbsan.M.loaded_segments (0x831f4 : word) = Some Wx_831ac.
Proof. vm_refl. Qed.
Lemma Dx_831ac : decode_any Wx_831ac = Some (OpImm ALU_ADD 11 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831b0 : bv 32 := 0xff85f913.
Lemma Fx_831b0 : fetch_word AsanUbsan.M.loaded_segments (0x831f8 : word) = Some Wx_831b0.
Proof. vm_refl. Qed.
Lemma Dx_831b0 : decode_any Wx_831b0 = Some (OpImm ALU_AND 18 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831b4 : bv 32 := 0xf5257ce3.
Lemma Fx_831b4 : fetch_word AsanUbsan.M.loaded_segments (0x831fc : word) = Some Wx_831b4.
Proof. vm_refl. Qed.
Lemma Dx_831b4 : decode_any Wx_831b4 = Some (Branch BC_GEU 10 18 8024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831b8 : bv 32 := 0xff84f513.
Lemma Fx_831b8 : fetch_word AsanUbsan.M.loaded_segments (0x83200 : word) = Some Wx_831b8.
Proof. vm_refl. Qed.
Lemma Dx_831b8 : decode_any Wx_831b8 = Some (OpImm ALU_AND 10 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831bc : bv 32 := 0xbd0ff0ef.
Lemma Fx_831bc : fetch_word AsanUbsan.M.loaded_segments (0x83204 : word) = Some Wx_831bc.
Proof. vm_refl. Qed.
Lemma Dx_831bc : decode_any Wx_831bc = Some (Jal 1 2094032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831c0 : bv 32 := 0x01350023.
Lemma Fx_831c0 : fetch_word AsanUbsan.M.loaded_segments (0x83208 : word) = Some Wx_831c0.
Proof. vm_refl. Qed.
Lemma Dx_831c0 : decode_any Wx_831c0 = Some (Store SZ1 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831c4 : bv 32 := 0x00090593.
Lemma Fx_831c4 : fetch_word AsanUbsan.M.loaded_segments (0x8320c : word) = Some Wx_831c4.
Proof. vm_refl. Qed.
Lemma Dx_831c4 : decode_any Wx_831c4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831c8 : bv 32 := 0x012a6463.
Lemma Fx_831c8 : fetch_word AsanUbsan.M.loaded_segments (0x83210 : word) = Some Wx_831c8.
Proof. vm_refl. Qed.
Lemma Dx_831c8 : decode_any Wx_831c8 = Some (Branch BC_LTU 20 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831cc : bv 32 := 0x000a0593.
Lemma Fx_831cc : fetch_word AsanUbsan.M.loaded_segments (0x83214 : word) = Some Wx_831cc.
Proof. vm_refl. Qed.
Lemma Dx_831cc : decode_any Wx_831cc = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831d0 : bv 32 := 0x012ae463.
Lemma Fx_831d0 : fetch_word AsanUbsan.M.loaded_segments (0x83218 : word) = Some Wx_831d0.
Proof. vm_refl. Qed.
Lemma Dx_831d0 : decode_any Wx_831d0 = Some (Branch BC_LTU 21 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831d4 : bv 32 := 0x000a8913.
Lemma Fx_831d4 : fetch_word AsanUbsan.M.loaded_segments (0x8321c : word) = Some Wx_831d4.
Proof. vm_refl. Qed.
Lemma Dx_831d4 : decode_any Wx_831d4 = Some (OpImm ALU_ADD 18 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831d8 : bv 32 := 0x00090a93.
Lemma Fx_831d8 : fetch_word AsanUbsan.M.loaded_segments (0x83220 : word) = Some Wx_831d8.
Proof. vm_refl. Qed.
Lemma Dx_831d8 : decode_any Wx_831d8 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831dc : bv 32 := 0x00058513.
Lemma Fx_831dc : fetch_word AsanUbsan.M.loaded_segments (0x83224 : word) = Some Wx_831dc.
Proof. vm_refl. Qed.
Lemma Dx_831dc : decode_any Wx_831dc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831e0 : bv 32 := 0xf325fce3.
Lemma Fx_831e0 : fetch_word AsanUbsan.M.loaded_segments (0x83228 : word) = Some Wx_831e0.
Proof. vm_refl. Qed.
Lemma Dx_831e0 : decode_any Wx_831e0 = Some (Branch BC_GEU 11 18 7992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831e4 : bv 32 := 0xff857513.
Lemma Fx_831e4 : fetch_word AsanUbsan.M.loaded_segments (0x8322c : word) = Some Wx_831e4.
Proof. vm_refl. Qed.
Lemma Dx_831e4 : decode_any Wx_831e4 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831e8 : bv 32 := 0xf2baece3.
Lemma Fx_831e8 : fetch_word AsanUbsan.M.loaded_segments (0x83230 : word) = Some Wx_831e8.
Proof. vm_refl. Qed.
Lemma Dx_831e8 : decode_any Wx_831e8 = Some (Branch BC_LTU 21 11 7992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831ec : bv 32 := 0x000a8593.
Lemma Fx_831ec : fetch_word AsanUbsan.M.loaded_segments (0x83234 : word) = Some Wx_831ec.
Proof. vm_refl. Qed.
Lemma Dx_831ec : decode_any Wx_831ec = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831f0 : bv 32 := 0xff8af493.
Lemma Fx_831f0 : fetch_word AsanUbsan.M.loaded_segments (0x83238 : word) = Some Wx_831f0.
Proof. vm_refl. Qed.
Lemma Dx_831f0 : decode_any Wx_831f0 = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831f4 : bv 32 := 0x007a8613.
Lemma Fx_831f4 : fetch_word AsanUbsan.M.loaded_segments (0x8323c : word) = Some Wx_831f4.
Proof. vm_refl. Qed.
Lemma Dx_831f4 : decode_any Wx_831f4 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831f8 : bv 32 := 0xff867913.
Lemma Fx_831f8 : fetch_word AsanUbsan.M.loaded_segments (0x83240 : word) = Some Wx_831f8.
Proof. vm_refl. Qed.
Lemma Dx_831f8 : decode_any Wx_831f8 = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_831fc : bv 32 := 0xf2956ae3.
Lemma Fx_831fc : fetch_word AsanUbsan.M.loaded_segments (0x83244 : word) = Some Wx_831fc.
Proof. vm_refl. Qed.
Lemma Dx_831fc : decode_any Wx_831fc = Some (Branch BC_LTU 10 9 7988, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83200 : bv 32 := 0x00758513.
Lemma Fx_83200 : fetch_word AsanUbsan.M.loaded_segments (0x83248 : word) = Some Wx_83200.
Proof. vm_refl. Qed.
Lemma Dx_83200 : decode_any Wx_83200 = Some (OpImm ALU_ADD 10 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83204 : bv 32 := 0xff857513.
Lemma Fx_83204 : fetch_word AsanUbsan.M.loaded_segments (0x8324c : word) = Some Wx_83204.
Proof. vm_refl. Qed.
Lemma Dx_83204 : decode_any Wx_83204 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83208 : bv 32 := 0x00a97a63.
Lemma Fx_83208 : fetch_word AsanUbsan.M.loaded_segments (0x83250 : word) = Some Wx_83208.
Proof. vm_refl. Qed.
Lemma Dx_83208 : decode_any Wx_83208 = Some (Branch BC_GEU 18 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8320c : bv 32 := 0x412505b3.
Lemma Fx_8320c : fetch_word AsanUbsan.M.loaded_segments (0x83254 : word) = Some Wx_8320c.
Proof. vm_refl. Qed.
Lemma Dx_8320c : decode_any Wx_8320c = Some (Op ALU_SUB 11 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83210 : bv 32 := 0x0fc00613.
Lemma Fx_83210 : fetch_word AsanUbsan.M.loaded_segments (0x83258 : word) = Some Wx_83210.
Proof. vm_refl. Qed.
Lemma Dx_83210 : decode_any Wx_83210 = Some (OpImm ALU_ADD 12 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83214 : bv 32 := 0x00090513.
Lemma Fx_83214 : fetch_word AsanUbsan.M.loaded_segments (0x8325c : word) = Some Wx_83214.
Proof. vm_refl. Qed.
Lemma Dx_83214 : decode_any Wx_83214 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83218 : bv 32 := 0xe79fe0ef.
Lemma Fx_83218 : fetch_word AsanUbsan.M.loaded_segments (0x83260 : word) = Some Wx_83218.
Proof. vm_refl. Qed.
Lemma Dx_83218 : decode_any Wx_83218 = Some (Jal 1 2092664, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8321c : bv 32 := 0x02990063.
Lemma Fx_8321c : fetch_word AsanUbsan.M.loaded_segments (0x83264 : word) = Some Wx_8321c.
Proof. vm_refl. Qed.
Lemma Dx_8321c : decode_any Wx_8321c = Some (Branch BC_EQ 18 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83220 : bv 32 := 0x409906b3.
Lemma Fx_83220 : fetch_word AsanUbsan.M.loaded_segments (0x83268 : word) = Some Wx_83220.
Proof. vm_refl. Qed.
Lemma Dx_83220 : decode_any Wx_83220 = Some (Op ALU_SUB 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83224 : bv 32 := 0x00800513.
Lemma Fx_83224 : fetch_word AsanUbsan.M.loaded_segments (0x8326c : word) = Some Wx_83224.
Proof. vm_refl. Qed.
Lemma Dx_83224 : decode_any Wx_83224 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83228 : bv 32 := 0x02a69e63.
Lemma Fx_83228 : fetch_word AsanUbsan.M.loaded_segments (0x83270 : word) = Some Wx_83228.
Proof. vm_refl. Qed.
Lemma Dx_83228 : decode_any Wx_83228 = Some (Branch BC_NE 13 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8322c : bv 32 := 0x007af913.
Lemma Fx_8322c : fetch_word AsanUbsan.M.loaded_segments (0x83274 : word) = Some Wx_8322c.
Proof. vm_refl. Qed.
Lemma Dx_8322c : decode_any Wx_8322c = Some (OpImm ALU_AND 18 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83230 : bv 32 := 0x00048513.
Lemma Fx_83230 : fetch_word AsanUbsan.M.loaded_segments (0x83278 : word) = Some Wx_83230.
Proof. vm_refl. Qed.
Lemma Dx_83230 : decode_any Wx_83230 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83234 : bv 32 := 0xb58ff0ef.
Lemma Fx_83234 : fetch_word AsanUbsan.M.loaded_segments (0x8327c : word) = Some Wx_83234.
Proof. vm_refl. Qed.
Lemma Dx_83234 : decode_any Wx_83234 = Some (Jal 1 2093912, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83238 : bv 32 := 0x01250023.
Lemma Fx_83238 : fetch_word AsanUbsan.M.loaded_segments (0x83280 : word) = Some Wx_83238.
Proof. vm_refl. Qed.
Lemma Dx_83238 : decode_any Wx_83238 = Some (Store SZ1 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8323c : bv 32 := 0x06010113.
Lemma Fx_8323c : fetch_word AsanUbsan.M.loaded_segments (0x83284 : word) = Some Wx_8323c.
Proof. vm_refl. Qed.
Lemma Dx_8323c : decode_any Wx_8323c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83240 : bv 32 := 0x7e813083.
Lemma Fx_83240 : fetch_word AsanUbsan.M.loaded_segments (0x83288 : word) = Some Wx_83240.
Proof. vm_refl. Qed.
Lemma Dx_83240 : decode_any Wx_83240 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83244 : bv 32 := 0x7e013403.
Lemma Fx_83244 : fetch_word AsanUbsan.M.loaded_segments (0x8328c : word) = Some Wx_83244.
Proof. vm_refl. Qed.
Lemma Dx_83244 : decode_any Wx_83244 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83248 : bv 32 := 0x7d813483.
Lemma Fx_83248 : fetch_word AsanUbsan.M.loaded_segments (0x83290 : word) = Some Wx_83248.
Proof. vm_refl. Qed.
Lemma Dx_83248 : decode_any Wx_83248 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8324c : bv 32 := 0x7d013903.
Lemma Fx_8324c : fetch_word AsanUbsan.M.loaded_segments (0x83294 : word) = Some Wx_8324c.
Proof. vm_refl. Qed.
Lemma Dx_8324c : decode_any Wx_8324c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83250 : bv 32 := 0x7c813983.
Lemma Fx_83250 : fetch_word AsanUbsan.M.loaded_segments (0x83298 : word) = Some Wx_83250.
Proof. vm_refl. Qed.
Lemma Dx_83250 : decode_any Wx_83250 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83254 : bv 32 := 0x7c013a03.
Lemma Fx_83254 : fetch_word AsanUbsan.M.loaded_segments (0x8329c : word) = Some Wx_83254.
Proof. vm_refl. Qed.
Lemma Dx_83254 : decode_any Wx_83254 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83258 : bv 32 := 0x7b813a83.
Lemma Fx_83258 : fetch_word AsanUbsan.M.loaded_segments (0x832a0 : word) = Some Wx_83258.
Proof. vm_refl. Qed.
Lemma Dx_83258 : decode_any Wx_83258 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8325c : bv 32 := 0x7f010113.
Lemma Fx_8325c : fetch_word AsanUbsan.M.loaded_segments (0x832a4 : word) = Some Wx_8325c.
Proof. vm_refl. Qed.
Lemma Dx_8325c : decode_any Wx_8325c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83260 : bv 32 := 0x00008067.
Lemma Fx_83260 : fetch_word AsanUbsan.M.loaded_segments (0x832a8 : word) = Some Wx_83260.
Proof. vm_refl. Qed.
Lemma Dx_83260 : decode_any Wx_83260 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83264 : bv 32 := 0xfff9f517.
Lemma Fx_83264 : fetch_word AsanUbsan.M.loaded_segments (0x832ac : word) = Some Wx_83264.
Proof. vm_refl. Qed.
Lemma Dx_83264 : decode_any Wx_83264 = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83268 : bv 32 := 0xfff96617.
Lemma Fx_83268 : fetch_word AsanUbsan.M.loaded_segments (0x832b0 : word) = Some Wx_83268.
Proof. vm_refl. Qed.
Lemma Dx_83268 : decode_any Wx_83268 = Some (Auipc 12 1048470, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8326c : bv 32 := 0x1dc00593.
Lemma Fx_8326c : fetch_word AsanUbsan.M.loaded_segments (0x832b4 : word) = Some Wx_8326c.
Proof. vm_refl. Qed.
Lemma Dx_8326c : decode_any Wx_8326c = Some (OpImm ALU_ADD 11 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83270 : bv 32 := 0xa2350513.
Lemma Fx_83270 : fetch_word AsanUbsan.M.loaded_segments (0x832b8 : word) = Some Wx_83270.
Proof. vm_refl. Qed.
Lemma Dx_83270 : decode_any Wx_83270 = Some (OpImm ALU_ADD 10 10 2595, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83274 : bv 32 := 0xd8560613.
Lemma Fx_83274 : fetch_word AsanUbsan.M.loaded_segments (0x832bc : word) = Some Wx_83274.
Proof. vm_refl. Qed.
Lemma Dx_83274 : decode_any Wx_83274 = Some (OpImm ALU_ADD 12 12 3461, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83278 : bv 32 := 0x00800713.
Lemma Fx_83278 : fetch_word AsanUbsan.M.loaded_segments (0x832c0 : word) = Some Wx_83278.
Proof. vm_refl. Qed.
Lemma Dx_83278 : decode_any Wx_83278 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8327c : bv 32 := 0x460170ef.
Lemma Fx_8327c : fetch_word AsanUbsan.M.loaded_segments (0x832c4 : word) = Some Wx_8327c.
Proof. vm_refl. Qed.
Lemma Dx_8327c : decode_any Wx_8327c = Some (Jal 1 95328, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83280 : bv 32 := 0x000a8a13.
Lemma Fx_83280 : fetch_word AsanUbsan.M.loaded_segments (0x832c8 : word) = Some Wx_83280.
Proof. vm_refl. Qed.
Lemma Dx_83280 : decode_any Wx_83280 = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83284 : bv 32 := 0xf13aece3.
Lemma Fx_83284 : fetch_word AsanUbsan.M.loaded_segments (0x832cc : word) = Some Wx_83284.
Proof. vm_refl. Qed.
Lemma Dx_83284 : decode_any Wx_83284 = Some (Branch BC_LTU 21 19 7960, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83288 : bv 32 := 0x00098a13.
Lemma Fx_83288 : fetch_word AsanUbsan.M.loaded_segments (0x832d0 : word) = Some Wx_83288.
Proof. vm_refl. Qed.
Lemma Dx_83288 : decode_any Wx_83288 = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8328c : bv 32 := 0xe72aece3.
Lemma Fx_8328c : fetch_word AsanUbsan.M.loaded_segments (0x832d4 : word) = Some Wx_8328c.
Proof. vm_refl. Qed.
Lemma Dx_8328c : decode_any Wx_8328c = Some (Branch BC_LTU 21 18 7800, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83290 : bv 32 := 0x00090a93.
Lemma Fx_83290 : fetch_word AsanUbsan.M.loaded_segments (0x832d8 : word) = Some Wx_83290.
Proof. vm_refl. Qed.
Lemma Dx_83290 : decode_any Wx_83290 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_83294 : bv 32 := 0xe71ff06f.
Lemma Fx_83294 : fetch_word AsanUbsan.M.loaded_segments (0x832dc : word) = Some Wx_83294.
Proof. vm_refl. Qed.
Lemma Dx_83294 : decode_any Wx_83294 = Some (Jal 0 2096752, 4%Z).
Proof. vm_refl. Qed.

