(* reloc-zl14c *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress2_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_19000 : bv 32 := 0x00050593.
Lemma F_19000 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19178 : word) = Some W_19000.
Proof. vm_refl. Qed.
Lemma D_19000 : decode_any W_19000 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19004 : bv 32 := 0x05e00893.
Lemma F_19004 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1917c : word) = Some W_19004.
Proof. vm_refl. Qed.
Lemma D_19004 : decode_any W_19004 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19008 : bv 32 := 0x00000073.
Lemma F_19008 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19180 : word) = Some W_19008.
Proof. vm_refl. Qed.
Lemma D_19008 : decode_any W_19008 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_19008 : is_ecall W_19008 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_19100 : bv 32 := 0xff010113.
Lemma F_19100 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19278 : word) = Some W_19100.
Proof. vm_refl. Qed.
Lemma D_19100 : decode_any W_19100 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19104 : bv 32 := 0x00113423.
Lemma F_19104 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1927c : word) = Some W_19104.
Proof. vm_refl. Qed.
Lemma D_19104 : decode_any W_19104 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19108 : bv 32 := 0x00050e63.
Lemma F_19108 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19280 : word) = Some W_19108.
Proof. vm_refl. Qed.
Lemma D_19108 : decode_any W_19108 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1910c : bv 32 := 0x00050593.
Lemma F_1910c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19284 : word) = Some W_1910c.
Proof. vm_refl. Qed.
Lemma D_1910c : decode_any W_1910c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19110 : bv 32 := 0x00009517.
Lemma F_19110 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19288 : word) = Some W_19110.
Proof. vm_refl. Qed.
Lemma D_19110 : decode_any W_19110 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19114 : bv 32 := 0x9c053503.
Lemma F_19114 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1928c : word) = Some W_19114.
Proof. vm_refl. Qed.
Lemma D_19114 : decode_any W_19114 = Some (Load SZ8 true 10 10 2496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19118 : bv 32 := 0x00800613.
Lemma F_19118 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19290 : word) = Some W_19118.
Proof. vm_refl. Qed.
Lemma D_19118 : decode_any W_19118 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1911c : bv 32 := 0x739060ef.
Lemma F_1911c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19294 : word) = Some W_1911c.
Proof. vm_refl. Qed.
Lemma D_1911c : decode_any W_1911c = Some (Jal 1 28472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19120 : bv 32 := 0x01c0006f.
Lemma F_19120 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19298 : word) = Some W_19120.
Proof. vm_refl. Qed.
Lemma D_19120 : decode_any W_19120 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19124 : bv 32 := 0x00009517.
Lemma F_19124 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1929c : word) = Some W_19124.
Proof. vm_refl. Qed.
Lemma D_19124 : decode_any W_19124 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19128 : bv 32 := 0x9ac53503.
Lemma F_19128 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192a0 : word) = Some W_19128.
Proof. vm_refl. Qed.
Lemma D_19128 : decode_any W_19128 = Some (Load SZ8 true 10 10 2476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1912c : bv 32 := 0x41c655b7.
Lemma F_1912c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192a4 : word) = Some W_1912c.
Proof. vm_refl. Qed.
Lemma D_1912c : decode_any W_1912c = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19130 : bv 32 := 0xe6d5859b.
Lemma F_19130 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192a8 : word) = Some W_19130.
Proof. vm_refl. Qed.
Lemma D_19130 : decode_any W_19130 = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19134 : bv 32 := 0x02b505b3.
Lemma F_19134 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192ac : word) = Some W_19134.
Proof. vm_refl. Qed.
Lemma D_19134 : decode_any W_19134 = Some (Mul M_MUL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19138 : bv 32 := 0x00b53023.
Lemma F_19138 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192b0 : word) = Some W_19138.
Proof. vm_refl. Qed.
Lemma D_19138 : decode_any W_19138 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1913c : bv 32 := 0x00009517.
Lemma F_1913c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192b4 : word) = Some W_1913c.
Proof. vm_refl. Qed.
Lemma D_1913c : decode_any W_1913c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19140 : bv 32 := 0x99453503.
Lemma F_19140 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192b8 : word) = Some W_19140.
Proof. vm_refl. Qed.
Lemma D_19140 : decode_any W_19140 = Some (Load SZ8 true 10 10 2452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19144 : bv 32 := 0x000500a3.
Lemma F_19144 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192bc : word) = Some W_19144.
Proof. vm_refl. Qed.
Lemma D_19144 : decode_any W_19144 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19148 : bv 32 := 0x00053503.
Lemma F_19148 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192c0 : word) = Some W_19148.
Proof. vm_refl. Qed.
Lemma D_19148 : decode_any W_19148 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1914c : bv 32 := 0x00020593.
Lemma F_1914c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192c4 : word) = Some W_1914c.
Proof. vm_refl. Qed.
Lemma D_1914c : decode_any W_1914c = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19150 : bv 32 := 0xfea5b823.
Lemma F_19150 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192c8 : word) = Some W_19150.
Proof. vm_refl. Qed.
Lemma D_19150 : decode_any W_19150 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19154 : bv 32 := 0x00813083.
Lemma F_19154 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192cc : word) = Some W_19154.
Proof. vm_refl. Qed.
Lemma D_19154 : decode_any W_19154 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19158 : bv 32 := 0x01010113.
Lemma F_19158 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192d0 : word) = Some W_19158.
Proof. vm_refl. Qed.
Lemma D_19158 : decode_any W_19158 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1915c : bv 32 := 0x00008067.
Lemma F_1915c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192d4 : word) = Some W_1915c.
Proof. vm_refl. Qed.
Lemma D_1915c : decode_any W_1915c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19168 : bv 32 := 0xfffff5b7.
Lemma F_19168 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192e0 : word) = Some W_19168.
Proof. vm_refl. Qed.
Lemma D_19168 : decode_any W_19168 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1916c : bv 32 := 0x0015859b.
Lemma F_1916c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192e4 : word) = Some W_1916c.
Proof. vm_refl. Qed.
Lemma D_1916c : decode_any W_1916c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19170 : bv 32 := 0x02b56663.
Lemma F_19170 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x192e8 : word) = Some W_19170.
Proof. vm_refl. Qed.
Lemma D_19170 : decode_any W_19170 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1919c : bv 32 := 0x00008067.
Lemma F_1919c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19314 : word) = Some W_1919c.
Proof. vm_refl. Qed.
Lemma D_1919c : decode_any W_1919c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192f0 : bv 32 := 0x1c050463.
Lemma F_192f0 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19468 : word) = Some W_192f0.
Proof. vm_refl. Qed.
Lemma D_192f0 : decode_any W_192f0 = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192f4 : bv 32 := 0xfd010113.
Lemma F_192f4 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1946c : word) = Some W_192f4.
Proof. vm_refl. Qed.
Lemma D_192f4 : decode_any W_192f4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192f8 : bv 32 := 0x02113423.
Lemma F_192f8 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19470 : word) = Some W_192f8.
Proof. vm_refl. Qed.
Lemma D_192f8 : decode_any W_192f8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_192fc : bv 32 := 0x02813023.
Lemma F_192fc : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19474 : word) = Some W_192fc.
Proof. vm_refl. Qed.
Lemma D_192fc : decode_any W_192fc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19300 : bv 32 := 0x00913c23.
Lemma F_19300 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19478 : word) = Some W_19300.
Proof. vm_refl. Qed.
Lemma D_19300 : decode_any W_19300 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19304 : bv 32 := 0x01213823.
Lemma F_19304 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1947c : word) = Some W_19304.
Proof. vm_refl. Qed.
Lemma D_19304 : decode_any W_19304 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19308 : bv 32 := 0x01313423.
Lemma F_19308 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19480 : word) = Some W_19308.
Proof. vm_refl. Qed.
Lemma D_19308 : decode_any W_19308 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1930c : bv 32 := 0x00050493.
Lemma F_1930c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19484 : word) = Some W_1930c.
Proof. vm_refl. Qed.
Lemma D_1930c : decode_any W_1930c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19310 : bv 32 := 0x1ac000ef.
Lemma F_19310 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19488 : word) = Some W_19310.
Proof. vm_refl. Qed.
Lemma D_19310 : decode_any W_19310 = Some (Jal 1 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19314 : bv 32 := 0x02053583.
Lemma F_19314 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1948c : word) = Some W_19314.
Proof. vm_refl. Qed.
Lemma D_19314 : decode_any W_19314 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19318 : bv 32 := 0xffd4c683.
Lemma F_19318 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19490 : word) = Some W_19318.
Proof. vm_refl. Qed.
Lemma D_19318 : decode_any W_19318 = Some (Load SZ1 false 13 9 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1931c : bv 32 := 0x00c5d613.
Lemma F_1931c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19494 : word) = Some W_1931c.
Proof. vm_refl. Qed.
Lemma D_1931c : decode_any W_1931c = Some (ShiftImm ALU_SRL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19320 : bv 32 := 0x01f6f413.
Lemma F_19320 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19498 : word) = Some W_19320.
Proof. vm_refl. Qed.
Lemma D_19320 : decode_any W_19320 = Some (OpImm ALU_AND 8 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19324 : bv 32 := 0x00060e63.
Lemma F_19324 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1949c : word) = Some W_19324.
Proof. vm_refl. Qed.
Lemma D_19324 : decode_any W_19324 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19328 : bv 32 := 0x01f5f613.
Lemma F_19328 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194a0 : word) = Some W_19328.
Proof. vm_refl. Qed.
Lemma D_19328 : decode_any W_19328 = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1932c : bv 32 := 0x00061a63.
Lemma F_1932c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194a4 : word) = Some W_1932c.
Proof. vm_refl. Qed.
Lemma D_1932c : decode_any W_1932c = Some (Branch BC_NE 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19330 : bv 32 := 0xfffff637.
Lemma F_19330 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194a8 : word) = Some W_19330.
Proof. vm_refl. Qed.
Lemma D_19330 : decode_any W_19330 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19334 : bv 32 := 0x00c5f633.
Lemma F_19334 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194ac : word) = Some W_19334.
Proof. vm_refl. Qed.
Lemma D_19334 : decode_any W_19334 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19338 : bv 32 := 0xff060613.
Lemma F_19338 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194b0 : word) = Some W_19338.
Proof. vm_refl. Qed.
Lemma D_19338 : decode_any W_19338 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1933c : bv 32 := 0x0200006f.
Lemma F_1933c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194b4 : word) = Some W_1933c.
Proof. vm_refl. Qed.
Lemma D_1933c : decode_any W_1933c = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19340 : bv 32 := 0x0055d613.
Lemma F_19340 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194b8 : word) = Some W_19340.
Proof. vm_refl. Qed.
Lemma D_19340 : decode_any W_19340 = Some (ShiftImm ALU_SRL 12 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19344 : bv 32 := 0xffff9717.
Lemma F_19344 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194bc : word) = Some W_19344.
Proof. vm_refl. Qed.
Lemma D_19344 : decode_any W_19344 = Some (Auipc 14 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19348 : bv 32 := 0x07e67613.
Lemma F_19348 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194c0 : word) = Some W_19348.
Proof. vm_refl. Qed.
Lemma D_19348 : decode_any W_19348 = Some (OpImm ALU_AND 12 12 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1934c : bv 32 := 0xfa070713.
Lemma F_1934c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194c4 : word) = Some W_1934c.
Proof. vm_refl. Qed.
Lemma D_1934c : decode_any W_1934c = Some (OpImm ALU_ADD 14 14 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19350 : bv 32 := 0x00c70633.
Lemma F_19350 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194c8 : word) = Some W_19350.
Proof. vm_refl. Qed.
Lemma D_19350 : decode_any W_19350 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19354 : bv 32 := 0x00065603.
Lemma F_19354 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194cc : word) = Some W_19354.
Proof. vm_refl. Qed.
Lemma D_19354 : decode_any W_19354 = Some (Load SZ2 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19358 : bv 32 := 0x00461613.
Lemma F_19358 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194d0 : word) = Some W_19358.
Proof. vm_refl. Qed.
Lemma D_19358 : decode_any W_19358 = Some (ShiftImm ALU_SLL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1935c : bv 32 := 0x01053703.
Lemma F_1935c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194d4 : word) = Some W_1935c.
Proof. vm_refl. Qed.
Lemma D_1935c : decode_any W_1935c = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19360 : bv 32 := 0x028607b3.
Lemma F_19360 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194d8 : word) = Some W_19360.
Proof. vm_refl. Qed.
Lemma D_19360 : decode_any W_19360 = Some (Mul M_MUL 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19364 : bv 32 := 0x0a000813.
Lemma F_19364 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194dc : word) = Some W_19364.
Proof. vm_refl. Qed.
Lemma D_19364 : decode_any W_19364 = Some (OpImm ALU_ADD 16 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19368 : bv 32 := 0x00c70633.
Lemma F_19368 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194e0 : word) = Some W_19368.
Proof. vm_refl. Qed.
Lemma D_19368 : decode_any W_19368 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1936c : bv 32 := 0x00f607b3.
Lemma F_1936c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194e4 : word) = Some W_1936c.
Proof. vm_refl. Qed.
Lemma D_1936c : decode_any W_1936c = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19370 : bv 32 := 0x00c78613.
Lemma F_19370 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194e8 : word) = Some W_19370.
Proof. vm_refl. Qed.
Lemma D_19370 : decode_any W_19370 = Some (OpImm ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19374 : bv 32 := 0x0056d713.
Lemma F_19374 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194ec : word) = Some W_19374.
Proof. vm_refl. Qed.
Lemma D_19374 : decode_any W_19374 = Some (ShiftImm ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19378 : bv 32 := 0x0306e663.
Lemma F_19378 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194f0 : word) = Some W_19378.
Proof. vm_refl. Qed.
Lemma D_19378 : decode_any W_19378 = Some (Branch BC_LTU 13 16 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1937c : bv 32 := 0x00500693.
Lemma F_1937c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194f4 : word) = Some W_1937c.
Proof. vm_refl. Qed.
Lemma D_1937c : decode_any W_1937c = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19380 : bv 32 := 0x00d70463.
Lemma F_19380 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x194f8 : word) = Some W_19380.
Proof. vm_refl. Qed.
Lemma D_19380 : decode_any W_19380 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19388 : bv 32 := 0x0087e703.
Lemma F_19388 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19500 : word) = Some W_19388.
Proof. vm_refl. Qed.
Lemma D_19388 : decode_any W_19388 = Some (Load SZ4 false 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1938c : bv 32 := 0x00400693.
Lemma F_1938c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19504 : word) = Some W_1938c.
Proof. vm_refl. Qed.
Lemma D_1938c : decode_any W_1938c = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19390 : bv 32 := 0x00e6e463.
Lemma F_19390 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19508 : word) = Some W_19390.
Proof. vm_refl. Qed.
Lemma D_19390 : decode_any W_19390 = Some (Branch BC_LTU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19398 : bv 32 := 0x0077c683.
Lemma F_19398 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19510 : word) = Some W_19398.
Proof. vm_refl. Qed.
Lemma D_19398 : decode_any W_19398 = Some (Load SZ1 false 13 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1939c : bv 32 := 0x00068463.
Lemma F_1939c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19514 : word) = Some W_1939c.
Proof. vm_refl. Qed.
Lemma D_1939c : decode_any W_1939c = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193a4 : bv 32 := 0x409606b3.
Lemma F_193a4 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1951c : word) = Some W_193a4.
Proof. vm_refl. Qed.
Lemma D_193a4 : decode_any W_193a4 = Some (Op ALU_SUB 13 12 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193a8 : bv 32 := 0x00e6f463.
Lemma F_193a8 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19520 : word) = Some W_193a8.
Proof. vm_refl. Qed.
Lemma D_193a8 : decode_any W_193a8 = Some (Branch BC_GEU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193b0 : bv 32 := 0x40e606b3.
Lemma F_193b0 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19528 : word) = Some W_193b0.
Proof. vm_refl. Qed.
Lemma D_193b0 : decode_any W_193b0 = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193b4 : bv 32 := 0x0006c683.
Lemma F_193b4 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1952c : word) = Some W_193b4.
Proof. vm_refl. Qed.
Lemma D_193b4 : decode_any W_193b4 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193b8 : bv 32 := 0x00068463.
Lemma F_193b8 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19530 : word) = Some W_193b8.
Proof. vm_refl. Qed.
Lemma D_193b8 : decode_any W_193b8 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193c0 : bv 32 := 0x00064603.
Lemma F_193c0 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19538 : word) = Some W_193c0.
Proof. vm_refl. Qed.
Lemma D_193c0 : decode_any W_193c0 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193c4 : bv 32 := 0x00060463.
Lemma F_193c4 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1953c : word) = Some W_193c4.
Proof. vm_refl. Qed.
Lemma D_193c4 : decode_any W_193c4 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194bc : bv 32 := 0x00f57593.
Lemma F_194bc : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19634 : word) = Some W_194bc.
Proof. vm_refl. Qed.
Lemma D_194bc : decode_any W_194bc = Some (OpImm ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194c0 : bv 32 := 0x00058463.
Lemma F_194c0 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19638 : word) = Some W_194c0.
Proof. vm_refl. Qed.
Lemma D_194c0 : decode_any W_194c0 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194c8 : bv 32 := 0xffc54603.
Lemma F_194c8 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19640 : word) = Some W_194c8.
Proof. vm_refl. Qed.
Lemma D_194c8 : decode_any W_194c8 = Some (Load SZ1 false 12 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194cc : bv 32 := 0xffd54683.
Lemma F_194cc : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19644 : word) = Some W_194cc.
Proof. vm_refl. Qed.
Lemma D_194cc : decode_any W_194cc = Some (Load SZ1 false 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194d0 : bv 32 := 0xffe55583.
Lemma F_194d0 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19648 : word) = Some W_194d0.
Proof. vm_refl. Qed.
Lemma D_194d0 : decode_any W_194d0 = Some (Load SZ2 false 11 10 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194d4 : bv 32 := 0x00060e63.
Lemma F_194d4 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1964c : word) = Some W_194d4.
Proof. vm_refl. Qed.
Lemma D_194d4 : decode_any W_194d4 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194f0 : bv 32 := 0x00459613.
Lemma F_194f0 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19668 : word) = Some W_194f0.
Proof. vm_refl. Qed.
Lemma D_194f0 : decode_any W_194f0 = Some (ShiftImm ALU_SLL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194f4 : bv 32 := 0x40c50633.
Lemma F_194f4 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1966c : word) = Some W_194f4.
Proof. vm_refl. Qed.
Lemma D_194f4 : decode_any W_194f4 = Some (Op ALU_SUB 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194f8 : bv 32 := 0xff063503.
Lemma F_194f8 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19670 : word) = Some W_194f8.
Proof. vm_refl. Qed.
Lemma D_194f8 : decode_any W_194f8 = Some (Load SZ8 true 10 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194fc : bv 32 := 0x01053703.
Lemma F_194fc : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19674 : word) = Some W_194fc.
Proof. vm_refl. Qed.
Lemma D_194fc : decode_any W_194fc = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19500 : bv 32 := 0xff060613.
Lemma F_19500 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19678 : word) = Some W_19500.
Proof. vm_refl. Qed.
Lemma D_19500 : decode_any W_19500 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19504 : bv 32 := 0x01f6f693.
Lemma F_19504 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1967c : word) = Some W_19504.
Proof. vm_refl. Qed.
Lemma D_19504 : decode_any W_19504 = Some (OpImm ALU_AND 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19508 : bv 32 := 0x00c70463.
Lemma F_19508 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19680 : word) = Some W_19508.
Proof. vm_refl. Qed.
Lemma D_19508 : decode_any W_19508 = Some (Branch BC_EQ 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19510 : bv 32 := 0x02053603.
Lemma F_19510 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19688 : word) = Some W_19510.
Proof. vm_refl. Qed.
Lemma D_19510 : decode_any W_19510 = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19514 : bv 32 := 0x01f67713.
Lemma F_19514 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1968c : word) = Some W_19514.
Proof. vm_refl. Qed.
Lemma D_19514 : decode_any W_19514 = Some (OpImm ALU_AND 14 12 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19518 : bv 32 := 0x00d77463.
Lemma F_19518 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19690 : word) = Some W_19518.
Proof. vm_refl. Qed.
Lemma D_19518 : decode_any W_19518 = Some (Branch BC_GEU 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19520 : bv 32 := 0x01852783.
Lemma F_19520 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19698 : word) = Some W_19520.
Proof. vm_refl. Qed.
Lemma D_19520 : decode_any W_19520 = Some (Load SZ4 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19524 : bv 32 := 0x00100713.
Lemma F_19524 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1969c : word) = Some W_19524.
Proof. vm_refl. Qed.
Lemma D_19524 : decode_any W_19524 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19528 : bv 32 := 0x00d7173b.
Lemma F_19528 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196a0 : word) = Some W_19528.
Proof. vm_refl. Qed.
Lemma D_19528 : decode_any W_19528 = Some (Op32 ALU_SLL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1952c : bv 32 := 0x00e7f7b3.
Lemma F_1952c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196a4 : word) = Some W_1952c.
Proof. vm_refl. Qed.
Lemma D_1952c : decode_any W_1952c = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19530 : bv 32 := 0x00078463.
Lemma F_19530 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196a8 : word) = Some W_19530.
Proof. vm_refl. Qed.
Lemma D_19530 : decode_any W_19530 = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19538 : bv 32 := 0x01c52783.
Lemma F_19538 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196b0 : word) = Some W_19538.
Proof. vm_refl. Qed.
Lemma D_19538 : decode_any W_19538 = Some (Load SZ4 true 15 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1953c : bv 32 := 0x00e7f733.
Lemma F_1953c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196b4 : word) = Some W_1953c.
Proof. vm_refl. Qed.
Lemma D_1953c : decode_any W_1953c = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19540 : bv 32 := 0x00070463.
Lemma F_19540 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196b8 : word) = Some W_19540.
Proof. vm_refl. Qed.
Lemma D_19540 : decode_any W_19540 = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19548 : bv 32 := 0xfffff737.
Lemma F_19548 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196c0 : word) = Some W_19548.
Proof. vm_refl. Qed.
Lemma D_19548 : decode_any W_19548 = Some (Lui 14 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1954c : bv 32 := 0x0007a797.
Lemma F_1954c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196c4 : word) = Some W_1954c.
Proof. vm_refl. Qed.
Lemma D_1954c : decode_any W_1954c = Some (Auipc 15 122, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19550 : bv 32 := 0x00e57733.
Lemma F_19550 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196c8 : word) = Some W_19550.
Proof. vm_refl. Qed.
Lemma D_19550 : decode_any W_19550 = Some (Op ALU_AND 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19554 : bv 32 := 0x00073703.
Lemma F_19554 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196cc : word) = Some W_19554.
Proof. vm_refl. Qed.
Lemma D_19554 : decode_any W_19554 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19558 : bv 32 := 0xbfc7b783.
Lemma F_19558 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196d0 : word) = Some W_19558.
Proof. vm_refl. Qed.
Lemma D_19558 : decode_any W_19558 = Some (Load SZ8 true 15 15 3068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1955c : bv 32 := 0x00f70463.
Lemma F_1955c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196d4 : word) = Some W_1955c.
Proof. vm_refl. Qed.
Lemma D_1955c : decode_any W_1955c = Some (Branch BC_EQ 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19564 : bv 32 := 0x03461713.
Lemma F_19564 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196dc : word) = Some W_19564.
Proof. vm_refl. Qed.
Lemma D_19564 : decode_any W_19564 = Some (ShiftImm ALU_SLL 14 12 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19568 : bv 32 := 0x03a75713.
Lemma F_19568 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196e0 : word) = Some W_19568.
Proof. vm_refl. Qed.
Lemma D_19568 : decode_any W_19568 = Some (ShiftImm ALU_SRL 14 14 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1956c : bv 32 := 0x02f00793.
Lemma F_1956c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196e4 : word) = Some W_1956c.
Proof. vm_refl. Qed.
Lemma D_1956c : decode_any W_1956c = Some (OpImm ALU_ADD 15 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19570 : bv 32 := 0x02e7ea63.
Lemma F_19570 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196e8 : word) = Some W_19570.
Proof. vm_refl. Qed.
Lemma D_19570 : decode_any W_19570 = Some (Branch BC_LTU 15 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19574 : bv 32 := 0x00171713.
Lemma F_19574 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196ec : word) = Some W_19574.
Proof. vm_refl. Qed.
Lemma D_19574 : decode_any W_19574 = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19578 : bv 32 := 0xffff9797.
Lemma F_19578 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196f0 : word) = Some W_19578.
Proof. vm_refl. Qed.
Lemma D_19578 : decode_any W_19578 = Some (Auipc 15 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1957c : bv 32 := 0xd6c78793.
Lemma F_1957c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196f4 : word) = Some W_1957c.
Proof. vm_refl. Qed.
Lemma D_1957c : decode_any W_1957c = Some (OpImm ALU_ADD 15 15 3436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19580 : bv 32 := 0x00e78733.
Lemma F_19580 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196f8 : word) = Some W_19580.
Proof. vm_refl. Qed.
Lemma D_19580 : decode_any W_19580 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19584 : bv 32 := 0x00075703.
Lemma F_19584 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x196fc : word) = Some W_19584.
Proof. vm_refl. Qed.
Lemma D_19584 : decode_any W_19584 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19588 : bv 32 := 0x02d707b3.
Lemma F_19588 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19700 : word) = Some W_19588.
Proof. vm_refl. Qed.
Lemma D_19588 : decode_any W_19588 = Some (Mul M_MUL 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1958c : bv 32 := 0x00f5f463.
Lemma F_1958c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19704 : word) = Some W_1958c.
Proof. vm_refl. Qed.
Lemma D_1958c : decode_any W_1958c = Some (Branch BC_GEU 11 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19594 : bv 32 := 0x00168693.
Lemma F_19594 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1970c : word) = Some W_19594.
Proof. vm_refl. Qed.
Lemma D_19594 : decode_any W_19594 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19598 : bv 32 := 0x02e686b3.
Lemma F_19598 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19710 : word) = Some W_19598.
Proof. vm_refl. Qed.
Lemma D_19598 : decode_any W_19598 = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1959c : bv 32 := 0x00d5f863.
Lemma F_1959c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19714 : word) = Some W_1959c.
Proof. vm_refl. Qed.
Lemma D_1959c : decode_any W_1959c = Some (Branch BC_GEU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195a0 : bv 32 := 0x0100006f.
Lemma F_195a0 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19718 : word) = Some W_195a0.
Proof. vm_refl. Qed.
Lemma D_195a0 : decode_any W_195a0 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195a4 : bv 32 := 0x03f00693.
Lemma F_195a4 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1971c : word) = Some W_195a4.
Proof. vm_refl. Qed.
Lemma D_195a4 : decode_any W_195a4 = Some (OpImm ALU_ADD 13 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195a8 : bv 32 := 0x00d70463.
Lemma F_195a8 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19720 : word) = Some W_195a8.
Proof. vm_refl. Qed.
Lemma D_195a8 : decode_any W_195a8 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195b0 : bv 32 := 0x00c65613.
Lemma F_195b0 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19728 : word) = Some W_195b0.
Proof. vm_refl. Qed.
Lemma D_195b0 : decode_any W_195b0 = Some (ShiftImm ALU_SRL 12 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195b4 : bv 32 := 0x00060a63.
Lemma F_195b4 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1972c : word) = Some W_195b4.
Proof. vm_refl. Qed.
Lemma D_195b4 : decode_any W_195b4 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195b8 : bv 32 := 0x00861613.
Lemma F_195b8 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19730 : word) = Some W_195b8.
Proof. vm_refl. Qed.
Lemma D_195b8 : decode_any W_195b8 = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195bc : bv 32 := 0xfff60613.
Lemma F_195bc : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19734 : word) = Some W_195bc.
Proof. vm_refl. Qed.
Lemma D_195bc : decode_any W_195bc = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195c0 : bv 32 := 0x00b67463.
Lemma F_195c0 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19738 : word) = Some W_195c0.
Proof. vm_refl. Qed.
Lemma D_195c0 : decode_any W_195c0 = Some (Branch BC_GEU 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_195c8 : bv 32 := 0x00008067.
Lemma F_195c8 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19740 : word) = Some W_195c8.
Proof. vm_refl. Qed.
Lemma D_195c8 : decode_any W_195c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1994c : bv 32 := 0x00072503.
Lemma F_1994c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19ac4 : word) = Some W_1994c.
Proof. vm_refl. Qed.
Lemma D_1994c : decode_any W_1994c = Some (Load SZ4 true 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19950 : bv 32 := 0x00b56633.
Lemma F_19950 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19ac8 : word) = Some W_19950.
Proof. vm_refl. Qed.
Lemma D_19950 : decode_any W_19950 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19954 : bv 32 := 0x160726af.
Lemma F_19954 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19acc : word) = Some W_19954.
Proof. vm_refl. Qed.
Lemma D_19954 : decode_any W_19954 = Some (Lr AW true true 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19958 : bv 32 := 0x00a69663.
Lemma F_19958 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19ad0 : word) = Some W_19958.
Proof. vm_refl. Qed.
Lemma D_19958 : decode_any W_19958 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1995c : bv 32 := 0x1ec727af.
Lemma F_1995c : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19ad4 : word) = Some W_1995c.
Proof. vm_refl. Qed.
Lemma D_1995c : decode_any W_1995c = Some (Sc AW true true 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19960 : bv 32 := 0xfe079ae3.
Lemma F_19960 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19ad8 : word) = Some W_19960.
Proof. vm_refl. Qed.
Lemma D_19960 : decode_any W_19960 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19964 : bv 32 := 0x0006869b.
Lemma F_19964 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19adc : word) = Some W_19964.
Proof. vm_refl. Qed.
Lemma D_19964 : decode_any W_19964 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19968 : bv 32 := 0xfea692e3.
Lemma F_19968 : fetch_word SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19ae0 : word) = Some W_19968.
Proof. vm_refl. Qed.
Lemma D_19968 : decode_any W_19968 = Some (Branch BC_NE 13 10 8164, 4%Z).
Proof. vm_refl. Qed.
