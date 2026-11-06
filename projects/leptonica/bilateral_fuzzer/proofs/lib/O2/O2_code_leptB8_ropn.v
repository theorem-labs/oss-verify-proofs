(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_233ec : bv 32 := 0xf2010113.
Lemma F_233ec : fetch_word Plain.M.loaded_segments (0x23444 : word) = Some W_233ec.
Proof. vm_refl. Qed.
Lemma D_233ec : decode_any W_233ec = Some (OpImm ALU_ADD 2 2 3872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233f0 : bv 32 := 0x0c113c23.
Lemma F_233f0 : fetch_word Plain.M.loaded_segments (0x23448 : word) = Some W_233f0.
Proof. vm_refl. Qed.
Lemma D_233f0 : decode_any W_233f0 = Some (Store SZ8 2 1 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233f4 : bv 32 := 0x0c813823.
Lemma F_233f4 : fetch_word Plain.M.loaded_segments (0x2344c : word) = Some W_233f4.
Proof. vm_refl. Qed.
Lemma D_233f4 : decode_any W_233f4 = Some (Store SZ8 2 8 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233f8 : bv 32 := 0x0c913423.
Lemma F_233f8 : fetch_word Plain.M.loaded_segments (0x23450 : word) = Some W_233f8.
Proof. vm_refl. Qed.
Lemma D_233f8 : decode_any W_233f8 = Some (Store SZ8 2 9 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233fc : bv 32 := 0x0d213023.
Lemma F_233fc : fetch_word Plain.M.loaded_segments (0x23454 : word) = Some W_233fc.
Proof. vm_refl. Qed.
Lemma D_233fc : decode_any W_233fc = Some (Store SZ8 2 18 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23400 : bv 32 := 0x0b313c23.
Lemma F_23400 : fetch_word Plain.M.loaded_segments (0x23458 : word) = Some W_23400.
Proof. vm_refl. Qed.
Lemma D_23400 : decode_any W_23400 = Some (Store SZ8 2 19 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23404 : bv 32 := 0x0b413823.
Lemma F_23404 : fetch_word Plain.M.loaded_segments (0x2345c : word) = Some W_23404.
Proof. vm_refl. Qed.
Lemma D_23404 : decode_any W_23404 = Some (Store SZ8 2 20 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23408 : bv 32 := 0x0b513423.
Lemma F_23408 : fetch_word Plain.M.loaded_segments (0x23460 : word) = Some W_23408.
Proof. vm_refl. Qed.
Lemma D_23408 : decode_any W_23408 = Some (Store SZ8 2 21 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2340c : bv 32 := 0x0b613023.
Lemma F_2340c : fetch_word Plain.M.loaded_segments (0x23464 : word) = Some W_2340c.
Proof. vm_refl. Qed.
Lemma D_2340c : decode_any W_2340c = Some (Store SZ8 2 22 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23410 : bv 32 := 0x09713c23.
Lemma F_23410 : fetch_word Plain.M.loaded_segments (0x23468 : word) = Some W_23410.
Proof. vm_refl. Qed.
Lemma D_23410 : decode_any W_23410 = Some (Store SZ8 2 23 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23414 : bv 32 := 0x09813823.
Lemma F_23414 : fetch_word Plain.M.loaded_segments (0x2346c : word) = Some W_23414.
Proof. vm_refl. Qed.
Lemma D_23414 : decode_any W_23414 = Some (Store SZ8 2 24 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23418 : bv 32 := 0x09913423.
Lemma F_23418 : fetch_word Plain.M.loaded_segments (0x23470 : word) = Some W_23418.
Proof. vm_refl. Qed.
Lemma D_23418 : decode_any W_23418 = Some (Store SZ8 2 25 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2341c : bv 32 := 0x09a13023.
Lemma F_2341c : fetch_word Plain.M.loaded_segments (0x23474 : word) = Some W_2341c.
Proof. vm_refl. Qed.
Lemma D_2341c : decode_any W_2341c = Some (Store SZ8 2 26 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23420 : bv 32 := 0x07b13c23.
Lemma F_23420 : fetch_word Plain.M.loaded_segments (0x23478 : word) = Some W_23420.
Proof. vm_refl. Qed.
Lemma D_23420 : decode_any W_23420 = Some (Store SZ8 2 27 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23424 : bv 32 := 0x0a050863.
Lemma F_23424 : fetch_word Plain.M.loaded_segments (0x2347c : word) = Some W_23424.
Proof. vm_refl. Qed.
Lemma D_23424 : decode_any W_23424 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234d4 : bv 32 := 0x00015517.
Lemma F_234d4 : fetch_word Plain.M.loaded_segments (0x2352c : word) = Some W_234d4.
Proof. vm_refl. Qed.
Lemma D_234d4 : decode_any W_234d4 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234d8 : bv 32 := 0xf4453503.
Lemma F_234d8 : fetch_word Plain.M.loaded_segments (0x23530 : word) = Some W_234d8.
Proof. vm_refl. Qed.
Lemma D_234d8 : decode_any W_234d8 = Some (Load SZ8 true 10 10 3908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234dc : bv 32 := 0x00052503.
Lemma F_234dc : fetch_word Plain.M.loaded_segments (0x23534 : word) = Some W_234dc.
Proof. vm_refl. Qed.
Lemma D_234dc : decode_any W_234dc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234e0 : bv 32 := 0x00500593.
Lemma F_234e0 : fetch_word Plain.M.loaded_segments (0x23538 : word) = Some W_234e0.
Proof. vm_refl. Qed.
Lemma D_234e0 : decode_any W_234e0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234e4 : bv 32 := 0x16a5c263.
Lemma F_234e4 : fetch_word Plain.M.loaded_segments (0x2353c : word) = Some W_234e4.
Proof. vm_refl. Qed.
Lemma D_234e4 : decode_any W_234e4 = Some (Branch BC_LT 11 10 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234e8 : bv 32 := 0xfffee517.
Lemma F_234e8 : fetch_word Plain.M.loaded_segments (0x23540 : word) = Some W_234e8.
Proof. vm_refl. Qed.
Lemma D_234e8 : decode_any W_234e8 = Some (Auipc 10 1048558, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234ec : bv 32 := 0xfffee597.
Lemma F_234ec : fetch_word Plain.M.loaded_segments (0x23544 : word) = Some W_234ec.
Proof. vm_refl. Qed.
Lemma D_234ec : decode_any W_234ec = Some (Auipc 11 1048558, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234f0 : bv 32 := 0x3d250513.
Lemma F_234f0 : fetch_word Plain.M.loaded_segments (0x23548 : word) = Some W_234f0.
Proof. vm_refl. Qed.
Lemma D_234f0 : decode_any W_234f0 = Some (OpImm ALU_ADD 10 10 978, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234f4 : bv 32 := 0x21658593.
Lemma F_234f4 : fetch_word Plain.M.loaded_segments (0x2354c : word) = Some W_234f4.
Proof. vm_refl. Qed.
Lemma D_234f4 : decode_any W_234f4 = Some (OpImm ALU_ADD 11 11 534, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234f8 : bv 32 := 0x00100613.
Lemma F_234f8 : fetch_word Plain.M.loaded_segments (0x23550 : word) = Some W_234f8.
Proof. vm_refl. Qed.
Lemma D_234f8 : decode_any W_234f8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234fc : bv 32 := 0x0d813083.
Lemma F_234fc : fetch_word Plain.M.loaded_segments (0x23554 : word) = Some W_234fc.
Proof. vm_refl. Qed.
Lemma D_234fc : decode_any W_234fc = Some (Load SZ8 true 1 2 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23500 : bv 32 := 0x0d013403.
Lemma F_23500 : fetch_word Plain.M.loaded_segments (0x23558 : word) = Some W_23500.
Proof. vm_refl. Qed.
Lemma D_23500 : decode_any W_23500 = Some (Load SZ8 true 8 2 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23504 : bv 32 := 0x0c813483.
Lemma F_23504 : fetch_word Plain.M.loaded_segments (0x2355c : word) = Some W_23504.
Proof. vm_refl. Qed.
Lemma D_23504 : decode_any W_23504 = Some (Load SZ8 true 9 2 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23508 : bv 32 := 0x0c013903.
Lemma F_23508 : fetch_word Plain.M.loaded_segments (0x23560 : word) = Some W_23508.
Proof. vm_refl. Qed.
Lemma D_23508 : decode_any W_23508 = Some (Load SZ8 true 18 2 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2350c : bv 32 := 0x0b813983.
Lemma F_2350c : fetch_word Plain.M.loaded_segments (0x23564 : word) = Some W_2350c.
Proof. vm_refl. Qed.
Lemma D_2350c : decode_any W_2350c = Some (Load SZ8 true 19 2 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23510 : bv 32 := 0x0b013a03.
Lemma F_23510 : fetch_word Plain.M.loaded_segments (0x23568 : word) = Some W_23510.
Proof. vm_refl. Qed.
Lemma D_23510 : decode_any W_23510 = Some (Load SZ8 true 20 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23514 : bv 32 := 0x0a813a83.
Lemma F_23514 : fetch_word Plain.M.loaded_segments (0x2356c : word) = Some W_23514.
Proof. vm_refl. Qed.
Lemma D_23514 : decode_any W_23514 = Some (Load SZ8 true 21 2 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23518 : bv 32 := 0x0a013b03.
Lemma F_23518 : fetch_word Plain.M.loaded_segments (0x23570 : word) = Some W_23518.
Proof. vm_refl. Qed.
Lemma D_23518 : decode_any W_23518 = Some (Load SZ8 true 22 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2351c : bv 32 := 0x09813b83.
Lemma F_2351c : fetch_word Plain.M.loaded_segments (0x23574 : word) = Some W_2351c.
Proof. vm_refl. Qed.
Lemma D_2351c : decode_any W_2351c = Some (Load SZ8 true 23 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23520 : bv 32 := 0x09013c03.
Lemma F_23520 : fetch_word Plain.M.loaded_segments (0x23578 : word) = Some W_23520.
Proof. vm_refl. Qed.
Lemma D_23520 : decode_any W_23520 = Some (Load SZ8 true 24 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23524 : bv 32 := 0x08813c83.
Lemma F_23524 : fetch_word Plain.M.loaded_segments (0x2357c : word) = Some W_23524.
Proof. vm_refl. Qed.
Lemma D_23524 : decode_any W_23524 = Some (Load SZ8 true 25 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23528 : bv 32 := 0x08013d03.
Lemma F_23528 : fetch_word Plain.M.loaded_segments (0x23580 : word) = Some W_23528.
Proof. vm_refl. Qed.
Lemma D_23528 : decode_any W_23528 = Some (Load SZ8 true 26 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2352c : bv 32 := 0x07813d83.
Lemma F_2352c : fetch_word Plain.M.loaded_segments (0x23584 : word) = Some W_2352c.
Proof. vm_refl. Qed.
Lemma D_2352c : decode_any W_2352c = Some (Load SZ8 true 27 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23530 : bv 32 := 0x0e010113.
Lemma F_23530 : fetch_word Plain.M.loaded_segments (0x23588 : word) = Some W_23530.
Proof. vm_refl. Qed.
Lemma D_23530 : decode_any W_23530 = Some (OpImm ALU_ADD 2 2 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23534 : bv 32 := 0xe18f406f.
Lemma F_23534 : fetch_word Plain.M.loaded_segments (0x2358c : word) = Some W_23534.
Proof. vm_refl. Qed.
Lemma D_23534 : decode_any W_23534 = Some (Jal 0 2049560, 4%Z).
Proof. vm_refl. Qed.

