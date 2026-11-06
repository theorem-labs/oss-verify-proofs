(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
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
Definition W_6d20c : bv 32 := @BV 32 0x0009a697%Z I.
Lemma F_6d20c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d20c%Z I : word) = Some W_6d20c.
Proof. vm_refl. Qed.
Lemma D_6d20c : decode_any W_6d20c = Some (Auipc (@BV 5 13%Z I) (@BV 20 154%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d210 : bv 32 := @BV 32 0x8746b683%Z I.
Lemma F_6d210 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d210%Z I : word) = Some W_6d210.
Proof. vm_refl. Qed.
Lemma D_6d210 : decode_any W_6d210 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 2164%Z I), 4%Z).
Proof. vm_refl. Qed.











































(* [comment removed for export] *)
Definition W_6d24c : bv 32 := @BV 32 0x00099697%Z I.
Lemma F_6d24c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d24c%Z I : word) = Some W_6d24c.
Proof. vm_refl. Qed.
Lemma D_6d24c : decode_any W_6d24c = Some (Auipc (@BV 5 13%Z I) (@BV 20 153%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d250 : bv 32 := @BV 32 0xccc6b683%Z I.
Lemma F_6d250 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d250%Z I : word) = Some W_6d250.
Proof. vm_refl. Qed.
Lemma D_6d250 : decode_any W_6d250 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 3276%Z I), 4%Z).
Proof. vm_refl. Qed.


































(* [comment removed for export] *)
Definition W_6d280 : bv 32 := @BV 32 0x2a079a63%Z I.
Lemma F_6d280 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d280%Z I : word) = Some W_6d280.
Proof. vm_refl. Qed.
Lemma D_6d280 : decode_any W_6d280 = Some (Branch BC_NE (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 13 692%Z I), 4%Z).
Proof. vm_refl. Qed.













(* [comment removed for export] *)
Definition W_6d294 : bv 32 := @BV 32 0x00099697%Z I.
Lemma F_6d294 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d294%Z I : word) = Some W_6d294.
Proof. vm_refl. Qed.
Lemma D_6d294 : decode_any W_6d294 = Some (Auipc (@BV 5 13%Z I) (@BV 20 153%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d298 : bv 32 := @BV 32 0xc846b683%Z I.
Lemma F_6d298 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d298%Z I : word) = Some W_6d298.
Proof. vm_refl. Qed.
Lemma D_6d298 : decode_any W_6d298 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 3204%Z I), 4%Z).
Proof. vm_refl. Qed.


































(* [comment removed for export] *)
Definition W_6d2c8 : bv 32 := @BV 32 0x30079863%Z I.
Lemma F_6d2c8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d2c8%Z I : word) = Some W_6d2c8.
Proof. vm_refl. Qed.
Lemma D_6d2c8 : decode_any W_6d2c8 = Some (Branch BC_NE (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 13 784%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d2cc : bv 32 := @BV 32 0x0009b697%Z I.
Lemma F_6d2cc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d2cc%Z I : word) = Some W_6d2cc.
Proof. vm_refl. Qed.
Lemma D_6d2cc : decode_any W_6d2cc = Some (Auipc (@BV 5 13%Z I) (@BV 20 155%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d2d0 : bv 32 := @BV 32 0xb846b683%Z I.
Lemma F_6d2d0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d2d0%Z I : word) = Some W_6d2d0.
Proof. vm_refl. Qed.
Lemma D_6d2d0 : decode_any W_6d2d0 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 2948%Z I), 4%Z).
Proof. vm_refl. Qed.





















































































































































































































































































































































































































































































(* [comment removed for export] *)
Definition W_6d564 : bv 32 := @BV 32 0xd20680e3%Z I.
Lemma F_6d564 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d564%Z I : word) = Some W_6d564.
Proof. vm_refl. Qed.
Lemma D_6d564 : decode_any W_6d564 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 7456%Z I), 4%Z).
Proof. vm_refl. Qed.



















































































































(* [comment removed for export] *)
Definition W_6d608 : bv 32 := @BV 32 0xcc0682e3%Z I.
Lemma F_6d608 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d608%Z I : word) = Some W_6d608.
Proof. vm_refl. Qed.
Lemma D_6d608 : decode_any W_6d608 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 7364%Z I), 4%Z).
Proof. vm_refl. Qed.










































































































(* [comment removed for export] *)
Definition W_6d6a0 : bv 32 := @BV 32 0x00099697%Z I.
Lemma F_6d6a0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d6a0%Z I : word) = Some W_6d6a0.
Proof. vm_refl. Qed.
Lemma D_6d6a0 : decode_any W_6d6a0 = Some (Auipc (@BV 5 13%Z I) (@BV 20 153%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d6a4 : bv 32 := @BV 32 0x3e06b683%Z I.
Lemma F_6d6a4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d6a4%Z I : word) = Some W_6d6a4.
Proof. vm_refl. Qed.
Lemma D_6d6a4 : decode_any W_6d6a4 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 992%Z I), 4%Z).
Proof. vm_refl. Qed.




























(* [comment removed for export] *)
Definition W_6d6cc : bv 32 := @BV 32 0x00099697%Z I.
Lemma F_6d6cc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d6cc%Z I : word) = Some W_6d6cc.
Proof. vm_refl. Qed.
Lemma D_6d6cc : decode_any W_6d6cc = Some (Auipc (@BV 5 13%Z I) (@BV 20 153%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d6d0 : bv 32 := @BV 32 0x84c6b683%Z I.
Lemma F_6d6d0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d6d0%Z I : word) = Some W_6d6d0.
Proof. vm_refl. Qed.
Lemma D_6d6d0 : decode_any W_6d6d0 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 2124%Z I), 4%Z).
Proof. vm_refl. Qed.





































(* [comment removed for export] *)
Definition W_6d704 : bv 32 := @BV 32 0x10081a63%Z I.
Lemma F_6d704 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d704%Z I : word) = Some W_6d704.
Proof. vm_refl. Qed.
Lemma D_6d704 : decode_any W_6d704 = Some (Branch BC_NE (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 13 276%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d708 : bv 32 := @BV 32 0x0009a697%Z I.
Lemma F_6d708 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d708%Z I : word) = Some W_6d708.
Proof. vm_refl. Qed.
Lemma D_6d708 : decode_any W_6d708 = Some (Auipc (@BV 5 13%Z I) (@BV 20 154%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d70c : bv 32 := @BV 32 0x7506b683%Z I.
Lemma F_6d70c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d70c%Z I : word) = Some W_6d70c.
Proof. vm_refl. Qed.
Lemma D_6d70c : decode_any W_6d70c = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1872%Z I), 4%Z).
Proof. vm_refl. Qed.































































































































































































































(* [comment removed for export] *)
Definition W_6d848 : bv 32 := @BV 32 0xec0680e3%Z I.
Lemma F_6d848 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d848%Z I : word) = Some W_6d848.
Proof. vm_refl. Qed.
Lemma D_6d848 : decode_any W_6d848 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 7872%Z I), 4%Z).
Proof. vm_refl. Qed.







































































































(* [comment removed for export] *)
Definition W_6d8e4 : bv 32 := @BV 32 0x00099697%Z I.
Lemma F_6d8e4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d8e4%Z I : word) = Some W_6d8e4.
Proof. vm_refl. Qed.
Lemma D_6d8e4 : decode_any W_6d8e4 = Some (Auipc (@BV 5 13%Z I) (@BV 20 153%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d8e8 : bv 32 := @BV 32 0x19c6b683%Z I.
Lemma F_6d8e8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d8e8%Z I : word) = Some W_6d8e8.
Proof. vm_refl. Qed.
Lemma D_6d8e8 : decode_any W_6d8e8 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 412%Z I), 4%Z).
Proof. vm_refl. Qed.




























(* [comment removed for export] *)
Definition W_6d910 : bv 32 := @BV 32 0x00098697%Z I.
Lemma F_6d910 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d910%Z I : word) = Some W_6d910.
Proof. vm_refl. Qed.
Lemma D_6d910 : decode_any W_6d910 = Some (Auipc (@BV 5 13%Z I) (@BV 20 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d914 : bv 32 := @BV 32 0x6086b683%Z I.
Lemma F_6d914 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d914%Z I : word) = Some W_6d914.
Proof. vm_refl. Qed.
Lemma D_6d914 : decode_any W_6d914 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1544%Z I), 4%Z).
Proof. vm_refl. Qed.































(* [comment removed for export] *)
Definition W_6d948 : bv 32 := @BV 32 0x18081e63%Z I.
Lemma F_6d948 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d948%Z I : word) = Some W_6d948.
Proof. vm_refl. Qed.
Lemma D_6d948 : decode_any W_6d948 = Some (Branch BC_NE (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 13 412%Z I), 4%Z).
Proof. vm_refl. Qed.













(* [comment removed for export] *)
Definition W_6d95c : bv 32 := @BV 32 0x00098697%Z I.
Lemma F_6d95c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d95c%Z I : word) = Some W_6d95c.
Proof. vm_refl. Qed.
Lemma D_6d95c : decode_any W_6d95c = Some (Auipc (@BV 5 13%Z I) (@BV 20 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d960 : bv 32 := @BV 32 0x5bc6b683%Z I.
Lemma F_6d960 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d960%Z I : word) = Some W_6d960.
Proof. vm_refl. Qed.
Lemma D_6d960 : decode_any W_6d960 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1468%Z I), 4%Z).
Proof. vm_refl. Qed.





































(* [comment removed for export] *)
Definition W_6d994 : bv 32 := @BV 32 0x1e081a63%Z I.
Lemma F_6d994 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6d994%Z I : word) = Some W_6d994.
Proof. vm_refl. Qed.
Lemma D_6d994 : decode_any W_6d994 = Some (Branch BC_NE (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 13 500%Z I), 4%Z).
Proof. vm_refl. Qed.






























































































































































































































































































(* [comment removed for export] *)
Definition W_6db14 : bv 32 := @BV 32 0xe2068ce3%Z I.
Lemma F_6db14 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6db14%Z I : word) = Some W_6db14.
Proof. vm_refl. Qed.
Lemma D_6db14 : decode_any W_6db14 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 7736%Z I), 4%Z).
Proof. vm_refl. Qed.













































































































(* [comment removed for export] *)
Definition W_6dbb8 : bv 32 := @BV 32 0xde0680e3%Z I.
Lemma F_6dbb8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6dbb8%Z I : word) = Some W_6dbb8.
Proof. vm_refl. Qed.
Lemma D_6dbb8 : decode_any W_6dbb8 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 7648%Z I), 4%Z).
Proof. vm_refl. Qed.













































































































(* [comment removed for export] *)
Definition W_6dc54 : bv 32 := @BV 32 0x00099697%Z I.
Lemma F_6dc54 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6dc54%Z I : word) = Some W_6dc54.
Proof. vm_refl. Qed.
Lemma D_6dc54 : decode_any W_6dc54 = Some (Auipc (@BV 5 13%Z I) (@BV 20 153%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dc58 : bv 32 := @BV 32 0xe2c6b683%Z I.
Lemma F_6dc58 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6dc58%Z I : word) = Some W_6dc58.
Proof. vm_refl. Qed.
Lemma D_6dc58 : decode_any W_6dc58 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 3628%Z I), 4%Z).
Proof. vm_refl. Qed.






















(* [comment removed for export] *)
Definition W_6dc80 : bv 32 := @BV 32 0x00098697%Z I.
Lemma F_6dc80 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6dc80%Z I : word) = Some W_6dc80.
Proof. vm_refl. Qed.
Lemma D_6dc80 : decode_any W_6dc80 = Some (Auipc (@BV 5 13%Z I) (@BV 20 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dc84 : bv 32 := @BV 32 0x2986b683%Z I.
Lemma F_6dc84 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6dc84%Z I : word) = Some W_6dc84.
Proof. vm_refl. Qed.
Lemma D_6dc84 : decode_any W_6dc84 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 664%Z I), 4%Z).
Proof. vm_refl. Qed.





































(* [comment removed for export] *)
Definition W_6dcb8 : bv 32 := @BV 32 0x10081e63%Z I.
Lemma F_6dcb8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6dcb8%Z I : word) = Some W_6dcb8.
Proof. vm_refl. Qed.
Lemma D_6dcb8 : decode_any W_6dcb8 = Some (Branch BC_NE (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 13 284%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dcbc : bv 32 := @BV 32 0x0009a697%Z I.
Lemma F_6dcbc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6dcbc%Z I : word) = Some W_6dcbc.
Proof. vm_refl. Qed.
Lemma D_6dcbc : decode_any W_6dcbc = Some (Auipc (@BV 5 13%Z I) (@BV 20 154%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dcc0 : bv 32 := @BV 32 0x19c6b683%Z I.
Lemma F_6dcc0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6dcc0%Z I : word) = Some W_6dcc0.
Proof. vm_refl. Qed.
Lemma D_6dcc0 : decode_any W_6dcc0 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 412%Z I), 4%Z).
Proof. vm_refl. Qed.








































































































































































































































(* [comment removed for export] *)
Definition W_6de04 : bv 32 := @BV 32 0xea068ce3%Z I.
Lemma F_6de04 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6de04%Z I : word) = Some W_6de04.
Proof. vm_refl. Qed.
Lemma D_6de04 : decode_any W_6de04 = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 7864%Z I), 4%Z).
Proof. vm_refl. Qed.










































































































(* [comment removed for export] *)
Definition W_6df48 : bv 32 := @BV 32 0x00099697%Z I.
Lemma F_6df48 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6df48%Z I : word) = Some W_6df48.
Proof. vm_refl. Qed.
Lemma D_6df48 : decode_any W_6df48 = Some (Auipc (@BV 5 13%Z I) (@BV 20 153%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df4c : bv 32 := @BV 32 0xb386b683%Z I.
Lemma F_6df4c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6df4c%Z I : word) = Some W_6df4c.
Proof. vm_refl. Qed.
Lemma D_6df4c : decode_any W_6df4c = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 2872%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df74 : bv 32 := @BV 32 0x00098697%Z I.
Lemma F_6df74 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6df74%Z I : word) = Some W_6df74.
Proof. vm_refl. Qed.
Lemma D_6df74 : decode_any W_6df74 = Some (Auipc (@BV 5 13%Z I) (@BV 20 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df78 : bv 32 := @BV 32 0xfa46b683%Z I.
Lemma F_6df78 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6df78%Z I : word) = Some W_6df78.
Proof. vm_refl. Qed.
Lemma D_6df78 : decode_any W_6df78 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 4004%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dfac : bv 32 := @BV 32 0x1a081063%Z I.
Lemma F_6dfac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6dfac%Z I : word) = Some W_6dfac.
Proof. vm_refl. Qed.
Lemma D_6dfac : decode_any W_6dfac = Some (Branch BC_NE (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 13 416%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dfc0 : bv 32 := @BV 32 0x00098697%Z I.
Lemma F_6dfc0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6dfc0%Z I : word) = Some W_6dfc0.
Proof. vm_refl. Qed.
Lemma D_6dfc0 : decode_any W_6dfc0 = Some (Auipc (@BV 5 13%Z I) (@BV 20 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dfc4 : bv 32 := @BV 32 0xf586b683%Z I.
Lemma F_6dfc4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6dfc4%Z I : word) = Some W_6dfc4.
Proof. vm_refl. Qed.
Lemma D_6dfc4 : decode_any W_6dfc4 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 3928%Z I), 4%Z).
Proof. vm_refl. Qed.







(* [comment removed for export] *)
Definition W_6dff8 : bv 32 := @BV 32 0x24081a63%Z I.
Lemma F_6dff8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6dff8%Z I : word) = Some W_6dff8.
Proof. vm_refl. Qed.
Lemma D_6dff8 : decode_any W_6dff8 = Some (Branch BC_NE (@BV 5 16%Z I) (@BV 5 0%Z I) (@BV 13 596%Z I), 4%Z).
Proof. vm_refl. Qed.









































































(* [comment removed for export] *)
Definition W_6e17c : bv 32 := @BV 32 0xe2068ae3%Z I.
Lemma F_6e17c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e17c%Z I : word) = Some W_6e17c.
Proof. vm_refl. Qed.
Lemma D_6e17c : decode_any W_6e17c = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 7732%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e27c : bv 32 := @BV 32 0xd80680e3%Z I.
Lemma F_6e27c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e27c%Z I : word) = Some W_6e27c.
Proof. vm_refl. Qed.
Lemma D_6e27c : decode_any W_6e27c = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 7552%Z I), 4%Z).
Proof. vm_refl. Qed.







































































































(* [comment removed for export] *)
Definition W_6e40c : bv 32 := @BV 32 0x00098697%Z I.
Lemma F_6e40c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e40c%Z I : word) = Some W_6e40c.
Proof. vm_refl. Qed.
Lemma D_6e40c : decode_any W_6e40c = Some (Auipc (@BV 5 13%Z I) (@BV 20 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e410 : bv 32 := @BV 32 0x6746b683%Z I.
Lemma F_6e410 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e410%Z I : word) = Some W_6e410.
Proof. vm_refl. Qed.
Lemma D_6e410 : decode_any W_6e410 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1652%Z I), 4%Z).
Proof. vm_refl. Qed.




























(* [comment removed for export] *)
Definition W_6e44c : bv 32 := @BV 32 0x00098697%Z I.
Lemma F_6e44c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e44c%Z I : word) = Some W_6e44c.
Proof. vm_refl. Qed.
Lemma D_6e44c : decode_any W_6e44c = Some (Auipc (@BV 5 13%Z I) (@BV 20 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e450 : bv 32 := @BV 32 0xacc6b683%Z I.
Lemma F_6e450 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e450%Z I : word) = Some W_6e450.
Proof. vm_refl. Qed.
Lemma D_6e450 : decode_any W_6e450 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 2764%Z I), 4%Z).
Proof. vm_refl. Qed.






















(* [comment removed for export] *)
Definition W_6e480 : bv 32 := @BV 32 0x2a079e63%Z I.
Lemma F_6e480 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e480%Z I : word) = Some W_6e480.
Proof. vm_refl. Qed.
Lemma D_6e480 : decode_any W_6e480 = Some (Branch BC_NE (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 13 700%Z I), 4%Z).
Proof. vm_refl. Qed.













(* [comment removed for export] *)
Definition W_6e494 : bv 32 := @BV 32 0x00098697%Z I.
Lemma F_6e494 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e494%Z I : word) = Some W_6e494.
Proof. vm_refl. Qed.
Lemma D_6e494 : decode_any W_6e494 = Some (Auipc (@BV 5 13%Z I) (@BV 20 152%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e498 : bv 32 := @BV 32 0xa846b683%Z I.
Lemma F_6e498 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e498%Z I : word) = Some W_6e498.
Proof. vm_refl. Qed.
Lemma D_6e498 : decode_any W_6e498 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 2692%Z I), 4%Z).
Proof. vm_refl. Qed.


































(* [comment removed for export] *)
Definition W_6e4c8 : bv 32 := @BV 32 0x36079a63%Z I.
Lemma F_6e4c8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e4c8%Z I : word) = Some W_6e4c8.
Proof. vm_refl. Qed.
Lemma D_6e4c8 : decode_any W_6e4c8 = Some (Branch BC_NE (@BV 5 15%Z I) (@BV 5 0%Z I) (@BV 13 884%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4cc : bv 32 := @BV 32 0x0009a697%Z I.
Lemma F_6e4cc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e4cc%Z I : word) = Some W_6e4cc.
Proof. vm_refl. Qed.
Lemma D_6e4cc : decode_any W_6e4cc = Some (Auipc (@BV 5 13%Z I) (@BV 20 154%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4d0 : bv 32 := @BV 32 0x9846b683%Z I.
Lemma F_6e4d0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e4d0%Z I : word) = Some W_6e4d0.
Proof. vm_refl. Qed.
Lemma D_6e4d0 : decode_any W_6e4d0 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 2436%Z I), 4%Z).
Proof. vm_refl. Qed.


























































































































































































































































(* [comment removed for export] *)
Definition W_6e76c : bv 32 := @BV 32 0xd0068ce3%Z I.
Lemma F_6e76c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e76c%Z I : word) = Some W_6e76c.
Proof. vm_refl. Qed.
Lemma D_6e76c : decode_any W_6e76c = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 7448%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e86c : bv 32 := @BV 32 0xc60680e3%Z I.
Lemma F_6e86c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6e86c%Z I : word) = Some W_6e86c.
Proof. vm_refl. Qed.
Lemma D_6e86c : decode_any W_6e86c = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 7264%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition W_6eab4 : bv 32 := @BV 32 0x00097597%Z I.
Lemma F_6eab4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eab4%Z I : word) = Some W_6eab4.
Proof. vm_refl. Qed.
Lemma D_6eab4 : decode_any W_6eab4 = Some (Auipc (@BV 5 11%Z I) (@BV 20 151%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eab8 : bv 32 := @BV 32 0x4645b583%Z I.
Lemma F_6eab8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eab8%Z I : word) = Some W_6eab8.
Proof. vm_refl. Qed.
Lemma D_6eab8 : decode_any W_6eab8 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 1124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ead4 : bv 32 := @BV 32 0x00097697%Z I.
Lemma F_6ead4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ead4%Z I : word) = Some W_6ead4.
Proof. vm_refl. Qed.
Lemma D_6ead4 : decode_any W_6ead4 = Some (Auipc (@BV 5 13%Z I) (@BV 20 151%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ead8 : bv 32 := @BV 32 0x44c6b683%Z I.
Lemma F_6ead8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ead8%Z I : word) = Some W_6ead8.
Proof. vm_refl. Qed.
Lemma D_6ead8 : decode_any W_6ead8 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 1100%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eadc : bv 32 := @BV 32 0x00097717%Z I.
Lemma F_6eadc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eadc%Z I : word) = Some W_6eadc.
Proof. vm_refl. Qed.
Lemma D_6eadc : decode_any W_6eadc = Some (Auipc (@BV 5 14%Z I) (@BV 20 151%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eae0 : bv 32 := @BV 32 0x44c73703%Z I.
Lemma F_6eae0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eae0%Z I : word) = Some W_6eae0.
Proof. vm_refl. Qed.
Lemma D_6eae0 : decode_any W_6eae0 = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 1100%Z I), 4%Z).
Proof. vm_refl. Qed.







(* [comment removed for export] *)
Definition W_6eaf8 : bv 32 := @BV 32 0x00097717%Z I.
Lemma F_6eaf8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eaf8%Z I : word) = Some W_6eaf8.
Proof. vm_refl. Qed.
Lemma D_6eaf8 : decode_any W_6eaf8 = Some (Auipc (@BV 5 14%Z I) (@BV 20 151%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eafc : bv 32 := @BV 32 0x43873703%Z I.
Lemma F_6eafc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eafc%Z I : word) = Some W_6eafc.
Proof. vm_refl. Qed.
Lemma D_6eafc : decode_any W_6eafc = Some (Load SZ8 true (@BV 5 14%Z I) (@BV 5 14%Z I) (@BV 12 1080%Z I), 4%Z).
Proof. vm_refl. Qed.































































































































































































































































































































































































































(* [comment removed for export] *)
Definition W_6ed5c : bv 32 := @BV 32 0x0100006f%Z I.
Lemma F_6ed5c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed5c%Z I : word) = Some W_6ed5c.
Proof. vm_refl. Qed.
Lemma D_6ed5c : decode_any W_6ed5c = Some (Jal (@BV 5 0%Z I) (@BV 21 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ed60 : bv 32 := @BV 32 0x1dc0006f%Z I.
Lemma F_6ed60 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed60%Z I : word) = Some W_6ed60.
Proof. vm_refl. Qed.
Lemma D_6ed60 : decode_any W_6ed60 = Some (Jal (@BV 5 0%Z I) (@BV 21 476%Z I), 4%Z).
Proof. vm_refl. Qed.







(* [comment removed for export] *)
Definition W_6ed6c : bv 32 := @BV 32 0x81010113%Z I.
Lemma F_6ed6c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed6c%Z I : word) = Some W_6ed6c.
Proof. vm_refl. Qed.
Lemma D_6ed6c : decode_any W_6ed6c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 2064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ed70 : bv 32 := @BV 32 0x7e113423%Z I.
Lemma F_6ed70 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed70%Z I : word) = Some W_6ed70.
Proof. vm_refl. Qed.
Lemma D_6ed70 : decode_any W_6ed70 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 2024%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ed74 : bv 32 := @BV 32 0x7e813023%Z I.
Lemma F_6ed74 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed74%Z I : word) = Some W_6ed74.
Proof. vm_refl. Qed.
Lemma D_6ed74 : decode_any W_6ed74 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 2016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ed78 : bv 32 := @BV 32 0x7c913c23%Z I.
Lemma F_6ed78 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed78%Z I : word) = Some W_6ed78.
Proof. vm_refl. Qed.
Lemma D_6ed78 : decode_any W_6ed78 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 2008%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ed7c : bv 32 := @BV 32 0x7d213823%Z I.
Lemma F_6ed7c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed7c%Z I : word) = Some W_6ed7c.
Proof. vm_refl. Qed.
Lemma D_6ed7c : decode_any W_6ed7c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 2000%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ed80 : bv 32 := @BV 32 0x7d313423%Z I.
Lemma F_6ed80 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed80%Z I : word) = Some W_6ed80.
Proof. vm_refl. Qed.
Lemma D_6ed80 : decode_any W_6ed80 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 1992%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ed84 : bv 32 := @BV 32 0x7d413023%Z I.
Lemma F_6ed84 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed84%Z I : word) = Some W_6ed84.
Proof. vm_refl. Qed.
Lemma D_6ed84 : decode_any W_6ed84 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 1984%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ed88 : bv 32 := @BV 32 0x7b513c23%Z I.
Lemma F_6ed88 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed88%Z I : word) = Some W_6ed88.
Proof. vm_refl. Qed.
Lemma D_6ed88 : decode_any W_6ed88 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 1976%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ed8c : bv 32 := @BV 32 0x7f010413%Z I.
Lemma F_6ed8c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed8c%Z I : word) = Some W_6ed8c.
Proof. vm_refl. Qed.
Lemma D_6ed8c : decode_any W_6ed8c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 2032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ed90 : bv 32 := @BV 32 0xfa010113%Z I.
Lemma F_6ed90 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed90%Z I : word) = Some W_6ed90.
Proof. vm_refl. Qed.
Lemma D_6ed90 : decode_any W_6ed90 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4000%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ed94 : bv 32 := @BV 32 0x00008913%Z I.
Lemma F_6ed94 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed94%Z I : word) = Some W_6ed94.
Proof. vm_refl. Qed.
Lemma D_6ed94 : decode_any W_6ed94 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ed98 : bv 32 := @BV 32 0x00050493%Z I.
Lemma F_6ed98 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed98%Z I : word) = Some W_6ed98.
Proof. vm_refl. Qed.
Lemma D_6ed98 : decode_any W_6ed98 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ed9c : bv 32 := @BV 32 0x10c0c0ef%Z I.
Lemma F_6ed9c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ed9c%Z I : word) = Some W_6ed9c.
Proof. vm_refl. Qed.
Lemma D_6ed9c : decode_any W_6ed9c = Some (Jal (@BV 5 1%Z I) (@BV 21 49420%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eda0 : bv 32 := @BV 32 0x02f4d593%Z I.
Lemma F_6eda0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eda0%Z I : word) = Some W_6eda0.
Proof. vm_refl. Qed.
Lemma D_6eda0 : decode_any W_6eda0 = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 6 47%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eda4 : bv 32 := @BV 32 0x0a059063%Z I.
Lemma F_6eda4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eda4%Z I : word) = Some W_6eda4.
Proof. vm_refl. Qed.
Lemma D_6eda4 : decode_any W_6eda4 = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 13 160%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eda8 : bv 32 := @BV 32 0x0204d593%Z I.
Lemma F_6eda8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eda8%Z I : word) = Some W_6eda8.
Proof. vm_refl. Qed.
Lemma D_6eda8 : decode_any W_6eda8 = Some (ShiftImm ALU_SRL (@BV 5 11%Z I) (@BV 5 9%Z I) (@BV 6 32%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6edac : bv 32 := @BV 32 0x00359613%Z I.
Lemma F_6edac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6edac%Z I : word) = Some W_6edac.
Proof. vm_refl. Qed.
Lemma D_6edac : decode_any W_6edac = Some (ShiftImm ALU_SLL (@BV 5 12%Z I) (@BV 5 11%Z I) (@BV 6 3%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6edb0 : bv 32 := @BV 32 0x00c50633%Z I.
Lemma F_6edb0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6edb0%Z I : word) = Some W_6edb0.
Proof. vm_refl. Qed.
Lemma D_6edb0 : decode_any W_6edb0 = Some (Op ALU_ADD (@BV 5 12%Z I) (@BV 5 10%Z I) (@BV 5 12%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6edb4 : bv 32 := @BV 32 0x00863683%Z I.
Lemma F_6edb4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6edb4%Z I : word) = Some W_6edb4.
Proof. vm_refl. Qed.
Lemma D_6edb4 : decode_any W_6edb4 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 12%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6edb8 : bv 32 := @BV 32 0x0230000f%Z I.
Lemma F_6edb8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6edb8%Z I : word) = Some W_6edb8.
Proof. vm_refl. Qed.
Lemma D_6edb8 : decode_any W_6edb8 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6edbc : bv 32 := @BV 32 0x08068463%Z I.
Lemma F_6edbc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6edbc%Z I : word) = Some W_6edbc.
Proof. vm_refl. Qed.
Lemma D_6edbc : decode_any W_6edbc = Some (Branch BC_EQ (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 13 136%Z I), 4%Z).
Proof. vm_refl. Qed.




































































































(* [comment removed for export] *)
Definition W_6ee44 : bv 32 := @BV 32 0x80040a13%Z I.
Lemma F_6ee44 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ee44%Z I : word) = Some W_6ee44.
Proof. vm_refl. Qed.
Lemma D_6ee44 : decode_any W_6ee44 = Some (OpImm ALU_ADD (@BV 5 20%Z I) (@BV 5 8%Z I) (@BV 12 2048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee48 : bv 32 := @BV 32 0xfb0a0a13%Z I.
Lemma F_6ee48 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ee48%Z I : word) = Some W_6ee48.
Proof. vm_refl. Qed.
Lemma D_6ee48 : decode_any W_6ee48 = Some (OpImm ALU_ADD (@BV 5 20%Z I) (@BV 5 20%Z I) (@BV 12 4016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee4c : bv 32 := @BV 32 0x80040513%Z I.
Lemma F_6ee4c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ee4c%Z I : word) = Some W_6ee4c.
Proof. vm_refl. Qed.
Lemma D_6ee4c : decode_any W_6ee4c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 2048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee50 : bv 32 := @BV 32 0xfc050513%Z I.
Lemma F_6ee50 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ee50%Z I : word) = Some W_6ee50.
Proof. vm_refl. Qed.
Lemma D_6ee50 : decode_any W_6ee50 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee54 : bv 32 := @BV 32 0x7ffa0a93%Z I.
Lemma F_6ee54 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ee54%Z I : word) = Some W_6ee54.
Proof. vm_refl. Qed.
Lemma D_6ee54 : decode_any W_6ee54 = Some (OpImm ALU_ADD (@BV 5 21%Z I) (@BV 5 20%Z I) (@BV 12 2047%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee58 : bv 32 := @BV 32 0x000ab4a3%Z I.
Lemma F_6ee58 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ee58%Z I : word) = Some W_6ee58.
Proof. vm_refl. Qed.
Lemma D_6ee58 : decode_any W_6ee58 = Some (Store SZ8 (@BV 5 21%Z I) (@BV 5 0%Z I) (@BV 12 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee5c : bv 32 := @BV 32 0x00aa3023%Z I.
Lemma F_6ee5c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ee5c%Z I : word) = Some W_6ee5c.
Proof. vm_refl. Qed.
Lemma D_6ee5c : decode_any W_6ee5c = Some (Store SZ8 (@BV 5 20%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee60 : bv 32 := @BV 32 0x000a3423%Z I.
Lemma F_6ee60 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ee60%Z I : word) = Some W_6ee60.
Proof. vm_refl. Qed.
Lemma D_6ee60 : decode_any W_6ee60 = Some (Store SZ8 (@BV 5 20%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee64 : bv 32 := @BV 32 0x550080ef%Z I.
Lemma F_6ee64 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ee64%Z I : word) = Some W_6ee64.
Proof. vm_refl. Qed.
Lemma D_6ee64 : decode_any W_6ee64 = Some (Jal (@BV 5 1%Z I) (@BV 21 34128%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee68 : bv 32 := @BV 32 0x00200593%Z I.
Lemma F_6ee68 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ee68%Z I : word) = Some W_6ee68.
Proof. vm_refl. Qed.
Lemma D_6ee68 : decode_any W_6ee68 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 2%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ee6c : bv 32 := @BV 32 0x02a5ea63%Z I.
Lemma F_6ee6c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ee6c%Z I : word) = Some W_6ee6c.
Proof. vm_refl. Qed.
Lemma D_6ee6c : decode_any W_6ee6c = Some (Branch BC_LTU (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 13 52%Z I), 4%Z).
Proof. vm_refl. Qed.





































(* [comment removed for export] *)
Definition W_6eea0 : bv 32 := @BV 32 0x7d5200ef%Z I.
Lemma F_6eea0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eea0%Z I : word) = Some W_6eea0.
Proof. vm_refl. Qed.
Lemma D_6eea0 : decode_any W_6eea0 = Some (Jal (@BV 5 1%Z I) (@BV 21 135124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eea4 : bv 32 := @BV 32 0x00097597%Z I.
Lemma F_6eea4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eea4%Z I : word) = Some W_6eea4.
Proof. vm_refl. Qed.
Lemma D_6eea4 : decode_any W_6eea4 = Some (Auipc (@BV 5 11%Z I) (@BV 20 151%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eea8 : bv 32 := @BV 32 0x0645b583%Z I.
Lemma F_6eea8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eea8%Z I : word) = Some W_6eea8.
Proof. vm_refl. Qed.
Lemma D_6eea8 : decode_any W_6eea8 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 100%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eeac : bv 32 := @BV 32 0x0225c983%Z I.
Lemma F_6eeac : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eeac%Z I : word) = Some W_6eeac.
Proof. vm_refl. Qed.
Lemma D_6eeac : decode_any W_6eeac = Some (Load SZ1 false (@BV 5 19%Z I) (@BV 5 11%Z I) (@BV 12 34%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eeb0 : bv 32 := @BV 32 0x00050913%Z I.
Lemma F_6eeb0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eeb0%Z I : word) = Some W_6eeb0.
Proof. vm_refl. Qed.
Lemma D_6eeb0 : decode_any W_6eeb0 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eeb4 : bv 32 := @BV 32 0x500080ef%Z I.
Lemma F_6eeb4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eeb4%Z I : word) = Some W_6eeb4.
Proof. vm_refl. Qed.
Lemma D_6eeb4 : decode_any W_6eeb4 = Some (Jal (@BV 5 1%Z I) (@BV 21 34048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eeb8 : bv 32 := @BV 32 0x00050793%Z I.
Lemma F_6eeb8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eeb8%Z I : word) = Some W_6eeb8.
Proof. vm_refl. Qed.
Lemma D_6eeb8 : decode_any W_6eeb8 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eebc : bv 32 := @BV 32 0x00153513%Z I.
Lemma F_6eebc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eebc%Z I : word) = Some W_6eebc.
Proof. vm_refl. Qed.
Lemma D_6eebc : decode_any W_6eebc = Some (OpImm ALU_SLTU (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eec0 : bv 32 := @BV 32 0xfff50513%Z I.
Lemma F_6eec0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eec0%Z I : word) = Some W_6eec0.
Proof. vm_refl. Qed.
Lemma D_6eec0 : decode_any W_6eec0 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eec4 : bv 32 := @BV 32 0x008575b3%Z I.
Lemma F_6eec4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eec4%Z I : word) = Some W_6eec4.
Proof. vm_refl. Qed.
Lemma D_6eec4 : decode_any W_6eec4 = Some (Op ALU_AND (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eec8 : bv 32 := @BV 32 0x00100513%Z I.
Lemma F_6eec8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eec8%Z I : word) = Some W_6eec8.
Proof. vm_refl. Qed.
Lemma D_6eec8 : decode_any W_6eec8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eecc : bv 32 := @BV 32 0x00bab4a3%Z I.
Lemma F_6eecc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eecc%Z I : word) = Some W_6eecc.
Proof. vm_refl. Qed.
Lemma D_6eecc : decode_any W_6eecc = Some (Store SZ8 (@BV 5 21%Z I) (@BV 5 11%Z I) (@BV 12 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eed0 : bv 32 := @BV 32 0x00f56a63%Z I.
Lemma F_6eed0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eed0%Z I : word) = Some W_6eed0.
Proof. vm_refl. Qed.
Lemma D_6eed0 : decode_any W_6eed0 = Some (Branch BC_LTU (@BV 5 10%Z I) (@BV 5 15%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.













(* [comment removed for export] *)
Definition W_6eee4 : bv 32 := @BV 32 0x80040513%Z I.
Lemma F_6eee4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eee4%Z I : word) = Some W_6eee4.
Proof. vm_refl. Qed.
Lemma D_6eee4 : decode_any W_6eee4 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 2048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eee8 : bv 32 := @BV 32 0xfb050513%Z I.
Lemma F_6eee8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eee8%Z I : word) = Some W_6eee8.
Proof. vm_refl. Qed.
Lemma D_6eee8 : decode_any W_6eee8 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eeec : bv 32 := @BV 32 0x00090593%Z I.
Lemma F_6eeec : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eeec%Z I : word) = Some W_6eeec.
Proof. vm_refl. Qed.
Lemma D_6eeec : decode_any W_6eeec = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eef0 : bv 32 := @BV 32 0x00040613%Z I.
Lemma F_6eef0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eef0%Z I : word) = Some W_6eef0.
Proof. vm_refl. Qed.
Lemma D_6eef0 : decode_any W_6eef0 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eef4 : bv 32 := @BV 32 0x00000693%Z I.
Lemma F_6eef4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eef4%Z I : word) = Some W_6eef4.
Proof. vm_refl. Qed.
Lemma D_6eef4 : decode_any W_6eef4 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eef8 : bv 32 := @BV 32 0x00098713%Z I.
Lemma F_6eef8 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eef8%Z I : word) = Some W_6eef8.
Proof. vm_refl. Qed.
Lemma D_6eef8 : decode_any W_6eef8 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6eefc : bv 32 := @BV 32 0x4c8080ef%Z I.
Lemma F_6eefc : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6eefc%Z I : word) = Some W_6eefc.
Proof. vm_refl. Qed.
Lemma D_6eefc : decode_any W_6eefc = Some (Jal (@BV 5 1%Z I) (@BV 21 33992%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef00 : bv 32 := @BV 32 0x80040593%Z I.
Lemma F_6ef00 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef00%Z I : word) = Some W_6ef00.
Proof. vm_refl. Qed.
Lemma D_6ef00 : decode_any W_6ef00 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 2048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef04 : bv 32 := @BV 32 0xfb058593%Z I.
Lemma F_6ef04 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef04%Z I : word) = Some W_6ef04.
Proof. vm_refl. Qed.
Lemma D_6ef04 : decode_any W_6ef04 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 4016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef08 : bv 32 := @BV 32 0x00100613%Z I.
Lemma F_6ef08 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef08%Z I : word) = Some W_6ef08.
Proof. vm_refl. Qed.
Lemma D_6ef08 : decode_any W_6ef08 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef0c : bv 32 := @BV 32 0x00048513%Z I.
Lemma F_6ef0c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef0c%Z I : word) = Some W_6ef0c.
Proof. vm_refl. Qed.
Lemma D_6ef0c : decode_any W_6ef0c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef10 : bv 32 := @BV 32 0xb48dd0ef%Z I.
Lemma F_6ef10 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef10%Z I : word) = Some W_6ef10.
Proof. vm_refl. Qed.
Lemma D_6ef10 : decode_any W_6ef10 = Some (Jal (@BV 5 1%Z I) (@BV 21 1954632%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef14 : bv 32 := @BV 32 0x06010113%Z I.
Lemma F_6ef14 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef14%Z I : word) = Some W_6ef14.
Proof. vm_refl. Qed.
Lemma D_6ef14 : decode_any W_6ef14 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef18 : bv 32 := @BV 32 0x7e813083%Z I.
Lemma F_6ef18 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef18%Z I : word) = Some W_6ef18.
Proof. vm_refl. Qed.
Lemma D_6ef18 : decode_any W_6ef18 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 2024%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef1c : bv 32 := @BV 32 0x7e013403%Z I.
Lemma F_6ef1c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef1c%Z I : word) = Some W_6ef1c.
Proof. vm_refl. Qed.
Lemma D_6ef1c : decode_any W_6ef1c = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 2016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef20 : bv 32 := @BV 32 0x7d813483%Z I.
Lemma F_6ef20 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef20%Z I : word) = Some W_6ef20.
Proof. vm_refl. Qed.
Lemma D_6ef20 : decode_any W_6ef20 = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 2008%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef24 : bv 32 := @BV 32 0x7d013903%Z I.
Lemma F_6ef24 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef24%Z I : word) = Some W_6ef24.
Proof. vm_refl. Qed.
Lemma D_6ef24 : decode_any W_6ef24 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 2000%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef28 : bv 32 := @BV 32 0x7c813983%Z I.
Lemma F_6ef28 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef28%Z I : word) = Some W_6ef28.
Proof. vm_refl. Qed.
Lemma D_6ef28 : decode_any W_6ef28 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 1992%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef2c : bv 32 := @BV 32 0x7c013a03%Z I.
Lemma F_6ef2c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef2c%Z I : word) = Some W_6ef2c.
Proof. vm_refl. Qed.
Lemma D_6ef2c : decode_any W_6ef2c = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 1984%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef30 : bv 32 := @BV 32 0x7b813a83%Z I.
Lemma F_6ef30 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef30%Z I : word) = Some W_6ef30.
Proof. vm_refl. Qed.
Lemma D_6ef30 : decode_any W_6ef30 = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 1976%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef34 : bv 32 := @BV 32 0x7f010113%Z I.
Lemma F_6ef34 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef34%Z I : word) = Some W_6ef34.
Proof. vm_refl. Qed.
Lemma D_6ef34 : decode_any W_6ef34 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 2032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef38 : bv 32 := @BV 32 0x00008067%Z I.
Lemma F_6ef38 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6ef38%Z I : word) = Some W_6ef38.
Proof. vm_refl. Qed.
Lemma D_6ef38 : decode_any W_6ef38 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef3c : bv 32 := @BV 32 0x81010113%Z I.

Lemma D_6ef3c : decode_any W_6ef3c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 2064%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef40 : bv 32 := @BV 32 0x7e113423%Z I.

Lemma D_6ef40 : decode_any W_6ef40 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 2024%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef44 : bv 32 := @BV 32 0x7e813023%Z I.

Lemma D_6ef44 : decode_any W_6ef44 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 2016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef48 : bv 32 := @BV 32 0x7c913c23%Z I.

Lemma D_6ef48 : decode_any W_6ef48 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 9%Z I) (@BV 12 2008%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef4c : bv 32 := @BV 32 0x7d213823%Z I.

Lemma D_6ef4c : decode_any W_6ef4c = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 18%Z I) (@BV 12 2000%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef50 : bv 32 := @BV 32 0x7d313423%Z I.

Lemma D_6ef50 : decode_any W_6ef50 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 19%Z I) (@BV 12 1992%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef54 : bv 32 := @BV 32 0x7d413023%Z I.

Lemma D_6ef54 : decode_any W_6ef54 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 20%Z I) (@BV 12 1984%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef58 : bv 32 := @BV 32 0x7b513c23%Z I.

Lemma D_6ef58 : decode_any W_6ef58 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 21%Z I) (@BV 12 1976%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef5c : bv 32 := @BV 32 0x7f010413%Z I.

Lemma D_6ef5c : decode_any W_6ef5c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 2032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef60 : bv 32 := @BV 32 0xfa010113%Z I.

Lemma D_6ef60 : decode_any W_6ef60 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4000%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef64 : bv 32 := @BV 32 0x00008913%Z I.

Lemma D_6ef64 : decode_any W_6ef64 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef68 : bv 32 := @BV 32 0x00050493%Z I.

Lemma D_6ef68 : decode_any W_6ef68 = Some (OpImm ALU_ADD (@BV 5 9%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef6c : bv 32 := @BV 32 0x6c0070ef%Z I.

Lemma D_6ef6c : decode_any W_6ef6c = Some (Jal (@BV 5 1%Z I) (@BV 21 30400%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef70 : bv 32 := @BV 32 0x06050063%Z I.

Lemma D_6ef70 : decode_any W_6ef70 = Some (Branch BC_EQ (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 13 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef74 : bv 32 := @BV 32 0x80040a13%Z I.

Lemma D_6ef74 : decode_any W_6ef74 = Some (OpImm ALU_ADD (@BV 5 20%Z I) (@BV 5 8%Z I) (@BV 12 2048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef78 : bv 32 := @BV 32 0xfb0a0a13%Z I.

Lemma D_6ef78 : decode_any W_6ef78 = Some (OpImm ALU_ADD (@BV 5 20%Z I) (@BV 5 20%Z I) (@BV 12 4016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef7c : bv 32 := @BV 32 0x80040513%Z I.

Lemma D_6ef7c : decode_any W_6ef7c = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 2048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef80 : bv 32 := @BV 32 0xfc050513%Z I.

Lemma D_6ef80 : decode_any W_6ef80 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef84 : bv 32 := @BV 32 0x7ffa0a93%Z I.

Lemma D_6ef84 : decode_any W_6ef84 = Some (OpImm ALU_ADD (@BV 5 21%Z I) (@BV 5 20%Z I) (@BV 12 2047%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef88 : bv 32 := @BV 32 0x000ab4a3%Z I.

Lemma D_6ef88 : decode_any W_6ef88 = Some (Store SZ8 (@BV 5 21%Z I) (@BV 5 0%Z I) (@BV 12 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef8c : bv 32 := @BV 32 0x00aa3023%Z I.

Lemma D_6ef8c : decode_any W_6ef8c = Some (Store SZ8 (@BV 5 20%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef90 : bv 32 := @BV 32 0x000a3423%Z I.

Lemma D_6ef90 : decode_any W_6ef90 = Some (Store SZ8 (@BV 5 20%Z I) (@BV 5 0%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef94 : bv 32 := @BV 32 0x420080ef%Z I.

Lemma D_6ef94 : decode_any W_6ef94 = Some (Jal (@BV 5 1%Z I) (@BV 21 33824%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef98 : bv 32 := @BV 32 0x00200593%Z I.

Lemma D_6ef98 : decode_any W_6ef98 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 0%Z I) (@BV 12 2%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ef9c : bv 32 := @BV 32 0x06a5e263%Z I.

Lemma D_6ef9c : decode_any W_6ef9c = Some (Branch BC_LTU (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 13 100%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6efa0 : bv 32 := @BV 32 0x414080ef%Z I.



(* [comment removed for export] *)
Definition W_6efa4 : bv 32 := @BV 32 0x00aa2423%Z I.



(* [comment removed for export] *)
Definition W_6efa8 : bv 32 := @BV 32 0x40c080ef%Z I.



(* [comment removed for export] *)
Definition W_6efac : bv 32 := @BV 32 0x0a050a63%Z I.



(* [comment removed for export] *)
Definition W_6efb0 : bv 32 := @BV 32 0x008ab4a3%Z I.



(* [comment removed for export] *)
Definition W_6efb4 : bv 32 := @BV 32 0x6c1200ef%Z I.



(* [comment removed for export] *)
Definition W_6efb8 : bv 32 := @BV 32 0x00aa3823%Z I.



(* [comment removed for export] *)
Definition W_6efbc : bv 32 := @BV 32 0x3f8080ef%Z I.



(* [comment removed for export] *)
Definition W_6efc0 : bv 32 := @BV 32 0x00200593%Z I.



(* [comment removed for export] *)
Definition W_6efc4 : bv 32 := @BV 32 0x08b56e63%Z I.



(* [comment removed for export] *)
Definition W_6efc8 : bv 32 := @BV 32 0x012a3c23%Z I.



(* [comment removed for export] *)
Definition W_6efcc : bv 32 := @BV 32 0x0940006f%Z I.



(* [comment removed for export] *)
Definition W_6efd0 : bv 32 := @BV 32 0x00800593%Z I.



(* [comment removed for export] *)
Definition W_6efd4 : bv 32 := @BV 32 0x00048513%Z I.



(* [comment removed for export] *)
Definition W_6efd8 : bv 32 := @BV 32 0x06010113%Z I.



(* [comment removed for export] *)
Definition W_6efdc : bv 32 := @BV 32 0x7e813083%Z I.



(* [comment removed for export] *)
Definition W_6efe0 : bv 32 := @BV 32 0x7e013403%Z I.



(* [comment removed for export] *)
Definition W_6efe4 : bv 32 := @BV 32 0x7d813483%Z I.



(* [comment removed for export] *)
Definition W_6efe8 : bv 32 := @BV 32 0x7d013903%Z I.



(* [comment removed for export] *)
Definition W_6efec : bv 32 := @BV 32 0x7c813983%Z I.



(* [comment removed for export] *)
Definition W_6eff0 : bv 32 := @BV 32 0x7c013a03%Z I.



(* [comment removed for export] *)
Definition W_6eff4 : bv 32 := @BV 32 0x7b813a83%Z I.



(* [comment removed for export] *)
Definition W_6eff8 : bv 32 := @BV 32 0x7f010113%Z I.



(* [comment removed for export] *)
Definition W_6effc : bv 32 := @BV 32 0x09c0006f%Z I.



(* [comment removed for export] *)
Definition W_6f000 : bv 32 := @BV 32 0x675200ef%Z I.

Lemma D_6f000 : decode_any W_6f000 = Some (Jal (@BV 5 1%Z I) (@BV 21 134772%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f004 : bv 32 := @BV 32 0x00097597%Z I.
Lemma F_6f004 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6f004%Z I : word) = Some W_6f004.
Proof. vm_refl. Qed.
Lemma D_6f004 : decode_any W_6f004 = Some (Auipc (@BV 5 11%Z I) (@BV 20 151%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f008 : bv 32 := @BV 32 0xf045b583%Z I.
Lemma F_6f008 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x6f008%Z I : word) = Some W_6f008.
Proof. vm_refl. Qed.
Lemma D_6f008 : decode_any W_6f008 = Some (Load SZ8 true (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 3844%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f00c : bv 32 := @BV 32 0x0225c983%Z I.

Lemma D_6f00c : decode_any W_6f00c = Some (Load SZ1 false (@BV 5 19%Z I) (@BV 5 11%Z I) (@BV 12 34%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f010 : bv 32 := @BV 32 0x00050913%Z I.

Lemma D_6f010 : decode_any W_6f010 = Some (OpImm ALU_ADD (@BV 5 18%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f014 : bv 32 := @BV 32 0x3a0080ef%Z I.

Lemma D_6f014 : decode_any W_6f014 = Some (Jal (@BV 5 1%Z I) (@BV 21 33696%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f018 : bv 32 := @BV 32 0x00050793%Z I.

Lemma D_6f018 : decode_any W_6f018 = Some (OpImm ALU_ADD (@BV 5 15%Z I) (@BV 5 10%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f01c : bv 32 := @BV 32 0x00153513%Z I.

Lemma D_6f01c : decode_any W_6f01c = Some (OpImm ALU_SLTU (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f020 : bv 32 := @BV 32 0xfff50513%Z I.

Lemma D_6f020 : decode_any W_6f020 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4095%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f024 : bv 32 := @BV 32 0x008575b3%Z I.

Lemma D_6f024 : decode_any W_6f024 = Some (Op ALU_AND (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 5 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f028 : bv 32 := @BV 32 0x00100513%Z I.

Lemma D_6f028 : decode_any W_6f028 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f02c : bv 32 := @BV 32 0x00bab4a3%Z I.

Lemma D_6f02c : decode_any W_6f02c = Some (Store SZ8 (@BV 5 21%Z I) (@BV 5 11%Z I) (@BV 12 9%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f030 : bv 32 := @BV 32 0x00f56a63%Z I.

Lemma D_6f030 : decode_any W_6f030 = Some (Branch BC_LTU (@BV 5 10%Z I) (@BV 5 15%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f034 : bv 32 := @BV 32 0x00a79463%Z I.



(* [comment removed for export] *)
Definition W_6f038 : bv 32 := @BV 32 0x012a3823%Z I.



(* [comment removed for export] *)
Definition W_6f03c : bv 32 := @BV 32 0x00fa2423%Z I.



(* [comment removed for export] *)
Definition W_6f040 : bv 32 := @BV 32 0x0200006f%Z I.



(* [comment removed for export] *)
Definition W_6f044 : bv 32 := @BV 32 0x80040513%Z I.

Lemma D_6f044 : decode_any W_6f044 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 8%Z I) (@BV 12 2048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f048 : bv 32 := @BV 32 0xfb050513%Z I.

Lemma D_6f048 : decode_any W_6f048 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 10%Z I) (@BV 12 4016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f04c : bv 32 := @BV 32 0x00090593%Z I.

Lemma D_6f04c : decode_any W_6f04c = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 18%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f050 : bv 32 := @BV 32 0x00040613%Z I.

Lemma D_6f050 : decode_any W_6f050 = Some (OpImm ALU_ADD (@BV 5 12%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f054 : bv 32 := @BV 32 0x00000693%Z I.

Lemma D_6f054 : decode_any W_6f054 = Some (OpImm ALU_ADD (@BV 5 13%Z I) (@BV 5 0%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f058 : bv 32 := @BV 32 0x00098713%Z I.

Lemma D_6f058 : decode_any W_6f058 = Some (OpImm ALU_ADD (@BV 5 14%Z I) (@BV 5 19%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f05c : bv 32 := @BV 32 0x368080ef%Z I.

Lemma D_6f05c : decode_any W_6f05c = Some (Jal (@BV 5 1%Z I) (@BV 21 33640%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f060 : bv 32 := @BV 32 0x80040593%Z I.

Lemma D_6f060 : decode_any W_6f060 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 2048%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f064 : bv 32 := @BV 32 0xfb058593%Z I.

Lemma D_6f064 : decode_any W_6f064 = Some (OpImm ALU_ADD (@BV 5 11%Z I) (@BV 5 11%Z I) (@BV 12 4016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f068 : bv 32 := @BV 32 0x00048513%Z I.

Lemma D_6f068 : decode_any W_6f068 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 9%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f06c : bv 32 := @BV 32 0xcccdd0ef%Z I.

Lemma D_6f06c : decode_any W_6f06c = Some (Jal (@BV 5 1%Z I) (@BV 21 1955020%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f070 : bv 32 := @BV 32 0x06010113%Z I.

Lemma D_6f070 : decode_any W_6f070 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 96%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f074 : bv 32 := @BV 32 0x7e813083%Z I.

Lemma D_6f074 : decode_any W_6f074 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 2024%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f078 : bv 32 := @BV 32 0x7e013403%Z I.

Lemma D_6f078 : decode_any W_6f078 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 2016%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f07c : bv 32 := @BV 32 0x7d813483%Z I.

Lemma D_6f07c : decode_any W_6f07c = Some (Load SZ8 true (@BV 5 9%Z I) (@BV 5 2%Z I) (@BV 12 2008%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f080 : bv 32 := @BV 32 0x7d013903%Z I.

Lemma D_6f080 : decode_any W_6f080 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 2%Z I) (@BV 12 2000%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f084 : bv 32 := @BV 32 0x7c813983%Z I.

Lemma D_6f084 : decode_any W_6f084 = Some (Load SZ8 true (@BV 5 19%Z I) (@BV 5 2%Z I) (@BV 12 1992%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f088 : bv 32 := @BV 32 0x7c013a03%Z I.

Lemma D_6f088 : decode_any W_6f088 = Some (Load SZ8 true (@BV 5 20%Z I) (@BV 5 2%Z I) (@BV 12 1984%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f08c : bv 32 := @BV 32 0x7b813a83%Z I.

Lemma D_6f08c : decode_any W_6f08c = Some (Load SZ8 true (@BV 5 21%Z I) (@BV 5 2%Z I) (@BV 12 1976%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f090 : bv 32 := @BV 32 0x7f010113%Z I.

Lemma D_6f090 : decode_any W_6f090 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 2032%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f094 : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_6f094 : decode_any W_6f094 = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.
























































































































































































































































































































































































































































































































