(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6c7A.v at 4c23b042570d for reac-pw/fuzz_role's
   image B (fuzz_role.asan-ubsan): image B's pcs; the atoms are the B head's extra env slots (t in atom 33, s in atom
   34); the names are w6cb_; the module requires no image file; w6cb_s12_U added (the unsigned value, for the branch
   conditions). *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): two closed arithmetic facts
   about case 7 of ent_build (pod.h:353-354), for the head lemma w6cb_h7 (lib/AU/RPgW6c7.v). Proves no function
   (kind: model lemma).

   The compiler computes the two remainders of case 7 without a division:
   - the type t mod 21 by the multiply with 0x87 (135) at 0x8107c..0x810ac (`li a2,135; mul; srli 8; subw; slli 56;
     srli 57; add; slli 56; srli 60; li a3,21; mul; subw; zext.b`). The symbolic engine leaves that value as
     w6cb_e7t, an expression in the one atom 33 (the head's extra env slot that holds t, the byte `lbu` reads at
     0x81074);
   - the size s mod 12 by the multiply with the real-frame cell [R+0x10] = 0x15555556 (357913942) at 0x816f0..0x81708
     (`ld a0,0x10(s1); mul; srli 32; slli 4; slli 2; sub; add`). The engine leaves that value as w6cb_e7s, an
     expression in the one atom 34 (the slot that holds s, the byte `lbu` reads at 0x816e4).
   w6cb_t21: when atom 33 holds t with 0 <= t < 256, w6cb_e7t denotes t mod 21.
   w6cb_s12: when atom 34 holds s with 0 <= s < 256, w6cb_e7s denotes s mod 12; w6cb_s12_U is its unsigned value.
   Each expression reads one atom only, so its value is the value in the environment w6cb_env v (every atom holds v);
   the 256 cases are checked by computation (w6cb_chk). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition w6cb_e7t : sv :=
SAlu ALU_AND
 (SAluw ALU_SUB (SOff 33 0)
   (SMd M_MUL
     (SAlu ALU_SRL
       (SAlu ALU_SLL
         (SAlu ALU_ADD
           (SAlu ALU_SRL
             (SAlu ALU_SLL
               (SAlu ALU_SUB (SOff 33 0) (SAlu ALU_SRL (SMd M_MUL (SOff 33 0) (SLit 135)) (SLit 8)))
               (SLit 56))
             (SLit 57))
           (SAlu ALU_SRL (SMd M_MUL (SOff 33 0) (SLit 135)) (SLit 8)))
         (SLit 56))
       (SLit 60))
     (SLit 21)))
 (SLit 255).
Definition w6cb_e7s : sv :=
SAlu ALU_ADD (SOff 34 0)
 (SAlu ALU_SUB
   (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SOff 34 0) (SLit 357913942)) (SLit 32)) (SLit 2))
   (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SOff 34 0) (SLit 357913942)) (SLit 32)) (SLit 4))).

(* the environment in which every atom holds v *)
Definition w6cb_env (v : Z) : env := mkEnv (fun _ => Z_to_bv 64 v) (fun _ => []).

(* e denotes v mod m in w6cb_env v, for each v in [0, 256) *)
Definition w6cb_chk (e : sv) (m : Z) : bool :=
forallb (fun n => let v := Z.of_nat n in bv_eqb (sv_denot (w6cb_env v) e) (Z_to_bv 64 (v mod m))) (seq 0 256).
Lemma w6cb_chk_ok : forall e m, w6cb_chk e m = true ->
forall v, 0 <= v < 256 -> sv_denot (w6cb_env v) e = Z_to_bv 64 (v mod m).
Proof.
intros e m H v Hv. unfold w6cb_chk in H. rewrite forallb_forall in H.
specialize (H (Z.to_nat v)). rewrite Z2Nat.id in H by lia.
apply bv_eqb_true_iff. apply H. apply in_seq. lia.
Qed.

Lemma w6cb_chk_t : w6cb_chk w6cb_e7t 21 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w6cb_chk_s : w6cb_chk w6cb_e7s 12 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma w6cb_e7t_env : forall (E : env) t, ew E 33 = Z_to_bv 64 t -> sv_denot E w6cb_e7t = sv_denot (w6cb_env t) w6cb_e7t.
Proof. intros E t H. unfold w6cb_e7t. cbn [sv_denot]. rewrite H. reflexivity. Qed.
Lemma w6cb_e7s_env : forall (E : env) s, ew E 34 = Z_to_bv 64 s -> sv_denot E w6cb_e7s = sv_denot (w6cb_env s) w6cb_e7s.
Proof. intros E s H. unfold w6cb_e7s. cbn [sv_denot]. rewrite H. reflexivity. Qed.

Lemma w6cb_t21 : forall (E : env) t, ew E 33 = Z_to_bv 64 t -> 0 <= t < 256 ->
sv_denot E w6cb_e7t = Z_to_bv 64 (t mod 21).
Proof.
intros E t H Ht. rewrite (w6cb_e7t_env E t H). exact (w6cb_chk_ok _ _ w6cb_chk_t t Ht).
Qed.
Lemma w6cb_s12 : forall (E : env) s, ew E 34 = Z_to_bv 64 s -> 0 <= s < 256 ->
sv_denot E w6cb_e7s = Z_to_bv 64 (s mod 12).
Proof.
intros E s H Hs. rewrite (w6cb_e7s_env E s H). exact (w6cb_chk_ok _ _ w6cb_chk_s s Hs).
Qed.
Lemma w6cb_s12_U : forall (E : env) s, ew E 34 = Z_to_bv 64 s -> 0 <= s < 256 -> U E w6cb_e7s = s mod 12.
Proof.
intros E s H Hs. unfold U. rewrite (w6cb_s12 E s H Hs).
apply unsigned_lit_small. pose proof (Z.mod_pos_bound s 12 ltac:(lia)). lia.
Qed.
