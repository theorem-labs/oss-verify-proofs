(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): two closed arithmetic facts
   about case 7 of ent_build (pod.h:353-354). Proves no function (kind: model lemma).

   The compiler computes the two remainders of case 7 without a division:
   - the type t mod 21 by the multiply with 0x87 (135) at 0x81ca0..0x81cd0. The symbolic engine leaves that value as
     w6c_e7t, an expression in the one atom 34 (the register that holds t);
   - the size s mod 12 by the multiply with 0x15555556 (357913942) at 0x821cc..0x821e4. The symbolic engine leaves that
     value as w6c_e7s, an expression in the one atom 36 (the register that holds s).
   w6c_t21: when atom 34 holds t with 0 <= t < 256, w6c_e7t denotes t mod 21.
   w6c_s12: when atom 36 holds s with 0 <= s < 256, w6c_e7s denotes s mod 12.
   Each expression reads one atom only, so its value is the value in the environment w6c_env v (every atom holds v);
   the 256 cases are checked by computation (w6c_chk). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSteps HPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition w6c_e7t : sv :=
SAlu ALU_AND
 (SAluw ALU_SUB (SOff 34 0)
   (SMd M_MUL
     (SAlu ALU_SRL
       (SAlu ALU_SLL
         (SAlu ALU_ADD
           (SAlu ALU_SRL
             (SAlu ALU_SLL
               (SAlu ALU_SUB (SOff 34 0) (SAlu ALU_SRL (SMd M_MUL (SOff 34 0) (SLit 135)) (SLit 8)))
               (SLit 56))
             (SLit 57))
           (SAlu ALU_SRL (SMd M_MUL (SOff 34 0) (SLit 135)) (SLit 8)))
         (SLit 56))
       (SLit 60))
     (SLit 21)))
 (SLit 255).
Definition w6c_e7s : sv :=
SAlu ALU_ADD (SOff 36 0)
 (SAlu ALU_SUB
   (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SOff 36 0) (SLit 357913942)) (SLit 32)) (SLit 2))
   (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SOff 36 0) (SLit 357913942)) (SLit 32)) (SLit 4))).

(* the environment in which every atom holds v *)
Definition w6c_env (v : Z) : env := mkEnv (fun _ => Z_to_bv 64 v) (fun _ => []).

(* e denotes v mod m in w6c_env v, for each v in [0, 256) *)
Definition w6c_chk (e : sv) (m : Z) : bool :=
forallb (fun n => let v := Z.of_nat n in bv_eqb (sv_denot (w6c_env v) e) (Z_to_bv 64 (v mod m))) (seq 0 256).
Lemma w6c_chk_ok : forall e m, w6c_chk e m = true ->
forall v, 0 <= v < 256 -> sv_denot (w6c_env v) e = Z_to_bv 64 (v mod m).
Proof.
intros e m H v Hv. unfold w6c_chk in H. rewrite forallb_forall in H.
specialize (H (Z.to_nat v)). rewrite Z2Nat.id in H by lia.
apply bv_eqb_true_iff. apply H. apply in_seq. lia.
Qed.

Lemma w6c_chk_t : w6c_chk w6c_e7t 21 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w6c_chk_s : w6c_chk w6c_e7s 12 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma w6c_e7t_env : forall (E : env) t, ew E 34 = Z_to_bv 64 t -> sv_denot E w6c_e7t = sv_denot (w6c_env t) w6c_e7t.
Proof. intros E t H. unfold w6c_e7t. cbn [sv_denot]. rewrite H. reflexivity. Qed.
Lemma w6c_e7s_env : forall (E : env) s, ew E 36 = Z_to_bv 64 s -> sv_denot E w6c_e7s = sv_denot (w6c_env s) w6c_e7s.
Proof. intros E s H. unfold w6c_e7s. cbn [sv_denot]. rewrite H. reflexivity. Qed.

Lemma w6c_t21 : forall (E : env) t, ew E 34 = Z_to_bv 64 t -> 0 <= t < 256 -> sv_denot E w6c_e7t = Z_to_bv 64 (t mod 21).
Proof.
intros E t H Ht. rewrite (w6c_e7t_env E t H). exact (w6c_chk_ok _ _ w6c_chk_t t Ht).
Qed.
Lemma w6c_s12 : forall (E : env) s, ew E 36 = Z_to_bv 64 s -> 0 <= s < 256 -> sv_denot E w6c_e7s = Z_to_bv 64 (s mod 12).
Proof.
intros E s H Hs. rewrite (w6c_e7s_env E s H). exact (w6c_chk_ok _ _ w6c_chk_s s Hs).
Qed.

Print Assumptions w6c_t21.
Print Assumptions w6c_s12.
