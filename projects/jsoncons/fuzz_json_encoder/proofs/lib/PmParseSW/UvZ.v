(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec AxSymExec3.
Import ListNotations. Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module UVZ.
(* [comment removed for export] *)
Definition w64 (z : Z) : Z := z mod 2 ^ 64.
Definition sx32 (z : Z) : Z := let u := z mod 2 ^ 32 in if u <? 2 ^ 31 then u else u + 2 ^ 64 - 2 ^ 32.
Definition sg64 (u : Z) : Z := if u <? 2 ^ 63 then u else u - 2 ^ 64.

Fixpoint zev (rho : nat -> option Z) (e : expr) : option Z :=
  match e with
  | ELit z => Some (w64 z)
  | EVar n => rho n
  | EAlu op a b =>
      match zev rho a, zev rho b with
      | Some x, Some y =>
          match op with
          | ALU_ADD => Some (w64 (x + y))
          | ALU_SUB => Some (w64 (x - y))
          | ALU_AND => Some (Z.land x y)
          | ALU_OR => Some (Z.lor x y)
          | ALU_XOR => Some (Z.lxor x y)
          | ALU_SLL => Some (w64 (Z.shiftl x (Z.land y 63)))
          | ALU_SRL => Some (Z.shiftr x (Z.land y 63))
          | ALU_SLTU => Some (if x <? y then 1 else 0)
          | ALU_SLT => Some (if sg64 x <? sg64 y then 1 else 0)
          | ALU_SRA => None
          end
      | _, _ => None
      end
  | EAluw op a b =>
      match zev rho a, zev rho b with
      | Some x, Some y =>
          let x' := x mod 2 ^ 32 in let y' := y mod 2 ^ 32 in
          match op with
          | ALU_ADD => Some (sx32 (x' + y'))
          | ALU_SUB => Some (sx32 (x' - y'))
          | ALU_AND => Some (sx32 (Z.land x' y'))
          | ALU_OR => Some (sx32 (Z.lor x' y'))
          | ALU_SLL => Some (sx32 (Z.shiftl x' (Z.land y' 31)))
          | ALU_SRL => Some (sx32 (Z.shiftr x' (Z.land y' 31)))
          | _ => None
          end
      | _, _ => None
      end
  | EMd M_MUL a b =>
      match zev rho a, zev rho b with
      | Some x, Some y => Some (w64 (x * y))
      | _, _ => None
      end
  | EMd _ _ _ => None
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      match zev rho a with
      | Some x => Some (w64 (ext_Z sx lo n x))
      | None => None
      end
  | EBlob _ _ _ _ => None
  end.

(* [comment removed for export] *)
Lemma modulus64 : bv_modulus 64 = 2 ^ 64. Proof. reflexivity. Qed.
Lemma modulus32 : bv_modulus 32 = 2 ^ 32. Proof. reflexivity. Qed.
Lemma wrap64 : forall z, bv_wrap 64 z = w64 z. Proof. intros z. unfold bv_wrap, w64. rewrite modulus64. reflexivity. Qed.
Lemma wrap32 : forall z, bv_wrap 32 z = z mod 2 ^ 32. Proof. intros z. unfold bv_wrap. rewrite modulus32. reflexivity. Qed.
Lemma u64_range : forall b : bv 64, 0 <= bv_unsigned b < 2 ^ 64.
Proof. intros b. pose proof (bv_unsigned_in_range 64 b) as H. rewrite modulus64 in H. lia. Qed.
Lemma u32_range : forall b : bv 32, 0 <= bv_unsigned b < 2 ^ 32.
Proof. intros b. pose proof (bv_unsigned_in_range 32 b) as H. rewrite modulus32 in H. lia. Qed.
Lemma swrap64 : forall u, 0 <= u < 2 ^ 64 -> bv_swrap 64 u = sg64 u.
Proof.
  intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus. rewrite modulus64. change (2 ^ 64 `div` 2) with (2 ^ 63). unfold sg64.
  destruct (Z.ltb_spec u (2 ^ 63)) as [L|L].
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap32 : forall u, 0 <= u < 2 ^ 32 -> bv_swrap 32 u = (if u <? 2 ^ 31 then u else u - 2 ^ 32).
Proof.
  intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus. rewrite modulus32. change (2 ^ 32 `div` 2) with (2 ^ 31).
  destruct (Z.ltb_spec u (2 ^ 31)) as [L|L].
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma signed64 : forall b : bv 64, bv_signed b = sg64 (bv_unsigned b).
Proof. intros b. unfold bv_signed. apply swrap64. apply u64_range. Qed.
(* [comment removed for export] *)
Lemma sext32_64 : forall r : bv 32, bv_unsigned (sext 64 r) = sx32 (bv_unsigned r).
Proof.
  intros r. unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed. pose proof (u32_range r) as Hr.
  rewrite (swrap32 _ Hr). rewrite wrap64. unfold w64, sx32. rewrite (Z.mod_small (bv_unsigned r) (2 ^ 32)) by lia.
  destruct (Z.ltb_spec (bv_unsigned r) (2 ^ 31)) as [L|L].
  - rewrite Z.mod_small by lia. reflexivity.
  - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma low32_u : forall w : bv 64, bv_unsigned (low32 w) = bv_unsigned w mod 2 ^ 32.
Proof. intros w. unfold low32. rewrite bv_extract_unsigned. rewrite wrap32. rewrite Z.shiftr_0_r. reflexivity. Qed.
Lemma lit64_u : forall z, bv_unsigned (Z_to_bv 64 z) = w64 z.
Proof. intros z. rewrite Z_to_bv_unsigned. apply wrap64. Qed.
Lemma mask63 : bv_unsigned (Z_to_bv 64 63) = 63. Proof. reflexivity. Qed.
Lemma mask31 : bv_unsigned (Z_to_bv 32 31) = 31. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma alu64_sound : forall op (a b : bv 64) z,
  match op with
  | ALU_ADD => Some (w64 (bv_unsigned a + bv_unsigned b))
  | ALU_SUB => Some (w64 (bv_unsigned a - bv_unsigned b))
  | ALU_AND => Some (Z.land (bv_unsigned a) (bv_unsigned b))
  | ALU_OR => Some (Z.lor (bv_unsigned a) (bv_unsigned b))
  | ALU_XOR => Some (Z.lxor (bv_unsigned a) (bv_unsigned b))
  | ALU_SLL => Some (w64 (Z.shiftl (bv_unsigned a) (Z.land (bv_unsigned b) 63)))
  | ALU_SRL => Some (Z.shiftr (bv_unsigned a) (Z.land (bv_unsigned b) 63))
  | ALU_SLTU => Some (if bv_unsigned a <? bv_unsigned b then 1 else 0)
  | ALU_SLT => Some (if sg64 (bv_unsigned a) <? sg64 (bv_unsigned b) then 1 else 0)
  | ALU_SRA => None
  end = Some z -> bv_unsigned (alu64 op a b) = z.
Proof.
  intros op a b z H. unfold alu64, alu. destruct op; try discriminate H; injection H as <-.
  - rewrite bv_add_unsigned. apply wrap64.
  - rewrite bv_sub_unsigned. apply wrap64.
  - rewrite bv_shiftl_unsigned, bv_and_unsigned, mask63. apply wrap64.
  - unfold bv_lts. rewrite !signed64. destruct (_ <? _); reflexivity.
  - unfold bv_ltu. destruct (_ <? _); reflexivity.
  - apply bv_xor_unsigned.
  - rewrite bv_shiftr_unsigned, bv_and_unsigned, mask63. reflexivity.
  - apply bv_or_unsigned.
  - apply bv_and_unsigned.
Qed.
(* [comment removed for export] *)
Lemma aluw_sound : forall op (a b : bv 64) z,
  let x' := bv_unsigned a mod 2 ^ 32 in let y' := bv_unsigned b mod 2 ^ 32 in
  match op with
  | ALU_ADD => Some (sx32 (x' + y'))
  | ALU_SUB => Some (sx32 (x' - y'))
  | ALU_AND => Some (sx32 (Z.land x' y'))
  | ALU_OR => Some (sx32 (Z.lor x' y'))
  | ALU_SLL => Some (sx32 (Z.shiftl x' (Z.land y' 31)))
  | ALU_SRL => Some (sx32 (Z.shiftr x' (Z.land y' 31)))
  | _ => None
  end = Some z -> bv_unsigned (sext 64 (alu32 op (low32 a) (low32 b))) = z.
Proof.
  intros op a b z. cbv zeta. intros H. rewrite sext32_64. unfold alu32, alu.
  assert (SX : forall u, sx32 (u mod 2 ^ 32) = sx32 u) by (intros u; unfold sx32; rewrite Z.mod_mod by lia; reflexivity).
  destruct op; try discriminate H; injection H as <-.
  - rewrite bv_add_unsigned, wrap32, !low32_u. apply SX.
  - rewrite bv_sub_unsigned, wrap32, !low32_u. apply SX.
  - rewrite bv_shiftl_unsigned, wrap32, bv_and_unsigned, mask31, !low32_u. apply SX.
  - rewrite bv_shiftr_unsigned, bv_and_unsigned, mask31, !low32_u. reflexivity.
  - rewrite bv_or_unsigned, !low32_u. reflexivity.
  - rewrite bv_and_unsigned, !low32_u. reflexivity.
Qed.

Theorem zev_sound : forall (E : env) (rho : nat -> option Z),
  (forall n v, rho n = Some v -> bv_unsigned (ev E n) = v) ->
  forall e z, zev rho e = Some z -> bv_unsigned (edenot E e) = z.
Proof.
  intros E rho Hrho. induction e as [z0|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros z H; cbn [zev] in H; cbn [edenot].
  - injection H as <-. apply lit64_u.
  - exact (Hrho n z H).
  - destruct (zev rho a) as [x|] eqn:Ha; [|discriminate H]. destruct (zev rho b) as [y|] eqn:Hb; [|destruct op; discriminate H].
    rewrite <- (IHa x eq_refl), <- (IHb y eq_refl) in H. exact (alu64_sound op _ _ z H).
  - destruct (zev rho a) as [x|] eqn:Ha; [|discriminate H]. destruct (zev rho b) as [y|] eqn:Hb; [|destruct op; discriminate H].
    rewrite <- (IHa x eq_refl), <- (IHb y eq_refl) in H. exact (aluw_sound op _ _ z H).
  - destruct op; try discriminate H.
    destruct (zev rho a) as [x|] eqn:Ha; [|discriminate H]. destruct (zev rho b) as [y|] eqn:Hb; [|discriminate H]. injection H as <-.
    rewrite <- (IHa x eq_refl), <- (IHb y eq_refl). unfold mul_div. rewrite bv_mul_unsigned. apply wrap64.
  - discriminate H.
  - destruct (zev rho a) as [x|] eqn:Ha; [|discriminate H]. injection H as <-. rewrite <- (IHa x eq_refl). unfold ext_val. apply lit64_u.
  - discriminate H.
Qed.

(* [comment removed for export] *)
Definition rho_of (l : list (nat * Z)) : nat -> option Z := fun n => match find (fun p => Nat.eqb (fst p) n) l with Some p => Some (snd p) | None => None end.
Lemma rho_of_sound : forall E l, Forall (fun p => bv_unsigned (ev E (fst p)) = snd p) l -> forall n v, rho_of l n = Some v -> bv_unsigned (ev E n) = v.
Proof.
  intros E l HF n v H. unfold rho_of in H. destruct (find _ l) as [p|] eqn:Hf; [|discriminate H]. injection H as <-.
  apply find_some in Hf as [Hin Heq]. apply Nat.eqb_eq in Heq. subst n. exact (proj1 (Forall_forall _ _) HF p Hin).
Qed.
(* [comment removed for export] *)
Lemma range_fact : forall E rho e z lo hi, (forall n v, rho n = Some v -> bv_unsigned (ev E n) = v) -> zev rho e = Some z ->
  lo <= bv_unsigned (edenot E e) <= hi -> lo <= z <= hi.
Proof. intros E rho e z lo hi Hr Hz H. rewrite (zev_sound E rho Hr e z Hz) in H. exact H. Qed.
End UVZ.
