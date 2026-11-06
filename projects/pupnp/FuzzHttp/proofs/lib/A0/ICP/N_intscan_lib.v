(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr Image.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim StrFun ScanInt.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import M_memcpy M_memchr M_printf_lib M_errno_location.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import N_rfile.
Import ListNotations.
Open Scope Z_scope.

Definition INTSCAN : Z := 0xa1038.
Definition IS_DEPTH : Z := 2480.
Definition IS_TABLE : Z := 0x23728.
Notation ERRNO tp := (bv_unsigned tp - 164)%Z (only parsing).

Definition ISTAB : list Z := map (fun i => digval (Z.of_nat i - 1)) (seq 0 257).
Lemma ISTAB_length : length ISTAB = 257%nat.
Proof. reflexivity. Qed.
Lemma znth_ISTAB : forall c, -1 <= c <= 255 -> znth ISTAB (c + 1) = digval c.
Proof.
  intros c Hc. unfold ISTAB, znth. destruct (Z.ltb_spec0 (c + 1) 0); [lia|].
  apply nth_error_nth. rewrite nth_error_map, nth_error_seq.
  destruct (PeanoNat.Nat.ltb_spec0 (Z.to_nat (c + 1)) 257); [|lia]. cbn [option_map Nat.add]. f_equal. f_equal. lia.
Qed.

Open Scope bv_scope.
Lemma istab_bytes : forall m, mem_inv asegs m -> bytes_at asegs m IS_TABLE (zbytes ISTAB).
Proof.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold IS_TABLE. lia. } { rewrite zbytes_length, ISTAB_length. unfold IS_TABLE. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma istab_read : forall m c a, mem_inv asegs m -> (-1 <= c <= 255)%Z -> a = wa (0x23728 + c + 1) ->
  ov_read_bytes asegs m a 1 = Some [Z_to_bv 8 (digval c)].
Proof.
  intros m c a MI Hc ->. rewrite <- (znth_ISTAB c Hc). replace (0x23728 + c + 1)%Z with (IS_TABLE + (c + 1))%Z by (unfold IS_TABLE; lia).
  eapply (u8ro_read asegs m IS_TABLE (zbytes ISTAB) (c + 1)); [apply istab_bytes; exact MI | | lia | reflexivity].
  apply zbytes_nth. unfold zlength. rewrite ISTAB_length. lia.
Qed.
Lemma digval_byte : forall c, (0 <= digval c < 256)%Z.
Proof. intros c. destruct (digval_range c); lia. Qed.

Definition is_frame (ra s0e s1e s2e s3e s4e s5e s6e s7e s8e : word) : list cell :=
  [C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

Definition is_W (q Fp : Z) (tp : word) : list (Z * Z) := [(q - IS_DEPTH, q); (Fp, Fp + 232); (ERRNO tp, ERRNO tp + 4)]%Z.

Definition is_finv (ra : word) (q : Z) (tp s0e s1e s2e s3e s4e s5e s6e s7e s8e : word) (m0 : word -> option byte)
    (Fp T : Z) (txt : list Z) (canary : word) (m : word -> option byte) : Prop :=
  mem_inv asegs m /\ munch (is_W q Fp tp) m0 m /\ wmono asegs m0 m
  /\ rw_cells asegs m (q + -80) (is_frame ra s0e s1e s2e s3e s4e s5e s6e s7e s8e)
  /\ stk asegs m (q - IS_DEPTH) (q + -80)
  /\ bytes_at asegs m T (zbytes txt) /\ ssp_cells m canary
  /\ (exists ev : word, rw_cells asegs m (ERRNO tp) [C4 ev]).

Definition intscan_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Fp T p : Z) (J : rfj) (txt : list Z) (canary : word) (fR : shfile) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' co' k' c' (ev : word),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (is_W q Fp tp) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
    /\ stk asegs m' (q - IS_DEPTH) q
    /\ rw_cells asegs m' Fp (rf_cells T co' fR J) /\ RFJ T txt p J co' k' c' fR
    /\ bytes_at asegs m' T (zbytes txt) /\ ssp_cells m' canary
    /\ rw_cells asegs m' (ERRNO tp) [C4 ev].

Lemma stdio_getc : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. intros f. unfold sh_getc. destruct (sh_stdio f); cbn [negb]; [destruct (_ =? _)%Z; reflexivity | reflexivity]. Qed.
Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
Lemma stdio_lim0 : forall f, sh_stdio (sh_lim0 f) = sh_stdio f.
Proof. reflexivity. Qed.

Lemma errno_callq : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  (164 <= bv_unsigned tp)%Z -> mem_inv asegs m ->
  evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (ERRNO tp)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x94778) fc None m (seg_rom asegs)).
Proof. intros. eapply errno_location_spec; assumption. Qed.

Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac mlia2 := rewrite ?land_W64 in *; Z.div_mod_to_equations; lia.
Lemma swrap32_landW : forall a c, bv_swrap 32 (Z.land a 18446744073709551615 + c) = bv_swrap 32 (a + c).
Proof.
  intros a c. rewrite land_W64, !swrap32_eq. f_equal.
  rewrite (Z.mod_eq a (2^64)) by lia.
  replace (a - 2 ^ 64 * (a / 2 ^ 64) + c + 2147483648)%Z with ((a + c + 2147483648) + (- (a / 2 ^ 64) * 4294967296) * 4294967296)%Z by lia.
  apply Z.mod_add. lia.
Qed.
Lemma swrap32_landW_sub : forall a c, bv_swrap 32 (Z.land a 18446744073709551615 - c) = bv_swrap 32 (a - c).
Proof. intros a c. rewrite <- !Z.add_opp_r. apply swrap32_landW. Qed.
Ltac fixw2 := rewrite ?swrap32_landW, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
