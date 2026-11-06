(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit Stdio_base Printf_lib.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit IcptLeaves I_printf_back I_strnlen IcptPack.
Import ListNotations.
Open Scope Z_scope.

Section ICS.
Context {HC : HasCeiling}.

Definition strnlen_i_stmt_x : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P n lo : Z) (buf : list byte),
  stk asegs m lo q -> bytes_at asegs m P buf -> memchr_ok P 0 n buf -> mem_inv asegs m ->
  (alloc_ceiling <= lo)%Z -> (lo <= q - A0_RT_STACK2)%Z -> (0 <= q < 2^64)%Z ->
  (P + Z.of_nat (length buf) <= alloc_ceiling \/ q <= P)%Z -> (0 < P)%Z -> (0 <= n < 2^64)%Z ->
  asan_env asegs m -> shw m P (Z.min (strnlen_res n buf + 1) n) -> icpt_rng P (Z.min (strnlen_res n buf + 1) n) ->
  a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 n ->
  evt asegs (strnlen_i_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P n buf lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 A0_STRNLEN_I) fc None m (seg_rom asegs)).

#[using="Type"] Lemma strnlen_i_proof_x : strnlen_i_stmt_x.
Proof.
  intros until buf. intros ST BY OK MI CLO LO Q SEP P0 N AE (ACC & RDB & WIN) (_ & W2 & NS) -> ->.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE.
  eapply evt_mono.
  { eapply strnlen_i_spec with (P := P) (n := n) (lo := lo) (buf := buf); try eassumption; try reflexivity; lia. }
  intros ms' Q'. unfold istrnlen_post in Q'. unfold strnlen_i_post.
  destruct Q' as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & ST' & BY').
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [| exact BY']. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO].
Qed.

#[using="Type"] Lemma ics_all_x :
    memcpy_i_stmt /\ memset_i_stmt /\ strnlen_i_stmt_x /\ read_front_stmt /\ read_back_stmt /\ fwrite_front_stmt /\ fwrite_back_stmt
    /\ vprintf_front_stmt /\ vprintf_back_stmt /\ vfprintf_front_stmt /\ vfprintf_back_stmt
    /\ (forall fmt flen, fprintf_s_front_stmt fmt flen) /\ fprintf_u_front_stmt /\ fprintf_back_stmt /\ asan_dtor_stmt.
Proof.
  split; [exact ic_memcpy_i_proof|]. split; [exact ic_memset_i_proof|]. split; [exact strnlen_i_proof_x|].
  split; [exact ic_read_front_proof|]. split; [exact ic_read_back_proof|]. split; [exact ic_fwrite_front_proof|]. split; [exact ic_fwrite_back_proof|].
  split; [exact ic_vprintf_front_proof|]. split; [exact ic_vprintf_back_proof|]. split; [exact ic_vfprintf_front_proof|]. split; [exact ic_vfprintf_back_proof|].
  split; [exact ic_fprintf_s_front_proof|]. split; [exact ic_fprintf_u_front_proof|]. split; [exact ic_fprintf_back_proof|]. exact ic_asan_dtor_proof.
Qed.
End ICS.

Lemma ics_all : forall (HC : HasCeiling),
    memcpy_i_stmt /\ memset_i_stmt /\ strnlen_i_stmt /\ read_front_stmt /\ read_back_stmt /\ fwrite_front_stmt /\ fwrite_back_stmt
    /\ vprintf_front_stmt /\ vprintf_back_stmt /\ vfprintf_front_stmt /\ vfprintf_back_stmt
    /\ (forall fmt flen, fprintf_s_front_stmt fmt flen) /\ fprintf_u_front_stmt /\ fprintf_back_stmt /\ asan_dtor_stmt.
Proof. intros HC. exact (@ics_all_x HC). Qed.
Print Assumptions ics_all.
