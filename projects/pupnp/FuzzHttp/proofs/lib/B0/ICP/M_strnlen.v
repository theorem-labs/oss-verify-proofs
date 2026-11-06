(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit I_memchr.
Import ListNotations.
Open Scope Z_scope.

Definition A0_musl_strnlen : Z := 0xa342c.

Definition snl_sz (P n : Z) (buf : list byte) : Z := let r := memchr_res P 0 n buf in if r =? 0 then n else r - P + 1.

Definition strnlen_a_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P n : Z) (buf : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz (strnlen_res n buf)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' P buf.

Lemma strnlen_a_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (P n : Z) (buf : list byte) (lo : Z),
  bytes_at asegs m P buf -> memchr_ok P 0 n buf ->
  accessible m P (snl_sz P n buf) -> sh_readable m P (snl_sz P n buf) ->
  icpt_env m -> cwin P (snl_sz P n buf) -> P + snl_sz P n buf < 2^47 -> snl_sz P n buf <= 2^43 ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 32 - 2208 -> q < 2^64 ->
  (P + Z.of_nat (length buf) <= lo \/ q <= P) -> 0 < P -> 0 <= n < 2^64 ->
  mem_inv asegs m -> a0 = wz P -> a1 = wz n ->
  evt asegs (strnlen_a_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P n buf lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_musl_strnlen) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros BUF OK ACC RDB IE WIN WIN2 NSZ ST KLO LO Q64 SEP HP HN MI -> ->. unfold A0_musl_strnlen.
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ BUF) as AB.
  assert (LO' : lo <= q - 32) by lia.
  carve_frame 32%nat ST.
  do 9 zstep.
  assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (ACC1 : accessible mm P (snl_sz P n buf)) by (eapply accessible_munch; [exact ACC| exact MU| exact WIN| intros s Hs; apply HO; lia]);
    assert (RDB1 : sh_readable mm P (snl_sz P n buf)) by (eapply sh_readable_munch; [exact RDB| exact MU| exact WIN| exact HO]);
    pose proof (icpt_env_stack lo q m mm IE MU WM ltac:(lia)) as IE1;
    eapply evt_cut;
    [ eapply memchr_i_spec with (lo := lo) (A := P) (c := 0) (n := n) (buf := buf);
      [ eassumption | exact OK | exact ACC1 | exact RDB1 | exact IE1 | exact WIN | exact WIN2 | exact NSZ | eassumption | lia | lia | lia
      | lia | assumption | reflexivity | reflexivity | reflexivity | lia | lia ]
    | post_call asegs mm ] end.
  unfold memchr_res.
  destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:FB.
  - pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite firstn_length in Hl.
    zstep. if_cases K; zify_cond K. { exfalso. lia. }
    do 7 zstep.
    replace (P + Z.of_nat i - P) with (strnlen_res n buf) by (unfold strnlen_res; rewrite FB; lia).
    match goal with PC : stk asegs _ lo (q + -32) |- _ => release_frame FR PC q end. finish.
  - zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
    do 6 zstep.
    replace (Z_to_bv 64 n) with (Z_to_bv 64 (strnlen_res n buf)) by (unfold strnlen_res; rewrite FB; reflexivity).
    match goal with PC : stk asegs _ lo (q + -32) |- _ => release_frame FR PC q end. finish.
Qed.

Lemma snl_sz_min : forall P n buf, 0 < P -> 0 <= n -> snl_sz P n buf = Z.min (strnlen_res n buf + 1) n.
Proof.
  intros P n buf HP Hn. unfold snl_sz, memchr_res, strnlen_res.
  destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:FB.
  - pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite firstn_length in Hl.
    destruct (Z.eqb_spec (P + Z.of_nat i) 0); lia.
  - cbn. lia.
Qed.
