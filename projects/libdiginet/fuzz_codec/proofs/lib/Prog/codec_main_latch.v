From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells codec_main_inv LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** addiw s6, s6, 1 on ops <= 254. *)
Lemma ops_succ : forall x, 0 <= x <= 254 -> bv_unsigned (Z_to_bv 64 (bv_swrap 32 (x + 1))) = x + 1.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity. replace (bv_modulus 32) with (2^32) by reflexivity.
  rewrite (Z.mod_small (x + 1 + 2^31) (2^32)) by lia.
  replace (x + 1 + 2 ^ 31 - 2 ^ 31) with (x + 1) by lia. apply unsigned_lit. lia.
Qed.

(** The body frame as HEAD takes it: k forgotten, in.n and the tail one block. *)
Lemma body_to_head : forall e m1 k c rem tl,
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400)
    (head_cells e c (cells_bytes (kcall_cells k)) (le8 (Z_to_bv 64 rem) ++ tl)).
Proof.
  intros e m1 k c rem tl H. unfold body_cells in H.
  apply (rw_cells_merge rsegs m1 _ [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0)]) in H.
  rewrite kcall_cells_size in H.
  pose proof (rw_cells_merge rsegs m1 (bv_unsigned (e_sp e) + -400)
                [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0); CB 184 (cells_bytes (kcall_cells k));
                 C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c))]
                [C8 (Z_to_bv 64 rem); CB 80 tl] []) as M.
  rewrite app_nil_r in M. cbn [app] in M, H. specialize (M H).
  cbn [cells_size csize cells_bytes cbytes Nat.add] in M. rewrite app_nil_r in M. exact M.
Qed.

(** 0x1482c ld s5, 0xd0(sp); 0x14830 addiw s6, s6, 1; 0x14834 beqz s5 -> EXIT; 0x14838 j HEAD. *)
Lemma codec_main_latch2 : forall e fuel, env_ok e -> head_ok e fuel -> exit_ok e -> latch2_ok e fuel.
Proof.
  intros e fuel HE HEAD EX. unfold latch2_ok, st, body_regs.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops k c rem tl m1
         [HF HO] H254 HC FR HFR.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp. unfold bv_modulus in Rp.
  pose proof (bv_unsigned_in_range 64 ops) as Rops. unfold bv_modulus in Rops.
  pose proof HE as (_ & _ & _ & HLO & _ & _ & HPB & _). unfold LLVM_CODEC_STACK in HLO.
  pose proof HFR as (SV & ST & MU & WM & HMI).
  pose proof ST as [Hlo0 _].
  destruct HC as (Hc0 & Hr0 & Hcr).
  unfold body_cells in FR. cbn [kcall_cells app] in FR.
  zstep. zstep. zstep.
  assert (FB : rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl)) by exact FR.
  clear FR.
  if_cases EZ.
  - zify_cond EZ.
    eapply EX; [ | exact FB | exact HFR ]. apply body_cells_size.
  - zify_cond EZ.
    pose proof (body_to_head e m1 k c rem tl FB) as FH. unfold head_cells in FH. clear FB.
    zstep.
    unfold head_ok, st, body_regs in HEAD.
    eapply HEAD; [ | | | exact FH | exact HFR ].
    + split; [ rewrite ops_succ by lia; lia | rewrite ops_succ by lia; lia ].
    + lia.
    + unfold cur_ok. lia.
Qed.

(** 0x14828 bltu s3, s6 -> EXIT (the finished iteration was the 256th), else LATCH2. *)
Lemma codec_main_latch : S_latch.
Proof.
  unfold S_latch. intros e fuel HE HEAD EX.
  pose proof (codec_main_latch2 e fuel HE HEAD EX) as L2.
  split; [ | exact L2 ].
  unfold latch_ok, st, body_regs.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops k c rem tl m1
         [HF HO] HC FR HFR.
  pose proof (bv_unsigned_in_range 64 ops) as Rops. unfold bv_modulus in Rops.
  zstep.
  if_cases EB.
  - zify_cond EB.
    eapply EX; [ | exact FR | exact HFR ]. apply body_cells_size.
  - zify_cond EB.
    unfold latch2_ok, st, body_regs in L2.
    eapply L2; [ split; [exact HF | exact HO] | lia | exact HC | exact FR | exact HFR ].
Qed.
