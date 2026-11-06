From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog Require Import qdisc_spec qdisc_div.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Prog Require Import reac_qdisc_etf_catchup_slots_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_qdisc_etf_catchup_slots of the ubsan image (0x12ca0, 24 instructions): the plain code with other
    pc-relative fields (the `auipc; ld` still reads 0x103a8), so the walk is the plain one (Prog/
    reac_qdisc_etf_catchup_slots.v). Paths: fps <= 0 (blez taken, 1); p = usable * fps below 10^6 (1); p above
    10^12 + 999999 (10^6); else p / 10^6 by `mulhu` with the constant at 0x103a8, which mem_inv makes the walk
    read from the image. *)

(* Rewrite slots_spec with the path's value [E], drop the 32-bit sign wraps of `sext.w` (each argument is in
   int range), then close with the walk's [finish]. *)
Ltac fin E :=
  rewrite E;
  repeat match goal with
  | |- context [bv_swrap 32 ?e] =>
      rewrite (bv_swrap_small 32 e) by (change (bv_half_modulus 32) with 2147483648; lia)
  end;
  rewrite ?Z.add_0_r;
  finish.

Theorem qdisc_slots_holds : qdisc_slots_contract.
Proof.
  unfold qdisc_slots_contract, QDISC_SLOTS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lead fps HL HA0 HF HA1 HMI.
  subst a1.
  replace a0 with (Z_to_bv 64 lead) by (rewrite <- HA0; apply Z_to_bv_bv_unsigned).
  clear HA0.
  destruct (Z.leb_spec0 fps 0) as [Hneg|Hpos].
  - (* fps <= 0: blez is taken; sext.w a0, a2 returns the 1 in a2 *)
    zstep. zstep.
    if_cases K1.
    + zstep. zstep. fin (qdisc_spec_nonpos lead fps Hneg).
    + exfalso. zify_cond K1. Z.div_mod_to_equations. lia.
  - zstep. zstep.
    if_cases K1.
    + exfalso. zify_cond K1. apply andb_false_iff in K1. destruct K1 as [K|K]; apply Z.ltb_ge in K; lia.
    + zify_cond K1.
      (* addiw; sltu; addi; and: a0 = usable *)
      zstep. zstep. zstep. zstep.
      rewrite (qdisc_usable_bv lead HL).
      remember (Z.max 0 (lead - 300)) as u eqn:Hu.
      assert (Bu : 0 <= u <= 65235) by lia.
      (* lui; slli 32; srli 32 *)
      zstep. zstep. zstep.
      rewrite (Z.mod_small u 4294967296) by lia.
      (* mul: a1 = p *)
      zstep.
      remember (u * fps) as p eqn:Hp.
      assert (Hpu : p = Z.max 0 (lead - 300) * fps) by (rewrite Hp, Hu; reflexivity).
      assert (Bp : 0 <= p < 2^47) by (rewrite Hpu; apply qdisc_product_range; lia).
      (* addiw a0 = 10^6; bltu a1, a0 *)
      zstep. zstep.
      if_cases Ck2.
      * (* p < 10^6: sext.w a0, a2 returns 1 *)
        zify_cond Ck2.
        zstep. zstep. fin (qdisc_spec_small lead fps p ltac:(lia) Hpu Ck2).
      * zify_cond Ck2.
        (* lui; addiw; slli; addi: a2 = 10^12 + 999999; bltu a2, a1 *)
        zstep. zstep. zstep. zstep. zstep.
        if_cases Ck3.
        -- (* 10^12 + 999999 < p: mv a2, a0; sext.w returns 10^6 *)
           zify_cond Ck3.
           zstep. zstep. zstep. fin (qdisc_spec_cap lead fps p ltac:(lia) Hpu Ck3).
        -- (* auipc; ld (the constant at 0x103a8); mulhu; srli 18: a0 = p / 10^6 *)
           zify_cond Ck3.
           zstep. zstep. zstep. zstep.
           rewrite (qdisc_magic_shift p) by lia.
           pose proof (qdisc_n_range p ltac:(lia)) as Bn.
           (* mv; sext.w; ret *)
           zstep. zstep. zstep. fin (qdisc_spec_mid lead fps p ltac:(lia) Hpu ltac:(lia)).
Qed.
