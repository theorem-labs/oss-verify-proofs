From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog Require Import qdisc_spec qdisc_div.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Prog Require Import check_slots_c.
Import ListNotations.
Open Scope Z_scope.

(** check_slots of the ubsan image (0x12c2c, 28 instructions and a trailing unimp after the abort call): the
    plain code with other pc-relative fields (the `auipc; ld` still reads 0x103a8), so the walk is the plain
    one (Prog/check_slots.v). It computes slots_of in a2 on the four paths of reac_qdisc_etf_catchup_slots,
    then `bne a0, a2` to the abort call: a0 is slots_spec, so that branch is never taken. *)

(* After `sext.w a2, a2`: rewrite slots_spec with the path's value [E], drop the 32-bit sign wraps (each
   argument is in int range), step `bne a0, a2`, refute the abort branch (a0 = a2) and return. *)
Ltac fin_check E :=
  rewrite E;
  repeat match goal with
  | |- context [bv_swrap 32 ?e] =>
      rewrite (bv_swrap_small 32 e) by (change (bv_half_modulus 32) with 2147483648; lia)
  end;
  rewrite ?Z.add_0_r;
  zstep;
  let Kb := fresh "Kb" in
  if_cases Kb;
  first [ exfalso; zify_cond Kb; lia | zstep; finish ].

Theorem qdisc_check_holds : qdisc_check_contract.
Proof.
  unfold qdisc_check_contract, QDISC_CHECK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lead fps HL HA1 HF HA2 HA0 HMI.
  subst a0 a2.
  replace a1 with (Z_to_bv 64 lead) by (rewrite <- HA1; apply Z_to_bv_bv_unsigned).
  clear HA1.
  destruct (Z.leb_spec0 fps 0) as [Hneg|Hpos].
  - (* fps <= 0: blez is taken; a2 = 1 *)
    zstep.
    if_cases K1.
    + zstep. zstep. fin_check (qdisc_spec_nonpos lead fps Hneg).
    + exfalso. zify_cond K1. Z.div_mod_to_equations. lia.
  - zstep.
    if_cases K1.
    + exfalso. zify_cond K1. apply andb_false_iff in K1. destruct K1 as [K|K]; apply Z.ltb_ge in K; lia.
    + zify_cond K1.
      (* addiw; sltu; addi; and: a1 = usable *)
      zstep. zstep. zstep. zstep.
      rewrite (qdisc_usable_bv lead HL).
      remember (Z.max 0 (lead - 300)) as u eqn:Hu.
      assert (Bu : 0 <= u <= 65235) by lia.
      (* lui; mul: a1 = p *)
      zstep. zstep.
      remember (u * fps) as p eqn:Hp.
      assert (Hpu : p = Z.max 0 (lead - 300) * fps) by (rewrite Hp, Hu; reflexivity).
      assert (Bp : 0 <= p < 2^47) by (rewrite Hpu; apply qdisc_product_range; lia).
      (* lui; addiw; slli; addi: a2 = 10^12 + 999999; addiw a3 = 10^6; bgeu a2, a1 *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      if_cases Ck2.
      * (* p <= 10^12 + 999999: auipc; ld (the constant at 0x103a8); mulhu; srli 18: a2 = p / 10^6 *)
        zify_cond Ck2.
        zstep. zstep. zstep. zstep.
        rewrite (qdisc_magic_shift p) by lia.
        pose proof (qdisc_n_range p ltac:(lia)) as Bn.
        (* bgeu a1, a3 *)
        zstep.
        if_cases Ck3.
        -- (* 10^6 <= p: sext.w a2 = p / 10^6 *)
           zify_cond Ck3.
           zstep. fin_check (qdisc_spec_mid lead fps p ltac:(lia) Hpu ltac:(lia)).
        -- (* p < 10^6: a2 = 1; sext.w *)
           zify_cond Ck3.
           zstep. zstep. fin_check (qdisc_spec_small lead fps p ltac:(lia) Hpu ltac:(lia)).
      * (* 10^12 + 999999 < p: mv a2, a3 (10^6); bltu a1, a3 (not taken); j; sext.w *)
        zify_cond Ck2.
        zstep. zstep.
        if_cases Ck3.
        -- exfalso. zify_cond Ck3. lia.
        -- zify_cond Ck3.
           zstep. zstep. fin_check (qdisc_spec_cap lead fps p ltac:(lia) Hpu ltac:(lia)).
Qed.
