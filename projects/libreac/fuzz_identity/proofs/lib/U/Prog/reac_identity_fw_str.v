From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_identity_fw_str_c reac_identity_fw_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import reac_identity_fw_str_c.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_identity_fw_str_c(FW, L).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_identity_fw_str(
  reac_identity_fw_str_c2_h, reac_identity_fw_str_c2_hd, reac_identity_fw_str_c2_f100,
  reac_identity_fw_str_c2_f10, reac_identity_fw_str_c2_h10, reac_identity_fw_str_c2_fd10,
  lor48, sub_div_mul, wtm_at, wtm_join, fw_short, fw_long).
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Lemma fw_fin : forall m o bs, 0 <= o -> o + Z.of_nat (length bs) <= 2^64 ->
  bytes_at rsegs (write_to_mem m (wa o) bs) o bs /\
  munch [(o, o + Z.of_nat (length bs))] m (write_to_mem m (wa o) bs) /\
  wmono rsegs m (write_to_mem m (wa o) bs).
Proof.
  intros m o bs H1 H2. split; [apply bytes_at_write_same; lia|]. split.
  - apply munch_write; [apply munch_refl | lia | lia | cbn; left; lia].
  - apply wmono_write, wmono_refl.
Qed.

Local Ltac rng := rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia.

Local Ltac ul :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by rng end.

Local Ltac norm :=
  repeat first
    [ progress ul
    | rewrite reac_identity_fw_str_c2_h by lia
    | rewrite reac_identity_fw_str_c2_hd by lia
    | rewrite reac_identity_fw_str_c2_f100 by rng
    | rewrite reac_identity_fw_str_c2_f10 by rng
    | rewrite reac_identity_fw_str_c2_h10 by rng
    | rewrite reac_identity_fw_str_c2_fd10 by rng
    | rewrite sub_div_mul by lia
    | match goal with |- context [bv_swrap 32 ?e] =>
        rewrite (bv_swrap_small 32 e) by (change (bv_half_modulus 32) with (2^31); rng) end
    | match goal with |- context [Z.lor ?x 48] => rewrite (lor48 x) by rng end ].

Local Ltac st := step; norm.

Local Ltac bcond :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); bcond
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); bcond
  | _ => first [ apply Z.eqb_eq; rng | apply Z.eqb_neq; rng | apply Z.ltb_lt; rng | apply Z.ltb_ge; rng ]
  end.

Local Ltac br b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [ cbv iota | symmetry; unfold_cond; ul; fold_lit_ux; bcond ]
  end.

Local Ltac chk := st; br false; st; br false.

Local Ltac refuse :=
  st; st;
  apply evt_done; cbv beta; do 16 eexists; split; [reflexivity|];
  split; [apply wmono_refl|];
  split; [ intros _; split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity] | reflexivity]
         | intros; exfalso; lia ].

Local Ltac hs o W j :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?M _) =>
    let H := fresh "HS" in
    assert (H : store_ok rsegs M (wa (o + j)) 1 = true)
      by (eapply wr_at_store_ok; [repeat apply wr_at_write; exact W | lia | lia])
  end.

Local Ltac merge o :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem (write_to_mem ?m (wa o) ?acc) ?A ?bs) _) =>
      rewrite (wtm_join acc bs m o A) by (unfold wa; f_equal; simpl_sizes; lia)
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?A ?bs) _) =>
      rewrite (wtm_at m A o bs) by (unfold wa; f_equal; lia)
  end.

Local Ltac sto o W j := hs o W j; st; merge o.

Local Ltac tail o W k :=
  st; chk;
  do 14 st; sto o W (k + 0); chk;
  do 3 st; sto o W (k + 1); chk;
  do 12 st; sto o W (k + 2); chk;
  do 14 st; sto o W (k + 3); chk;
  do 6 st; sto o W (k + 4); chk;
  sto o W (k + 5); st.

Local Ltac byte_eq := unfold dg; ul; first [reflexivity | f_equal; lia].

Local Ltac bytes_eq :=
  lazymatch goal with
  | |- [] = [] => reflexivity
  | |- _ :: _ = _ :: _ => apply (f_equal2 (@cons byte)); [byte_eq | bytes_eq]
  end.

Local Ltac finish v o EFW :=
  st;
  let FB := fresh "FB" in let FM := fresh "FM" in let FWM := fresh "FWM" in
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa o) ?bs) _) =>
      replace bs with (FW v ++ [Z_to_bv 8 0]) by (rewrite EFW; unfold le1; cbn [Z_to_le_bytes app]; bytes_eq);
      pose proof (fw_fin m o (FW v ++ [Z_to_bv 8 0]) ltac:(lia)
                    ltac:(rewrite length_app, EFW; cbn [length]; lia)) as (FB & FM & FWM)
  end;
  apply evt_done; cbv beta; do 16 eexists; split; [reflexivity|];
  split; [exact FWM|]; split; [intros [Hx|Hx]; exfalso; lia|];
  intros _ _; split; [unfold L; rewrite EFW; first [reflexivity | apply bv_eq; vm_compute; reflexivity]|];
  split; [exact FB|];
  replace (o + L v + 1) with (o + Z.of_nat (length (FW v ++ [Z_to_bv 8 0])))
    by (unfold L; rewrite length_app; cbn [length]; lia);
  exact FM.

Theorem reac_identity_fw_str_holds : reac_identity_fw_str_contract.
Proof.
  unfold reac_identity_fw_str_contract, REAC_IDENTITY_FW_STR.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v o c
    E0 E1 E2 Hv Ho Hc HW.
  subst a0 a1 a2.
  st. st.
  destruct (Z.eq_dec o 0) as [O0|O0].
  { br true. refuse. }
  br false. st. st.
  destruct (Z.ltb_spec c 8) as [C8|C8].
  { br true. refuse. }
  br false.
  specialize (HW O0 C8). pose proof HW as (Wo & Wn & _).
  st. st. st.
  destruct (Z.ltb_spec v 10000) as [V|V].
  - br true. st.
    pose proof (fw_short v ltac:(lia)) as EFW.
    tail o HW 0. finish v o EFW.
  - br false. do 4 st. sto o HW 0. st. st.
    pose proof (fw_long v ltac:(lia)) as EFW.
    tail o HW 1. finish v o EFW.
Qed.
