From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import diginet_counter_encode_c diginet_counter_encode_lib.
Import ListNotations.
Open Scope Z_scope.

(* every byte store is a C1 cell of the low byte of the register *)
Local Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Local Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* a branch whose other side contradicts the context *)
Local Ltac br := let K := fresh "K" in if_cases K; first [ exfalso; zify_cond K; lia | clear K ].

(* the byte cells of the frame in their plain form *)
Local Ltac fr_clean FR := rewrite ?cnt_b8_u64, ?cnt_b8_ub in FR.

(* one iteration of the reverse copy of seg into the frame: lbu, sb, two addi, bne *)
Local Ltac cpy HS FR k e :=
  let HR := fresh "HR" in
  pose proof (cnt_byte_read _ _ _ k e HS ltac:(cbn; lia) ltac:(lia)) as HR; cbn [nth] in HR;
  zstep; clear HR; zstep; fr_clean FR; zstep; zstep; zstep.

(* run to pc stop *)
Local Ltac run_to stop :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif constr_eq pc stop then fail else zstep
  end.

(* a failing return: the epilogue at 0x15d98, out untouched *)
Local Ltac fexit FR ST hi :=
  run_to 0x15da8; release_frame FR ST hi; zstep; finish; reflexivity.

(* a payload byte with bit 7 set: counter_spec says E_RANGE *)
Local Ltac chk_bad K :=
  zify_cond K; apply cnt_sxb_neg in K; try (rewrite cnt_u8 in K by lia);
  lazymatch goal with
  | |- context [cnt_bad ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j] =>
      replace (cnt_bad a b c d e f g h i j) with true
        by (symmetry; unfold cnt_bad; rewrite (cnt_leb_true _ K); rewrite ?orb_true_r, ?orb_true_l; reflexivity)
  end.
Local Ltac chk_ok K := zify_cond K; apply cnt_sxb_pos in K; try (rewrite cnt_u8 in K by lia).

Theorem diginet_counter_encode_holds : memcpy_contract -> diginet_counter_encode_contract.
Proof.
  intros MC.
  unfold diginet_counter_encode_contract, diginet_counter_encode_pre, DIGINET_COUNTER_ENCODE,
    DIGINET_COUNTER_ENCODE_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo pd dots sg before
         (HP & HD1 & HD2 & Ha1 & HS & HL & [Hdots ->] & Ha3 & HO & Hsp1 & Hsp3 & HMI & ST & LO).
  change (2 ^ 8) with 256 in Hdots.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a3) as Ra3.
  change (bv_modulus 64) with 18446744073709551616 in Rsp, Ra0, Ra1, Ra3.
  pose proof (rw_cells_bound rsegs m _ _ HO) as BO. cbn [cells_size csize] in BO.
  change (2 ^ 64) with 18446744073709551616 in BO.
  assert (Hlo : 0 <= lo) by (destruct ST as [Hlo _]; exact Hlo).
  carve_frame 48%nat ST.
  destruct pd as [d|].
  2: {
    cbn [pers_arg] in HP. subst a0.
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_false.
    zstep. if_true.
    run_to 0x15da8.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    replace (counter_spec None (zb sg) dots) with (E_ARG, @None cmd) by reflexivity.
    finish. reflexivity. }
  cbn [pers_arg] in HP. destruct HP as [Hp0 [Hdk HPB]].
  cbn [bz map] in HPB. unfold b8 in HPB.
  specialize (HD1 d eq_refl). specialize (HD2 d eq_refl). unfold disj in HD1, HD2.
  pose proof Hdk as (Hd0 & Hd1 & Hd2 & Hd3).
  destruct sg as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 rest]]]]]]]]; try (cbn in HL; lia).
  rewrite (cnt_spec_some d dots g0 g1 g2 g3 g4 g5 g6 g7 rest Hdk Hdots).
  assert (HS8 : bytes_at rsegs m (bv_unsigned a1) [g0; g1; g2; g3; g4; g5; g6; g7])
    by exact (proj1 (proj1 (bytes_at_app rsegs m (bv_unsigned a1) [g0; g1; g2; g3; g4; g5; g6; g7] rest) HS)).
  clear HS HL.
  (* prologue and the NULL tests *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. if_false.
  zstep. if_false.
  zstep.
  zstep. if_false.
  (* pl[0] = p->counter_addr, pl[1] = dots *)
  pose proof (cnt_byte_read _ _ _ 3 (bv_unsigned a0 + 19) HPB ltac:(cbn; lia) ltac:(lia)) as HR.
  cbn [nth] in HR.
  zstep. clear HR.
  zstep. zstep.
  zstep. fr_clean FR.
  zstep. fr_clean FR.
  zstep.
  (* pl[2..9] = seg[7..0] *)
  cpy HS8 FR 7%nat (bv_unsigned a1 + 7). br.
  cpy HS8 FR 6%nat (bv_unsigned a1 + 6). br.
  cpy HS8 FR 5%nat (bv_unsigned a1 + 5). br.
  cpy HS8 FR 4%nat (bv_unsigned a1 + 4). br.
  cpy HS8 FR 3%nat (bv_unsigned a1 + 3). br.
  cpy HS8 FR 2%nat (bv_unsigned a1 + 2). br.
  cpy HS8 FR 1%nat (bv_unsigned a1 + 1). br.
  pose proof (cnt_byte_read _ _ _ 0 (bv_unsigned a1) HS8 ltac:(cbn; lia) ltac:(lia)) as HR.
  cbn [nth] in HR. unfold wa in HR. rewrite Z_to_bv_bv_unsigned in HR.
  zstep. clear HR. zstep. fr_clean FR. zstep. zstep. zstep. br.
  clear HS8.
  (* the device byte (inlined sysex_encode: device bit 7) *)
  pose proof (cnt_byte_read _ _ _ 0 (bv_unsigned a0 + 16) HPB ltac:(cbn; lia) ltac:(lia)) as HR.
  cbn [nth] in HR.
  zstep. clear HR.
  zstep. if_cases KD.
  { zify_cond KD. apply cnt_sxb_neg in KD. rewrite cnt_u8 in KD by lia.
    replace (127 <? d_dev d) with true by (symmetry; apply Z.ltb_lt; lia).
    fexit FR ST (bv_unsigned sp). }
  zify_cond KD. apply cnt_sxb_pos in KD. rewrite cnt_u8 in KD by lia.
  replace (127 <? d_dev d) with false by (symmetry; apply Z.ltb_ge; lia).
  zstep. zstep.
  (* the payload check over pl[0..9] *)
  zstep. zstep. if_cases K0. { chk_bad K0. fexit FR ST (bv_unsigned sp). }
  chk_ok K0. zstep. zstep. zstep. if_true.
  zstep. zstep. if_cases K1. { chk_bad K1. fexit FR ST (bv_unsigned sp). }
  chk_ok K1. zstep. zstep. zstep. if_true.
  zstep. zstep. if_cases K2. { chk_bad K2. fexit FR ST (bv_unsigned sp). }
  chk_ok K2. zstep. zstep. zstep. if_true.
  zstep. zstep. if_cases K3. { chk_bad K3. fexit FR ST (bv_unsigned sp). }
  chk_ok K3. zstep. zstep. zstep. if_true.
  zstep. zstep. if_cases K4. { chk_bad K4. fexit FR ST (bv_unsigned sp). }
  chk_ok K4. zstep. zstep. zstep. if_true.
  zstep. zstep. if_cases K5. { chk_bad K5. fexit FR ST (bv_unsigned sp). }
  chk_ok K5. zstep. zstep. zstep. if_true.
  zstep. zstep. if_cases K6. { chk_bad K6. fexit FR ST (bv_unsigned sp). }
  chk_ok K6. zstep. zstep. zstep. if_true.
  zstep. zstep. if_cases K7. { chk_bad K7. fexit FR ST (bv_unsigned sp). }
  chk_ok K7. zstep. zstep. zstep. if_true.
  zstep. zstep. if_cases K8. { chk_bad K8. fexit FR ST (bv_unsigned sp). }
  chk_ok K8. zstep. zstep. zstep. if_true.
  zstep. zstep. if_cases K9. { chk_bad K9. fexit FR ST (bv_unsigned sp). }
  chk_ok K9. zstep. zstep. zstep. if_false.
  replace (cnt_bad d dots g0 g1 g2 g3 g4 g5 g6 g7) with false
    by (symmetry; unfold cnt_bad; rewrite !cnt_leb_false by lia; reflexivity).
  (* out: bytes 0..3, then memcpy of pl to bytes 4..13 *)
  pose proof HO as [[[HLB _] _] _].
  destruct (cnt_out_split _ _ _ HO) as (O1 & O2 & O3). clear HO.
  zstep. zstep. zstep.
  zstep.
  zstep. rewrite ?cnt_b8_sxb in O1.
  zstep. rewrite ?cnt_b8_u64 in O1.
  zstep. zstep. zstep.
  zstep.
  pose proof (cnt_fr_src _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as SRC.
  replace (bv_unsigned sp + -48 + 14) with (bv_unsigned sp + -34) in SRC by lia.
  assert (U4 : bv_unsigned (Z_to_bv 64 (bv_unsigned a3 + 4)) = bv_unsigned a3 + 4) by (apply unsigned_lit; lia).
  assert (U34 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -34)) = bv_unsigned sp + -34) by (apply unsigned_lit; lia).
  assert (U10 : bv_unsigned (Z_to_bv 64 10) = 10) by reflexivity.
  call MC.
  { rewrite U34. exact SRC. }
  { reflexivity. }
  { rewrite U4, U10. exact O2. }
  { rewrite ?U34, ?U4, ?U10. lia. }
  { exact HMI. }
  rewrite U4, U10 in PC. change (Z.to_nat 10) with 10%nat in PC.
  (* out: 0xf7 at 14, len and display at 24, the key at 28 *)
  zstep. zstep. zstep.
  zstep. rewrite ?cnt_b8_u64 in O3.
  zstep.
  pose proof (cnt_byte_read _ _ _ 3 (bv_unsigned a0 + 19) HPB ltac:(cbn; lia) ltac:(lia)) as HR.
  cbn [nth] in HR.
  zstep. clear HR.
  zstep. zstep.
  zstep.
  rewrite (cnt_key (d_counter d) Hd3) in O3.
  run_to 0x15da8.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  pose proof (cnt_out_join _ _ _ _ _ O1 PC O3 eq_refl eq_refl) as OUT.
  finish.
  all: first [ reflexivity | exact (cnt_out_final _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLB OUT) ].
Qed.
