(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/mbedtls/fuzz_pkcs7/lib/Lib/Asn1Aux.v; 305 of its 322 lines of code are new or changed and 432 lines of the source are left out. *)
(* proves the wide UBSan contract of diginet_frame_build (fuzz_transport.ubsan, 0x18260) and that it gives the narrow one. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_frame_build_w.v at bb3053036017d1d92db6eca9e973ce610be16c08 to fuzz_transport's images *)
(* Walk of diginet_frame_build (src/diginet_frame.c:93-127 at 835f336c) in fuzz_transport.ubsan for
   U/Prog/diginet_frame_build_w_c.v. The wide contracts of diginet_body_check and diginet_sum16
   and the contracts of memcpy and memset are its hypotheses.
   - Mode 0 or 1: the walk of U/Prog/diginet_frame_build.v (its lemmas and tactics are used
     here), with the premise body <> 0 \/ body_len = 0 in place of body <> 0. That premise
     decides the test body_len && !body (0x182cc) and is the premise of the wide contracts of
     diginet_body_check and diginet_sum16; the narrow walk uses body <> 0 for nothing else
     (with body_len = 0, 0x184a4 skips the memcpy of the body).
   - Another mode: the tests of out, dst, src, hp and body_len && !body are not taken,
     0x182d8 (bltu 1, a7) goes to 0x184e4 with s8 = -1, and the epilogue returns -1 with the
     bytes at out unchanged (err_fin_w). No trap branch is on this path. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import diginet_frame_build_c
  diginet_frame_build_w_c diginet_body_check_c diginet_body_check_w_c memcpy_c diginet_sum16_c
  diginet_sum16_w_c memset_c diginet_frame_build.
Import ListNotations.
Open Scope Z_scope.

(* The same store shapes as in U/Prog/diginet_frame_build.v. *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(** * The model for mode 0 or 1 *)

Lemma build_code_w_ok : forall bb cap mode, mode = 0 \/ mode = 1 ->
  build_code_w bb cap mode = build_code bb cap.
Proof. intros bb cap mode [-> | ->]; reflexivity. Qed.

Lemma build_out_w_ok : forall dmac smac send ack retry cmd ncmds bb mode oj, mode = 0 \/ mode = 1 ->
  build_out_w dmac smac send ack retry cmd ncmds bb mode oj = build_out dmac smac send ack retry cmd ncmds bb mode oj.
Proof.
  intros dmac smac send ack retry cmd ncmds bb mode oj Hm.
  unfold build_out_w, build_out. rewrite (build_code_w_ok bb (Z.of_nat (length oj)) mode Hm). reflexivity.
Qed.

Theorem diginet_frame_build_contract_of_w : diginet_frame_build_contract_w -> diginet_frame_build_contract.
Proof.
  unfold diginet_frame_build_contract_w, diginet_frame_build_contract.
  intros W ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out dst src hp body mode lo send ack retry cmd ncmds dmac smac bb oj
    HO Hdst Hsrc Hhp Hbody Hmode HA4 Hsend Hack Hretry Hcmd Hncmds Hhp64 Ldm BDM Lsm BSM BHP BB RWO
    Ddst Dsrc Dhp Dbody SP8 ST LO0 LO Dosp Ddsp Dssp Dhsp Dbsp MI.
  pose proof (W ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out dst src hp body mode lo send ack retry cmd ncmds dmac smac bb oj
    HO Hdst Hsrc Hhp (or_introl Hbody) ltac:(destruct Hmode; lia) HA4 Hsend Hack Hretry Hcmd Hncmds Hhp64
    Ldm BDM Lsm BSM BHP BB RWO Ddst Dsrc Dhp Dbody SP8 ST LO0 LO Dosp Ddsp Dssp Dhsp Dbsp MI) as H.
  rewrite (build_code_w_ok bb (Z.of_nat (length oj)) mode Hmode) in H.
  rewrite (build_out_w_ok dmac smac send ack retry cmd ncmds bb mode oj Hmode) in H.
  exact H.
Qed.

(** * Another mode *)

(* 0x182d8 bltu 1, a7: a7 is the int mode sign-extended, above 1 as unsigned. *)
Lemma mode_bad_ltu : forall mode, -2^31 <= mode < 2^31 -> mode <> 0 -> mode <> 1 ->
  1 < bv_unsigned (Z_to_bv 64 mode).
Proof. intros mode R N0 N1. rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia. Qed.

(* err_fin of U/Prog/diginet_frame_build.v for the wide result. *)
Ltac err_fin_w FR STa ST0 sp lo BC RWO MUS WMS D :=
  release_frame FR STa (bv_unsigned sp);
  let R := fresh "RWOx" in
  xport RWO R MUS WMS ltac:(unfold keep in D);
  let S0 := fresh "ST0x" in
  xport ST0 S0 MUS WMS idtac;
  let SF := fresh "STf" in
  pose proof (stk_merge rsegs _ lo (bv_unsigned sp - 240) (bv_unsigned sp) S0 STa ltac:(lia)) as SF;
  apply evt_done; do 15 eexists; split;
  [ f_equal; rewrite BC; fin_regs
  | split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact SF|];
    unfold build_out_w; rewrite BC; exact R ].

Theorem diginet_frame_build_holds_w :
  diginet_body_check_contract_w -> memcpy_contract -> diginet_sum16_contract_w -> memset_contract ->
  diginet_frame_build_contract_w.
Proof.
  intros DBC MCPY SUM MSET. unfold diginet_frame_build_contract_w, DIGINET_FRAME_BUILD.
  intros ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out dst src hp body mode lo send ack retry cmd ncmds dmac smac bb oj
    HO Hdst Hsrc Hhp Hbody Hmr HA4 Hsend Hack Hretry Hcmd Hncmds Hhp64 Ldm BDM Lsm BSM BHP BB RWO
    Ddst Dsrc Dhp Dbody SP8 ST LO0 LO Dosp Ddsp Dssp Dhsp Dbsp MI.
  destruct (orb (mode =? 0) (mode =? 1)) eqn:MV.
  2: {
    (* a mode other than 0 and 1: -1 at 0x182d8, before every trap branch *)
    apply orb_false_iff in MV. destruct MV as [M0 M1]. apply Z.eqb_neq in M0. apply Z.eqb_neq in M1.
    assert (BC : build_code_w bb (Z.of_nat (length oj)) mode = -1)
      by (unfold build_code_w; rewrite (proj2 (Z.eqb_neq _ _) M0), (proj2 (Z.eqb_neq _ _) M1); reflexivity).
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (Z.of_N 64) with 64 in Rsp.
    pose proof (bytes_at_bound _ _ _ _ BDM) as Rdst. rewrite Ldm in Rdst.
    pose proof (bytes_at_bound _ _ _ _ BSM) as Rsrc. rewrite Lsm in Rsrc.
    pose proof (bytes_at_bound _ _ _ _ BB) as Rbb.
    pose proof (rw_cells_bound _ _ _ _ RWO) as Roj. cbn [cells_size csize] in Roj. rewrite Nat.add_0_r in Roj.
    pose proof ST as (Rlo & Rhi & _).
    destruct (stk_split rsegs m lo (bv_unsigned sp - 240) (bv_unsigned sp) ST ltac:(lia)) as [ST0 STa].
    clear ST.
    pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (out, out + Z.of_nat (length oj))] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)] m) as MUS.
    pose proof (wmono_refl rsegs m) as WMS.
    hide Ddst. hide Dsrc. hide Dhp. hide Dbody. hide Dosp. hide Ddsp. hide Dssp. hide Dhsp. hide Dbsp.
    hide Hbody. hide BDM. hide BSM. hide BHP. hide BB. hide RWO. hide ST0.
    carve_frame 96%nat STa.
    do 13 step.
    (* 0x18294 .. 0x182ac: out, dst, src, hp are not 0 *)
    step. take false.
    step. step. take false.
    step. step. take false.
    step. step. take false.
    (* 0x182b0 .. 0x182cc: body_len && !body *)
    do 8 step.
    take_by false ltac:(apply and_test_false; unfold keep in Hbody; lia).
    (* 0x182d0 .. 0x182d8: mode > DIGINET_SUM_ZERO as unsigned *)
    do 3 step.
    take_by true ltac:(unfold_cond; usub; fold_lit_ux; apply Z.ltb_lt; apply mode_bad_ltu; assumption).
    (* 0x184e4: sext.w a0, s8 (-1) and the epilogue *)
    do 14 step.
    err_fin_w FR STa ST0 sp lo BC RWO MUS WMS Dosp. }
  (* mode 0 or 1: the narrow walk *)
  assert (Hmode : mode = 0 \/ mode = 1).
  { apply orb_true_iff in MV. destruct MV as [M|M]; apply Z.eqb_eq in M; [left | right]; exact M. }
  rewrite (build_code_w_ok bb (Z.of_nat (length oj)) mode Hmode).
  rewrite (build_out_w_ok dmac smac send ack retry cmd ncmds bb mode oj Hmode).
  clear MV Hmr.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (Z.of_N 64) with 64 in Rsp.
  pose proof (bytes_at_bound _ _ _ _ BDM) as Rdst. rewrite Ldm in Rdst.
  pose proof (bytes_at_bound _ _ _ _ BSM) as Rsrc. rewrite Lsm in Rsrc.
  pose proof (bytes_at_bound _ _ _ _ BB) as Rbb.
  (* the narrow walk has body <> 0 here, so body_len < 2^64; the wide premise gives it too *)
  assert (Rlen : Z.of_nat (length bb) < 2^64) by (destruct Hbody; lia).
  pose proof (rw_cells_bound _ _ _ _ RWO) as Roj. cbn [cells_size csize] in Roj. rewrite Nat.add_0_r in Roj.
  pose proof ST as (Rlo & Rhi & _).
  assert (Rmode : 0 <= mode <= 1) by (destruct Hmode; lia).
  pose proof (hdr_ro m hp send ack retry cmd ncmds Hsend Hack Hretry BHP) as HC. clear BHP.
  destruct (stk_split rsegs m lo (bv_unsigned sp - 240) (bv_unsigned sp) ST ltac:(lia)) as [ST0 STa].
  clear ST.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (out, out + Z.of_nat (length oj))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)] m) as MUS.
  pose proof (wmono_refl rsegs m) as WMS.
  hide Ddst. hide Dsrc. hide Dhp. hide Dbody. hide Dosp. hide Ddsp. hide Dssp. hide Dhsp. hide Dbsp. hide Hmode.
  hide Hbody.
  hide BDM. hide BSM. hide BB. hide RWO. hide HC. hide ST0.
  carve_frame 96%nat STa.
  do 13 step.
  (* 0x18294 .. 0x182ac: out, dst, src, hp are not 0 *)
  step. take false.
  step. step. take false.
  step. step. take false.
  step. step. take false.
  (* 0x182b0 .. 0x182cc: body_len && !body *)
  do 8 step.
  take_by false ltac:(apply and_test_false; unfold keep in Hbody; lia).
  (* 0x182d0 .. 0x182d8: mode > DIGINET_SUM_ZERO *)
  do 3 step. take false.
  (* 0x182dc: body_len > DIGINET_MAX_BODY_LEN *)
  do 2 step.
  destruct (Z_lt_le_dec 1484 (Z.of_nat (length bb))) as [BIG|SMALL].
  { take false. do 2 step. do 14 step.
    assert (BC : build_code bb (Z.of_nat (length oj)) = -4)
      by (unfold build_code; destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [reflexivity | lia]).
    err_fin FR STa ST0 sp lo BC RWO MUS WMS Dosp. }
  take true.
  (* 0x182ec: diginet_body_check (body, body_len) *)
  do 3 step.
  xport BB BB1 MUS WMS ltac:(unfold keep in Dbsp).
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  call DBC.
  { unfold keep in Hbody. exact Hbody. }
  { exact BB1. }
  { rewrite USP. lia. }
  { rewrite USP. exact STa. }
  { lia. }
  { rewrite USP. lia. }
  { rewrite USP. unfold keep in Dbsp. lia. }
  { assumption. }
  lazymatch goal with H : stk _ _ _ (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite USP in H; rename H into STa end.
  (* 0x182f8: the code of diginet_body_check *)
  rewrite body_check_spec. destruct (system_at bb) eqn:SA; cbv iota; step.
  { take false. do 2 step. do 14 step.
    assert (BC : build_code bb (Z.of_nat (length oj)) = -10)
      by (unfold build_code; rewrite SA; destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [lia | reflexivity]).
    err_fin FR STa ST0 sp lo BC RWO MUS WMS Dosp. }
  take true.
  (* 0x18304 .. 0x18314: the frame length *)
  destruct (ex_intro (fun z => z = frame_len (length bb)) _ eq_refl) as [fl EFL].
  assert (FLv : fl = Z.max 60 (30 + Z.of_nat (length bb))) by (rewrite EFL; reflexivity).
  do 3 step.
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?mc ?ro) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 24)) in
      let R' := eval cbv beta iota delta [tset] in (tset p (Z_to_bv 64 fl) R) in
      assert (K1 : evt segs Q (MS R' F (Z_to_bv 64 0x18318) fc rv mc ro))
  end.
  2: { step. destruct (Z_lt_le_dec (Z.of_nat (length bb)) 30) as [N30|N30].
       - take false. step. set_reg_tac 24 (Z_to_bv 64 fl); [f_equal; lia | exact K1].
       - take true. set_reg_tac 24 (Z_to_bv 64 fl); [f_equal; lia | exact K1]. }
  (* 0x18318: cap < frame length *)
  step.
  destruct (Z_lt_le_dec (Z.of_nat (length oj)) fl) as [CAPS|CAPOK].
  { take false. do 2 step. do 14 step.
    assert (BC : build_code bb (Z.of_nat (length oj)) = -5)
      by (unfold build_code; rewrite SA; rewrite <- EFL;
          destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [lia|];
          destruct (Z.ltb_spec (Z.of_nat (length oj)) fl); [reflexivity | lia]).
    err_fin FR STa ST0 sp lo BC RWO MUS WMS Dosp. }
  take true.
  assert (FLr : 60 <= fl <= 1514) by lia.
  assert (LEN : (30 + length bb + (30 - length bb) <= length oj)%nat) by lia.
  assert (FLN : Z.to_nat fl = (30 + length bb + (30 - length bb))%nat) by lia.
  assert (RN : 0 <= Z.of_nat (length bb) <= 1484) by lia.
  assert (STr : lo <= bv_unsigned sp - 240 <= bv_unsigned sp) by lia.
  (* 0x18324: the writes into the buffer. The facts the writes keep move from the entry memory
     here; the frame and the stack under it go under keep, and the fence MUO starts. *)
  xport RWO RWO1 MUS WMS ltac:(unfold keep in Dosp).
  xport BDM BDM1 MUS WMS ltac:(unfold keep in Ddsp).
  xport BSM BSM1 MUS WMS ltac:(unfold keep in Dssp).
  xport HC HC1 MUS WMS ltac:(unfold keep in Dhsp).
  xport BB BB2 MUS WMS ltac:(unfold keep in Dbsp).
  clear MUS WMS BDM BSM HC BB RWO Ddsp Dssp Dhsp Dbsp.
  hide BDM1. hide BSM1. hide HC1. hide BB2. hide STa. hide FR.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (munch_refl [(out, out + Z.of_nat (length oj))] mc) as MUO;
    pose proof (wmono_refl rsegs mc) as WMO end.
  destruct (out_split _ out (length bb) (30 - length bb) oj LEN RWO1)
    as ((j1 & P1) & (j2 & P2) & (j3 & P3) & (j4 & P4) & (j5 & P5) & P6).
  clear RWO1.
  assert (UO : bv_unsigned (Z_to_bv 64 out) = out) by (apply unsigned_lit; lia).
  assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  (* 0x18324: memcpy (out, dst, 6) *)
  do 4 step.
  xport BDM1 BDM2 MUO WMO ltac:(unfold keep in Ddst).
  assert (UD : bv_unsigned (Z_to_bv 64 dst) = dst) by (apply unsigned_lit; lia).
  call MCPY; [ rewrite UD; exact BDM2 | rewrite Ldm; reflexivity | rewrite UO; exact P1
             | rewrite UD, UO, U6; unfold keep in Ddst; lia | assumption | ].
  lazymatch goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ =>
    rewrite UO, U6 in H; change (Z.to_nat 6) with 6%nat in H; rename H into Q1 end.
  (* 0x18334: out + 6 wraps *)
  do 2 step. take false.
  (* 0x1833c: memcpy (out + 6, src, 6) *)
  do 4 step.
  xport BSM1 BSM2 MUO WMO ltac:(unfold keep in Dsrc).
  assert (UO6 : bv_unsigned (Z_to_bv 64 (out + 6)) = out + 6) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; lia).
  call MCPY; [ rewrite US; exact BSM2 | rewrite Lsm; reflexivity | rewrite UO6; exact P2
             | rewrite US, UO6, U6; unfold keep in Dsrc; lia | assumption | ].
  lazymatch goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ =>
    rewrite UO6, U6 in H; change (Z.to_nat 6) with 6%nat in H; rename H into Q2 end.
  clear BDM1 BSM1 Ddst Dsrc.
  (* 0x1834c .. 0x1839c: EtherType and numbytes, with the checks of out + 12 .. out + 16 *)
  do 2 step. take false.
  do 5 step. take false.
  do 4 step. take false.
  do 6 step. take false.
  do 3 step. take false.
  step.
  (* 0x183a0: the sum in the mode DIGINET_SUM_BODY, zero in DIGINET_SUM_ZERO; both reach
     0x183c0 with a0 the sum and a1 its high byte *)
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?mc ?ro) =>
      let k1 := eval vm_compute in (bv_key (Z_to_bv 5 1)) in
      let k10 := eval vm_compute in (bv_key (Z_to_bv 5 10)) in
      let k11 := eval vm_compute in (bv_key (Z_to_bv 5 11)) in
      let k12 := eval vm_compute in (bv_key (Z_to_bv 5 12)) in
      let k13 := eval vm_compute in (bv_key (Z_to_bv 5 13)) in
      let k14 := eval vm_compute in (bv_key (Z_to_bv 5 14)) in
      let k15 := eval vm_compute in (bv_key (Z_to_bv 5 15)) in
      let k16 := eval vm_compute in (bv_key (Z_to_bv 5 16)) in
      let Rf := eval cbv beta iota delta [tset] in
        (fun (vra v1 v2 v3 v4 v5 v6 : word) (sv : Z) =>
           tset k1 vra (tset k10 (Z_to_bv 64 sv) (tset k11 v1 (tset k12 v2 (tset k13 v3
             (tset k14 v4 (tset k15 v5 (tset k16 v6 R)))))))) in
      assert (K2 : forall (vra v1 v2 v3 v4 v5 v6 : word) (sv : Z),
                sv = (if mode =? 0 then lib_sum16 bb else 0) -> v1 = Z_to_bv 64 (Z.shiftr sv 8) ->
                evt segs Q (MS (Rf vra v1 v2 v3 v4 v5 v6 sv) F (Z_to_bv 64 0x183c0) fc rv mc ro))
  end.
  2: { step. pose proof Hmode as HM. unfold keep in HM. destruct HM as [M|M]; subst mode.
       - (* 0x183b0: diginet_sum16 (body, body_len) *)
         take true. do 3 step.
         xport BB2 BB3 MUO WMO ltac:(unfold keep in Dbody).
         eapply evt_cut; [eapply SUM; [unfold keep in Hbody; exact Hbody | exact BB3] |].
         intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & ->).
         replace (ret_pc (Z_to_bv 64 0x183bc)) with (Z_to_bv 64 0x183bc)
           by (symmetry; apply ret_pc_even; [lia | reflexivity]).
         step.
         eapply K2; [reflexivity |].
         rewrite (unsigned_lit (lib_sum16 bb)) by (rewrite lib_sum16_eq; pose proof (sum16_range bb); lia).
         reflexivity.
       - take false. do 3 step. eapply K2; reflexivity. }
  intros vra v1 v2 v3 v4 v5 v6 sv Esv Ev1. subst v1. cbv beta.
  assert (Rsv : 0 <= sv < 2^16)
    by (rewrite Esv; destruct (mode =? 0); [rewrite lib_sum16_eq; apply sum16_range | lia]).
  (* 0x183c0 .. 0x183d4: the sum, with the checks of out + 16 and out + 17 *)
  do 3 step. take false.
  do 3 step. take false.
  (* 0x183d8: the alignment of the header *)
  do 2 step.
  take_by false ltac:(unfold_cond; usub; rewrite land3_mod4 by lia; usub; fold_lit_ux; solve_cond_rec).
  (* 0x183e0 .. 0x18420: send_counter *)
  xport HC1 HC2 MUO WMO ltac:(unfold keep in Dhp).
  do 6 step. take false.
  do 4 step. take false.
  do 4 step. take false.
  do 3 step. take false.
  (* 0x18424 .. 0x18464: ack_counter *)
  xport HC1 HC3 MUO WMO ltac:(unfold keep in Dhp).
  do 6 step. take false.
  do 4 step. take false.
  do 4 step. take false.
  do 3 step. take false.
  (* 0x18468 .. 0x18488: retry *)
  xport HC1 HC4 MUO WMO ltac:(unfold keep in Dhp).
  do 6 step. take false.
  do 3 step. take false.
  (* 0x1848c .. 0x184a0: cmd and num_commands *)
  xport HC1 HC5 MUO WMO ltac:(unfold keep in Dhp).
  do 4 step. take false.
  xport HC1 HC6 MUO WMO ltac:(unfold keep in Dhp).
  do 2 step.
  clear HC1 Dhp.
  assert (BC : build_code bb (Z.of_nat (length oj)) = fl)
    by (unfold build_code; rewrite SA; rewrite <- EFL;
        destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [lia|];
        destruct (Z.ltb_spec (Z.of_nat (length oj)) fl); [lia | reflexivity]).
  assert (Hsvz : sv = (if mode =? 1 then 0 else spec_sum bb))
    by (pose proof Hmode as HM; unfold keep in HM;
        destruct HM as [-> | ->]; rewrite Esv; cbn [Z.eqb];
        [rewrite lib_sum16_eq, spec_sum_eq; reflexivity | reflexivity]).
  (* 0x184a4: body_len is 0 *)
  step.
  destruct (Nat.eq_dec (length bb) 0) as [N0|N0].
  { take true.
    assert (Hb4 : j4 = bb).
    { pose proof P4 as [[[Lj4 _] _] _]. apply nil_of_len; [exact Lj4 | exact N0]. }
    assert (Hpad : repeat (b8 0) (30 - length bb) = repeat (b8 0) (30 - length bb)) by reflexivity.
    memset_tail MSET P5 out bb Q5.
    ok_fin sp lo fl out oj bb FR STa ST0 MUO WMO MU WM Dosp Q1 Q2 P3 P4 Q5 P6 BC Hb4 Hpad Hsvz FLr LEN FLN. }
  take false.
  (* 0x184a8: out + 30 wraps *)
  do 2 step. take false.
  (* 0x184b0: memcpy (out + 30, body, body_len) *)
  do 4 step.
  xport BB2 BB4 MUO WMO ltac:(unfold keep in Dbody).
  assert (UO30 : bv_unsigned (Z_to_bv 64 (out + 30)) = out + 30) by (apply unsigned_lit; lia).
  assert (UB : bv_unsigned (Z_to_bv 64 body) = body) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 (Z.of_nat (length bb))) = Z.of_nat (length bb))
    by (apply unsigned_lit; lia).
  call MCPY; [ rewrite UB; exact BB4 | rewrite UN, Nat2Z.id; reflexivity
             | rewrite UO30, UN, Nat2Z.id; exact P4
             | rewrite UB, UO30, UN; unfold keep in Dbody; lia | assumption | ].
  lazymatch goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ =>
    rewrite UO30, UN, Nat2Z.id in H; rename H into Q4 end.
  (* 0x184c0: body_len > 29 *)
  do 2 step.
  destruct (Z_lt_le_dec 29 (Z.of_nat (length bb))) as [NB|NB].
  2: { take false.
       assert (Hb4 : bb = bb) by reflexivity.
       assert (Hpad : repeat (b8 0) (30 - length bb) = repeat (b8 0) (30 - length bb)) by reflexivity.
       memset_tail MSET P5 out bb Q5.
       ok_fin sp lo fl out oj bb FR STa ST0 MUO WMO MU WM Dosp Q1 Q2 P3 Q4 Q5 P6 BC Hb4 Hpad Hsvz FLr LEN FLN. }
  take true.
  assert (Hb4 : bb = bb) by reflexivity.
  assert (Hpad : j5 = repeat (b8 0) (30 - length bb)).
  { pose proof P5 as [[[Lj5 _] _] _].
    apply nil_of_len; rewrite repeat_length; [exact Lj5 | apply sub30_0; exact NB]. }
  ok_fin sp lo fl out oj bb FR STa ST0 MUO WMO MU WM Dosp Q1 Q2 P3 Q4 P5 P6 BC Hb4 Hpad Hsvz FLr LEN FLN.
Qed.
