(** reac_segconf_ignore_file (UBSan build, 0x16188): proof of [reac_segconf_ignore_file_contract]
    (U/Prog/reac_segconf_ignore_file_c.v) from the contract of its callee reac_segconf_find
    (U/Prog/reac_segconf_find_c.v).

    Shape (the UBSan binary): lib/Prog/reac_segconf_ignore_file.v's walk (find at
    0x15ff0, frame 64) plus, after `beqz a0`, the alignment check `andi a1,a0,3; bnez a1` to `unimp`: s = c + 356 i
    with c 16-aligned (Prog/seg_query_facts.v sq_seg_mod4) rules it out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_find_c reac_segconf_ignore_file_c.
Import ListNotations.
Open Scope Z_scope.

(* A branch whose condition is false (tkn) or true (ntk) by arithmetic; nothing to do when the step already
   computed a closed condition. *)
Ltac tkn := let K := fresh "K" in
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      if_cases K; [clear K | exfalso; zify_cond K; Z.div_mod_to_equations; lia]
  | _ => idtac
  end.
Ltac ntk := let K := fresh "K" in
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      if_cases K; [exfalso; zify_cond K; Z.div_mod_to_equations; lia | clear K]
  | _ => idtac
  end.
(* A branch on a closed condition (a loaded flag, the cleared alignment check): computed. *)
Ltac br_closed :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in
      lazymatch v with true => idtac | false => idtac end;
      replace c with v by (vm_compute; reflexivity); cbv iota
  end.
(* The UBSan alignment check `andi r,s,3`: s mod 4 = 0 (M4) makes it 0. *)
Ltac chk4 M4 :=
  match goal with |- context [Z.land ?x 3] =>
    let L := fresh "L3" in
    assert (L : Z.land x 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact M4);
    rewrite L; clear L
  end.
(* `and a0,a1,a0` with a1 = seqz(byte) - 1, a closed mask: all ones (byte <> 0) or 0 (byte 0). *)
Ltac fold_mask :=
  match goal with |- context [Z.land ?k ?x] =>
    let k' := eval vm_compute in k in replace k with k' by (vm_compute; reflexivity)
  end.

Theorem reac_segconf_ignore_file_holds : reac_segconf_find_contract -> reac_segconf_ignore_file_contract.
Proof.
  intros FIND. unfold reac_segconf_ignore_file_contract, REAC_SEGCONF_IGNORE_FILE, IGNORE_FILE_STACK.
  change (16 + FIND_STACK) with 80.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo rc nm
    (HC0 & HC16 & (bs & HB & HE) & HAC & HN0 & (bn & HBN & HZN & HNN) & HAN & (ST & HLO & HSP & HRO) & MI).
  unfold apart, SEG_C_SIZE in HAC, HAN.
  destruct (sq_rconf_len rc bs HE) as [HL HLS].
  assert (LN : length nm = length bn) by (rewrite <- HZN; unfold zs; apply length_map).
  pose proof (bytes_at_bound _ _ _ _ HB) as B1.
  pose proof (bytes_at_bound _ _ _ _ HBN) as B2. rewrite length_app in B2. cbn [length] in B2.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 16%nat ST.
  zstep. zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply FIND with (lo := lo) (rc := rc) (nm := nm) | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold FIND_STACK in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call segs mm ]
  end.
  { unfold query_pre, stack_ok, apart, SEG_C_SIZE, FIND_STACK. rewrite !unsigned_lit by lia.
    refine (conj HC0 (conj HC16 (conj _ (conj _ (conj HN0 (conj _ (conj _ (conj (conj _ (conj _ (conj _ _))) _)))))))).
    - exists bs. split; assumption.
    - lia.
    - exists bn. split; [assumption|]. split; assumption.
    - lia.
    - exact ST.
    - lia.
    - Z.div_mod_to_equations. lia.
    - intros a Ha. apply HRO. lia.
    - assumption. }
  match goal with H : stk _ _ lo _ |- _ => rename H into ST end. rewrite unsigned_lit in ST by lia.
  rewrite sq_find_ptr. unfold ignore_file_ptr, r_ignore_file, rseg_addr, RSEG_SIZE, RS_IGNORE_FILE.
  destruct (r_find rc nm) as [i|] eqn:RF.
  - pose proof (sq_find_lt rc nm i RF) as Hi.
    pose proof (sq_seg_mod4 (bv_unsigned a0) i HC16) as M4.
    pose proof (sq_ignore_file0_range rc bs i HE Hi) as HR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (sq_ignore_set rsegs mm (bv_unsigned a0) bs rc i HB HE Hi) as RD;
      pose proof (sq_ignore_file0 rsegs mm (bv_unsigned a0) bs rc i HB HE Hi) as RD0 end.
    unfold RS_IGNORE_SET in RD. unfold RS_IGNORE_FILE in RD0.
    zstep. ntk.
    zstep. zstep. chk4 M4. br_closed.
    destruct (rs_ignore_set (r_seg rc i)) eqn:IS1; unfold b2z in RD.
    + zstep. zstep. br_closed.
      destruct (Z.eqb_spec (hd0 (rs_ignore_file (r_seg rc i))) 0) as [H0|H0].
      * rewrite H0 in RD0.
        do 5 zstep.
        fold_mask. rewrite Z.land_0_l.
        do 4 zstep.
        release_frame FR ST (bv_unsigned sp).
        finish.
      * do 5 zstep.
        assert (E8 : bv_unsigned (Z_to_bv 8 (hd0 (rs_ignore_file (r_seg rc i)))) = hd0 (rs_ignore_file (r_seg rc i))).
        { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia. }
        rewrite E8. replace (hd0 (rs_ignore_file (r_seg rc i)) <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
        fold_mask. rewrite (Z.land_comm 18446744073709551615), Z_to_bv_land64.
        do 4 zstep.
        release_frame FR ST (bv_unsigned sp).
        finish.
    + zstep. zstep. br_closed.
      do 4 zstep.
      release_frame FR ST (bv_unsigned sp).
      finish.
  - zstep. tkn.
    do 3 zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
Qed.
