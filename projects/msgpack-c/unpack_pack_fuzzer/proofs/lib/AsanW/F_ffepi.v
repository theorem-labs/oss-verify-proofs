(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section FFEPI.
Variable segs : list Segment.

Lemma ffepi_walk : forall (RNG : footprint) (R FR : bvmap 5 word) (pc : word) (fc : bv 32) (m : word -> option byte)
    (w1 w2 : bv 32) (sg : bool) (RT RF R2 : reg) (imm imm2 : bv 12) (Fa flg : Z),
  fetch_word segs pc = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (Load SZ8 sg RT RF imm, 4) ->
  fetch_word segs (bv_add pc (Z_to_bv 64 4)) = Some w2 -> is_ecall w2 = false ->
  decode_any w2 = Some (Store SZ1 RT R2 imm2, 4) -> is_x0 R2 = true -> bv_unsigned (sext 64 imm2) = 0 ->
  is_x0 RT = false ->
  bv_add (getr R RF) (sext 64 imm) = wa Fa ->
  bytes_at segs m Fa (le8 (Z_to_bv 64 flg)) -> wr_at segs m flg 1 -> 0 <= flg < 2^64 ->
  rng RNG Fa 8 -> rng RNG flg 1 ->
  evtF segs RNG (fun ms' => ms' = MS (regupd R RT (Z_to_bv 64 flg)) FR (bv_add (bv_add pc (Z_to_bv 64 4)) (Z_to_bv 64 4)) fc None
                                      (write_to_mem m (wa flg) [Z_to_bv 8 0]) (seg_rom segs))
       (MS R FR pc fc None m (seg_rom segs)).
Proof.
  intros RNG R FR pc fc m w1 w2 sg RT RF R2 imm imm2 Fa flg F1 E1 D1 F2 E2 D2 X2 I2 NX ADDR BA WR FLG RG1 RG2.
  assert (RD : ov_read_bytes segs m (wa Fa) 8 = Some (le8 (Z_to_bv 64 flg))).
  { replace (wa Fa) with (wa (Fa + Z.of_nat 0)) by (f_equal; lia).
    pose proof (length_le8 (Z_to_bv 64 flg)) as LL.
    rewrite (bytes_at_ov_read segs m Fa (le8 (Z_to_bv 64 flg)) 0 8 BA).
    2:{ lia. }
    rewrite skipn_O, firstn_all2 by lia. reflexivity. }
  assert (SO : store_ok segs m (wa flg) 1 = true).
  { replace (wa flg) with (wa (flg + 0)) by (f_equal; lia). apply (wr_at_store_ok segs m flg 1 0 1 WR); lia. }
  eapply (evtF_step_acc segs RNG).
  - reflexivity.
  - rewrite (stepF_gen segs R FR pc fc None m (seg_rom segs) w1 _ _ F1 E1 D1).
    cbn [exec load_val].
    change (rget {| c_regs := R; c_fregs := FR; c_pc := pc; c_fcsr := fc; c_resv := None |} RF) with (getr R RF).
    rewrite ADDR. cbn [interp_eff_accesses]. change (width_bytes 64) with 8%nat. rewrite RD. rewrite load_u64.
    unfold rset. rewrite NX. cbn [lift_resultF with_pc with_regs c_regs c_fregs c_pc c_fcsr c_resv MS_of_core]. reflexivity.
  - cbn [accessed_ranges]. constructor; [| constructor]. unfold wa. apply (rng_acc_lit RNG Fa 8 Fa 8 RG1); lia.
  - cbn [access_value with_regs with_pc c_regs c_fregs c_pc c_fcsr c_resv MS_of_core fst snd].
    eapply (evtF_step_acc segs RNG).
    + reflexivity.
    + lazymatch goal with |- step_accesses segs ?ms0 = _ =>
        change ms0 with (MS (regupd R RT (Z_to_bv 64 flg)) FR (bv_add pc (Z_to_bv 64 4)) fc None m (seg_rom segs)) end.
      rewrite (stepF_gen segs _ FR _ fc None m (seg_rom segs) w2 _ _ F2 E2 D2).
      cbn [exec store_val].
      assert (G1 : rget {| c_regs := regupd R RT (Z_to_bv 64 flg); c_fregs := FR; c_pc := bv_add pc (Z_to_bv 64 4); c_fcsr := fc; c_resv := None |} RT
                   = Z_to_bv 64 flg).
      { unfold rget. rewrite NX. cbn [c_regs]. unfold regupd. apply reg_get_set_same. }
      rewrite G1.
      assert (A2 : bv_add (Z_to_bv 64 flg) (sext 64 imm2) = wa flg).
      { unfold wa. apply bv_eq. rewrite bv_add_unsigned. rewrite I2.
        rewrite Z.add_0_r. rewrite Z_to_bv_unsigned. apply bv_wrap_idemp. }
      rewrite A2.
      assert (G2 : rget {| c_regs := regupd R RT (Z_to_bv 64 flg); c_fregs := FR; c_pc := bv_add pc (Z_to_bv 64 4); c_fcsr := fc; c_resv := None |} R2 = w0)
        by (unfold rget; rewrite X2; reflexivity).
      rewrite G2.
      cbn [interp_eff_accesses]. change (width_bytes 8) with 1%nat. rewrite SO.
      unfold inval_resv. cbn [with_pc c_regs c_fregs c_pc c_fcsr c_resv lift_resultF MS_of_core].
      reflexivity.
    + cbn [accessed_ranges access_value]. constructor; [| constructor]. unfold wa. apply (rng_acc_lit RNG flg 1 flg 1 RG2); lia.
    + cbn [access_value with_pc c_regs c_fregs c_pc c_fcsr c_resv MS_of_core fst snd]. apply evtF_done.
      change (Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 w0))) with [Z_to_bv 8 0]. reflexivity.
Qed.

Lemma ffepi_walk_off : forall (RNG : footprint) (R FR : bvmap 5 word) (pc : word) (fc : bv 32) (m : word -> option byte)
    (w1 w2 : bv 32) (sg : bool) (RT RF R2 : reg) (imm imm2 : bv 12) (Fb OFF flg : Z),
  fetch_word segs pc = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (Load SZ8 sg RT RF imm, 4) ->
  fetch_word segs (bv_add pc (Z_to_bv 64 4)) = Some w2 -> is_ecall w2 = false ->
  decode_any w2 = Some (Store SZ1 RT R2 imm2, 4) -> is_x0 R2 = true -> bv_unsigned (sext 64 imm2) = 0 ->
  is_x0 RT = false ->
  getr R RF = Z_to_bv 64 Fb -> sext 64 imm = Z_to_bv 64 OFF ->
  bytes_at segs m (Fb + OFF) (le8 (Z_to_bv 64 flg)) -> wr_at segs m flg 1 -> 0 <= flg < 2^64 ->
  rng RNG (Fb + OFF) 8 -> rng RNG flg 1 ->
  evtF segs RNG (fun ms' => ms' = MS (regupd R RT (Z_to_bv 64 flg)) FR (bv_add pc (Z_to_bv 64 8)) fc None
                                      (write_to_mem m (wa flg) [Z_to_bv 8 0]) (seg_rom segs))
       (MS R FR pc fc None m (seg_rom segs)).
Proof.
  intros RNG R FR pc fc m w1 w2 sg RT RF R2 imm imm2 Fb OFF flg F1 E1 D1 F2 E2 D2 X2 I2 NX GR IM BA WR FLG RG1 RG2.
  assert (PC8 : bv_add (bv_add pc (Z_to_bv 64 4)) (Z_to_bv 64 4) = bv_add pc (Z_to_bv 64 8)).
  { apply bv_eq. rewrite !bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 4)) with 4. change (bv_unsigned (Z_to_bv 64 8)) with 8.
    unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Zplus_mod_idemp_l. f_equal. lia. }
  rewrite <- PC8.
  apply (ffepi_walk RNG R FR pc fc m w1 w2 sg RT RF R2 imm imm2 (Fb + OFF) flg F1 E1 D1 F2 E2 D2 X2 I2 NX); try assumption.
  rewrite GR, IM. unfold wa. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- Zplus_mod. reflexivity.
Qed.
End FFEPI.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg.
Unset Nia Cache. Unset Nra Cache.
Definition ffepi_shape (pcz : Z) (rt rf off : Z) : bool :=
  match fetch_word asegs (Z_to_bv 64 pcz), fetch_word asegs (bv_add (Z_to_bv 64 pcz) (Z_to_bv 64 4)) with
  | Some w1, Some w2 =>
      negb (is_ecall w1) && negb (is_ecall w2) &&
      match decode_any w1, decode_any w2 with
      | Some (Load SZ8 _ t f imm, 4), Some (Store SZ1 t2 r2 imm2, 4) =>
          (bv_unsigned t =? rt) && (bv_unsigned f =? rf) && (bv_unsigned (sext 64 imm) =? off) && (bv_unsigned t2 =? rt)
          && is_x0 r2 && (bv_unsigned (sext 64 imm2) =? 0) && negb (is_x0 t)
      | _, _ => false
      end
  | _, _ => false
  end.
Example ffepi_sites_ok :
  forallb (fun s => ffepi_shape (fst (fst (fst s))) (snd (fst (fst s))) (snd (fst s)) (snd s))
    [ (0x8ce24, 10, 18, 248); (0x8d404, 10, 18, 248); (0x8d638, 10, 10, 248); (0x8dc08, 10, 18, 120);
      (0x8dd38, 10, 18, 120); (0x94e24, 10, 18, 120); (0x94f08, 10, 18, 120); (0x957ac, 10, 26, 120);
      (0x95b58, 10, 18, 56); (0x95ed4, 10, 18, 120); (0x96250, 10, 18, 120); (0x96654, 10, 18, 120);
      (0x9695c, 10, 18, 120); (0x97178, 10, 18, 248); (0x97784, 10, 18, 248); (0x97cdc, 10, 19, 248) ] = true.
Proof. vm_compute. reflexivity. Qed.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section FFEPI.
Variable segs : list Segment.

Lemma ffepi_walk : forall (RNG : footprint) (R FR : bvmap 5 word) (pc : word) (fc : bv 32) (m : word -> option byte)
    (w1 w2 : bv 32) (sg : bool) (RT RF R2 : reg) (imm imm2 : bv 12) (Fa flg : Z),
  fetch_word segs pc = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (Load SZ8 sg RT RF imm, 4) ->
  fetch_word segs (bv_add pc (Z_to_bv 64 4)) = Some w2 -> is_ecall w2 = false ->
  decode_any w2 = Some (Store SZ1 RT R2 imm2, 4) -> is_x0 R2 = true -> bv_unsigned (sext 64 imm2) = 0 ->
  is_x0 RT = false ->
  bv_add (getr R RF) (sext 64 imm) = wa Fa ->
  bytes_at segs m Fa (le8 (Z_to_bv 64 flg)) -> wr_at segs m flg 1 -> 0 <= flg < 2^64 ->
  rng RNG Fa 8 -> rng RNG flg 1 ->
  evtF segs RNG (fun ms' => ms' = MS (regupd R RT (Z_to_bv 64 flg)) FR (bv_add (bv_add pc (Z_to_bv 64 4)) (Z_to_bv 64 4)) fc None
                                      (write_to_mem m (wa flg) [Z_to_bv 8 0]) (seg_rom segs))
       (MS R FR pc fc None m (seg_rom segs)).
Proof.
  intros RNG R FR pc fc m w1 w2 sg RT RF R2 imm imm2 Fa flg F1 E1 D1 F2 E2 D2 X2 I2 NX ADDR BA WR FLG RG1 RG2.
  assert (RD : ov_read_bytes segs m (wa Fa) 8 = Some (le8 (Z_to_bv 64 flg))).
  { replace (wa Fa) with (wa (Fa + Z.of_nat 0)) by (f_equal; lia).
    pose proof (length_le8 (Z_to_bv 64 flg)) as LL.
    rewrite (bytes_at_ov_read segs m Fa (le8 (Z_to_bv 64 flg)) 0 8 BA).
    2:{ lia. }
    rewrite skipn_O, firstn_all2 by lia. reflexivity. }
  assert (SO : store_ok segs m (wa flg) 1 = true).
  { replace (wa flg) with (wa (flg + 0)) by (f_equal; lia). apply (wr_at_store_ok segs m flg 1 0 1 WR); lia. }
  eapply (evtF_step_acc segs RNG).
  - reflexivity.
  - rewrite (stepF_gen segs R FR pc fc None m (seg_rom segs) w1 _ _ F1 E1 D1).
    cbn [exec load_val].
    change (rget {| c_regs := R; c_fregs := FR; c_pc := pc; c_fcsr := fc; c_resv := None |} RF) with (getr R RF).
    rewrite ADDR. cbn [interp_eff_accesses]. change (width_bytes 64) with 8%nat. rewrite RD. rewrite load_u64.
    unfold rset. rewrite NX. cbn [lift_resultF with_pc with_regs c_regs c_fregs c_pc c_fcsr c_resv MS_of_core]. reflexivity.
  - cbn [accessed_ranges]. constructor; [| constructor]. unfold wa. apply (rng_acc_lit RNG Fa 8 Fa 8 RG1); lia.
  - cbn [access_value with_regs with_pc c_regs c_fregs c_pc c_fcsr c_resv MS_of_core fst snd].
    eapply (evtF_step_acc segs RNG).
    + reflexivity.
    + lazymatch goal with |- step_accesses segs ?ms0 = _ =>
        change ms0 with (MS (regupd R RT (Z_to_bv 64 flg)) FR (bv_add pc (Z_to_bv 64 4)) fc None m (seg_rom segs)) end.
      rewrite (stepF_gen segs _ FR _ fc None m (seg_rom segs) w2 _ _ F2 E2 D2).
      cbn [exec store_val].
      assert (G1 : rget {| c_regs := regupd R RT (Z_to_bv 64 flg); c_fregs := FR; c_pc := bv_add pc (Z_to_bv 64 4); c_fcsr := fc; c_resv := None |} RT
                   = Z_to_bv 64 flg).
      { unfold rget. rewrite NX. cbn [c_regs]. unfold regupd. apply reg_get_set_same. }
      rewrite G1.
      assert (A2 : bv_add (Z_to_bv 64 flg) (sext 64 imm2) = wa flg).
      { unfold wa. apply bv_eq. rewrite bv_add_unsigned. rewrite I2.
        rewrite Z.add_0_r. rewrite Z_to_bv_unsigned. apply bv_wrap_idemp. }
      rewrite A2.
      assert (G2 : rget {| c_regs := regupd R RT (Z_to_bv 64 flg); c_fregs := FR; c_pc := bv_add pc (Z_to_bv 64 4); c_fcsr := fc; c_resv := None |} R2 = w0)
        by (unfold rget; rewrite X2; reflexivity).
      rewrite G2.
      cbn [interp_eff_accesses]. change (width_bytes 8) with 1%nat. rewrite SO.
      unfold inval_resv. cbn [with_pc c_regs c_fregs c_pc c_fcsr c_resv lift_resultF MS_of_core].
      reflexivity.
    + cbn [accessed_ranges access_value]. constructor; [| constructor]. unfold wa. apply (rng_acc_lit RNG flg 1 flg 1 RG2); lia.
    + cbn [access_value with_pc c_regs c_fregs c_pc c_fcsr c_resv MS_of_core fst snd]. apply evtF_done.
      change (Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 w0))) with [Z_to_bv 8 0]. reflexivity.
Qed.

Lemma ffepi_walk_off : forall (RNG : footprint) (R FR : bvmap 5 word) (pc : word) (fc : bv 32) (m : word -> option byte)
    (w1 w2 : bv 32) (sg : bool) (RT RF R2 : reg) (imm imm2 : bv 12) (Fb OFF flg : Z),
  fetch_word segs pc = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (Load SZ8 sg RT RF imm, 4) ->
  fetch_word segs (bv_add pc (Z_to_bv 64 4)) = Some w2 -> is_ecall w2 = false ->
  decode_any w2 = Some (Store SZ1 RT R2 imm2, 4) -> is_x0 R2 = true -> bv_unsigned (sext 64 imm2) = 0 ->
  is_x0 RT = false ->
  getr R RF = Z_to_bv 64 Fb -> sext 64 imm = Z_to_bv 64 OFF ->
  bytes_at segs m (Fb + OFF) (le8 (Z_to_bv 64 flg)) -> wr_at segs m flg 1 -> 0 <= flg < 2^64 ->
  rng RNG (Fb + OFF) 8 -> rng RNG flg 1 ->
  evtF segs RNG (fun ms' => ms' = MS (regupd R RT (Z_to_bv 64 flg)) FR (bv_add pc (Z_to_bv 64 8)) fc None
                                      (write_to_mem m (wa flg) [Z_to_bv 8 0]) (seg_rom segs))
       (MS R FR pc fc None m (seg_rom segs)).
Proof.
  intros RNG R FR pc fc m w1 w2 sg RT RF R2 imm imm2 Fb OFF flg F1 E1 D1 F2 E2 D2 X2 I2 NX GR IM BA WR FLG RG1 RG2.
  assert (PC8 : bv_add (bv_add pc (Z_to_bv 64 4)) (Z_to_bv 64 4) = bv_add pc (Z_to_bv 64 8)).
  { apply bv_eq. rewrite !bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 4)) with 4. change (bv_unsigned (Z_to_bv 64 8)) with 8.
    unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Zplus_mod_idemp_l. f_equal. lia. }
  rewrite <- PC8.
  apply (ffepi_walk RNG R FR pc fc m w1 w2 sg RT RF R2 imm imm2 (Fb + OFF) flg F1 E1 D1 F2 E2 D2 X2 I2 NX); try assumption.
  rewrite GR, IM. unfold wa. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- Zplus_mod. reflexivity.
Qed.
End FFEPI.

Unset Nia Cache. Unset Nra Cache.
Definition ffepi_shape (pcz : Z) (rt rf off : Z) : bool :=
  match fetch_word bsegs (Z_to_bv 64 pcz), fetch_word bsegs (bv_add (Z_to_bv 64 pcz) (Z_to_bv 64 4)) with
  | Some w1, Some w2 =>
      negb (is_ecall w1) && negb (is_ecall w2) &&
      match decode_any w1, decode_any w2 with
      | Some (Load SZ8 _ t f imm, 4), Some (Store SZ1 t2 r2 imm2, 4) =>
          (bv_unsigned t =? rt) && (bv_unsigned f =? rf) && (bv_unsigned (sext 64 imm) =? off) && (bv_unsigned t2 =? rt)
          && is_x0 r2 && (bv_unsigned (sext 64 imm2) =? 0) && negb (is_x0 t)
      | _, _ => false
      end
  | _, _ => false
  end.
Example ffepi_sites_ok :
  forallb (fun s => ffepi_shape (fst (fst (fst s))) (snd (fst (fst s))) (snd (fst s)) (snd s))
    [ (0x8d7b4, 10, 18, 248); (0x8ddf0, 10, 23, 248); (0x8e028, 10, 10, 248); (0x8e648, 10, 18, 120);
      (0x8e77c, 10, 18, 120); (0x91964, 11, 12, 248); (0x96014, 10, 18, 120); (0x960f8, 10, 18, 120);
      (0x96a04, 10, 18, 56); (0x96c54, 10, 18, 56); (0x96e84, 10, 18, 56); (0x970d4, 10, 18, 56);
      (0x97e4c, 10, 18, 248); (0x984f8, 10, 18, 248); (0x98904, 10, 19, 120); (0x98c4c, 10, 19, 120);
      (0x991e4, 10, 19, 248); (0x99564, 10, 19, 120); (0x9a458, 10, 19, 120) ] = true.
Proof. vm_compute. reflexivity. Qed.
End TwinB.
