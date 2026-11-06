(* spec_read_frame_seg_mid: the SPEC_OK part of run 2 of spec_read_frame (image B; lib/B/Prog/spec_read_frame_seg_run.v):
     srf_mid_F  0x83b44 .. 0x83e24: the checks and loads of b[16] .. b[29] and the field stores sum (fp + 28), send
                (fp + 32), ack (fp + 36), retry (fp + 30), cmd (fp + 40), ncmds (fp + 41), body (fp + 48), body_len
                (fp + 56), pad_len (fp + 64), each behind its UBSan wrap test and its ASan store check; then
                lib/B/Prog/spec_read_frame_seg_tail.v srf_sum_F (body_sum and the code store). The cells it leaves are
                TContract.sf_bytes of the SPEC_OK record (spec_read_frame_seg_run.v srf_ok_bytes). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import spec_read_frame_seg_run spec_read_frame_seg_tail.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Section Mid.
Variables (RNG : ExecF.footprint) (m0 : word -> option byte) (sp : word) (b len fp : Z) (frame junk : list byte)
  (c3 c2 c1 c0 cra : word).
Hypothesis CX : srf_cx RNG m0 sp b len fp frame junk c3 c2 c1 c0 cra.

Lemma srf_mid_F : forall (gp tp ra1 t0 t1 t2 a0 a1 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  munch [(fp, fp + 80)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m fp (srf_cells 0 b (b + 6) (DS.spec_be16 (TW.zs frame) 12) (DS.spec_be16 (TW.zs frame) 14)
                         0 0 0 0 (Z_to_bv 8 0) (Z_to_bv 8 0) 0 0 0 0) ->
  30 <= len -> 16 <= DS.spec_be16 (TW.zs frame) 14 -> DS.spec_be16 (TW.zs frame) 14 <= len - 14 ->
  ExecF.evtF rsegs RNG
    (srf_q2 sp gp tp cra c0 c1 c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 fp 0 (TCt.sf_bytes b (srf_okf frame len)))
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 fp) (Z_to_bv 64 len)
             a0 a1 (Z_to_bv 64 (DS.spec_be16 (TW.zs frame) 14)) (Z_to_bv 64 (-17)) a4 a5 a6 a7
             (Z_to_bv 64 b) (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x83b44) fc None m (seg_rom rsegs)).
Proof.
  intros gp tp ra1 t0 t1 t2 a0 a1 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MU WMo ST HL HN1 HN2.
  srf_open CX.
  lazymatch goal with |- ExecF.evtF _ _ ?Q _ => set (QQ := Q) end.
  unfold srf_cells in ST.
  pose proof (srf_be16_range (TW.zs frame) 14) as RNB.
  (* 0x83b44: b + 16 wraps: the trap word *)
  step. srf_br false.
  (* 0x83b48-0x83b50: a0 = b + 16; b + 16 = 2^64 - 1 *)
  step. step. step. srf_br false.
  (* 0x83b54-0x83b60: the check of b + 16 *)
  step. srf_shr. step. srf_shf 16 SHF0 FSOUT RSF MU k16 SK16. step.
  srf_join 13 K16; [srf_chk K16 k16 SK16|]. srf_clear.
  (* 0x83b64-0x83b78: the check of b + 17, the load of b[16] *)
  step. step. srf_shr. step. srf_shf 17 SHF0 FSOUT RSF MU k17 SK17. step.
  srf_ldf 16 FR0 FOUT MU. step.
  srf_join 10 K17; [srf_chk K17 k17 SK17|]. srf_clear.
  (* 0x83b7c-0x83b90: the check of the 2-byte store at fp + 28, the load of b[17] *)
  step. step. srf_shr. step. srf_shp 28 SHP0 PSOUT RSP MU. step.
  srf_ldf 17 FR0 FOUT MU. step. step. srf_br false. srf_clear.
  (* 0x83b94-0x83ba0: sum = b[16] << 8 | b[17], a3 = -19, stored at fp + 28 *)
  step. step. rewrite (srf_be16c frame 16 17 eq_refl). step. step.
  (* 0x83ba4: b + 18 wraps *)
  step. srf_br false.
  (* 0x83ba8-0x83bb8: a0 = b + 18, its check *)
  step. step. srf_shr. step. srf_shf 18 SHF0 FSOUT RSF MU k18 SK18. step.
  srf_join 13 K18; [srf_chk K18 k18 SK18|]. srf_clear.
  (* 0x83bbc-0x83bc0: b + 18 = 2^64 - 1 *)
  step. step. srf_br false.
  (* 0x83bc4-0x83bd8: the check of b + 19, the load of b[18] *)
  step. step. srf_shr. step. srf_shf 19 SHF0 FSOUT RSF MU k19 SK19. step.
  srf_ldf 18 FR0 FOUT MU. step.
  srf_join 15 K19; [srf_chk K19 k19 SK19|]. srf_clear.
  (* 0x83bdc-0x83be4: b + 21 below 2 (b + 21 wraps) *)
  step. step. step. srf_br false.
  (* 0x83be8-0x83bfc: the check of b + 20, the load of b[19] *)
  step. step. srf_shr. step. srf_shf 20 SHF0 FSOUT RSF MU k20 SK20. step.
  srf_ldf 19 FR0 FOUT MU. step.
  srf_join 11 K20; [srf_chk K20 k20 SK20|]. srf_clear.
  (* 0x83c00-0x83c14: the check of b + 21, the load of b[20] *)
  step. step. srf_shr. step. srf_shf 21 SHF0 FSOUT RSF MU k21 SK21. step.
  srf_ldf 20 FR0 FOUT MU. step.
  srf_join 10 K21; [srf_chk K21 k21 SK21|]. srf_clear.
  (* 0x83c18-0x83c2c: the check of the 4-byte store at fp + 32, the load of b[21] *)
  step. step. srf_shr. step. srf_shp 32 SHP0 PSOUT RSP MU. step.
  srf_ldf 21 FR0 FOUT MU. step. step. srf_br false. srf_clear.
  (* 0x83c30-0x83c44: send = b[18] << 24 | b[19] << 16 | b[20] << 8 | b[21] *)
  step. step. step. step. step. step. rewrite (srf_be32c frame 18 19 20 21 eq_refl eq_refl eq_refl).
  (* 0x83c48-0x83c4c: a3 = -23, send stored at fp + 32 *)
  step. step.
  (* 0x83c50: b + 22 wraps *)
  step. srf_br false.
  (* 0x83c54-0x83c64: a0 = b + 22, its check *)
  step. step. srf_shr. step. srf_shf 22 SHF0 FSOUT RSF MU k22 SK22. step.
  srf_join 13 K22; [srf_chk K22 k22 SK22|]. srf_clear.
  (* 0x83c68-0x83c6c: b + 22 = 2^64 - 1 *)
  step. step. srf_br false.
  (* 0x83c70-0x83c84: the check of b + 23, the load of b[22] *)
  step. step. srf_shr. step. srf_shf 23 SHF0 FSOUT RSF MU k23 SK23. step.
  srf_ldf 22 FR0 FOUT MU. step.
  srf_join 15 K23; [srf_chk K23 k23 SK23|]. srf_clear.
  (* 0x83c88-0x83c90: b + 25 below 2 *)
  step. step. step. srf_br false.
  (* 0x83c94-0x83ca8: the check of b + 24, the load of b[23] *)
  step. step. srf_shr. step. srf_shf 24 SHF0 FSOUT RSF MU k24 SK24. step.
  srf_ldf 23 FR0 FOUT MU. step.
  srf_join 11 K24; [srf_chk K24 k24 SK24|]. srf_clear.
  (* 0x83cac-0x83cc0: the check of b + 25, the load of b[24] *)
  step. step. srf_shr. step. srf_shf 25 SHF0 FSOUT RSF MU k25 SK25. step.
  srf_ldf 24 FR0 FOUT MU. step.
  srf_join 10 K25; [srf_chk K25 k25 SK25|]. srf_clear.
  (* 0x83cc4-0x83cd8: the check of the 4-byte store at fp + 36, the load of b[25] *)
  step. step. srf_shr. step. srf_shp 36 SHP0 PSOUT RSP MU. step.
  srf_ldf 25 FR0 FOUT MU. step. step. srf_br false. srf_clear.
  (* 0x83cdc-0x83cf0: ack = b[22] << 24 | b[23] << 16 | b[24] << 8 | b[25] *)
  step. step. step. step. step. step. rewrite (srf_be32c frame 22 23 24 25 eq_refl eq_refl eq_refl).
  (* 0x83cf4-0x83cf8: a3 = -27, ack stored at fp + 36 *)
  step. step.
  (* 0x83cfc: b + 26 wraps *)
  step. srf_br false.
  (* 0x83d00-0x83d08: a0 = b + 26; b + 26 = 2^64 - 1 *)
  step. step. step. srf_br false.
  (* 0x83d0c-0x83d18: the check of b + 26 *)
  step. srf_shr. step. srf_shf 26 SHF0 FSOUT RSF MU k26 SK26. step.
  srf_join 13 K26; [srf_chk K26 k26 SK26|]. srf_clear.
  (* 0x83d1c-0x83d30: the check of b + 27, the load of b[26] *)
  step. step. srf_shr. step. srf_shf 27 SHF0 FSOUT RSF MU k27 SK27. step.
  srf_ldf 26 FR0 FOUT MU. step.
  srf_join 10 K27; [srf_chk K27 k27 SK27|]. srf_clear.
  (* 0x83d34-0x83d48: the check of the 2-byte store at fp + 30, the load of b[27] *)
  step. step. srf_shr. step. srf_shp 30 SHP0 PSOUT RSP MU. step.
  srf_ldf 27 FR0 FOUT MU. step. step. srf_br false. srf_clear.
  (* 0x83d4c-0x83d58: retry = b[26] << 8 | b[27], a3 = -29, stored at fp + 30 *)
  step. step. rewrite (srf_be16c frame 26 27 eq_refl). step. step.
  (* 0x83d5c: b + 28 wraps *)
  step. srf_br false.
  (* 0x83d60-0x83d70: a0 = b + 28, its check *)
  step. step. srf_shr. step. srf_shf 28 SHF0 FSOUT RSF MU k28 SK28. step.
  srf_join 13 K28; [srf_chk K28 k28 SK28|]. srf_clear.
  (* 0x83d74-0x83d88: the check of the 1-byte store at fp + 40, the load of b[28] *)
  step. step. srf_shr. step. srf_shp 40 SHP0 PSOUT RSP MU. step.
  srf_ldf 28 FR0 FOUT MU. step. step. srf_br false. srf_clear.
  (* 0x83d8c-0x83d90: a3 = -30, cmd stored at fp + 40 (zxb unfolded before the `sb`; srf_c1 turns the stored byte
     back into the loaded byte) *)
  step. unfold zxb. step. rewrite srf_c1 in ST.
  (* 0x83d94: b + 29 wraps *)
  step. srf_br false.
  (* 0x83d98-0x83da8: a0 = b + 29, its check *)
  step. step. srf_shr. step. srf_shf 29 SHF0 FSOUT RSF MU k29 SK29. step.
  srf_join 13 K29; [srf_chk K29 k29 SK29|]. srf_clear.
  (* 0x83dac-0x83dc0: the check of the 1-byte store at fp + 41, the load of b[29] *)
  step. step. srf_shr. step. srf_shp 41 SHP0 PSOUT RSP MU. step.
  srf_ldf 29 FR0 FOUT MU. step. step. srf_br false. srf_clear.
  (* 0x83dc4-0x83dc8: a3 = -31, ncmds stored at fp + 41 *)
  step. unfold zxb. step. rewrite srf_c1 in ST.
  (* 0x83dcc: b + 30 wraps *)
  step. srf_br false.
  (* 0x83dd0-0x83de0: the check of the 8-byte store at fp + 48 *)
  step. step. srf_shr. step. srf_shp 48 SHP0 PSOUT RSP MU. step. step. srf_br false. srf_clear.
  (* 0x83de4-0x83dec: s2 = body = b + 30, a0 = fp + 56, body stored at fp + 48 *)
  step. step. step.
  (* 0x83df0-0x83dfc: the check of the 8-byte store at fp + 56 *)
  step. srf_shr. step. srf_shp 56 SHP0 PSOUT RSP MU. step. step. srf_br false. srf_clear.
  (* 0x83e00-0x83e08: a1 = body_len = numbytes - 16, a0 = fp + 64, body_len stored at fp + 56 *)
  step. replace (DS.spec_be16 (TW.zs frame) 14 + -16) with (DS.spec_be16 (TW.zs frame) 14 - 16) by lia.
  step. step.
  (* 0x83e0c-0x83e18: the check of the 8-byte store at fp + 64 *)
  step. srf_shr. step. srf_shp 64 SHP0 PSOUT RSP MU. step. step. srf_br false. srf_clear.
  (* 0x83e1c-0x83e24: pad_len = len - numbytes - 14, stored at fp + 64 *)
  step.
  rewrite (unsigned_lit len), (unsigned_lit (DS.spec_be16 (TW.zs frame) 14)) by lia.
  step.
  replace (len - DS.spec_be16 (TW.zs frame) 14 + -14) with (len - 30 - (DS.spec_be16 (TW.zs frame) 14 - 16)) by lia.
  step.
  (* 0x83e28: body_sum, then the code store *)
  eapply srf_sum_F; [exact CX | exact MU | exact WMo | exact ST | lia | lia |].
  exact (srf_ok_bytes frame b len).
Qed.
End Mid.
