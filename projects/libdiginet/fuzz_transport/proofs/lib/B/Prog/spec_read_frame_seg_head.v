(* spec_read_frame_seg_head: run 2 of spec_read_frame (image B; lib/B/Prog/spec_read_frame_seg_run.v), from the
   memset's return (0x83a00) to 0x83b44, and with it the whole of run 2:
     srf_run2_F  0x83a00 .. 0x83b44: len < 30 (SPEC_E_SHORT); the UBSan checks; the checks and loads of b[12], b[13];
                 ethertype stored at fp + 24 (<> 0x885f: SPEC_E_ETHERTYPE); the checks and loads of b[14], b[15];
                 numbytes stored at fp + 26 (< 16 or above len - 14: SPEC_E_LENGTH); dst = b at fp + 8; src = b + 6 at
                 fp + 16; then lib/B/Prog/spec_read_frame_seg_mid.v srf_mid_F. Each error code joins the code store
                 (spec_read_frame_seg_tail.v srf_epi_F) with the model's error record (srf_fm_short / _et / _len). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import spec_read_frame_seg_run spec_read_frame_seg_tail
  spec_read_frame_seg_mid.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Section Head.
Variables (RNG : ExecF.footprint) (m0 : word -> option byte) (sp : word) (b len fp : Z) (frame junk : list byte)
  (c3 c2 c1 c0 cra : word).
Hypothesis CX : srf_cx RNG m0 sp b len fp frame junk c3 c2 c1 c0 cra.

Lemma srf_run2_F : forall (gp tp ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  munch [(fp, fp + 80)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m fp (srf_cells 0 0 0 0 0 0 0 0 0 (Z_to_bv 8 0) (Z_to_bv 8 0) 0 0 0 0) ->
  ExecF.evtF rsegs RNG
    (srf_q2 sp gp tp cra c0 c1 c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 fp
       (DS.sf_code (srf_fm frame len)) (TCt.sf_bytes b (srf_fm frame len)))
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 fp) (Z_to_bv 64 len)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 b) (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SRF_RET1) fc None m (seg_rom rsegs)).
Proof.
  intros gp tp ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MU WMo ST.
  srf_open CX. unfold SRF_RET1.
  lazymatch goal with |- ExecF.evtF _ _ ?Q _ => set (QQ := Q) end.
  unfold srf_cells in ST.
  (* 0x83a00-0x83a04: len <= 29 goes to SPEC_E_SHORT *)
  step. step. srf_cond. destruct (Z.ltb_spec 29 len) as [HL|HL]; cbv iota.
  2:{ (* 0x83a08-0x83a14: the alignment check of fp, a0 = -2, the jump to the code store *)
      step. srf_shr. rewrite P8. step. srf_br false. step. step.
      unfold QQ. rewrite (srf_fm_short frame len) by lia.
      eapply srf_epi_F; [exact CX | exact MU | exact WMo | exact ST |].
      srf_bytes. }
  (* 0x83a18-0x83a34: the UBSan checks before b[12] *)
  step. srf_br false. step. step. srf_br false. step. step. step. srf_br false.
  step. srf_shr. rewrite P8. step. srf_br false.
  (* 0x83a38-0x83a44: the check of b + 12 *)
  step. step. srf_shr. srf_shf 12 SHF0 FSOUT RSF MU k12 SK12. step.
  srf_join 12 K12; [srf_chk K12 k12 SK12|]. srf_clear.
  (* 0x83a48-0x83a5c: the check of b + 13, the load of b[12] *)
  step. step. srf_shr. step. srf_shf 13 SHF0 FSOUT RSF MU k13 SK13. step.
  srf_ldf 12 FR0 FOUT MU. step.
  srf_join 13 K13; [srf_chk K13 k13 SK13|]. srf_clear.
  (* 0x83a60-0x83a74: the check of the 2-byte store at fp + 24, the load of b[13] *)
  step. step. srf_shr. step. srf_shp 24 SHP0 PSOUT RSP MU. step.
  srf_ldf 13 FR0 FOUT MU. step. step. srf_br false. srf_clear.
  (* 0x83a78-0x83a88: ethertype = b[12] << 8 | b[13], stored at fp + 24 *)
  step. step. rewrite (srf_be16c frame 12 13 eq_refl).
  pose proof (srf_be16_range (TW.zs frame) 12) as RET.
  step. step. step.
  (* 0x83a8c: ethertype <> 0x885f goes to 0x83e70: a0 = -3 *)
  step. srf_cond. destruct (Z.eqb_spec (DS.spec_be16 (TW.zs frame) 12) 34911) as [HET|HET]; cbn [negb]; cbv iota.
  2:{ step. unfold QQ. rewrite (srf_fm_et frame len) by lia.
      eapply srf_epi_F; [exact CX | exact MU | exact WMo | exact ST |].
      srf_bytes. }
  (* 0x83a90-0x83aa0: the UBSan checks of b + 14, b + 15 *)
  step. step. srf_br false. step. step. step. srf_br false.
  (* 0x83aa4-0x83ab0: the check of b + 14 *)
  step. srf_shr. step. srf_shf 14 SHF0 FSOUT RSF MU k14 SK14. step.
  srf_join 12 K14; [srf_chk K14 k14 SK14|]. srf_clear.
  (* 0x83ab4-0x83ac8: the check of b + 15, the load of b[14] *)
  step. step. srf_shr. step. srf_shf 15 SHF0 FSOUT RSF MU k15 SK15. step.
  srf_ldf 14 FR0 FOUT MU. step.
  srf_join 10 K15; [srf_chk K15 k15 SK15|]. srf_clear.
  (* 0x83acc-0x83ae0: the check of the 2-byte store at fp + 26, the load of b[15] *)
  step. step. srf_shr. step. srf_shp 26 SHP0 PSOUT RSP MU. step.
  srf_ldf 15 FR0 FOUT MU. step. step. srf_br false. srf_clear.
  (* 0x83ae4-0x83af0: numbytes = b[14] << 8 | b[15], stored at fp + 26 *)
  step. step. rewrite (srf_be16c frame 14 15 eq_refl).
  pose proof (srf_be16_range (TW.zs frame) 14) as RNB.
  step. step.
  (* 0x83af4-0x83af8: a0 = -4 (SPEC_E_LENGTH); numbytes < 16 goes to the code store *)
  step. step. srf_cond. destruct (Z.ltb_spec (DS.spec_be16 (TW.zs frame) 14) 16) as [HN1|HN1]; cbv iota.
  { unfold QQ. rewrite (srf_fm_len frame len) by lia.
    eapply srf_epi_F; [exact CX | exact MU | exact WMo | exact ST |]. srf_bytes. }
  (* 0x83afc-0x83b00: len - 14 < numbytes goes to the code store *)
  step. step. srf_cond. destruct (Z.ltb_spec (len + -14) (DS.spec_be16 (TW.zs frame) 14)) as [HN2|HN2]; cbv iota.
  { unfold QQ. rewrite (srf_fm_len frame len) by lia.
    eapply srf_epi_F; [exact CX | exact MU | exact WMo | exact ST |]. srf_bytes. }
  (* 0x83b04-0x83b14: the check of the 8-byte store at fp + 8 *)
  step. step. srf_shr. step. srf_shp 8 SHP0 PSOUT RSP MU. step. step. srf_br false. srf_clear.
  (* 0x83b18-0x83b24: a1 = b + 6, a3 = 7, dst = b stored at fp + 8; b + 6 below 7 traps *)
  step. step. step. step. srf_br false.
  (* 0x83b28-0x83b38: the check of the 8-byte store at fp + 16 *)
  step. step. srf_shr. step. srf_shp 16 SHP0 PSOUT RSP MU. step. step. srf_br false. srf_clear.
  (* 0x83b3c-0x83b40: a3 = -17, src = b + 6 stored at fp + 16 *)
  step. step.
  (* 0x83b44 on: the SPEC_OK record *)
  unfold QQ. rewrite (srf_fm_ok frame len) by lia. change (DS.sf_code (srf_okf frame len)) with 0.
  eapply srf_mid_F; [exact CX | exact MU | exact WMo | exact ST | lia | lia | lia].
Qed.
End Head.
