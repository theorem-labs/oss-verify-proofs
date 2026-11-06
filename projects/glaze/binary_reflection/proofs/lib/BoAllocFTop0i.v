(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFZ.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI.BoAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Section FPGen.
Context {fx : FPState}.

Section Z1.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 x21 x22 ra0 s0v s1v s2v s3v s4v s5v : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2128).
  Hypothesis H8 : getr regs 8 = S.
  Hypothesis H9 : getr regs 9 = p.
  Hypothesis H18 : getr regs 18 = x18.
  Hypothesis H19 : getr regs 19 = x19.
  Hypothesis H20 : getr regs 20 = x20.
  Hypothesis H21 : getr regs 21 = x21.
  Hypothesis H22 : getr regs 22 = x22.
  Hypothesis Hp0 : p = Z_to_bv 64 0.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  (* [comment removed for export] *)
  Hypothesis Ri0 : rdn BSEGS mem (at_ S (-8)) 8 = Some (word_to_le_bytes 8 ra0).
  Hypothesis Ri1 : rdn BSEGS mem (at_ S (-16)) 8 = Some (word_to_le_bytes 8 s0v).
  Hypothesis Ri2 : rdn BSEGS mem (at_ S (-24)) 8 = Some (word_to_le_bytes 8 s1v).
  Hypothesis Ri3 : rdn BSEGS mem (at_ S (-32)) 8 = Some (word_to_le_bytes 8 s2v).
  Hypothesis Ri4 : rdn BSEGS mem (at_ S (-40)) 8 = Some (word_to_le_bytes 8 s3v).
  Hypothesis Ri5 : rdn BSEGS mem (at_ S (-48)) 8 = Some (word_to_le_bytes 8 s4v).
  Hypothesis Ri6 : rdn BSEGS mem (at_ S (-56)) 8 = Some (word_to_le_bytes 8 s5v).

  Lemma z1_run :
    exists r,
      msteps BSEGS (mkst regs (0x6ef00 : word) mem rom) (mkst r ra0 (fr_b1 mem S p x18 x19 x20 x21 x22) rom)
      /\ getr r 2 = S /\ getr r 1 = ra0 /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
      /\ getr r 20 = s4v /\ getr r 21 = s5v /\ getr r 22 = x22 /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Ri6 Ri5 Ri4 Ri3 Ri2 Ri1 Ri0 Hstk Hret HS Hp0 H22 H21 H20 H19 H18 H9 H8 H2.
    pose proof (u64_range S) as HSr. subst p.
    wd_eexists. split.
    - an F_6ef00 D_6ef00.                              (* [comment removed for export] *)
      an F_6ef04 D_6ef04.                              (* [comment removed for export] *)
      an F_6ef08 D_6ef08.                              (* [comment removed for export] *)
      an F_6ef0c D_6ef0c.                              (* [comment removed for export] *)
      an F_6ef10 D_6ef10.                              (* [comment removed for export] *)
      an F_4c258 D_4c258.                              (* [comment removed for export] *)
      an F_4c25c D_4c25c.                              (* [comment removed for export] *)
      an F_4c260 D_4c260.                              (* [comment removed for export] *)
      an F_4c264 D_4c264.                              (* [comment removed for export] *)
      an F_4c268 D_4c268.                              (* [comment removed for export] *)
      an F_4c26c D_4c26c.                              (* [comment removed for export] *)
      an F_4c270 D_4c270.                              (* [comment removed for export] *)
      an F_4c274 D_4c274.                              (* [comment removed for export] *)
      an F_4c278 D_4c278.                              (* [comment removed for export] *)
      an F_4c27c D_4c27c.                              (* [comment removed for export] *)
      an F_4c280 D_4c280.                              (* [comment removed for export] *)
      fsd F_4c284 D_4c284 (at_ S (-2136)).             (* [comment removed for export] *)
      fsd F_4c288 D_4c288 (at_ S (-2144)).             (* [comment removed for export] *)
      fsd F_4c28c D_4c28c (at_ S (-2152)).             (* [comment removed for export] *)
      fsd F_4c290 D_4c290 (at_ S (-2160)).             (* [comment removed for export] *)
      fsd F_4c294 D_4c294 (at_ S (-2168)).             (* [comment removed for export] *)
      fsd F_4c298 D_4c298 (at_ S (-2176)).             (* [comment removed for export] *)
      fsd F_4c29c D_4c29c (at_ S (-2184)).             (* [comment removed for export] *)
      fsd F_4c2a0 D_4c2a0 (at_ S (-2192)).             (* [comment removed for export] *)
      ab_tk F_4c2a4 D_4c2a4 ltac:(condz).              (* [comment removed for export] *)
      fld F_4c2e0 D_4c2e0 (Z_to_bv 64 0x6ef14).        (* [comment removed for export] *)
      fld F_4c2e4 D_4c2e4 S.                           (* [comment removed for export] *)
      fld F_4c2e8 D_4c2e8 (Z_to_bv 64 0).              (* [comment removed for export] *)
      fld F_4c2ec D_4c2ec x18.                         (* [comment removed for export] *)
      fld F_4c2f0 D_4c2f0 x19.                         (* [comment removed for export] *)
      fld F_4c2f4 D_4c2f4 x20.                         (* [comment removed for export] *)
      fld F_4c2f8 D_4c2f8 x21.                         (* [comment removed for export] *)
      fld F_4c2fc D_4c2fc x22.                         (* [comment removed for export] *)
      an F_4c300 D_4c300.                              (* [comment removed for export] *)
      rt F_4c304 D_4c304.                              (* [comment removed for export] *)
      (* [comment removed for export] *)
      an F_6ef14 D_6ef14.                              (* [comment removed for export] *)
      cld8 F_6ef18 D_6ef18 ra0 Ri0.                    (* [comment removed for export] *)
      cld8 F_6ef1c D_6ef1c s0v Ri1.                    (* [comment removed for export] *)
      cld8 F_6ef20 D_6ef20 s1v Ri2.                    (* [comment removed for export] *)
      cld8 F_6ef24 D_6ef24 s2v Ri3.                    (* [comment removed for export] *)
      cld8 F_6ef28 D_6ef28 s3v Ri4.                    (* [comment removed for export] *)
      cld8 F_6ef2c D_6ef2c s4v Ri5.                    (* [comment removed for export] *)
      cld8 F_6ef30 D_6ef30 s5v Ri6.                    (* [comment removed for export] *)
      an F_6ef34 D_6ef34.                              (* [comment removed for export] *)
      aret F_6ef38 D_6ef38 ra0.                        (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_b1 mem S (Z_to_bv 64 0) x18 x19 x20 x21 x22). rewrite ?at_0. wd_refl.
    - post.
  Qed.
End Z1.
End FPGen.
End BoAllocFZ.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRun0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i.BoAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI.BoAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRun OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem BoAllocFZ.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Section RUN0I.
  Variables (mem rom : word -> option byte) (R : bvmap 5 word).
  Variables (S p ra0 tp tsdp P top bot : word) (T tctx q32 : Z) (D : nat).
  Variable r2 : bvmap 5 word.              (* [comment removed for export] *)
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  (* [comment removed for export] *)
  Hypothesis HR1 : getr R 1 = ra0.
  Hypothesis HR2 : getr R 2 = S.
  Hypothesis HR4 : getr R 4 = tp.
  Hypothesis A2 : getr r2 2 = at_ S (-2128).
  Hypothesis A8 : getr r2 8 = S.
  Hypothesis A9 : getr r2 9 = p.
  Hypothesis A18 : getr r2 18 = ra0.
  Hypothesis A4 : getr r2 4 = getr R 4.
  Hypothesis A3 : getr r2 3 = getr R 3.
  Hypothesis A20 : getr r2 20 = getr R 20.
  Hypothesis A21 : getr r2 21 = getr R 21.
  Hypothesis A22 : getr r2 22 = getr R 22.
  Hypothesis A23 : getr r2 23 = getr R 23.
  Hypothesis A24 : getr r2 24 = getr R 24.
  Hypothesis A25 : getr r2 25 = getr R 25.
  Hypothesis A26 : getr r2 26 = getr R 26.
  Hypothesis A27 : getr r2 27 = getr R 27.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gp0 : p = Z_to_bv 64 0.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584 /\ (tctx + 4096 <= T \/ T + 4096 <= tctx))%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis GP : (AIMGLO <= U P /\ U P + 8 <= AIMGHI)%Z.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.
  Hypothesis Gbot : (U bot < U top)%Z.
  Hypothesis Gq32 : (U p / 2 ^ 32 = q32 /\ 0 <= q32 < 2 ^ 15 /\ U p / 2 ^ 47 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  (* [comment removed for export] *)
  Hypothesis C_mcs : rdn BSEGS mem (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30).
  Hypothesis C_gcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_fum : rdn BSEGS mem (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_inited : rdn BSEGS mem (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_unw : rdn BSEGS mem (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_unw_ok : store_ok BSEGS mem (at_ thr 3168) 1 = true.
  Hypothesis C_pg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 P).
  Hypothesis C_P : rdn BSEGS mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_kif : rdn BSEGS mem (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS mem (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS mem (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS mem tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS mem (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_sw : rdn BSEGS mem (at_ thr 40) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_top : rdn BSEGS mem (at_ thr 8) 8 = Some (LE8 top).
  Hypothesis C_bot : rdn BSEGS mem (at_ thr 16) 8 = Some (LE8 bot).
  Hypothesis C_hook : rdn BSEGS mem (Z_to_bv 64 0x19fc88) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_T0 : rdn BSEGS mem (Z_to_bv 64 T) 8 = Some (LE8 ctxw).
  Hypothesis C_tid : rdn BSEGS mem (Z_to_bv 64 (tctx + 8)) 4 = Some (LE4 0).
  (* [comment removed for export] *)
  Hypothesis Hfpc : fpc mem (U (getr R 8)) (U S) D.

  #[local] Abbreviation M1 := (fr_icpt mem S ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)).
  #[local] Abbreviation M3 := (fr_P1 mem S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)).

  (* [comment removed for export] *)
  Lemma fr_P1_outside0 : forall x : word, (U x < U S - 2176)%Z \/ (U S <= U x)%Z -> M3 x = mem x.
  Proof using GS.
    intros x Hx. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1, fr_ia, fr_icpt in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma fr_P1_grows0 : mem_grows mem M3.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1, fr_ia, fr_icpt in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  (* [comment removed for export] *)
  Ltac xfer OUT H := eapply rd_same; [intros x Hx; apply OUT | | exact H].

  Theorem run0_from_6ee44 :
    exists r MU (sz : Z),
      msteps BSEGS (mkst r2 (0x6ee44 : word) (fr_ia M1 S p ra0 (getr R 19)) rom)
                   (mkst r ra0 (fr_b1 MU S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22)) rom)
      /\ getr r 2 = S /\ getr r 8 = getr R 8 /\ getr r 9 = getr R 9 /\ getr r 18 = getr R 18 /\ getr r 19 = getr R 19
      /\ getr r 20 = getr R 20 /\ getr r 21 = getr R 21 /\ getr r 22 = getr R 22 /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ getr r 23 = getr R 23 /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27
      /\ (1 <= sz <= 30)%Z
      /\ (forall x : word, MU x <> M3 x ->
            (U S - 2272 <= U x < U S - 2128)%Z \/ (U S - 2120 <= U x < U S - 1872)%Z \/ (U S - 72 <= U x < U S - 64)%Z \/ U x = (T + 3168)%Z)
      /\ mem_grows M3 MU
      /\ rdn BSEGS MU (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Proof using Hfpc C_bot C_top C_sw C_thr C_tctx C_tsdp C_key C_kif C_P C_pg C_unw_ok C_unw C_inited C_fum C_gcf C_mcs Hstk Gq32 Gbot Gtop GP Gtsdp Gtp Gctx GT Hret Gp0 GS A27 A26 A25 A24 A23 A22 A3 A4 A18 A9 A8 A2 HR4 D q32 tctx bot top P tsdp.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. pose proof (u64_range tp) as Htpr. pose proof (u64_range tsdp) as Htsr.
    pose proof (u64_range P) as HPr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as (GT1 & GT2). destruct GT2 as [GTS GT2]. destruct Gctx as (Gc1 & Gc2 & Gc3).
    assert (Hp0 : U p = 0%Z) by (rewrite Gp0; reflexivity).
    destruct Gtp as (Gtp1 & Gtp2). destruct Gq32 as (Q1 & Q2 & Q3).
    (* [comment removed for export] *)
    assert (OUT1 : forall x : word, (U x < U S - 56 \/ U S <= U x)%Z -> M1 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold fr_icpt in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GR1 : mem_grows mem M1) by ((lazymatch goal with |- ?G => let G' := eval unfold fr_icpt in G in change_no_check G' end); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    Ltac x1 OUT H := eapply rd_same; [intros x Hx; apply OUT; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                    | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H].
    (* [comment removed for export] *)
    destruct (p1_blkB M1 rom S ra0 p (getr R 19) ltac:(hlia) GS2) with (r0 := r2)
      as (r3 & RUN3 & B1 & B2 & B8 & B9 & B18 & B10 & B11 & B12 & B13 & B14 & B15 & B19 & B20 & B21 & B4 & B3 & B22 & B23 & B24 & B25 & B26 & B27);
      [ | x1 OUT1 C_mcs | x1 OUT1 C_gcf | x1 OUT1 C_fum | exact A2 | exact A8 | exact A9 | exact A18 | ].
    { eapply store_ok_mono; [exact GR1|]. eapply (store_ok_sub BSEGS mem (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    set (M3' := fr_p1 M1 S p ra0 (getr R 19)) in RUN3.
    assert (EM3 : M3' = M3) by reflexivity. rewrite EM3 in RUN3. clear EM3 M3'.
    pose proof fr_P1_outside0 as OUT3. pose proof fr_P1_grows0 as GR3.
    assert (SOK3 : store_ok BSEGS M3 (at_ S (-2304)) 2304 = true) by (eapply store_ok_mono; [exact GR3 | exact Hstk]).
    Ltac x3 OUT H := eapply rd_same; [intros x Hx; apply OUT; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                    | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H].
    (* [comment removed for export] *)
    assert (UH : uiH BSEGS both_ui_tab M3 (at_ S (-2128)) (at_ S (-2128)) S thr P).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_g_inited ut_g_pgsz ut_img_lo ut_img_hi both_ui_tab] in G in change_no_check G' end).
      - x3 OUT3 C_inited.
      - x3 OUT3 C_unw.
      - eapply store_ok_mono; [exact GR3 | exact C_unw_ok].
      - x3 OUT3 C_pg.
      - x3 OUT3 C_P.
      - rewrite !at_at. eapply (store_ok_sub BSEGS M3 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact SOK3 | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - rewrite !at_at. eapply (store_ok_sub BSEGS M3 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact SOK3 | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - hlia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. hlia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. hlia. }
    assert (GH : gctH BSEGS (ut_gct both_ui_tab) M3 (at_ (at_ S (-2128)) (-80)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_gct both_ui_tab gt_tsd both_gct_tab] in G in change_no_check G' end).
      - x3 OUT3 C_kif.
      - x3 OUT3 C_key.
      - x3 OUT3 C_tsdp.
      - x3 OUT3 C_tctx.
      - x3 OUT3 C_thr.
      - unorm. lia.
      - rewrite !at_at. eapply (store_ok_sub BSEGS M3 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact SOK3 | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    assert (SH : stkH BSEGS M3 thr top bot).
    { split.
      - x3 OUT3 C_sw.
      - x3 OUT3 C_top.
      - x3 OUT3 C_bot.
      - exact Gbot.
      - unorm. lia. }
    (* [comment removed for export] *)
    assert (B4' : getr r3 4 = tp) by (rewrite B4, A4; exact HR4).
    assert (RET_U : ret_ok (Z_to_bv 64 0x6ef00)) by (apply ret_ok_lit; [lia | reflexivity]).
    assert (Rr : rdn BSEGS M3 (at_ S (-8)) 8 = Some (LE8 ra0)).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1, fr_ia, fr_icpt in G in change_no_check G' end). repeat (wd_rdstep rd8_side). }
    assert (Rw : rdn BSEGS M3 (at_ S (-16)) 8 = Some (LE8 (getr R 8))).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1, fr_ia, fr_icpt in G in change_no_check G' end). repeat (wd_rdstep rd8_side). }
    assert (FPC3 : fpc M3 (bytes_le_to_Z (LE8 (getr R 8))) (U S) D).
    { rewrite bytes_le_to_Z_8. apply (fpc_kept_gen mem _ _ _ Hfpc M3).
      destruct (fpc_shape _ _ _ _ Hfpc) as [ST | FR]; [left; exact ST | right].
      intros a Ha. pose proof (u64_range (getr R 8)). rewrite <- (u_Z2bv a) in Ha by (unfold PTRHI in Ha; lia).
      apply OUT3. lia. }
    destruct (both_ui_run r3 M3 rom (Z_to_bv 64 0x6ef00) (at_ S (-2128)) tp (at_ S (-2128)) (Z_to_bv 64 0x6eea4) S (Z_to_bv 64 1)
                thr top bot tsdp ctxw P RET_U B1 B2 B4' B10 B11 B12 B13 B14 B15 ltac:(wd_ulia) UH GH SH Gtop
                D (LE8 ra0) (LE8 (getr R 8)) Rr (length_N_to_le_bytes _ _) Rw (length_N_to_le_bytes _ _) FPC3)
      as (rU & MU & sz & RUNU & AGU & SZ1 & SZ2 & RDsz & RDpc & RDunw & FOOTU & GRU).
    cbn [ut_rb both_ui_tab] in RUNU. rewrite at0_lit in RUNU by lia.
    replace (488388 : word) with (Z_to_bv 64 488388 : word) in RUN3 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (MUq : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z) \/ (U S <= U x)%Z -> MU x = mem x).
    { intros x Hx. destruct (decide (MU x = M3 x)) as [E|NE].
      - rewrite E. apply OUT3. lia.
      - exfalso. pose proof (FOOTU x NE) as F. revert F. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. intros F. lia. }
    assert (GRU' : mem_grows mem MU) by (eapply mem_grows_trans; [exact GR3 | exact GRU]).
    assert (SOKU : store_ok BSEGS MU (at_ S (-2304)) 2304 = true) by (eapply store_ok_mono; [exact GRU | exact SOK3]).
    Ltac via AG r H := let TT := fresh in pose proof (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold ui_clob, gct_clob in G in change_no_check G' end); notin)) as TT; rewrite H in TT; exact TT.
    (* [comment removed for export] *)
    Ltac rch := repeat (first [ reflexivity | assumption
                              | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).
    Ltac viac AG r := rewrite (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold ui_clob, gct_clob in G in change_no_check G' end); notin)); rch.
    assert (U2 : getr rU 2 = at_ S (-2128)) by via AGU (2:reg) B2.
    assert (U8 : getr rU 8 = S) by via AGU (8:reg) B8.
    assert (U9 : getr rU 9 = p) by via AGU (9:reg) B9.
    assert (U18 : getr rU 18 = Z_to_bv 64 0x6eea4) by via AGU (18:reg) B18.
    assert (U19 : getr rU 19 = Z_to_bv 64 1) by via AGU (19:reg) B19.
    assert (U20 : getr rU 20 = at_ S (-2128)) by via AGU (20:reg) B20.
    assert (U21 : getr rU 21 = at_ S (-81)) by via AGU (21:reg) B21.
    assert (B22' : getr r3 22 = getr R 22) by (rewrite B22; exact A22).
    assert (U22 : getr rU 22 = getr R 22) by via AGU (22:reg) B22'.
    assert (B3' : getr r3 3 = getr R 3) by (rewrite B3; exact A3).
    assert (U3 : getr rU 3 = getr R 3) by via AGU (3:reg) B3'.
    assert (U4 : getr rU 4 = tp) by via AGU (4:reg) B4'.
    assert (B23' : getr r3 23 = getr R 23) by (rewrite B23; exact A23).
    assert (B24' : getr r3 24 = getr R 24) by (rewrite B24; exact A24).
    assert (B25' : getr r3 25 = getr R 25) by (rewrite B25; exact A25).
    assert (B26' : getr r3 26 = getr R 26) by (rewrite B26; exact A26).
    assert (B27' : getr r3 27 = getr R 27) by (rewrite B27; exact A27).
    assert (U23 : getr rU 23 = getr R 23) by via AGU (23:reg) B23'.
    assert (U24 : getr rU 24 = getr R 24) by via AGU (24:reg) B24'.
    assert (U25 : getr rU 25 = getr R 25) by via AGU (25:reg) B25'.
    assert (U26 : getr rU 26 = getr R 26) by via AGU (26:reg) B26'.
    assert (U27 : getr rU 27 = getr R 27) by via AGU (27:reg) B27'.
    (* [comment removed for export] *)
    assert (GSm : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z) by lia.
    assert (ICPT : forall (k : Z) (v : word), (-56 <= k <= -8)%Z ->
              rdn BSEGS M3 (at_ S k) 8 = Some (LE8 v) -> rdn BSEGS MU (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hk Hr. apply (rd_same BSEGS MU M3); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. destruct (decide (MU x = M3 x)) as [E|NE]; [exact E|].
      exfalso. pose proof (FOOTU x NE) as F. revert F. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. intros F. lia. }
    pose proof (ICPT (-8)%Z ra0 ltac:(lia) (fr_P1_i0 mem S p ra0 _ _ _ _ _ _ GSm)) as Ci0.
    pose proof (ICPT (-16)%Z (getr R 8) ltac:(lia) (fr_P1_i1 mem S p ra0 _ _ _ _ _ _ GSm)) as Ci1.
    pose proof (ICPT (-24)%Z (getr R 9) ltac:(lia) (fr_P1_i2 mem S p ra0 _ _ _ _ _ _ GSm)) as Ci2.
    pose proof (ICPT (-32)%Z (getr R 18) ltac:(lia) (fr_P1_i3 mem S p ra0 _ _ _ _ _ _ GSm)) as Ci3.
    pose proof (ICPT (-40)%Z (getr R 19) ltac:(lia) (fr_P1_i4 mem S p ra0 _ _ _ _ _ _ GSm)) as Ci4.
    pose proof (ICPT (-48)%Z (getr R 20) ltac:(lia) (fr_P1_i5 mem S p ra0 _ _ _ _ _ _ GSm)) as Ci5.
    pose proof (ICPT (-56)%Z (getr R 21) ltac:(lia) (fr_P1_i6 mem S p ra0 _ _ _ _ _ _ GSm)) as Ci6.
    (* [comment removed for export] *)
    destruct (z1_run MU rom S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22)
                ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) rU
                U2 U8 U9 U18 U19 U20 U21 U22 Gp0 ltac:(hlia) Hret SOKU Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6)
      as (rZ & RUNZ & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E3 & E4 & E23 & E24 & E25 & E26 & E27).
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x6ef00 : word) with (0x6ef00 : word) in RUNU by (apply bv_eq; reflexivity).
    exists rZ, MU, sz.
    split.
    { eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUNU|]. exact RUNZ. }
    repeat match goal with |- _ /\ _ => split end; try assumption; try rch; try lia.
    intros x Hx. pose proof (FOOTU x Hx) as F. revert F. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. intros F. lia.
  Qed.
End RUN0I.

(* [comment removed for export] *)
Section RUN0.
  Variables (mem rom : word -> option byte) (R : bvmap 5 word).
  Variables (S p ra0 tp tsdp P top bot : word) (T tctx q32 : Z) (D : nat).
  Variables (iab : byte) (pim : list byte).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  (* [comment removed for export] *)
  Hypothesis HR1 : getr R 1 = ra0.
  Hypothesis HR2 : getr R 2 = S.
  Hypothesis HR4 : getr R 4 = tp.
  Hypothesis HR10 : getr R 10 = p.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gp0 : p = Z_to_bv 64 0.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584 /\ (tctx + 4096 <= T \/ T + 4096 <= tctx))%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis GP : (AIMGLO <= U P /\ U P + 8 <= AIMGHI)%Z.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.
  Hypothesis Gbot : (U bot < U top)%Z.
  Hypothesis Gq32 : (U p / 2 ^ 32 = q32 /\ 0 <= q32 < 2 ^ 15 /\ U p / 2 ^ 47 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  (* [comment removed for export] *)
  Hypothesis C_iaflag : rdn BSEGS mem (Z_to_bv 64 0x19dc48) 1 = Some [iab].
  Hypothesis C_iab : U iab <> 0%Z.
  Hypothesis C_pim : rdn BSEGS mem (Z_to_bv 64 (0x10f3c8 + 8 * q32)) 8 = Some pim.
  Hypothesis C_pim0 : bytes_le_to_Z pim = 0%Z.
  Hypothesis C_mcs : rdn BSEGS mem (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30).
  Hypothesis C_gcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_fum : rdn BSEGS mem (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_inited : rdn BSEGS mem (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_unw : rdn BSEGS mem (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_unw_ok : store_ok BSEGS mem (at_ thr 3168) 1 = true.
  Hypothesis C_pg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 P).
  Hypothesis C_P : rdn BSEGS mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_kif : rdn BSEGS mem (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS mem (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS mem (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS mem tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS mem (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_sw : rdn BSEGS mem (at_ thr 40) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_top : rdn BSEGS mem (at_ thr 8) 8 = Some (LE8 top).
  Hypothesis C_bot : rdn BSEGS mem (at_ thr 16) 8 = Some (LE8 bot).
  Hypothesis C_hook : rdn BSEGS mem (Z_to_bv 64 0x19fc88) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_T0 : rdn BSEGS mem (Z_to_bv 64 T) 8 = Some (LE8 ctxw).
  Hypothesis C_tid : rdn BSEGS mem (Z_to_bv 64 (tctx + 8)) 4 = Some (LE4 0).
  (* [comment removed for export] *)
  Hypothesis Hfpc : fpc mem (U (getr R 8)) (U S) D.

  #[local] Abbreviation M3 := (fr_P1 mem S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)).

  Theorem run_p0 :
    exists r MU (sz : Z),
      msteps BSEGS (mkst R (0x6ed6c : word) mem rom)
                   (mkst r ra0 (fr_b1 MU S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22)) rom)
      /\ getr r 2 = S /\ getr r 8 = getr R 8 /\ getr r 9 = getr R 9 /\ getr r 18 = getr R 18 /\ getr r 19 = getr R 19
      /\ getr r 20 = getr R 20 /\ getr r 21 = getr R 21 /\ getr r 22 = getr R 22 /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ getr r 23 = getr R 23 /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27
      /\ (1 <= sz <= 30)%Z
      /\ (forall x : word, MU x <> M3 x ->
            (U S - 2272 <= U x < U S - 2128)%Z \/ (U S - 2120 <= U x < U S - 1872)%Z \/ (U S - 72 <= U x < U S - 64)%Z \/ U x = (T + 3168)%Z)
      /\ mem_grows M3 MU
      /\ rdn BSEGS MU (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Proof using Hfpc C_bot C_top C_sw C_thr C_tctx C_tsdp C_key C_kif C_P C_pg C_unw_ok C_unw C_inited C_fum C_gcf C_mcs C_pim0 C_pim C_iab C_iaflag Hstk Gq32 Gbot Gtop GP Gtsdp Gtp Gctx GT Hret Gp0 GS HR10 HR4 HR2 HR1 pim iab D q32 tctx bot top P tsdp.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    pose proof GS as (GS1 & GS2 & GS3). pose proof Gq32 as (Q1 & Q2 & Q3).
    (* [comment removed for export] *)
    destruct (icpt_pro mem rom S ra0 p R HR1 HR2 HR10 ltac:(lia)) as (r1 & RUN1 & A1 & A2 & A8 & A9 & A18 & A4 & A3 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
    { eapply (store_ok_sub BSEGS mem (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    set (M1 := fr_icpt mem S ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) in RUN1.
    assert (OUT1 : forall x : word, (U x < U S - 56 \/ U S <= U x)%Z -> M1 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1, fr_icpt in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GR1 : mem_grows mem M1) by ((lazymatch goal with |- ?G => let G' := eval unfold M1, fr_icpt in G in change_no_check G' end); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    Ltac x1 OUT H := eapply rd_same; [intros x Hx; apply OUT; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                    | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H].
    (* [comment removed for export] *)
    destruct (p1_blkA M1 rom S ra0 p (getr R 19) r1 iab pim A1 A2 A8 A9 A18 A19 ltac:(lia) GS2) with (q32 := q32)
      as (r2 & RUN2 & B2 & B8 & B9 & B18 & B4 & B3 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27).
    { eapply store_ok_mono; [exact GR1|]. eapply (store_ok_sub BSEGS mem (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { x1 OUT1 C_iaflag. }
    { exact C_iab. }
    { exact Q1. } { exact Q2. } { exact Q3. }
    { x1 OUT1 C_pim. }
    { exact C_pim0. }
    (* [comment removed for export] *)
    assert (B4' : getr r2 4 = getr R 4) by (rewrite B4; exact A4).
    assert (B3' : getr r2 3 = getr R 3) by (rewrite B3; exact A3).
    assert (B20' : getr r2 20 = getr R 20) by (rewrite B20; exact A20).
    assert (B21' : getr r2 21 = getr R 21) by (rewrite B21; exact A21).
    assert (B22' : getr r2 22 = getr R 22) by (rewrite B22; exact A22).
    assert (B23' : getr r2 23 = getr R 23) by (rewrite B23; exact A23).
    assert (B24' : getr r2 24 = getr R 24) by (rewrite B24; exact A24).
    assert (B25' : getr r2 25 = getr R 25) by (rewrite B25; exact A25).
    assert (B26' : getr r2 26 = getr R 26) by (rewrite B26; exact A26).
    assert (B27' : getr r2 27 = getr R 27) by (rewrite B27; exact A27).
    destruct (run0_from_6ee44 mem rom R S p ra0 tp tsdp P top bot T tctx q32 D r2) as (r & MU & sz & RUNT & REST).
    all: try assumption.
    all: let k := numgoals in guard k = 1.
    exists r, MU, sz. split; [| exact REST].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [| exact RUNT]. subst M1. exact RUN2.
  Qed.
End RUN0.
End FPGen.
End BoAllocFRun0.
Require Stdlib.Logic.FunctionalExtensionality OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRunJ.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i.BoAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI.BoAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRun OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem BoAllocFZ BoAllocFRun0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation ZF n := (repeat (Z_to_bv 8 0) (Z.to_nat n)).

(* [comment removed for export] *)
Lemma wbytes_pw : forall bs (m m' : word -> option byte) (a x : word), m x = m' x -> wbytes m a bs x = wbytes m' a bs x.
Proof.
  induction bs as [|b bs IH]; intros m m' a x H; (lazymatch goal with |- ?G => let G' := eval cbn [wbytes] in G in change_no_check G' end); [exact H|].
  apply IH. cbn beta. destruct (bv_eqb x a); [reflexivity | exact H].
Qed.

(* [comment removed for export] *)
Lemma rdn1_in_fill : forall (m : word -> option byte) (a : word) (n i : Z),
  (U a <= i)%Z -> (i < U a + n)%Z -> (U a + n <= 2 ^ 64)%Z ->
  rdn BSEGS (wbytes m a (ZF n)) (Z_to_bv 64 i) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m a n i H1 H2 H3. pose proof (u64_range a). (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end).
  rewrite (wbytes_inside (ZF n) m a (Z_to_bv 64 i)) by (rewrite repeat_length; unorm; rewrite Z2Nat.id by lia; lia).
  rewrite nth_repeat. reflexivity.
Qed.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_init (mem : word -> option byte) (b2 b3 : byte) (pgv : word) (n1 n2 n3 n4 : Z) : word -> option byte :=
  fr_i5 (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 0x19dc48) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3])
    (Z_to_bv 64 0x1903c8) (ZF n1))
    (Z_to_bv 64 0x10f3c0) [Z_to_bv 8 0])
    (Z_to_bv 64 0x10f3c8) (ZF n2))
    (Z_to_bv 64 0x14f400) (ZF n3))
    (Z_to_bv 64 0x150180) (ZF n4)) pgv.

(* [comment removed for export] *)
Definition init_out (x : word) : Prop :=
  ((U x < 0x10f3c0)%Z \/ (0x1903f0 <= U x)%Z) /\ ((U x < 0x19dc48)%Z \/ (0x19dc4c <= U x)%Z).

Section INIT.
  Variables (b2 b3 : byte) (pgv : word) (n1 n2 n3 n4 : Z).
  Hypothesis En1 : n1 = 40%Z.
  Hypothesis En2 : n2 = 262144%Z.
  Hypothesis En3 : n3 = 3456%Z.
  Hypothesis En4 : n4 = 262728%Z.
  #[local] Abbreviation INIT m := (fr_init m b2 b3 pgv n1 n2 n3 n4).

  Lemma fr_init_pw : forall (m m' : word -> option byte) (x : word), m x = m' x -> INIT m x = INIT m' x.
  Proof using. intros m m' x H. (lazymatch goal with |- ?G => let G' := eval unfold fr_init, fr_i5 in G in change_no_check G' end). repeat apply wbytes_pw. exact H. Qed.

  Lemma fr_init_out : forall (m : word -> option byte) (x : word), init_out x -> INIT m x = m x.
  Proof using En4 En3 En2 En1.
    intros m x [X1 X2]. (lazymatch goal with |- ?G => let G' := eval unfold fr_init, fr_i5 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); unorm; try lia.
    reflexivity.
  Qed.

  Lemma fr_init_grows : forall m, mem_grows m (INIT m).
  Proof using. intros m. (lazymatch goal with |- ?G => let G' := eval unfold fr_init, fr_i5 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  Lemma fr_init_some : forall (m : word -> option byte) (x : word), INIT m x <> m x -> INIT m x <> None.
  Proof using.
    intros m x NE. intros N. apply NE. destruct (m x) eqn:E; [|exact N].
    exfalso. pose proof (fr_init_grows m x) as G. rewrite E in G. rewrite N in G. exact (G ltac:(discriminate) eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma init_keeps_rdn : forall (m : word -> option byte) (a : word) (k : nat) bs,
    (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    ((U a + Z.of_nat k <= 0x10f3c0)%Z \/ (0x1903f0 <= U a /\ U a + Z.of_nat k <= 0x19dc48)%Z \/ (0x19dc4c <= U a)%Z) ->
    rdn BSEGS m a k = Some bs -> rdn BSEGS (INIT m) a k = Some bs.
  Proof using En4 En3 En2 En1.
    intros m a k bs Hnw Hout H. eapply rd_same; [| exact Hnw | exact H].
    intros x Hx. apply fr_init_out. (lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end). lia.
  Qed.


  (* [comment removed for export] *)
  Lemma fr_init_comm : forall (F : (word -> option byte) -> (word -> option byte)),
    (forall m m' x, m x = m' x -> F m x = F m' x) ->
    (forall m (x : word), (U x < 2 ^ 24)%Z -> F m x = m x) ->
    forall m, INIT (F m) = F (INIT m).
  Proof using En4 En3 En2 En1.
    intros F Fpw Flow m. apply functional_extensionality. intros x. pose proof (u64_range x).
    destruct (Z_lt_le_dec (U x) (2 ^ 24)) as [LO | HI].
    - rewrite (Flow (INIT m) x LO). apply fr_init_pw. apply Flow. exact LO.
    - rewrite (fr_init_out (F m) x) by ((lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end); lia). symmetry. apply Fpw. apply fr_init_out. (lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end); lia.
  Qed.

  Lemma fr_ia0_init : forall m (S p ra s3 : word), (2 ^ 24 + 2176 <= U S)%Z ->
    fr_ia0 m S p ra s3 b2 b3 pgv n1 n2 n3 n4 = fr_ia (INIT m) S p ra s3.
  Proof using En4 En3 En2 En1.
    intros m S p ra s3 HS. pose proof (u64_range S).
    change (fr_ia0 m S p ra s3 b2 b3 pgv n1 n2 n3 n4) with (INIT (fr_ia m S p ra s3)).
    apply (fr_init_comm (fun m0 => fr_ia m0 S p ra s3)).
    - intros m0 m0' x H0. (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end). repeat apply wbytes_pw. exact H0.
    - intros m0 x Hx. (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia. reflexivity.
  Qed.

  Lemma fr_icpt_init : forall m (S ra s0 s1 s2 s3 s4 s5 : word), (2 ^ 24 + 2176 <= U S)%Z ->
    INIT (fr_icpt m S ra s0 s1 s2 s3 s4 s5) = fr_icpt (INIT m) S ra s0 s1 s2 s3 s4 s5.
  Proof using En4 En3 En2 En1.
    intros m S ra s0 s1 s2 s3 s4 s5 HS. pose proof (u64_range S).
    apply (fr_init_comm (fun m0 => fr_icpt m0 S ra s0 s1 s2 s3 s4 s5)).
    - intros m0 m0' x H0. (lazymatch goal with |- ?G => let G' := eval unfold fr_icpt in G in change_no_check G' end). repeat apply wbytes_pw. exact H0.
    - intros m0 x Hx. (lazymatch goal with |- ?G => let G' := eval unfold fr_icpt in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fr_init_flag : forall m, rdn BSEGS (INIT m) (Z_to_bv 64 0x19dc48) 1 = Some [Z_to_bv 8 1].
  Proof using.
    intros m. (lazymatch goal with |- ?G => let G' := eval unfold fr_init, fr_i5 in G in change_no_check G' end). rewrite rdn_wbytes_out; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia].
    lazymatch goal with |- rdn _ ?M ?a 1%nat = _ =>
      replace (rdn BSEGS M a 1) with (rdn BSEGS M (at_ a (Z.of_nat 0)) 1) by (f_equal; apply bv_eq; rewrite at_u; wd_ulia) end.
    apply rdn1_wbytes_in; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia].
  Qed.
  Lemma fr_init_lock : forall m, rdn BSEGS (INIT m) (Z_to_bv 64 0x19dc49) 1 = Some [Z_to_bv 8 0].
  Proof using.
    intros m. (lazymatch goal with |- ?G => let G' := eval unfold fr_init, fr_i5 in G in change_no_check G' end).
    lazymatch goal with |- rdn _ ?M ?a 1%nat = _ =>
      replace (rdn BSEGS M a 1) with (rdn BSEGS M (at_ a (Z.of_nat 0)) 1) by (f_equal; apply bv_eq; rewrite at_u; wd_ulia) end.
    apply rdn1_wbytes_in; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia].
  Qed.
  Lemma fr_init_pgcell : forall m, rdn BSEGS (INIT m) (Z_to_bv 64 0x150180) 8 = Some (LE8 pgv).
  Proof using. intros m. (lazymatch goal with |- ?G => let G' := eval unfold fr_init, fr_i5 in G in change_no_check G' end). repeat (wd_rdstep rd8_side). Qed.
  Lemma fr_init_chunks : forall m, rdn BSEGS (INIT m) (Z_to_bv 64 0x150188) 8 = Some (LE8 (Z_to_bv 64 0x150190)).
  Proof using. intros m. (lazymatch goal with |- ?G => let G' := eval unfold fr_init, fr_i5 in G in change_no_check G' end). repeat (wd_rdstep rd8_side). Qed.
  Lemma fr_init_map1 : forall m (i : Z), (0x10f3c8 <= i < 0x10f3c8 + 0x40000)%Z ->
    rdn BSEGS (INIT m) (Z_to_bv 64 i) 1 = Some [Z_to_bv 8 0].
  Proof using En4 En3 En2.
    intros m i Hi. (lazymatch goal with |- ?G => let G' := eval unfold fr_init, fr_i5 in G in change_no_check G' end).
    do 6 (rewrite rdn_wbytes_out; [| rd8_side | rd8_side | rd8_side ]).
    apply rdn1_in_fill; wd_ulia.
  Qed.
End INIT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RUN12I.
  Variables (mem rom : word -> option byte) (R : bvmap 5 word).
  Variables (S p ra0 tp tsdp P top bot : word) (T tctx n q32 : Z) (D : nat).
  Variables (h1 h2 h3 : byte) (hv : word) (bf0 bf1 : list byte).
  Variables (b2 b3 : byte) (n1 n2 n3 n4 : Z).
  Hypothesis En1 : n1 = 40%Z.
  Hypothesis En2 : n2 = 262144%Z.
  Hypothesis En3 : n3 = 3456%Z.
  Hypothesis En4 : n4 = 262728%Z.
  #[local] Abbreviation f0 := (Z_to_bv 64 (bytes_le_to_Z bf0)).
  #[local] Abbreviation f1 := (Z_to_bv 64 (bytes_le_to_Z bf1)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  (* [comment removed for export] *)
  #[local] Abbreviation MI := (fr_init mem b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4).
  (* [comment removed for export] *)
  Hypothesis HR1 : getr R 1 = ra0.
  Hypothesis HR2 : getr R 2 = S.
  Hypothesis HR4 : getr R 4 = tp.
  Hypothesis HR10 : getr R 10 = p.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gp : (AIMGHI + 16 <= U p /\ U p + 8 <= U S - 3584 /\ U p mod 16 = 0)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis GpT : (U p + 8 <= T \/ T + 4096 <= U p - 16)%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584 /\ (tctx + 4096 <= T \/ T + 4096 <= tctx) /\ (tctx + 4096 <= U p - 16 \/ U p + 8 <= tctx))%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis GP : (AIMGLO <= U P /\ U P + 8 <= AIMGHI)%Z.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.
  Hypothesis Gbot : (U bot < U top)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 40)%Z.
  Hypothesis Gq32 : (U p / 2 ^ 32 = q32 /\ 0 <= q32 < 2 ^ 15 /\ U p / 2 ^ 47 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  (* [comment removed for export] *)
  Hypothesis C_flagw : rdn BSEGS mem (Z_to_bv 64 0x19dc48) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3].
  Hypothesis C_pg0 : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 P).
  Hypothesis C_P0 : rdn BSEGS mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis GPI : ((U P + 8 <= 0x10f3c0 \/ 0x10f3c0 + 0x81030 <= U P) /\ (U P + 8 <= 0x19dc48 \/ 0x19dc4c <= U P))%Z.
  (* [comment removed for export] *)
  Hypothesis C_mcs : rdn BSEGS MI (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30).
  Hypothesis C_gcf : rdn BSEGS MI (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_fum : rdn BSEGS MI (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_inited : rdn BSEGS MI (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_unw : rdn BSEGS MI (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_unw_ok : store_ok BSEGS mem (at_ thr 3168) 1 = true.
  Hypothesis C_pg : rdn BSEGS MI (Z_to_bv 64 0x105ef8) 8 = Some (LE8 P).
  Hypothesis C_P : rdn BSEGS MI P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_kif : rdn BSEGS MI (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS MI (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS MI (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS MI tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS MI (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_sw : rdn BSEGS MI (at_ thr 40) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_top : rdn BSEGS MI (at_ thr 8) 8 = Some (LE8 top).
  Hypothesis C_bot : rdn BSEGS MI (at_ thr 16) 8 = Some (LE8 bot).
  Hypothesis C_hook : rdn BSEGS MI (Z_to_bv 64 0x19fc88) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_h1 : h1 = Z_to_bv 8 0x11 \/ h1 = Z_to_bv 8 0x91.
  Hypothesis C_hdr : rdn BSEGS MI (at_ p (-16)) 4 = Some [Z_to_bv 8 2; h1; h2; h3].
  Hypothesis C_hv : bytes_le_to_Z [Z_to_bv 8 2; h1; h2; h3] = U hv.
  Hypothesis C_hdr_ok : store_ok BSEGS mem (at_ p (-16)) 4 = true.
  Hypothesis C_p_ok : store_ok BSEGS mem p 8 = true.
  Hypothesis C_nhi : rdn BSEGS MI (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn BSEGS MI (at_ p (-12)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_f0 : rdn BSEGS MI (Z_to_bv 64 (T + 2824)) 8 = Some bf0.
  Hypothesis L_f0 : length bf0 = 8%nat.
  Hypothesis C_f1 : rdn BSEGS MI (Z_to_bv 64 (T + 2832)) 8 = Some bf1.
  Hypothesis L_f1 : length bf1 = 8%nat.
  Hypothesis C_stat_ok : store_ok BSEGS mem (Z_to_bv 64 (T + 2824)) 16 = true.
  Hypothesis C_T0 : rdn BSEGS MI (Z_to_bv 64 T) 8 = Some (LE8 ctxw).
  Hypothesis C_tid : rdn BSEGS MI (Z_to_bv 64 (tctx + 8)) 4 = Some (LE4 0).
  (* [comment removed for export] *)
  Hypothesis Hfpc : fpc mem (U (getr R 8)) (U S) D.

  #[local] Abbreviation M3 := (fr_P1 MI S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)).

  Theorem run_p12_0 :
    exists r MU (sz : Z) (bsz : list byte),
      msteps BSEGS (mkst R (0x6ed6c : word) mem rom) (mkst r (0x8f4f0 : word) (fr_P2 MU S p (getr R 22) T n h1 h2 h3 bf0 bf1) rom)
      /\ getr r 1 = Z_to_bv 64 0x50838 /\ getr r 2 = at_ S (-2176) /\ getr r 8 = at_ p (-16) /\ getr r 9 = at_ S (-2128)
      /\ getr r 10 = at_ S (-2112) /\ getr r 11 = Z_to_bv 64 (bytes_le_to_Z bsz) /\ getr r 18 = Z_to_bv 64 0x10ab58
      /\ getr r 19 = Z_to_bv 64 0 /\ getr r 20 = thr /\ getr r 21 = at_ S (-81) /\ getr r 22 = getr R 22
      /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ getr r 23 = getr R 23 /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27
      /\ (1 <= sz <= 30)%Z /\ (sz <= 2 + Z.of_nat D)%Z
      /\ (forall x : word, MU x <> M3 x ->
            (U S - 2272 <= U x < U S - 2128)%Z \/ (U S - 2120 <= U x < U S - 1872)%Z \/ (U S - 72 <= U x < U S - 64)%Z \/ U x = (T + 3168)%Z)
      /\ mem_grows M3 MU
      /\ rdn BSEGS MU (at_ S (-2120)) 4 = Some (LE4 sz) /\ rdn BSEGS MU (at_ S (-2112)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4))
      /\ rdn BSEGS MU (at_ thr 3168) 1 = Some [Z_to_bv 8 0]
      /\ rdn BSEGS MU (at_ S (-2120)) 8 = Some bsz /\ length bsz = 8%nat
      /\ rdn BSEGS MU (at_ S (-2116)) 4 = Some (LE4 0).                                  (* [comment removed for export] *)
  Proof using Hfpc C_tid C_T0 C_stat_ok L_f1 C_f1 L_f0 C_f0 C_nlo C_nhi C_p_ok C_hdr_ok C_hv C_hdr C_h1 C_hook C_bot C_top C_sw C_thr C_tctx C_tsdp C_key C_kif C_P C_pg C_unw_ok C_unw C_inited C_fum C_gcf C_mcs GPI C_P0 C_pg0 C_flagw Hstk Gq32 Gn Gbot Gtop GP Gtsdp Gtp Gctx GpT GT Gp GS HR10 HR4 HR2 HR1 En4 En3 En2 En1 hv q32 tctx bot top P tsdp.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. pose proof (u64_range P) as HPr.
    pose proof GS as (GS1 & GS2 & GS3). pose proof Gp as (Gp1 & Gp2 & Gp3). pose proof Gq32 as (Q1 & Q2 & Q3). pose proof GP as [GP1 GP2]. pose proof GPI as [GPI1 GPI2].
    (* [comment removed for export] *)
    destruct (icpt_pro mem rom S ra0 p R HR1 HR2 HR10 ltac:(lia)) as (r1 & RUN1 & A1 & A2 & A8 & A9 & A18 & A4 & A3 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
    { eapply (store_ok_sub BSEGS mem (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    set (M1 := fr_icpt mem S ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) in RUN1.
    assert (OUT1 : forall x : word, (U x < U S - 56 \/ U S <= U x)%Z -> M1 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1, fr_icpt in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GR1 : mem_grows mem M1) by ((lazymatch goal with |- ?G => let G' := eval unfold M1, fr_icpt in G in change_no_check G' end); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    Ltac x1 OUT H := eapply rd_same; [intros x Hx; apply OUT; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                    | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H].
    (* [comment removed for export] *)
    pose proof (bytes_le_to_Z_bound [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3]) as Bvw. cbn [length] in Bvw.
    pose proof (bytes_le_to_Z_nonneg [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3]) as Bvw0.
    assert (Hvw : bytes_le_to_Z [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3] = U (Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3]))) by (unorm; reflexivity).
    assert (C_flag1 : rdn BSEGS mem (Z_to_bv 64 0x19dc48) 1 = Some [Z_to_bv 8 0]).
    { pose proof (rdn_firstn BSEGS mem 4 _ _ 1 C_flagw ltac:(lia)) as F1. exact F1. }
    assert (EP : Z_to_bv 64 (U P) = P) by (apply Z_to_bv_bv_unsigned).
    destruct (p1_blkA0 M1 rom S ra0 p (getr R 19) r1 b2 b3 (Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3])) (U P) (Z_to_bv 64 4096) n1 n2 n3 n4 q32
                En1 En2 En3 En4 A1 A2 A8 A9 A18 A19 ltac:(lia))
      as (r2 & RUN2 & B2 & B8 & B9 & B18 & B4 & B3 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27).
    { eapply store_ok_mono; [exact GR1|]. eapply (store_ok_sub BSEGS mem (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { x1 OUT1 C_flag1. }
    { x1 OUT1 C_flagw. }
    { exact Hvw. }
    { rewrite EP. x1 OUT1 C_pg0. }
    { lia. }
    { rewrite EP. x1 OUT1 C_P0. }
    { change (U (Z_to_bv 64 4096)) with 4096%Z. lia. }
    { exact Q1. } { exact Q2. } { exact Q3. }
    (* [comment removed for export] *)
    rewrite (fr_ia0_init b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 En1 En2 En3 En4 M1 S p ra0 (getr R 19)) in RUN2 by lia.
    subst M1. rewrite (fr_icpt_init b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 En1 En2 En3 En4 mem S ra0) in RUN2 by lia.
    (* [comment removed for export] *)
    assert (B4' : getr r2 4 = getr R 4) by (rewrite B4; exact A4).
    assert (B3' : getr r2 3 = getr R 3) by (rewrite B3; exact A3).
    assert (B20' : getr r2 20 = getr R 20) by (rewrite B20; exact A20).
    assert (B21' : getr r2 21 = getr R 21) by (rewrite B21; exact A21).
    assert (B22' : getr r2 22 = getr R 22) by (rewrite B22; exact A22).
    assert (B23' : getr r2 23 = getr R 23) by (rewrite B23; exact A23).
    assert (B24' : getr r2 24 = getr R 24) by (rewrite B24; exact A24).
    assert (B25' : getr r2 25 = getr R 25) by (rewrite B25; exact A25).
    assert (B26' : getr r2 26 = getr R 26) by (rewrite B26; exact A26).
    assert (B27' : getr r2 27 = getr R 27) by (rewrite B27; exact A27).
    pose proof (fr_init_grows b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 mem) as GRI.
    assert (HstkI : store_ok BSEGS MI (at_ S (-2304)) 2304 = true) by (eapply store_ok_mono; [exact GRI | exact Hstk]).
    assert (C_unw_okI : store_ok BSEGS MI (at_ thr 3168) 1 = true) by (eapply store_ok_mono; [exact GRI | exact C_unw_ok]).
    assert (C_hdr_okI : store_ok BSEGS MI (at_ p (-16)) 4 = true) by (eapply store_ok_mono; [exact GRI | exact C_hdr_ok]).
    assert (C_p_okI : store_ok BSEGS MI p 8 = true) by (eapply store_ok_mono; [exact GRI | exact C_p_ok]).
    assert (C_stat_okI : store_ok BSEGS MI (Z_to_bv 64 (T + 2824)) 16 = true) by (eapply store_ok_mono; [exact GRI | exact C_stat_ok]).
    assert (HfpcI : fpc MI (U (getr R 8)) (U S) D).
    { apply (fpc_kept_gen mem _ _ _ Hfpc MI). destruct (fpc_shape _ _ _ _ Hfpc) as [ST | FR]; [left; exact ST | right].
      intros a Ha. pose proof (u64_range (getr R 8)). apply (fr_init_out b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 En1 En2 En3 En4). unfold init_out, PTRHI in *. unorm. lia. }
    destruct (run_from_6ee44 MI rom R S p ra0 tp tsdp P top bot T tctx n q32 D h1 h2 h3 hv bf0 bf1 r2)
      as (r & MU & sz & bsz & RUNT & REST).
    all: try assumption.
    all: let k := numgoals in guard k = 1.
    exists r, MU, sz, bsz. split; [| exact REST].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [| exact RUNT]. exact RUN2.
  Qed.
End RUN12I.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RUN0J.
  Variables (mem rom : word -> option byte) (R : bvmap 5 word).
  Variables (S p ra0 tp tsdp P top bot : word) (T tctx q32 : Z) (D : nat).
  Variables (b2 b3 : byte) (n1 n2 n3 n4 : Z).
  Hypothesis En1 : n1 = 40%Z.
  Hypothesis En2 : n2 = 262144%Z.
  Hypothesis En3 : n3 = 3456%Z.
  Hypothesis En4 : n4 = 262728%Z.
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  #[local] Abbreviation MI := (fr_init mem b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4).
  Hypothesis HR1 : getr R 1 = ra0.
  Hypothesis HR2 : getr R 2 = S.
  Hypothesis HR4 : getr R 4 = tp.
  Hypothesis HR10 : getr R 10 = p.
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gp0 : p = Z_to_bv 64 0.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584 /\ (tctx + 4096 <= T \/ T + 4096 <= tctx))%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis GP : (AIMGLO <= U P /\ U P + 8 <= AIMGHI)%Z.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.
  Hypothesis Gbot : (U bot < U top)%Z.
  Hypothesis Gq32 : (U p / 2 ^ 32 = q32 /\ 0 <= q32 < 2 ^ 15 /\ U p / 2 ^ 47 = 0)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  Hypothesis C_flagw : rdn BSEGS mem (Z_to_bv 64 0x19dc48) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3].
  Hypothesis C_pg0 : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 P).
  Hypothesis C_P0 : rdn BSEGS mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis GPI : ((U P + 8 <= 0x10f3c0 \/ 0x10f3c0 + 0x81030 <= U P) /\ (U P + 8 <= 0x19dc48 \/ 0x19dc4c <= U P))%Z.
  Hypothesis C_mcs : rdn BSEGS MI (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30).
  Hypothesis C_gcf : rdn BSEGS MI (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_fum : rdn BSEGS MI (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_inited : rdn BSEGS MI (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_unw : rdn BSEGS MI (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_unw_ok : store_ok BSEGS mem (at_ thr 3168) 1 = true.
  Hypothesis C_pg : rdn BSEGS MI (Z_to_bv 64 0x105ef8) 8 = Some (LE8 P).
  Hypothesis C_P : rdn BSEGS MI P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_kif : rdn BSEGS MI (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS MI (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS MI (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS MI tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS MI (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_sw : rdn BSEGS MI (at_ thr 40) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_top : rdn BSEGS MI (at_ thr 8) 8 = Some (LE8 top).
  Hypothesis C_bot : rdn BSEGS MI (at_ thr 16) 8 = Some (LE8 bot).
  Hypothesis C_hook : rdn BSEGS MI (Z_to_bv 64 0x19fc88) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_T0 : rdn BSEGS MI (Z_to_bv 64 T) 8 = Some (LE8 ctxw).
  Hypothesis C_tid : rdn BSEGS MI (Z_to_bv 64 (tctx + 8)) 4 = Some (LE4 0).
  Hypothesis Hfpc : fpc mem (U (getr R 8)) (U S) D.

  #[local] Abbreviation M3 := (fr_P1 MI S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)).

  Theorem run_p0_0 :
    exists r MU (sz : Z),
      msteps BSEGS (mkst R (0x6ed6c : word) mem rom)
                   (mkst r ra0 (fr_b1 MU S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22)) rom)
      /\ getr r 2 = S /\ getr r 8 = getr R 8 /\ getr r 9 = getr R 9 /\ getr r 18 = getr R 18 /\ getr r 19 = getr R 19
      /\ getr r 20 = getr R 20 /\ getr r 21 = getr R 21 /\ getr r 22 = getr R 22 /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ getr r 23 = getr R 23 /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27
      /\ (1 <= sz <= 30)%Z
      /\ (forall x : word, MU x <> M3 x ->
            (U S - 2272 <= U x < U S - 2128)%Z \/ (U S - 2120 <= U x < U S - 1872)%Z \/ (U S - 72 <= U x < U S - 64)%Z \/ U x = (T + 3168)%Z)
      /\ mem_grows M3 MU
      /\ rdn BSEGS MU (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Proof using Hfpc C_bot C_top C_sw C_thr C_tctx C_tsdp C_key C_kif C_P C_pg C_unw_ok C_unw C_inited C_fum C_gcf C_mcs GPI C_P0 C_pg0 C_flagw Hstk Gq32 Gbot Gtop GP Gtsdp Gtp Gctx GT Hret Gp0 GS HR10 HR4 HR2 HR1 En4 En3 En2 En1 D q32 tctx bot top P tsdp.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. pose proof (u64_range P) as HPr.
    pose proof GS as (GS1 & GS2 & GS3). pose proof Gq32 as (Q1 & Q2 & Q3). pose proof GP as [GP1 GP2]. pose proof GPI as [GPI1 GPI2].
    assert (Hp0 : U p = 0%Z) by (rewrite Gp0; reflexivity).
    (* [comment removed for export] *)
    destruct (icpt_pro mem rom S ra0 p R HR1 HR2 HR10 ltac:(lia)) as (r1 & RUN1 & A1 & A2 & A8 & A9 & A18 & A4 & A3 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
    { eapply (store_ok_sub BSEGS mem (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    set (M1 := fr_icpt mem S ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) in RUN1.
    assert (OUT1 : forall x : word, (U x < U S - 56 \/ U S <= U x)%Z -> M1 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1, fr_icpt in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GR1 : mem_grows mem M1) by ((lazymatch goal with |- ?G => let G' := eval unfold M1, fr_icpt in G in change_no_check G' end); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    Ltac x1' OUT H := eapply rd_same; [intros x Hx; apply OUT; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                     | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H].
    (* [comment removed for export] *)
    pose proof (bytes_le_to_Z_bound [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3]) as Bvw. cbn [length] in Bvw.
    pose proof (bytes_le_to_Z_nonneg [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3]) as Bvw0.
    assert (Hvw : bytes_le_to_Z [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3] = U (Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3]))) by (unorm; reflexivity).
    assert (C_flag1 : rdn BSEGS mem (Z_to_bv 64 0x19dc48) 1 = Some [Z_to_bv 8 0]).
    { pose proof (rdn_firstn BSEGS mem 4 _ _ 1 C_flagw ltac:(lia)) as F1. exact F1. }
    assert (EP : Z_to_bv 64 (U P) = P) by (apply Z_to_bv_bv_unsigned).
    destruct (p1_blkA0 M1 rom S ra0 p (getr R 19) r1 b2 b3 (Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3])) (U P) (Z_to_bv 64 4096) n1 n2 n3 n4 q32
                En1 En2 En3 En4 A1 A2 A8 A9 A18 A19 ltac:(lia))
      as (r2 & RUN2 & B2 & B8 & B9 & B18 & B4 & B3 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27).
    { eapply store_ok_mono; [exact GR1|]. eapply (store_ok_sub BSEGS mem (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { x1' OUT1 C_flag1. }
    { x1' OUT1 C_flagw. }
    { exact Hvw. }
    { rewrite EP. x1' OUT1 C_pg0. }
    { lia. }
    { rewrite EP. x1' OUT1 C_P0. }
    { change (U (Z_to_bv 64 4096)) with 4096%Z. lia. }
    { exact Q1. } { exact Q2. } { exact Q3. }
    rewrite (fr_ia0_init b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 En1 En2 En3 En4 M1 S p ra0 (getr R 19)) in RUN2 by lia.
    subst M1. rewrite (fr_icpt_init b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 En1 En2 En3 En4 mem S ra0) in RUN2 by lia.
    (* [comment removed for export] *)
    assert (B4' : getr r2 4 = getr R 4) by (rewrite B4; exact A4).
    assert (B3' : getr r2 3 = getr R 3) by (rewrite B3; exact A3).
    assert (B20' : getr r2 20 = getr R 20) by (rewrite B20; exact A20).
    assert (B21' : getr r2 21 = getr R 21) by (rewrite B21; exact A21).
    assert (B22' : getr r2 22 = getr R 22) by (rewrite B22; exact A22).
    assert (B23' : getr r2 23 = getr R 23) by (rewrite B23; exact A23).
    assert (B24' : getr r2 24 = getr R 24) by (rewrite B24; exact A24).
    assert (B25' : getr r2 25 = getr R 25) by (rewrite B25; exact A25).
    assert (B26' : getr r2 26 = getr R 26) by (rewrite B26; exact A26).
    assert (B27' : getr r2 27 = getr R 27) by (rewrite B27; exact A27).
    pose proof (fr_init_grows b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 mem) as GRI.
    assert (HstkI : store_ok BSEGS MI (at_ S (-2304)) 2304 = true) by (eapply store_ok_mono; [exact GRI | exact Hstk]).
    assert (C_unw_okI : store_ok BSEGS MI (at_ thr 3168) 1 = true) by (eapply store_ok_mono; [exact GRI | exact C_unw_ok]).
    assert (HfpcI : fpc MI (U (getr R 8)) (U S) D).
    { apply (fpc_kept_gen mem _ _ _ Hfpc MI). destruct (fpc_shape _ _ _ _ Hfpc) as [ST | FR]; [left; exact ST | right].
      intros a Ha. pose proof (u64_range (getr R 8)). apply (fr_init_out b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 En1 En2 En3 En4). unfold init_out, PTRHI in *. unorm. lia. }
    destruct (run0_from_6ee44 MI rom R S p ra0 tp tsdp P top bot T tctx q32 D r2) as (r & MU & sz & RUNT & REST).
    all: try assumption.
    all: let k := numgoals in guard k = 1.
    exists r, MU, sz. split; [| exact REST].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [| exact RUNT]. exact RUN2.
  Qed.
End RUN0J.
End FPGen.
End BoAllocFRunJ.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFHypI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i.BoAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i BoAllocFRunJ OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma ivl_disj : forall x k lo hi,
  (forall a, x <= a < x + k -> ~ (lo <= a < hi)) -> 0 < k -> lo < hi -> x + k <= lo \/ hi <= x.
Proof.
  intros x k lo hi F Hk Hlh.
  destruct (Z_lt_le_dec lo (x + k)) as [A|A]; [| left; lia].
  destruct (Z_lt_le_dec x hi) as [B|B]; [| right; lia].
  exfalso. destruct (Z_lt_le_dec x lo) as [C|C].
  - apply (F lo); lia.
  - apply (F x); lia.
Qed.

(* [comment removed for export] *)
Lemma rom_19dc8a : seg_rom BSEGS (Z_to_bv 64 0x19dc4a) = Some (Z_to_bv 8 0).
Proof. vm_compute. reflexivity. Qed.
Lemma rom_19dc8b : seg_rom BSEGS (Z_to_bv 64 0x19dc4b) = Some (Z_to_bv 8 0).
Proof. vm_compute. reflexivity. Qed.
Lemma rdn2_junk_ex : forall (M : word -> option byte), exists b2 b3, rdn BSEGS M (Z_to_bv 64 0x19dc4a) 2 = Some [b2; b3].
Proof.
  intros M. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end).
  replace (Z_to_bv 64 0x19dc4a + 1)%bv with (Z_to_bv 64 0x19dc4b : word) by (apply bv_eq; reflexivity).
  destruct (M (Z_to_bv 64 0x19dc4a)) as [b2|]; [| rewrite rom_19dc8a];
    (destruct (M (Z_to_bv 64 0x19dc4b)) as [b3|]; [| rewrite rom_19dc8b]); eexists _, _; reflexivity.
Qed.

Section FPGen.
Context {fx : FPState}.


End FPGen.

Section HYPI.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  (* [comment removed for export] *)
  Definition foot_ialloc4 (a : Z) : Prop :=
    (IA_FLAG bt <= a < IA_FLAG bt + 4) \/ (IA_INST bt <= a < IA_INST bt + IASZ) \/ CEIL <= a.
  Definition OPS_REP_ialloc_init4_stmt : Prop := forall st Lc FF M M' mdl,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> a_ialloc st = false ->
    agrees_off foot_ialloc4 M M' ->
    byteZ (bt_segs bt) M' (IA_FLAG bt) 1 -> byteZ (bt_segs bt) M' (IA_FLAG bt + 1) 0 ->
    fillZ (bt_segs bt) M' (IA_INST bt + 8) (IA_INST bt + 8 + 0x40000) 0 ->
    cellZ (bt_segs bt) M' (IA_INST bt + 0x40dc0) 8 PG -> cellZ (bt_segs bt) M' (IA_INST bt + 0x40dc8) 8 (IA_INST bt + 0x40dd0) ->
    Rep bt (op_ialloc_init st) Lc FF M' mdl.

End HYPI.
End BoAllocFHypI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFXTrk.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvXTrk3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeil.
Context {RC : run_ceil}.

Lemma live_hdr_xtracked : forall bt st Lc FF p n a, WF bt st Lc FF -> In (p, n) Lc -> p - 16 <= a < p + 8 -> xtracked bt st a.
Proof using.
  intros bt st Lc FF p n a W Hin Ha.
  destruct (live_range bt st Lc FF W p n Hin) as (_ & _ & (N1 & _) & _).
  destruct (is_primary n) eqn:HP.
  - pose proof (prim_block_in_space bt st Lc FF p n W Hin HP) as [B1 B2]. pose proof (rz_range n) as RZ.
    apply (xtracked_space bt st Lc FF _ _ W). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - B1 B2 RZ N1 Ha. lia.
  - destruct (live_sec bt st Lc FF W p n Hin HP) as (sc & Hs & Eu & En).
    destruct (sec_facts bt st Lc FF W sc Hs) as (_ & _ & _ & _ & A5 & A6 & A7 & _).
    apply (xtracked_sec bt st Lc FF _ _ W sc a Hs). unfold PG in A5. clear - A5 A6 A7 Eu En Ha. lia.
Qed.

Lemma xd_xtracked : forall bt st Lc FF S p n a, WF bt st Lc FF -> In (p, n) Lc -> CEIL <= S - 2304 ->
  Xd S p (bt_thread bt) a -> xtracked bt st a.
Proof using.
  intros bt st Lc FF S p n a W Hin HS [Ha | [Ha | [Ha | Ha]]].
  - apply (live_hdr_xtracked bt st Lc FF p n a W Hin). clear - Ha. lia.
  - apply (live_hdr_xtracked bt st Lc FF p n a W Hin). clear - Ha. lia.
  - apply (xtracked_thread bt st Lc FF _ _ W). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - Ha. lia.
  - apply xtracked_stack. clear - Ha HS. lia.
Qed.
End WithCeil.
End BoAllocFXTrk.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFTopA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvXTrk3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b BoAllocFXTrk.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i.BoAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI.BoAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRun OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N.BoAllocFRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wf_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wf_clear_disj_or A | wf_clear_disj_or B] | ?A <-> ?B => first [wf_clear_disj_or A | wf_clear_disj_or B] | ?A -> ?B => first [wf_clear_disj_or A | wf_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wf_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wf_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wf_clear_disj; wf_lia0] | wf_lia0 ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
(* [comment removed for export] *)
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Lemma restrict_mkstF : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Ltac feed H :=
  lazymatch type of H with
  | ?A -> ?B =>
      lazymatch type of A with
      | Prop => let HA := fresh "HA" in
                assert (HA : A) by (first [assumption | hlia | lia]); specialize (H HA); clear HA; feed H
      | _ => idtac
      end
  | _ => idtac
  end.

Section TOPA.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HYP_DEPOT : HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).

  (* [comment removed for export] *)
  Definition runA_st (st : ast) (d' : depot) (naa : list (Z * Z)) : ast :=
    AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (a_sec st) (a_nres st) d' (a_hint st) (a_ialloc st)
        (a_aa st ++ naa) (a_kact st + EVT) (a_shsec st).

  (* [comment removed for export] *)
  Definition runA_post (st : ast) (Lc FF : list (Z * Z)) (R : bvmap 5 word) (M : mem) (mdl : Model) (p : word) (c' : config) : Prop :=
    exists fx' (R' : bvmap 5 word) (M' M0 : mem) (mdl' : Model) (d' : depot) (naa : list (Z * Z)) (id : Z),
      let S := getr R 2 in
      let st' := runA_st st d' naa in
      c' = mkCfg (@mkst fx' R' (Z_to_bv 64 0x50838) M' (seg_rom BSEGS)) mdl'
      /\ FXOK fx' /\ m_halted mdl' = None
      /\ WF bt st' Lc FF /\ Rep bt st' Lc FF M0 mdl'
      /\ (forall a : word, M' a <> M0 a -> Xd (U S) (U p) T (U a) /\ M' a <> None)
      /\ (forall a : word, M' a <> M a ->
            (Xd (U S) (U p) T (U a) \/ (U S - 2176 - KD <= U a < U S - 2176)
             \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a))
            /\ M' a <> None)
      /\ M' (at_ p (-16)) = Some (Z_to_bv 8 3)
      /\ rdn BSEGS M' (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)) /\ rdn BSEGS M' (at_ S (-2144)) 8 = Some (LE8 S)
      /\ rdn BSEGS M' (at_ S (-2152)) 8 = Some (LE8 p) /\ rdn BSEGS M' (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4))
      /\ rdn BSEGS M' (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)) /\ rdn BSEGS M' (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128)))
      /\ rdn BSEGS M' (at_ S (-8)) 8 = Some (LE8 (getr R 1)) /\ rdn BSEGS M' (at_ S (-16)) 8 = Some (LE8 (getr R 8))
      /\ rdn BSEGS M' (at_ S (-24)) 8 = Some (LE8 (getr R 9)) /\ rdn BSEGS M' (at_ S (-32)) 8 = Some (LE8 (getr R 18))
      /\ rdn BSEGS M' (at_ S (-40)) 8 = Some (LE8 (getr R 19)) /\ rdn BSEGS M' (at_ S (-48)) 8 = Some (LE8 (getr R 20))
      /\ rdn BSEGS M' (at_ S (-56)) 8 = Some (LE8 (getr R 21))
      /\ getr R' 2 = at_ S (-2176) /\ getr R' 8 = at_ p (-16) /\ getr R' 9 = at_ S (-2128) /\ getr R' 10 = Z_to_bv 64 id
      /\ getr R' 18 = Z_to_bv 64 (IB bt) /\ getr R' 19 = Z_to_bv 64 0 /\ getr R' 20 = Z_to_bv 64 T /\ getr R' 21 = at_ S (-81)
      /\ getr R' 22 = getr R 22 /\ getr R' 3 = getr R 3 /\ getr R' 4 = getr R 4
      /\ getr R' 23 = getr R 23 /\ getr R' 24 = getr R 24 /\ getr R' 25 = getr R 25 /\ getr R' 26 = getr R 26 /\ getr R' 27 = getr R 27
      /\ 0 <= id < 2 ^ 32
      /\ same_except_vm mdl mdl'
      /\ lazy_kept (bt_ia bt) Lc FF mdl mdl'
      /\ BackingAlgebra.model_ivs_wf mdl'.                                          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition free_runA_stmt : Prop :=
    forall fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp m : Z) (p : word) (st : ast),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> getr R 10 = p -> fpc M (U (getr R 8)) sp DMAX ->
      In (U p, m) Lc -> K + kcost_free <= KCAP -> (exists h : option Z, holes_le h st) ->     (* [comment removed for export] *)
      a_ialloc st = true ->
      katD BSEGS (cfg BSEGS fx R (ia_free both_addrs) M mdl) (runA_post st Lc FF R M mdl p).

  Theorem free_runA : free_runA_stmt.
  Proof using HTP HYP_DEPOT G_KD GEOM CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold free_runA_stmt in G in change_no_check G' end).
    intros fx R M mdl Lc FF B C K ret sp m p st HFX HH MW W RP BD CP HR10 FPC HinP HK HLEX IA.
    pose proof ceil_rng as CR.
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4.
    assert (Utp : U tp = 0x641380) by (rewrite CP4; vm_compute; reflexivity).
    assert (ETP : TP = 0x641380) by (rewrite HTP; reflexivity).
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & OBL_freed_private & OBL_rt_private & OBL_stats_not_rep & OBL_blk_geom & OBL_batch_geom & OBL_hdr_writable & OBL_X_vs_node & OBL_store_private).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_freed_private_stmt in OBL_freed_private. unfold OBL_rt_private_stmt in OBL_rt_private.
    unfold OBL_stats_not_rep_stmt in OBL_stats_not_rep. unfold OBL_blk_geom_stmt in OBL_blk_geom. unfold OBL_batch_geom_stmt in OBL_batch_geom.
    unfold OBL_hdr_writable_stmt in OBL_hdr_writable. unfold OBL_X_vs_node_stmt in OBL_X_vs_node. unfold OBL_store_private_stmt in OBL_store_private.
    destruct (live_range bt st Lc FF W (U p) m HinP) as (Lp1 & Lp2 & Lp3 & Lp4).
    destruct (OBL_blk_geom st Lc FF (U p) m W HinP) as (GpT & GCp & (AB1 & AB2 & AB3 & AB4)).
    pose proof (blk_above_img bt st Lc FF W ltac:((lazymatch goal with |- ?G => let G' := eval unfold img_lo_small in G in change_no_check G' end); rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) (U p) m HinP) as PIMG.
    destruct (up8_facts m ltac:(lia)) as (U8a & U8b & U8c & U8d).
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    clear AB3 GCT'. hidehyp GpT. hidehyp GCp. hidehyp GCT. hidehyp GTB. hidehyp GCB. hidehyp AB4.
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    destruct R8 as [RH _]. destruct (RH (U p) m HinP) as (Hst & (b1 & Hb1 & H11) & Hnhi & Hnlo & Hw8 & Hz4 & _).
    assert (Hb1r : 0 <= b1 < 256) by (destruct Hb1; subst; lia). unfold byteZ, cellN in H11. rewrite w2b1 in H11 by lia.
    destruct R11 as (IAf & IAl & IAz & _). rewrite IA in IAf.
    destruct (R15 (U p) m HinP) as [WBLK WSH].
    pose proof (OBL_hdr_writable st Lc FF M mdl (U p) m W RP HinP) as WHDR.
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI, PIMG.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, KSPACE, NMAX, PTRLO in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) \/ (U p - 16 <= z < U p + up8 m) ->
                   Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st Lc FF M mdl z W RP).
      (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). first [clear - Hz HinP | idtac]; (destruct Hz as [Hz|[Hz|Hz]]; [am_tauto | am_tauto | right; right; left; exists (U p), m; split; [exact HinP | lia]]). }
    destruct R14 as (B1 & B2 & B3 & B4 & B5).
    set (Mr := mrestrict Hd M).
    Ltac hoff NH := apply hid_off_of; intros z Hz; unfold T_UNW, T_QC, T_PC, PC_SZ in *; split; [lia | apply NH; lia].
    (* [comment removed for export] *)
    Ltac konst Hd M R1 NHs C := apply (cellZ_restrict Hd M _ _ _ (const_cell bt M _ _ _ R1 C)); [lia | lia | hoff NHs].
    assert (K_mcs : rdn BSEGS Mr (Z_to_bv 64 0x10eebc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 30))) by konst Hd M R1 NHs CELL_mcs.
    assert (K_gcf : rdn BSEGS Mr (Z_to_bv 64 0x105f08) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x19fce8))) by konst Hd M R1 NHs CELL_gcf.
    assert (K_fum : rdn BSEGS Mr (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_fum.
    assert (K_inited : rdn BSEGS Mr (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_inited.
    assert (K_pg : rdn BSEGS Mr (Z_to_bv 64 0x105ef8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 PGP))) by konst Hd M R1 NHs CELL_pg.
    assert (K_P : rdn BSEGS Mr (Z_to_bv 64 PGP) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096))) by konst Hd M R1 NHs CELL_P.
    assert (K_kif : rdn BSEGS Mr (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_kif.
    assert (K_key : rdn BSEGS Mr (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
    { replace (at_ (Z_to_bv 64 0x10da20) 4) with (Z_to_bv 64 0x10da24) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_key. }
    assert (K_tsdp : rdn BSEGS Mr (at_ tp (-88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 TSDP))).
    { replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by (apply bv_eq; rewrite at_u by (rewrite Utp; lia); rewrite Utp, ETP; reflexivity). rewrite ETP. rewrite ETP in CELL_tsdp. konst Hd M R1 NHs CELL_tsdp. }
    assert (K_tctx : rdn BSEGS Mr (Z_to_bv 64 TSDP) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CTX))) by konst Hd M R1 NHs CELL_tctx.
    assert (K_hook : rdn BSEGS Mr (Z_to_bv 64 0x19fc88) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by konst Hd M R1 NHs CELL_hook.
    (* [comment removed for export] *)
    Ltac thr_cell Hd M NHrt C := apply (cellZ_restrict Hd M _ _ _ C); [(lazymatch goal with |- ?G => let G' := eval unfold T_UNW, T_QC in G in change_no_check G' end); lia | unfold T_UNW, T_QC in *; lia | hoff NHrt].
    assert (K_thr : rdn BSEGS Mr (at_ (Z_to_bv 64 CTX) 152) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tback. }
    assert (K_T0 : rdn BSEGS Mr (Z_to_bv 64 T) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CTX))) by thr_cell Hd M NHrt Tctx.
    assert (K_tid : rdn BSEGS Mr (Z_to_bv 64 (CTX + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by thr_cell Hd M NHrt Ttid.
    assert (K_unw : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 3168) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 3168) with (Z_to_bv 64 (T + T_UNW)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_UNW in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tunw. }
    assert (K_sw : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 40) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 40) with (Z_to_bv 64 (T + 40)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tsw. }
    assert (K_top : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bt_stack_top bt)))).
    { replace (at_ (Z_to_bv 64 T) 8) with (Z_to_bv 64 (T + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Ttop. }
    assert (K_bot : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 16) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bt_stack_bottom bt)))).
    { replace (at_ (Z_to_bv 64 T) 16) with (Z_to_bv 64 (T + 16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tbot. }
    (* [comment removed for export] *)
    unfold IA_FLAG, IA_INST in IAf, IAl, IAz. rewrite BT_ia in IAf, IAl, IAz. cbn [ia_ialloc_flag ia_ialloc_inst both_addrs] in IAf, IAl, IAz.
    assert (K_iaflag : rdn BSEGS Mr (Z_to_bv 64 0x19dc48) 1 = Some [Z_to_bv 8 1]).
    { apply (cellZ_restrict Hd M _ _ _ IAf); [lia | lia | hoff NHs]. }
    destruct (p_div_facts (U p) ltac:(lia)) as [Q47 Q32].
    set (q32 := U p / 2 ^ 32) in Q32.
    assert (K_pim : rdn BSEGS Mr (Z_to_bv 64 (0x10f3c8 + 8 * q32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
    { apply (cellZ_restrict Hd M _ _ _); [| lia | lia | hoff NHs].
      apply (fill_cellZ_zero BSEGS M _ _ IAz); (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_inst both_addrs Z.of_nat] in G in change_no_check G' end); lia. }
    (* [comment removed for export] *)
    assert (K_hdr : rdn BSEGS Mr (at_ p (-16)) 4 = Some [Z_to_bv 8 2; Z_to_bv 8 b1; Z_to_bv 8 (U (Z_to_bv 64 (m / 2 ^ 32))); Z_to_bv 8 (Z.shiftr (U (Z_to_bv 64 (m / 2 ^ 32))) 8)]).
    { replace (at_ p (-16)) with (Z_to_bv 64 (U p - 16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [| wd_ulia | unorm; hoff NHrt].
      change 4%nat with (1 + (1 + 2))%nat.
      apply (rdn_cat BSEGS M _ 1 3 [Z_to_bv 8 2]); [exact Hst | | wd_ulia].
      replace (at_ (Z_to_bv 64 (U p - 16)) (Z.of_nat 1)) with (Z_to_bv 64 (U p - 15)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply (rdn_cat BSEGS M _ 1 2 [Z_to_bv 8 b1]); [exact H11 | | wd_ulia].
      replace (at_ (Z_to_bv 64 (U p - 15)) (Z.of_nat 1)) with (Z_to_bv 64 (U p - 14)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      exact Hnhi. }
    assert (K_nhi : rdn BSEGS Mr (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (m / 2 ^ 32)))).
    { replace (at_ p (-14)) with (Z_to_bv 64 (U p - 14)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Hnhi. }
    assert (K_nlo : rdn BSEGS Mr (at_ p (-12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (m mod 2 ^ 32)))).
    { replace (at_ p (-12)) with (Z_to_bv 64 (U p - 12)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Hnlo. }
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS Mr (at_ S (-2304)) 2304 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. apply CPstk. cbn in Hx. lia. }
    assert (SOKunw : store_ok BSEGS Mr (at_ (Z_to_bv 64 T) 3168) 1 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia_c | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ TW); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia_c. }
    assert (SOKhdr : store_ok BSEGS Mr (at_ p (-16)) 4 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ WHDR); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]. }
    assert (SOKp : store_ok BSEGS Mr p 8 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ WHDR); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (SOKstat : store_ok BSEGS Mr (Z_to_bv 64 (T + 2824)) 16 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ TW); wd_ulia_c. }
    (* [comment removed for export] *)
    destruct (rdn_defined_ex BSEGS Mr (Z_to_bv 64 (T + 2824)) 8) as (bf0 & Cf0 & Lf0).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off; [| apply NHrt; revert Hi; unorm; intros Hi; lia].
      apply (writableZ_def M _ _ _ TW). revert Hi; unorm; intros Hi. lia. }
    { unorm. lia. }
    destruct (rdn_defined_ex BSEGS Mr (Z_to_bv 64 (T + 2832)) 8) as (bf1 & Cf1 & Lf1).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off; [| apply NHrt; revert Hi; unorm; intros Hi; lia].
      apply (writableZ_def M _ _ _ TW). revert Hi; unorm; intros Hi. lia. }
    { unorm. lia. }
    (* [comment removed for export] *)
    assert (FPCr : fpc Mr (U (getr R 8)) (U S) DMAX).
    { rewrite CP2. apply (fpc_kept_gen M _ _ _ FPC Mr). destruct (fpc_shape _ _ _ _ FPC) as [ST|FR]; [left; exact ST | right].
      intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. apply NHs; unfold PTRHI in *; lia. }
    set (h2 := Z_to_bv 8 (U (Z_to_bv 64 (m / 2 ^ 32)))) in *. set (h3 := Z_to_bv 8 (Z.shiftr (U (Z_to_bv 64 (m / 2 ^ 32))) 8)) in *.
    set (hdr := [Z_to_bv 8 2; Z_to_bv 8 b1; h2; h3]) in K_hdr.
    pose proof (bytes_le_to_Z_bound hdr) as Bhv. cbn [length hdr] in Bhv.
    pose proof (bytes_le_to_Z_nonneg hdr) as Bhv0.
    assert (Vhv : bytes_le_to_Z hdr = U (Z_to_bv 64 (bytes_le_to_Z hdr))) by (unorm; reflexivity).
    (* [comment removed for export] *)
    assert (GS12 : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0) by (rewrite CP2; lia).
    assert (Gp12 : AIMGHI + 16 <= U p /\ U p + 8 <= U S - 3584 /\ U p mod 16 = 0) by (rewrite CP2; lia).
    assert (GT12 : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact GT4|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); unfold hide in GTB; split; lia | rewrite CP2; lia]. }
    assert (GpT12 : U p + 8 <= T \/ T + 4096 <= U p - 16) by (unfold hide in GpT; lia).
    assert (Gctx12 : 1 <= CTX /\ CTX + 4096 <= U S - 3584 /\ (CTX + 4096 <= T \/ T + 4096 <= CTX) /\ (CTX + 4096 <= U p - 16 \/ U p + 8 <= CTX)).
    { unfold hide in GCT, GCp. rewrite CP2. lia. }
    assert (Gtp12 : AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI) by (rewrite Utp; lia).
    assert (Gtsdp12 : AIMGLO <= U (Z_to_bv 64 TSDP) /\ U (Z_to_bv 64 TSDP) + 8 <= AIMGHI) by (wd_ulia).
    assert (GP12 : AIMGLO <= U (Z_to_bv 64 PGP) /\ U (Z_to_bv 64 PGP) + 8 <= AIMGHI) by (wd_ulia).
    assert (Gtop12 : 4096 <= U (Z_to_bv 64 (bt_stack_top bt)) <= 2 ^ 47) by (wd_ulia).
    assert (Gbot12 : U (Z_to_bv 64 (bt_stack_bottom bt)) < U (Z_to_bv 64 (bt_stack_top bt))) by (first [clear - Gbot Gtop | idtac]; (wd_ulia)).
    assert (Gn12 : 1 <= m <= 2 ^ 40) by lia.
    assert (Gq12 : U p / 2 ^ 32 = q32 /\ 0 <= q32 < 2 ^ 15 /\ U p / 2 ^ 47 = 0) by (repeat split; try reflexivity; lia).
    assert (Ciab : U (Z_to_bv 8 1) <> 0) by (change (U (Z_to_bv 8 1)) with 1; lia).
    assert (Cpim0 : bytes_le_to_Z (word_to_le_bytes 8 (Z_to_bv 64 0)) = 0) by (rewrite bytes_le_to_Z_8; reflexivity).
    assert (Ch1 : Z_to_bv 8 b1 = Z_to_bv 8 0x11 \/ Z_to_bv 8 b1 = Z_to_bv 8 0x91) by (destruct Hb1 as [E|E]; rewrite E; [left|right]; reflexivity).
    assert (Chv : bytes_le_to_Z [Z_to_bv 8 2; Z_to_bv 8 b1; h2; h3] = U (Z_to_bv 64 (bytes_le_to_Z hdr))) by (subst hdr; exact Vhv).
    (* [comment removed for export] *)
    destruct (run_p12 Mr (seg_rom BSEGS) R S p ra0 tp (Z_to_bv 64 TSDP) (Z_to_bv 64 PGP) (Z_to_bv 64 (bt_stack_top bt)) (Z_to_bv 64 (bt_stack_bottom bt))
                T CTX m q32 DMAX (Z_to_bv 8 1) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 8 b1) h2 h3 (Z_to_bv 64 (bytes_le_to_Z hdr)) bf0 bf1)
      as (r12 & MU & sz & bsz & RUN12 & X1 & X2 & X8 & X9 & X10 & X11 & X18 & X19 & X20 & X21 & X22 & X3 & X4 & X23 & X24 & X25 & X26 & X27
          & SZ1 & SZ2 & FOOTU & GRU & USZ & UPC & UUNW & RSZ & LSZ & TAG0).
    all: try assumption.
    all: try reflexivity.
    all: let k := numgoals in guard k = 1.
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end). replace (Z_to_bv 64 (ia_free both_addrs)) with (Z_to_bv 64 0x6ed6c : word) by (apply bv_eq; reflexivity).
    replace (0x6ed6c%bv : word) with (Z_to_bv 64 0x6ed6c : word) in RUN12 by (apply bv_eq; reflexivity).
    replace (0x8f4f0%bv : word) with (Z_to_bv 64 0x8f4f0 : word) in RUN12 by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x6ed6c) M (seg_rom BSEGS))
             (@mkst fx r12 (Z_to_bv 64 0x8f4f0) (fr_P2 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. }
    { exact B1. }
    { exact B2. }
    { exact HH. }
    { rewrite restrict_mkstF. exact RUN12. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x6ed6c) M (seg_rom BSEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    remember (fr_P2 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as M11r eqn:EM11.
    remember (fr_P1 Mr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as M3 eqn:EM3 in FOOTU, GRU.
    set (MDin := munrestrict Hd M M11r).
    (* [comment removed for export] *)
    set (st1 := op_meter st EVT [] 0).
    assert (W1 : WF bt st1 Lc FF) by (apply WF_meter; [exact W | (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia | reflexivity]   (* [comment removed for export] *)).
    destruct SF1 as (_ & Evm & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _ & _ & _ & Eeg).
    assert (RP1 : Rep bt st1 Lc FF M mdl1).
    { pose proof (Rep_sbm bt st Lc FF M mdl mdl1 RP MI1 SBM1) as RPm.
      apply (OPS_REP_meter_pf bt st Lc FF M mdl1 mdl1 EVT [] 0 RPm eq_refl).
      - intros a; apply iff_refl.
      - pose proof RPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & FA & _) & _). exact FA.
      - rewrite app_nil_r. exact B1.
      - rewrite app_nil_r. exact MI1.
      - lia.
      - (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    assert (Mb15 : M (at_ p (-15)) = Some (Z_to_bv 8 b1)).
    { replace (at_ p (-15)) with (Z_to_bv 64 (U p - 15)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). apply rdn1_heap; [wd_ulia | exact H11]. }
    assert (Mb14 : M (at_ p (-14)) = Some h2 /\ M (at_ p (-13)) = Some h3).
    { pose proof (rdn_firstn BSEGS M 2 _ _ 1 Hnhi ltac:(lia)) as F1. cbn [firstn word_to_le_bytes Z_to_le_bytes] in F1.
      pose proof (rdn_skip BSEGS M _ 2 _ 1 Hnhi ltac:(lia) ltac:(wd_ulia)) as F2. cbn [skipn word_to_le_bytes Z_to_le_bytes Nat.sub] in F2.
      split.
      - replace (at_ p (-14)) with (Z_to_bv 64 (U p - 14)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). subst h2. apply rdn1_heap; [wd_ulia | exact F1].
      - replace (at_ p (-13)) with (at_ (Z_to_bv 64 (U p - 14)) (Z.of_nat 1)) by (first [clear - Lp3 Lp2 Lp1 CPhi CPlo | idtac]; (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia)). subst h3. apply rdn1_heap; [(lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia | exact F2]. }
    destruct Mb14 as [Mb14 Mb13].
    assert (Mb3210 : M (at_ (Z_to_bv 64 T) 3168) = Some (Z_to_bv 8 0)).
    { replace (at_ (Z_to_bv 64 T) 3168) with (Z_to_bv 64 (T + T_UNW)) by (first [clear - GTC GT0 CPhi CPlo | idtac]; (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_UNW in G in change_no_check G' end); wd_ulia)).
      change (Z_to_bv 8 0) with (Z_to_bv 8 (U (Z_to_bv 64 0))). apply rdn1_offimg; [(lazymatch goal with |- ?G => let G' := eval unfold T_UNW in G in change_no_check G' end); wd_ulia | exact Tunw]. }
    assert (MUb3210 : MU (at_ (Z_to_bv 64 T) 3168) = Some (Z_to_bv 8 0)) by (apply rdn1_offimg; [(lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia | exact UUNW]).
    (* [comment removed for export] *)
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (rewrite CP2; lia).
    assert (Gpm : AIMGHI + 16 <= U p /\ U p + 8 <= U S - 3584) by (rewrite CP2; lia).
    assert (GTm : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)) by exact GT12.
    assert (GpTm : U p + 8 <= T \/ T + 4096 <= U p - 16) by exact GpT12.
    (* [comment removed for export] *)
    pose proof (fr_P1_grows' Mr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as GRr3. feed GRr3. rewrite <- EM3 in GRr3.
    pose proof (fr_P2_grows MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as GR2. feed GR2. rewrite <- EM11 in GR2.
    assert (GRr11 : mem_grows Mr M11r).
    { eapply mem_grows_trans; [exact GRr3|]. eapply mem_grows_trans; [exact GRU|]. exact GR2. }
    assert (GRin : mem_grows M MDin).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MDin, munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:Ex; [exact Hx|]. apply GRr11. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off by exact Ex. exact Hx. }
    (* [comment removed for export] *)
    assert (MUeq : forall x : word, (U x < U S - 2272 \/ U S - 64 <= U x) -> U x <> T + 3168 -> MU x = M3 x).
    { intros x Hx1 Hx2. destruct (decide (MU x = M3 x)) as [E|NE]; [exact E|]. exfalso. first [clear - NE Hx2 Hx1 FOOTU | idtac]; (destruct (FOOTU x NE) as [F|[F|[F|F]]]; lia). }
    (* [comment removed for export] *)
    pose proof (fr_P1_foot Mr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as P1F. feed P1F. rewrite <- EM3 in P1F.
    pose proof (fr_P2_foot MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as P2F. feed P2F. rewrite <- EM11 in P2F.
    pose proof (fr_P2_hdr MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as P2H. feed P2H. rewrite <- EM11 in P2H.
    destruct P2H as (E16 & E15 & E14 & E13).
    assert (DIFF1 : forall a : word, MDin a <> M a -> Xd (U S) (U p) T (U a) /\ MDin a <> None).
    { intros a NE. pose proof (u64_range a) as Ha.
      split; cycle 1.
      { destruct (MDin a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (M a) eqn:E2; [|reflexivity].
        exfalso. assert (X : M a <> None) by (rewrite E2; discriminate). apply GRin in X. rewrite E1 in X. exact (X eq_refl). }
      unfold MDin, munrestrict in NE. destruct (Hd a) eqn:Eh; [exfalso; exact (NE eq_refl)|].
      assert (EMr : Mr a = M a) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); apply mrestrict_off; exact Eh).
      (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end).
      destruct (decide (M11r a = MU a)) as [E11|N11].
      - rewrite E11 in NE. destruct (decide (MU a = M3 a)) as [EU|NU].
        + rewrite EU in NE. rewrite <- EMr in NE. pose proof (P1F a NE). lia.
        + destruct (FOOTU a NU) as [F|[F|[F|F]]]; try (first [clear - F | idtac]; lia).
          exfalso. apply NE. replace a with (at_ (Z_to_bv 64 T) 3168) by (first [clear - F GTC GT0 CPhi CPlo | idtac]; (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia)). rewrite MUb3210, Mb3210. reflexivity.
      - destruct (P2F a N11) as [F|[F|[F|F]]]; try (first [clear - F | idtac]; lia).
        (* [comment removed for export] *)
        destruct (decide (U a = U p - 16)) as [E16'|N16]; [lia|]. exfalso. apply NE.
        destruct (decide (U a = U p - 15)) as [E|N1].
        { replace a with (at_ p (-15)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). rewrite E15, Mb15. reflexivity. }
        destruct (decide (U a = U p - 14)) as [E|N2].
        { replace a with (at_ p (-14)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). rewrite E14, Mb14. reflexivity. }
        replace a with (at_ p (-13)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). rewrite E13, Mb13. reflexivity. }
    (* [comment removed for export] *)
    assert (VIS : forall a : word, Hd a = false -> MDin a = M11r a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold MDin in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (VISstk : forall a : word, U S - 3584 <= U a < U S -> MDin a = M11r a).
    { intros a Ha. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply NHs; [lia|]. left. rewrite CP2 in Ha. lia. }
    (* [comment removed for export] *)
    assert (SZW : U (Z_to_bv 64 (bytes_le_to_Z bsz)) mod 2 ^ 32 = sz).
    { pose proof (bytes_le_to_Z_bound bsz) as Bb. rewrite LSZ in Bb. pose proof (bytes_le_to_Z_nonneg bsz). unorm. apply (lez_low32 BSEGS MU (at_ S (-2120)) bsz sz RSZ USZ). lia. }
    apply (katD_bind BSEGS _ (depot_post bt FXOK KD (Xd (U S) (U p) T) st1 Lc FF MDin mdl1 r12 (at_ S (-2176)) (Z_to_bv 64 0x50838))).
    { apply (HYP_DEPOT fx (Xd (U S) (U p) T) st1 Lc FF MDin mdl1 r12 (at_ S (-2176)) (at_ S (-2112)) (Z_to_bv 64 (bytes_le_to_Z bsz)) (Z_to_bv 64 0x50838) sz HFX).
      { rewrite Ehl. exact HH. }
      { exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW). }
      { exact W1. }
      { exists M. split; [exact RP1 | exact DIFF1]. }
      { intros a Ha. split.
        - unfold Xd in Ha. rewrite CP2 in Ha. rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end).
          first [clear - Ha GTI PIMG CR CPlo | idtac]; (destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | lia | destruct GTI as [GTI'|GTI']; lia | lia]).
        - intros id Hid. cbn [st1 op_meter add_meter a_dep] in Hid |- *.
          apply (OBL_X_vs_node st Lc FF (U p) m id a W HinP Hid). unfold Xd in Ha. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). rewrite CP2 in Ha. clear - Ha U8a U8b U8c U8d Lp3 CPlo CR. lia. }
      { (* [comment removed for export] *)
        intros a Ha. apply (xd_xtracked bt _ Lc FF (U S) (U p) m a W1 HinP); [rewrite CP2; clear - CPlo; lia | exact Ha]. }
      { (* [comment removed for export] *)
        destruct HLEX as [h0 HLE0]. exists h0. exact HLE0. }
      { (lazymatch goal with |- ?G => let G' := eval cbn [st1 op_meter add_meter a_dep a_kact] in G in change_no_check G' end). destruct W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & Drest) & (WM1 & _) & _).
        rewrite meter_div by exact WM1. lia. }
      { (lazymatch goal with |- ?G => let G' := eval cbn [st1 op_meter add_meter a_dep a_kact] in G in change_no_check G' end). destruct W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & Drest) & (WM1 & _) & _).
        rewrite meter_div by exact WM1. unfold FRW in *. lia. }
      { exact X1. } { exact X2. } { exact X10. } { exact X11. }
      { rewrite at_u by lia. rewrite CP2. destruct (sp_facts16 sp CP16) as [E _]. exact E. }
      { rewrite at_u by lia. rewrite CP2. lia. }
      { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end). lia. }
      { apply ret_ok_lit; [lia | reflexivity]. }
      { intros a Ha. rewrite at_u in Ha by lia. split.
        - apply GRin. apply store_ok1_heap; [lia|]. apply CPstk. rewrite <- CP2. lia.
        - eapply store_ok_mono; [exact GRin|]. apply CPstk. rewrite <- CP2. lia. }
      { split; [exact (proj1 SZ1) | unfold DMAX in SZ2; cbn in SZ2; exact SZ2]. }            (* [comment removed for export] *)
      { exact SZW. }
      { (* [comment removed for export] *)
        assert (TG : rdn BSEGS MU (at_ (at_ S (-2120)) 4) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by (rewrite at_at; exact TAG0).
        pose proof (lez_high32_0 BSEGS MU (at_ S (-2120)) bsz RSZ TG) as HI.
        pose proof (bytes_le_to_Z_bound bsz) as Bb. rewrite LSZ in Bb. pose proof (bytes_le_to_Z_nonneg bsz) as Bn.
        rewrite u_Z2bv by (clear - Bb Bn; cbn in Bb; lia). rewrite HI. clear; lia. }
      { (* [comment removed for export] *)
        (lazymatch goal with |- ?G => let G' := eval cbn [st1 op_meter add_meter a_kact] in G in change_no_check G' end). destruct BD as (_ & _ & BK). unfold kcost_free in HK. clear - BK HK. lia. }
      { intros i Hi. rewrite at_u in Hi by lia. apply GRin. apply store_ok1_heap; [wd_ulia|].
        replace (Z_to_bv 64 i) with (Z_to_bv 64 (U (Z_to_bv 64 i))) by (apply bv_eq; unorm; reflexivity).
        rewrite Z_to_bv_bv_unsigned. apply CPstk. unorm. rewrite <- CP2. lia. }
      { rewrite at_u by lia. rewrite CP2. lia. }
      { rewrite !at_u by lia. clear. lia. }                                                  (* [comment removed for export] *)
      { rewrite at_u by lia. clear - SZ1 SZ2 HSr. unfold DMAX in SZ2. cbn in SZ2. lia. } }    (* [comment removed for export] *)
    (* [comment removed for export] *)
    intros c' POST.
    destruct POST as (fx' & st' & M' & mdl' & R' & id & Ec' & HFX' & (d' & naa & Est') & W2 & RX2 & KEPTX & DIFF2 & CHG2 & RK & A0 & Hid & SEV & LZ & HH2 & MW2).
    subst c'. apply katD_refl.
    unfold depot_st in Est'. cbn [st1 op_meter add_meter a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_kact a_shsec] in Est'.
    rewrite app_nil_r, Z.add_0_r in Est'. subst st'.
    destruct RX2 as (M0' & RP2 & DX2).
    (* [comment removed for export] *)
    pose proof (fr_P2_q0 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as Cq0. feed Cq0. rewrite <- EM11 in Cq0.
    pose proof (fr_P2_q1 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as Cq1. feed Cq1. rewrite <- EM11 in Cq1.
    pose proof (fr_P2_q2 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as Cq2. feed Cq2. rewrite <- EM11 in Cq2.
    pose proof (fr_P2_q3 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as Cq3. feed Cq3. rewrite <- EM11 in Cq3.
    pose proof (fr_P2_q4 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as Cq4. feed Cq4. rewrite <- EM11 in Cq4.
    pose proof (fr_P2_q5 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as Cq5. feed Cq5. rewrite <- EM11 in Cq5.
    (* [comment removed for export] *)
    pose proof (fr_P2_rdn_out MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as P2O. feed P2O. rewrite <- EM11 in P2O.
    assert (ICPT : forall k (v : word), -56 <= k <= -8 ->
              rdn BSEGS M3 (at_ S k) 8 = Some (LE8 v) -> rdn BSEGS M11r (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hk Hr. rewrite P2O; cycle 1.
      { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. } { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. } { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. } { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
      apply (rd_same BSEGS MU M3); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply MUeq; lia. }
    pose proof (fr_P1_i0 Mr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I0. feed I0. rewrite <- EM3 in I0.
    pose proof (fr_P1_i1 Mr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I1. feed I1. rewrite <- EM3 in I1.
    pose proof (fr_P1_i2 Mr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I2. feed I2. rewrite <- EM3 in I2.
    pose proof (fr_P1_i3 Mr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I3. feed I3. rewrite <- EM3 in I3.
    pose proof (fr_P1_i4 Mr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I4. feed I4. rewrite <- EM3 in I4.
    pose proof (fr_P1_i5 Mr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I5. feed I5. rewrite <- EM3 in I5.
    pose proof (fr_P1_i6 Mr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I6. feed I6. rewrite <- EM3 in I6.
    pose proof (ICPT (-8) ra0 ltac:(lia) I0) as Ci0.
    pose proof (ICPT (-16) (getr R 8) ltac:(lia) I1) as Ci1.
    pose proof (ICPT (-24) (getr R 9) ltac:(lia) I2) as Ci2.
    pose proof (ICPT (-32) (getr R 18) ltac:(lia) I3) as Ci3.
    pose proof (ICPT (-40) (getr R 19) ltac:(lia) I4) as Ci4.
    pose proof (ICPT (-48) (getr R 20) ltac:(lia) I5) as Ci5.
    pose proof (ICPT (-56) (getr R 21) ltac:(lia) I6) as Ci6.
    (* [comment removed for export] *)
    assert (XF : forall k bs0, -2176 <= k -> k + 8 <= 0 -> rdn BSEGS M11r (at_ S k) 8 = Some bs0 -> rdn BSEGS M' (at_ S k) 8 = Some bs0).
    { intros k bs0 Hk1 Hk2 Hr. apply (rd_same BSEGS M' M11r); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. rewrite (KEPTX x); [| (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); (first [clear - Hx Hk2 Hk1 | idtac]; lia) | rewrite at_u by (first [clear - CR CPlo CP2 CPhi | idtac]; lia); (first [clear - Hx Hk1 | idtac]; lia)]. apply VISstk. lia. }
    Ltac incs := apply in_cs; reflexivity.
    Ltac viaRK RK k X := etransitivity; [| exact X];
      match goal with |- getr _ ?x = getr _ _ => replace x with (Z_to_bv 5 k) by (apply bv_eq; reflexivity) end; apply RK; incs.
    (lazymatch goal with |- ?G => let G' := eval unfold runA_post in G in change_no_check G' end). exists fx', R', M', M0', mdl', d', naa, id.
    (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold runA_st in G in change_no_check G' end). fold S. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end).
    split; [reflexivity|]. split; [exact HFX'|]. split; [exact HH2|]. split; [exact W2|]. split; [exact RP2|]. split; [exact DX2|].
    split.
    { (* [comment removed for export] *) intros a NE. destruct (decide (M' a = MDin a)) as [E|N].
      + rewrite E in NE |- *. destruct (DIFF1 a NE) as [X D]. split; [left; exact X | exact D].
      + destruct (DIFF2 a N) as [_ D]. split; [| exact D]. right. pose proof (CHG2 a N) as CX. rewrite at_u in CX by lia. rewrite ?BT_ia in CX.
        destruct CX as [X|[X|X]]; [left; lia | right; left; exact X | right; right; exact X]. }
    split.
    { (* [comment removed for export] *) rewrite (KEPTX (at_ p (-16))); [| (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); rewrite at_u by (first [clear - Lp1 Lp3 Lp2 CPhi CPlo | idtac]; lia); (repeat match goal with H : _ |- _ => clear H end; lia) | rewrite !at_u by (first [clear - CR CPlo CP2 CPhi Lp1 Lp3 Lp2 | idtac]; lia); (first [clear - Lp3 Lp2 CPlo CP2 G_KD | idtac]; lia)].
      rewrite VIS by (rewrite <- (Z_to_bv_bv_unsigned 64 (at_ p (-16))); rewrite at_u by lia; apply NHrt; lia). exact E16. }
    split; [apply XF; [lia | lia | exact Cq0]|]. split; [apply XF; [lia | lia | exact Cq1]|]. split; [apply XF; [lia | lia | exact Cq2]|].
    split; [apply XF; [lia | lia | exact Cq3]|]. split; [apply XF; [lia | lia | exact Cq4]|]. split; [apply XF; [lia | lia | exact Cq5]|].
    split; [apply XF; [lia | lia | exact Ci0]|]. split; [apply XF; [lia | lia | exact Ci1]|]. split; [apply XF; [lia | lia | exact Ci2]|].
    split; [apply XF; [lia | lia | exact Ci3]|]. split; [apply XF; [lia | lia | exact Ci4]|]. split; [apply XF; [lia | lia | exact Ci5]|].
    split; [apply XF; [lia | lia | exact Ci6]|].
    split; [viaRK RK 2 X2|]. split; [viaRK RK 8 X8|]. split; [viaRK RK 9 X9|]. split; [exact A0|].
    split; [viaRK RK 18 X18|]. split; [viaRK RK 19 X19|]. split; [viaRK RK 20 X20|]. split; [viaRK RK 21 X21|].
    split; [viaRK RK 22 X22|]. split; [viaRK RK 3 X3|]. split; [viaRK RK 4 X4|].
    split; [viaRK RK 23 X23|]. split; [viaRK RK 24 X24|]. split; [viaRK RK 25 X25|]. split; [viaRK RK 26 X26|]. split; [viaRK RK 27 X27|].
    split; [exact Hid|].
    split; [eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV]|].
    split.
    { intros a Ha. cbn [a_dep] in LZ.
      assert (RNGa : 0 <= a < 2 ^ 64).                                                       (* [comment removed for export] *)
      { destruct Ha as [V|[V|V]]; [| clear - V CR; lia | cbn [ia_img_lo ia_img_hi both_addrs] in V; clear - V; lia].
        rewrite <- ?BT_ia in V. exact (proj1 (AsKSys7b.app_visible_cases bt _ Lc FF _ _ W2 a V)). }
      destruct (LZ a RNGa) as [E|(blk & Hin & Hnin & Hr)]; [rewrite E; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz; reflexivity|].
      exfalso. destruct (OBL_store_private _ Lc FF blk a W2 Hin Hr) as (Z1 & Z2 & Z3). rewrite ?BT_ia in Z2, Z3. cbn [ia_img_lo ia_img_hi both_addrs] in Z2.
      destruct Ha as [V|[V|V]]; [exact (Z3 V) | lia | cbn [ia_img_lo ia_img_hi both_addrs] in V; lia]. }
    exact MW2.
  Qed.
End TOPA.
End BoAllocFTopA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i.BoAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI.BoAllocF2 BoAllocFZ OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRun BoAllocFRun0 BoAllocFRunJ OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp BoAllocFHypI BoAllocFTopA.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AsAllocFFam.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
(* [comment removed for export] *)
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Section TOP0I.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Hypothesis OPS_IA4 : OPS_REP_ialloc_init4_stmt bt.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).

  (* [comment removed for export] *)
  Definition free_null0_stmt : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp : Z) (p : word) (st : ast),
      FXOK fx -> m_halted mdl = None ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> HP h st -> BackingAlgebra.model_ivs_wf mdl ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> getr R 10 = p -> fpc M (U (getr R 8)) sp DMAX ->
      a_ialloc st = false -> p = Z_to_bv 64 0 ->
      katD BSEGS (cfg BSEGS fx R (ia_free both_addrs) M mdl) (free_post BSEGS FXOK both_addrs (AAINV_F bt HP) h MSTK_A R M mdl Lc FF B C K ret sp).

  Theorem free_null0 : free_null0_stmt.
  Proof using FAM HPc OPS_IA4 HTP GEOM CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold free_null0_stmt in G in change_no_check G' end).
    intros h fx R M mdl Lc FF B C K ret sp p st HFX HH W RP BD HLE MW CP HR10 FPC IA Hp0.
    pose proof ceil_rng as CR.
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4.
    assert (Utp : U tp = 0x641380) by (rewrite CP4; vm_compute; reflexivity).
    assert (ETP : TP = 0x641380) by (rewrite HTP; reflexivity).
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _ & OBL_rt_private & _ & _ & _ & _ & _ & _).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_rt_private_stmt in OBL_rt_private.
    assert (Hpz : U p = 0) by (rewrite Hp0; reflexivity).
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    clear GCT' GCB. hidehyp GCT. hidehyp GTB.
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    destruct R11 as (IAf & IAl & IAz & _). rewrite IA in IAf.
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, KSPACE, NMAX, PTRLO in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st Lc FF M mdl z W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). destruct Hz as [Hz|Hz]; [am_tauto | am_tauto]. }
    destruct R14 as (B1 & B2 & B3 & B4 & B5).
    set (Mr := mrestrict Hd M).
    Ltac hoff NH := apply hid_off_of; intros z Hz; unfold T_UNW, T_QC, T_PC, PC_SZ in *; split; [lia | apply NH; lia].
    (* [comment removed for export] *)
    Ltac konst Hd M R1 NHs C := apply (cellZ_restrict Hd M _ _ _ (const_cell bt M _ _ _ R1 C)); [lia | lia | hoff NHs].
    assert (K_mcs : rdn BSEGS Mr (Z_to_bv 64 0x10eebc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 30))) by konst Hd M R1 NHs CELL_mcs.
    assert (K_gcf : rdn BSEGS Mr (Z_to_bv 64 0x105f08) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x19fce8))) by konst Hd M R1 NHs CELL_gcf.
    assert (K_fum : rdn BSEGS Mr (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_fum.
    assert (K_inited : rdn BSEGS Mr (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_inited.
    assert (K_pg : rdn BSEGS Mr (Z_to_bv 64 0x105ef8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 PGP))) by konst Hd M R1 NHs CELL_pg.
    assert (K_P : rdn BSEGS Mr (Z_to_bv 64 PGP) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096))) by konst Hd M R1 NHs CELL_P.
    assert (K_kif : rdn BSEGS Mr (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_kif.
    assert (K_key : rdn BSEGS Mr (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
    { replace (at_ (Z_to_bv 64 0x10da20) 4) with (Z_to_bv 64 0x10da24) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_key. }
    assert (K_tsdp : rdn BSEGS Mr (at_ tp (-88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 TSDP))).
    { replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by (apply bv_eq; rewrite at_u by (rewrite Utp; lia); rewrite Utp, ETP; reflexivity). rewrite ETP. rewrite ETP in CELL_tsdp. konst Hd M R1 NHs CELL_tsdp. }
    assert (K_tctx : rdn BSEGS Mr (Z_to_bv 64 TSDP) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CTX))) by konst Hd M R1 NHs CELL_tctx.
    assert (K_hook : rdn BSEGS Mr (Z_to_bv 64 0x19fc88) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by konst Hd M R1 NHs CELL_hook.
    (* [comment removed for export] *)
    Ltac thr_cell Hd M NHrt C := apply (cellZ_restrict Hd M _ _ _ C); [(lazymatch goal with |- ?G => let G' := eval unfold T_UNW, T_QC in G in change_no_check G' end); lia | unfold T_UNW, T_QC in *; lia | hoff NHrt].
    assert (K_thr : rdn BSEGS Mr (at_ (Z_to_bv 64 CTX) 152) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tback. }
    assert (K_T0 : rdn BSEGS Mr (Z_to_bv 64 T) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CTX))) by thr_cell Hd M NHrt Tctx.
    assert (K_tid : rdn BSEGS Mr (Z_to_bv 64 (CTX + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by thr_cell Hd M NHrt Ttid.
    assert (K_unw : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 3168) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 3168) with (Z_to_bv 64 (T + T_UNW)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_UNW in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tunw. }
    assert (K_sw : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 40) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 40) with (Z_to_bv 64 (T + 40)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tsw. }
    assert (K_top : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bt_stack_top bt)))).
    { replace (at_ (Z_to_bv 64 T) 8) with (Z_to_bv 64 (T + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Ttop. }
    assert (K_bot : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 16) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bt_stack_bottom bt)))).
    { replace (at_ (Z_to_bv 64 T) 16) with (Z_to_bv 64 (T + 16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tbot. }
    (* [comment removed for export] *)
    unfold IA_FLAG, IA_INST in IAf, IAl, IAz. rewrite BT_ia in IAf, IAl, IAz. cbn [ia_ialloc_flag ia_ialloc_inst both_addrs] in IAf, IAl, IAz.
    assert (K_iaflag : rdn BSEGS Mr (Z_to_bv 64 0x19dc48) 1 = Some [Z_to_bv 8 0]).
    { apply (cellZ_restrict Hd M _ _ _ IAf); [lia | lia | hoff NHs]. }
    assert (K_lock : rdn BSEGS Mr (Z_to_bv 64 0x19dc49) 1 = Some [Z_to_bv 8 0]).
    { apply (cellZ_restrict Hd M _ _ _ IAl); [lia | lia | hoff NHs]. }
    destruct (rdn2_junk_ex Mr) as (b2 & b3 & K_junk).
    assert (K_flagw : rdn BSEGS Mr (Z_to_bv 64 0x19dc48) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3]).
    { change 4%nat with (1 + (1 + 2))%nat. apply (rdn_cat BSEGS Mr _ 1 3 [Z_to_bv 8 0]); [exact K_iaflag | | wd_ulia].
      replace (at_ (Z_to_bv 64 0x19dc48) (Z.of_nat 1)) with (Z_to_bv 64 0x19dc49 : word) by (apply bv_eq; reflexivity).
      apply (rdn_cat BSEGS Mr _ 1 2 [Z_to_bv 8 0]); [exact K_lock | | wd_ulia].
      replace (at_ (Z_to_bv 64 0x19dc49) (Z.of_nat 1)) with (Z_to_bv 64 0x19dc4a : word) by (apply bv_eq; reflexivity). exact K_junk. }
    destruct (p_div_facts (U p) ltac:(lia)) as [Q47 Q32].
    set (q32 := U p / 2 ^ 32) in Q32.
    assert (exists n1 : Z, n1 = 40) as [n1 En1] by (exists 40; reflexivity).
    assert (exists n2 : Z, n2 = 262144) as [n2 En2] by (exists 262144; reflexivity).
    assert (exists n3 : Z, n3 = 3456) as [n3 En3] by (exists 3456; reflexivity).
    assert (exists n4 : Z, n4 = 262728) as [n4 En4] by (exists 262728; reflexivity).
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & _ & _ & _).
    rewrite Forall_forall in DC.
    assert (DYN_P : forall a, PGP <= a < PGP + 8 -> ~ img_dyn (bt_ia bt) a) by (intros a Ha; exact (DC _ CELL_P a Ha)).
    assert (DYN_TS : forall a, TSDP <= a < TSDP + 8 -> ~ img_dyn (bt_ia bt) a) by (intros a Ha; exact (DC _ CELL_tctx a Ha)).
    rewrite BT_ia in DYN_P, DYN_TS.
    assert (GPIz : (PGP + 8 <= 0x10f3c0 \/ 0x10f3c0 + 0x81030 <= PGP) /\ (PGP + 8 <= 0x19dc48 \/ 0x19dc4c <= PGP)).
    { split.
      - destruct (ivl_disj PGP 8 0x10f3c0 (0x10f3c0 + 0x81030) ltac:(intros a Ha X; apply (DYN_P a Ha); (lazymatch goal with |- ?G => let G' := eval unfold img_dyn, IASZ in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance ia_depot_tab ia_stackstore ia_ialloc_flag ia_ialloc_inst both_addrs] in G in change_no_check G' end); lia) ltac:(lia) ltac:(lia)); lia.
      - destruct (ivl_disj PGP 8 0x19dc48 (0x19dc48 + 8) ltac:(intros a Ha X; apply (DYN_P a Ha); (lazymatch goal with |- ?G => let G' := eval unfold img_dyn, IASZ in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance ia_depot_tab ia_stackstore ia_ialloc_flag ia_ialloc_inst both_addrs] in G in change_no_check G' end); lia) ltac:(lia) ltac:(lia)); lia. }
    assert (GPI : (U (Z_to_bv 64 PGP) + 8 <= 0x10f3c0 \/ 0x10f3c0 + 0x81030 <= U (Z_to_bv 64 PGP)) /\ (U (Z_to_bv 64 PGP) + 8 <= 0x19dc48 \/ 0x19dc4c <= U (Z_to_bv 64 PGP))) by (unorm; exact GPIz).
    assert (GTSI : (TSDP + 8 <= 0x10f3c0 \/ 0x10f3c0 + 0x81030 <= TSDP) /\ (TSDP + 8 <= 0x19dc48 \/ 0x19dc50 <= TSDP)).
    { split.
      - destruct (ivl_disj TSDP 8 0x10f3c0 (0x10f3c0 + 0x81030) ltac:(intros a Ha X; apply (DYN_TS a Ha); (lazymatch goal with |- ?G => let G' := eval unfold img_dyn, IASZ in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance ia_depot_tab ia_stackstore ia_ialloc_flag ia_ialloc_inst both_addrs] in G in change_no_check G' end); lia) ltac:(lia) ltac:(lia)); lia.
      - destruct (ivl_disj TSDP 8 0x19dc48 (0x19dc48 + 8) ltac:(intros a Ha X; apply (DYN_TS a Ha); (lazymatch goal with |- ?G => let G' := eval unfold img_dyn, IASZ in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance ia_depot_tab ia_stackstore ia_ialloc_flag ia_ialloc_inst both_addrs] in G in change_no_check G' end); lia) ltac:(lia) ltac:(lia)); lia. }
    (* [comment removed for export] *)
    set (MIr := fr_init Mr b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4).
    Ltac xinit En1 En2 En3 En4 K := apply (init_keeps_rdn _ _ _ _ _ _ _ En1 En2 En3 En4); [(lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact K].
    assert (KI_mcs : rdn BSEGS MIr (Z_to_bv 64 0x10eebc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 30))) by xinit En1 En2 En3 En4 K_mcs.
    assert (KI_gcf : rdn BSEGS MIr (Z_to_bv 64 0x105f08) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x19fce8))) by xinit En1 En2 En3 En4 K_gcf.
    assert (KI_fum : rdn BSEGS MIr (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1]) by xinit En1 En2 En3 En4 K_fum.
    assert (KI_inited : rdn BSEGS MIr (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1]) by xinit En1 En2 En3 En4 K_inited.
    assert (KI_pg : rdn BSEGS MIr (Z_to_bv 64 0x105ef8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 PGP))) by xinit En1 En2 En3 En4 K_pg.
    assert (KI_P : rdn BSEGS MIr (Z_to_bv 64 PGP) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096))) by xinit En1 En2 En3 En4 K_P.
    assert (KI_kif : rdn BSEGS MIr (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]) by xinit En1 En2 En3 En4 K_kif.
    assert (KI_key : rdn BSEGS MIr (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by xinit En1 En2 En3 En4 K_key.
    assert (KI_tsdp : rdn BSEGS MIr (at_ tp (-88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 TSDP))) by xinit En1 En2 En3 En4 K_tsdp.
    assert (KI_tctx : rdn BSEGS MIr (Z_to_bv 64 TSDP) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CTX))) by xinit En1 En2 En3 En4 K_tctx.
    assert (KI_hook : rdn BSEGS MIr (Z_to_bv 64 0x19fc88) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by xinit En1 En2 En3 En4 K_hook.
    assert (KI_thr : rdn BSEGS MIr (at_ (Z_to_bv 64 CTX) 152) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 T))) by xinit En1 En2 En3 En4 K_thr.
    assert (KI_T0 : rdn BSEGS MIr (Z_to_bv 64 T) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CTX))) by xinit En1 En2 En3 En4 K_T0.
    assert (KI_tid : rdn BSEGS MIr (Z_to_bv 64 (CTX + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by xinit En1 En2 En3 En4 K_tid.
    assert (KI_unw : rdn BSEGS MIr (at_ (Z_to_bv 64 T) 3168) 1 = Some [Z_to_bv 8 0]) by xinit En1 En2 En3 En4 K_unw.
    assert (KI_sw : rdn BSEGS MIr (at_ (Z_to_bv 64 T) 40) 1 = Some [Z_to_bv 8 0]) by xinit En1 En2 En3 En4 K_sw.
    assert (KI_top : rdn BSEGS MIr (at_ (Z_to_bv 64 T) 8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bt_stack_top bt)))) by xinit En1 En2 En3 En4 K_top.
    assert (KI_bot : rdn BSEGS MIr (at_ (Z_to_bv 64 T) 16) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bt_stack_bottom bt)))) by xinit En1 En2 En3 En4 K_bot.
    clear K_mcs K_gcf K_fum K_inited K_kif K_key K_tsdp K_tctx K_hook K_thr K_T0 K_tid K_unw K_sw K_top K_bot.
    (* [comment removed for export] *)
    clear GPIz GTSI DYN_P DYN_TS DC. hidehyp GPI.
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS Mr (at_ S (-2304)) 2304 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. apply CPstk. cbn in Hx. lia. }
    assert (SOKunw : store_ok BSEGS Mr (at_ (Z_to_bv 64 T) 3168) 1 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia_c | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ TW); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia_c. }
    (* [comment removed for export] *)
    assert (FPCr : fpc Mr (U (getr R 8)) (U S) DMAX).
    { rewrite CP2. apply (fpc_kept_gen M _ _ _ FPC Mr). destruct (fpc_shape _ _ _ _ FPC) as [ST|FR]; [left; exact ST | right].
      intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. apply NHs; unfold PTRHI in *; lia. }
    (* [comment removed for export] *)
    assert (RETOK : ret_ok ra0) by (rewrite CP1; apply ret_ok_lit; [lia | exact CPe]).
    assert (GS12 : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0) by (rewrite CP2; lia).
    assert (GT12 : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact GT4|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); unfold hide in GTB; split; lia | rewrite CP2; lia]. }
    assert (Gctx12 : 1 <= CTX /\ CTX + 4096 <= U S - 3584 /\ (CTX + 4096 <= T \/ T + 4096 <= CTX)) by (unfold hide in GCT; rewrite CP2; lia).
    assert (Gtp12 : AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI) by (rewrite Utp; lia).
    assert (Gtsdp12 : AIMGLO <= U (Z_to_bv 64 TSDP) /\ U (Z_to_bv 64 TSDP) + 8 <= AIMGHI) by (wd_ulia).
    assert (GP12 : AIMGLO <= U (Z_to_bv 64 PGP) /\ U (Z_to_bv 64 PGP) + 8 <= AIMGHI) by (wd_ulia).
    assert (Gtop12 : 4096 <= U (Z_to_bv 64 (bt_stack_top bt)) <= 2 ^ 47) by (wd_ulia).
    assert (Gbot12 : U (Z_to_bv 64 (bt_stack_bottom bt)) < U (Z_to_bv 64 (bt_stack_top bt))) by (wd_ulia).
    assert (Gq12 : U p / 2 ^ 32 = q32 /\ 0 <= q32 < 2 ^ 15 /\ U p / 2 ^ 47 = 0) by (repeat split; try reflexivity; lia).
    (* [comment removed for export] *)
    unfold hide in GPI.
    destruct (run_p0_0 Mr (seg_rom BSEGS) R S p ra0 tp (Z_to_bv 64 TSDP) (Z_to_bv 64 PGP) (Z_to_bv 64 (bt_stack_top bt)) (Z_to_bv 64 (bt_stack_bottom bt))
                T CTX q32 DMAX b2 b3 n1 n2 n3 n4)
      as (rZ & MU & sz & RUNZ & X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X3 & X4 & X23 & X24 & X25 & X26 & X27 & SZ1 & FOOTU & GRU & UUNW).
    all: try assumption.
    all: try reflexivity.
    all: let k := numgoals in guard k = 1.
    change (fr_init Mr b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4) with MIr in FOOTU, GRU.
    clear GPI.
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end). replace (Z_to_bv 64 (ia_free both_addrs)) with (Z_to_bv 64 0x6ed6c : word) by (apply bv_eq; reflexivity).
    replace (0x6ed6c%bv : word) with (Z_to_bv 64 0x6ed6c : word) in RUNZ by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x6ed6c) M (seg_rom BSEGS))
             (@mkst fx rZ ra0 (fr_b1 MU S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22)) (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. }
    { exact B1. }
    { exact B2. }
    { exact HH. }
    { rewrite restrict_mkstF. exact RUNZ. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x6ed6c) M (seg_rom BSEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & Evm & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _ & _ & _ & Eeg).
    remember (fr_b1 MU S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22)) as Mz eqn:EMz.
    remember (fr_P1 MIr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as M3 eqn:EM3 in FOOTU, GRU.
    set (Mfin := munrestrict Hd M Mz).
    (* [comment removed for export] *)
    set (MI := fr_init M b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4).
    assert (VISI : forall x : word, Hd x = true -> init_out x).
    { intros x Hx. pose proof (u64_range x) as Rx. (lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end).
      destruct (Z_lt_le_dec (U x) AIMGLO) as [L|L]; [lia|]. destruct (Z_lt_le_dec (U x) AIMGHI) as [H'|H']; [|lia].
      exfalso. rewrite <- (Z_to_bv_bv_unsigned 64 x) in Hx. rewrite (NHs (U x)) in Hx; [discriminate | lia | right; lia]. }
    assert (EMI : forall a : word, Hd a = false -> MIr a = MI a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold MIr, MI in G in change_no_check G' end). apply (fr_init_pw b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. exact Ha. }
    pose proof (fr_init_grows b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 M) as GRMI. change (mem_grows M MI) in GRMI.
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (rewrite CP2; lia).
    assert (Mb3210 : M (at_ (Z_to_bv 64 T) 3168) = Some (Z_to_bv 8 0)).
    { replace (at_ (Z_to_bv 64 T) 3168) with (Z_to_bv 64 (T + T_UNW)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_UNW in G in change_no_check G' end); wd_ulia).
      change (Z_to_bv 8 0) with (Z_to_bv 8 (U (Z_to_bv 64 0))). apply rdn1_offimg; [(lazymatch goal with |- ?G => let G' := eval unfold T_UNW in G in change_no_check G' end); wd_ulia | exact Tunw]. }
    assert (MUb3210 : MU (at_ (Z_to_bv 64 T) 3168) = Some (Z_to_bv 8 0)) by (apply rdn1_offimg; [(lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia | exact UUNW]).
    assert (Ib3210 : MIr (at_ (Z_to_bv 64 T) 3168) = Some (Z_to_bv 8 0)).
    { (lazymatch goal with |- ?G => let G' := eval unfold MIr in G in change_no_check G' end). rewrite (fr_init_out _ _ _ _ _ _ _ En1 En2 En3 En4) by ((lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off; [exact Mb3210 | rewrite <- (Z_to_bv_bv_unsigned 64 (at_ _ _)); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; apply NHrt; lia]. }
    pose proof (fr_P1_grows' MIr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as GRr3. feed GRr3. rewrite <- EM3 in GRr3.
    assert (GRIz : mem_grows MIr Mz).
    { eapply mem_grows_trans; [exact GRr3|]. eapply mem_grows_trans; [exact GRU|]. subst Mz. (lazymatch goal with |- ?G => let G' := eval unfold fr_b1 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
    assert (GRfinI : mem_grows MI Mfin).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Mfin, munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:Ex.
      - unfold MI in Hx. rewrite (fr_init_out b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 En1 En2 En3 En4) in Hx by (apply VISI; exact Ex). exact Hx.
      - apply GRIz. rewrite (EMI x Ex). exact Hx. }
    assert (GRfin : mem_grows M Mfin) by (eapply mem_grows_trans; [exact GRMI | exact GRfinI]).
    (* [comment removed for export] *)
    pose proof (fr_P1_foot MIr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as P1F. feed P1F. rewrite <- EM3 in P1F.
    assert (DIFFI : forall a : word, Mfin a <> MI a -> U S - 2304 <= U a < U S).
    { intros a NE. pose proof (u64_range a) as Ha. unfold Mfin, munrestrict in NE. destruct (Hd a) eqn:Eh.
      { exfalso. apply NE. symmetry. (lazymatch goal with |- ?G => let G' := eval unfold MI in G in change_no_check G' end). apply (fr_init_out b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 En1 En2 En3 En4). apply VISI. exact Eh. }
      rewrite <- (EMI a Eh) in NE.
      destruct (decide (Mz a = MU a)) as [Ez|Nz].
      - rewrite Ez in NE. destruct (decide (MU a = M3 a)) as [EU|NU].
        + rewrite EU in NE. pose proof (P1F a NE). lia.
        + destruct (FOOTU a NU) as [F|[F|[F|F]]]; try lia.
          exfalso. apply NE. replace a with (at_ (Z_to_bv 64 T) 3168) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). rewrite MUb3210, Ib3210. reflexivity.
      - subst Mz. unfold fr_b1 in Nz.
        assert (OUT : (U a < U S - 2192 \/ U S - 2128 <= U a) -> False).
        { intros Hx. apply Nz. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity. }
        destruct (decide (U S - 2192 <= U a < U S - 2128)); [lia | exfalso; apply OUT; lia]. }
    assert (DIFF : forall a : word, Mfin a <> M a -> (U S - 2304 <= U a < U S) \/ ~ init_out a).
    { intros a NE. destruct (decide (Mfin a = MI a)) as [E|N]; [| left; exact (DIFFI a N)].
      right. intros IO. apply NE. rewrite E. (lazymatch goal with |- ?G => let G' := eval unfold MI in G in change_no_check G' end). apply (fr_init_out b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 En1 En2 En3 En4). exact IO. }
    assert (DEF : forall a : word, Mfin a <> M a -> Mfin a <> None).
    { intros a NE. destruct (decide (Mfin a = MI a)) as [E|N].
      - rewrite E. apply (fr_init_some b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 M a). change (MI a <> M a). rewrite <- E. exact NE.
      - pose proof (DIFFI a N) as ST. apply GRfin. apply store_ok1_heap; [lia|]. apply CPstk. rewrite <- CP2. lia. }
    (* [comment removed for export] *)
    assert (IMG : forall a : word, ~ init_out a -> Mfin a = MI a).
    { intros a NIO. destruct (decide (Mfin a = MI a)) as [E|N]; [exact E|]. exfalso. pose proof (DIFFI a N). pose proof (u64_range a). apply NIO. (lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold free_post, cfg in G in change_no_check G' end). rewrite <- CP1.
    exists fx, rZ, Mfin, mdl1.
    split; [reflexivity|]. split; [exact HFX|].
    split; [apply regs_kept_intro; rewrite ?X2, ?X3, ?X4, ?X8, ?X9, ?X18, ?X19, ?X20, ?X21, ?X22, ?X23, ?X24, ?X25, ?X26, ?X27; reflexivity|].
    split.
    { intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold as_changed in G in change_no_check G' end). destruct (DIFF a NE) as [ST|NIO]; [left; rewrite <- CP2; (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end); lia|].
      right. right. left. exists 0x10ee9a, 0x19fce8. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); do 4 right; left; reflexivity|]. pose proof (u64_range a). unfold init_out in NIO. lia. }
    split; [intros a _ Da; apply GRfin; exact Da|].
    split.
    { intros a Ha. rewrite <- CP2 in Ha. unfold MSTK_A in Ha. split.
      + apply GRfin. apply store_ok1_heap; [lia|]. apply CPstk. rewrite <- CP2. lia.
      + eapply store_ok_mono; [exact GRfin|]. apply CPstk. rewrite <- CP2. lia. }
    split.
    { (* [comment removed for export] *)
      exists (set_ialloc st). split; [apply WF_ialloc_init; exact W|]. split; [| split; [split; [exact BD | exact (hp_ia bt HP HPc FAM h st HLE)] | exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)]].
      apply (OPS_IA4 st Lc FF M Mfin mdl1 W (Rep_sbm bt st Lc FF M mdl mdl1 RP MI1 SBM1) IA).
      - intros a NE. split; [| exact (DEF a NE)]. pose proof (u64_range a) as Ra. (lazymatch goal with |- ?G => let G' := eval unfold foot_ialloc4, IA_FLAG, IA_INST, IASZ in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_flag ia_ialloc_inst both_addrs] in G in change_no_check G' end).
        destruct (DIFF a NE) as [ST|NIO]; [right; right; clear - ST CP2 CPlo; lia|]. unfold init_out in NIO.
        destruct (Z_lt_le_dec (U a) 0x10f3c0) as [A1|A1]; [| destruct (Z_lt_le_dec (U a) 0x1903f0) as [A2|A2]; [right; left; lia|]];
          (destruct (Z_lt_le_dec (U a) 0x19dc48) as [A3|A3]; [| destruct (Z_lt_le_dec (U a) 0x19dc4c) as [A4|A4]; [left; lia|]]); exfalso; apply NIO; lia.
      - rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN, IA_FLAG in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_flag both_addrs] in G in change_no_check G' end).
        apply (rd_same BSEGS Mfin MI); [intros x Hx; apply IMG; (lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end); revert Hx; unorm; intros Hx; lia | wd_ulia | apply (fr_init_flag b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4)].
      - rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN, IA_FLAG in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_flag both_addrs Z.add Pos.add Pos.succ] in G in change_no_check G' end).
        apply (rd_same BSEGS Mfin MI); [intros x Hx; apply IMG; (lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end); revert Hx; unorm; intros Hx; lia | wd_ulia | apply (fr_init_lock b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4)].
      - rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold fillZ, byteZ, cellN, IA_INST in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_inst both_addrs] in G in change_no_check G' end). intros i Hi.
        apply (rd_same BSEGS Mfin MI); [intros x Hx; apply IMG; (lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end); revert Hx; unorm; intros Hx; lia | wd_ulia | apply (fr_init_map1 b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4); first [assumption | lia]].
      - rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, IA_INST in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_inst both_addrs Z.add Pos.add Pos.succ] in G in change_no_check G' end). change (Z_to_bv 64 PG) with (Z_to_bv 64 4096 : word).
        apply (rd_same BSEGS Mfin MI); [intros x Hx; apply IMG; (lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end); revert Hx; unorm; intros Hx; lia | wd_ulia | apply (fr_init_pgcell b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4)].
      - rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, IA_INST in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_inst both_addrs Z.add Pos.add Pos.succ] in G in change_no_check G' end).
        apply (rd_same BSEGS Mfin MI); [intros x Hx; apply IMG; (lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end); revert Hx; unorm; intros Hx; lia | wd_ulia | apply (fr_init_chunks b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4)]. }
    split; [apply same_but_materialized_except_vm; exact SBM1|].
    split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz; reflexivity|].
    rewrite Ehl. exact HH.
  Qed.
End TOP0I.
