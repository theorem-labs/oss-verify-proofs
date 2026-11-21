(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require IConj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit Require S9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S Require SBase S_ZB S_GroupB.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame Hoare AllocSim.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require MstepsGrows.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S Require S_Entry S_ZA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require ZStep ZMem ZTac ZPrune ZSysLite ZCall ZCallL ZArr ZRd IGlue IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S Require Base.

Module S_ZC.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Frame OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Hoare OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.AllocSim.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.S9LibStmt.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.ZStep OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.ZPrune OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.ZSysLite OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.ZRd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IGlue OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.MstepsGrows.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.Base.
Import ListNotations. Open Scope bv_scope. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

(* 1.4: uncompress2_z's epilogue (0x14eac): ld ra, s0 .. s4 (frame 160, no s5), addi, ret. *)
Definition L_EPI_S : Z := 0x14f0c.

End FXG.
Ltac zreg := cbv [zget_l kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                  kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6];
             cbn [alookup Pos.eqb]; rewrite ?zget_zupd; cbv [zget_l]; cbn [alookup Pos.eqb];
             zrefold_getl; zbase; first [ reflexivity | assumption | OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.ITac.zarith_goal; lia ].
Ltac zkeys := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in *.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Section ZC.

Lemma zc_epi : forall Rb l M MD T (u v0 v1 v2 v3 v4 v5 : Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u ->
  S9_IMG_TOP <= u - 16 -> u + 208 <= 2 ^ 47 ->
  mem_u64 R_segs M (u + 152) S9_HARN_RA ->
  mem_u64 R_segs M (u + 144) v0 -> mem_u64 R_segs M (u + 136) v1 -> mem_u64 R_segs M (u + 128) v2 ->
  mem_u64 R_segs M (u + 120) v3 -> mem_u64 R_segs M (u + 112) v4 ->
  (forall lc,
     zget_l Rb lc kSP = u + 160 ->
     zget_l Rb lc kS0 = v0 -> zget_l Rb lc kS1 = v1 -> zget_l Rb lc kS2 = v2 ->
     zget_l Rb lc kS3 = v3 -> zget_l Rb lc kS4 = v4 -> zget_l Rb lc kS5 = zget_l Rb l kS5 ->
     zget_l Rb lc kGP = zget_l Rb l kGP -> zget_l Rb lc kTP = zget_l Rb l kTP ->
     zget_l Rb lc kS6 = zget_l Rb l kS6 -> zget_l Rb lc kS7 = zget_l Rb l kS7 -> zget_l Rb lc kS8 = zget_l Rb l kS8 ->
     zget_l Rb lc kS9 = zget_l Rb l kS9 -> zget_l Rb lc kS10 = zget_l Rb l kS10 -> zget_l Rb lc kS11 = zget_l Rb l kS11 ->
     realizes R_segs (zcfg R_segs S9_HARN_RA (zupd Rb lc) M MD) T) ->
  realizes R_segs (zcfg R_segs L_EPI_S (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u v0 v1 v2 v3 v4 v5 Hh Lsp Hc1 Hc2 H152 H144 H136 H128 H120 H112 K.
  zkeys. unfold S9_IMG_TOP, S9_HARN_RA, L_EPI_S in *. pose proof two64_eq as TW64.
  zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* ld ra; ld s0 .. s4 *)
  zstep Rfd.                          (* addi sp,sp,160 *)
  zret Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?lc) _ _) _ => apply (K lc) end; zreg.
Qed.

Lemma zsetreg_lemma : forall segs pc Rb k (e v : Z) rest M MD T, v = e ->
  realizes segs (zcfg segs pc (zupd Rb ((k, v) :: rest)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb ((k, e) :: rest)) M MD) T.
Proof. intros. subst. assumption. Qed.
Ltac zsetreg v tac := eapply (zsetreg_lemma _ _ _ _ _ v); [tac|].

(* 1.4: inflateEnd's tail from the zfree return (S9_ZC), back in uncompress2_z at RA2: the err in s0 (inflateEnd
   restores it) is mapped (Z_STREAM_END -> Z_OK, Z_NEED_DICT -> Z_DATA_ERROR, Z_BUF_ERROR with len + avail_in = 0 ->
   Z_DATA_ERROR), then the epilogue. Every branch reaches the epilogue; the return value is not stated. *)
Lemma zc_cps : forall Rb l M MD T (u v0 v1 v2 v3 v4 v5 s16 s3v : Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + (-16) -> zget_l Rb l kS0 = u ->
  zget_l Rb l kS3 = s3v -> 0 <= s16 < two64 -> 0 <= s3v < two64 ->
  S9_IMG_TOP <= u - 16 -> u + 208 <= 2 ^ 47 ->
  mem_wr R_segs M (u + (-16)) 224 ->
  mem_u64 R_segs M (u + (-8)) S9_RA2 -> mem_u64 R_segs M (u + (-16)) s16 ->
  mem_u64 R_segs M (u + 152) S9_HARN_RA ->
  mem_u64 R_segs M (u + 144) v0 -> mem_u64 R_segs M (u + 136) v1 -> mem_u64 R_segs M (u + 128) v2 ->
  mem_u64 R_segs M (u + 120) v3 -> mem_u64 R_segs M (u + 112) v4 ->
  (forall lc M',
     mpost R_segs M M' (u + 56) (u + 64) 0 0 -> mem_u64 R_segs M' (u + 56) 0 ->
     zget_l Rb lc kSP = u + 160 ->
     zget_l Rb lc kS0 = v0 -> zget_l Rb lc kS1 = v1 -> zget_l Rb lc kS2 = v2 ->
     zget_l Rb lc kS3 = v3 -> zget_l Rb lc kS4 = v4 -> zget_l Rb lc kS5 = zget_l Rb l kS5 ->
     zget_l Rb lc kGP = zget_l Rb l kGP -> zget_l Rb lc kTP = zget_l Rb l kTP ->
     zget_l Rb lc kS6 = zget_l Rb l kS6 -> zget_l Rb lc kS7 = zget_l Rb l kS7 -> zget_l Rb lc kS8 = zget_l Rb l kS8 ->
     zget_l Rb lc kS9 = zget_l Rb l kS9 -> zget_l Rb lc kS10 = zget_l Rb l kS10 -> zget_l Rb lc kS11 = zget_l Rb l kS11 ->
     realizes R_segs (zcfg R_segs S9_HARN_RA (zupd Rb lc) M' MD) T) ->
  realizes R_segs (zcfg R_segs S9_ZC (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u v0 v1 v2 v3 v4 v5 s16 s3v Hh Lsp Ls0 Ls3 Rs16 Rs3 Hc1 Hc2
         WR H8 H16 H152 H144 H136 H128 H120 H112 K.
  zkeys. unfold S9_IMG_TOP, S9_HARN_RA, S9_RA2, S9_ZC, L_EPI_S in *. pose proof two64_eq as TW64.
  pose proof (mpost_refl R_segs M (u + 56) (u + 64) 0 0 : framed (fun X => mpost R_segs M X (u + 56) (u + 64) 0 0) M) as HAG.
  pose proof (mpost_stable R_segs M (u + 56) (u + 64) 0 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HST.
  zstep Rfd.                          (* 17184 li a0,0 *)
  zstep Rfd.                          (* 17188 sd zero,56(s0) *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (EPI : forall lc, zget_l Rb lc 3 = u ->
     zget_l Rb lc 4 = zget_l Rb l 4 -> zget_l Rb lc 5 = zget_l Rb l 5 -> zget_l Rb lc 22 = zget_l Rb l 22 ->
     zget_l Rb lc 23 = zget_l Rb l 23 -> zget_l Rb lc 24 = zget_l Rb l 24 -> zget_l Rb lc 25 = zget_l Rb l 25 ->
     zget_l Rb lc 26 = zget_l Rb l 26 -> zget_l Rb lc 27 = zget_l Rb l 27 -> zget_l Rb lc 28 = zget_l Rb l 28 ->
     realizes R_segs (zcfg R_segs L_EPI_S (zupd Rb lc) Mc MD) T) end.
  { intros lc Gsp G4 G5 G22 G23 G24 G25 G26 G27 G28.
    eapply (zc_epi Rb lc _ MD T u v0 v1 v2 v3 v4 v5 Hh Gsp Hc1 Hc2 H152 H144 H136 H128 H120 H112).
    intros lc2 Q3 Q9 Q10 Q19 Q20 Q21 Q22 Q4 Q5 Q23 Q24 Q25 Q26 Q27 Q28.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mq _) _ => apply (K lc2 Mq) end;
      first [ exact HAG | assumption | etransitivity; eassumption ]. }
  zstep Rfd.                          (* 1718c ld ra,8(sp) *)
  zstep Rfd.                          (* 17190 ld s0,0(sp) *)
  zstep Rfd.                          (* 17194 addi sp,sp,16 *)
  zret Rfd.                           (* 17198 ret: RA2 *)
  Local Ltac to_epi EPI := lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?lc) _ _) _ => apply (EPI lc) end; zreg.
  zstep Rfd.                          (* 14e80 li a1,1 *)
  destruct (Z.eq_dec s16 1) as [E1|N1]; [zbr Rfd true | zbr Rfd false].   (* beq s0,a1: Z_STREAM_END *)
  { zstep Rfd. to_epi EPI. }          (* li a0,0 *)
  zstep Rfd. zstep Rfd.               (* mv a0,s0; li a1,2 *)
  destruct (Z.eq_dec s16 2) as [E2|N2]; [zbr Rfd true | zbr Rfd false].   (* beq s0,a1: Z_NEED_DICT *)
  { zstep Rfd. zstep Rfd. to_epi EPI. }   (* li a0,-3; j *)
  zstep Rfd. zstep Rfd.               (* xori a1,a0,-5; or a1,a1,s3 *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => destruct (Z.eq_dec (e mod 18446744073709551616) 0) as [Ez|Ez] end; [zbr Rfd false | zbr Rfd true].
  2: { to_epi EPI. }
  zstep Rfd. zstep Rfd. to_epi EPI.   (* li a0,-3; j *)
Qed.
End ZC.


Definition MD0 : Model := mkModel [] (mkVmMaps [] [] (Z_to_bv 64 0) (Z_to_bv 64 0) 0) IEof [] None None None.
Lemma MD0_halted : m_halted MD0 = None.
Proof. reflexivity. Qed.

Theorem zc_s : zc_stmt_S9.
Proof.
  unfold zc_stmt_S9.
  intros regs mem u v0 v1 v2 v3 v4 v5 Hsp Hs0 Hal Hceil Htop ST R8 R152 R144 R136 R128 R120 R112.
  pose proof Hceil as Hc'. unfold S9_IMG_TOP in Hc'.
  set (Rb := zlift regs).
  assert (Gk : forall r : reg, bv_eqb r 0%bv = false -> zget_l Rb [] (bv_key r) = bv_unsigned (getr regs r)).
  { intros r Hr. cbv [zget_l alookup]. subst Rb. rewrite zget_zlift, (getr_reg_get regs r Hr). reflexivity. }
  assert (Lsp : zget_l Rb [] kSP = u + (-16)).
  { change kSP with (bv_key (2%bv : reg)). rewrite Gk by reflexivity. rewrite Hsp.
    change (Z_to_bv 64 (u - 16)) with (w64 (u - 16)). rewrite w64_unsigned, mod_small_u64 by lia. lia. }
  assert (Ls0 : zget_l Rb [] kS0 = u).
  { change kS0 with (bv_key (8%bv : reg)). rewrite Gk by reflexivity. rewrite Hs0.
    change (Z_to_bv 64 (u)) with (w64 (u)). rewrite w64_unsigned, mod_small_u64 by lia. lia. }
  pose proof (u64_range (getr regs 19)) as Rs3.
  pose proof (mem_wr_of_store_ok _ _ _ _ ST) as WR. rewrite Z2Nat.id in WR by lia.
  change (mem_wr R_segs mem (u - 16) 224) in WR.
  destruct (mem_wr_u64_exists_R mem (u + (-16)) ltac:(eapply mem_wr_sub; [exact WR | lia | lia])) as (s16 & H16 & Rs16).
  set (Q := fun c : config => exists lc M',
    c = zcfg R_segs S9_HARN_RA (zupd Rb lc) M' MD0
    /\ mpost R_segs mem M' (u + 56) (u + 64) 0 0
    /\ zget_l Rb lc kSP = u + 160
    /\ zget_l Rb lc kS0 = bv_unsigned v0 /\ zget_l Rb lc kS1 = bv_unsigned v1 /\ zget_l Rb lc kS2 = bv_unsigned v2
    /\ zget_l Rb lc kS3 = bv_unsigned v3 /\ zget_l Rb lc kS4 = bv_unsigned v4 /\ zget_l Rb lc kS5 = zget_l Rb [] kS5
    /\ zget_l Rb lc kGP = zget_l Rb [] kGP /\ zget_l Rb lc kTP = zget_l Rb [] kTP
    /\ zget_l Rb lc kS6 = zget_l Rb [] kS6 /\ zget_l Rb lc kS7 = zget_l Rb [] kS7 /\ zget_l Rb lc kS8 = zget_l Rb [] kS8
    /\ zget_l Rb lc kS9 = zget_l Rb [] kS9 /\ zget_l Rb lc kS10 = zget_l Rb [] kS10 /\ zget_l Rb lc kS11 = zget_l Rb [] kS11).
  assert (HR : realizes R_segs (zcfg R_segs S9_ZC (zupd Rb []) mem MD0) Q).
  { eapply (zc_cps Rb [] mem MD0 Q u (bv_unsigned v0) (bv_unsigned v1) (bv_unsigned v2) (bv_unsigned v3)
              (bv_unsigned v4) (bv_unsigned v5) s16 (bv_unsigned (getr regs 19)) MD0_halted Lsp Ls0).
    - change kS3 with (bv_key (19%bv : reg)). apply Gk. reflexivity.
    - exact Rs16.
    - exact Rs3.
    - exact Hceil.
    - exact Htop.
    - exact WR.
    - exact R8.
    - exact H16.
    - exact R152. - exact R144. - exact R136. - exact R128. - exact R120. - exact R112.
    - intros lc M' HP HM Q3 Q9 Q10 Q19 Q20 Q21 Q22 Q4 Q5 Q23 Q24 Q25 Q26 Q27 Q28.
      apply rz_now. subst Q. cbv beta. exists lc, M'.
      repeat (split; [first [reflexivity | assumption] |]). assumption. }
  dand HR as (ms' & RUN & HQ). subst Q. cbv beta in HQ. cbn [cfg_ms cfg_model zcfg] in RUN, HQ.
  dand HQ as (lc & M' & E & HP & Q3 & Q9 & Q10 & Q19 & Q20 & Q21 & Q22 & Q4 & Q5 & Q23 & Q24 & Q25 & Q26 & Q27 & Q28).
  unfold zcfg in E. injection E as E1. subst ms'.
  exists (zden (zupd Rb lc)), M'.
  assert (GET : forall (r : reg) k v, bv_eqb r 0%bv = false -> bv_key r = k -> zget_l Rb lc k = v ->
                getr (zden (zupd Rb lc)) r = w64 v).
  { intros r k v Hr Hk Hv. rewrite (getr_zupd Rb lc r Hr), Hk, Hv. reflexivity. }
  assert (KEEP : forall (r0 : reg) k, bv_eqb r0 0%bv = false -> bv_key r0 = k -> zget_l Rb lc k = zget_l Rb [] k ->
            getr (zden (zupd Rb lc)) r0 = getr regs r0).
  { intros r0 k Hr0 Hk HQk. rewrite (GET r0 k _ Hr0 Hk HQk). rewrite <- Hk, (Gk r0 Hr0). apply w64_of_word. }
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
  - unfold zst in RUN. cbn [zupd] in RUN. subst Rb. rewrite zden_zlift in RUN. exact RUN.
  - replace 8 with (u + 64 - (u + 56)) by lia.
    apply (frame_mod_of_mpost R_segs); [lia | lia | exact HP |].
    pose proof (msteps_mem_grows R_segs _ _ RUN) as G. unfold zst in G. cbn [ms_mem] in G. exact G.
  - rewrite (GET 2%bv kSP (u + 160) eq_refl eq_refl Q3). reflexivity.
  - rewrite (GET 8%bv kS0 _ eq_refl eq_refl Q9). apply w64_of_word.
  - rewrite (GET 9%bv kS1 _ eq_refl eq_refl Q10). apply w64_of_word.
  - rewrite (GET 18%bv kS2 _ eq_refl eq_refl Q19). apply w64_of_word.
  - rewrite (GET 19%bv kS3 _ eq_refl eq_refl Q20). apply w64_of_word.
  - rewrite (GET 20%bv kS4 _ eq_refl eq_refl Q21). apply w64_of_word.
  - eapply KEEP; [reflexivity | reflexivity | exact Q22].
  - intros r Hr. unfold S_ENTRY in Hr. cbn [app] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ eapply KEEP; [ reflexivity | reflexivity
                     | first [ exact Q4 | exact Q5 | exact Q23 | exact Q24 | exact Q25 | exact Q26 | exact Q27 | exact Q28 ] ] |]).
    destruct Hr.
Qed.
End FXG.
End S_ZC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S Require S_Type S_Check.

Module S_Head.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_Check.S_HeadA.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_HEAD_LOOP : Z := 87028.
Definition L_HEAD_BODY : Z := 89476.
Definition L_HEAD_WERR : Z := 93292.
Definition L_HEAD_FIN : Z := 93456.

End FXG.
Ltac zbr_hyp_with bv F E D :=
  eapply (zu_branch_b bv); [zexact F | zexact E | zexact D | zhalted | znorm; first [assumption | zcond_tac] | ];
  zcbv_iota; znorm.
Tactic Notation "zbrH" tactic0(fd) constr(bv) :=
  let pc := zpc in fd pc ltac:(fun F E D => zbr_hyp_with bv F E D).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition fp_head (u p : Z) : list (Z * Z) := [(p + 8, 4); (p + 28, 20); (u + 48, 8); (u + 96, 8)].

Section WITH_ADLER_NULL.
Hypothesis ADLN : adler32_null_spec_s.

Lemma head_main : forall cx fin MD T M0 Rb l M st lf cf (cin1 hold1 bits1 : Z),
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = HEAD -> sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -224 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kA0 = c_u cx -> zget_l Rb l kA1 = 0 ->
  zget_l Rb l kS6 = c_p cx + 168 -> zget_l Rb l kT6 = -16180 -> zget_l Rb l kT4 = 30 -> zget_l Rb l kS9 = JTAB_ADDR ->
  zget_l Rb l kS4 = 16209 -> zget_l Rb l kA2 = 5 ->
  zget_l Rb l kS2 = c_n cx - cin1 -> zget_l Rb l kS3 = c_ob cx + t_cout st -> zget_l Rb l kRA = c_osz cx - t_cout st ->
  zget_l Rb l kS11 = c_q cx + cin1 -> zget_l Rb l kS10 = c_q cx + cin1 ->
  zget_l Rb l kS7 = hold1 -> zget_l Rb l kS8 = bits1 ->
  t_cin st <= cin1 <= c_n cx -> 16 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
  8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_HEAD_BODY (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf cin1 hold1 bits1 CX Hh Hfin Hm SI
         LSP LGP LTP L9 LA0 LA1 LRA LT6 LT4 LT5 L5 LA2 L8 L3 L2 L10 L11 L7 L0 Hc1 Hb1 Hh1 Hbc1 HW1 KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof KM as KM0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags t_cin t_cout t_hold t_bits t_out] in *. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh64.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & _ & H48 & H56 & _).
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q104 & Q96 & _ & Q72 & _).
  pose proof (rom_mod31_u64 M ROM) as H31.
  pose proof SREST as SR'. unfold st_rest in SR'. icx_cbn. dand SR' as (_ & H24 & _).
  clear ROM Wob Ww FRM CST HK Hmode SREST SRET SOUT Hlens Hcodes Hin.
  zkeysb. unfold L_HEAD_BODY, L_HEAD_WERR, L_HEAD_FIN, L_BADMSG_S11 in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (mpostL_stable R_segs M (fp_head u p) ltac:(unfold fp_head; ranges_ok_tac)) as HSTh.
  assert (HAGh : framed (fun X => mpostL R_segs M X (fp_head u p)) M) by (apply mpostL_refl).
  unfold fp_head in HSTh, HAGh.
  assert (EXIT : forall (ra1 : bool) RX Mq m' flags' hold' bits',
    sinv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                m' flags' cin1 hold' bits') lf cf ->
    meas (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                m' flags' cin1 hold' bits') <
    meas (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ->
    zget RX kSP = u + -224 -> zget RX kGP = K0 kGP -> zget RX kTP = K0 kTP -> zget RX kS0 = p ->
    zget RX kA0 = u -> zget RX kS4 = 16209 -> zget RX kS10 = q + cin1 -> zget RX kS2 = n - cin1 ->
    zget RX kS3 = ob + cout -> zget RX kS1 = osz - cout -> zget RX kS7 = hold' -> zget RX kS8 = bits' ->
    zget RX kS6 = p + 168 -> zget RX kS9 = 67008 -> (ra1 = true -> zget RX kA1 = 0) ->
    mem_u32 R_segs Mq (p + 8) m' -> mem_u32 R_segs Mq (p + 28) flags' ->
    mpostL R_segs M Mq [(p + 8, 4); (p + 28, 20); (u + 48, 8); (u + 96, 8)] ->
    realizes R_segs (zcfg R_segs (if ra1 then L_RELOAD_RA else L_RELOAD_A1) (zupd RX []) Mq MD) T).
  { intros ra1 RX Mq m' flags' hold' bits' SI1 MB1 E3 E4 E5 E26 E11 E22 E28 E25 E20 E19 E24 E9 E21 E27 EA1 Hm8 Hf24 HPq.
    clear HST HAG Wstk Wp HSTh HAGh H48 H56 H31 Q104 Q96 Q72 H24.
    open_kmem KM0. open_std STD. destruct SAT as [Hmode SREST]. clear Hmode.
    unfold st_rest in SREST. icx_cbn.
    dand SREST as (H12 & _ & H64 & H68 & H92 & H96 & H100 & H104 & H112 & H120 & H124 & H128 & H132 & H136 & H140 & H144).
    fp_frame_from HP0.
    cbv [N_LENS N_CODES] in Hlens, Hcodes.
    zreattachL HPq.
    destruct ra1;
      [ change (if true then L_RELOAD_RA else L_RELOAD_A1) with L_RELOAD_RA;
        eapply (KRRA RX Mq (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                              m' flags' cin1 hold' bits') lf cf SI1 MB1)
      | change (if false then L_RELOAD_RA else L_RELOAD_A1) with L_RELOAD_A1;
        eapply (KRA1 RX Mq (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                              m' flags' cin1 hold' bits') lf cf SI1 MB1) ].
    1,3: unfold s_regs_reload, hd_st; icx_cbn; zkeys; split_conj; first [assumption | intros; discriminate | solve [intros _; apply EA1; reflexivity] | zreg].
    all: unfold k_mem; split_conj;
      [ close_std
      | unfold st_at, st_rest, hd_st; icx_cbn; split_conj; assumption
      | unfold s_ret, hd_st in *; icx_cbn; assumption | unfold s_out, hd_st in *; icx_cbn; assumption
      | assumption | assumption | exact HAG ]. }
  zstep Rfd. zlit.
  zbr Rfd true.
  tstep1 Rfd.
  zbr Rfd true.
  zstep Rfd. zlit.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zlit.
  zstep Rfd.
  zstep Rfd. zlit.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd. zlit.
  zstep Rfd. zlit.
  zstep Rfd.
  zgenreg pr.
  clear H31 H48.
  destruct (zcond BC_LTU pr 595056260442243601) eqn:Hc31.
  2: {
    zbrH Rfd false.
    zstep Rfd. zstep Rfd. zlit.
    zstep Rfd.
    pose proof (sinv_hd _ _ lf cf BAD flags cin1 hold1 bits1 SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(intros _; right; reflexivity)
                  ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  BAD flags cin1 hold1 bits1 ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MB1.
    clear HSTh HAGh H56 Q104 Q96 Q72 H24 EXIT. open_kmem KM0. destruct SAT as [Hmode SREST].
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KB11 R' Mx (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                                  HEAD flags cin1 hold1 bits1) lf cf SI1 MB1) end.
    - unfold s_regs_disp, s_fix, s_vars, hd_st; icx_cbn; zkeys; split_conj; zreg.
    - lazymatch goal with |- 0 <= ?x < _ => assert (EA2 : x = 66636) by zreg; rewrite EA2 end. lia.
    - unfold k_mem, hd_st; icx_cbn; split_conj;
        [ exact STD | split; [exact Hmode | exact SREST] | exact SRET | exact SOUT | exact Hlens | exact Hcodes | exact HP0 ]. }
  zbrH Rfd true.
  zstep Rfd.
  zstep Rfd.
  zgenreg mth.
  zstep Rfd.
  destruct (zcond BC_NE mth 8) eqn:Hcm.
  {
    zbrH Rfd true.
    clear H56.
    zstep Rfd. zstep Rfd. zlit.
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    pose proof (sinv_hd _ _ lf cf BAD flags cin1 hold1 bits1 SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(intros _; right; reflexivity)
                  ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  BAD flags cin1 hold1 bits1 ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?Mx _) _ => apply (EXIT false RX Mx BAD flags hold1 bits1 SI1 MB1) end;
      first [zreg | assumption | intros; discriminate | exact HAGh]. }
  zbrH Rfd false.                     (* bne a0,a1: the method is 8 *)
  (* 1.4 (the HEAD rider): len = BITS(4) + 8 is checked against 15 first, then against wbits only when wbits != 0,
     and wbits is set to len only when it was 0 (1.3.1 set it before the check). Here wbits = 15, so the state is as at
     1.3.1; only the instruction order moved. *)
  zstep Rfd.                          (* 16bec srli a1,s7,4 *)
  zsetreg (Z.shiftr hold1 4) ltac:(rewrite (Z.mod_small hold1) by lia; reflexivity).
  zstep Rfd.                          (* 16bf0 andi a0,a1,15 *)
  zgenreg len4.
  zstep Rfd.                          (* 16bf4 li a2,7 *)
  pose proof (shiftr_lt_pow2 hold1 bits1 4 ltac:(lia) Hh1) as Hsh4.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (WERR : forall RW,
    zget RW kSP = u + -224 -> zget RW kGP = K0 kGP -> zget RW kTP = K0 kTP -> zget RW kS0 = p ->
    zget RW kS4 = 16209 -> zget RW kS2 = n - cin1 -> zget RW kS3 = ob + cout -> zget RW kS1 = osz - cout ->
    zget RW kS10 = q + cin1 -> zget RW kS8 = bits1 -> zget RW kA1 = Z.shiftr hold1 4 ->
    zget RW kS6 = p + 168 -> zget RW kS9 = 67008 ->
    realizes R_segs (zcfg R_segs L_HEAD_WERR (zupd RW []) Mc MD) T) end.
  { intros RW. intros. unfold L_HEAD_WERR. zkeys. clear H56.
    tstep1 Rfd.                       (* addiw s8,s8,-4 *)
    zstep Rfd. zstep Rfd. zlit.       (* auipc; addi: the message *)
    tstep1 Rfd.                       (* ld a0,96(sp) *)
    tstep1 Rfd.                       (* sd a2,48(a0) *)
    tstep1 Rfd.                       (* ld s4,72(sp) *)
    tstep1 Rfd.                       (* sw s4,8(s0) *)
    zstep Rfd.                        (* mv s7,a1 *)
    zstep Rfd.                        (* j *)
    pose proof (sinv_hd _ _ lf cf BAD flags cin1 (Z.shiftr hold1 4) (bits1 - 4) SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity)
                  ltac:(intros _; right; reflexivity)
                  ltac:(cbn; lia) ltac:(lia) ltac:(exact Hsh4) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  BAD flags cin1 (Z.shiftr hold1 4) (bits1 - 4) ltac:(left; cbn; lia)) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?Mx _) _ => apply (EXIT false RX Mx BAD flags (Z.shiftr hold1 4) (bits1 - 4) SI1 MB1) end;
      first [zreg | assumption | intros; discriminate | exact HAGh]. }
  destruct (zcond BC_LTU 7 len4) eqn:Hc7.
  { zbrH Rfd true.                    (* bltu a2,a0: len > 15 *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?RW _ _) _ => apply (WERR RW); zreg end. }
  zbrH Rfd false.
  tstep1 Rfd.                         (* 16bfc lw a3,68(s0): wbits *)
  zstep Rfd.                          (* 16c00 addi a2,a0,8 *)
  zgenreg lenp8.
  zbr Rfd false.                      (* 16c04 beqz a3: wbits = 15 *)
  destruct (zcond BC_GEU 15 lenp8) eqn:Hc15.
  2: { zbrH Rfd false.                (* bgeu a3,a2 not taken: len > wbits *)
       lazymatch goal with |- realizes _ (zcfg _ _ ?RW _ _) _ => apply (WERR RW); zreg end. }
  zbrH Rfd true.                      (* bgeu a3,a2 *)
  zbr Rfd true.                       (* 16c58 bnez a3: wbits kept *)
  clear WERR Hsh4.
  zstep Rfd.                          (* li a1,256 *)
  zstep Rfd.                          (* sllw a0,a1,a0 *)
  zgenreg dmax.
  tstep1 Rfd.                         (* sw zero,28(s0) *)
  tstep1 Rfd.                         (* sw a0,32(s0) *)
  zstep Rfd. zstep Rfd. zstep Rfd.   (* li a0; li a1; li a2 *)
  zstep Rfd.                          (* jal adler32 *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R ?lc') ?Mx _) _ =>
    eapply (ADLN R lc' Mx MD T _ Hh) end; [zreg | zreg | zreg | reflexivity |].
  intros R2 E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
  zimps. zkeys.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zgenreg hs.
  zstep Rfd. zlit.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (FIN : forall RF m', (m' = DICTID \/ m' = TYPE) ->
    zget RF kSP = u + -224 -> zget RF kGP = K0 kGP -> zget RF kTP = K0 kTP -> zget RF kS0 = p ->
    zget RF kS4 = 16209 -> zget RF kS2 = n - cin1 -> zget RF kS3 = ob + cout -> zget RF kS1 = osz - cout ->
    zget RF kS10 = q + cin1 -> zget RF kA0 = m' ->
    zget RF kS6 = p + 168 -> zget RF kS9 = 67008 ->
    realizes R_segs (zcfg R_segs L_HEAD_FIN (zupd RF []) Mc MD) T) end.
  { intros RF m' Hm'. intros. unfold L_HEAD_FIN. zkeys.
    assert (Rm' : 0 <= m' < 4294967296) by (destruct Hm' as [-> | ->]; cbv [DICTID TYPE]; lia).
    zstep Rfd. zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    pose proof (sinv_hd _ _ lf cf m' 0 cin1 0 0 SI0 eq_refl ltac:(destruct Hm' as [-> | ->]; (first [solve [zkeep_section; tauto] | tauto])) ltac:(right; reflexivity)
                  ltac:(intros E; discriminate E)
                  ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  m' 0 cin1 0 0 ltac:(left; cbn; lia)) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?Mx _) _ => apply (EXIT true RX Mx m' 0 0 0 SI1 MB1) end;
      first [zreg | assumption | intros _; zreg | exact HAGh]. }
  destruct (zcond BC_GE hs 0) eqn:Hcs.
  - zbrH Rfd true.
    zstep Rfd. zlit.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RF _ _) _ => apply (FIN RF TYPE); [right; reflexivity | zreg ..] end.
  - zbrH Rfd false.
    zstep Rfd. zlit.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RF _ _) _ => apply (FIN RF DICTID); [left; reflexivity | zreg ..] end.
Qed.


Lemma head_loop : forall (k : nat) cx fin MD T Rb l M (cinj holdj j : Z),
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_S cx ->
  16 - 8 * Z.of_nat k <= j < 24 - 8 * Z.of_nat k -> (1 <= k <= 2)%nat -> 0 <= j ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS8 = j -> zget_l Rb l kA3 = j ->
  zget_l Rb l kS11 = c_q cx + cinj -> zget_l Rb l kS2 = c_n cx - cinj -> zget_l Rb l kS7 = holdj ->
  mem_arr 1 R_segs M (c_q cx) (c_n cx) fin ->
  (forall R' hold' j',
     zget R' kS11 = c_q cx + c_n cx -> zget R' kS2 = 0 -> zget R' kS7 = hold' -> zget R' kS8 = j' ->
     j' = j + 8 * (c_n cx - cinj) -> 0 <= hold' < 2 ^ j' -> c_n cx - cinj < Z.of_nat k ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kA2 = zget_l Rb l kA2 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kS3 = zget_l Rb l kS3 ->
     zget R' kS4 = zget_l Rb l kS4 ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kT4 = zget_l Rb l kT4 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kT6 = zget_l Rb l kT6 ->
     realizes R_segs (zcfg R_segs L_LEAVE_LD (zupd R' []) M MD) T) ->
  (forall R' hold' j',
     zget R' kS11 = c_q cx + cinj + Z.of_nat k -> zget R' kS10 = c_q cx + cinj + Z.of_nat k ->
     zget R' kS2 = c_n cx - cinj - Z.of_nat k -> zget R' kS7 = hold' -> zget R' kS8 = j' ->
     j' = j + 8 * Z.of_nat k -> 0 <= hold' < 2 ^ j' -> Z.of_nat k <= c_n cx - cinj ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kA2 = zget_l Rb l kA2 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kS3 = zget_l Rb l kS3 ->
     zget R' kS4 = zget_l Rb l kS4 ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kT4 = zget_l Rb l kT4 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kT6 = zget_l Rb l kT6 ->
     realizes R_segs (zcfg R_segs L_HEAD_BODY (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_HEAD_LOOP (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M cinj holdj j Hh Hfin CXl Hj Hk Hj0 Hc Hhj Hjc L9 L0 LA3 L10 L8 L7 Hin KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S] in CXl; destr_conj CXl.
  zkeysb. unfold L_HEAD_LOOP, L_HEAD_BODY, L_LEAVE_LD in *. pose proof two64_eq as TW64.
  assert (Hj24 : 2 ^ j <= 2 ^ 23) by (apply Z.pow_le_mono_r; lia). change (2 ^ 23) with 8388608 in Hj24.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  -
    zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj j) end; try zreg; try lia.
    all: replace (j + 8 * (n - cinj)) with j by lia; lia.
  - zbr Rfd true.
    pose proof (Hfin cinj ltac:(lia)) as Hb0.
    zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (fin cinj * 2 ^ j) ltac:(rewrite (Z.mod_small j) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    pose proof (pullbyte_bound holdj j (fin cinj) ltac:(lia) Hhj Hb0) as Hpb.
    destruct k as [|k'].
    +
      zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KDN R' (fin cinj * 2 ^ j + holdj) (j + 8)) end; try zreg; try lia.
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') _ _) _ =>
        eapply (IH (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' M (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) Hh Hfin) end;
        [ unfold ctx_lin; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S]; split_conj; assumption || lia
        | lia | lia | lia | icx_cbn; lia | lia | icx_cbn; lia
        | (icx_cbn; zreg) .. | exact Hin | | ].
      * intros R' hold' j'. icx_cbn. intros. eapply KLV; try eassumption; try lia; try zkept.
      * intros R' hold' j'. icx_cbn. intros. eapply KDN; try eassumption; try lia; try zkept.
Qed.

Lemma head_body : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = HEAD -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_HEAD (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof KM as KM0. pose proof K as KA0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof (proj1 CX) as CXl. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags] in Hm. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & H16 & _).
  clear ROM Wob Ww FRM CST HK Hmode SREST SRET SOUT Hlens Hcodes.
  zkeysb. unfold L_HEAD, L_HEAD_LOOP, L_HEAD_BODY, L_LEAVE_LD in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  tstep1 Rfd.
  zbr Rfd false.
  zstep Rfd.
  destruct (Z_lt_dec 15 bits) as [Hb16 | Hb16].
  - zbr Rfd true.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (head_main (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf cin hold bits CX0 Hh Hfin eq_refl SI0) end;
      [ (icx_cbn; zreg) .. | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
  - zbr Rfd false.
    zstep Rfd.
    assert (Hkk : exists k : nat, 16 - 8 * Z.of_nat k <= bits < 24 - 8 * Z.of_nat k /\ (1 <= k <= 2)%nat).
    { exists (Z.to_nat (2 - bits / 8)).
      rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (head_loop k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' Mx cin hold bits Hh Hfin CXl Hk1 Hk2) end;
      [ lia | icx_cbn; lia | lia | lia | (icx_cbn; zreg) .. | exact Hin | | ].
    +
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_LEAVE_LD in *.
      pose proof (sinv_hd _ _ lf cf HEAD flags n hold' j' SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(intros _; left; reflexivity)
                    ltac:(cbn; lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia)) as SI1.
      clear H16. open_kmem KM0. destruct SAT as [Hmode SREST].
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KLL Rx Mx _ lf cf SI1) end.
      * unfold s_regs_leave_ld, hd_st; icx_cbn; zkeys; split_conj; try zreg; zkept.
      * exact STD.
      * unfold hd_st; split; [exact Hmode | exact SREST].
      * exact SRET.
      * exact SOUT.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_HEAD_BODY in *.
      eapply (head_main (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' [] M
                (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf (cin + Z.of_nat k) hold' j' CX0 Hh Hfin eq_refl SI0);
        [ (icx_cbn; first [zreg | zkeys; cbv [zget_l alookup]; first [zkept | lia]]) .. | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
Qed.

Theorem arm_HEAD_s : arm_stmt L_HEAD HEAD.
Proof. intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K. eapply head_body; eassumption. Qed.

End WITH_ADLER_NULL.
End FXG.
End S_Head.

Module S_HeadB.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_Check.S_HeadA.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_DICTID_LOOP : Z := 87212.
Definition L_DICTID_BODY : Z := 87680.

Section WITH_ADLER_NULL.
Hypothesis ADLN : adler32_null_spec_s.

Lemma dictid_loop : forall (k : nat) cx fin MD T Rb l M (cinj holdj j : Z),
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_S cx ->
  32 - 8 * Z.of_nat k <= j < 40 - 8 * Z.of_nat k -> (1 <= k <= 4)%nat -> 0 <= j ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS8 = j -> zget_l Rb l kA3 = j ->
  zget_l Rb l kS11 = c_q cx + cinj -> zget_l Rb l kS2 = c_n cx - cinj -> zget_l Rb l kS7 = holdj ->
  mem_arr 1 R_segs M (c_q cx) (c_n cx) fin ->
  (forall R' hold' j',
     zget R' kS11 = c_q cx + c_n cx -> zget R' kS2 = 0 -> zget R' kS7 = hold' -> zget R' kS8 = j' ->
     j' = j + 8 * (c_n cx - cinj) -> 0 <= hold' < 2 ^ j' -> c_n cx - cinj < Z.of_nat k ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kS3 = zget_l Rb l kS3 ->
     zget R' kS4 = zget_l Rb l kS4 ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kT4 = zget_l Rb l kT4 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kT6 = zget_l Rb l kT6 ->
     realizes R_segs (zcfg R_segs L_LEAVE_LD (zupd R' []) M MD) T) ->
  (forall R' hold' j',
     zget R' kA2 = c_q cx + cinj + Z.of_nat k -> zget R' kS11 = c_q cx + cinj + Z.of_nat k ->
     zget R' kS2 = c_n cx - cinj - Z.of_nat k -> zget R' kS7 = hold' -> zget R' kS8 = j' ->
     j' = j + 8 * Z.of_nat k -> 0 <= hold' < 2 ^ j' -> Z.of_nat k <= c_n cx - cinj ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kS3 = zget_l Rb l kS3 ->
     zget R' kS4 = zget_l Rb l kS4 ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kT4 = zget_l Rb l kT4 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kT6 = zget_l Rb l kT6 ->
     realizes R_segs (zcfg R_segs L_DICTID_BODY (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_DICTID_LOOP (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M cinj holdj j Hh Hfin CXl Hj Hk Hj0 Hc Hhj Hjc L9 L0 LA3 L10 L8 L7 Hin KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S] in CXl; destr_conj CXl.
  zkeysb. unfold L_DICTID_LOOP, L_DICTID_BODY, L_LEAVE_LD in *. pose proof two64_eq as TW64.
  assert (Hj40 : 2 ^ j <= 2 ^ 39) by (apply Z.pow_le_mono_r; lia). change (2 ^ 39) with 549755813888 in Hj40.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  -
    zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj j) end; try zreg; try lia.
    all: replace (j + 8 * (n - cinj)) with j by lia; lia.
  - zbr Rfd true.
    pose proof (Hfin cinj ltac:(lia)) as Hb0.
    zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (fin cinj * 2 ^ j) ltac:(rewrite (Z.mod_small j) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (pullbyte_bound holdj j (fin cinj) ltac:(lia) Hhj Hb0) as Hpb.
    destruct k as [|k'].
    +
      zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KDN R' (fin cinj * 2 ^ j + holdj) (j + 8)) end; try zreg; try lia.
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') _ _) _ =>
        eapply (IH (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' M (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) Hh Hfin) end;
        [ unfold ctx_lin; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S]; split_conj; assumption || lia
        | lia | lia | lia | icx_cbn; lia | lia | icx_cbn; lia
        | (icx_cbn; zreg) .. | exact Hin | | ].
      * intros R' hold' j'. icx_cbn. intros. eapply KLV; try eassumption; try lia; try zkept.
      * intros R' hold' j'. icx_cbn. intros. eapply KDN; try eassumption; try lia; try zkept.
Qed.

Lemma dictid_body : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DICTID -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_DICTID (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof (proj1 CX) as CXl. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags] in Hm, Hfl. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_. pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  zkeysb. unfold L_DICTID, L_DICTID_LOOP, L_DICTID_BODY, L_LEAVE_LD, L_DICT in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (BODY : forall RJ cin1 hold1 bits1,
    zget RJ kSP = u + -224 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA0 = u -> zget RJ kA1 = 0 -> zget RJ kS6 = p + 168 -> zget RJ kT6 = -16180 ->
    zget RJ kT4 = 30 -> zget RJ kS9 = 67008 -> zget RJ kS4 = 16209 ->
    zget RJ kS2 = n - cin1 -> zget RJ kS3 = ob + cout -> zget RJ kRA = osz - cout ->
    zget RJ kA2 = q + cin1 -> zget RJ kS7 = hold1 -> zget RJ kS8 = bits1 ->
    cin <= cin1 <= n -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (n - cin1) + bits1 = 8 * (n - cin) + bits ->
    realizes R_segs (zcfg R_segs L_DICTID_BODY (zupd RJ []) Mc MD) T) end.
  { intros RJ cin1 hold1 bits1. intros. unfold L_DICTID_BODY. zkeys.
    pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh1.
    zstep Rfd.
    do 10 (zstep Rfd).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zstep Rfd.
    zgenreg_range chk 0 18446744073709551616
      ltac:(rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; [apply Z.mod_pos_bound|]; lia | apply Z.div_lt_upper_bound; [lia|]; eapply Z.lt_le_trans; [apply Z.mod_pos_bound; lia|]; cbn; lia]).
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_hd _ _ lf cf DICT flags cin1 0 0 SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(cbn; intros E; exfalso; exact (Hfl E))
                  ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST DICTID last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  DICT flags cin1 0 0 ltac:(left; cbn; lia)) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (dict_body ADLN (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                (hd_st (IST DICTID last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) DICT flags cin1 0 0)
                lf cf CX0 Hh Hfin eq_refl SI1) end;
      [ (unfold hd_st; icx_cbn; zkeys; zreg) ..
      | unfold k_mem, hd_st; icx_cbn; split_conj;
        [ close_std | split; [assumption | exact SREST] | exact SRET | exact SOUT | exact Hlens | exact Hcodes | exact HAG ]
      | eapply KALL_mono; [| exact KA0]; lia ]. }
  destruct (Z_lt_dec 31 bits) as [Hb32 | Hb32].
  - zbr Rfd true.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (BODY R' cin hold bits) end; first [zreg | lia].
  - zbr Rfd false.
    zstep Rfd.
    assert (Hkk : exists k : nat, 32 - 8 * Z.of_nat k <= bits < 40 - 8 * Z.of_nat k /\ (1 <= k <= 4)%nat).
    { exists (Z.to_nat (4 - bits / 8)).
      rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (dictid_loop k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' Mx cin hold bits Hh Hfin CXl Hk1 Hk2) end;
      [ lia | icx_cbn; lia | lia | lia | (icx_cbn; zreg) .. | exact Hin | | ].
    +
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_LEAVE_LD in *.
      pose proof (sinv_hd _ _ lf cf DICTID flags n hold' j' SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(cbn; intros E; exfalso; exact (Hfl E))
                    ltac:(cbn; lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia)) as SI1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KLL Rx Mx _ lf cf SI1) end.
      * unfold s_regs_leave_ld, hd_st; icx_cbn; zkeys; split_conj; try zreg; zkept.
      * close_std.
      * unfold hd_st; split; [exact Hmode | exact SREST].
      * exact SRET.
      * exact SOUT.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_DICTID_BODY in *.
      apply (BODY R' (cin + Z.of_nat k) hold' j'); try zkept; try lia.
Qed.

Theorem arm_DICTID_s : arm_stmt L_DICTID DICTID.
Proof. intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K. eapply dictid_body; eassumption. Qed.

End WITH_ADLER_NULL.
End FXG.
End S_HeadB.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S Require S_Stored S_LenF.

Module S_Top.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Frame OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Hoare OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.AllocSim.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.S9LibStmt.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.MstepsGrows.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_Entry.S_Loop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_ZA.S_Ret OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_Entry OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_ZAw.S_Uw OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_ZA.S_LeaveA OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_ZA.S_Leave OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_ZA.S_Inflate OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_ZAw.S_U2A OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_ZA.S_U2B OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_ZA.S_U2C OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_ZA S_ZC OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_ZB.S_Tok OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_ZB S_Head OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_Check.S_HeadA S_HeadB OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_Stored OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_Stored.S_StoredA OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_LenF OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_LenF.S_LenX OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_LenF.S_Dist OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_LenF.S_DistX OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_LenF.S_Match OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_Check.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Lemma zl_get : forall regs (r : reg), bv_eqb r 0%bv = false ->
  zget_l (zlift regs) [] (bv_key r) = bv_unsigned (getr regs r).
Proof. intros regs r Hr. cbv [zget_l alookup]. rewrite zget_zlift, (getr_reg_get regs r Hr). reflexivity. Qed.

Lemma zl_get_lit : forall regs (r : reg) k z, bv_eqb r 0%bv = false -> bv_key r = k ->
  getr regs r = Z_to_bv 64 z -> 0 <= z < two64 -> zget_l (zlift regs) [] k = z.
Proof.
  intros regs r k z Hr <- H Hz. rewrite (zl_get regs r Hr), H.
  change (Z_to_bv 64 z) with (w64 z). rewrite w64_unsigned, mod_small_u64 by exact Hz. reflexivity.
Qed.

Lemma zd_get : forall R (r : reg) k v, bv_eqb r 0%bv = false -> bv_key r = k -> zget R k = v ->
  getr (zden R) r = w64 v.
Proof. intros R r k v Hr <- <-. apply getr_zkey. exact Hr. Qed.
Lemma zd_get_u : forall R (r : reg) k v, bv_eqb r 0%bv = false -> bv_key r = k -> zget R k = v -> 0 <= v < two64 ->
  bv_unsigned (getr (zden R) r) = v.
Proof. intros R r k v Hr Hk Hv Rv. rewrite (zd_get R r k v Hr Hk Hv), w64_unsigned. apply mod_small_u64. exact Rv. Qed.

Lemma hold_u64 : forall hold bits, 0 <= bits -> bits <= 40 -> 0 <= hold -> hold < 2 ^ bits -> 0 <= hold < two64.
Proof.
  intros hold bits B0 B1 H0 H1. pose proof (Z.pow_le_mono_r 2 bits 40 ltac:(lia_std) B1) as P.
  change (2 ^ 40) with 1099511627776 in P. rewrite two64_eq. split; [exact H0|]. change (2 ^ 64) with 18446744073709551616. lia_std.
Qed.

Lemma frame_mod_WA : forall mem mem' u p,
  0 <= u + -1024 -> u + 208 <= two64 -> 0 < p -> p + STATE_SIZE <= two64 ->
  mpostL R_segs mem mem' (fp_u2 u p 0) -> mem_grows mem mem' -> frame_mod mem mem' (WA_S9 u p).
Proof.
  intros mem mem' u p Hu0 Hu1 Hp0 Hp1 HP HG. pose proof two64_eq as TW64.
  eapply frame_mod_weaken; [| eapply (frame_mod_of_mpostL R_segs mem mem' (fp_u2 u p 0)); [| exact HP | exact HG]].
  - intros a Ho. unfold WA_S9 in Ho. cbn [outside wranges fp_u2 Z.eqb] in *.
    dand Ho as (O1 & O2 & O3 & O4 & O5 & _). repeat split; try assumption.
    unfold in_rng. lia_std.
  - unfold fp_u2. cbn [ranges_lt]. cbv [STATE_SIZE BUF] in *. lia_std.
Qed.
Lemma frame_mod_WAw : forall mem mem' u p (ww : word),
  0 <= u + -1024 -> u + 208 <= two64 -> 0 < p -> p + STATE_SIZE <= two64 -> bv_unsigned ww <> 0 -> bv_unsigned ww + WIN_SIZE <= two64 ->
  mpostL R_segs mem mem' (fp_u2 u p (bv_unsigned ww)) -> mem_grows mem mem' -> frame_mod mem mem' (WA_S9 u p ++ [(ww, S9_WIN_N)]).
Proof.
  intros mem mem' u p ww Hu0 Hu1 Hp0 Hp1 Hw0 Hw1 HP HG. pose proof two64_eq as TW64. pose proof (u64_range ww) as Rw.
  eapply frame_mod_weaken; [| eapply (frame_mod_of_mpostL R_segs mem mem' (fp_u2 u p (bv_unsigned ww))); [| exact HP | exact HG]].
  - intros a Ho. unfold WA_S9 in Ho. cbn [outside wranges fp_u2 app] in *.
    dand Ho as (O1 & O2 & O3 & O4 & O5 & O6 & _). rewrite (proj2 (Z.eqb_neq _ 0) Hw0).
    repeat split; try assumption. rewrite Z_to_bv_bv_unsigned. exact O6.
  - unfold fp_u2. cbn [ranges_lt]. cbv [STATE_SIZE BUF] in *. lia_std.
Qed.

Section CONTRACT.
Hypothesis A_TABLE : arm_stmt L_TABLE TABLE.
Hypothesis A_LENLENS : arm_stmt L_LENLENS LENLENS.
Hypothesis A_CODELENS : arm_stmt L_CODELENS CODELENS.

Let A_HEAD : arm_stmt L_HEAD HEAD := arm_HEAD_s adler32_null_ok.
Let A_DICTID : arm_stmt L_DICTID DICTID := arm_DICTID_s adler32_null_ok.
Let A_DICT : arm_stmt L_DICT DICT := arm_DICT_s adler32_null_ok.
Let A_TYPE : arm_stmt L_TYPE TYPE := arm_TYPE_s.
Let A_TYPEDO : arm_stmt L_TYPEDO TYPEDO := arm_TYPEDO_s.
Let A_STORED : arm_stmt L_STORED STORED := arm_STORED_s memcpy_ok.
Let A_COPY_ : arm_stmt L_COPY_ COPY_ := arm_COPY__s memcpy_ok.
Let A_COPY : arm_stmt L_COPY COPY := arm_COPY_s memcpy_ok.
Let A_LEN_ : arm_stmt L_LEN_ LEN_ := arm_LEN_ ifast_ok.
Let A_LEN : arm_stmt L_LEN LEN := arm_LEN ifast_ok.
Let A_LENEXT : arm_stmt L_LENEXT LENEXT := arm_LENEXT.
Let A_DIST : arm_stmt L_DIST DIST := arm_DIST.
Let A_DISTEXT : arm_stmt L_DISTEXT DISTEXT := arm_DISTEXT.
Let A_MATCH : arm_stmt L_MATCH MATCH := arm_MATCH.
Let A_LIT : arm_stmt L_LIT LIT := arm_LIT.
Let A_CHECK : arm_stmt_ob L_CHECK CHECK := arm_CHECK_s adler32_ok.
Let A_LENGTH : arm_stmt L_LENGTH LENGTH := arm_LENGTH_s.

Local Ltac open_layout LAY := let Hu0 := ident:(Hu0) in let Hu1 := ident:(Hu1) in let Hzimg := ident:(Hzimg) in let Hp1 := ident:(Hp1) in let Spob := ident:(Spob) in let Hqn := ident:(Hqn) in let Sobq := ident:(Sobq) in let Spq := ident:(Spq) in let ROMH := ident:(ROMH) in let STK := ident:(STK) in let STP := ident:(STP) in let Sprom := ident:(Sprom) in let Sqrom := ident:(Sqrom) in (dand LAY as (Hua & Hu0 & Hu1 & Hzimg & Hpa & Hp0 & Hp1 & Spob & Hn & Hq1 & Hqn & Sobq & Spq & RD & ROMH & STK & STP & Sprom & Sqrom);
  cbv [S9_FRA S9_INFL_N S9_BUF S9_BUF_N S9_RO_LO S9_RO_HI S9_IMG_TOP] in Hu0, Hu1, Hzimg, Hp1, Spob, Hqn, Sobq, Spq, ROMH, STK, STP, Sprom, Sqrom).

Theorem za_s : za_stmt_S9 zwtok_S9.
Proof.
  unfold za_stmt_S9. intros regs mem u pw qw n zc Hsp Hs1 Ha0 Hs3 Hs4 LAY F32 F24 F16 F8 S8 S16 S72 S80 S88.
  set (p := bv_unsigned pw) in *. set (q := bv_unsigned qw) in *.
  assert (Ep : bv_unsigned pw = p) by reflexivity. assert (Eq : bv_unsigned qw = q) by reflexivity. clearbody p q.
  pose proof (u64_range pw) as Rp. pose proof (u64_range qw) as Rq. rewrite Ep in Rp. rewrite Eq in Rq.
  open_layout LAY. pose proof two64_eq as TW64.
  set (Rb := zlift regs).
  assert (Lsp : zget_l Rb [] kSP = u + -32).
  { subst Rb. rewrite (zl_get_lit regs 2%bv kSP (u - 32) eq_refl eq_refl Hsp); lia_std. }
  assert (Ls1 : zget_l Rb [] kS1 = u).
  { subst Rb. apply (zl_get_lit regs 9%bv kS1 (u) eq_refl eq_refl Hs1). lia_std. }
  assert (La0 : zget_l Rb [] kA0 = p).
  { subst Rb. change kA0 with (bv_key (10%bv : reg)). rewrite (zl_get regs 10%bv eq_refl), Ha0. exact Ep. }
  assert (Ls3 : zget_l Rb [] kS3 = n).
  { subst Rb. apply (zl_get_lit regs 19%bv kS3 n eq_refl eq_refl Hs3). lia_std. }
  assert (Ls4 : zget_l Rb [] kS4 = 262144).
  { subst Rb. apply (zl_get_lit regs 20%bv kS4 262144 eq_refl eq_refl Hs4). lia_std. }
  set (gp := zget_l Rb [] kGP). set (tp := zget_l Rb [] kTP).
  set (s5 := zget_l Rb [] kS5). set (s6 := zget_l Rb [] kS6). set (s7 := zget_l Rb [] kS7). set (s8 := zget_l Rb [] kS8).
  set (s9 := zget_l Rb [] kS9). set (s10 := zget_l Rb [] kS10). set (s11 := zget_l Rb [] kS11).
  assert (RRG : forall (r : reg), bv_eqb r 0%bv = false -> 0 <= zget_l Rb [] (bv_key r) < two64).
  { intros r Hr. subst Rb. rewrite (zl_get regs r Hr). rewrite two64_eq. apply u64_range. }
  pose proof (RRG 3%bv eq_refl : 0 <= gp < two64) as Rgp. pose proof (RRG 4%bv eq_refl : 0 <= tp < two64) as Rtp.
  pose proof (RRG 21%bv eq_refl : 0 <= s5 < two64) as Rs5. pose proof (RRG 22%bv eq_refl : 0 <= s6 < two64) as Rs6. pose proof (RRG 23%bv eq_refl : 0 <= s7 < two64) as Rs7.
  pose proof (RRG 24%bv eq_refl : 0 <= s8 < two64) as Rs8. pose proof (RRG 25%bv eq_refl : 0 <= s9 < two64) as Rs9.
  pose proof (RRG 26%bv eq_refl : 0 <= s10 < two64) as Rs10. pose proof (RRG 27%bv eq_refl : 0 <= s11 < two64) as Rs11.
  clear RRG.
  pose proof (mem_wr_of_store_ok _ _ _ _ STK) as Wstk. rewrite Z2Nat.id in Wstk by lia_std.
  change (mem_wr R_segs mem (u - 1024) 1232) in Wstk. replace (u - 1024) with (u + -1024) in Wstk by lia_std.
  pose proof (mem_wr_of_store_ok _ _ _ _ STP) as Wp. rewrite Z2Nat.id in Wp by lia_std.
  change (mem_wr R_segs mem p 7176) in Wp.
  pose proof (rom_ok_of_hyp mem ROMH) as ROM.
  destruct (mem_arr_of_readable R_segs mem q n ltac:(lia_std) ltac:(lia_std) ltac:(lia_std) RD) as (fin & Hin & Hfin).
  set (Q := fun c : config => exists (R : tree Z) (M' : word -> option byte),
    (c = zcfg R_segs T_ZE2 (zupd R []) M' MD0 /\
     zget R kA4 = A_ZCFREE /\ zget R kA1 = p /\ zget R kA0 = 0 /\ zget R kS0 = u /\ zget R kSP = u + -16 /\
     zget R kGP = gp /\ zget R kTP = tp /\
     zget R kS5 = s5 /\ zget R kS6 = s6 /\ zget R kS7 = s7 /\ zget R kS8 = s8 /\ zget R kS9 = s9 /\ zget R kS10 = s10 /\ zget R kS11 = s11 /\
     mem_u64 R_segs M' (u + -8) RA2 /\ mem_u64 R_segs M' (u + 56) p /\ mem_u64 R_segs M' (u + 72) A_ZCFREE /\ mem_u64 R_segs M' (u + 80) 0 /\
     mpostL R_segs mem M' (fp_u2 u p 0))
    \/
    (c = zcfg R_segs T_ZW (zupd R []) M' MD0 /\
     zget R kA3 = A_ZCALLOC /\ zget R kA0 = 0 /\ zget R kA1 = WIN_SIZE /\ zget R kA2 = 1 /\ zget R kSP = u + -272 /\
     zget R kGP = gp /\ zget R kTP = tp /\
     zwtok_S9 u p q n zc (sregs regs S_ENTRY5) (sregs (zden R) S_ALL) M' /\
     mpostL R_segs mem M' (fp_u2 u p 0))).
  assert (HR : realizes R_segs (zcfg R_segs L_ZA (zupd Rb []) mem MD0) Q).
  { eapply (za_cps u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD0 Q zc MD0_halted Hfin);
      try first [ exact Lsp | exact Ls1 | exact La0 | exact Ls3 | exact Ls4 | reflexivity | assumption
                | exact memcpy_ok | exact adler32_ok
                | exact F32 | exact F24 | exact F16 | exact F8 | rewrite <- Eq; exact S8 | exact S16 | exact S72 | exact S80 | exact S88
                | unfold ZSEP; cbv [STATE_SIZE ROM_LO_ALL ROMHI_S BUF]; lia_std
                | cbv [FRA STATE_SIZE DATA_LO DATA_LEN]; lia_std ].
    -
      intros R M'. intros. apply rz_now. subst Q. cbv beta. exists R, M'. left.
      repeat (split; [first [reflexivity | assumption] |]). assumption.
    -
      intros R M' cin0 cout0 W0 ra st rv lf cf. cbv zeta. intros Hra Hcin0 Hcout0 SI Hcc Hmd.
      intros GA3 GA0 GA1 GA2 GS0 GS1 GS2 GS3 GS4 GSP GGP GTP GS5 GS6 GS7 GS8 GS9 GS10 U232 U240 U248 U256 U264 U272 STD SAT STRM Hlens Hcodes Hw0 HP.
      apply rz_now. subst Q. cbv beta. exists R, M'. right.
      split; [reflexivity|]. do 7 (split; [assumption|]). split; [| exact HP].
      pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _). unfold RNG, cxc in RNG_. icx_cbn.
      destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
      icx_cbn. destr_conj RNG_.
      pose proof (hold_u64 hold bits ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Rhold.
      cbv [BUF] in GS0.
      exists s5, s6, s7, s8, s9, s10, s11, cin0, cout0, W0, ra, rv, (bv_unsigned (getr (zden R) 26)),
             (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext), lf, cf.
      split; [| split; [| split]].
      + subst s5 s6 s7 s8 s9 s10 s11 Rb. unfold sregs, S_ENTRY5, S_ENTRY. cbn [map app].
        rewrite <- (zl_get regs 21%bv eq_refl), <- (zl_get regs 22%bv eq_refl), <- (zl_get regs 23%bv eq_refl), <- (zl_get regs 24%bv eq_refl),
                <- (zl_get regs 25%bv eq_refl), <- (zl_get regs 26%bv eq_refl), <- (zl_get regs 27%bv eq_refl).
        reflexivity.
      + unfold sregs, S_ALL, tok_regs. cbn [map]. icx_cbn. cbv [BUF FRA STATE_SIZE] in *.
        rewrite (zd_get_u R 8 kS0 _ eq_refl eq_refl GS0) by lia_std.
        rewrite (zd_get_u R 9 kS1 _ eq_refl eq_refl GS1) by lia_std.
        rewrite (zd_get_u R 18 kS2 _ eq_refl eq_refl GS2) by lia_std.
        rewrite (zd_get_u R 19 kS3 _ eq_refl eq_refl GS3) by lia_std.
        rewrite (zd_get_u R 20 kS4 _ eq_refl eq_refl GS4) by lia_std.
        rewrite (zd_get_u R 21 kS5 _ eq_refl eq_refl GS5) by lia_std.
        rewrite (zd_get_u R 22 kS6 _ eq_refl eq_refl GS6) by lia_std.
        rewrite (zd_get_u R 23 kS7 _ eq_refl eq_refl GS7) by exact Rhold.
        rewrite (zd_get_u R 24 kS8 _ eq_refl eq_refl GS8) by lia_std.
        rewrite (zd_get_u R 25 kS9 _ eq_refl eq_refl GS9) by lia_std.
        rewrite (zd_get_u R 27 kS11 _ eq_refl eq_refl GS10) by lia_std.
        reflexivity.
      + unfold tok_pure. pose proof (u64_range (getr (zden R) 26)). rewrite <- TW64 in *.
        split_conj; try assumption; try (icx_cbn; assumption); try (cbv [FRA STATE_SIZE]; lia_std).
      + unfold tok_mem, cxw. icx_cbn. clear ROM Wstk Wp Hin. open_std STD. split_conj; try assumption.
        all: first [ exact FRM | exact CST | exact HK | exact SAT | exact STRM
                   | match goal with |- ?G => idtac "TOKSIDE" G end ]. }
  dand HR as (ms' & RUN & HQ). subst Q. cbv beta in HQ. cbn [cfg_ms cfg_model zcfg] in RUN, HQ.
  unfold zst in RUN. cbn [zupd] in RUN. subst Rb. rewrite zden_zlift in RUN.
  pose proof (msteps_mem_grows R_segs _ _ RUN) as G. cbn [ms_mem] in G.
  assert (KEPT : forall (R : tree Z) (r : reg) k, bv_eqb r 0%bv = false -> bv_key r = k ->
            zget R k = zget_l (zlift regs) [] k -> getr (zden R) r = getr regs r).
  { intros R r k Hr Hk Hv. rewrite (zd_get R r k _ Hr Hk Hv), <- Hk, (zl_get regs r Hr). apply w64_of_word. }
  assert (SE : forall R : tree Z, zget R kS5 = s5 -> zget R kS6 = s6 -> zget R kS7 = s7 -> zget R kS8 = s8 -> zget R kS9 = s9 ->
            zget R kS10 = s10 -> zget R kS11 = s11 -> sregs (zden R) S_ENTRY5 = sregs regs S_ENTRY5).
  { intros R E5 E6 E7 E8 E9 E10 E11. unfold sregs, S_ENTRY5, S_ENTRY. cbn [map app].
    rewrite (KEPT R 21%bv kS5 eq_refl eq_refl E5), (KEPT R 22%bv kS6 eq_refl eq_refl E6), (KEPT R 23%bv kS7 eq_refl eq_refl E7), (KEPT R 24%bv kS8 eq_refl eq_refl E8),
            (KEPT R 25%bv kS9 eq_refl eq_refl E9), (KEPT R 26%bv kS10 eq_refl eq_refl E10), (KEPT R 27%bv kS11 eq_refl eq_refl E11).
    reflexivity. }
  destruct HQ as (R & M' & [(E & GA4 & GA1 & GA0 & GS0 & GSP & GGP & GTP & G5 & G6 & G7 & G8 & G9 & G10 & G11 & C8 & C64 & C80 & C88 & HP)
                           |(E & GA3 & GA0 & GA1 & GA2 & GSP & GGP & GTP & TOK & HP)]);
    unfold zcfg, zst in E; injection E as E1; subst ms'; cbn [ms_mem] in G; cbn [zupd].
  - exists (zden R), M', T_ZE2. split; [exact RUN | split].
    + apply frame_mod_WA; try assumption; cbv [STATE_SIZE]; lia_std.
    + left. split; [reflexivity | split].
      * unfold end_regs_S9. split_conj.
        -- exact (zd_get R 14%bv kA4 _ eq_refl eq_refl GA4).
        -- exact (zd_get R 11%bv kA1 _ eq_refl eq_refl GA1).
        -- exact (zd_get R 10%bv kA0 _ eq_refl eq_refl GA0).
        -- exact (zd_get R 8%bv kS0 _ eq_refl eq_refl GS0).
        -- exact (zd_get R 2%bv kSP _ eq_refl eq_refl GSP).
        -- exact (KEPT R 3%bv kGP eq_refl eq_refl GGP).
        -- exact (KEPT R 4%bv kTP eq_refl eq_refl GTP).
        -- apply SE; assumption.
      * unfold end_cells_S9. split_conj; [exact C8 | exact C64 | exact C80 | exact C88].
  - exists (zden R), M', T_ZW. split; [exact RUN | split].
    + apply frame_mod_WA; try assumption; cbv [STATE_SIZE]; lia_std.
    + right. split; [reflexivity |]. split_conj.
      * exact (zd_get R 13%bv kA3 _ eq_refl eq_refl GA3).
      * exact (zd_get R 10%bv kA0 _ eq_refl eq_refl GA0).
      * exact (zd_get R 11%bv kA1 _ eq_refl eq_refl GA1).
      * exact (zd_get R 12%bv kA2 _ eq_refl eq_refl GA2).
      * exact (zd_get R 2%bv kSP _ eq_refl eq_refl GSP).
      * exact (KEPT R 3%bv kGP eq_refl eq_refl GGP).
      * exact (KEPT R 4%bv kTP eq_refl eq_refl GTP).
      * exact TOK.
Qed.

Lemma sregs_S_ALL : forall regs l,
  sregs regs S_ALL = l ->
  l = [bv_unsigned (getr regs 8); bv_unsigned (getr regs 9); bv_unsigned (getr regs 18); bv_unsigned (getr regs 19);
       bv_unsigned (getr regs 20); bv_unsigned (getr regs 21); bv_unsigned (getr regs 22); bv_unsigned (getr regs 23);
       bv_unsigned (getr regs 24); bv_unsigned (getr regs 25); bv_unsigned (getr regs 26); bv_unsigned (getr regs 27)].
Proof. intros regs l <-. reflexivity. Qed.

Local Ltac open_token TOK := let PURE := ident:(PURE) in (dand TOK as (s5 & s6 & s7 & s8 & s9 & s10 & s11 & cin0 & cout0 & W0 & ra & rv & s11v & st & lf & cf & EsE & EsW & PURE & TM);
  unfold tok_pure in PURE;
  dand PURE as (Hra & Hcin0 & Hcout0 & Rs5 & Rs6 & Rs7 & Rs8 & Rs9 & Rs10 & Rs11 & Rs11v & SI & Hcc & Hmd & Lu0 & Lu1 & Lp0 & Lp1)).

Theorem zb_s : zb_stmt_S9 zwtok_S9.
Proof.
  unfold zb_stmt_S9. intros regs mem u pw qw ww n zc sE sW Hsp Ha0 HsW TOK LAY Hwa Hw0 Hw1 Swb Swp Swq Swi STW.
  set (p := bv_unsigned pw) in *. set (q := bv_unsigned qw) in *. set (w := bv_unsigned ww) in *.
  assert (Ep : bv_unsigned pw = p) by reflexivity. assert (Eq : bv_unsigned qw = q) by reflexivity. assert (Ew : bv_unsigned ww = w) by reflexivity.
  clearbody p q w.
  pose proof (u64_range pw) as Rp. pose proof (u64_range qw) as Rq. pose proof (u64_range ww) as Rw.
  rewrite Ep in Rp. rewrite Eq in Rq. rewrite Ew in Rw.
  open_layout LAY. cbv [S9_WIN_N S9_BUF S9_BUF_N S9_INFL_N S9_IMG_TOP] in Hw1, Swb, Swp, Swq, Swi, STW. pose proof two64_eq as TW64.
  open_token TOK.
  pose proof (sregs_S_ALL regs sW HsW) as EW. rewrite EsW in EW. unfold tok_regs in EW.
  injection EW as W0_ W1_ W2_ W3_ W4_ W5_ W6_ W7_ W8_ W9_ W10_ W11_.
  set (Rb := zlift regs).
  assert (Lsp : zget_l Rb [] kSP = u + -272).
  { subst Rb. rewrite (zl_get_lit regs 2%bv kSP (u - 272) eq_refl eq_refl Hsp); lia_std. }
  assert (La0 : zget_l Rb [] kA0 = w).
  { subst Rb. change kA0 with (bv_key (10%bv : reg)). rewrite (zl_get regs 10%bv eq_refl), Ha0. exact Ew. }
  assert (GL : forall (r : reg) k v, bv_eqb r 0%bv = false -> bv_key r = k -> bv_unsigned (getr regs r) = v -> zget_l Rb [] k = v).
  { intros r k v Hr <- Hv. subst Rb. rewrite (zl_get regs r Hr). exact Hv. }
  pose proof (GL 8%bv kS0 _ eq_refl eq_refl (eq_sym W0_)) as Ls0.
  pose proof (GL 9%bv kS1 _ eq_refl eq_refl (eq_sym W1_)) as Ls1.
  pose proof (GL 18%bv kS2 _ eq_refl eq_refl (eq_sym W2_)) as Ls2.
  pose proof (GL 19%bv kS3 _ eq_refl eq_refl (eq_sym W3_)) as Ls3.
  pose proof (GL 20%bv kS4 _ eq_refl eq_refl (eq_sym W4_)) as Ls4.
  pose proof (GL 21%bv kS5 _ eq_refl eq_refl (eq_sym W5_)) as Ls5.
  pose proof (GL 22%bv kS6 _ eq_refl eq_refl (eq_sym W6_)) as Ls6.
  pose proof (GL 23%bv kS7 _ eq_refl eq_refl (eq_sym W7_)) as Ls7.
  pose proof (GL 24%bv kS8 _ eq_refl eq_refl (eq_sym W8_)) as Ls8.
  pose proof (GL 25%bv kS9 _ eq_refl eq_refl (eq_sym W9_)) as Ls9.
  pose proof (GL 27%bv kS11 _ eq_refl eq_refl (eq_sym W11_)) as Ls10.
  set (gp := zget_l Rb [] kGP). set (tp := zget_l Rb [] kTP).
  assert (RRG : forall (r : reg), bv_eqb r 0%bv = false -> 0 <= zget_l Rb [] (bv_key r) < two64).
  { intros r Hr. subst Rb. rewrite (zl_get regs r Hr). rewrite two64_eq. apply u64_range. }
  pose proof (RRG 3%bv eq_refl : 0 <= gp < two64) as Rgp. pose proof (RRG 4%bv eq_refl : 0 <= tp < two64) as Rtp. clear RRG.
  pose proof (mem_wr_of_store_ok _ _ _ _ STK) as Wstk. rewrite Z2Nat.id in Wstk by lia_std.
  change (mem_wr R_segs mem (u - 1024) 1232) in Wstk. replace (u - 1024) with (u + -1024) in Wstk by lia_std.
  pose proof (mem_wr_of_store_ok _ _ _ _ STP) as Wp. rewrite Z2Nat.id in Wp by lia_std.
  change (mem_wr R_segs mem p 7176) in Wp.
  rewrite <- (Z_to_bv_bv_unsigned 64 ww), Ew in STW.
  pose proof (mem_wr_of_store_ok _ _ _ _ STW) as Ww. rewrite Z2Nat.id in Ww by lia_std.
  change (mem_wr R_segs mem w 32768) in Ww.
  pose proof (rom_ok_of_hyp mem ROMH) as ROM.
  destruct (mem_arr_of_readable R_segs mem q n ltac:(lia_std) ltac:(lia_std) ltac:(lia_std) RD) as (fin & Hin & Hfin).
  assert (Hwok : wok p q n zc w).
  { unfold wok, ZSEP. cbv [WIN_SIZE STATE_SIZE BUF ROM_LO_ALL ROMHI_S]. split_conj; try lia_std. }
  assert (Hsite : exists site : bool, ra = ra_site site).
  { destruct Hra as [-> | ->]; [exists true | exists false]; reflexivity. }
  dand Hsite as (site & Esite). subst ra.
  assert (Ku0 : zc + FRA <= u) by (cbv [FRA]; lia_std).
  assert (Kzimg : DATA_LO + DATA_LEN <= zc) by (cbv [DATA_LO DATA_LEN]; lia_std).
  assert (Ku1 : u + 208 <= 140737488355328) by lia_std.
  assert (Kp1 : p + STATE_SIZE <= zc) by (cbv [STATE_SIZE]; lia_std).
  assert (Kn0 : 0 <= n) by lia_std. assert (Kn1 : n < 67108864) by lia_std.
  assert (Kqn : q + n <= zc) by lia_std.
  assert (Kpq : ZSEP (p + STATE_SIZE <= q \/ q + n <= p)) by (unfold ZSEP; cbv [STATE_SIZE]; lia_std).
  assert (Kpob : ZSEP (p + STATE_SIZE <= BUF \/ BUF + 262144 <= p)) by (unfold ZSEP; cbv [STATE_SIZE BUF]; lia_std).
  assert (Kobq : ZSEP (BUF + 262144 <= q \/ q + n <= BUF)) by (unfold ZSEP; cbv [BUF]; lia_std).
  assert (Kprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p)) by (unfold ZSEP; cbv [STATE_SIZE ROM_LO_ALL ROMHI_S]; lia_std).
  set (Q := fun c : config => exists (R : tree Z) (M' : word -> option byte),
    c = zcfg R_segs T_ZE1 (zupd R []) M' MD0 /\
    zget R kA4 = A_ZCFREE /\ zget R kA1 = w /\ zget R kA0 = 0 /\ zget R kS0 = u /\ zget R kSP = u + -16 /\
    zget R kGP = gp /\ zget R kTP = tp /\
    zget R kS5 = s5 /\ zget R kS6 = s6 /\ zget R kS7 = s7 /\ zget R kS8 = s8 /\ zget R kS9 = s9 /\ zget R kS10 = s10 /\ zget R kS11 = s11 /\
    mem_u64 R_segs M' (u + -8) RA2 /\ mem_u64 R_segs M' (u + 56) p /\ mem_u64 R_segs M' (u + 72) A_ZCFREE /\ mem_u64 R_segs M' (u + 80) 0 /\
    mpostL R_segs mem M' (fp_u2 u p w)).
  assert (HR : realizes R_segs (zcfg R_segs L_ZB (zupd Rb []) mem MD0) Q).
  { eapply (zb_cps u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD0 Q zc MD0_halted Hfin
              Ku0 Kzimg Ku1 Hua Hp0 Kp1 Hpa Hq1 Kn0 Kn1 Kqn Kpq Kpob Kobq Kprom Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 memcpy_ok adler32_ok
              A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
              A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH
              w Hwok site cin0 cout0 W0 rv st lf cf Hcin0 Hcout0 SI Hcc Rb [] mem
              Lsp La0 Ls0 Ls1 Ls2 Ls3 Ls4 Ls5 Ls6 Ls7 Ls8 Ls9 Ls10 eq_refl eq_refl ROM Wstk Wp ltac:(intros _; exact Ww) Hin TM).
    -
      intros R M'. intros. exfalso. lia_std.
    -
      intros R M'. intros. apply rz_now. subst Q. cbv beta. exists R, M'.
      repeat (split; [first [reflexivity | assumption] |]). assumption. }
  dand HR as (ms' & RUN & HQ). subst Q. cbv beta in HQ. cbn [cfg_ms cfg_model zcfg] in RUN, HQ.
  unfold zst in RUN. cbn [zupd] in RUN. subst Rb. rewrite zden_zlift in RUN.
  pose proof (msteps_mem_grows R_segs _ _ RUN) as G. cbn [ms_mem] in G.
  dand HQ as (R & M' & E & GA4 & GA1 & GA0 & GS0 & GSP & GGP & GTP & G5 & G6 & G7 & G8 & G9 & G10 & G11 & C8 & C64 & C80 & C88 & HP).
  unfold zcfg, zst in E; injection E as E1; subst ms'; cbn [ms_mem] in G; cbn [zupd].
  exists (zden R), M'. split; [exact RUN | split; [| split]].
  - apply frame_mod_WAw; rewrite ?Ew; try assumption; cbv [STATE_SIZE WIN_SIZE]; first [lia | lia_std].
  - unfold end_regs_S9. split_conj.
    + exact (zd_get R 14%bv kA4 _ eq_refl eq_refl GA4).
    + exact (zd_get R 11%bv kA1 _ eq_refl eq_refl GA1).
    + exact (zd_get R 10%bv kA0 _ eq_refl eq_refl GA0).
    + exact (zd_get R 8%bv kS0 _ eq_refl eq_refl GS0).
    + exact (zd_get R 2%bv kSP _ eq_refl eq_refl GSP).
    + rewrite (zd_get R 3%bv kGP _ eq_refl eq_refl GGP). subst gp. rewrite (zl_get regs 3%bv eq_refl). apply w64_of_word.
    + rewrite (zd_get R 4%bv kTP _ eq_refl eq_refl GTP). subst tp. rewrite (zl_get regs 4%bv eq_refl). apply w64_of_word.
    + rewrite EsE. unfold sregs, S_ENTRY5, S_ENTRY. cbn [map app]. rewrite (zd_get_u R 21 kS5 _ eq_refl eq_refl G5) by exact Rs5.
      rewrite (zd_get_u R 22 kS6 _ eq_refl eq_refl G6) by exact Rs6. rewrite (zd_get_u R 23 kS7 _ eq_refl eq_refl G7) by exact Rs7.
      rewrite (zd_get_u R 24 kS8 _ eq_refl eq_refl G8) by exact Rs8. rewrite (zd_get_u R 25 kS9 _ eq_refl eq_refl G9) by exact Rs9.
      rewrite (zd_get_u R 26 kS10 _ eq_refl eq_refl G10) by exact Rs10. rewrite (zd_get_u R 27 kS11 _ eq_refl eq_refl G11) by exact Rs11.
      reflexivity.
  - unfold end_cells_S9. split_conj; [exact C8 | exact C64 | exact C80 | exact C88].
Qed.

Theorem zb0_s : zb0_stmt_S9 zwtok_S9.
Proof.
  unfold zb0_stmt_S9. intros regs mem u pw qw n zc sE sW Hsp Ha0 HsW TOK LAY.
  set (p := bv_unsigned pw) in *. set (q := bv_unsigned qw) in *.
  assert (Ep : bv_unsigned pw = p) by reflexivity. assert (Eq : bv_unsigned qw = q) by reflexivity.
  clearbody p q.
  pose proof (u64_range pw) as Rp. pose proof (u64_range qw) as Rq. rewrite Ep in Rp. rewrite Eq in Rq.
  open_layout LAY. pose proof two64_eq as TW64.
  open_token TOK.
  pose proof (sregs_S_ALL regs sW HsW) as EW. rewrite EsW in EW. unfold tok_regs in EW.
  injection EW as W0_ W1_ W2_ W3_ W4_ W5_ W6_ W7_ W8_ W9_ W10_ W11_.
  set (Rb := zlift regs).
  assert (Lsp : zget_l Rb [] kSP = u + -272).
  { subst Rb. rewrite (zl_get_lit regs 2%bv kSP (u - 272) eq_refl eq_refl Hsp); lia_std. }
  assert (La0 : zget_l Rb [] kA0 = 0).
  { subst Rb. apply (zl_get_lit regs 10%bv kA0 0 eq_refl eq_refl Ha0). lia_std. }
  assert (GL : forall (r : reg) k v, bv_eqb r 0%bv = false -> bv_key r = k -> bv_unsigned (getr regs r) = v -> zget_l Rb [] k = v).
  { intros r k v Hr <- Hv. subst Rb. rewrite (zl_get regs r Hr). exact Hv. }
  pose proof (GL 8%bv kS0 _ eq_refl eq_refl (eq_sym W0_)) as Ls0.
  pose proof (GL 9%bv kS1 _ eq_refl eq_refl (eq_sym W1_)) as Ls1.
  pose proof (GL 18%bv kS2 _ eq_refl eq_refl (eq_sym W2_)) as Ls2.
  pose proof (GL 19%bv kS3 _ eq_refl eq_refl (eq_sym W3_)) as Ls3.
  pose proof (GL 20%bv kS4 _ eq_refl eq_refl (eq_sym W4_)) as Ls4.
  pose proof (GL 21%bv kS5 _ eq_refl eq_refl (eq_sym W5_)) as Ls5.
  pose proof (GL 22%bv kS6 _ eq_refl eq_refl (eq_sym W6_)) as Ls6.
  pose proof (GL 23%bv kS7 _ eq_refl eq_refl (eq_sym W7_)) as Ls7.
  pose proof (GL 24%bv kS8 _ eq_refl eq_refl (eq_sym W8_)) as Ls8.
  pose proof (GL 25%bv kS9 _ eq_refl eq_refl (eq_sym W9_)) as Ls9.
  pose proof (GL 27%bv kS11 _ eq_refl eq_refl (eq_sym W11_)) as Ls10.
  set (gp := zget_l Rb [] kGP). set (tp := zget_l Rb [] kTP).
  assert (RRG : forall (r : reg), bv_eqb r 0%bv = false -> 0 <= zget_l Rb [] (bv_key r) < two64).
  { intros r Hr. subst Rb. rewrite (zl_get regs r Hr). rewrite two64_eq. apply u64_range. }
  pose proof (RRG 3%bv eq_refl : 0 <= gp < two64) as Rgp. pose proof (RRG 4%bv eq_refl : 0 <= tp < two64) as Rtp. clear RRG.
  pose proof (mem_wr_of_store_ok _ _ _ _ STK) as Wstk. rewrite Z2Nat.id in Wstk by lia_std.
  change (mem_wr R_segs mem (u - 1024) 1232) in Wstk. replace (u - 1024) with (u + -1024) in Wstk by lia_std.
  pose proof (mem_wr_of_store_ok _ _ _ _ STP) as Wp. rewrite Z2Nat.id in Wp by lia_std.
  change (mem_wr R_segs mem p 7176) in Wp.
  pose proof (rom_ok_of_hyp mem ROMH) as ROM.
  destruct (mem_arr_of_readable R_segs mem q n ltac:(lia_std) ltac:(lia_std) ltac:(lia_std) RD) as (fin & Hin & Hfin).
  assert (Hsite : exists site : bool, ra = ra_site site).
  { destruct Hra as [-> | ->]; [exists true | exists false]; reflexivity. }
  dand Hsite as (site & Esite). subst ra.
  assert (Ku0 : zc + FRA <= u) by (cbv [FRA]; lia_std).
  assert (Kzimg : DATA_LO + DATA_LEN <= zc) by (cbv [DATA_LO DATA_LEN]; lia_std).
  assert (Ku1 : u + 208 <= 140737488355328) by lia_std.
  assert (Kp1 : p + STATE_SIZE <= zc) by (cbv [STATE_SIZE]; lia_std).
  assert (Kn0 : 0 <= n) by lia_std. assert (Kn1 : n < 67108864) by lia_std.
  assert (Kqn : q + n <= zc) by lia_std.
  assert (Kpq : ZSEP (p + STATE_SIZE <= q \/ q + n <= p)) by (unfold ZSEP; cbv [STATE_SIZE]; lia_std).
  assert (Kpob : ZSEP (p + STATE_SIZE <= BUF \/ BUF + 262144 <= p)) by (unfold ZSEP; cbv [STATE_SIZE BUF]; lia_std).
  assert (Kobq : ZSEP (BUF + 262144 <= q \/ q + n <= BUF)) by (unfold ZSEP; cbv [BUF]; lia_std).
  assert (Kprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p)) by (unfold ZSEP; cbv [STATE_SIZE ROM_LO_ALL ROMHI_S]; lia_std).
  set (Q := fun c : config => exists (R : tree Z) (M' : word -> option byte),
    c = zcfg R_segs T_ZE2 (zupd R []) M' MD0 /\
    zget R kA4 = A_ZCFREE /\ zget R kA1 = p /\ zget R kA0 = 0 /\ zget R kS0 = u /\ zget R kSP = u + -16 /\
    zget R kGP = gp /\ zget R kTP = tp /\
    zget R kS5 = s5 /\ zget R kS6 = s6 /\ zget R kS7 = s7 /\ zget R kS8 = s8 /\ zget R kS9 = s9 /\ zget R kS10 = s10 /\ zget R kS11 = s11 /\
    mem_u64 R_segs M' (u + -8) RA2 /\ mem_u64 R_segs M' (u + 56) p /\ mem_u64 R_segs M' (u + 72) A_ZCFREE /\ mem_u64 R_segs M' (u + 80) 0 /\
    mpostL R_segs mem M' (fp_u2 u p 0)).
  assert (HR : realizes R_segs (zcfg R_segs L_ZB (zupd Rb []) mem MD0) Q).
  { eapply (zb_cps u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD0 Q zc MD0_halted Hfin
              Ku0 Kzimg Ku1 Hua Hp0 Kp1 Hpa Hq1 Kn0 Kn1 Kqn Kpq Kpob Kobq Kprom Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 memcpy_ok adler32_ok
              A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
              A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH
              0 (wok0 p q n zc Kzimg) site cin0 cout0 W0 rv st lf cf Hcin0 Hcout0 SI Hcc Rb [] mem
              Lsp La0 Ls0 Ls1 Ls2 Ls3 Ls4 Ls5 Ls6 Ls7 Ls8 Ls9 Ls10 eq_refl eq_refl ROM Wstk Wp ltac:(intros C; exfalso; exact (C eq_refl)) Hin TM).
    -
      intros R M'. intros. apply rz_now. subst Q. cbv beta. exists R, M'.
      repeat (split; [first [reflexivity | assumption] |]). assumption.
    -
      intros R M'. intros. exfalso. match goal with H : 0 <> 0 |- _ => exact (H eq_refl) end. }
  dand HR as (ms' & RUN & HQ). subst Q. cbv beta in HQ. cbn [cfg_ms cfg_model zcfg] in RUN, HQ.
  unfold zst in RUN. cbn [zupd] in RUN. subst Rb. rewrite zden_zlift in RUN.
  pose proof (msteps_mem_grows R_segs _ _ RUN) as G. cbn [ms_mem] in G.
  dand HQ as (R & M' & E & GA4 & GA1 & GA0 & GS0 & GSP & GGP & GTP & G5 & G6 & G7 & G8 & G9 & G10 & G11 & C8 & C64 & C80 & C88 & HP).
  unfold zcfg, zst in E; injection E as E1; subst ms'; cbn [ms_mem] in G; cbn [zupd].
  exists (zden R), M'. split; [exact RUN | split; [| split]].
  - apply frame_mod_WA; try assumption; cbv [STATE_SIZE]; lia_std.
  - unfold end_regs_S9. split_conj.
    + exact (zd_get R 14%bv kA4 _ eq_refl eq_refl GA4).
    + exact (zd_get R 11%bv kA1 _ eq_refl eq_refl GA1).
    + exact (zd_get R 10%bv kA0 _ eq_refl eq_refl GA0).
    + exact (zd_get R 8%bv kS0 _ eq_refl eq_refl GS0).
    + exact (zd_get R 2%bv kSP _ eq_refl eq_refl GSP).
    + rewrite (zd_get R 3%bv kGP _ eq_refl eq_refl GGP). subst gp. rewrite (zl_get regs 3%bv eq_refl). apply w64_of_word.
    + rewrite (zd_get R 4%bv kTP _ eq_refl eq_refl GTP). subst tp. rewrite (zl_get regs 4%bv eq_refl). apply w64_of_word.
    + rewrite EsE. unfold sregs, S_ENTRY5, S_ENTRY. cbn [map app]. rewrite (zd_get_u R 21 kS5 _ eq_refl eq_refl G5) by exact Rs5.
      rewrite (zd_get_u R 22 kS6 _ eq_refl eq_refl G6) by exact Rs6. rewrite (zd_get_u R 23 kS7 _ eq_refl eq_refl G7) by exact Rs7.
      rewrite (zd_get_u R 24 kS8 _ eq_refl eq_refl G8) by exact Rs8. rewrite (zd_get_u R 25 kS9 _ eq_refl eq_refl G9) by exact Rs9.
      rewrite (zd_get_u R 26 kS10 _ eq_refl eq_refl G10) by exact Rs10. rewrite (zd_get_u R 27 kS11 _ eq_refl eq_refl G11) by exact Rs11.
      reflexivity.
  - unfold end_cells_S9. split_conj; [exact C8 | exact C64 | exact C80 | exact C88].
Qed.

Definition contract_S9 : zlib_u2_contract_S9 :=
  ZU2C_S9 zwtok_S9 zw_local za_s zb_s zb0_s zc_s.

End CONTRACT.
End FXG.
End S_Top.

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit Require Import S9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S Require Import SBase. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S Require S_ZB. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.S_ZB.S_Tok. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S Require Import S_GroupB. Import S_Top.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.
Definition zlib_contract_S9 : zlib_u2_contract_S9 :=
  contract_S9 (arm_TABLE_s itable_ok ifast_ok) (arm_LENLENS_s itable_ok ifast_ok) (arm_CODELENS_s itable_ok ifast_ok).
End FXG.
