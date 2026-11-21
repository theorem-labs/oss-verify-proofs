(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require RefMemcpyLib FuzzMem U9MemcpyBase U9Memcpy U9AdlerBase U9AdlerIface U9Adler.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require U9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U Require TBase T_It1.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require ZTac ZMem ZCall ZCallL ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require S_It0 S_It3 S_It4 S_It5 S_It6.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U Require Base T_It2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U Require T_Fast2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require InflateInvTab.

Module T_Fast1E.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U.T_Fast2.T_Fast1.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.


Definition f_emem {RCa1 : RunCtx}  (cx : fcx) (cin cout hold bits : Z) (fo : Z -> Z) (M : mem) : Prop :=
  let u := f_u cx in let p := f_p cx in
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u) (f_q cx + cin) /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 8) (f_n cx - cin) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 24) (f_ob cx + cout) /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 32) (f_osz cx - cout) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 56) p /\
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) (f_wn cx) /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 76) (f_whave cx) /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 80) (f_wnext cx) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) (f_w cx) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 96) hold /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 104) bits /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 120) (f_la cx) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 128) (f_da cx) /\
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 136) (f_lb cx) /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 140) (f_db cx) /\
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 7160) 1 /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 8) LEN /\
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_q cx) (f_n cx) (f_fin cx) /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_la cx) (f_na cx) (f_rdL cx) /\
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_da cx) (f_nd cx) (f_rdD cx) /\ mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_w cx) (f_wn cx) (f_fw cx) /\
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (f_ob cx) (f_osz cx) fo.

Lemma f_emem_magreeL {RCa1 : RunCtx}  : forall cx cin cout hold bits fo M0 M,
  fcx_ok cx -> magreeL M0 M [(f_spi cx + -160, 160)] -> f_emem cx cin cout hold bits fo M0 -> f_emem cx cin cout hold bits fo M.
Proof.
  intros cx cin cout hold bits fo M0 M CX HA H.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. unfold f_emem in *. fcx_cbn. pose proof two64_eq as TW64.
  dand H as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & A1 & A2 & A3 & A4 & A5).
  pose proof (mem_arr_bounds _ _ _ _ _ _ A4) as Bw. pose proof (mem_arr_bounds _ _ _ _ _ _ A5) as Bob.
  split_conj;
  first [ eapply mem_u64_magreeL; [exact HA | eassumption | lia | lia | cbn [disj_all]; split; [zlia | exact I]]
        | eapply mem_u32_magreeL; [exact HA | eassumption | lia | lia | cbn [disj_all]; split; [zlia | exact I]]
        | eapply mem_arr_magreeL; [exact HA | eassumption | cbn [disj_all]; split; [zlia | exact I]] ].
Qed.

Ltac open_emem H :=
  unfold f_emem in H; cbv zeta in H; fcx_cbn;
  dand H as (E8 & E16 & E32 & E40 & E64 & P60 & P64 & P68 & P72 & P80 & P88 & P104 & P112 & P120 & P124 & Hsane & Hm8 &
                 Hin & HtL & HtD & Hwin & HOB).

Lemma f_frame_magreeL {RCa1 : RunCtx}  : forall cx Rb l ret M0 M,
  fcx_ok cx -> magreeL M0 M [(f_spi cx + -160, 56)] -> f_frame cx Rb l ret M0 -> f_frame cx Rb l ret M.
Proof.
  intros cx Rb l ret M0 M CX HA H.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. unfold f_frame in *. fcx_cbn. pose proof two64_eq as TW64.
  dand H as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
  split_conj; (eapply mem_u64_magreeL; [exact HA | eassumption | lia | lia | cbn [disj_all]; split; [lia | exact I]]).
Qed.

Lemma fast_entry {RCa1 : RunCtx}  : forall cx Rb l M MD T (cin cout hold bits out ret : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  zget_l Rb l kA0 = f_u cx -> zget_l Rb l kA1 = out -> zget_l Rb l kSP = f_spi cx -> zget_l Rb l kRA = ret ->
  zget_l Rb l kGP = f_gp cx -> zget_l Rb l kTP = f_tp cx ->
  f_cout0 cx = cout -> f_bo cx = cout - (out - (f_osz cx - cout)) -> f_osz cx - cout <= out -> out <= f_osz cx ->
  0 <= cin -> cin + 6 <= f_n cx -> 0 <= cout -> cout + 258 <= f_osz cx ->
  0 <= bits -> bits <= 40 -> 0 <= hold -> hold < 2 ^ bits ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_u cx + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_p cx) 7176 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (f_ob cx) (f_osz cx) ->
  f_emem cx cin cout hold bits fo M ->
  (forall R M1,
     f_const cx R [] -> zget_l R [] kS1 = 14 ->
     zget_l R [] kA4 = hold -> zget_l R [] kA6 = f_q cx + cin -> zget_l R [] kS6 = f_ob cx + cout -> zget_l R [] kA5 = bits ->
     f_live cx fo M1 -> f_ro cx M1 -> f_frame cx Rb l ret M1 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (f_p cx + 8) LEN ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M1 [(f_spi cx + -160, 160)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FHEAD (zupd R []) M1 MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FENTRY (zupd Rb l) M MD) T.
Proof.
  intros cx Rb l M MD T cin cout hold bits out ret fo CX Hh La0 La1 Lsp Lra Lgp Ltp
         Eco0 Ebo Hout1 Hout2 Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hh1 Hh2 Wu Wp Wob EM K.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. open_ok CX. unfold f_frame, f_live, f_ro, f_const in K. fcx_cbn.
  clear Spq Sobq Swp Swq Swob Slaob Slap Sdaob Sdap TOKL TOKD Rfin Rfw Cs8.
  zkeys. unfold L_FENTRY, L_FHEAD in *. pose proof two64_eq as TW64. pose proof m1_mod64 as Hm1.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia).
  pose proof (pow2_15 lb ltac:(lia)) as HPl. pose proof (pow2_15 db ltac:(lia)) as HPd.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(spi + -160, 160)] ltac:(ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(spi + -160, 160)]) M) by (apply mpostL_refl).
  remember (zget_l Rb l 9) as v9 eqn:E9. assert (G9 : zget_l Rb l 9 = v9) by (symmetry; exact E9).
  remember (zget_l Rb l 10) as v10 eqn:E10. assert (G10 : zget_l Rb l 10 = v10) by (symmetry; exact E10).
  remember (zget_l Rb l 19) as v19 eqn:E19. assert (G19 : zget_l Rb l 19 = v19) by (symmetry; exact E19).
  remember (zget_l Rb l 20) as v20 eqn:E20. assert (G20 : zget_l Rb l 20 = v20) by (symmetry; exact E20).
  remember (zget_l Rb l 21) as v21 eqn:E21. assert (G21 : zget_l Rb l 21 = v21) by (symmetry; exact E21).
  remember (zget_l Rb l 22) as v22 eqn:E22. assert (G22 : zget_l Rb l 22 = v22) by (symmetry; exact E22).
  remember (zget_l Rb l 23) as v23 eqn:E23. assert (G23 : zget_l Rb l 23 = v23) by (symmetry; exact E23).
  remember (zget_l Rb l 24) as v24 eqn:E24. assert (G24 : zget_l Rb l 24 = v24) by (symmetry; exact E24).
  remember (zget_l Rb l 25) as v25 eqn:E25. assert (G25 : zget_l Rb l 25 = v25) by (symmetry; exact E25).
  remember (zget_l Rb l 26) as v26 eqn:E26. assert (G26 : zget_l Rb l 26 = v26) by (symmetry; exact E26).
  remember (zget_l Rb l 27) as v27 eqn:E27. assert (G27 : zget_l Rb l 27 = v27) by (symmetry; exact E27).
  remember (zget_l Rb l 28) as v28 eqn:E28. assert (G28 : zget_l Rb l 28 = v28) by (symmetry; exact E28).
  zrebase.
  zstep Rfd.
  do 13 (zstep Rfd).
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
    assert (FR : f_frame (FCX u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw) Rb l ret Mc)
      by (unfold f_frame; cbn [f_spi]; zkeys; rewrite <- ?E9, <- ?E10, <- ?E19, <- ?E20, <- ?E21, <- ?E22, <- ?E23, <- ?E24,
            <- ?E25, <- ?E26, <- ?E27, <- ?E28; split_conj; zfact_exact);
    repeat match goal with H : mem_u64 _ Mc _ _ |- _ => clear H end;
    pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) Mc [(spi + -160, 56)] ltac:(ranges_ok_tac)) as HST2;
    assert (HAG2 : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mc X [(spi + -160, 56)]) Mc) by (apply mpostL_refl)
  end.
  pose proof EM as EM0. unfold f_emem in EM0. cbv zeta in EM0. cbn [f_u f_p f_q f_n f_ob f_osz f_w f_whave f_wnext f_wn f_lb f_db f_la f_na f_da f_nd
    f_spi f_bo f_cout0 f_W0 f_s8 f_gp f_tp f_zc f_rdL f_rdD f_fin f_fw] in EM0.
  dand EM0 as (E8 & E16 & E32 & E40 & E64 & P60 & P64 & P68 & P72 & P80 & P88 & P104 & P112 & P120 & P124 & _).
  zbr Rfd false.
  zstep Rfd. zalign.
  zbr Rfd false.
  zderiveL HAG E16 E16'. tstep1 Rfd. clear E16'.
  zderiveL HAG E8 E8'. tstep1 Rfd. clear E8'.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zext32.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd. zbool.
  zstep Rfd. zbool.
  zstep Rfd. zlit.
  zbr Rfd false.
  zderiveL HAG E40 E40'. tstep1 Rfd. clear E40'.
  zderiveL HAG E32 E32'. tstep1 Rfd. clear E32'.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd. zext32.
  zbr Rfd false.
  zstep Rfd. zbool.
  zstep Rfd.
  zstep Rfd.
  zsetreg 0 ltac:(symmetry; apply seqz_xor_neq; lia).
  zstep Rfd. zlit.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zext32.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd. zbool.
  zstep Rfd. zlit.
  zbr Rfd false.
  zderiveL HAG E64 E64'. tstep1 Rfd. clear E64'.
  zbr Rfd false.
  zstep Rfd. zalign.
  zbr Rfd false.
  zderiveL HAG P120 P120'. tstep1 Rfd. clear P120'.
  zstep Rfd.
  zbr Rfd false.
  zderiveL HAG P124 P124'. tstep1 Rfd. clear P124'.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zderiveL HAG P60 P60'. tstep1 Rfd. clear P60'.
  zderiveL HAG P64 P64'. tstep1 Rfd. clear P64'.
  zstep Rfd.
  zderiveL HAG P68 P68'. tstep1 Rfd. clear P68'.
  zderiveL HAG P72 P72'. tstep1 Rfd. clear P72'.
  zstep Rfd.
  zderiveL HAG P80 P80'. tstep1 Rfd. clear P80'.
  zderiveL HAG P88 P88'. tstep1 Rfd. clear P88'.
  zderiveL HAG P104 P104'. tstep1 Rfd. clear P104'.
  zderiveL HAG P112 P112'. tstep1 Rfd. clear P112'.
  zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zsetreg (2 ^ lb - 1) ltac:(symmetry; apply mask_not_sllw; lia).
  zstep Rfd.
  zsetreg (2 ^ db - 1) ltac:(symmetry; apply mask_not_sllw; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. znot.
  zstep Rfd. znot.
  zstep Rfd. zbool.
  clear E8 E16 E32 E40 E64 P60 P64 P68 P72 P80 P88 P104 P112 P120 P124.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
    apply (f_emem_magreeL _ cin cout hold bits fo M Mc CX' (proj1 HAG)) in EM end.
  open_emem EM.
  lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ => eapply (K R Mx) end.
  - split_conj; try zreg.
  - zreg. - zreg. - zreg. - zreg. - zreg.
  - split_conj; assumption.
  - split_conj; try assumption. all: eapply mem_u64_retype; [zfact_exact | lia].
  - pose proof (f_frame_magreeL _ Rb l ret _ _ CX' (proj1 HAG2) FR) as FR1.
    unfold f_frame in FR1. cbn [f_spi] in FR1. cbv [kS0 kS1 kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11] in FR1.
    rewrite <- ?E9, <- ?E10, <- ?E19, <- ?E20, <- ?E21, <- ?E22, <- ?E23, <- ?E24, <- ?E25, <- ?E26, <- ?E27, <- ?E28 in FR1.
    exact FR1.
  - exact Hm8.
  - exact HAG.
Qed.

End T_Fast1E.

Module T_Fast3.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U.T_Fast2.T_Fast1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U.T_Fast2.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.


Lemma fast_decdist {RCa1 : RunCtx}  : forall cx R l M MD T (hold bits v3 v4 v27 : Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> zget_l R l kA4 = hold -> zget_l R l kA6 = v3 -> zget_l R l kS6 = v4 -> zget_l R l kA5 = bits ->
  zget_l R l kS11 = v27 ->
  f_ro cx M ->
  15 <= bits -> bits <= 40 -> 0 <= hold -> hold < 2 ^ bits ->
  (forall R' (k hold' bits' : Z),
     f_const cx R' [] -> zget_l R' [] kA4 = hold' -> zget_l R' [] kA6 = v3 -> zget_l R' [] kS6 = v4 -> zget_l R' [] kA5 = bits' ->
     zget_l R' [] kS11 = v27 ->
     zget_l R' [] kA3 = f_da cx + 4 * k -> zget_l R' [] kT0 = code_op (f_rdD cx k) -> 0 <= k -> k < f_nd cx ->
     16 <= code_op (f_rdD cx k) -> code_op (f_rdD cx k) <= 29 -> 1 <= code_val (f_rdD cx k) ->
     code_val (f_rdD cx k) + 2 ^ (code_op (f_rdD cx k) - 16) - 1 <= 32768 ->
     0 <= bits' -> 1 <= bits - bits' -> bits - bits' <= 15 -> 0 <= hold' -> hold' < 2 ^ bits' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDISTB (zupd R' []) M MD) T) ->
  (forall R' (hold' bits' : Z),
     f_const cx R' [] -> zget_l R' [] kA4 = hold' -> zget_l R' [] kA6 = v3 -> zget_l R' [] kS6 = v4 -> zget_l R' [] kA5 = bits' ->
     0 <= bits' -> 1 <= bits - bits' -> bits - bits' <= 15 -> 0 <= hold' -> hold' < 2 ^ bits' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FBADD (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDLOOK (zupd R l) M MD) T.
Proof.
  intros cx R l M MD T hold bits v3 v4 v27 CX Hh HC La4 La6 Ls6 La5 Ls11 HL Hb1 Hb2 Hh1 Hh2 KDB KBAD.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_const HC. open_ro HL. unfold f_const in KDB, KBAD. fcx_cbn.
  clear Hin HtL Hsane Q40 Q32 Q24 Q16 Q8 Q0.
  clear Sobu Spob Spq Sobq Cw1 Cw2 Swp Swq Swob Slaob Slap Sdaob Sdap TOKL Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cwn4 Cbo1 Cbo2 Cco1 Cco2 Cco3 Cs8 Rfw Rfin
        Calu Calp Call.
  zkeys. unfold L_FDLOOK, L_FDISTB, L_FBADD in *. pose proof two64_eq as TW64. pose proof m1_mod64 as Hm1.
  pose proof (lnot_val_mod' da ltac:(lia)) as Hs9.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia). pose proof (pow2_15 db ltac:(lia)) as HPd.
  zrebase.
  zstep Rfd.
  clear Q48.
  zstep Rfd.
  let x := zlastval in set (i1 := x) in *;
  pose proof (land_mask_range' hold db ltac:(lia)) as Ri1; fold i1 in Ri1.
  clearbody i1.
  pose proof (tab_root_entry DISTS rdD db nd i1 TOKD Ri1) as (Hbits1 & _ & Hext & CASES).
  pose proof (code_op_range (rdD i1)) as Rop1. pose proof (code_val_range (rdD i1)) as Rval1.
  zstep Rfd.
  zsetreg (4 * i1) ltac:(symmetry; apply shiftl_2).
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd. zbool.
  zstep Rfd. zbool.
  zstep Rfd. zlit.
  zbr Rfd false.
  zstep Rfd. zeven.
  zbr Rfd false.
  zbr Rfd false.
  tld4_bits HtD i1.
  zbr Rfd false.
  tld4_op HtD i1.
  zstep Rfd.
  zsetreg (hold / 2 ^ code_bits (rdD i1)) ltac:(symmetry; apply (srl_hold hold bits); lia).
  pose proof (hold_shr_bound hold bits (code_bits (rdD i1)) ltac:(lia) ltac:(lia)) as Hh'.
  zstep Rfd.
  tstep1 Rfd.
  destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
  - apply term_ok_DISTS in TM as (Hb1' & CL).
    destruct CL as [(Hop16 & Hv1 & Hv2 & Hop29) | (H64 & H16 & H32)].
    + pose proof (op_base_tests (code_op (rdD i1)) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
      rewrite shiftl_1_pow in Hv2 by lia.
      zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (KDB Rx i1 (hold / 2 ^ code_bits (rdD i1)) (bits - code_bits (rdD i1))) end.
      all: kfin.
    + pose proof (land_range_r (code_op (rdD i1)) 64 ltac:(lia)) as R64.
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (KBAD Rx (hold / 2 ^ code_bits (rdD i1)) (bits - code_bits (rdD i1))) end.
      all: kfin.
  - pose proof (op_link_tests (code_op (rdD i1)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
    pose proof (pow2_15 (code_op (rdD i1)) ltac:(lia)) as HPo.
    zbr Rfd false.
    zstep Rfd.
    zbr Rfd false.
    tld4_val HtD i1.
    zstep Rfd.
    zsetreg (4 * code_val (rdD i1)) ltac:(symmetry; apply shiftl_2).
    zbr Rfd false.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (2 ^ code_op (rdD i1) - 1) ltac:(symmetry; apply mask_not_sllw; lia).
    zstep Rfd.
    let x := zlastval in set (j := x) in *;
    pose proof (land_mask_range' (hold / 2 ^ code_bits (rdD i1)) (code_op (rdD i1)) ltac:(lia)) as Rj; fold j in Rj.
    clearbody j.
    destruct (SUB j Rj) as [NL2 TM2]. apply term_ok_DISTS in TM2 as (Hbits2 & CL2).
    pose proof (code_op_range (rdD (code_val (rdD i1) + j))) as Rop2.
    zstep Rfd.
    zsetreg (4 * j) ltac:(symmetry; apply shiftl_2).
    zstep Rfd. znot.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd. zeven.
    zbr Rfd true.
    tld4_bits HtD (code_val (rdD i1) + j).
    zbr Rfd false.
    tld4_op HtD (code_val (rdD i1) + j).
    zstep Rfd.
    zsetreg (hold / 2 ^ code_bits (rdD i1) / 2 ^ code_bits (rdD (code_val (rdD i1) + j)))
      ltac:(symmetry; apply (srl_hold _ (bits - code_bits (rdD i1))); lia).
    pose proof (hold_shr_bound (hold / 2 ^ code_bits (rdD i1)) (bits - code_bits (rdD i1))
                  (code_bits (rdD (code_val (rdD i1) + j))) ltac:(lia) ltac:(lia)) as Hh''.
    zstep Rfd.
    tstep1 Rfd.
    destruct CL2 as [(Hop16 & Hv1 & Hv2 & Hop29) | (H64 & H16 & H32)].
    + pose proof (op_base_tests (code_op (rdD (code_val (rdD i1) + j))) ltac:(lia)) as (U16 & U64 & U32 & U240 & U15 & Unz).
      rewrite shiftl_1_pow in Hv2 by lia.
      zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (KDB Rx (code_val (rdD i1) + j) (hold / 2 ^ code_bits (rdD i1) / 2 ^ code_bits (rdD (code_val (rdD i1) + j)))
                  (bits - code_bits (rdD i1) - code_bits (rdD (code_val (rdD i1) + j)))) end.
      all: kfin.
    + pose proof (land_range_r (code_op (rdD (code_val (rdD i1) + j))) 64 ltac:(lia)) as R64.
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (KBAD Rx (hold / 2 ^ code_bits (rdD i1) / 2 ^ code_bits (rdD (code_val (rdD i1) + j)))
                  (bits - code_bits (rdD i1) - code_bits (rdD (code_val (rdD i1) + j)))) end.
      all: kfin.
Qed.

Lemma fast_distb {RCa1 : RunCtx}  : forall cx R l M MD T (k ci co hold bits len : Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> zget_l R l kA4 = hold -> zget_l R l kA6 = f_q cx + ci -> zget_l R l kS6 = f_ob cx + co -> zget_l R l kA5 = bits ->
  zget_l R l kS11 = len ->
  zget_l R l kA3 = f_da cx + 4 * k -> zget_l R l kT0 = code_op (f_rdD cx k) -> 0 <= k -> k < f_nd cx ->
  16 <= code_op (f_rdD cx k) -> code_op (f_rdD cx k) <= 29 -> 1 <= code_val (f_rdD cx k) ->
  code_val (f_rdD cx k) + 2 ^ (code_op (f_rdD cx k) - 16) - 1 <= 32768 ->
  f_ro cx M ->
  0 <= ci -> ci <= f_n cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci -> 0 <= hold -> hold < 2 ^ bits ->
  13 <= 8 * (f_n cx - ci) + bits ->
  f_bo cx <= co -> co <= f_osz cx ->
  (forall R' (ci' hold' bits' dist : Z),
     f_const cx R' [] -> zget_l R' [] kA4 = hold' -> zget_l R' [] kA6 = f_q cx + ci' -> zget_l R' [] kS6 = f_ob cx + co ->
     zget_l R' [] kA5 = bits' -> zget_l R' [] kS11 = len -> zget_l R' [] kS7 = dist -> zget_l R' [] kT1 = f_ob cx + f_bo cx ->
     1 <= dist -> dist <= 32768 -> dist <= co - f_bo cx ->
     ci <= ci' -> ci' <= ci + 2 -> ci' <= f_n cx -> 0 <= bits' -> bits' <= 40 -> bits' <= 8 * ci' -> 0 <= hold' -> hold' < 2 ^ bits' ->
     8 * (f_n cx - ci') + bits' <= 8 * (f_n cx - ci) + bits ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDIRECT (zupd R' []) M MD) T) ->
  (forall R' (ci' hold' bits' dist : Z),
     f_const cx R' [] -> zget_l R' [] kA4 = hold' -> zget_l R' [] kA6 = f_q cx + ci' -> zget_l R' [] kS6 = f_ob cx + co ->
     zget_l R' [] kA5 = bits' -> zget_l R' [] kS11 = len -> zget_l R' [] kS7 = dist -> zget_l R' [] kT1 = f_ob cx + f_bo cx ->
     1 <= dist -> dist <= 32768 -> co - f_bo cx < dist ->
     ci <= ci' -> ci' <= ci + 2 -> ci' <= f_n cx -> 0 <= bits' -> bits' <= 40 -> bits' <= 8 * ci' -> 0 <= hold' -> hold' < 2 ^ bits' ->
     8 * (f_n cx - ci') + bits' <= 8 * (f_n cx - ci) + bits ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FWIN (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDISTB (zupd R l) M MD) T.
Proof.
  intros cx R l M MD T k ci co hold bits len CX Hh HC La4 La6 Ls6 La5 Ls11 La3 Lt0 Hk1 Hk2 Hop1 Hop2 Hv1 Hv2 HL
         Hci1 Hci2 Hb1 Hb2 Hb3 Hh1 Hh2 HA Hco1 Hco2 KDIR KWIN.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  open_ok CX. open_const HC. open_ro HL. unfold f_const in KDIR, KWIN. fcx_cbn.
  clear HtL Hsane Q48 Q40 Q24 Q16 Q8 Q0.
  clear Sobu Spob Spq Sobq Cw1 Cw2 Swp Swq Swob Slaob Slap Sdaob Sdap TOKL TOKD Cwh1 Cwn1 Cwh2 Cwn2 Cwn3 Cwn4 Cco1 Cco2 Cco3 Cs8 Rfw
        Calu Calp Call Cald.
  zkeys. unfold L_FDISTB, L_FDIRECT, L_FWIN in *. pose proof two64_eq as TW64. pose proof m1_mod64 as Hm1.
  assert (HPb : 2 ^ bits <= 2 ^ 40) by (apply pow2_le; lia).
  set (op := code_op (rdD k)) in *.
  pose proof (op_base_tests op ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
  replace (op - 16) with (op + -16) in Hv2 by lia. replace (op - 16) with (op + -16) in T15 by lia.
  pose proof (pow2_15 (op + -16) ltac:(lia)) as HPe.
  assert (J : forall RJ (cj hj bj : Z),
    zget RJ 11 = u -> zget RJ 12 = p -> zget RJ 13 = q + n + -5 -> zget RJ 22 = ob + osz + -257 ->
    zget RJ 31 = la -> zget RJ 32 = da -> zget RJ 21 = 2 ^ lb - 1 -> zget RJ 29 = wnext ->
    zget RJ 25 = - la + -1 -> zget RJ 26 = - da + -1 -> zget RJ 27 = 1 -> zget RJ 9 = -1 -> zget RJ 19 = 2 -> zget RJ 20 = 63 -> zget RJ 18 = 31 ->
    zget RJ 3 = spi + -160 -> zget RJ 4 = vgp -> zget RJ 5 = vtp ->
    zget RJ 15 = hj -> zget RJ 17 = q + cj -> zget RJ 23 = ob + co -> zget RJ 16 = bj -> zget RJ 28 = len ->
    zget RJ 24 = code_val (rdD k) -> zget RJ 14 = op + -16 ->
    ci <= cj -> cj <= ci + 2 -> cj <= n -> op + -16 <= bj -> bj <= 40 -> bj <= 8 * cj -> 0 <= hj -> hj < 2 ^ bj ->
    8 * (n - cj) + bj = 8 * (n - ci) + bits ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 104216 (zupd RJ []) M MD) T).
  { intros RJ cj hj bj G11 G12 G13 G22 G31 G32 G21 G29 G25 G26 G27 G9 G19 G20 G18 G3 G4 G5 G15 G17 G23 G16 G28 G24 G14
           Hcj1 Hcj2 Hcj3 Hbj1 Hbj2 Hbj3 Hhj1 Hhj2 HAj.
    assert (HPbj : 2 ^ bj <= 2 ^ 40) by (apply pow2_le; lia).
    pose proof (land_mask_range' hj (op + -16) ltac:(lia)) as Rm.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (2 ^ (op + -16) - 1) ltac:(symmetry; apply mask_not_sllw; lia).
    zstep Rfd.
    zstep Rfd.
    zsetreg (hj / 2 ^ (op + -16)) ltac:(symmetry; apply (srl_hold hj bj); lia).
    pose proof (hold_shr_bound hj bj (op + -16) ltac:(lia) ltac:(lia)) as Hh'.
    zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    destruct (Z_lt_dec (co - bo) (Z.land hj (2 ^ (op + -16) + -1) + code_val (rdD k))) as [Hw|Hd].
    - zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (KWIN Rx cj (hj / 2 ^ (op + -16)) (bj - (op + -16)) (Z.land hj (2 ^ (op + -16) + -1) + code_val (rdD k))) end.
      all: kfin.
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (KDIR Rx cj (hj / 2 ^ (op + -16)) (bj - (op + -16)) (Z.land hj (2 ^ (op + -16) + -1) + code_val (rdD k))) end.
      all: kfin. }
  clear KDIR KWIN.
  zrebase.
  tld4_val HtD k.
  zstep Rfd.
  zsetreg (op + -16) ltac:(symmetry; exact T15).
  destruct (Z_lt_dec bits (op + -16)) as [Hlt|Hge].
  - zbr Rfd false.
    pose proof (Rfin ci ltac:(lia)) as Rb0.
    zstep Rfd.
    zbr Rfd false.
    tld1 Hin ci Rfin.
    zstep Rfd.
    zsetreg (fin ci * 2 ^ bits) ltac:(symmetry; apply (proj1 (shl_byte _ bits Rb0 ltac:(lia)))).
    tstep1 Rfd.
    zstep Rfd.
    pose proof (hold_pull1 hold bits (fin ci) ltac:(lia) ltac:(lia) Rb0) as HP1.
    destruct (Z_lt_dec (bits + 8) (op + -16)) as [Hlt2|Hge2].
    + zbr Rfd false.
      pose proof (Rfin (ci + 1) ltac:(lia)) as Rb1.
      zbr Rfd false.
      tld1 Hin (ci + 1) Rfin.
      zstep Rfd.
      zstep Rfd.
      zsetreg (fin (ci + 1) * 2 ^ (bits + 8)) ltac:(symmetry; apply (proj1 (shl_byte _ (bits + 8) Rb1 ltac:(lia)))).
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (hold_pull1 (fin ci * 2 ^ bits + hold) (bits + 8) (fin (ci + 1)) ltac:(lia) ltac:(lia) Rb1) as HP2.
      replace (bits + 8 + 8) with (bits + 16) in HP2 by lia.
      assert (HPb2 : 2 ^ (bits + 16) <= 2 ^ 40) by (apply pow2_le; lia).
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (J Rx (ci + 2) (fin (ci + 1) * 2 ^ (bits + 8) + (fin ci * 2 ^ bits + hold)) (bits + 16)) end.
      all: kfin.
    + zbr Rfd true.
      zstep Rfd.
      zstep Rfd.
      assert (HPb1 : 2 ^ (bits + 8) <= 2 ^ 40) by (apply pow2_le; lia).
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (J Rx (ci + 1) (fin ci * 2 ^ bits + hold) (bits + 8)) end.
      all: kfin.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J Rx ci hold bits) end.
    all: kfin.
Qed.
End T_Fast3.

Module T_Fast4.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U.T_Fast2.T_Fast1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U.T_Fast2.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_FC3LOOP : Z := 104924.
Definition L_FC3TAIL : Z := 105036.
Definition L_FWLOOPB : Z := 104360.
Definition L_FWLOOP2 : Z := 104432.
Definition L_FDLOOP : Z := 104516.
Definition L_FDTAIL : Z := 104600.

Definition cregs (cx : fcx) (v1 v3 v7 v28 : Z) (R : tree Z) (l : list (positive * Z)) : Prop :=
  f_const cx R l /\ zget_l R l kA4 = v1 /\ zget_l R l kA6 = v3 /\ zget_l R l kA5 = v7 /\ zget_l R l kS7 = v28.
Ltac open_cregs H := let HC := ident:(HC) in (dand H as (HC & La4 & La6 & La5 & Ls7); open_const HC).
Definition cregs0 (cx : fcx) (v1 v3 v7 : Z) (R : tree Z) (l : list (positive * Z)) : Prop :=
  f_const cx R l /\ zget_l R l kA4 = v1 /\ zget_l R l kA6 = v3 /\ zget_l R l kA5 = v7.
Ltac open_cregs0 H := let HC := ident:(HC) in (dand H as (HC & La4 & La6 & La5); open_const HC).

Definition KL {RCa1 : RunCtx}  (cx : fcx) (M1 : mem) (MD : Model) (T : TSet) (v1 v3 v7 c : Z) : Prop :=
  forall R' M' (fo' : Z -> Z),
    cregs0 cx v1 v3 v7 R' [] -> zget_l R' [] kS6 = f_ob cx + c ->
    f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FLATCH (zupd R' []) M' MD) T.

Ltac prep_copy CX HR HL :=
  open_ok CX; open_cregs HR; open_live HL; fcx_cbn; zkeys; pose proof two64_eq as TW64; pose proof m1_mod64 as Hmod1.
Ltac prep_copy0 CX HR HL :=
  open_ok CX; open_cregs0 HR; open_live HL; fcx_cbn; zkeys; pose proof two64_eq as TW64; pose proof m1_mod64 as Hmod1.

Lemma fast_wloopA {RCa1 : RunCtx}  : forall pc, (pc = 104732 \/ pc = 104840) ->
  forall (N : nat) cx M1 R l M MD T (wi c m v1 v3 v7 v28 v28b : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 v28 R l -> zget_l R l kS11 = v28b ->
  zget_l R l kT4 = f_w cx + wi -> zget_l R l kT1 = f_w cx + wi -> zget_l R l kA3 = f_ob cx + c -> zget_l R l kS6 = f_ob cx + c ->
  zget_l R l kT0 = m ->
  1 <= m -> m <= Z.of_nat N -> 0 <= wi -> wi + m <= f_wn cx -> 0 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R' M' (fo' : Z -> Z),
     cregs cx v1 v3 v7 v28 R' [] -> zget_l R' [] kS11 = v28b ->
     zget_l R' [] kT4 = f_w cx + wi + m -> zget_l R' [] kT1 = f_w cx + wi + m ->
     zget_l R' [] kA3 = f_ob cx + c + m -> zget_l R' [] kS6 = f_ob cx + c + m -> zget_l R' [] kRA = f_ob cx + c + m ->
     f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (pc + 44) (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd R l) M MD) T.
Proof.
  intros pc Hpc N. induction N as [|N IH]; intros cx M1 R l M MD T wi c m v1 v3 v7 v28 v28b fo CX Hh HR Ls11 Lt4 Lt1 La3 Ls6 Lt0
    Hm1 Hm2 Hwi1 Hwi2 Hc1 Hc2 HL Rfo HAG K; [lia|].
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. prep_copy CX HR HL. unfold cregs, f_const, f_live, FPW in K, IH |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  pose proof (Rfw wi ltac:(lia)) as Rb.
  destruct Hpc as [-> | ->].
  all: zrebase;
    zstep Rfd;
    zbr Rfd false;
    zstep Rfd;
    zbr Rfd false;
    tld1 Hwin wi Rfw;
    zstep Rfd;
    zstep Rfd;
    tstep1 Rfd;
    tstore_arr Rfd HOB c;
    zstep Rfd;
    pose proof (zfupd_byte fo c (fw wi) 0 osz Rfo Rb) as Rfo';
    (destruct (Z.eq_dec m 1) as [E1|N1];
     [ zbr Rfd false;
       lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd fo c (fw wi))) end; kfin
     | zbr Rfd true;
       lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
         eapply (IH _ M1 Rx [] Mx MD T (wi + 1) (c + 1) (m - 1) v1 v3 v7 v28 v28b (zfupd fo c (fw wi)) CX' Hh) end;
       [ (fcx_cbn; kfin) .. | ] ]).
  all: intros R' M' fo' HR' Ls11' Lt4' Lt1' La3' Ls6' Lra' HL' Rfo'' HAG'; fcx_cbn;
       lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K R' M' fo') end; kfin.
Qed.

Lemma fast_wloopB {RCa1 : RunCtx}  : forall (N : nat) cx M1 R l M MD T (wi c m v1 v3 v7 v28 v28b : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 v28 R l -> zget_l R l kS11 = v28b ->
  zget_l R l kT4 = f_w cx + wi -> zget_l R l kT1 = f_w cx + wi -> zget_l R l kT2 = f_ob cx + c -> zget_l R l kS6 = f_ob cx + c ->
  zget_l R l kT0 = f_ob cx + c + 1 -> zget_l R l kRA = m ->
  1 <= m -> m <= Z.of_nat N -> 0 <= wi -> wi + m <= f_wn cx -> 0 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R' M' (fo' : Z -> Z),
     cregs cx v1 v3 v7 v28 R' [] -> zget_l R' [] kS11 = v28b ->
     zget_l R' [] kT4 = f_w cx + wi + m -> zget_l R' [] kT1 = f_w cx + wi + m ->
     zget_l R' [] kS6 = f_ob cx + c + m -> zget_l R' [] kA3 = f_ob cx + c + m -> zget_l R' [] kS1 = f_ob cx + c + m ->
     f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (L_FWLOOPB + 52) (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FWLOOPB (zupd R l) M MD) T.
Proof.
  induction N as [|N IH]; intros cx M1 R l M MD T wi c m v1 v3 v7 v28 v28b fo CX Hh HR Ls11 Lt4 Lt1 Lt2 Ls6 Lt0 Lra
    Hm1 Hm2 Hwi1 Hwi2 Hc1 Hc2 HL Rfo HAG K; [lia|].
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. prep_copy CX HR HL. unfold cregs, f_const, f_live, FPW, L_FWLOOPB in K, IH |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  pose proof (Rfw wi ltac:(lia)) as Rb.
  zrebase.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  tld1 Hwin wi Rfw.
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  tstore_arr Rfd HOB c.
  zstep Rfd.
  zstep Rfd.
  pose proof (zfupd_byte fo c (fw wi) 0 osz Rfo Rb) as Rfo'.
  destruct (Z.eq_dec m 1) as [E1|N1].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd fo c (fw wi))) end; kfin.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH _ M1 Rx [] Mx MD T (wi + 1) (c + 1) (m - 1) v1 v3 v7 v28 v28b (zfupd fo c (fw wi)) CX' Hh) end.
    all: try (fcx_cbn; kfin).
    intros R' M' fo' HR' Ls11' Lt4' Lt1' Ls6' La3' Ls1' HL' Rfo'' HAG'; fcx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K R' M' fo') end; kfin.
Qed.

Lemma fast_wloop2 {RCa1 : RunCtx}  : forall (N : nat) cx M1 R l M MD T (wi c m v1 v3 v7 v28 v28b : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 v28 R l -> zget_l R l kS11 = v28b ->
  zget_l R l kT0 = f_w cx + wi -> zget_l R l kT2 = f_w cx + wi -> zget_l R l kA3 = f_ob cx + c -> zget_l R l kS1 = f_ob cx + c ->
  zget_l R l kT4 = m ->
  1 <= m -> m <= Z.of_nat N -> 0 <= wi -> wi + m <= f_wn cx -> 0 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R' M' (fo' : Z -> Z),
     cregs cx v1 v3 v7 v28 R' [] -> zget_l R' [] kS11 = v28b ->
     zget_l R' [] kA3 = f_ob cx + c + m -> zget_l R' [] kS1 = f_ob cx + c + m -> zget_l R' [] kRA = f_ob cx + c + m ->
     f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (L_FWLOOP2 + 44) (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FWLOOP2 (zupd R l) M MD) T.
Proof.
  induction N as [|N IH]; intros cx M1 R l M MD T wi c m v1 v3 v7 v28 v28b fo CX Hh HR Ls11 Lt0 Lt2 La3 Ls1 Lt4
    Hm1 Hm2 Hwi1 Hwi2 Hc1 Hc2 HL Rfo HAG K; [lia|].
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. prep_copy CX HR HL. unfold cregs, f_const, f_live, FPW, L_FWLOOP2 in K, IH |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  pose proof (Rfw wi ltac:(lia)) as Rb.
  zrebase.
  zstep Rfd.
  zbr Rfd false.
  zbr Rfd false.
  tld1 Hwin wi Rfw.
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  tstore_arr Rfd HOB c.
  zstep Rfd.
  zstep Rfd.
  pose proof (zfupd_byte fo c (fw wi) 0 osz Rfo Rb) as Rfo'.
  destruct (Z.eq_dec m 1) as [E1|N1].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd fo c (fw wi))) end; kfin.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH _ M1 Rx [] Mx MD T (wi + 1) (c + 1) (m - 1) v1 v3 v7 v28 v28b (zfupd fo c (fw wi)) CX' Hh) end.
    all: try (fcx_cbn; kfin).
    intros R' M' fo' HR' Ls11' La3' Ls1' Lra' HL' Rfo'' HAG'; fcx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K R' M' fo') end; kfin.
Qed.

Lemma fast_c3loop_w {RCa1 : RunCtx}  : forall (N : nat) cx M1 R l M MD T (wi c m v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs0 cx v1 v3 v7 R l ->
  zget_l R l kT0 = f_w cx + wi -> zget_l R l kT4 = f_w cx + wi -> zget_l R l kA3 = f_ob cx + c -> zget_l R l kRA = f_ob cx + c ->
  zget_l R l kS11 = m ->
  3 <= m -> m <= Z.of_nat N -> 0 <= wi -> wi + m <= f_wn cx -> 0 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R' M' (fo' : Z -> Z) (k : Z),
     cregs0 cx v1 v3 v7 R' [] ->
     zget_l R' [] kT4 = f_w cx + wi + k -> zget_l R' [] kRA = f_ob cx + c + k -> zget_l R' [] kS11 = m - k ->
     3 <= k -> k <= m -> m - k <= 2 ->
     f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FC3TAIL (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FC3LOOP (zupd R l) M MD) T.
Proof.
  induction N as [|N IH]; intros cx M1 R l M MD T wi c m v1 v3 v7 fo CX Hh HR Lt0 Lt4 La3 Lra Ls11
    Hm1 Hm2 Hwi1 Hwi2 Hc1 Hc2 HL Rfo HAG K; [lia|].
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. prep_copy0 CX HR HL. unfold cregs0, f_const, f_live, FPW, L_FC3LOOP, L_FC3TAIL in K, IH |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  pose proof (Rfw wi ltac:(lia)) as Rb0. pose proof (Rfw (wi + 1) ltac:(lia)) as Rb1. pose proof (Rfw (wi + 2) ltac:(lia)) as Rb2.
  zrebase.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  tld1 Hwin wi Rfw.
  zstep Rfd.
  tstore_arr Rfd HOB c.
  pose proof (zfupd_byte fo c (fw wi) 0 osz Rfo Rb0) as Rfo1.
  zbr Rfd false.
  zstep Rfd.
  zbr Rfd false.
  tld1 Hwin (wi + 1) Rfw.
  zstep Rfd.
  tstore_arr Rfd HOB (c + 1).
  pose proof (zfupd_byte _ (c + 1) (fw (wi + 1)) 0 osz Rfo1 Rb1) as Rfo2.
  zbr Rfd false.
  zstep Rfd.
  zbr Rfd false.
  tld1 Hwin (wi + 2) Rfw.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  tstore_arr Rfd HOB (c + 2).
  pose proof (zfupd_byte _ (c + 2) (fw (wi + 2)) 0 osz Rfo2 Rb2) as Rfo3.
  zstep Rfd.
  destruct (Z_lt_dec 2 (m - 3)) as [Hgo|Hstop].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH _ M1 Rx [] Mx MD T (wi + 3) (c + 3) (m - 3) v1 v3 v7 _ CX' Hh) end.
    all: try (fcx_cbn; kfin).
    intros R' M' fo' k HR' Lt4' Lra' Ls11' Hk1 Hk2 Hk3 HL' Rfo'' HAG'; fcx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K R' M' fo' (k + 3)) end; kfin.
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx _ 3) end; kfin.
Qed.

Lemma fast_c3loop_o {RCa1 : RunCtx}  : forall (N : nat) cx M1 R l M MD T (s c m v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs0 cx v1 v3 v7 R l ->
  zget_l R l kT0 = f_ob cx + s -> zget_l R l kT4 = f_ob cx + s -> zget_l R l kA3 = f_ob cx + c -> zget_l R l kRA = f_ob cx + c ->
  zget_l R l kS11 = m ->
  3 <= m -> m <= Z.of_nat N -> 0 <= s -> s + 1 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R' M' (fo' : Z -> Z) (k : Z),
     cregs0 cx v1 v3 v7 R' [] ->
     zget_l R' [] kT4 = f_ob cx + s + k -> zget_l R' [] kRA = f_ob cx + c + k -> zget_l R' [] kS11 = m - k ->
     3 <= k -> k <= m -> m - k <= 2 ->
     f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FC3TAIL (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FC3LOOP (zupd R l) M MD) T.
Proof.
  induction N as [|N IH]; intros cx M1 R l M MD T s c m v1 v3 v7 fo CX Hh HR Lt0 Lt4 La3 Lra Ls11
    Hm1 Hm2 Hs1 Hs2 Hc2 HL Rfo HAG K; [lia|].
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. prep_copy0 CX HR HL. unfold cregs0, f_const, f_live, FPW, L_FC3LOOP, L_FC3TAIL in K, IH |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  zrebase.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  pose proof (Rfo s ltac:(lia)) as Rb0.
  tld1 HOB s Rfo.
  zstep Rfd.
  tstore_arr Rfd HOB c.
  pose proof (zfupd_byte fo c (fo s) 0 osz Rfo Rb0) as Rfo1.
  zbr Rfd false.
  zstep Rfd.
  zbr Rfd false.
  pose proof (Rfo1 (s + 1) ltac:(lia)) as Rb1.
  tld1 HOB (s + 1) Rfo1.
  zstep Rfd.
  tstore_arr Rfd HOB (c + 1).
  pose proof (zfupd_byte _ (c + 1) _ 0 osz Rfo1 Rb1) as Rfo2.
  zbr Rfd false.
  zstep Rfd.
  zbr Rfd false.
  pose proof (Rfo2 (s + 2) ltac:(lia)) as Rb2.
  tld1 HOB (s + 2) Rfo2.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  tstore_arr Rfd HOB (c + 2).
  pose proof (zfupd_byte _ (c + 2) _ 0 osz Rfo2 Rb2) as Rfo3.
  zstep Rfd.
  destruct (Z_lt_dec 2 (m - 3)) as [Hgo|Hstop].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH _ M1 Rx [] Mx MD T (s + 3) (c + 3) (m - 3) v1 v3 v7 _ CX' Hh) end.
    all: try (fcx_cbn; kfin).
    intros R' M' fo' k HR' Lt4' Lra' Ls11' Hk1 Hk2 Hk3 HL' Rfo'' HAG'; fcx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K R' M' fo' (k + 3)) end; kfin.
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx _ 3) end; kfin.
Qed.

Lemma fast_dloop {RCa1 : RunCtx}  : forall (N : nat) cx M1 R l M MD T (c0 off m dist v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs0 cx v1 v3 v7 R l ->
  zget_l R l kT4 = f_ob cx + c0 - dist -> zget_l R l kS6 = f_ob cx + c0 -> zget_l R l kT0 = off -> zget_l R l kS11 = m ->
  3 <= m -> m <= Z.of_nat N -> 1 <= dist -> dist <= c0 -> 0 <= off -> c0 + off + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R' M' (fo' : Z -> Z) (k : Z),
     cregs0 cx v1 v3 v7 R' [] ->
     zget_l R' [] kT4 = f_ob cx + c0 - dist -> zget_l R' [] kS6 = f_ob cx + c0 -> zget_l R' [] kT0 = off + k -> zget_l R' [] kS11 = m - k ->
     3 <= k -> k <= m -> m - k <= 2 ->
     f_live cx fo' M' -> (forall i, 0 <= i < f_osz cx -> 0 <= fo' i < 256) ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDTAIL (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDLOOP (zupd R l) M MD) T.
Proof.
  induction N as [|N IH]; intros cx M1 R l M MD T c0 off m dist v1 v3 v7 fo CX Hh HR Lt4 Ls6 Lt0 Ls11
    Hm1 Hm2 Hd1 Hd2 Hoff Hc2 HL Rfo HAG K; [lia|].
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  pose proof CX as CX'. prep_copy0 CX HR HL. unfold cregs0, f_const, f_live, FPW, L_FDLOOP, L_FDTAIL in K, IH |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  zrebase.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  pose proof (Rfo (c0 - dist + off) ltac:(lia)) as Rb0.
  tld1 HOB (c0 - dist + off) Rfo.
  tstore_arr Rfd HOB (c0 + off).
  pose proof (zfupd_byte fo (c0 + off) (fo (c0 - dist + off)) 0 osz Rfo Rb0) as Rfo1.
  zbr Rfd false.
  zbr Rfd false.
  pose proof (Rfo1 (c0 - dist + off + 1) ltac:(lia)) as Rb1.
  tld1 HOB (c0 - dist + off + 1) Rfo1.
  zstep Rfd.
  tstore_arr Rfd HOB (c0 + off + 1).
  pose proof (zfupd_byte _ (c0 + off + 1) _ 0 osz Rfo1 Rb1) as Rfo2.
  zbr Rfd false.
  zstep Rfd.
  zbr Rfd false.
  pose proof (Rfo2 (c0 - dist + off + 2) ltac:(lia)) as Rb2.
  tld1 HOB (c0 - dist + off + 2) Rfo2.
  tstep1 Rfd.
  tstore_arr Rfd HOB (c0 + off + 2).
  pose proof (zfupd_byte _ (c0 + off + 2) _ 0 osz Rfo2 Rb2) as Rfo3.
  zstep Rfd.
  destruct (Z_lt_dec 2 (m - 3)) as [Hgo|Hstop].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH _ M1 Rx [] Mx MD T c0 (off + 3) (m - 3) dist v1 v3 v7 _ CX' Hh) end.
    all: try (fcx_cbn; kfin).
    intros R' M' fo' k HR' Lt4' Ls6' Lt0' Ls11' Hk1 Hk2 Hk3 HL' Rfo'' HAG'; fcx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K R' M' fo' (k + 3)) end; kfin.
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx _ 3) end; kfin.
Qed.
End T_Fast4.

Module T_Fast5.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U.T_Fast2.T_Fast1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U.T_Fast2 T_Fast4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.


Definition L_FFROMOUT : Z := 104888.
Definition L_FCOPY3W : Z := 104904.
Definition L_FFROMWIN : Z := 105100.

Lemma fast_c3tail_w {RCa1 : RunCtx}  : forall cx M1 R l M MD T (wi c m v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs0 cx v1 v3 v7 R l ->
  zget_l R l kT4 = f_w cx + wi -> zget_l R l kRA = f_ob cx + c -> zget_l R l kS11 = m ->
  0 <= m -> m <= 2 -> 0 <= wi -> wi + m <= f_wn cx -> 0 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 (c + m) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FC3TAIL (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T wi c m v1 v3 v7 fo CX Hh HR Lt4 Lra Ls11 Hm1 Hm2 Hwi1 Hwi2 Hc1 Hc2 HL Rfo HAG K.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy0 CX HR HL. unfold KL, cregs0, f_const, f_live, FPW, L_FC3TAIL, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  zrebase.
  destruct (Z.eq_dec m 0) as [E0|N0].
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx fo) end; kfin.
  - zbr Rfd false.
    pose proof (Rfw wi ltac:(lia)) as Rb0.
    zstep Rfd.
    zbr Rfd false.
    zstep Rfd.
    zbr Rfd false.
    tld1 Hwin wi Rfw.
    tstore_arr Rfd HOB c.
    pose proof (zfupd_byte fo c (fw wi) 0 osz Rfo Rb0) as Rfo1.
    destruct (Z.eq_dec m 2) as [E2|N2].
    + zbr Rfd false.
      zbr Rfd false.
      zbr Rfd false.
      pose proof (Rfw (wi + 1) ltac:(lia)) as Rb1.
      tld1 Hwin (wi + 1) Rfw.
      zstep Rfd.
      tstore_arr Rfd HOB (c + 1).
      pose proof (zfupd_byte _ (c + 1) (fw (wi + 1)) 0 osz Rfo1 Rb1) as Rfo2.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end; kfin.
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end; kfin.
Qed.

Lemma fast_c3tail_o {RCa1 : RunCtx}  : forall cx M1 R l M MD T (s c m v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs0 cx v1 v3 v7 R l ->
  zget_l R l kT4 = f_ob cx + s -> zget_l R l kRA = f_ob cx + c -> zget_l R l kS11 = m ->
  0 <= m -> m <= 2 -> 0 <= s -> s + 1 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 (c + m) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FC3TAIL (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T s c m v1 v3 v7 fo CX Hh HR Lt4 Lra Ls11 Hm1 Hm2 Hs1 Hs2 Hc2 HL Rfo HAG K.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy0 CX HR HL. unfold KL, cregs0, f_const, f_live, FPW, L_FC3TAIL, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  zrebase.
  destruct (Z.eq_dec m 0) as [E0|N0].
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx fo) end; kfin.
  - zbr Rfd false.
    pose proof (Rfo s ltac:(lia)) as Rb0.
    zstep Rfd.
    zbr Rfd false.
    zstep Rfd.
    zbr Rfd false.
    tld1 HOB s Rfo.
    tstore_arr Rfd HOB c.
    pose proof (zfupd_byte fo c (fo s) 0 osz Rfo Rb0) as Rfo1.
    destruct (Z.eq_dec m 2) as [E2|N2].
    + zbr Rfd false.
      zbr Rfd false.
      zbr Rfd false.
      pose proof (Rfo1 (s + 1) ltac:(lia)) as Rb1.
      tld1 HOB (s + 1) Rfo1.
      zstep Rfd.
      tstore_arr Rfd HOB (c + 1).
      pose proof (zfupd_byte _ (c + 1) _ 0 osz Rfo1 Rb1) as Rfo2.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end; kfin.
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end; kfin.
Qed.

Lemma fast_copy3_w {RCa1 : RunCtx}  : forall cx M1 R l M MD T (wi c m v1 v3 v7 v28 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 v28 R l ->
  zget_l R l kT4 = f_w cx + wi -> zget_l R l kS6 = f_ob cx + c -> zget_l R l kS11 = m ->
  0 <= m -> m <= 258 -> 0 <= wi -> wi + m <= f_wn cx -> 0 <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 (c + m) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FCOPY3W (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T wi c m v1 v3 v7 v28 fo CX Hh HR Lt4 Ls6 Ls11 Hm1 Hm2 Hwi1 Hwi2 Hc1 Hc2 HL Rfo HAG K.
  pose proof CX as CX'. pose proof HL as HL'.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. unfold KL, cregs0, f_const, f_live, FPW, L_FCOPY3W, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  clear Wu Wp Wob Hwin HOB.
  zstep Rfd.
  zstep Rfd.
  destruct (Z_lt_dec m 3) as [Hlt|Hge].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_c3tail_w _ M1 Rx lx Mx MD T wi c m v1 v3 v7 fo CX' Hh) end.
    all: try (unfold cregs0, f_const; fcx_cbn; kfin). all: exact K.
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_c3loop_w (Z.to_nat m) _ M1 Rx lx Mx MD T wi c m v1 v3 v7 fo CX' Hh) end.
    all: try (unfold cregs0, f_const; fcx_cbn; kfin).
    intros R' M' fo' k HR2 Lt4' Lra' Ls11' Hk1 Hk2 Hk3 HL2 Rfo' HAG'. fcx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_c3tail_w _ M1 Rx lx Mx MD T (wi + k) (c + k) (m - k) v1 v3 v7 fo' CX' Hh) end.
    all: try (unfold cregs0, f_const; fcx_cbn; kfin).
    all: replace (c + k + (m - k)) with (c + m) by lia; exact K.
Qed.

Lemma fast_copy3_o {RCa1 : RunCtx}  : forall cx M1 R l M MD T (c m v1 v3 v7 dist : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  zget_l R l kRA = f_ob cx + c -> zget_l R l kS11 = m ->
  0 <= m -> m <= 258 -> 1 <= dist -> dist <= c -> c + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 (c + m) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FFROMOUT (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T c m v1 v3 v7 dist fo CX Hh HR Lra Ls11 Hm1 Hm2 Hd1 Hd2 Hc2 HL Rfo HAG K.
  pose proof CX as CX'. pose proof HL as HL'.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. unfold KL, cregs0, f_const, f_live, FPW, L_FFROMOUT, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  clear Wu Wp Wob Hwin HOB.
  zstep Rfd.
  zstep Rfd.
  destruct (Z_lt_dec m 3) as [Hlt|Hge].
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_c3tail_o _ M1 Rx lx Mx MD T (c - dist) c m v1 v3 v7 fo CX' Hh) end.
    all: try (unfold cregs0, f_const; fcx_cbn; kfin). all: exact K.
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_c3loop_o (Z.to_nat m) _ M1 Rx lx Mx MD T (c - dist) c m v1 v3 v7 fo CX' Hh) end.
    all: try (unfold cregs0, f_const; fcx_cbn; kfin).
    intros R' M' fo' k HR2 Lt4' Lra' Ls11' Hk1 Hk2 Hk3 HL2 Rfo' HAG'. fcx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_c3tail_o _ M1 Rx lx Mx MD T (c - dist + k) (c + k) (m - k) v1 v3 v7 fo' CX' Hh) end.
    all: try (unfold cregs0, f_const; fcx_cbn; kfin).
    all: replace (c + k + (m - k)) with (c + m) by lia; exact K.
Qed.

Lemma fast_fromwin {RCa1 : RunCtx}  : forall cx M1 R l M MD T (c m v1 v3 v7 v28 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 v28 R l ->
  zget_l R l kA3 = f_ob cx + c -> zget_l R l kS11 = m ->
  0 <= m -> m <= 258 -> m <= f_wn cx -> 0 <= c -> c + m <= f_osz cx ->
  f_ro cx M1 -> f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 (c + m) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FFROMWIN (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T c m v1 v3 v7 v28 fo CX Hh HR La3 Ls11 Hm1 Hm2 Hm3 Hc1 Hc2 HRO1 HL Rfo HAG K.
  pose proof CX as CX'. pose proof HL as HL'. pose proof (f_ro_now _ M1 M CX HRO1 HAG) as HRO.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. open_ro HRO. unfold KL, cregs0, f_const, f_live, FPW, L_FFROMWIN, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  clear Wu Wp Wob Hwin HOB Hin HtL HtD Hsane Q48 Q32 Q24 Q16 Q8 Q0.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  destruct (Z_lt_dec m 3) as [Hlt|Hge].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_c3tail_w _ M1 Rx lx Mx MD T 0 c m v1 v3 v7 fo CX' Hh) end.
    all: try (unfold cregs0, f_const; fcx_cbn; kfin). all: exact K.
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_c3loop_w (Z.to_nat m) _ M1 Rx lx Mx MD T 0 c m v1 v3 v7 fo CX' Hh) end.
    all: try (unfold cregs0, f_const; fcx_cbn; kfin).
    intros R' M' fo' k HR2 Lt4' Lra' Ls11' Hk1 Hk2 Hk3 HL2 Rfo' HAG'. fcx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_c3tail_w _ M1 Rx lx Mx MD T (0 + k) (c + k) (m - k) v1 v3 v7 fo' CX' Hh) end.
    all: try (unfold cregs0, f_const; fcx_cbn; kfin).
    all: replace (c + k + (m - k)) with (c + m) by lia; exact K.
Qed.

End T_Fast5.

Module T_Fast5W.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U.T_Fast2.T_Fast1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U.T_Fast2 T_Fast4 T_Fast5.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.


Definition L_FW0 : Z := 104668.
Definition L_FCONTIG : Z := 104780.
Definition L_FWRAP : Z := 104288.

Lemma fast_w0 {RCa1 : RunCtx}  : forall cx M1 R l M MD T (co len dist op v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  zget_l R l kS6 = f_ob cx + co -> zget_l R l kS11 = len -> zget_l R l kT0 = op ->
  3 <= len -> len <= 258 -> 0 <= co -> co + len <= f_osz cx -> f_bo cx <= co ->
  op = dist - (co - f_bo cx) -> 1 <= op -> op <= f_whave cx -> dist <= 32768 ->
  f_ro cx M1 -> f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 (co + len) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FW0 (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T co len dist op v1 v3 v7 fo CX Hh HR Ls6 Ls11 Lt0 Hl1 Hl2 Hco1 Hco2 Hbo Hop Hop1 Hop2 Hd HRO1 HL Rfo HAG K.
  pose proof CX as CX'. pose proof HL as HL'. pose proof (f_ro_now _ M1 M CX HRO1 HAG) as HRO.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. open_ro HRO. unfold KL, cregs, cregs0, f_const, f_live, FPW, L_FW0, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  clear Wu Wp Wob Hwin HOB Hin HtL HtD Hsane Q48 Q32 Q24 Q16 Q0.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd. zext32.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd. zbool.
  zstep Rfd. zbool.
  zstep Rfd. zlit.
  zbr Rfd false.
  clear Q8 Q40.
  destruct (Z_lt_dec op len) as [Hlt|Hge].
  - zbr Rfd false.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_wloopA 104732 ltac:(lia) (Z.to_nat op) _ M1 Rx lx Mx MD T (wn - op) co op v1 v3 v7 dist (len - op) fo CX' Hh) end.
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
    intros R' M' fo' HR2 Ls11' Lt4' Lt1' La3' Ls6' Lra' HL2 Rfo' HAG'. fcx_cbn.
    pose proof HR2 as HR3. dand HR2 as (HC2 & La4' & La6' & La5' & Ls7'). unfold f_const in HC2. fcx_cbn. destr_conj HC2.
    zkeys. zgetl0. zpc_norm.
    zstep Rfd.
    zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_copy3_o _ M1 Rx lx Mx MD T (co + op) (len - op) v1 v3 v7 dist fo' CX' Hh) end.
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
    all: replace (co + op + (len - op)) with (co + len) by lia; exact K.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_copy3_w _ M1 Rx lx Mx MD T (wn - op) co len v1 v3 v7 dist fo CX' Hh) end.
    all: try (unfold cregs, f_const; fcx_cbn; kfin). all: exact K.
Qed.

Lemma fast_contig {RCa1 : RunCtx}  : forall cx M1 R l M MD T (co len dist op v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  zget_l R l kS6 = f_ob cx + co -> zget_l R l kS11 = len -> zget_l R l kT0 = op ->
  3 <= len -> len <= 258 -> 0 <= co -> co + len <= f_osz cx -> f_bo cx <= co ->
  op = dist - (co - f_bo cx) -> 1 <= op -> op <= f_whave cx -> op <= f_wnext cx -> dist <= 32768 ->
  f_ro cx M1 -> f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 (co + len) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FCONTIG (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T co len dist op v1 v3 v7 fo CX Hh HR Ls6 Ls11 Lt0 Hl1 Hl2 Hco1 Hco2 Hbo Hop Hop1 Hop2 Hop3 Hd HRO1 HL Rfo HAG K.
  pose proof CX as CX'. pose proof HL as HL'. pose proof (f_ro_now _ M1 M CX HRO1 HAG) as HRO.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. open_ro HRO. unfold KL, cregs, cregs0, f_const, f_live, FPW, L_FCONTIG, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  clear Wu Wp Wob Hwin HOB Hin HtL HtD Hsane Q48 Q32 Q24 Q16 Q8 Q0.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd. zext32.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd. zbool.
  zstep Rfd. zbool.
  zstep Rfd. zlit.
  zbr Rfd false.
  clear Q40.
  destruct (Z_lt_dec op len) as [Hlt|Hge].
  - zbr Rfd false.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_wloopA 104840 ltac:(lia) (Z.to_nat op) _ M1 Rx lx Mx MD T (wnext - op) co op v1 v3 v7 dist (len - op) fo CX' Hh) end.
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
    intros R' M' fo' HR2 Ls11' Lt4' Lt1' La3' Ls6' Lra' HL2 Rfo' HAG'. fcx_cbn.
    pose proof HR2 as HR3. dand HR2 as (HC2 & La4' & La6' & La5' & Ls7'). unfold f_const in HC2. fcx_cbn. destr_conj HC2.
    zkeys. zgetl0. zpc_norm.
    zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_copy3_o _ M1 Rx lx Mx MD T (co + op) (len - op) v1 v3 v7 dist fo' CX' Hh) end.
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
    all: replace (co + op + (len - op)) with (co + len) by lia; exact K.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_copy3_w _ M1 Rx lx Mx MD T (wnext - op) co len v1 v3 v7 dist fo CX' Hh) end.
    all: try (unfold cregs, f_const; fcx_cbn; kfin). all: exact K.
Qed.

Lemma fast_wrap {RCa1 : RunCtx}  : forall cx M1 R l M MD T (co len dist op v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  zget_l R l kS6 = f_ob cx + co -> zget_l R l kS11 = len -> zget_l R l kT0 = op ->
  3 <= len -> len <= 258 -> 0 <= co -> co + len <= f_osz cx -> f_bo cx <= co ->
  op = dist - (co - f_bo cx) -> 1 <= op -> op <= f_whave cx -> 0 < f_wnext cx -> f_wnext cx < op -> dist <= 32768 ->
  f_ro cx M1 -> f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 (co + len) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FWRAP (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T co len dist op v1 v3 v7 fo CX Hh HR Ls6 Ls11 Lt0 Hl1 Hl2 Hco1 Hco2 Hbo Hop Hop1 Hop2 Hwn1 Hwn2 Hd
         HRO1 HL Rfo HAG K.
  pose proof CX as CX'. pose proof HL as HL'. pose proof (f_ro_now _ M1 M CX HRO1 HAG) as HRO.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. open_ro HRO. unfold KL, cregs, cregs0, f_const, f_live, FPW, L_FWRAP, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  clear Wu Wp Wob Hwin HOB Hin HtL HtD Hsane Q48 Q32 Q24 Q16 Q8.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd. zext32.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd. zbool.
  zstep Rfd. zbool.
  zstep Rfd. zlit.
  zbr Rfd false.
  clear Q0 Q40.
  tstep1 Rfd.
  destruct (Z_lt_dec (op - wnext) len) as [Hlt|Hge].
  - zbr Rfd false.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_wloopB (Z.to_nat op) _ M1 Rx lx Mx MD T (wn + wnext - op) co (op - wnext) v1 v3 v7 dist (len - (op - wnext)) fo CX' Hh) end.
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
    intros R' M' fo' HR2 Ls11' Lt4' Lt1' Ls6' La3' Ls1' HL2 Rfo' HAG'. fcx_cbn.
    pose proof HR2 as HR3. dand HR2 as (HC2 & La4' & La6' & La5' & Ls7'). unfold f_const in HC2. fcx_cbn. destr_conj HC2.
    unfold L_FWLOOPB. zkeys. zgetl0. zpc_norm.
    destruct (Z_le_dec (len - (op - wnext)) wnext) as [Hle|Hgt].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_fromwin _ M1 Rx lx Mx MD T (co + (op - wnext)) (len - (op - wnext)) v1 v3 v7 dist fo' CX' Hh) end.
      all: try (unfold cregs, f_const; fcx_cbn; kfin). all: try exact HRO1.
      all: replace (co + (op - wnext) + (len - (op - wnext))) with (co + len) by lia; exact K.
    + zbr Rfd false.
      tstep1 Rfd.
      pose proof (f_ro_now _ M1 M' CX' HRO1 HAG') as HRO'. unfold f_ro in HRO'. cbn [f_q f_n f_fin f_la f_na f_rdL f_da f_nd f_rdD f_p f_spi f_db f_w f_ob f_bo f_whave f_wn f_wnext] in HRO'.
      dand HRO' as (_ & _ & _ & _ & _ & Q40' & _).
      zstep Rfd.
      clear Q40'.
      zstep Rfd.
      zstep Rfd.
      pose proof HL2 as HL3. unfold f_live in HL3.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_wloop2 (Z.to_nat wnext) _ M1 Rx lx Mx MD T 0 (co + (op - wnext)) wnext v1 v3 v7 dist (len - (op - wnext) - wnext) fo' CX' Hh) end.
      all: try (unfold cregs, f_const; fcx_cbn; kfin).
      intros R'' M'' fo'' HR4 Ls11'' La3'' Ls1'' Lra'' HL4 Rfo'' HAG''. fcx_cbn.
      pose proof HR4 as HR5. dand HR4 as (HC4 & La4'' & La6'' & La5'' & Ls7''). unfold f_const in HC4. fcx_cbn. destr_conj HC4.
      unfold L_FWLOOP2. zkeys. zgetl0. zpc_norm.
      zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_copy3_o _ M1 Rx lx Mx MD T (co + op) (len - op) v1 v3 v7 dist fo'' CX' Hh) end.
      all: try (unfold cregs, f_const; fcx_cbn; kfin).
      all: replace (co + op + (len - op)) with (co + len) by lia; exact K.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fast_copy3_w _ M1 Rx lx Mx MD T (wn + wnext - op) co len v1 v3 v7 dist fo CX' Hh) end.
    all: try (unfold cregs, f_const; fcx_cbn; kfin). all: exact K.
Qed.

Lemma fast_win {RCa1 : RunCtx}  : forall cx M1 R l M MD T (co len dist v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  zget_l R l kS6 = f_ob cx + co -> zget_l R l kS11 = len -> zget_l R l kT1 = f_ob cx + f_bo cx ->
  3 <= len -> len <= 258 -> 0 <= co -> co + len <= f_osz cx -> f_bo cx <= co ->
  co - f_bo cx < dist -> 1 <= dist -> dist <= 32768 ->
  f_ro cx M1 -> f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  (forall R', cregs cx v1 v3 v7 dist R' [] -> zget_l R' [] kS6 = f_ob cx + co ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FTOOFAR (zupd R' []) M MD) T) ->
  KL cx M1 MD T v1 v3 v7 (co + len) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FWIN (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T co len dist v1 v3 v7 fo CX Hh HR Ls6 Ls11 Lt1 Hl1 Hl2 Hco1 Hco2 Hbo Hd0 Hd1 Hd2 HRO1 HL Rfo HAG KTF K.
  pose proof CX as CX'. pose proof HL as HL'. pose proof (f_ro_now _ M1 M CX HRO1 HAG) as HRO.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. open_ro HRO. unfold KL, cregs, cregs0, f_const, f_live, FPW, L_FWIN, L_FTOOFAR in K, KTF |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  clear Wu Wp Wob Hwin HOB Hin HtL HtD Q48 Q40 Q32 Q8 Q0.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  destruct (Z_lt_dec whave (dist - (co - bo))) as [Hfar|Hok].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KTF Rx) end.
    all: try (unfold cregs, f_const; fcx_cbn; kfin).
  - zbr Rfd true.
    clear Hsane Q16 Q24 KTF.
    destruct (Z.eq_dec wnext 0) as [Ew0|Nw0].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (fast_w0 _ M1 Rx lx Mx MD T co len dist (dist - (co - bo)) v1 v3 v7 fo CX' Hh) end.
      all: try (unfold cregs, f_const; fcx_cbn; kfin). all: try exact HRO1. all: exact K.
    + zbr Rfd false.
      destruct (Z_le_dec (dist - (co - bo)) wnext) as [Hc|Hw].
      * zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (fast_contig _ M1 Rx lx Mx MD T co len dist (dist - (co - bo)) v1 v3 v7 fo CX' Hh) end.
        all: try (unfold cregs, f_const; fcx_cbn; kfin). all: try exact HRO1. all: exact K.
      * zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (fast_wrap _ M1 Rx lx Mx MD T co len dist (dist - (co - bo)) v1 v3 v7 fo CX' Hh) end.
        all: try (unfold cregs, f_const; fcx_cbn; kfin). all: try exact HRO1. all: exact K.
Qed.
End T_Fast5W.

Module T_Fast6.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U.T_Fast2.T_Fast1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U.T_Fast2 T_Fast4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.



Lemma fast_dtail {RCa1 : RunCtx}  : forall cx M1 R l M MD T (co k m dist v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs0 cx v1 v3 v7 R l ->
  zget_l R l kT4 = f_ob cx + co - dist -> zget_l R l kS6 = f_ob cx + co -> zget_l R l kT0 = k -> zget_l R l kS11 = m ->
  0 <= m -> m <= 2 -> 1 <= dist -> dist <= co -> 0 <= k -> co + k + m <= f_osz cx ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 (co + k + m) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDTAIL (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T co k m dist v1 v3 v7 fo CX Hh HR Lt4 Ls6 Lt0 Ls11 Hm1 Hm2 Hd1 Hd2 Hk Hc2 HL Rfo HAG K.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy0 CX HR HL. unfold KL, cregs0, f_const, f_live, FPW, L_FDTAIL, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M1 [(ob, osz)] ltac:(ranges_ok_tac)) as HST.
  zrebase.
  zstep Rfd.
  destruct (Z.eq_dec m 0) as [E0|N0].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx fo) end; kfin.
  - zbr Rfd false.
    zstep Rfd.
    zbr Rfd false.
    zbr Rfd false.
    pose proof (Rfo (co - dist + k) ltac:(lia)) as Rb0.
    tld1 HOB (co - dist + k) Rfo.
    zstep Rfd.
    tstore_arr Rfd HOB (co + k).
    pose proof (zfupd_byte fo (co + k) (fo (co - dist + k)) 0 osz Rfo Rb0) as Rfo1.
    destruct (Z.eq_dec m 2) as [E2|N2].
    + zbr Rfd false.
      zstep Rfd.
      zbr Rfd false.
      zbr Rfd false.
      pose proof (Rfo1 (co - dist + k + 1) ltac:(lia)) as Rb1.
      tld1 HOB (co - dist + k + 1) Rfo1.
      zstep Rfd.
      tstore_arr Rfd HOB (co + k + 1).
      pose proof (zfupd_byte _ (co + k + 1) _ 0 osz Rfo1 Rb1) as Rfo2.
      zstep Rfd.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end; kfin.
    + zbr Rfd true.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end; kfin.
Qed.

Lemma fast_direct {RCa1 : RunCtx}  : forall cx M1 R l M MD T (co len dist v1 v3 v7 : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  cregs cx v1 v3 v7 dist R l ->
  zget_l R l kS6 = f_ob cx + co -> zget_l R l kS11 = len ->
  3 <= len -> len <= 258 -> 0 <= co -> co + len <= f_osz cx ->
  1 <= dist -> dist <= co ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KL cx M1 MD T v1 v3 v7 (co + len) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FDIRECT (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T co len dist v1 v3 v7 fo CX Hh HR Ls6 Ls11 Hl1 Hl2 Hco1 Hco2 Hd1 Hd2 HL Rfo HAG K.
  pose proof CX as CX'. pose proof HL as HL'.
  destruct cx as [u p q n ob osz w whave wnext wn lb db la na da nd spi bo cout0 W0 s8v vgp vtp zc rdL rdD fin fw].
  prep_copy CX HR HL. unfold KL, cregs0, f_const, f_live, FPW, L_FDIRECT, L_FLATCH in K |- *. fcx_cbn.
  clear Spq Slap Sdap TOKL TOKD Clb1 Clb2 Cdb1 Cdb2 Cs8 Rfin Calu Calp Call Cald.
  clear Wu Wp Wob Hwin HOB.
  zbr Rfd false.
  zstep Rfd. zbool.
  zstep Rfd.
  zstep Rfd.
  zsetreg 0 ltac:(symmetry; apply seqz_xor_neq; lia).
  zstep Rfd. zlit.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (fast_dloop (Z.to_nat len) _ M1 Rx lx Mx MD T co 0 len dist v1 v3 v7 fo CX' Hh) end.
  all: try (unfold cregs0, f_const; fcx_cbn; kfin).
  intros R' M' fo' k HR2 Lt4' Ls6' Lt0' Ls11' Hk1 Hk2 Hk3 HL2 Rfo' HAG'. fcx_cbn.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (fast_dtail _ M1 Rx lx Mx MD T co k (len - k) dist v1 v3 v7 fo' CX' Hh) end.
  all: try (unfold cregs0, f_const; fcx_cbn; kfin).
  all: replace (co + k + (len - k)) with (co + len) by lia; exact K.
Qed.
End T_Fast6.

Module T_Fast7.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U.T_Fast2.T_Fast1 T_Fast1E OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I9U.T_Fast2 T_Fast3 T_Fast4 T_Fast5 T_Fast5W T_Fast6.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.



Ltac xpre_tac :=
  unfold XPRE, fW; unfold fW in *; split_conj;
  first [ assumption | zreg | lia
        | match goal with H : f_const _ _ _ |- _ => let H' := fresh in pose proof H as H'; unfold f_const in H'; destr_conj H'; first [assumption | zreg] end ].

Lemma fast_body {RCa1 : RunCtx}  : forall cx M1 R l M MD T (ci co hold bits : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> zget_l R l kS1 = 14 ->
  zget_l R l kA4 = hold -> zget_l R l kA6 = f_q cx + ci -> zget_l R l kS6 = f_ob cx + co -> zget_l R l kA5 = bits ->
  0 <= ci -> ci + 6 <= f_n cx -> f_cout0 cx <= co -> co + 258 <= f_osz cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci ->
  0 <= hold -> hold < 2 ^ bits -> fW cx ci bits co <= f_W0 cx -> fW cx ci bits (f_cout0 cx) <= f_W0 cx ->
  f_ro cx M1 -> f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KEXIT cx M1 MD T ->
  KLATCH cx M1 MD T (fW cx ci bits co) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FHEAD (zupd R l) M MD) T.
Proof.
  intros cx M1 R l M MD T ci co hold bits fo CX Hh HC Ls1 La1 La3 La4 La7 Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hb3 Hh1 Hh2 HW HWI
         HRO1 HL Rfo HAG HEX HKL.
  pose proof (f_ro_now cx M1 M CX HRO1 HAG) as HRO.
  pose proof CX as CX'. unfold fcx_ok in CX'; cbv zeta in CX'; destr_conj CX'.
  pose proof HL as HL'. unfold f_live in HL'. dand HL' as (Wu & Wp & Wob & Hwin & HOB).
  unfold KLATCH, fW in HKL. unfold fW in HW, HWI.
  eapply (fast_head cx R l M MD T ci hold bits (f_ob cx + co) CX Hh HC Ls1 La1 La3 La4 La7 HRO); try lia.
  intros R1 ci1 hold1 bits1 HC1 Ma1 Ma3 Ma4 Ma7 Hc1a Hc1b Hc1c Hb1a Hb1b Hb1c Hh1a Hh1b HA1.
  eapply (fast_declen cx R1 [] M MD T hold1 bits1 (f_q cx + ci1) (f_ob cx + co) CX Hh HC1 Ma1 Ma3 Ma4 Ma7 HRO); try lia.
  -
    intros R2 k hold2 bits2 HC2 Na1 Na3 Na4 Na7 Nt2 Hk1 Hk2 Hb2a Hb2b Hb2c Hh2a Hh2b.
    eapply (fast_lit cx M1 R2 [] M MD T k co hold2 (f_q cx + ci1) bits2 fo CX Hh HC2 Na1 Na3 Na4 Na7 Nt2 Hk1 Hk2); try lia; try assumption.
    intros R3 M3 fo3 HC3 Oa1 Oa3 Oa4 Oa7 HL3 Rfo3 HAG3.
    eapply (HKL R3 M3 ci1 (co + 1) hold2 bits2 fo3); try assumption; try lia.
  -
    intros R2 k hold2 bits2 HC2 Na1 Na3 Na4 Na7 Nt2 Ns9 Hk1 Hk2 Hop1 Hop2 Hv1 Hv2 Hb2a Hb2b Hb2c Hh2a Hh2b.
    eapply (fast_lenb cx R2 [] M MD T k ci1 hold2 bits2 (f_ob cx + co) CX Hh HC2 Na1 Na3 Na4 Na7 Nt2 Ns9 Hk1 Hk2 Hop1 Hop2 Hv1 Hv2 HRO); try lia.
    intros R3 ci3 hold3 bits3 len HC3 Oa1 Oa3 Oa4 Oa7 Os10 Hl1 Hl2 Hc3a Hc3b Hc3c Hb3a Hb3b Hb3c Hh3a Hh3b HA3a HA3b.
    eapply (fast_decdist cx R3 [] M MD T hold3 bits3 (f_q cx + ci3) (f_ob cx + co) len CX Hh HC3 Oa1 Oa3 Oa4 Oa7 Os10 HRO); try lia.
    +
      intros R4 k' hold4 bits4 HC4 Pa1 Pa3 Pa4 Pa7 Ps10 Pt2 Ps11 Hk1' Hk2' Hop1' Hop2' Hv1' Hv2' Hb4a Hb4b Hb4c Hh4a Hh4b.
      eapply (fast_distb cx R4 [] M MD T k' ci3 co hold4 bits4 len CX Hh HC4 Pa1 Pa3 Pa4 Pa7 Ps10 Pt2 Ps11 Hk1' Hk2' Hop1' Hop2' Hv1' Hv2' HRO); try lia.
      *
        intros R5 ci5 hold5 bits5 dist HC5 Qa1 Qa3 Qa4 Qa7 Qs10 Qs11 Qt1 Hd1 Hd2 Hd3 Hc5a Hc5b Hc5c Hb5a Hb5b Hb5c Hh5a Hh5b HA5.
        eapply (fast_direct cx M1 R5 [] M MD T co len dist hold5 (f_q cx + ci5) bits5 fo CX Hh); try lia; try assumption.
        { unfold cregs. split_conj; assumption. }
        intros R6 M6 fo6 HR6 Sa4 HL6 Rfo6 HAG6. dand HR6 as (HC6 & Sa1 & Sa3 & Sa7).
        eapply (HKL R6 M6 ci5 (co + len) hold5 bits5 fo6); try assumption; try lia.
      *
        intros R5 ci5 hold5 bits5 dist HC5 Qa1 Qa3 Qa4 Qa7 Qs10 Qs11 Qt1 Hd1 Hd2 Hd3 Hc5a Hc5b Hc5c Hb5a Hb5b Hb5c Hh5a Hh5b HA5.
        eapply (fast_win cx M1 R5 [] M MD T co len dist hold5 (f_q cx + ci5) bits5 fo CX Hh); try lia; try assumption.
        { unfold cregs. split_conj; assumption. }
        {
          intros R6 HR6 Sa4. dand HR6 as (HC6 & Sa1 & Sa3 & Sa7 & Ss11).
          eapply (fast_toofar cx M1 MD T CX Hh HEX R6 [] M ci5 co hold5 bits5 fo). xpre_tac. }
        intros R6 M6 fo6 HR6 Sa4 HL6 Rfo6 HAG6. dand HR6 as (HC6 & Sa1 & Sa3 & Sa7).
        eapply (HKL R6 M6 ci5 (co + len) hold5 bits5 fo6); try assumption; try lia.
    +
      intros R4 hold4 bits4 HC4 Pa1 Pa3 Pa4 Pa7 Hb4a Hb4b Hb4c Hh4a Hh4b.
      eapply (fast_badd cx M1 MD T CX Hh HEX R4 [] M ci3 co hold4 bits4 fo). xpre_tac.
  -
    intros R2 op hold2 bits2 HC2 Na1 Na3 Na4 Na7 Ns9 Hop1 Hop2 Hb2a Hb2b Hb2c Hh2a Hh2b.
    eapply (fast_eob cx M1 MD T CX Hh HEX R2 [] M ci1 co hold2 bits2 fo op); [ xpre_tac | exact Ns9 | lia ].
Qed.

Lemma fast_loop {RCa1 : RunCtx}  : forall (N : nat) cx M1 R l M MD T (ci co hold bits : Z) (fo : Z -> Z),
  fcx_ok cx -> m_halted MD = None ->
  f_const cx R l -> zget_l R l kS1 = 14 ->
  zget_l R l kA4 = hold -> zget_l R l kA6 = f_q cx + ci -> zget_l R l kS6 = f_ob cx + co -> zget_l R l kA5 = bits ->
  0 <= ci -> ci + 6 <= f_n cx -> f_cout0 cx <= co -> co + 258 <= f_osz cx -> 0 <= bits -> bits <= 40 -> bits <= 8 * ci ->
  0 <= hold -> hold < 2 ^ bits -> fW cx ci bits co <= f_W0 cx -> fW cx ci bits (f_cout0 cx) <= f_W0 cx -> fW cx ci bits co < Z.of_nat N ->
  f_ro cx M1 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (f_p cx + 8) LEN ->
  f_live cx fo M -> (forall i, 0 <= i < f_osz cx -> 0 <= fo i < 256) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 X (FPW cx)) M ->
  KEXIT cx M1 MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_FHEAD (zupd R l) M MD) T.
Proof.
  induction N as [|N IH]; intros cx M1 R l M MD T ci co hold bits fo CX Hh HC Ls1 La1 La3 La4 La7 Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hb3
    Hh1 Hh2 HW HWI HWN HRO1 Hm8 HL Rfo HAG HEX; [unfold fW in HWN; lia|].
  eapply (fast_body cx M1 R l M MD T ci co hold bits fo CX Hh HC Ls1 La1 La3 La4 La7); try assumption.
  intros R' M' ci' co' hold' bits' fo' HC' Ka1 Ka3 Ka4 Ka7 Hci1' Hci2' Hco1' Hco2' Hb1' Hb2' Hb3' Hh1' Hh2' HB' HW0' HWI' HL' Rfo' HAG'.
  pose proof CX as CX'. unfold fcx_ok in CX'; cbv zeta in CX'; destr_conj CX'.
  pose proof HC' as HC''. unfold f_const in HC''. destr_conj HC''.
  unfold fW in *. unfold L_FLATCH, L_FHEAD in *. zkeys. zgetl0. pose proof two64_eq as TW64.
  assert (EXIT : forall RX lx, f_const cx RX lx -> zget_l RX lx 15 = hold' -> zget_l RX lx 17 = f_q cx + ci' ->
                 zget_l RX lx 23 = f_ob cx + co' -> zget_l RX lx 16 = bits' ->
                 realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 105176 (zupd RX lx) M' MD) T).
  { intros RX lx GC G15 G17 G23 G16. unfold f_const in GC. destr_conj GC.
    pose proof HL' as HL2. unfold f_live in HL2. dand HL2 as (Wu & Wp & Wob & Hwin & HOB).
    zderiveL HAG' Hm8 Hm8'.
    apply (framed_mpostL_weaken (run_segments R_segs rc_inp rc_sp rc_mb) M1 M' (FPW cx) (FP1 cx) ltac:(unfold FPW, FP1; ranges_within_tac)) in HAG'.
    unfold KEXIT, L_FEXIT in HEX. zkeys.
    eapply (HEX (zupd RX lx) M' ci' co' hold' bits' LEN fo'); try assumption; try lia; try zreg. unfold PFOLD. left. reflexivity. }
  zstep Rfd.
  destruct (Z_lt_dec (f_q cx + ci') (f_q cx + f_n cx + -5)) as [Hin|Hnin].
  - zbr Rfd false.
    destruct (Z_lt_dec (f_ob cx + co') (f_ob cx + f_osz cx + -257)) as [Hout|Hnout].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (IH cx M1 Rx lx Mx MD T ci' co' hold' bits' fo' CX Hh) end.
      all: try assumption. all: try zreg. all: try lia.
      all: try (unfold f_const; split_conj; zreg).
    + zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ => apply (EXIT Rx lx) end;
        try assumption; try zreg. all: unfold f_const; split_conj; zreg.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ => apply (EXIT Rx lx) end;
      try assumption; try zreg. all: unfold f_const; split_conj; zreg.
Qed.

Theorem ifast_t {RCa1 : RunCtx}  : ifast_spec_at (run_segments R_segs rc_inp rc_sp rc_mb) L_FENTRY 160.
Proof.
  unfold ifast_spec_at.
  intros Rb l M MD T u p q n ob osz w whave wnext cin cout hold bits out lb db la na da nd spi ret rhi zc rdL rdD fin fo fw.
  intros Hh La0 La1 Lsp Lra Hret1 Hret2.
  intros Cu1 Cu2 Cu3 Cu4 Cu5 Cu6 Cp1 Cp2 Cp3 Cq1 Cn1 Cn2 Cq2 Cob1 Cosz1 Cosz2 Cob2 Sobu Spob Spq Sobq Cw Swp Swq Swob
         Cla1 Cla2 Cda1 Cda2 Cla3 Cda3 Slaob Slap Sdaob Sdap Clb1 Clb2 Cdb1 Cdb2 TOKL TOKD
         Hci1 Hci2 Hci3 Hco1 Hco2 Hco3 Hb1 Hb2 Hh1 Hh2 Hb3 Hout1 Hout2 Hout3 Hwh1 Hwn1 Hw0 Hw1
         Wu Wp Wob Ww E8 E16 E32 E40 E64 P60 P64 P68 P72 P80 P88 P8 P104 P112 P120 P124 P7144 HtL HtD Hin Rfin HOB Rfo Hwin Rfw K.
  cbv [FRA STATE_SIZE WIN_SIZE] in Cu1, Cu4, Cp2, Cq2, Sobu, Spob, Spq, Cw, Swp, Swq, Swob, Cla2, Cda2, Hw1, Wu, Wp, Ww, P60, Hwin, Rfw.
  pose proof two64_eq as TW64.
  pose proof (tab_ok_root _ _ _ _ TOKL) as (_ & HnaL & _). pose proof (tab_ok_root _ _ _ _ TOKD) as (_ & HndD & _).
  pose proof (pow2_15 lb ltac:(lia)) as HPl. pose proof (pow2_15 db ltac:(lia)) as HPd.
  set (wn := if w =? 0 then 0 else 32768) in *.
  assert (Hwn : (w = 0 /\ wn = 0 /\ whave = 0 /\ wnext = 0) \/ (0 < w /\ w + 32768 <= zc /\ wn = 32768 /\ whave <= 32768 /\ wnext < 32768)).
  { idtac. subst wn. destruct (Z.eqb_spec w 0) as [E|NE].
    - left. destruct (Hw0 E). lia.
    - right. dand (Hw1 NE) as (A & B & _). destruct Cw as [|(C1 & C2 & C3)]; [lia|]. lia. }
  clear Hw0 Hw1. clearbody wn. idtac.
  set (cx := FCX u p q n ob osz w whave wnext wn lb db la na da nd spi (cout - (out - (osz - cout))) cout
                 (8 * (n - cin) + bits + (osz - cout)) (w + wnext) (zget_l Rb l kGP) (zget_l Rb l kTP) zc rdL rdD fin fw).
  clear Cw.
  assert (CX : fcx_ok cx).
  { unfold fcx_ok. subst cx. cbn [f_u f_p f_q f_n f_ob f_osz f_w f_whave f_wnext f_wn f_lb f_db f_la f_na f_da f_nd
                     f_spi f_bo f_cout0 f_W0 f_s8 f_gp f_tp f_zc f_rdL f_rdD f_fin f_fw]. idtac.
    split_conj.
    all: try assumption.
    all: try lia.
    - unfold ZSEP in Swp |- *. lia.
    - unfold ZSEP in Swq |- *. lia.
    - unfold ZSEP in Swob |- *. lia.
    - unfold ZSEP. right. reflexivity.
    - intros i Hi. apply Rfw. lia. }
  Local Ltac pj := cbn [f_u f_p f_q f_n f_ob f_osz f_w f_whave f_wnext f_wn f_lb f_db f_la f_na f_da f_nd
                        f_spi f_bo f_cout0 f_W0 f_s8 f_gp f_tp f_zc f_rdL f_rdD f_fin f_fw].
  eapply (fast_entry cx Rb l M MD T cin cout hold bits out ret fo CX Hh); try (subst cx; pj; first [assumption | reflexivity | lia]).
  -
    unfold f_emem. subst cx. pj.
    split_conj; try assumption.
    destruct Hwn as [(Ew & Ewn & _) | (Cw1 & Cw2 & Ewn & _)].
    + rewrite Ew, Ewn. apply mem_arr_nil; [rewrite TW64; lia | lia].
    + rewrite Ewn. apply Hwin. lia.
  -
    intros R1 M1 HC1 Ms1 Ma1 Ma3 Ma4 Ma7 HL1 HRO1 HFR Hm8 PRO.
    eapply (fast_loop (S (Z.to_nat (8 * (n - cin) + bits + (osz - cout)))) cx M1 R1 [] M1 MD T cin cout hold bits fo CX Hh HC1 Ms1 Ma1 Ma3 Ma4 Ma7);
      try (subst cx; pj; first [assumption | lia]).
    + subst cx. unfold fW. pj. lia.
    + subst cx. unfold fW. pj. lia.
    + subst cx. unfold fW. pj. rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
    + apply mpostL_refl.
    + eapply (fast_exit cx Rb l M M1 MD T ret CX Hh Hret1 Hret2); try (subst cx; pj; first [assumption | reflexivity]).
      all: unfold KRET; subst cx; pj; intros R' M' cin' cout' hold' bits' mode' fo'; intros;
           eapply (K R' M' cin' cout' hold' bits' mode' fo'); try eassumption; lia.
Qed.
End T_Fast7.

