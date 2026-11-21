(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S Require SBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S Require S_MatchL.

Module S_Match.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.S_MatchL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Definition L_M4C : Z := 93136.
Definition L_M54 : Z := 93144.
Definition L_M30 : Z := 93108.
Definition L_M3C : Z := 93120.

Definition m_regs (u p q n ob osz : Z) (K0 : positive -> Z) (cin cout hold bits out dput : Z) (R : tree Z) : Prop :=
  zget R kSP = u + -224 /\ zget R kGP = K0 kGP /\ zget R kTP = K0 kTP /\ zget R kS0 = p /\
  zget R kA0 = u /\ zget R kA1 = 0 /\ zget R kS6 = p + 168 /\ zget R kT6 = -16180 /\ zget R kT4 = 30 /\
  zget R kS9 = JTAB_ADDR /\ zget R kS4 = 16209 /\ zget R kS2 = n - cin /\ zget R kRA = osz - cout /\
  zget R kS7 = hold /\ zget R kS8 = bits /\ zget R kS11 = q + cin /\
  zget R kS3 = ob + cout + dput.
End FXG.
Ltac open_mregs H := unfold m_regs in H; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS8 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kRA kS3 kS5 kS4 kS7 kS7 kS2 kS0 kS11 kS10 kT3 kT4 kS9 kT6 JTAB_ADDR] in H; destr_conj H.
Ltac close_mregs := unfold m_regs; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS8 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kRA kS3 kS5 kS4 kS7 kS7 kS2 kS0 kS11 kS10 kT3 kT4 kS9 kT6 JTAB_ADDR]; split_conj;
                   first [zreg | match goal with |- ?G => idtac "close_mregs FAIL" G; fail end].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Theorem match_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = MATCH -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_MATCH (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  assert (PR3' : out = osz - cout0) by (destruct PR3 as [E | [_ C]]; [exact E | exfalso; clear - C; cbv [CHECK MATCH] in C; lia]).
  clear PR3. rename PR3' into PR3.
  assert (HMA : 1 <= length /\ length < 65536 /\ offset < 98304)
    by (clear - MODE_; unfold MODE in MODE_; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
        match goal with H : MATCH = MATCH -> _ |- _ => exact (H eq_refl) end).
  dand HMA as (HL1 & HL16 & HO17). clear MODE_.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  zkeysb. unfold L_MATCH, L_M4C, L_M54, L_M30, L_M3C, L_MLOOP, L_MAFTER, L_SETLEN in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  open_K K. clear KD KD00 KRA1 KRL KB11 KBA3 KL KRT.
  destruct (Z.eq_dec (osz - cout) 0) as [Hleft0 | Hleft].
  { zbr Rfd true.
    unfold KLEAVE_LD, L_LEAVE_LD in KLL. zkeys.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KLL Rx Mx _ lf cf SI0) end.
    - unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SRET.
    - exact SOUT.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  zbr Rfd false. clear KLL.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn.
  dand SR0 as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
  pose proof CST as CS. unfold i_cst in CS. icx_cbn. dand CS as (_ & _ & _ & _ & _ & _ & C60 & C72 & C7144).
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S72 & _).
  pose proof SOUT as S80. unfold s_out in S80. icx_cbn.
  unfold WIN in WIN_. icx_cbn. cbv [WIN_SIZE] in WIN_. destruct WIN_ as [WIN0 WIN1].
  assert (Hwh32 : whave <= 32768 /\ wnext <= 32768) by (destruct (Z.eq_dec w 0) as [E|E]; [destruct (WIN0 E) | destruct (WIN1 E)]; lia).
  assert (JA : forall R' M' (copy : Z),
    m_regs u p q n ob osz K0 cin cout hold bits out copy R' -> zget R' kA2 = copy ->
    1 <= copy -> copy <= length -> copy <= osz - cout ->
    PM (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0 MATCH
       (st_upd (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
               MATCH copy (length - copy)) lf cf M' ->
    realizes R_segs (zcfg R_segs 93196 (zupd R' []) M' MD) T).
  { intros R' M' copy MR G13 Hc1 Hc2 Hc3 HPM. open_mregs MR. cbv [kA2] in G13.
    dand HPM as (STD' & Hm' & SR' & RET' & OUT' & HL' & HC' & HP0'). unfold st_upd in SR', RET', OUT'. icx_cbn.
    pose proof SR' as SR2. unfold st_rest in SR2. icx_cbn. dand SR2 as (_ & _ & _ & _ & C92' & _).
    tstep1 Rfd.
    clear C92'.
    tstep1 Rfd.
    unfold KSETMODE, L_SETMODE in KSM. unfold KDISP10, L_DISP10 in KD10. zkeys.
    destruct (Z.eq_dec (length - copy) 0) as [E0 | N0].
    + zbr Rfd true.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_upd _ _ lf cf LEN copy (length - copy) SI0 ltac:(left; reflexivity) Hc1 Hc3 ltac:(lia) ltac:(cbn [t_length]; lia) ltac:(right; reflexivity)) as [SI1 ME1].
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KSM Rx Mx _ MATCH lf cf SI1 ME1) end.
      * unfold s_regs_d0, s_fix, s_vars, st_upd; icx_cbn; zkeys; cbv [JTAB_ADDR LEN]; split_conj; zreg.
      * exact STD'.
      * exact Hm'.
      * exact SR'.
      * exact RET'.
      * exact OUT'.
      * exact HL'.
      * exact HC'.
      * exact HP0'.
    + zbr Rfd false.
      zstep Rfd.
      pose proof (sinv_upd _ _ lf cf MATCH copy (length - copy) SI0 ltac:(left; reflexivity) Hc1 Hc3 ltac:(lia) ltac:(cbn [t_length]; lia)
                    ltac:(left; split; [reflexivity | split; [reflexivity | lia]])) as [SI1 ME1].
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KD10 Rx Mx _ lf cf SI1 ME1) end.
      * unfold s_regs_d10, s_fix, s_vars, st_upd; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
      * unfold k_mem, st_at; icx_cbn. split_conj; try assumption. }
  assert (J54 : forall R2 (copy : Z) (src : Z + Z),
    m_regs u p q n ob osz K0 cin cout hold bits out 0 R2 ->
    zget R2 kA2 = copy -> zget R2 kA4 = length ->
    1 <= copy -> copy <= length -> copy <= osz - cout ->
    match src with
    | inl so => zget R2 kA3 = ob + so /\ 0 <= so /\ so <= cout
    | inr si => zget R2 kA3 = w + si /\ 0 <= si /\ si + copy <= 32768 /\ w <> 0
    end ->
    realizes R_segs (zcfg R_segs 93144 (zupd R2 []) M MD) T).
  { intros R2 copy src MR Q13 Q15 Hk1 Hk2 Hk3 HSRC. open_mregs MR. cbv [kA2 kA4 kA3] in Q13, Q15, HSRC.
    clear C60 C72 C7144 S72 S80.
    assert (Q14 : exists from, zget R2 14 = from) by (eexists; reflexivity). destruct Q14 as [from Q14].
    assert (HS2 : match src with inl so => from = ob + so /\ 0 <= so /\ so <= cout
                                | inr si => from = w + si /\ 0 <= si /\ si + copy <= 32768 /\ w <> 0 end)
      by (destruct src; rewrite <- Q14; exact HSRC).
    clear HSRC.
    tstep1 Rfd.
    clear C92 SREST.
    tstep1 Rfd.
    destruct (out_arr _ ob osz Wob ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fo & HOB & Rfo).
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
    assert (HPM : PM (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0 MATCH
                     (st_upd (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                             MATCH copy (length - copy)) lf cf Mc)
      by (unfold PM, st_upd, s_ret, s_out, st_rest; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std; exact HAG) end.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zext32.
    zstep Rfd.
    zstep Rfd.
    destruct src as [so | si].
    - dand HS2 as (Hfrom & Hso1 & Hso2). subst from.
      lazymatch type of HPM with ?Pm _ => lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (mloop_o (Z.to_nat copy) Pm Rx lx Mx MD T ob osz so cout copy fo Hh) end end.
      all: try zreg. all: try lia. all: try assumption.
      { intros MX a v HX Ha1 Ha2. exact (PM_store _ fin M0 MATCH _ lf cf MX a v CX0 HX Ha1 Ha2). }
      intros R9 M9 fo9 E14 E20 E3 E4 E5 E26 E11 E12 E2 E32 E30 E31 E22 E25 E19 E24 E9 E27 E13 Wob9 HOB9 Rfo9 HPM9.
      zimps.
      eapply (JA R9 M9 copy); try exact HPM9; try lia; [close_mregs | zreg].
    - dand HS2 as (Hfrom & Hsi1 & Hsi2 & Hw0). subst from.
      pose proof Ww as Ww32. rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw0) in Ww32. cbv [WIN_SIZE] in Ww32.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        destruct (out_arr Mx w 32768 Ww32 ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fw & HWA & Rfw) end.
      pose proof (sep_w_ob ROMHI_S _ SEP) as SWO. icx_cbn. cbv [WIN_SIZE] in SWO.
      assert (SWO' : ZSEP (w + 32768 <= ob \/ ob + osz <= w)) by (unfold ZSEP; clear - SWO Hw0; lia). clear SWO.
      lazymatch type of HPM with ?Pm _ => lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (mloop_w (Z.to_nat copy) Pm Rx lx Mx MD T ob osz w 32768 si cout copy fo fw Hh) end end.
      all: try zreg. all: try lia. all: try assumption.
      { intros MX a v HX Ha1 Ha2. exact (PM_store _ fin M0 MATCH _ lf cf MX a v CX0 HX Ha1 Ha2). }
      intros R9 M9 fo9 E14 E20 E3 E4 E5 E26 E11 E12 E2 E32 E30 E31 E22 E25 E19 E24 E9 E27 E13 Wob9 HOB9 Rfo9 Hwin9 HPM9.
      zimps.
      eapply (JA R9 M9 copy); try exact HPM9; try lia; [close_mregs | zreg]. }
  assert (J4C : forall R' (copy0 : Z) (src : Z + Z),
    m_regs u p q n ob osz K0 cin cout hold bits out 0 R' ->
    zget R' kA2 = copy0 -> zget R' kA4 = length ->
    1 <= copy0 -> copy0 <= length ->
    match src with
    | inl so => zget R' kA3 = ob + so /\ 0 <= so /\ so <= cout
    | inr si => zget R' kA3 = w + si /\ 0 <= si /\ si + copy0 <= 32768 /\ w <> 0
    end ->
    realizes R_segs (zcfg R_segs 93136 (zupd R' []) M MD) T).
  { intros R' copy0 src MR G13 G15 Hc1 Hc2 HSRC. open_mregs MR. cbv [kA2 kA4 kA3] in G13, G15, HSRC.
    assert (Q14 : exists from, zget R' 14 = from) by (eexists; reflexivity). destruct Q14 as [from Q14].
    assert (HS2 : forall copy, copy <= copy0 -> match src with inl so => zget R' 14 = ob + so /\ 0 <= so /\ so <= cout
                                | inr si => zget R' 14 = w + si /\ 0 <= si /\ si + copy <= 32768 /\ w <> 0 end)
      by (intros copy Hcp; destruct src; [exact HSRC | dand HSRC as (X1 & X2 & X3 & X4); repeat split; try assumption; lia]).
    assert (G14 : zget R' 14 = from) by exact Q14.
    clear HSRC Q14.
    zstep Rfd || idtac.
    destruct (Z_lt_dec copy0 (osz - cout)) as [Hlt | Hge].
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J54 Rx copy0 src) end; try zreg; try lia; try close_mregs.
      cbv [kA3]. pose proof (HS2 copy0 ltac:(lia)) as X. destruct src;
        lazymatch goal with |- ?a = _ /\ ?rest => replace a with from by (symmetry; zreg); rewrite <- G14; exact X end.
    - zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J54 Rx (osz - cout) src) end; try zreg; try lia; try close_mregs.
      cbv [kA3]. pose proof (HS2 (osz - cout) ltac:(lia)) as X. destruct src;
        lazymatch goal with |- ?a = _ /\ ?rest => replace a with from by (symmetry; zreg); rewrite <- G14; exact X end. }
  clear J54.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zsetreg (cout - cout0) ltac:(rewrite ?swrap32_small by lia; lia).
  tstep1 Rfd.
  destruct (Z_lt_dec (cout - cout0) offset) as [Hwin | Hout].
  2: {
    zbr Rfd true.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J4C Rx length (inl (cout - offset))) end; try zreg; try lia; try close_mregs.
    all: cbv [kA3]; split; [zreg | lia]. }
  zbr Rfd false.
  tstep1 Rfd.
  tstep1 Rfd.
  destruct (Z_lt_dec whave (offset - (cout - cout0))) as [Hfar | Hok].
  {
    zbr Rfd false.
    zstep Rfd.
    tstep1 Rfd.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    unfold KBADMSG_S10, L_BADMSG_S10 in KB10.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KB10 Rx Mx (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf) end.
    - apply sinv_bad_of. exact SI0.
    - pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
      cbn [t_mode] in MB. change (rank MATCH) with 14 in MB. clear - MB. lia.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - cbv [kA2]. lazymatch goal with |- 0 <= ?x < _ => replace x with 66236 by (symmetry; zreg) end. rewrite TW64. lia.
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std; try exact HAG. }
  zbr Rfd true.
  assert (Hw0 : w <> 0) by (intros E; destruct (WIN0 E); lia).
  dand (WIN1 Hw0) as (Wh1 & Wn1 & Whn). clear WIN0 WIN1.
  rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw0) in C60. cbv [WIN_SIZE] in C60.
  assert (J3C : forall R' (copy0 si : Z),
    m_regs u p q n ob osz K0 cin cout hold bits out 0 R' ->
    zget R' kA2 = copy0 -> zget R' kA3 = si -> zget R' kA4 = length ->
    1 <= copy0 -> copy0 <= length -> 0 <= si -> si + copy0 <= 32768 ->
    realizes R_segs (zcfg R_segs 93120 (zupd R' []) M MD) T).
  { intros R' copy0 si MR G13 G14 G15 Hc1 Hc2 Hsi1 Hsi2. open_mregs MR. cbv [kA2 kA3 kA4] in G13, G14, G15.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zext32.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J4C Rx copy0 (inr si)) end; try zreg; try lia; try close_mregs.
    all: cbv [kA3]; split; [zreg | lia]. }
  assert (J30 : forall R' (cp si : Z),
    m_regs u p q n ob osz K0 cin cout hold bits out 0 R' ->
    zget R' kA2 = cp -> zget R' kA3 = si ->
    1 <= cp -> cp < 98304 -> 0 <= si -> si + cp <= 32768 ->
    realizes R_segs (zcfg R_segs 93108 (zupd R' []) M MD) T).
  { intros R' cp si MR G13 G14 Hc1 Hc98 Hsi1 Hsi2. open_mregs MR. cbv [kA2 kA3] in G13, G14.
    tstep1 Rfd.
    destruct (Z_lt_dec cp length) as [Hlt | Hge].
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J3C Rx cp si) end; try zreg; try lia; close_mregs.
    - zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J3C Rx length si) end; try zreg; try lia; close_mregs. }
  clear J3C J4C.
  tstep1 Rfd.
  destruct (Z_lt_dec wnext (offset - (cout - cout0))) as [Hwrap | Hlin].
  - zbr Rfd false.
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J30 Rx (offset - (cout - cout0) - wnext) (32768 - (offset - (cout - cout0) - wnext))) end; try zreg; try lia; close_mregs.
  - zbr Rfd true.
    tstep1 Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J30 Rx (offset - (cout - cout0)) (wnext - (offset - (cout - cout0)))) end; try zreg; try lia; close_mregs.
Qed.

Theorem lit_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LIT -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_LIT (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_ MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  zkeysb. unfold L_LIT, L_SETLEN in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  open_K K. clear KD KD10 KD00 KRA1 KRL KB11 KB10 KBA3 KL KRT.
  destruct (Z.eq_dec (osz - cout) 0) as [Hleft0 | Hleft].
  { zbr Rfd false.
    zstep Rfd.
    unfold KLEAVE_LD, L_LEAVE_LD in KLL. zkeys.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KLL Rx Mx _ lf cf SI0) end.
    - unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SRET.
    - exact SOUT.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  zbr Rfd true.
  clear KLL.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn.
  dand SR0 as (_ & _ & _ & _ & C92 & _).
  pose proof (mem_u32_u8 _ _ _ C92) as B92.
  destruct (out_arr _ ob osz Wob ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fo & HOB & Rfo).
  zstep Rfd.
  clear B92 C92.
  tstep1 Rfd.
  tstore_arr Rfd HOB (cout).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  unfold KSETMODE, L_SETMODE in KSM. zkeys.
  pose proof (sinv_upd _ _ lf cf LEN 1 length SI0 ltac:(right; reflexivity) ltac:(lia) ltac:(cbn [c_osz t_cout]; lia) ltac:(lia) ltac:(cbn [t_length]; lia) ltac:(right; reflexivity)) as [SI1 ME1].
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KSM Rx Mx _ LIT lf cf SI1 ME1) end.
  - unfold s_regs_d0, s_fix, s_vars, st_upd; icx_cbn; zkeys; cbv [JTAB_ADDR LEN]; split_conj; zreg.
  - close_std.
  - exact Hmode.
  - unfold st_upd; icx_cbn. exact SREST.
  - exact SRET.
  - exact SOUT.
  - exact Hlens.
  - exact Hcodes.
  - exact HAG.
Qed.

Theorem arm_MATCH : arm_stmt L_MATCH MATCH.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply match_s; try eassumption.
Qed.

Theorem arm_LIT : arm_stmt L_LIT LIT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply lit_s; try eassumption.
Qed.
End FXG.
End S_Match.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S Require S_DistL.

Module S_DistX.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.S_MatchL S_Match OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.S_DistL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Definition L_DX20 : Z := 92832.
Definition L_DXBC : Z := 92988.

Definition x_regs (u p q n ob osz : Z) (K0 : positive -> Z) (cin cout bits out : Z) (R : tree Z) : Prop :=
  zget R kSP = u + -224 /\ zget R kGP = K0 kGP /\ zget R kTP = K0 kTP /\ zget R kS0 = p /\
  zget R kA0 = u /\ zget R kA1 = 0 /\ zget R kS6 = p + 168 /\ zget R kT6 = -16180 /\ zget R kT4 = 30 /\
  zget R kS9 = JTAB_ADDR /\ zget R kS4 = 16209 /\ zget R kS3 = ob + cout /\ zget R kRA = osz - cout /\
  zget R kS2 = n - cin /\ zget R kS8 = bits /\ zget R kS11 = q + cin.
End FXG.
Ltac open_xregs H := unfold x_regs in H; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6 JTAB_ADDR] in H; destr_conj H.
Ltac close_xregs := unfold x_regs; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6 JTAB_ADDR]; split_conj; zreg.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Theorem distext_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DISTEXT -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> zget_l Rb l kA3 = t_extra st -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_DX20 (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG La3 KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  assert (HDE : extra <= 15 /\ 1 <= length /\ length < 65536 /\ offset < 65536)
    by (clear - MODE_; unfold MODE in MODE_; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
        match goal with H : DISTEXT = DISTEXT -> _ |- _ => exact (H eq_refl) end).
  dand HDE as (HX15 & HL1 & HL16 & HO16). clear MODE_.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  zkeysb. unfold L_DX20, L_DXBC in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KD10 KD00 KSM KRA1 KRL KB11 KB10 KBA3 KLL KRT.
  prune_rng.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S72 & _).
  destruct (mem_wr_u32_exists_R M (p + 7164) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (vb & Hback & Rvb).
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  assert (JBC : forall R' M' (ci H B off : Z),
    x_regs u p q n ob osz K0 ci cout B out R' -> zget R' kS7 = H ->
    cin <= ci -> ci <= n -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
    8 * (n - ci) + B <= 8 * (n - cin) + bits -> 0 <= off -> off < 98304 ->
    s_std (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M' ->
    mem_u32 R_segs M' (p + 8) DISTEXT ->
    st_rest R_segs (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST DISTEXT last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_ret (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST DISTEXT last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_out (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST DISTEXT last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    mem_arr 2 R_segs M' (p + 168) 320 lf -> mem_arr 4 R_segs M' (p + 1384) 1444 cf ->
    framed (fun X => mpostL R_segs M0 X [(u - 1024, 1024); (u, 112); (p, 7176); (ob, osz)]) M' ->
    realizes R_segs (zcfg R_segs 92988 (zupd R' []) M' MD) T).
  { intros R' M' ci H B off XR G24 Hc1 Hc2 HB1 HB2 HH1 HH2 HBc HWm Ho1 Ho2 STD' Hm' SR' RET' OUT' HL' HC' HAG'.
    open_xregs XR. cbv [kS7] in G24.
    clear S72 Hback ROM Wstk Wp Wob Ww FRM CST HK Hin Hmode SREST SRET SOUT Hlens Hcodes HAG.
    pose proof STD' as STD2. open_std STD2. icx_cbn. zkeys.
    zstep Rfd.
    clear Hm'.
    tstep1 Rfd.
    pose proof (sinv_pull _ _ lf cf ci H B SI0 ltac:(cbn; lia) ltac:(cbn; lia) HB1 HB2 HH1 HH2 HBc ltac:(cbn; lia)) as [SI1 ME1].
    pose proof (sinv_to_match _ _ lf cf off SI1 eq_refl Ho1 Ho2) as [SI2 ME2].
    unfold st_pull, st_dx in SI2, ME2, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI2, ME2, ME1.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (match_s _ fin MD T M0 Rx lx Mx
                (IST MATCH last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI2) end.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
      all: cbv [MATCH]; assumption.
    - eapply KALL_mono; [| exact K]. clear - ME1 ME2. cbn [t_mode] in *. lia. }
  assert (J80 : forall R' (ci H B : Z),
    x_regs u p q n ob osz K0 cin cout bits out R' ->
    zget R' kA5 = q + ci -> zget R' kA2 = n - ci -> zget R' kA4 = B -> zget R' kS7 = H -> zget R' kA3 = extra ->
    cin <= ci -> ci <= n -> extra <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci -> B = bits + 8 * (ci - cin) ->
    realizes R_segs (zcfg R_segs 92928 (zupd R' []) M MD) T).
  { intros R' ci H B XR G16 G13 G15 G24 G14 Hc1 Hc2 HxB HB40 HH1 HH2 HBc HB.
    open_xregs XR. cbv [kA5 kA2 kA4 kS7 kA3] in G16, G13, G15, G24, G14. clear KL.
    repeat match goal with H : forall i : Z, _ |- _ => clear H end.
    pose proof SREST as C96. unfold st_rest in C96. icx_cbn. dand C96 as (_ & _ & _ & _ & _ & C96 & _).
    pose proof (pow2_15 extra ltac:(lia)) as HPx.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    tstep1 Rfd.
    clear C96.
    zstep Rfd.
    zstep Rfd.
    clear S72 Hback.
    zstep Rfd.
    zstep Rfd.
    zsetreg (2 ^ extra - 1) ltac:(symmetry; apply mask_not_sllw; lia).
    zstep Rfd.
    pose proof (land_mask_r H extra ltac:(lia)) as Rbx.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zsetreg (H / 2 ^ extra) ltac:(symmetry; apply (srl_hold H B); lia).
    pose proof (hold_shr_bound H B extra ltac:(lia) ltac:(lia)) as HH'.
    zstep Rfd.
    st_prestore_k st_rest_set96 17%positive SREST.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (JBC Rx Mx ci (H / 2 ^ extra) (B - extra) (offset + Z.land H (2 ^ extra - 1))) end;
      try zreg; try lia; try assumption.
    - close_xregs.
    - close_std. }
  destruct (Z.eq_dec extra 0) as [Hx0 | Hx1].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (JBC Rx Mx cin hold bits offset) end;
      try zreg; try lia; try assumption.
    - close_xregs.
    - close_std. }
  zbr Rfd false.
  destruct (Z_lt_dec bits extra) as [Hneed | Hhave].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (x_loop (S (Z.to_nat (n - cin))) 92852 92928 Rx lx Mx MD T q n extra cin bits cin bits hold fin) end;
      try zreg; try lia; try eassumption.
    + right. split; reflexivity.
    +
      intros R' H' G24 HH1 HH2 HB14 HBn KP. cbv [keptc KS_X] in KP. cbv [kS7] in G24. destr_conj KP. zimps.
      eapply (stub_L1 93564 R' [] M MD T q n cin bits u ret); [right; reflexivity | exact Hh | zreg | zreg | zreg | zreg | lia | lia | exact SRET |].
      intros R9 E9 E27 E25 E10 HK9. cbv [keptc KS_L1] in HK9. cbv [kS8 kS11 kS2 kS1] in E9, E27, E25, E10. destr_conj HK9. zimps.
      pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
      unfold st_pull in SI1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
        t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1.
      unfold KLEAVE, L_LEAVE in KL.
      eapply (KL R9 M _ ret lf cf SI1).
      * unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
      * close_std.
      * split; [exact Hmode | exact SREST].
      * exact SOUT.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' ci' B' H' G16 G13 G15 G24 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_X] in KP. cbv [kA5 kA2 kA4 kS7] in G16, G13, G15, G24.
      destr_conj KP. zimps.
      eapply (J80 R' ci' H' B'); try assumption; try lia. close_xregs.
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J80 Rx cin hold bits) end; try zreg; try lia.
    close_xregs.
Qed.

Theorem arm_DISTEXT : arm_stmt L_DISTEXT DISTEXT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof KM as KM0. open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof SREST as SR0. unfold st_rest in SR0. dand SR0 as (_ & _ & _ & _ & _ & _ & C100 & _).
  dand RG as (FIX & VARS & G27). pose proof FIX as FIX0. unfold s_fix in FIX. destr_conj FIX.
  zkeysb. unfold L_DISTEXT in *.
  zstep Rfd.
  zstep Rfd.
  pose proof SI as SI'. dand SI' as (R & _ & _ & Mo).
  assert (HX : 0 <= t_extra st <= 15).
  { dand Mo as (_ & _ & _ & _ & _ & _ & _ & Mde & _). destruct (Mde Hmd) as [A _].
    unfold RNG in R. destr_conj R. split; [assumption | exact A]. }
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
    eapply (distext_s cx fin MD T M0 Rx lx M st lf cf CX Hh Hfin Hmd SI) end.
  - split; [exact FIX0 | split; [exact VARS | zreg]].
  - cbv [zget_l alookup Pos.eqb]. rewrite swrap32_small by lia. reflexivity.
  - exact KM0.
  - exact K.
Qed.
End FXG.
End S_DistX.

Module S_Dist.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.S_MatchL S_Match OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.S_DistL S_DistX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Definition L_D8EC : Z := 92780.
Definition L_DBAD : Z := 92892.

Definition d_regs (u p ob osz : Z) (K0 : positive -> Z) (cout out : Z) (R : tree Z) : Prop :=
  zget R kSP = u + -224 /\ zget R kGP = K0 kGP /\ zget R kTP = K0 kTP /\ zget R kS0 = p /\
  zget R kA0 = u /\ zget R kA1 = 0 /\ zget R kS6 = p + 168 /\ zget R kS4 = 16209 /\
  zget R kS3 = ob + cout /\ zget R kRA = osz - cout /\ zget R kS9 = 67008.
End FXG.
Ltac open_dregs H := unfold d_regs in H; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6] in H; destr_conj H.
Ltac close_dregs := unfold d_regs; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6]; split_conj; zreg.
Ltac mode_getr Mo := clear - Mo; unfold MODE in Mo; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
  first [ assumption | match goal with H : ?x = ?x -> _ |- _ => exact (H eq_refl) end ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
End FXG.
Ltac jfin :=
  lazymatch goal with
  | |- zget _ _ = _ => zreg
  | |- zget_l _ _ _ = _ => zreg
  | |- d_regs _ _ _ _ _ _ _ _ => close_dregs
  | |- keptc _ _ _ _ => keptc_close
  | |- realizes _ _ _ => idtac
  | |- forall _, _ => try assumption
  | |- _ \/ _ => assumption
  | |- mem_arr _ _ _ _ _ _ => assumption
  | |- tab_ok _ _ _ _ = true => assumption
  | |- m_halted _ = _ => assumption
  | |- _ => first [assumption | lia]
  end.
Ltac kcbv_in H := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6] in H.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Lemma land_mask_l' : forall x k, 0 <= k -> 0 <= Z.land (2 ^ k + -1) x < 2 ^ k.
Proof. intros x k Hk. replace (2 ^ k + -1) with (2 ^ k - 1) by lia. apply land_mask_l. exact Hk. Qed.

Theorem dist_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DIST -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_DIST (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  pose proof KM as KM0. open_kmem KM. open_std STD.
  assert (TLV : tables_live cx st cf).
  { assert (ML : codes_liveP (t_mode st) -> tables_live cx st cf) by mode_get MODE_.
    apply ML. rewrite Hmd. unfold codes_liveP. cbv [LEN_ DIST LIT]. lia. }
  dand (live_tabs cx st lf cf M CX RNG_ TLV ROM Hcodes) as (na & nd & TB). clear TLV.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  assert (HDI : 1 <= length /\ length < 65536) by mode_getr MODE_. destruct HDI as [HL1 HL16]. clear MODE_.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold tabsP in TB. icx_cbn. idtac.
  dand TB as (HtL & HtD & TOKL & TOKD & Cla1 & Cla2 & Cda1 & Cda2 & Cna & Cnd & ALla & ALda & Slaob & Slap & Sdaob & Sdap & Slap2 & Sdap2 & _).
  clear HtL TOKL Cla1 Cla2 Cna ALla Slaob Slap Slap2.
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) dc) as da eqn:Eda.
  remember (rdc cf dc) as rdD eqn:ErdD. clear ErdD.
  prune_rng.
  zkeysb. unfold L_DIST, L_D8EC, L_DBAD, L_DLOOP1, L_D04, L_DLOOP2, L_D8BC, L_LVX_L1, L_LVX_L2 in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KD10 KD00 KSM KRA1 KRL KB11 KB10 KRT.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S104 & S96 & _ & S72 & _).
  destruct (mem_wr_u32_exists_R M (p + 7164) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (vb & Hback & Rvb).
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  pose proof (tab_ok_root _ _ _ _ TOKD) as (Hdb1 & Hnd1 & _).
  pose proof (pow2_15 db ltac:(lia)) as HPdb.
  assert (J8EC : forall R' (ci B H e ab : Z),
    d_regs u p ob osz K0 cout out R' -> zget R' kT6 = -16180 -> zget R' kT4 = 30 -> zget R' kS9 = 67008 ->
    zget R' kS2 = p + 7160 -> zget R' kT1 = code_op e -> zget R' kA6 = code_val e -> zget R' kA4 = code_bits e ->
    zget R' kA3 = B -> zget R' kS7 = H -> zget R' kA5 = ab -> zget R' kS10 = q + ci -> zget R' kA2 = n - ci ->
    1 <= code_bits e ->
    ((16 <= code_op e < 32 /\ 1 <= code_val e /\ code_val e + Z.shiftl 1 (code_op e - 16) - 1 <= 32768 /\ code_op e <= 29)
     \/ (Z.land (code_op e) 64 <> 0 /\ Z.land (code_op e) 16 = 0 /\ Z.land (code_op e) 32 = 0)) ->
    cin <= ci -> ci <= n -> code_bits e <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
    8 * (n - ci) + B <= 8 * (n - cin) + bits ->
    realizes R_segs (zcfg R_segs 92780 (zupd R' []) M MD) T).
  { intros R' ci B H e ab DR G32 G30 G31 G10 G7 G17 G15 G14 G24 G16 G28 G13 Hbe CLS Hc1 Hc2 HbB HB40 HH1 HH2 HBc HWm.
    open_dregs DR. kcbv_in G32; kcbv_in G30; kcbv_in G31; kcbv_in G10; kcbv_in G7; kcbv_in G17; kcbv_in G15;
    kcbv_in G14; kcbv_in G24; kcbv_in G16; kcbv_in G28; kcbv_in G13.
    clear S104 S96 S72 HtD KL KLL.
    pose proof (code_op_range e) as Rop. pose proof (code_val_range e) as Rval. pose proof (code_bits_range e) as Rbi.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    zsetreg (H / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold H B); lia).
    pose proof (hold_shr_bound H B (code_bits e) ltac:(lia) ltac:(lia)) as HH'.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    clear Hback.
    tstep1 Rfd.
    pose proof (sinv_pull _ _ lf cf ci (H / 2 ^ code_bits e) (B - code_bits e) SI0 ltac:(cbn; lia) ltac:(cbn; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 ME1].
    unfold st_pull in SI1, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1, ME1.
    destruct CLS as [(Hop16 & Hv1 & Hv32k & Hop29) | (H64 & H16 & H32)].
    2: {
      pose proof (land_range_r (code_op e) 64 ltac:(lia)) as R64.
      zbr Rfd true.
      zstep Rfd.
      zstep Rfd.
      unfold KBADMSG_A3, L_BADMSG_A3 in KBA3.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KBA3 Rx Mx (IST DIST last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret length offset extra
                              lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf) end.
      - apply sinv_bad_of. exact SI1.
      - pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                      (IST DIST last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret length offset extra
                           lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
        cbn [t_mode] in MB. change (rank DIST) with 16 in MB. clear - MB ME1. lia.
      - unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
      - zreg. - zreg. - zreg. - zreg. - zreg. - zreg.
      - cbv [kA3]. lazymatch goal with |- 0 <= ?x < _ => replace x with 66314 by (symmetry; zreg) end. rewrite TW64. lia.
      - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
        all: first [exact SREST | exact SRET | exact SOUT | exact HAG]. }
    pose proof (op_base_tests (code_op e) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
    zbr Rfd false.
    zstep Rfd.
    zsetreg (code_op e - 16) ltac:(lia).
    zstep Rfd.
    st_prestore st_rest_set96 (code_val e) SREST.
    tstep1 Rfd.
    st_prestore_k st_rest_set100 14%positive SREST.
    tstep1 Rfd.
    clear Hmode.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_to_distext _ _ lf cf (code_val e) (code_op e - 16) SI1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI2 ME2].
    unfold st_dx in SI2, ME2. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI2, ME2.
    unfold L_DX20 in *.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (distext_s _ fin MD T M0 Rx lx Mx
                (IST DISTEXT last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret length (code_val e) (code_op e - 16)
                     lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI2) end.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - zreg.
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
      all: first [cbv [DISTEXT]; assumption | exact SREST | exact SRET | exact SOUT | exact HAG].
    - eapply KALL_mono; [| exact K]. clear - ME1 ME2. cbn [t_mode] in *. lia. }
  assert (KX1 : forall R' (H' : Z),
    zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (bits + 8 * (n - cin)) -> bits + 8 * (n - cin) <= 14 -> bits + 8 * (n - cin) <= 8 * n ->
    d_regs u p ob osz K0 cout out R' -> zget R' kS2 = n - cin -> zget R' kS8 = bits -> zget R' kS11 = q + cin ->
    realizes R_segs (zcfg R_segs 93520 (zupd R' []) M MD) T).
  { intros R' H' G24 HH1 HH2 HB14 HBn DR G25 G9 G27. open_dregs DR. kcbv_in G24; kcbv_in G25; kcbv_in G9; kcbv_in G27.
    clear J8EC KBA3 KLL.
    eapply (stub_L1 93520 R' [] M MD T q n cin bits u ret); [left; reflexivity | exact Hh | zreg | zreg | zreg | zreg | lia | lia | exact SRET |].
    intros R9 E9 E27 E25 E10 KP. cbv [keptc KS_L1] in KP. kcbv_in E9; kcbv_in E27; kcbv_in E25; kcbv_in E10. destr_conj KP. zimps.
    pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
    unfold st_pull in SI1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1.
    unfold KLEAVE, L_LEAVE in KL.
    eapply (KL R9 M _ ret lf cf SI1).
    - unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SOUT.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  assert (J04 : forall R' (ci B H : Z),
    d_regs u p ob osz K0 cout out R' -> zget R' kT6 = -16180 -> zget R' kT4 = 30 -> zget R' kS9 = 67008 ->
    zget R' kS2 = n - cin -> zget R' kS8 = bits -> zget R' kS11 = q + cin -> zget R' kA5 = da -> zget R' kA7 = 2 ^ db + -1 ->
    zget R' kS10 = q + ci -> zget R' kA2 = n - ci -> zget R' kA3 = B -> zget R' kS7 = H ->
    zget R' kA6 = da + 4 * Z.land (2 ^ db + -1) H -> zget R' kA4 = code_bits (rdD (Z.land (2 ^ db + -1) H)) ->
    cin <= ci -> ci <= n -> B = bits + 8 * (ci - cin) -> code_bits (rdD (Z.land (2 ^ db + -1) H)) <= B -> B <= 40 ->
    0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
    realizes R_segs (zcfg R_segs 92552 (zupd R' []) M MD) T).
  { intros R' ci B H DR G32 G30 G31 G25 G9 G27 G16 G18 G28 G13 G14 G24 G17 G15 Hc1 Hc2 HB HbB HB40 HH1 HH2 HBc.
    open_dregs DR. kcbv_in G32; kcbv_in G30; kcbv_in G31; kcbv_in G25; kcbv_in G9; kcbv_in G27; kcbv_in G16; kcbv_in G18;
    kcbv_in G28; kcbv_in G13; kcbv_in G14; kcbv_in G24; kcbv_in G17; kcbv_in G15.
    clear KX1 KL.
    set (i := Z.land (2 ^ db + -1) H) in *.
    pose proof (land_mask_l' H db ltac:(lia)) as Ri. fold i in Ri.
    pose proof (tab_root_entry DISTS rdD db nd i TOKD Ri) as (Hbits & _ & _ & CASES).
    pose proof (code_op_range (rdD i)) as Rop. pose proof (code_val_range (rdD i)) as Rval.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    tld4_op HtD i.
    tld4_val HtD i.
    zstep Rfd.
    zstep Rfd.
    destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
    -
      apply term_ok_DISTS in TM as [Hb1 CLS].
      assert (Hop16 : 16 <= code_op (rdD i)).
      { destruct CLS as [(A & _) | (A64 & _ & _)]; [lia|].
        apply is_linkop_false in NL. pose proof (land_range_r (code_op (rdD i)) 64 ltac:(lia)).
        destruct (Z_lt_dec (code_op (rdD i)) 16); [|lia]. exfalso.
        assert (E : code_op (rdD i) = 0) by lia. rewrite E in A64. apply A64. reflexivity. }
      zbr Rfd true.
      zstep Rfd.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J8EC Rx ci B H (rdD i)) end.
      all: jfin.
    -
      rewrite L2 in G15.
      pose proof (op_link_tests (code_op (rdD i)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
      assert (HPm : 1 <= 2 ^ (db + code_op (rdD i)) <= 32768) by (apply pow2_15; lia).
      pose proof (pow2_15 (code_op (rdD i)) ltac:(lia)) as HPlo.
      zbr Rfd false.
      zstep Rfd.
      zsetreg (db + code_op (rdD i)) ltac:(lia).
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zsetreg (2 ^ (db + code_op (rdD i)) - 1) ltac:(symmetry; apply mask_not_sllw; lia).
      set (m2 := 2 ^ (db + code_op (rdD i)) - 1) in *.
      set (v := code_val (rdD i)) in *. set (lo := code_op (rdD i)) in *.
      assert (JR : forall Hx, 0 <= Z.land Hx m2 / 2 ^ db < 2 ^ lo).
      { intros Hx. pose proof (land_mask_r Hx (db + lo) ltac:(lia)) as A. fold m2 in A.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
      zstep Rfd.
      pose proof (land_mask_r H (db + lo) ltac:(lia)) as Rm. fold m2 in Rm.
      zstep Rfd.
      zsetreg (Z.land H m2 / 2 ^ db) ltac:(symmetry; apply srlw_small; lia).
      pose proof (JR H) as Rj.
      destruct (SUB _ Rj) as [NL2 TM2]. pose proof TM2 as TM2'. apply term_ok_DISTS in TM2 as [Hbits2 CLS2].
      zstep Rfd.
      zsetreg (v + Z.land H m2 / 2 ^ db) ltac:(lia).
      zstep Rfd.
      zstep Rfd.
      zsetreg (4 * (v + Z.land H m2 / 2 ^ db)) ltac:(symmetry; apply zext32_shift30; lia).
      zstep Rfd.
      tld4_bits HtD (v + Z.land H m2 / 2 ^ db).
      zstep Rfd.
      assert (J8BC : forall R2 (ci2 B2 H2 : Z),
        d_regs u p ob osz K0 cout out R2 -> zget R2 kS11 = q + cin ->
        zget R2 kA5 = da -> zget R2 kA4 = db -> zget R2 kA6 = v -> zget R2 kS2 = p + 7160 ->
        zget R2 kA2 = n - ci -> zget R2 kA3 = B -> zget R2 kS10 = q + ci ->
        zget R2 kT5 = q + ci2 -> zget R2 kA7 = n - ci2 -> zget R2 kT0 = B2 -> zget R2 kS7 = H2 ->
        zget R2 kT3 = da + 4 * (v + Z.land H2 m2 / 2 ^ db) -> zget R2 kT2 = code_bits (rdD (v + Z.land H2 m2 / 2 ^ db)) ->
        ci <= ci2 -> ci2 <= n -> B2 = bits + 8 * (ci2 - cin) -> db + code_bits (rdD (v + Z.land H2 m2 / 2 ^ db)) <= B2 -> B2 <= 40 ->
        0 <= H2 -> H2 < 2 ^ B2 -> B2 <= 8 * ci2 ->
        realizes R_segs (zcfg R_segs 92736 (zupd R2 []) M MD) T).
      { intros R2 ci2 B2 H2 DR2 Q27 Q16 Q15 Q17 Q10 Q13 Q14 Q28 Q31 Q18 Q6 Q24 Q29 Q8 Hd1 Hd2 HB2 HbB2 HB2' HH21 HH22 HBc2.
        open_dregs DR2. kcbv_in Q27; kcbv_in Q16; kcbv_in Q15; kcbv_in Q17; kcbv_in Q10;
        kcbv_in Q13; kcbv_in Q14; kcbv_in Q28; kcbv_in Q31; kcbv_in Q18; kcbv_in Q6; kcbv_in Q24; kcbv_in Q29; kcbv_in Q8.
        clear KLL.
        pose proof (JR H2) as Rj2.
        set (j2 := Z.land H2 m2 / 2 ^ db) in *.
        assert (HPB2 : 1 <= 2 ^ B2 <= 2 ^ 40) by (split; [pose proof (pow2_pos B2 ltac:(lia)); lia | apply pow2_le; lia]).
        pose proof (code_bits_range (rdD (v + j2))) as Rb2.
        zstep Rfd.
        tld4_op HtD (v + j2).
        tld4_val HtD (v + j2).
        zstep Rfd.
        zsetreg (H2 / 2 ^ db) ltac:(symmetry; apply (srl_hold H2 B2); lia).
        pose proof (hold_shr_bound H2 B2 db ltac:(lia) ltac:(lia)) as HH2'.
        tstep1 Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        destruct (SUB _ Rj2) as [NL3 TM3]. apply term_ok_DISTS in TM3 as [Hbits3 CLS3].
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
          eapply (J8EC Rx ci2 (B2 - db) (H2 / 2 ^ db) (rdD (v + j2))) end.
        all: jfin. }
      destruct (Z_lt_dec B (db + code_bits (rdD (v + Z.land H m2 / 2 ^ db)))) as [Hneed | Hok].
      + zbr Rfd false.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (d_loop2 (S (Z.to_nat (n - ci))) Rx lx Mx MD T q n da nd db lo v m2 ci B ci B H fin rdD Hh) end.
        all: jfin.
        *
          intros R5 H' Q24 HH1' HH2' HB29 HBn KP. cbv [keptc KS_D2] in KP. kcbv_in Q24. destr_conj KP. zimps.
          clear J8BC J8EC SUB JR.
          eapply (stub_L2 R5 [] M MD T q n ci B Hh); [zreg | zreg | zreg | lia | lia |].
          intros R9 E9 E27 E25 KP9. cbv [keptc KS_L2] in KP9. kcbv_in E9; kcbv_in E27; kcbv_in E25. destr_conj KP9. zimps.
          pose proof (sinv_pull _ _ lf cf n H' (B + 8 * (n - ci)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1' HH2' HBn ltac:(cbn; lia)) as [SI1 _].
          unfold st_pull in SI1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
            t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1.
          unfold KLEAVE_LD, L_LEAVE_LD in KLL. zkeys.
          eapply (KLL R9 M _ lf cf SI1).
          -- unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
          -- close_std.
          -- split; [exact Hmode | exact SREST].
          -- exact SRET.
          -- exact SOUT.
          -- exact Hlens.
          -- exact Hcodes.
          -- exact HAG.
        *
          intros R5 ci' B' H' Q31 Q18 Q6 Q30 Q24 Q29 Q8 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_D2] in KP.
          kcbv_in Q31; kcbv_in Q18; kcbv_in Q6; kcbv_in Q30; kcbv_in Q24; kcbv_in Q29; kcbv_in Q8. destr_conj KP. zimps.
          eapply (J8BC R5 ci' B' H'). all: jfin.
      + zbr Rfd true.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J8BC Rx ci B H) end. all: jfin. }
  clear KBA3 KLL.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn. dand SR0 as (_ & _ & _ & _ & _ & _ & _ & _ & C112 & _ & C124 & _).
  rewrite <- Eda in C112. clear Eda.
  tstep1 Rfd.
  zstep Rfd.
  clear C112 C124.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zsetreg (2 ^ db + -1) ltac:(symmetry; rewrite mask_not_sllw by lia; lia).
  zstep Rfd.
  pose proof (land_mask_l' hold db ltac:(lia)) as Ri0.
  pose proof (tab_root_entry DISTS rdD db nd (Z.land (2 ^ db + -1) hold) TOKD Ri0) as (Hbits0 & _ & _ & _).
  zstep Rfd.
  zsetreg (4 * Z.land (2 ^ db + -1) hold) ltac:(symmetry; apply shiftl_2).
  zstep Rfd.
  tld4_bits HtD (Z.land (2 ^ db + -1) hold).
  destruct (Z_lt_dec bits (code_bits (rdD (Z.land (2 ^ db + -1) hold)))) as [Hneed | Hok].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (d_loop1 (S (Z.to_nat (n - cin))) Rx lx Mx MD T q n da nd db (2 ^ db + -1) cin bits cin bits hold fin rdD Hh) end.
    all: jfin.
    + intros R' H' G24 HH1' HH2' HB14 HBn KP. cbv [keptc KS_D1] in KP. kcbv_in G24. destr_conj KP. zimps.
      eapply (KX1 R' H'). all: jfin.
    + intros R' ci' B' H' G28 G13 G14 G6 G24 G15 G17 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_D1] in KP.
      kcbv_in G28; kcbv_in G13; kcbv_in G14; kcbv_in G6; kcbv_in G24; kcbv_in G15; kcbv_in G17. destr_conj KP. zimps.
      eapply (J04 R' ci' B' H'). all: jfin.
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J04 Rx cin bits hold) end. all: jfin.
Qed.

Theorem arm_DIST : arm_stmt L_DIST DIST.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply dist_s; try eassumption.
Qed.
End FXG.
End S_Dist.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S Require S_LenL.

Module S_LenX.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.S_MatchL S_Match OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.S_DistL S_DistX S_Dist OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.S_LenL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Definition L_LX34 : Z := 87152.
Definition L_L770 : Z := 92404.
Definition L_L778 : Z := 92412.

End FXG.
Ltac kcbv_in H := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6] in H.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
End FXG.
Ltac jfin :=
  lazymatch goal with
  | |- zget _ _ = _ => zreg
  | |- zget_l _ _ _ = _ => zreg
  | |- x_regs _ _ _ _ _ _ _ _ _ _ _ _ => close_xregs
  | |- keptc _ _ _ _ => keptc_close
  | |- realizes _ _ _ => idtac
  | |- forall _, _ => try assumption
  | |- _ \/ _ => assumption
  | |- mem_arr _ _ _ _ _ _ => assumption
  | |- tab_ok _ _ _ _ = true => assumption
  | |- m_halted _ = _ => assumption
  | |- _ => first [assumption | lia]
  end.
Ltac st_cbn_in H := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in H.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Theorem len_to_dist : forall cx fin MD T M0 Rb l M st lf cf (m len : Z),
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENEXT -> sinv cx st lf cf -> 1 <= len -> len < 65536 ->
  s_regs_d10 cx st Rb l -> zget_l Rb l kA6 = len -> zget_l Rb l kT1 = c_p cx + 7160 ->
  s_std cx fin M -> mem_u32 R_segs M (c_p cx + 8) m -> st_rest R_segs cx (st_w3 st len (t_offset st) (t_extra st)) M ->
  s_ret cx st M -> s_out cx st M -> mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
  mpostL R_segs M0 M (fp_loop cx) ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_L778 (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf m len CX Hh Hfin Hmd SI Hl1 Hl2 RG La6 Lt1 STD Hm SREST SRET SOUT Hlens Hcodes HP0 K.
  pose proof (sinv_to_dist cx st lf cf len SI Hmd Hl1 Hl2) as [SI1 ME1].
  pose proof (st_rest_le cx st M DIST len (t_extra st) SREST) as SR1. clear SREST.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode. unfold st_le in SI1, ME1, SR1. st_cbn_in SI1. st_cbn_in ME1. st_cbn_in SR1.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_std STD. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  zkeysb. unfold L_L778, L_DIST in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.
  clear Hm.
  tstep1 Rfd.
  tstep1 Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (dist_s _ fin MD T M0 Rx lx Mx
              (IST DIST last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI1) end.
  - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [DIST]; assumption | exact SR1 | exact SRET | exact SOUT | exact HAG].
  - eapply KALL_mono; [| exact K]. clear - ME1. lia.
Qed.

Theorem len_70 : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENEXT -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l ->
  s_std cx fin M -> mem_u32 R_segs M (c_p cx + 8) LENEXT -> st_rest R_segs cx st M ->
  s_ret cx st M -> s_out cx st M -> mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
  mpostL R_segs M0 M (fp_loop cx) ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_L770 (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG STD Hm SREST SRET SOUT Hlens Hcodes HP0 K.
  assert (HLE : t_extra st <= 15 /\ 1 <= t_length st /\ t_length st <= 32768).
  { dand SI as (_ & _ & _ & Mo). clear - Mo Hmd. unfold MODE in Mo.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    match goal with H : t_mode st = LENEXT -> _ |- _ => exact (H Hmd) end. }
  dand HLE as (HX15 & HL1 & HL32).
  pose proof CX as CX0. pose proof RG as RG0. pose proof STD as STD0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_std STD. icx_cbn.
  zkeysb. unfold L_L770, L_L778 in *. cbv [JTAB_ADDR] in *.
  pose proof SREST as C92. unfold st_rest in C92. icx_cbn. dand C92 as (_ & _ & _ & _ & C92 & _).
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S72 & _).
  pose proof (proj1 SI) as R. unfold RNG in R. icx_cbn. dand R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [RL1 RL2] & _).
  tstep1 Rfd.
  zstep Rfd.
  clear C92 S72.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (len_to_dist _ fin MD T M0 Rx lx Mx
              (IST LENEXT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf LENEXT length CX0 Hh Hfin eq_refl SI) end.
  - lia.
  - lia.
  - split; [| split]; [unfold s_fix | unfold s_vars | ]; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - zreg.
  - icx_cbn. zreg.
  - exact STD0.
  - exact Hm.
  - unfold st_w3; icx_cbn. exact SREST.
  - exact SRET.
  - exact SOUT.
  - exact Hlens.
  - exact Hcodes.
  - exact HP0.
  - exact K.
Qed.

Theorem lenext_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENEXT -> sinv cx st lf cf -> t_extra st <> 0 ->
  s_regs_d10 cx st Rb l -> zget_l Rb l kA3 = t_extra st ->
  s_std cx fin M -> mem_u32 R_segs M (c_p cx + 8) LENEXT -> st_rest R_segs cx st M ->
  s_ret cx st M -> s_out cx st M -> mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
  mpostL R_segs M0 M (fp_loop cx) ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_LX34 (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI Hx1 RG La3 STD Hm SREST SRET SOUT Hlens Hcodes HP0 K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  assert (HLE : extra <= 15 /\ 1 <= length /\ length <= 32768)
    by (clear - MODE_; unfold MODE in MODE_; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
        match goal with H : LENEXT = LENEXT -> _ |- _ => exact (H eq_refl) end).
  dand HLE as (HX15 & HL1 & HL32). clear MODE_.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_std STD. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  prune_rng.
  zkeysb. unfold L_LX34, L_L778, L_LXLOOP, L_LX60, L_LVX_EXT in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KD10 KD00 KSM KRA1 KRL KB11 KB10 KBA3 KLL KRT.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S72 & _).
  destruct (mem_wr_u32_exists_R M (p + 7164) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (vb & Hback & Rvb).
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  assert (J60 : forall R' (ci H B : Z),
    x_regs u p q n ob osz K0 cin cout bits out R' ->
    zget R' kA5 = q + ci -> zget R' kA2 = n - ci -> zget R' kA4 = B -> zget R' kS7 = H -> zget R' kA3 = extra ->
    cin <= ci -> ci <= n -> extra <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci -> B = bits + 8 * (ci - cin) ->
    realizes R_segs (zcfg R_segs 89348 (zupd R' []) M MD) T).
  { intros R' ci H B XR G16 G13 G15 G24 G14 Hc1 Hc2 HxB HB40 HH1 HH2 HBc HB.
    open_xregs XR. kcbv_in G16; kcbv_in G13; kcbv_in G15; kcbv_in G24; kcbv_in G14. clear KL.
    repeat match goal with H : forall i : Z, _ |- _ => lazymatch H with Hfin => fail | _ => clear H end end.
    pose proof SREST as C92. unfold st_rest in C92. icx_cbn. dand C92 as (_ & _ & _ & _ & C92 & _).
    pose proof (pow2_15 extra ltac:(lia)) as HPx.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    tstep1 Rfd.
    clear C92.
    zstep Rfd.
    zstep Rfd.
    clear S72 Hback.
    zstep Rfd.
    zstep Rfd.
    zsetreg (2 ^ extra - 1) ltac:(symmetry; apply mask_not_sllw; lia).
    zstep Rfd.
    pose proof (land_mask_r H extra ltac:(lia)) as Rbx.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zsetreg (H / 2 ^ extra) ltac:(symmetry; apply (srl_hold H B); lia).
    pose proof (hold_shr_bound H B extra ltac:(lia) ltac:(lia)) as HH'.
    zstep Rfd.
    st_prestore_k st_rest_set92 17%positive SREST.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_pull _ _ lf cf ci (H / 2 ^ extra) (B - extra) SI0 ltac:(cbn; lia) ltac:(cbn; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 ME1].
    unfold st_pull in SI1, ME1. st_cbn_in SI1. st_cbn_in ME1.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (len_to_dist _ fin MD T M0 Rx lx Mx
                (IST LENEXT last flags ci cout (H / 2 ^ extra) (B - extra) out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf LENEXT (length + Z.land H (2 ^ extra - 1)) CX0 Hh Hfin eq_refl SI1) end.
    - lia.
    - lia.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - zreg.
    - icx_cbn. zreg.
    - close_std.
    - icx_cbn. exact Hm.
    - unfold st_w3; icx_cbn. exact SREST.
    - exact SRET.
    - exact SOUT.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG.
    - eapply KALL_mono; [| exact K]. clear - ME1. lia. }
  destruct (Z_lt_dec bits extra) as [Hneed | Hhave].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (x_loop (S (Z.to_nat (n - cin))) 87168 89348 Rx lx Mx MD T q n extra cin bits cin bits hold fin) end.
    1: left; split; reflexivity.
    all: jfin.
    +
      intros R' H' G24 HH1 HH2 HB14 HBn KP. cbv [keptc KS_X] in KP. kcbv_in G24. destr_conj KP. zimps.
      eapply (stub_L1 93564 R' [] M MD T q n cin bits u ret); [right; reflexivity | exact Hh | zreg | zreg | zreg | zreg | lia | lia | exact SRET |].
      intros R9 E9 E27 E25 E10 KP9. cbv [keptc KS_L1] in KP9. kcbv_in E9; kcbv_in E27; kcbv_in E25; kcbv_in E10. destr_conj KP9. zimps.
      pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
      unfold st_pull in SI1. st_cbn_in SI1.
      unfold KLEAVE, L_LEAVE in KL.
      eapply (KL R9 M _ ret lf cf SI1).
      * unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
      * close_std.
      * split; [exact Hm | exact SREST].
      * exact SOUT.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' ci' B' H' G16 G13 G15 G24 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_X] in KP. kcbv_in G16; kcbv_in G13; kcbv_in G15; kcbv_in G24.
      destr_conj KP. zimps.
      eapply (J60 R' ci' H' B'). all: jfin.
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J60 Rx cin hold bits) end. all: jfin.
Qed.

Theorem arm_LENEXT : arm_stmt L_LENEXT LENEXT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof SREST as SR0. unfold st_rest in SR0. dand SR0 as (_ & _ & _ & _ & _ & _ & C100 & _).
  dand RG as (FIX & VARS & G27). pose proof FIX as FIX0. unfold s_fix in FIX. destr_conj FIX.
  pose proof SI as SI'. dand SI' as (R & _ & _ & Mo).
  assert (HX : t_extra st <= 15 /\ 1 <= t_length st /\ t_length st <= 32768).
  { clear - Mo Hmd. unfold MODE in Mo. repeat match goal with H : _ /\ _ |- _ => destruct H end.
    match goal with H : t_mode st = LENEXT -> _ |- _ => exact (H Hmd) end. }
  assert (HX0 : 0 <= t_extra st) by (unfold RNG in R; destr_conj R; assumption). clear R Mo.
  zkeysb. unfold L_LENEXT, L_LX34, L_L770 in *.
  tstep1 Rfd.
  destruct (Z.eq_dec (t_extra st) 0) as [Hx0 | Hx1].
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (len_70 cx fin MD T M0 Rx lx M st lf cf CX Hh Hfin Hmd SI) end.
    + split; [exact FIX0 | split; [exact VARS | zreg]].
    + exact STD.
    + rewrite <- Hmd. exact Hmode.
    + exact SREST.
    + exact SRET.
    + exact SOUT.
    + exact Hlens.
    + exact Hcodes.
    + exact HP0.
    + exact K.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (lenext_s cx fin MD T M0 Rx lx M st lf cf CX Hh Hfin Hmd SI Hx1) end.
    + split; [exact FIX0 | split; [exact VARS | zreg]].
    + zreg.
    + exact STD.
    + rewrite <- Hmd. exact Hmode.
    + exact SREST.
    + exact SRET.
    + exact SOUT.
    + exact Hlens.
    + exact Hcodes.
    + exact HP0.
    + exact K.
Qed.
End FXG.
End S_LenX.

Module S_Len.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.S_MatchL S_Match OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.S_DistL S_DistX S_Dist OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S.S_LenL S_LenX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Definition L_LSLOW : Z := 91960.
Definition L_L28 : Z := 92332.

Definition e_regs (u p ob osz : Z) (K0 : positive -> Z) (cout out : Z) (R : tree Z) : Prop :=
  zget R kSP = u + -224 /\ zget R kGP = K0 kGP /\ zget R kTP = K0 kTP /\ zget R kS0 = p /\
  zget R kA0 = u /\ zget R kA1 = 0 /\ zget R kS6 = p + 168 /\ zget R kS4 = 16209 /\
  zget R kS3 = ob + cout /\ zget R kRA = osz - cout /\ zget R kS9 = 67008.
End FXG.
Ltac open_eregs H := unfold e_regs in H; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6] in H; destr_conj H.
Ltac close_eregs := unfold e_regs; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6]; split_conj; zreg.
Ltac jfin ::=
  lazymatch goal with
  | |- zget _ _ = _ => zreg
  | |- zget_l _ _ _ = _ => zreg
  | |- e_regs _ _ _ _ _ _ _ _ => close_eregs
  | |- keptc _ _ _ _ => keptc_close
  | |- realizes _ _ _ => idtac
  | |- forall _, _ => try assumption
  | |- _ \/ _ => assumption
  | |- mem_arr _ _ _ _ _ _ => assumption
  | |- tab_ok _ _ _ _ = true => assumption
  | |- m_halted _ = _ => assumption
  | |- s_std _ _ _ => close_std
  | |- st_rest _ _ _ _ => assumption
  | |- s_ret _ _ _ => assumption
  | |- s_out _ _ _ => assumption
  | |- framed _ _ => assumption
  | |- mem_u32 _ _ _ _ => assumption
  | |- mem_u64 _ _ _ _ => assumption
  | |- mem_wr _ _ _ _ => assumption
  | |- _ => first [assumption | lia]
  end.
Ltac mode_getr Mo := clear - Mo; unfold MODE in Mo; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
  first [ assumption | match goal with H : ?x = ?x -> _ |- _ => exact (H eq_refl) end ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
Lemma land_mask_l' : forall x k, 0 <= k -> 0 <= Z.land (2 ^ k + -1) x < 2 ^ k.
Proof. intros x k Hk. replace (2 ^ k + -1) with (2 ^ k - 1) by lia. apply land_mask_l. exact Hk. Qed.

Theorem len_slow_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LEN -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_LSLOW (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  pose proof KM as KM0. open_kmem KM. open_std STD.
  assert (TLV : tables_live cx st cf).
  { assert (ML : codes_liveP (t_mode st) -> tables_live cx st cf) by mode_get MODE_.
    apply ML. rewrite Hmd. unfold codes_liveP. cbv [LEN_ LEN LIT]. lia. }
  dand (live_tabs cx st lf cf M CX RNG_ TLV ROM Hcodes) as (na & nd & TB). clear TLV MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold tabsP in TB. icx_cbn. idtac.
  dand TB as (HtL & HtD & TOKL & TOKD & Cla1 & Cla2 & Cda1 & Cda2 & Cna & Cnd & ALla & ALda & Slaob & Slap & Sdaob & Sdap & Slap2 & Sdap2 & _).
  clear HtD TOKD Cda1 Cda2 Cnd ALda Sdaob Sdap Sdap2.
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) lc) as la eqn:Ela.
  remember (rdc cf lc) as rdL eqn:ErdL. clear ErdL.
  prune_rng.
  zkeysb. unfold L_LSLOW, L_L28, L_LLOOP1, L_L40, L_LLOOP2, L_L700, L_LVX_L1, L_LVX_L2, L_L770, L_LX34 in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD10 KD00 KSM KRA1 KRL KB11 KB10 KRT.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S104 & S96 & _ & S72 & _).
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  pose proof (tab_ok_root _ _ _ _ TOKL) as (Hlb1 & Hna1 & _).
  pose proof (pow2_15 lb ltac:(lia)) as HPlb.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn. dand SR0 as (_ & _ & _ & _ & _ & _ & _ & C104 & _ & C120 & _).
  rewrite <- Ela in C104. clear Ela.
  tstep1 Rfd.
  zstep Rfd.
  clear C104 C120.
  zstep Rfd.
  tstep1 Rfd.
  assert (J28 : forall R' M' (ci B Hd e lbv : Z),
    e_regs u p ob osz K0 cout out R' -> zget R' kT6 = -16180 -> zget R' kT4 = 30 -> zget R' kS9 = 67008 ->
    zget R' kS11 = p + 7160 -> zget R' kT2 = code_op e -> zget R' kA7 = code_val e -> zget R' kA4 = code_bits e ->
    zget R' kA6 = lbv -> zget R' kA3 = B -> zget R' kS7 = Hd -> zget R' kS10 = q + ci -> zget R' kA2 = n - ci ->
    1 <= code_bits e ->
    ((code_op e = 0 /\ code_val e < 256)
     \/ (16 <= code_op e < 32 /\ 3 <= code_val e /\ code_val e + Z.shiftl 1 (code_op e - 16) - 1 <= 258 /\ code_op e <= 21)
     \/ (Z.land (code_op e) 64 <> 0 /\ Z.land (code_op e) 16 = 0)) ->
    0 <= lbv -> lbv <= 15 ->
    cin <= ci -> ci <= n -> code_bits e <= B -> B <= 40 -> 0 <= Hd -> Hd < 2 ^ B -> B <= 8 * ci ->
    8 * (n - ci) + B <= 8 * (n - cin) + bits ->
    s_std (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M' -> mem_u32 R_segs M' (p + 8) LEN ->
    st_rest R_segs (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_ret (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_out (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    mem_arr 2 R_segs M' (p + 168) 320 lf -> mem_arr 4 R_segs M' (p + 1384) 1444 cf ->
    mem_wr R_segs M' p 7176 ->
    framed (fun X => mpostL R_segs M0 X [(u - 1024, 1024); (u, 112); (p, 7176); (ob, osz)]) M' ->
    realizes R_segs (zcfg R_segs 92332 (zupd R' []) M' MD) T).
  { intros R' M' ci B Hd e lbv ER G32 G30 G31 G25 G8 G18 G15 G17 G14 G24 G28 G13 Hbe CLS Hlv1 Hlv2 Hc1 Hc2 HbB HB40 HH1 HH2 HBc HWm
           STD' Hm' SR' RET' OUT' HL' HC' Wp' HAG'.
    open_eregs ER. kcbv_in G32; kcbv_in G30; kcbv_in G31; kcbv_in G25; kcbv_in G8; kcbv_in G18; kcbv_in G15;
    kcbv_in G17; kcbv_in G14; kcbv_in G24; kcbv_in G28; kcbv_in G13.
    clear S104 S96 S72 HtL KL KLL ROM Wstk Wp Wob Ww FRM CST HK Hin Hmode SREST SRET SOUT Hlens Hcodes HAG.
    repeat match goal with Hd : forall i : Z, _ |- _ => lazymatch Hd with Hfin => fail | _ => clear Hd end end.
    repeat match goal with Hd : context [M] |- _ => clear Hd end.
    rename STD' into STD. rename Hm' into Hmode. rename SR' into SREST. rename RET' into SRET. rename OUT' into SOUT.
    rename HL' into Hlens. rename HC' into Hcodes. rename HAG' into HAG.
    pose proof STD as STD2. open_std STD2. icx_cbn. zkeys.
    pose proof (code_op_range e) as Rop. pose proof (code_val_range e) as Rval. pose proof (code_bits_range e) as Rbi.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    zsetreg (Hd / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold Hd B); lia).
    pose proof (hold_shr_bound Hd B (code_bits e) ltac:(lia) ltac:(lia)) as HH'.
    tstep1 Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      destruct (mem_wr_u32_exists_R Mx (p + 7164) ltac:(eapply mem_wr_sub; [exact Wp' | lia | lia])) as (vb & Hback & Rvb) end. clear Hback.
    tstep1 Rfd.
    st_prestore st_rest_set92 (code_val e) SREST.
    tstep1 Rfd.
    pose proof (sinv_pull _ _ lf cf ci (Hd / 2 ^ code_bits e) (B - code_bits e) SI0 ltac:(cbn; lia) ltac:(cbn; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 ME1].
    unfold st_pull in SI1, ME1. st_cbn_in SI1. st_cbn_in ME1.
    unfold KDISP, L_DISP in KD. unfold KBADMSG_A3, L_BADMSG_A3 in KBA3. zkeys.
    destruct CLS as [[Hop0 Hv256] | [(Hop16 & Hv3 & Hv258 & Hop21) | [H64 H16]]].
    -
      zbr Rfd true.
      zstep Rfd.
      clear Hmode.
      tstep1 Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_len_set _ _ lf cf LIT (code_val e) SI1 eq_refl ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
      unfold st_le in SI2. st_cbn_in SI2.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KD Rx Mx (IST LIT last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                             lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI2) end.
      + clear - ME1. unfold meas, Wm in *. icx_cbn. change (rank LIT) with 13 in *. change (rank LEN) with 18 in *. lia.
      + unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
      + unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
        all: first [cbv [LIT]; assumption | exact SREST | exact SRET | exact SOUT | exact HAG].
    -
      pose proof (op_base_tests (code_op e) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
      rewrite shiftl_1_pow in Hv258 by lia. pose proof (pow2_15 (code_op e - 16) ltac:(lia)) as HPx.
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd.
      zsetreg (code_op e + -16) ltac:(lia).
      zstep Rfd.
      st_prestore_k st_rest_set100 14%positive SREST.
      tstep1 Rfd.
      clear Hmode.
      tstep1 Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_to_lenext _ _ lf cf (code_val e) (code_op e - 16) SI1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI2 ME2].
      unfold st_le in SI2, ME2. st_cbn_in SI2. st_cbn_in ME2.
      destruct (Z.eq_dec (code_op e - 16) 0) as [Hx0 | Hx1].
      + zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (len_70 _ fin MD T M0 Rx lx Mx
                    (IST LENEXT last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset (code_op e - 16)
                         lc dc lb db ncode nlen ndist shave nx whave wnext)
                    lf cf CX0 Hh Hfin eq_refl SI2) end.
        * unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
        * close_std.
        * icx_cbn. cbv [LENEXT]. assumption.
        * icx_cbn. exact SREST.
        * exact SRET.
        * exact SOUT.
        * exact Hlens.
        * exact Hcodes.
        * exact HAG.
        * eapply KALL_mono; [| exact K]. clear - ME1 ME2. lia.
      + zbr Rfd false.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (lenext_s _ fin MD T M0 Rx lx Mx
                    (IST LENEXT last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset (code_op e - 16)
                         lc dc lb db ncode nlen ndist shave nx whave wnext)
                    lf cf CX0 Hh Hfin eq_refl SI2) end.
        * icx_cbn. exact Hx1.
        * unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
        * icx_cbn. zreg.
        * close_std.
        * icx_cbn. cbv [LENEXT]. assumption.
        * icx_cbn. exact SREST.
        * exact SRET.
        * exact SOUT.
        * exact Hlens.
        * exact Hcodes.
        * exact HAG.
        * eapply KALL_mono; [| exact K]. clear - ME1 ME2. lia.
    -
      assert (Tnz : code_op e <> 0) by (intros E; rewrite E in H64; apply H64; reflexivity).
      pose proof (land_range_r (code_op e) 64 ltac:(lia)) as R64. pose proof (land_range_r (code_op e) 32 ltac:(lia)) as R32.
      zbr Rfd false.
      zstep Rfd.
      pose proof (sinv_len_set _ _ lf cf LEN (code_val e) SI1 eq_refl ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
      unfold st_le in SI2. st_cbn_in SI2.
      destruct (Z.eq_dec (Z.land (code_op e) 32) 0) as [H32 | H32].
      +
        zbr Rfd false.
        zstep Rfd.
        zbr Rfd true.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
          eapply (KBA3 Rx Mx (IST LEN last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                                lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf) end.
        * apply sinv_bad_of. exact SI2.
        * pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                        (IST LEN last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                             lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
          cbn [t_mode] in MB. change (rank LEN) with 18 in MB. clear - MB ME1. unfold meas, Wm in *. icx_cbn. lia.
        * unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
        * zreg. * zreg. * zreg. * zreg. * zreg. * zreg.
        * cbv [kA3]. lazymatch goal with |- 0 <= ?x < _ => replace x with 66608 by (symmetry; zreg) end. rewrite TW64. lia.
        * unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
          all: first [exact SREST | exact SRET | exact SOUT | exact HAG].
      +
        zbr Rfd true.
        zstep Rfd.
        zstep Rfd.
        clear Hmode.
        tstep1 Rfd.
        repeat match goal with Hd : mem_u32 _ _ (p + 7164) _ |- _ => clear Hd end.
        tstep1 Rfd.
        zstep Rfd.
        zstep Rfd.
        pose proof (sinv_len_set _ _ lf cf TYPE (code_val e) SI1 eq_refl ltac:(right; right; reflexivity) ltac:(lia) ltac:(lia)) as SI3.
        unfold st_le in SI3. st_cbn_in SI3.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
          eapply (KD Rx Mx (IST TYPE last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                               lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI3) end.
        * clear - HWm Hbe. unfold meas, Wm. icx_cbn. change (rank TYPE) with 24. change (rank LEN) with 18. lia.
        * unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
        * unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
          all: first [cbv [TYPE]; assumption | exact SREST | exact SRET | exact SOUT | exact HAG]. }
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => rename Mx into M1 end.
  match goal with Hb : mem_u32 _ M1 (p + 7164) 0 |- _ => rename Hb into Hback0 end.
  assert (KX1 : forall R' (H' : Z),
    zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (bits + 8 * (n - cin)) -> bits + 8 * (n - cin) <= 14 -> bits + 8 * (n - cin) <= 8 * n ->
    e_regs u p ob osz K0 cout out R' -> zget R' kS2 = n - cin -> zget R' kS8 = bits -> zget R' kS11 = q + cin ->
    realizes R_segs (zcfg R_segs 93520 (zupd R' []) M1 MD) T).
  { intros R' H' G24 HH1 HH2 HB14 HBn ER G25 G9 G27. open_eregs ER. kcbv_in G24; kcbv_in G25; kcbv_in G9; kcbv_in G27.
    clear J28 KBA3 KLL KD.
    eapply (stub_L1 93520 R' [] M1 MD T q n cin bits u ret); [left; reflexivity | exact Hh | zreg | zreg | zreg | zreg | lia | lia | exact SRET |].
    intros R9 E9 E27 E25 E10 KP. cbv [keptc KS_L1] in KP. kcbv_in E9; kcbv_in E27; kcbv_in E25; kcbv_in E10. destr_conj KP. zimps.
    pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
    unfold st_pull in SI1. st_cbn_in SI1.
    unfold KLEAVE, L_LEAVE in KL.
    eapply (KL R9 M1 _ ret lf cf SI1).
    - unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SOUT.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  assert (J40 : forall R' (ci B Hd : Z),
    e_regs u p ob osz K0 cout out R' -> zget R' kT6 = -16180 -> zget R' kT4 = 30 -> zget R' kS9 = 67008 ->
    zget R' kS2 = n - cin -> zget R' kS8 = bits -> zget R' kS11 = q + cin -> zget R' kA5 = la -> zget R' kA6 = 2 ^ lb + -1 ->
    zget R' kS10 = q + ci -> zget R' kA2 = n - ci -> zget R' kA3 = B -> zget R' kS7 = Hd ->
    zget R' kA7 = la + 4 * Z.land (2 ^ lb + -1) Hd -> zget R' kA4 = code_bits (rdL (Z.land (2 ^ lb + -1) Hd)) ->
    cin <= ci -> ci <= n -> B = bits + 8 * (ci - cin) -> code_bits (rdL (Z.land (2 ^ lb + -1) Hd)) <= B -> B <= 40 ->
    0 <= Hd -> Hd < 2 ^ B -> B <= 8 * ci ->
    realizes R_segs (zcfg R_segs 92096 (zupd R' []) M1 MD) T).
  { intros R' ci B Hd ER G32 G30 G31 G25 G9 G27 G16 G17 G28 G13 G14 G24 G18 G15 Hc1 Hc2 HB HbB HB40 HH1 HH2 HBc.
    open_eregs ER. kcbv_in G32; kcbv_in G30; kcbv_in G31; kcbv_in G25; kcbv_in G9; kcbv_in G27; kcbv_in G16; kcbv_in G17;
    kcbv_in G28; kcbv_in G13; kcbv_in G14; kcbv_in G24; kcbv_in G18; kcbv_in G15.
    clear KX1 KL KD KBA3.
    set (i := Z.land (2 ^ lb + -1) Hd) in *.
    pose proof (land_mask_l' Hd lb ltac:(lia)) as Ri. fold i in Ri.
    pose proof (tab_root_entry LENS rdL lb na i TOKL Ri) as (Hbits & _ & _ & CASES).
    pose proof (code_op_range (rdL i)) as Rop. pose proof (code_val_range (rdL i)) as Rval.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    tld4_op HtL i.
    tld4_val HtL i.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
    -
      apply term_ok_LENS in TM as [Hb1 CLS].
      apply is_linkop_false in NL.
      assert (Hterm : code_op (rdL i) = 0 \/ 16 <= code_op (rdL i)).
      { destruct CLS as [(A & _) | [(A & _) | (A64 & _)]]; [lia | lia |].
        pose proof (land_range_r (code_op (rdL i)) 64 ltac:(lia)).
        destruct (Z.eq_dec (code_op (rdL i)) 0) as [E|E]; [left; exact E|]. right.
        destruct (Z_lt_dec (code_op (rdL i)) 16); [|lia]. exfalso. apply NL. lia. }
      destruct Hterm as [E | E];
        [ assert (Hbr : (code_op (rdL i) + -1) mod 18446744073709551616 = 18446744073709551615) by (rewrite E; reflexivity)
        | idtac ];
        zbr Rfd true;
        zstep Rfd;
        zstep Rfd;
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J28 Rx Mx ci B Hd (rdL i) 0) end;
        jfin.
    -
      rewrite L2 in G15.
      pose proof (op_link_tests (code_op (rdL i)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
      assert (HPm : 1 <= 2 ^ (lb + code_op (rdL i)) <= 32768) by (apply pow2_15; lia).
      pose proof (pow2_15 (code_op (rdL i)) ltac:(lia)) as HPlo.
      zbr Rfd false.
      zstep Rfd.
      zsetreg (lb + code_op (rdL i)) ltac:(lia).
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zsetreg (2 ^ (lb + code_op (rdL i)) + -1) ltac:(symmetry; rewrite mask_not_sllw by lia; lia).
      set (m2 := 2 ^ (lb + code_op (rdL i)) + -1) in *.
      set (v := code_val (rdL i)) in *. set (lo := code_op (rdL i)) in *.
      assert (JR : forall Hx, 0 <= Z.land Hx m2 / 2 ^ lb < 2 ^ lo).
      { intros Hx. pose proof (land_mask_r Hx (lb + lo) ltac:(lia)) as A. replace (2 ^ (lb + lo) - 1) with m2 in A by lia.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
      zstep Rfd.
      pose proof (land_mask_r Hd (lb + lo) ltac:(lia)) as Rm. replace (2 ^ (lb + lo) - 1) with m2 in Rm by lia.
      zstep Rfd.
      zsetreg (Z.land Hd m2 / 2 ^ lb) ltac:(rewrite <- L2; symmetry; apply srlw_small; lia).
      pose proof (JR Hd) as Rj.
      destruct (SUB _ Rj) as [NL2 TM2]. pose proof TM2 as TM2'. apply term_ok_LENS in TM2 as [Hbits2 CLS2].
      zstep Rfd.
      zsetreg (v + Z.land Hd m2 / 2 ^ lb) ltac:(lia).
      zstep Rfd.
      zstep Rfd.
      zsetreg (4 * (v + Z.land Hd m2 / 2 ^ lb)) ltac:(symmetry; apply zext32_shift30; lia).
      zstep Rfd.
      tld4_bits HtL (v + Z.land Hd m2 / 2 ^ lb).
      zstep Rfd.
      assert (J700 : forall R2 (ci2 B2 H2 : Z),
        e_regs u p ob osz K0 cout out R2 ->
        zget R2 kA5 = la -> zget R2 kA6 = lb -> zget R2 kA7 = v -> zget R2 kS11 = p + 7160 -> zget R2 kA4 = lb ->
        zget R2 kA2 = n - ci -> zget R2 kA3 = B -> zget R2 kS10 = q + ci ->
        zget R2 kT6 = q + ci2 -> zget R2 kT0 = n - ci2 -> zget R2 kT1 = B2 -> zget R2 kS7 = H2 ->
        zget R2 kT5 = la + 4 * (v + Z.land H2 m2 / 2 ^ lb) -> zget R2 kT3 = code_bits (rdL (v + Z.land H2 m2 / 2 ^ lb)) ->
        ci <= ci2 -> ci2 <= n -> B2 = bits + 8 * (ci2 - cin) -> lb + code_bits (rdL (v + Z.land H2 m2 / 2 ^ lb)) <= B2 -> B2 <= 40 ->
        0 <= H2 -> H2 < 2 ^ B2 -> B2 <= 8 * ci2 ->
        realizes R_segs (zcfg R_segs 92296 (zupd R2 []) M1 MD) T).
      { intros R2 ci2 B2 H2 ER2 Q16 Q17 Q18 Q25 Q15 Q13 Q14 Q28 Q32 Q6 Q7 Q24 Q31 Q29 Hd1 Hd2 HB2 HbB2 HB2' HH21 HH22 HBc2.
        open_eregs ER2. kcbv_in Q16; kcbv_in Q17; kcbv_in Q18; kcbv_in Q25; kcbv_in Q15; kcbv_in Q13; kcbv_in Q14;
        kcbv_in Q28; kcbv_in Q32; kcbv_in Q6; kcbv_in Q7; kcbv_in Q24; kcbv_in Q31; kcbv_in Q29.
        clear KLL CLS2 TM2' NL2 Hbits2 Rj Rm.
        pose proof (JR H2) as Rj2.
        set (j2 := Z.land H2 m2 / 2 ^ lb) in *.
        assert (HPB2 : 1 <= 2 ^ B2 <= 2 ^ 40) by (split; [pose proof (pow2_pos B2 ltac:(lia)); lia | apply pow2_le; lia]).
        pose proof (code_bits_range (rdL (v + j2))) as Rb2.
        tld4_op HtL (v + j2).
        tld4_val HtL (v + j2).
        zstep Rfd.
        zsetreg (H2 / 2 ^ lb) ltac:(symmetry; apply (srl_hold H2 B2); lia).
        pose proof (hold_shr_bound H2 B2 lb ltac:(lia) ltac:(lia)) as HH2'.
        tstep1 Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        destruct (SUB _ Rj2) as [NL3 TM3]. apply term_ok_LENS in TM3 as [Hbits3 CLS3].
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
          eapply (J28 Rx Mx ci2 (B2 - lb) (H2 / 2 ^ lb) (rdL (v + j2)) lb) end.
        all: jfin. }
      destruct (Z_lt_dec B (lb + code_bits (rdL (v + Z.land Hd m2 / 2 ^ lb)))) as [Hneed | Hok].
      + zbr Rfd false.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (l_loop2 (S (Z.to_nat (n - ci))) Rx lx Mx MD T q n la na lb lo v m2 ci B ci B Hd fin rdL Hh) end.
        all: jfin.
        *
          intros R5 H' Q24 HH1' HH2' HB29 HBn KP. cbv [keptc KS_E2] in KP. kcbv_in Q24. destr_conj KP. zimps.
          clear J700 J28 SUB JR.
          eapply (stub_L2 R5 [] M1 MD T q n ci B Hh); [zreg | zreg | zreg | lia | lia |].
          intros R9 E9 E27 E25 KP9. cbv [keptc KS_L2] in KP9. kcbv_in E9; kcbv_in E27; kcbv_in E25. destr_conj KP9. zimps.
          pose proof (sinv_pull _ _ lf cf n H' (B + 8 * (n - ci)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1' HH2' HBn ltac:(cbn; lia)) as [SI1 _].
          unfold st_pull in SI1. st_cbn_in SI1.
          unfold KLEAVE_LD, L_LEAVE_LD in KLL. zkeys.
          eapply (KLL R9 M1 _ lf cf SI1).
          -- unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
          -- close_std.
          -- split; [exact Hmode | exact SREST].
          -- exact SRET.
          -- exact SOUT.
          -- exact Hlens.
          -- exact Hcodes.
          -- exact HAG.
        *
          intros R5 ci' B' H' Q32 Q6 Q7 Q30 Q24 Q31 Q29 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_E2] in KP.
          kcbv_in Q32; kcbv_in Q6; kcbv_in Q7; kcbv_in Q30; kcbv_in Q24; kcbv_in Q31; kcbv_in Q29. destr_conj KP. zimps.
          eapply (J700 R5 ci' B' H'). all: jfin.
      + zbr Rfd true.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J700 Rx ci B Hd) end. all: jfin. }
  clear KBA3 KLL KD J28.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zsetreg (2 ^ lb + -1) ltac:(symmetry; rewrite mask_not_sllw by lia; lia).
  zstep Rfd.
  pose proof (land_mask_l' hold lb ltac:(lia)) as Ri0.
  pose proof (tab_root_entry LENS rdL lb na (Z.land (2 ^ lb + -1) hold) TOKL Ri0) as (Hbits0 & _ & _ & _).
  zstep Rfd.
  zsetreg (4 * Z.land (2 ^ lb + -1) hold) ltac:(symmetry; apply shiftl_2).
  zstep Rfd.
  tld4_bits HtL (Z.land (2 ^ lb + -1) hold).
  destruct (Z_lt_dec bits (code_bits (rdL (Z.land (2 ^ lb + -1) hold)))) as [Hneed | Hok].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (l_loop1 (S (Z.to_nat (n - cin))) Rx lx Mx MD T q n la na lb (2 ^ lb + -1) cin bits cin bits hold fin rdL Hh) end.
    all: jfin.
    + intros R' H' G24 HH1' HH2' HB14 HBn KP. cbv [keptc KS_E1] in KP. kcbv_in G24. destr_conj KP. zimps.
      eapply (KX1 R' H'). all: jfin.
    + intros R' ci' B' H' G28 G13 G14 G6 G24 G15 G18 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_E1] in KP.
      kcbv_in G28; kcbv_in G13; kcbv_in G14; kcbv_in G6; kcbv_in G24; kcbv_in G15; kcbv_in G18. destr_conj KP. zimps.
      eapply (J40 R' ci' B' H'). all: jfin.
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J40 Rx cin bits hold) end. all: jfin.
Qed.
End FXG.
End S_Len.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S Require Import SBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S Require Import S_MatchL. Import S_Match. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S Require Import S_DistL. Import S_DistX. Import S_Dist. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I7S Require Import S_LenL. Import S_LenX. Import S_Len.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Definition L_FRET : Z := 91896.

End FXG.
Ltac st_cbn := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Definition st_fast (st : ist) (m ci co H B : Z) : ist :=
  IST m (t_last st) (t_flags st) ci co H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_after_fast : forall cx st lf cf m ci co H B,
  sinv cx st lf cf -> t_mode st = LEN ->
  0 <= ci -> ci <= c_n cx -> t_cout st <= co -> co <= c_osz cx ->
  0 <= B -> B <= 7 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B + (c_osz cx - co) < 8 * (c_n cx - t_cin st) + t_bits st + (c_osz cx - t_cout st) ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  (m = LEN \/ m = TYPE \/ m = BAD) ->
  sinv cx (st_fast st m ci co H B) lf cf /\ meas cx (st_fast st m ci co H B) < meas cx st.
Proof.
  intros cx st lf cf m ci co H B SI Hm Hci1 Hci2 Hco1 Hco2 HB1 HB2 HH1 HH2 HBc HW HI Hm'.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_fast, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN = HEAD \/ LEN = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  dand P as (P1 & P2 & P3). unfold PROG, Wm in P1, P2, P3 |- *. icx_cbn.
  split; [split; [| split; [exact W | split]] |].
  - clear W Mf Mlive P1 P2 P3. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - clear W Mf Mlive Hm'. split; [lia_std | split; [lia_std |]].
    first [ exact P3 | destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std] ].
  - unfold MODE. icx_cbn.
    split; [clear - Hm'; unfold reach; destruct Hm' as [-> | [-> | ->]]; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros HL; destruct Hm' as [-> | [-> | ->]];
              [ apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
              | exfalso; clear - HL; unfold codes_liveP in HL; modes_cbv; lia_std
              | exfalso; clear - HL; unfold codes_liveP in HL; modes_cbv; lia_std ]
          | destruct Hm' as [-> | [-> | ->]]; mode_vacuous ].
  - clear - HW Hm'. pose proof (rank_range m) as RR. change (rank LEN) with 18. lia_std.
Qed.

Lemma win_arr : forall M w, 0 < w \/ w = 0 -> w + 32768 <= two64 -> (w <> 0 -> mem_wr R_segs M w 32768) ->
  exists fw, (w <> 0 -> mem_arr 1 R_segs M w 32768 fw) /\ (forall i, 0 <= i < 32768 -> 0 <= fw i < 256).
Proof.
  intros M w Hw Hw2 Ww. destruct (Z.eq_dec w 0) as [E|NE].
  - exists (fun _ => 0). split; [intros C; contradiction | intros; lia_std].
  - destruct (out_arr M w 32768 (Ww NE) ltac:(lia_std) ltac:(lia_std) Hw2) as (fw & A & B).
    exists fw. split; [intros _; exact A | exact B].
Qed.

Section LenF.
Hypothesis IFAST : ifast_spec_s.

Theorem len_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LEN -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_LEN (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_).
  pose proof KM as KM0. pose proof RG as RG0. open_kmem KM. open_std STD.
  assert (TLV : tables_live cx st cf).
  { assert (ML : codes_liveP (t_mode st) -> tables_live cx st cf) by mode_get MODE_.
    apply ML. rewrite Hmd. unfold codes_liveP. cbv [LEN_ LEN LIT]. lia. }
  dand (live_tabs cx st lf cf M CX RNG_ TLV ROM Hcodes) as (na & nd & TB). clear TLV MODE_ PROG_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold tabsP in TB. icx_cbn. idtac.
  dand TB as (HtL & HtD & TOKL & TOKD & Cla1 & Cla2 & Cda1 & Cda2 & Cna & Cnd & ALla & ALda & Slaob & Slap & Sdaob & Sdap & Slap2 & Sdap2 & _).
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) lc) as la eqn:Ela.
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) dc) as da eqn:Eda.
  remember (rdc cf lc) as rdL eqn:ErdL. remember (rdc cf dc) as rdD eqn:ErdD. clear ErdL ErdD.
  pose proof (tab_ok_root _ _ _ _ TOKL) as (Hlb1 & Hna1 & _). pose proof (tab_ok_root _ _ _ _ TOKD) as (Hdb1 & Hnd1 & _).
  pose proof (pow2_15 lb ltac:(lia)) as HPlb. pose proof (pow2_15 db ltac:(lia)) as HPdb.
  prune_rng.
  zkeysb. unfold L_LEN, L_LSLOW, L_FRET, L_RELOAD, L_IFAST in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  zstep Rfd.
  destruct (Z_lt_dec (n - cin) 6) as [Hh6 | Hh6].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (len_slow_s _ fin MD T M0 Rx lx M
                (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI0) end; [| exact KM0 | exact K].
    unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg. }
  zbr Rfd false.
  zstep Rfd.
  destruct (Z_lt_dec (osz - cout) 258) as [Hl258 | Hl258].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (len_slow_s _ fin MD T M0 Rx lx M
                (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI0) end; [| exact KM0 | exact K].
    unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg. }
  zbr Rfd false.
  (* 1.4: the fast path also needs bits < 8 (li a2,7; bltu a2,s8 -> the slow path) *)
  zstep Rfd.                          (* li a2,7 *)
  destruct (Z_lt_dec 7 bits) as [Hb8 | Hb8].
  { zbr Rfd true.                     (* bits >= 8: the slow path *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (len_slow_s _ fin MD T M0 Rx lx M
                (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI0) end; [| exact KM0 | exact K].
    unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg. }
  zbr Rfd false.
  clear KM0 RG0.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KD10 KD00 KSM KRA1 KB11 KB10 KBA3 KL KLL KRT.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S104 & S96 & _ & _ & _ & S72 & _).
  pose proof SOUT as S80. unfold s_out in S80. icx_cbn.
  pose proof CST as CS. unfold i_cst in CS. icx_cbn. dand CS as (S64u & _ & _ & _ & _ & _ & C60 & C72 & C7144).
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn.
  dand SR0 as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
  rewrite <- Ela in C104. rewrite <- Eda in C112. clear SREST.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    destruct (out_arr Mx ob osz Wob ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fo & HOB & Rfo);
    destruct (win_arr Mx w ltac:(lia) ltac:(rewrite TW64; lia) ltac:(intros Hw; pose proof Ww as X; rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw) in X; cbv [WIN_SIZE] in X; exact X)) as (fw & Hwin & Rfw) end.
  pose proof WIN_ as WIN'. unfold WIN in WIN'. icx_cbn. cbv [WIN_SIZE] in WIN'. destruct WIN' as [WIN0 WIN1].
  unfold ifast_spec_s, ifast_spec_at in IFAST.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (IFAST Rx lx Mx MD T u p q n ob osz w whave wnext cin cout hold bits out lb db la na da nd (u + -224) 91896 135168 zc rdL rdD fin fo fw Hh) end.
  all: first [ lazymatch goal with
       | |- zget_l _ _ _ = _ => zreg
       | |- Z.land _ _ = _ => reflexivity
       | |- ZSEP _ => first [ assumption | exact (sep_ob_u _ _ SEP) | exact (sep_p_ob _ _ SEP) | exact (sep_p_q _ _ SEP) | exact (sep_ob_q _ _ SEP)
                            | exact (sep_w_p _ _ SEP) | exact (sep_w_q _ _ SEP) | exact (sep_w_ob _ _ SEP) ]
       | |- tab_ok _ _ _ _ = true => assumption
       | |- _ mod _ = _ => first [ assumption | exact (proj1 AL) | exact (proj1 (proj2 AL))
                                 | pose proof (proj1 AL) as ALu; clear - ALu; cbn in ALu; Z.to_euclidean_division_equations; lia ]
       | |- _ \/ _ => destruct (Z.eq_dec w 0) as [Ew|Nw]; [left; exact Ew | right; split; [lia | split; [cbv [WIN_SIZE ]; lia | exact (proj2 (proj2 AL))]]]
       | |- _ -> mem_wr _ _ _ _ => intros Hw; pose proof Ww as X; rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw) in X; cbv [WIN_SIZE] in X |- *; exact X
       | |- _ -> mem_arr _ _ _ _ _ _ => exact Hwin
       | |- _ -> _ /\ _ => first [exact WIN0 | cbv [WIN_SIZE]; exact WIN1]
       | |- mem_wr _ _ _ _ => first [assumption | exact Wstk]
       | |- mem_arr _ _ _ _ _ _ => assumption
       | |- mem_u64 _ _ _ _ => assumption
       | |- mem_u32 _ _ _ _ => first [assumption | exact C60 | cbv [LEN]; assumption]
       | |- forall i : Z, _ => first [exact Hfin | exact Rfo | exact Rfw]
       | |- forall R' M', _ => idtac
       | |- _ => cbv [FRA STATE_SIZE WIN_SIZE FR_IF FR_INF]; first [assumption | lia]
       end | match goal with |- ?G => idtac "IFAIL" G end ].
  intros R' M' cin' cout' hold' bits' mode' fo' Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hho1 Hho2 Hb3 HWlt HIle Hm' HP E8 E16 E32 E40 P80 P88 P8 HOB' Rfo' KE.
  unfold kept_eq in KE. zkeys. destr_conj KE. zimps.
  clear Hmode HOB Hwin C60 C72 C7144 S64u HtL HtD.
  repeat match goal with
         | H : mem_u64 _ ?Mo _ _ |- _ => lazymatch Mo with M' => fail | _ => lazymatch type of H with
             | mem_u64 _ _ (u) _ => clear H | mem_u64 _ _ (u + 24) _ => clear H | mem_u64 _ _ (p + 96) _ => clear H end end
         | H : mem_u32 _ ?Mo _ _ |- _ => lazymatch Mo with M' => fail | _ => lazymatch type of H with
             | mem_u32 _ _ (u + 8) _ => clear H | mem_u32 _ _ (u + 32) _ => clear H | mem_u32 _ _ (p + 104) _ => clear H end end
         end.
  unfold if_fp in HP. cbv [FR_IF] in HP. zreattachL HP.
  assert (Hmv : 0 <= mode' < 2147483648) by (clear - Hm'; cbv [LEN TYPE BAD] in Hm'; lia).
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  tstep1 Rfd.
  unfold KRELOAD in KRL. zkeys.
  assert (JRA : forall R9 M9 (m9 : Z),
    (m9 = LEN \/ m9 = TYPE \/ m9 = BAD) -> m9 = mode' \/ (m9 = TYPE /\ mode' = TYPE) ->
    zget R9 3 = u + -224 -> zget R9 4 = K0 4%positive -> zget R9 5 = K0 5%positive -> zget R9 9 = p -> zget R9 11 = u ->
    zget R9 12 = 0 -> zget R9 21 = 16209 -> zget R9 23 = p + 168 -> zget R9 26 = 67008 ->
    zget R9 27 = q + cin' -> zget R9 19 = n - cin' -> zget R9 20 = ob + cout' -> zget R9 2 = osz - cout' ->
    zget R9 24 = hold' -> zget R9 25 = bits' ->
    s_std (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M9 -> mem_u32 R_segs M9 (p + 8) m9 ->
    st_rest R_segs (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M9 ->
    s_ret (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M9 ->
    s_out (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M9 ->
    mem_arr 2 R_segs M9 (p + 168) 320 lf -> mem_arr 4 R_segs M9 (p + 1384) 1444 cf ->
    framed (fun X => mpostL R_segs M0 X [(u - 1024, 1024); (u, 112); (p, 7176); (ob, osz)]) M9 ->
    realizes R_segs (zcfg R_segs 91760 (zupd R9 []) M9 MD) T).
  { intros R9 M9 m9 Hm9 _ G3 G4 G5 G26 G11 G12 G20 G22 G25 G28 G10 G19 G2 G23 G24 STD9 Hmo9 SR9 RET9 OUT9 HL9 HC9 HAG9.
    pose proof (sinv_after_fast _ _ lf cf m9 cin' cout' hold' bits' SI0 eq_refl Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hho1 Hho2 Hb3
                  ltac:(cbn; lia) ltac:(cbn; lia) Hm9) as [SI9 ME9].
    unfold st_fast in SI9, ME9. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI9, ME9.
    eapply (KRL R9 M9 _ lf cf SI9 ME9).
    - unfold s_regs_reload; icx_cbn; zkeys; split_conj; try assumption; first [intros C; discriminate C | intros _; assumption].
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption. all: exact SR9. }
  destruct (Z.eq_dec mode' TYPE) as [HmT | HmT]; cbv [TYPE] in HmT.
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (JRA Rx Mx mode' Hm' ltac:(left; reflexivity)) end.
    all: try zreg.
    all: first [close_std | assumption | unfold st_rest; icx_cbn; split_conj; first [assumption | subst la; assumption | subst da; assumption]].
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (JRA Rx Mx mode' Hm' ltac:(left; reflexivity)) end.
    all: try zreg.
    all: first [close_std | assumption | unfold st_rest; icx_cbn; split_conj; first [assumption | subst la; assumption | subst da; assumption]].
Qed.

Theorem arm_LEN : arm_stmt L_LEN LEN.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply len_s; try eassumption.
Qed.

Lemma sinv_len_ : forall cx st lf cf,
  sinv cx st lf cf -> t_mode st = LEN_ ->
  sinv cx (st_le st LEN (t_length st) (t_extra st)) lf cf /\ meas cx (st_le st LEN (t_length st) (t_extra st)) < meas cx st.
Proof.
  intros cx st lf cf SI Hm.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN_ = HEAD \/ LEN_ = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN_ -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN_ last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  split; [split; [exact R | split; [exact W | split; [prog_transfer P|]]] |].
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Theorem arm_LEN_ : arm_stmt L_LEN_ LEN_.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof (sinv_len_ cx st lf cf SI Hmd) as [SI1 ME1].
  open_kmem KM. destruct SAT as [Hmode SREST].
  dand RG as (FIX & VARS & G27).
  pose proof CX as CX0. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold s_fix, s_vars in FIX, VARS. icx_cbn. destr_conj FIX. destr_conj VARS.
  open_std STD. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold st_le in SI1, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1, ME1.
  zkeysb. unfold L_LEN_, L_LEN in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.
  clear Hmode.
  tstep1 Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (len_s _ fin MD T M0 Rx lx Mx
              (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI1) end.
  - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [LEN]; assumption | exact SREST | exact SRET | exact SOUT | exact HAG].
  - eapply KALL_mono; [| exact K]. clear - ME1. lia.
Qed.
End LenF.
End FXG.
