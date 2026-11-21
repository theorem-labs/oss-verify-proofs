(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require SBase S_Entry.

Module S_Ret.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition s_regs_back (cx : ictx) (rc : Z) (R : tree Z) : Prop :=
  zget R kA0 = rc /\ zget R kSP = c_u cx /\ zget R kRA = c_K cx kRA /\
  zget R kGP = c_K cx kGP /\ zget R kTP = c_K cx kTP /\
  zget R kS0 = c_K cx kS0 /\ zget R kS1 = c_K cx kS1 /\ zget R kS2 = c_K cx kS2 /\ zget R kS3 = c_K cx kS3 /\
  zget R kS4 = c_K cx kS4 /\ zget R kS5 = c_K cx kS5 /\ zget R kS6 = c_K cx kS6 /\ zget R kS7 = c_K cx kS7 /\
  zget R kS8 = c_K cx kS8 /\ zget R kS9 = c_K cx kS9 /\ zget R kS10 = c_K cx kS10 /\ zget R kS11 = c_K cx kS11.

Lemma ret_s : forall cx Rb l M MD T rc,
  ctx_ok ROMHI_S cx -> m_halted MD = None ->
  s_regs_ret cx rc Rb l -> i_frame cx M ->
  (forall R', s_regs_back cx rc R' -> realizes R_segs (zcfg R_segs (c_K cx kRA) (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_RET (zupd Rb l) M MD) T.
Proof.
  intros cx Rb l M MD T rc CX Hh RE FRM K.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  unfold s_regs_ret in RE. icx_cbn. destr_conj RE.
  unfold i_frame in FRM. icx_cbn. destr_conj FRM.
  zkeysb. unfold L_RET in *. pose proof two64_eq as TW64.
  zstep Rfd.
  do 13 (zstep Rfd).
  zstep Rfd.
  zret Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (K R') end.
  unfold s_regs_back; icx_cbn; zkeys; split_conj; zreg.
Qed.
End FXG.
End S_Ret.

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_U2Cw. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2Cw.

Module S_LeaveA.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.SBase OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_Entry.S_Loop S_Ret OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_Entry S_Uw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_LCHECK : Z := 93760.
Definition L_LDT : Z := 93824.
Definition L_UW_ARGS : Z := 93916.
Definition L_LNOWIN : Z := 93964.
Definition L_LRC : Z := 94000.

Definition M2 (cx : ictx) (st : ist) : Z := Wm cx st * 134217728 + (c_n cx - t_cin st).
Definition M2e (cx : ictx) : Z := c_W0 cx * 134217728 + (c_n cx - c_cin0 cx).

Definition fp_call (cx : ictx) : list (Z * Z) := fp_loop cx ++ [(c_w cx, wsz cx)].

Lemma fp_call_widen : forall cx M0 M, mpostL R_segs M0 M (fp_loop cx) -> mpostL R_segs M0 M (fp_call cx).
Proof.
  intros cx M0 M [HA HW]. split; [| exact HW]. intros x Hx. apply HA.
  unfold fp_call, fp_loop in *. cbn in Hx |- *. (first [solve [zkeep_section; tauto] | tauto]).
Qed.

Lemma mem_u32_lo8 : forall M a e, mem_u32 R_segs M a e -> mem_u8 R_segs M a (e mod 256).
Proof.
  intros M a e H. unfold mem_u32, mem_u8 in *. rewrite le4_split in H.
  pose proof (mem_is_app_l R_segs M _ _ _ H) as H0. rewrite Z_to_le_bytes_1_mod. exact H0.
Qed.

Lemma wsz_facts : forall cx, 0 <= wsz cx <= WIN_SIZE /\ (c_w cx = 0 -> wsz cx = 0) /\ (c_w cx <> 0 -> wsz cx = WIN_SIZE).
Proof. intros cx. unfold wsz, WIN_SIZE. destruct (Z.eqb_spec (c_w cx) 0); lia. Qed.

End FXG.
Ltac fp_call_frame HP0 :=
  lazymatch type of HP0 with mpostL ?segs ?M0 ?M ?fp =>
    let HST := fresh "HST" in let HAG := fresh "HAG" in
    pose proof (mpostL_stable segs M0 fp ltac:(ranges_ok_tac)) as HST;
    change (framed (fun X => mpostL segs M0 X fp) M) in HP0; rename HP0 into HAG end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition hideP (P : Prop) : Prop := P.

End FXG.
Ltac zgen :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => let x' := fresh "gv" in set (x' := e); clearbody x'
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition set_win (st : ist) (wh wn : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) wh wn.
Lemma sinv_set_win : forall cx st lf cf wh wn,
  sinv cx st lf cf -> c_w cx <> 0 ->
  0 <= wh -> wh <= WIN_SIZE -> 0 <= wn -> wn < WIN_SIZE -> (wh < WIN_SIZE -> wn = wh) ->
  sinv cx (set_win st wh wn) lf cf.
Proof.
  intros cx st lf cf wh wn (R & W & P & Mo) Hw H1 H2 H3 H4 H5.
  destruct st; unfold sinv, set_win, RNG, WIN, PROG, MODE, Wm, tables_live, ctable_live in *; cbn -[Z.add Z.mul Z.sub Z.pow] in *.
  split; [| split; [| split; [exact P | exact Mo]]].
  - destr_conj R. split_conj; try assumption; lia_std.
  - split; [intros E; exfalso; exact (Hw E) | intros _; split_conj; assumption].
Qed.

Section KDefs.
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem).
Definition KRL : Prop :=
  forall (R : tree Z) (M : mem) (rc : Z) (st : ist) (lf cf : Z -> Z),
    s_regs_back cx rc R -> ainv cx st lf cf ->
    (rc mod two64 = 0 -> M2 cx st < M2e cx) -> Wm cx st <= c_W0 cx ->
    e_mem cx fin st lf cf M -> i_frame cx M ->
    mpostL R_segs M0 M (fp_call cx) ->
    realizes R_segs (zcfg R_segs (c_K cx kRA) (zupd R []) M MD) T.
Definition KRX : Prop :=
  forall (R : tree Z) (M : mem) (rc m : Z),
    rc mod two64 <> 0 -> s_regs_back cx rc R -> s_std cx fin M ->
    mem_u32 R_segs M (c_p cx + 8) m -> reach m ->
    mpostL R_segs M0 M (fp_call cx) ->
    realizes R_segs (zcfg R_segs (c_K cx kRA) (zupd R []) M MD) T.
Definition KW : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (rv : Z) (lf cf : Z -> Z),
    c_w cx = 0 -> sinv cx st lf cf -> c_cout0 cx < t_cout st -> t_mode st <= DONE ->
    zget R kA3 = A_ZCALLOC -> zget R kA0 = 0 -> zget R kA1 = WIN_SIZE -> zget R kA2 = 1 ->
    zget R kS0 = c_ob cx + t_cout st -> zget R kS1 = t_out st - (c_osz cx - t_cout st) -> zget R kS2 = 1 -> zget R kS3 = c_p cx ->
    zget R kS4 = t_out st - (c_osz cx - t_cout st) ->
    zget R kSP = c_u cx + -272 -> zget R kGP = c_K cx kGP -> zget R kTP = c_K cx kTP ->
    zget R kS5 = c_n cx - c_cin0 cx -> zget R kS6 = c_osz cx - t_cout st -> zget R kS7 = t_hold st -> zget R kS8 = t_bits st ->
    zget R kS9 = t_out st -> zget R kS11 = c_q cx + t_cin st ->
    (* 1.4: updatewindow's frame holds ra and inflate's s0 .. s4 (1.4 names: p, rv, n - cin, osz - cout, copy) *)
    mem_u64 R_segs M (c_u cx + -232) L_UW_RET -> mem_u64 R_segs M (c_u cx + -240) (c_p cx) ->
    mem_u64 R_segs M (c_u cx + -248) rv -> mem_u64 R_segs M (c_u cx + -256) (c_n cx - t_cin st) ->
    mem_u64 R_segs M (c_u cx + -264) (c_osz cx - t_cout st) -> mem_u64 R_segs M (c_u cx + -272) (t_out st - (c_osz cx - t_cout st)) ->
    s_std cx fin M -> st_at R_segs cx st M -> strm_at R_segs cx st M ->
    mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
    mpostL R_segs M0 M (fp_call cx) ->
    realizes R_segs (zcfg R_segs T_ZW (zupd R []) M MD) T.

End KDefs.

Section Leave.
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem).
Hypothesis CX : ctx_ok ROMHI_S cx.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < c_n cx -> 0 <= fin i < 256.
Hypothesis OBLOW : c_ob cx + c_osz cx <= c_u cx - FRA.
Hypothesis MEMCPY : memcpy_spec_s.
Hypothesis ADLER : adler32_spec_s.

Hypothesis HKRL : KRL cx fin MD T M0.
Hypothesis HKRX : KRX cx fin MD T M0.
Hypothesis HKW : KW cx fin MD T M0.

Local Ltac open_leave CX SI st HP0 :=
  pose proof SI as SI'; dand SI' as (RNG_ & WIN_ & PROG_ & MODE_);
  match goal with H : MODE _ _ _ _ |- _ => pose proof (reach_bounds _ (proj1 H)) as Hmb end;
  pose proof CX as CXc; open_cx CXc;
  repeat match goal with H : 0 <= c_K _ _ |- _ => clear H | H : c_K _ _ < _ |- _ => clear H end;
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext];
  icx_cbn;
  match goal with H : RNG _ _ _ _ |- _ => unfold RNG in H; icx_cbn; cbv [N_CODES N_LENS] in H; destr_conj H end;
  match goal with H : PROG _ _ |- _ => unfold PROG, Wm in H; icx_cbn; dand H as (PR1 & PR2 & PR3) end;
  zkeysb; unfold L_LCHECK, L_LDT, L_UW_ARGS, L_LNOWIN, L_LRC, L_LEAVE, L_UW, L_UW_RET, L_UW_CALL, L_RET, L_MEM, T_ZW, L_ZB in *;
  cbv [A_ZCALLOC A_ZCFREE A_ADLER32] in *; pose proof two64_eq as TW64;
  pose proof (proj1 (wsz_facts cx)) as Hws0; cbv [WIN_SIZE] in Hws0;
  unfold fp_call, fp_loop in HP0; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE] in HP0; cbn [app] in HP0.

Lemma leave_rc_s : forall Rb l M st rv lf cf,
  sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -224 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kA1 = 0 -> zget_l Rb l kS1 = rv ->
  zget_l Rb l kS5 = c_n cx - c_cin0 cx -> zget_l Rb l kS2 = c_n cx - t_cin st ->
  zget_l Rb l kS9 = t_out st -> zget_l Rb l kRA = c_osz cx - t_cout st ->
  s_std cx fin M -> st_at R_segs cx st M -> strm_at R_segs cx st M ->
  mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
  mpostL R_segs M0 M (fp_call cx) ->
  realizes R_segs (zcfg R_segs L_LRC (zupd Rb l) M MD) T.
Proof.
  intros Rb l M st rv lf cf SI Lsp Lgp Ltp La1 Ls0 Ls4 Ls1 Ls8 Lra STD SAT STRM Hlens Hcodes HP0.
  pose proof STD as STD0. open_std STD. open_leave CX SI st HP0.
  fp_call_frame HP0.
  assert (RET : forall RQ rc,
    zget RQ kSP = c_u cx + -224 -> zget RQ kGP = c_K cx kGP -> zget RQ kTP = c_K cx kTP -> zget RQ kS5 = rc ->
    hideP (rc mod two64 = 0 -> cin <> c_cin0 cx \/ out <> c_osz cx - cout) ->
    realizes R_segs (zcfg R_segs 94048 (zupd RQ []) M MD) T).
  { intros RQ rc Qsp Qgp Qtp Qs4 PRG. zkeys.
    eapply (ret_s cx RQ [] M MD T rc CX Hh).
    - unfold s_regs_ret; icx_cbn; zkeys; split_conj; zreg.
    - exact FRM.
    - intros R9 HB. icx_cbn.
      eapply (HKRL R9 M rc (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf HB).
      + dand SI as (X1 & X2 & X3 & X4). split; [exact X1 | split; [exact X2 | exact X4]].
      + intros Hrc. unfold hideP in PRG. specialize (PRG Hrc). unfold M2, M2e, Wm; icx_cbn. clear HKRL HKRX HKW.
        destruct PR3 as [PR3 | [PR3 _]]; lia.
      + unfold Wm; icx_cbn. clear HKRL HKRX HKW; lia.
      + unfold e_mem; icx_cbn. split_conj; assumption.
      + exact FRM.
      + exact HAG. }
  assert (FIN : forall RJ (j : Z),
    zget RJ kSP = c_u cx + -224 -> zget RJ kGP = c_K cx kGP -> zget RJ kTP = c_K cx kTP ->
    zget RJ kS1 = rv -> zget RJ kA0 = j ->
    hideP (j mod two64 = 0 -> rv mod two64 = 0 -> cin <> c_cin0 cx \/ out <> c_osz cx - cout) ->
    realizes R_segs (zcfg R_segs 94036 (zupd RJ []) M MD) T).
  { intros RJ j Rsp Rgp Rtp Rs0 Ra0 PROGRESS. zkeys.
    destruct (Z.eq_dec (j mod two64) 0) as [Ej|Ej].
    - zbr Rfd true.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (RET R' rv) end;
        [ zreg | zreg | zreg | zreg | intros Hrc; exact (PROGRESS Ej Hrc) ].
    - zbr Rfd false.
      zstep Rfd.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (RET R' (-5)) end;
        [ zreg | zreg | zreg | zreg | intros Hrc; exfalso; revert Hrc; cbv; discriminate ]. }
  Local Ltac rc_steps_A :=
    zstep Rfd; zsetreg 0 ltac:(symmetry; apply Z.lxor_nilpotent);
    zstep Rfd; zsetreg 0 ltac:(symmetry; apply Z.lxor_nilpotent);
    zstep Rfd;
    zstep Rfd; zlit;
    zstep Rfd; zlit;
    zstep Rfd; zlit;
    zstep Rfd; zlit;
    zstep Rfd; match goal with H : _ mod 18446744073709551616 = 0 |- _ => zsetreg 1 ltac:(rewrite H; reflexivity) end;
    zstep Rfd; zlit.
  Local Ltac rc_steps_B :=
    zstep Rfd; zgen;
    zstep Rfd; zgen;
    zstep Rfd;
    zstep Rfd; zgen;
    zstep Rfd; zlit;
    zstep Rfd; zgen;
    zstep Rfd; zgen;
    zstep Rfd; zgen;
    zstep Rfd; zgen.
  Local Ltac rc_apply FIN :=
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => eapply (FIN R') end; try zreg.
  destruct (Z.eq_dec cin (c_cin0 cx)) as [Ecin|Ecin]; [destruct (Z.eq_dec out (c_osz cx - cout)) as [Ecout|Ecout]; [destruct (Z.eq_dec (rv mod two64) 0) as [Erv|Erv]|]|].
  -
    revert Ls4 Ls8. rewrite <- Ecin. rewrite Ecout. intros Ls4 Ls8.
    rc_steps_A. rc_apply FIN. intros Hj _. exfalso. revert Hj. cbv. discriminate.
  - rc_steps_B. rc_apply FIN. intros _ Hrv. exfalso. exact (Erv Hrv).
  - rc_steps_B. rc_apply FIN. intros _ _. right. exact Ecout.
  - rc_steps_B. rc_apply FIN. intros _ _. left. exact Ecin.
Qed.

Lemma leave_uwret_s : forall Rb l M st rv uwret lf cf,
  sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -224 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kA0 = uwret -> (uwret = 0 \/ uwret = 1) -> zget_l Rb l kS1 = rv ->
  zget_l Rb l kS5 = c_n cx - c_cin0 cx -> zget_l Rb l kS2 = c_n cx - t_cin st ->
  zget_l Rb l kS9 = t_out st -> zget_l Rb l kS3 = c_osz cx - t_cout st -> zget_l Rb l kS0 = c_p cx ->
  s_std cx fin M -> st_at R_segs cx st M -> strm_at R_segs cx st M ->
  mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
  mpostL R_segs M0 M (fp_call cx) ->
  realizes R_segs (zcfg R_segs L_UW_RET (zupd Rb l) M MD) T.
Proof.
  intros Rb l M st rv uwret lf cf SI Lsp Lgp Ltp La0 Huw Ls0 Ls4 Ls1 Ls8 Ls2 Ls9 STD SAT STRM Hlens Hcodes HP0.
  pose proof STD as STD0. pose proof HP0 as HP00. open_std STD. open_leave CX SI st HP0.
  fp_call_frame HP0.
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q104 & _ & _ & Q72 & _).
  zstep Rfd.
  zstep Rfd.
  destruct Huw as [Uw0 | Uw1].
  -
    rewrite Uw0 in La0.
    zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (leave_rc_s R9 [] Mx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) rv lf cf SI) end;
      first [ zreg | icx_cbn; zreg | assumption | exact STD0 | exact HP00 ].
  -
    rewrite Uw1 in La0.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (ret_s cx R9 [] Mx MD T (-4) CX Hh) end.
    + unfold s_regs_ret; icx_cbn; zkeys; split_conj; zreg.
    + exact FRM.
    + intros R9 HB.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => eapply (HKRX R9 Mx (-4) 16210) end.
      * cbv. discriminate.
      * exact HB.
      * close_std.
      * match goal with H : mem_u32 R_segs _ (c_p cx + 8) 16210 |- _ => exact H end.
      * unfold reach; cbv [HEAD DICTID MEM]; lia_std.
      * exact HAG.
Qed.

End Leave.
End FXG.
End S_LeaveA.

Module S_Leave.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.SBase OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_Entry.S_Loop S_Ret OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_Entry S_Uw S_LeaveA.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.


Section Leave.
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem).
Hypothesis CX : ctx_ok ROMHI_S cx.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < c_n cx -> 0 <= fin i < 256.
Hypothesis OBLOW : c_ob cx + c_osz cx <= c_u cx - FRA.
Hypothesis MEMCPY : memcpy_spec_s.
Hypothesis ADLER : adler32_spec_s.

Hypothesis HKRL : KRL cx fin MD T M0.
Hypothesis HKRX : KRX cx fin MD T M0.
Hypothesis HKW : KW cx fin MD T M0.

Local Ltac open_leave CX SI st HP0 :=
  pose proof SI as SI'; dand SI' as (RNG_ & WIN_ & PROG_ & MODE_);
  match goal with H : MODE _ _ _ _ |- _ => pose proof (reach_bounds _ (proj1 H)) as Hmb end;
  pose proof CX as CXc; open_cx CXc;
  repeat match goal with H : 0 <= c_K _ _ |- _ => clear H | H : c_K _ _ < _ |- _ => clear H end;
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext];
  icx_cbn;
  match goal with H : RNG _ _ _ _ |- _ => unfold RNG in H; icx_cbn; cbv [N_CODES N_LENS] in H; destr_conj H end;
  match goal with H : PROG _ _ |- _ => unfold PROG, Wm in H; icx_cbn; dand H as (PR1 & PR2 & PR3) end;
  zkeysb; unfold L_LCHECK, L_LDT, L_UW_ARGS, L_LNOWIN, L_LRC, L_LEAVE, L_UW, L_UW_RET, L_UW_CALL, L_RET, L_MEM, T_ZW, L_ZB in *;
  cbv [A_ZCALLOC A_ZCFREE A_ADLER32] in *; pose proof two64_eq as TW64;
  pose proof (proj1 (wsz_facts cx)) as Hws0; cbv [WIN_SIZE] in Hws0;
  unfold fp_call, fp_loop in HP0; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE] in HP0; cbn [app] in HP0.

Lemma leave_dt_s : forall Rb l M st rv lf cf,
  sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -224 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kA0 = c_u cx -> zget_l Rb l kA1 = 0 -> zget_l Rb l kRA = c_osz cx - t_cout st ->
  zget_l Rb l kS1 = rv -> zget_l Rb l kS2 = c_n cx - t_cin st -> zget_l Rb l kS3 = c_ob cx + t_cout st ->
  zget_l Rb l kS4 = t_out st - (c_osz cx - t_cout st) -> zget_l Rb l kS5 = c_n cx - c_cin0 cx ->
  zget_l Rb l kS7 = t_hold st -> zget_l Rb l kS8 = t_bits st -> zget_l Rb l kS9 = t_out st ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS11 = c_q cx + t_cin st ->
  hideP (t_out st <> c_osz cx - t_cout st -> zget_l Rb l kS6 = c_osz cx - t_cout st) ->
  s_std cx fin M -> st_at R_segs cx st M -> strm_at R_segs cx st M ->
  mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
  mpostL R_segs M0 M (fp_call cx) ->
  realizes R_segs (zcfg R_segs L_LDT (zupd Rb l) M MD) T.
Proof.
  intros Rb l M st rv lf cf SI Lsp Lgp Ltp La0 La1 Lra Ls0 Ls1 Ls2 Ls3 Ls4 Ls6 Ls7 Ls8 Ls9 Ls10 H5 STD SAT STRM Hlens Hcodes HP0.
  open_std STD. open_leave CX SI st HP0.
  fp_call_frame HP0.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn.
  dand CST' as (C64 & C88 & Cp0 & Cp16 & Cp48 & Cp56 & Cp60 & Cp72 & Cp7144).
  pose proof SAT as SAT'. destruct SAT' as [Hmode SREST']. unfold st_rest in SREST'. icx_cbn. dand SREST' as (Hlast & _).
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  tstep1 Rfd.
  clear Hlast.
  zstep Rfd.
  zstep Rfd. zgen.
  zstep Rfd. zgen.
  zstep Rfd. zgen.
  zstep Rfd.
  zstep Rfd. zgen.
  zstep Rfd. zgen.
  zstep Rfd. zgen.
  zstep Rfd. zgen.
  zstep Rfd. zgen.
  zstep Rfd.
  zstep Rfd. zgen.
  zstep Rfd. zgen.
  zstep Rfd. zgen.
  zstep Rfd. zgen.
  zstep Rfd. zgen.
  zstep Rfd. zgen.
  tstep1 Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (CALL : forall RJ,
    zget RJ kSP = c_u cx + -224 -> zget RJ kGP = c_K cx kGP -> zget RJ kTP = c_K cx kTP ->
    zget RJ kA0 = c_u cx -> zget RJ kRA = c_osz cx - cout -> zget RJ kS1 = rv -> zget RJ kS2 = c_n cx - cin ->
    zget RJ kS4 = out - (c_osz cx - cout) -> zget RJ kS5 = c_n cx - c_cin0 cx ->
    zget RJ kS7 = hold -> zget RJ kS8 = bits -> zget RJ kS9 = out -> zget RJ kS0 = c_p cx -> zget RJ kS11 = c_q cx + cin ->
    hideP (c_w cx = 0 -> c_cout0 cx < cout /\ mode <= DONE /\ zget RJ kS6 = c_osz cx - cout) ->
    realizes R_segs (zcfg R_segs L_UW_ARGS (zupd RJ []) Mc MD) T) end.
  { intros RJ. intros. zimps. zkeys. unfold L_UW_ARGS.
    match goal with H : hideP _ |- _ => rename H into WHY end.
    pose proof STRM as STRM'. unfold strm_at in STRM'. icx_cbn. dand STRM' as (_ & _ & S32 & _).
    tstep1 Rfd.
    clear S32.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof SAT as SAT'. destruct SAT' as [Hmode' SREST']. unfold st_rest in SREST'. icx_cbn. destr_conj SREST'. clear SAT.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      destruct (mem_wr_arr_exists_R Mx (c_ob cx) (c_osz cx) Wob ltac:(lia) ltac:(lia) ltac:(lia)) as (fo & HOB & Hfo) end.
    pose proof WIN_ as WIN'. unfold WIN in WIN'. icx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?lc) ?Mx _) _ =>
      eapply (uw_entry_s MEMCPY R' lc Mx MD T (c_u cx) (c_p cx) (c_ob cx) (c_osz cx) (c_w cx) whave wnext cout (out - (c_osz cx - cout))
                (c_u cx + -224) L_UW_RET (c_p cx) rv (c_n cx - cin) (c_osz cx - cout) (out - (c_osz cx - cout)) (c_zc cx) fo Hh) end;
      try zreg.
    all: lazymatch goal with
         | |- forall R' M', c_w cx = 0 -> _ => idtac
         | |- forall R' M' whave' wnext', _ => idtac
         | |- _ => first [ reflexivity | assumption | exact Cp60
                         | exact (proj1 AL) | exact (proj1 (proj2 AL)) | exact (proj2 (proj2 AL))
                         | exact (sep_p_ob _ _ SEP) | exact (sep_w_p _ _ SEP) | exact (sep_w_ob _ _ SEP)
                         | exact (proj2 WIN') | exact (proj1 HK)
                         | eapply mem_wr_sub; [exact Wstk | klia | klia]
                         | intros Hw; pose proof Ww as X; rewrite ((proj2 (proj2 (wsz_facts cx))) Hw) in X; exact X
                         | unfold ZSEP; unfold FRA in OBLOW; klia | cbv [L_UW_RET]; klia
                         | intros i Hi; apply Hfo
                         | match goal with |- ?G => idtac "UWSIDE" G end ]
         end.
    -
      intros R' M' Hw0. unfold hideP in WHY. dand (WHY Hw0) as (WHY1 & WHY2 & WHY5). intros. zimps. zkeys.
      match goal with HP : mpostL R_segs _ M' _ |- _ => zreattachL HP end.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
        eapply (HKW R9 Mx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  rv lf cf Hw0 SI WHY1 WHY2) end;
        first [ zreg | icx_cbn; zreg | icx_cbn; zkept | assumption
              | match goal with H : mem_u64 R_segs ?My ?a ?v |- mem_u64 R_segs ?My ?a' _ =>
                  replace a' with a by lia_std; first [exact H | cbv [L_UW_RET]; exact H] end
              | close_std | unfold st_at, st_rest; icx_cbn; split_conj; assumption | exact HAG
              | match goal with |- ?G => idtac "KWSIDE" G end ].
    -
      intros R' M' whave' wnext' Hw. intros. zimps. zkeys.
      rewrite ((proj2 (proj2 (wsz_facts cx))) Hw) in *. cbv [WIN_SIZE] in *.
      clear Cp60 Cp72.
      clear CST.
      match goal with HP : mpostL R_segs _ M' _ |- _ => unfold uw_fp in HP; cbv [WIN_SIZE] in HP; zreattachL HP end.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
        eapply (leave_uwret_s cx fin MD T M0 CX Hh OBLOW HKRL HKRX R9 [] Mx
                  (set_win (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) whave' wnext')
                  rv 0 lf cf) end;
        first [ zreg | icx_cbn; zreg | icx_cbn; zkept | left; reflexivity | assumption
              | apply sinv_set_win; [exact SI | exact Hw | assumption ..]
              | unfold s_std, i_cst; rewrite ((proj2 (proj2 (wsz_facts cx))) Hw); cbv [WIN_SIZE]; icx_cbn; split_conj; assumption
              | unfold st_at, st_rest, set_win; icx_cbn; split_conj; assumption
              | unfold strm_at, set_win; icx_cbn; match goal with H : strm_at _ _ _ _ |- _ => unfold strm_at in H; icx_cbn; exact H end
              | unfold fp_call; rewrite ((proj2 (proj2 (wsz_facts cx))) Hw); exact HAG
              | match goal with |- ?G => idtac "UWRETSIDE" G end ]. }
  Local Ltac to_rc SI HAG :=
    lazymatch type of SI with sinv _ ?st _ _ =>
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (leave_rc_s cx fin MD T M0 CX Hh OBLOW HKRL R9 [] Mx st _ _ _ SI) end end;
    first [ zreg | icx_cbn; zreg | assumption | close_std | exact HAG
          | unfold strm_at; icx_cbn; match goal with H : strm_at _ _ _ _ |- _ => unfold strm_at in H; icx_cbn; exact H end
          | match goal with |- ?G => idtac "RCSIDE" G end ].
  Local Ltac to_call CALL :=
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 _ _) _ => eapply (CALL R9) end;
    first [ zreg | icx_cbn; zreg | assumption | lazymatch goal with |- hideP _ => idtac end ].
  destruct (Z.eq_dec (c_w cx) 0) as [Hw0 | Hw1].
  -
    pose proof ((proj1 (proj2 (wsz_facts cx))) Hw0) as Hz.
    zbr Rfd true.
    destruct (Z.eq_dec out (c_osz cx - cout)) as [Ec|Ec].
    + zbr Rfd true.
      to_rc SI HAG.
    + zbr Rfd false.
      zstep Rfd. zstep Rfd. zlit.
      destruct (Z_lt_dec 16208 mode) as [Hm|Hm].
      * zbr Rfd true.
        to_rc SI HAG.
      * zbr Rfd false.
        zstep Rfd.
        zbr Rfd true.
        unfold hideP in H5. specialize (H5 Ec).
        to_call CALL. unfold hideP. intros _. cbv [DONE]. split; [| split; [| zreg]]; destruct PR3 as [PR3 | [PR3 _]]; lia.
  -
    pose proof ((proj2 (proj2 (wsz_facts cx))) Hw1) as Hz. cbv [WIN_SIZE] in Hz.
    zbr Rfd false.
    to_call CALL. unfold hideP. intros E. exfalso. exact (Hw1 E).
Qed.

Theorem leave_s : KLEAVE cx fin MD T M0.
Proof.
  intros R M st rv lf cf SI RE STD SAT SOUT Hlens Hcodes HPl.
  pose proof (fp_call_widen cx M0 M HPl) as HP0. clear HPl.
  open_std STD. unfold s_regs_leave in RE. destr_conj RE. zgetl_nil. open_leave CX SI st HP0.
  fp_call_frame HP0.
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q104 & Q96 & _ & _ & Q56 & _).
  pose proof SOUT as Q80. unfold s_out in Q80. icx_cbn.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & Cp16 & _).
  pose proof (mem_u32_lo8 _ _ _ Cp16) as Cp16b. cbn [Z.modulo Z.pos_div_eucl] in Cp16b. clear Cp16.
  destruct (mem_wr_u64_exists_R M (c_u cx + 16) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (ti & Hti & Rti).
  destruct (mem_wr_u64_exists_R M (c_u cx + 40) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (to & Hto & Rto).
  destruct (mem_wr_u64_exists_R M (c_p cx + 48) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (tt & Htt & Rtt).
  zstep Rfd.
  tstep1 Rfd. zgen.
  zstep Rfd.
  tstep1 Rfd.
  zsetreg (out - (c_osz cx - cout)) ltac:(first [lia | rewrite swrap32_small by lia; lia]).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zstep Rfd. zgen.
  zstep Rfd. zgen.
  zstep Rfd. zstep Rfd. zext32.
  zstep Rfd. zgen.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd. zlit.
  zstep Rfd. zgen.
  zstep Rfd. zlit.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    assert (STRM : strm_at R_segs cx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) Mx)
      by (unfold strm_at; icx_cbn; split_conj; assumption) end.
  repeat match goal with H : mem_u64 R_segs ?Mx (c_u cx) _ |- _ => clear H
                        | H : mem_u32 R_segs ?Mx (c_u cx + 8) _ |- _ => clear H
                        | H : mem_u64 R_segs ?Mx (c_u cx + 16) _ |- _ => clear H
                        | H : mem_u64 R_segs ?Mx (c_u cx + 24) _ |- _ => clear H
                        | H : mem_u32 R_segs ?Mx (c_u cx + 32) _ |- _ => clear H
                        | H : mem_u64 R_segs ?Mx (c_u cx + 40) _ |- _ => clear H
                        | H : mem_u64 R_segs ?Mx (c_p cx + 48) _ |- _ => clear H
                        | H : mem_u64 R_segs ?Mx (c_p cx + 96) _ |- _ => clear H end.
  try clear Hti; try clear Hto; try clear Htt. clear Q56 Q80 Cp16b.
  zbr Rfd false.
  Local Ltac to_dt SI HAG :=
    lazymatch type of SI with sinv _ ?st _ _ =>
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (leave_dt_s R9 [] Mx st _ _ _ SI) end end;
    first [ zreg | icx_cbn; zreg | icx_cbn; zkept | assumption | close_std | exact HAG
          | unfold hideP; icx_cbn; intros X; first [ exfalso; apply X; assumption | zreg | zkept ]
          | match goal with |- ?G => idtac "DTSIDE" G end ].
  destruct (Z.eq_dec out (c_osz cx - cout)) as [Ecout|Ecout].
  -
    zbr Rfd true.
    to_dt SI HAG.
  -
    zbr Rfd false.
    assert (Hf0 : flags = 0).
    { dand MODE_ as (_ & Mf & _). icx_cbn.
      assert (Hn1 : flags <> -1) by (intros E; destruct (Mf E) as [_ Hc]; clear Mf HKRL HKRX HKW; lia).
      clear Mf HKRL HKRX HKW. lia. }
    pose proof SAT as SAT'. destruct SAT' as [_ SREST']. unfold st_rest in SREST'. icx_cbn. dand SREST' as (_ & Cfl & _).
    rewrite Hf0 in Cfl.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      destruct (mem_wr_u64_exists_R Mx (c_p cx + 40) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (ck & Hck & Rck) end.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd. zsetreg (c_ob cx + cout - (out - (c_osz cx - cout))) ltac:(lia).
    zstep Rfd.
    zbr Rfd true.
    clear Cfl.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      destruct (mem_wr_arr_exists_R Mx (c_ob cx) (c_osz cx) Wob ltac:(lia) ltac:(lia) ltac:(lia)) as (fo & HOB & Hfo) end.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      pose proof (mem_arr_sub R_segs 1 Mx (c_ob cx) (c_osz cx) fo (cout - (out - (c_osz cx - cout))) (out - (c_osz cx - cout)) HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc end.
    replace (c_ob cx + 1 * (cout - (out - (c_osz cx - cout)))) with (c_ob cx + cout - (out - (c_osz cx - cout))) in Hsrc by lia.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?lc) ?Mx _) _ =>
      eapply (ADLER R' lc Mx MD T ck (c_ob cx + cout - (out - (c_osz cx - cout))) (out - (c_osz cx - cout)) (out - (c_osz cx - cout)) (c_u cx + -224) _
                (fun j => fo (cout - (out - (c_osz cx - cout)) + j)) Hh) end;
      try zreg.
    all: lazymatch goal with
         | |- forall M' : mem, _ => idtac
         | |- _ => cbv [FR_AD]; first [ reflexivity | exact Hsrc | assumption | rewrite Z.mod_small by lia; reflexivity
                         | eapply mem_wr_sub; [exact Wstk | lia | lia] | intros i Hi; apply Hfo; lia
                         | unfold FRA in OBLOW; lia | lia
                         | match goal with |- ?G => idtac "ADSIDE" G end ]
         end.
    intros M' R' HP. intros. zimps. zkeys.
    clear Hck Hsrc. match goal with H : mem_arr 1 _ _ (c_ob cx) (c_osz cx) fo |- _ => clear H end.
    apply mpost_mpostL1 in HP. cbv [FR_AD] in HP. zreattachL HP.
    pose proof STRM as STRM'. unfold strm_at in STRM'. icx_cbn. dand STRM' as (_ & _ & _ & _ & _ & S88).
    zstep Rfd.
    tstep1 Rfd.
    clear S88.
    tstep1 Rfd.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    to_dt SI HAG.
Qed.
End Leave.
End FXG.
End S_Leave.

Module S_Inflate.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.SBase OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_Entry.S_Loop S_Ret OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_Entry S_Uw S_LeaveA S_Leave.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Section Inflate.
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet).
Hypothesis CX : ctx_ok ROMHI_S cx.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < c_n cx -> 0 <= fin i < 256.
Hypothesis OBLOW : c_ob cx + c_osz cx <= c_u cx - FRA.
Hypothesis MEMCPY : memcpy_spec_s.
Hypothesis ADLER : adler32_spec_s.
Hypothesis A_HEAD : arm_stmt L_HEAD HEAD.
Hypothesis A_DICTID : arm_stmt L_DICTID DICTID.
Hypothesis A_DICT : arm_stmt L_DICT DICT.
Hypothesis A_TYPE : arm_stmt L_TYPE TYPE.
Hypothesis A_TYPEDO : arm_stmt L_TYPEDO TYPEDO.
Hypothesis A_STORED : arm_stmt L_STORED STORED.
Hypothesis A_COPY_ : arm_stmt L_COPY_ COPY_.
Hypothesis A_COPY : arm_stmt L_COPY COPY.
Hypothesis A_TABLE : arm_stmt L_TABLE TABLE.
Hypothesis A_LENLENS : arm_stmt L_LENLENS LENLENS.
Hypothesis A_CODELENS : arm_stmt L_CODELENS CODELENS.
Hypothesis A_LEN_ : arm_stmt L_LEN_ LEN_.
Hypothesis A_LEN : arm_stmt L_LEN LEN.
Hypothesis A_LENEXT : arm_stmt L_LENEXT LENEXT.
Hypothesis A_DIST : arm_stmt L_DIST DIST.
Hypothesis A_DISTEXT : arm_stmt L_DISTEXT DISTEXT.
Hypothesis A_MATCH : arm_stmt L_MATCH MATCH.
Hypothesis A_LIT : arm_stmt L_LIT LIT.
Hypothesis A_CHECK : arm_stmt_ob L_CHECK CHECK.
Hypothesis A_LENGTH : arm_stmt L_LENGTH LENGTH.

Lemma kret_of_krx : forall M0, KRX cx fin MD T M0 -> KRET cx fin MD T M0.
Proof.
  intros M0 KX R M rc m Hrc RE STD Hm Hr HP0.
  pose proof STD as STD'. dand STD' as (_ & _ & _ & _ & _ & FRM & _).
  eapply (ret_s cx R [] M MD T rc CX Hh RE FRM).
  intros R9 HB. eapply (KX R9 M rc m Hrc HB STD Hm Hr). apply fp_call_widen. exact HP0.
Qed.

Theorem inflate_s : forall Rb l M st lf cf,
  ainv cx st lf cf -> c_cin0 cx = t_cin st -> c_cout0 cx = t_cout st -> c_W0 cx = Wm cx st ->
  s_regs_entry cx Rb l -> e_mem cx fin st lf cf M ->
  KRL cx fin MD T M -> KRX cx fin MD T M -> KW cx fin MD T M ->
  realizes R_segs (zcfg R_segs L_INFLATE (zupd Rb l) M MD) T.
Proof.
  intros Rb l M st lf cf AI H1 H2 H3 RE EM HKRL HKRX HKW.
  eapply (entry_s cx fin MD T Rb l M st lf cf CX Hh Hfin AI H1 H2 H3 RE EM).
  pose proof (leave_s cx fin MD T M CX Hh OBLOW MEMCPY ADLER HKRL HKRX HKW) as HKL.
  pose proof (kret_of_krx M HKRX) as HKR.
  pose proof (kall_s cx fin MD T M CX Hh Hfin HKL HKR A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY
                A_TABLE A_LENLENS A_CODELENS A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT OBLOW A_CHECK A_LENGTH
                (meas cx (st_load cx st) + 1)) as KA.
  open_K KA. exact KD00.
Qed.
End Inflate.
End FXG.
End S_Inflate.

Module S_U2B.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_EXIT : Z := 85680.    (* 0x14e4c: uncompress2_z's exit from the inflate loop *)
Definition T_ZE1 : Z := 94692.     (* 0x17168: inflateEnd, jalr zfree for the window *)
Definition T_ZE2 : Z := 94716.     (* 0x17180: inflateEnd, jalr zfree for the state *)
Definition RA2 : Z := 85732.       (* 0x14e80: uncompress2_z after jal inflateEnd *)

End FXG.
Ltac zgen :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => let x' := fresh "gv" in set (x' := e); clearbody x'
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Theorem u2_exit_s : forall Rb l M MD T (u p w rc len left m zc : Z) (gp tp s5 s6 s7 s8 s9 s10 s11 : Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u -> zget_l Rb l kA0 = rc -> zget_l Rb l kS0 = u + 176 -> zget_l Rb l kS1 = u + 168 ->
  zget_l Rb l kS3 = len -> zget_l Rb l kS4 = left -> zget_l Rb l kS5 = s5 ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp ->
  zget_l Rb l kS6 = s6 -> zget_l Rb l kS7 = s7 -> zget_l Rb l kS8 = s8 -> zget_l Rb l kS9 = s9 ->
  zget_l Rb l kS10 = s10 -> zget_l Rb l kS11 = s11 ->
  zc + FRA <= u -> DATA_LO + DATA_LEN <= zc -> u + 208 <= 140737488355328 -> 0 < p -> p + STATE_SIZE <= zc ->
  0 <= w -> w + WIN_SIZE <= zc -> reach m ->
  mem_wr R_segs M (u + -1024) 1232 -> mem_wr R_segs M p STATE_SIZE ->
  mem_u64 R_segs M (u + 56) p -> mem_u64 R_segs M (u + 64) A_ZCALLOC -> mem_u64 R_segs M (u + 72) A_ZCFREE ->
  mem_u64 R_segs M (u + 80) 0 -> mem_u64 R_segs M p u -> mem_u32 R_segs M (p + 8) m -> mem_u64 R_segs M (p + 88) w ->
  (forall R' M', w = 0 ->
     zget R' kA4 = A_ZCFREE -> zget R' kA1 = p -> zget R' kA0 = 0 -> zget R' kS0 = u -> zget R' kSP = u + -16 ->
     zget R' kGP = gp -> zget R' kTP = tp -> zget R' kS5 = s5 ->
     zget R' kS6 = s6 -> zget R' kS7 = s7 -> zget R' kS8 = s8 -> zget R' kS9 = s9 -> zget R' kS10 = s10 -> zget R' kS11 = s11 ->
     mem_u64 R_segs M' (u + -8) RA2 -> mem_u64 R_segs M' (u + 56) p -> mem_u64 R_segs M' (u + 72) A_ZCFREE -> mem_u64 R_segs M' (u + 80) 0 ->
     mpostL R_segs M M' [(u + -16, 16); (u + 168, 8); (u + 176, 8)] ->
     realizes R_segs (zcfg R_segs T_ZE2 (zupd R' []) M' MD) T) ->
  (forall R' M', w <> 0 ->
     zget R' kA4 = A_ZCFREE -> zget R' kA1 = w -> zget R' kA0 = 0 -> zget R' kS0 = u -> zget R' kSP = u + -16 ->
     zget R' kGP = gp -> zget R' kTP = tp -> zget R' kS5 = s5 ->
     zget R' kS6 = s6 -> zget R' kS7 = s7 -> zget R' kS8 = s8 -> zget R' kS9 = s9 -> zget R' kS10 = s10 -> zget R' kS11 = s11 ->
     mem_u64 R_segs M' (u + -8) RA2 -> mem_u64 R_segs M' (u + 56) p -> mem_u64 R_segs M' (u + 72) A_ZCFREE -> mem_u64 R_segs M' (u + 80) 0 ->
     mpostL R_segs M M' [(u + -16, 16); (u + 168, 8); (u + 176, 8)] ->
     realizes R_segs (zcfg R_segs T_ZE1 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_EXIT (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u p w rc len left m zc gp tp s5 s6 s7 s8 s9 s10 s11
         Hh Lsp La0 Ls0 Ls1 Ls3 Ls4 Ls5 Lgp Ltp Ls6 Ls7 Ls8 Ls9 Ls10 Ls11
         Hu0 Hzimg Hu1 Hp0 Hp1 Hw0 Hw1 Hm Wstk Wp C64 C72 C80 C88 Cp0 Cp8 Cp72 KNW KW.
  zkeysb. unfold L_EXIT, T_ZE1, T_ZE2, RA2 in *. cbv [STATE_SIZE FRA WIN_SIZE A_ZCALLOC A_ZCFREE BUF DATA_LO DATA_LEN] in *.
  pose proof two64_eq as TW64. pose proof (reach_bounds' := Hm). unfold reach in reach_bounds'. cbv [HEAD DICTID MEM] in reach_bounds'.
  assert (Hmb : 16180 <= m <= 16210) by lia_std. clear reach_bounds'.
  pose proof (mpostL_stable R_segs M [(u + -16, 16); (u + 168, 8); (u + 176, 8)] ltac:(ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL R_segs M X [(u + -16, 16); (u + 168, 8); (u + 176, 8)]) M) by (apply mpostL_refl).
  (* the current avail_in, *sourceLen, avail_out and *destLen *)
  destruct (mem_wr_u32_exists_R M (u + 8) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (vai & Hai & Rai).
  destruct (mem_wr_u64_exists_R M (u + 168) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (vsl & Hsl & Rsl).
  destruct (mem_wr_u32_exists_R M (u + 32) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (vao & Hao & Rao).
  destruct (mem_wr_u64_exists_R M (u + 176) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (vdl & Hdl & Rdl).
  zstep Rfd.                          (* 14e4c lwu a1,8(sp) *)
  zstep Rfd.                          (* 14e50 ld a2,0(s1) *)
  zstep Rfd.                          (* 14e54 lwu a3,32(sp) *)
  zstep Rfd. zgen.                    (* 14e58 add s3,s3,a1 *)
  zstep Rfd. zgen.                    (* 14e5c sub a1,a2,s3 *)
  zstep Rfd.                          (* 14e60 sd a1,0(s1) *)
  zstep Rfd.                          (* 14e64 ld a1,0(s0) *)
  zstep Rfd. zgen.                    (* 14e68 add a3,s4,a3 *)
  zstep Rfd. zgen.                    (* 14e6c sub a1,a1,a3 *)
  zstep Rfd.                          (* 14e70 sd a1,0(s0) *)
  zstep Rfd.                          (* 14e74 mv s0,a0 *)
  zstep Rfd.                          (* 14e78 mv a0,sp *)
  zstep Rfd.                          (* 14e7c jal inflateEnd *)
  (* inflateEnd (0x17100): the state checks, then the frame *)
  zstep Rfd.                          (* mv a2,a0 *)
  zstep Rfd.                          (* li a0,-2 *)
  zbr Rfd false.                      (* beqz a2 *)
  zstep Rfd. zbr Rfd false.           (* ld a1,64(a2); beqz a1 *)
  zstep Rfd. zbr Rfd false.           (* ld a4,72(a2); beqz a4 *)
  zstep Rfd. zbr Rfd false.           (* ld a1,56(a2); beqz a1 *)
  zstep Rfd. zbr Rfd true.            (* ld a3,0(a1); beq a3,a2 *)
  tstep1 Rfd.                         (* lw a3,8(a1) *)
  zstep Rfd. zstep Rfd. zlit.         (* lui a5; addi a5,a5,204 *)
  tstep1 Rfd.                         (* addw a3,a3,a5 *)
  zstep Rfd.                          (* li a5,31 *)
  zbr Rfd false.                      (* bltu a5,a3 *)
  zstep Rfd.                          (* addi sp,sp,-16 *)
  tstep1 Rfd.                         (* sd ra,8(sp) *)
  tstep1 Rfd.                         (* sd s0,0(sp) *)
  zstep Rfd.                          (* ld a3,88(a1) *)
  destruct (Z.eq_dec w 0) as [Wz | Wnz].
  - revert Cp72. subst w. intros Cp72.
    zbr Rfd true.                     (* beqz a3: no window *)
    zstep Rfd.                        (* ld a0,80(a2) *)
    zstep Rfd.                        (* mv s0,a2 *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => apply (KNW R' Mx eq_refl) end; try zreg; try assumption.
  - zbr Rfd false.                    (* beqz a3 *)
    zstep Rfd.                        (* ld a0,80(a2) *)
    zstep Rfd.                        (* mv s0,a2 *)
    zstep Rfd.                        (* mv a1,a3 *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => apply (KW R' Mx Wnz) end; try zreg; try assumption.
Qed.
End FXG.
End S_U2B.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require Import SBase. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_Entry. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_Entry.S_Loop. Import S_Ret. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require Import S_Entry. Import S_Uw. Import S_LeaveA. Import S_Leave. Import S_Inflate. Import S_U2B.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

(* 1.4: uncompress2_z's exit is new code at 1.4: *sourceLen -= len + avail_in; *destLen -= left + avail_out;
   err kept in s0 over inflateEnd (no dest == buf case, no *destLen = total_out). inflateEnd is 1.3.1's code. *)
Definition L_TAIL : Z := 85668.    (* 1.4: 0x14e40, lw a0,32(sp) once an inflate call returned Z_OK *)
Definition L_C1 : Z := 85584.      (* 1.4: 0x14dec, call site 1 (mv a0,sp) *)
Definition L_C2 : Z := 85652.      (* 1.4: 0x14e30, call site 2 (mv a0,sp) *)
Definition RA_C1 : Z := 85596.
Definition RA_C2 : Z := 85664.
Definition pc_site (site : bool) : Z := if site then L_C1 else L_C2.
Definition ra_site (site : bool) : Z := if site then RA_C1 else RA_C2.

Section U2.
Variables (u p q n gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z) (MD : Model) (T : TSet) (Mza : mem).
Variable zc : Z.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < n -> 0 <= fin i < 256.
Hypothesis Hu0 : zc + FRA <= u. Hypothesis Hzimg : DATA_LO + DATA_LEN <= zc. Hypothesis Hu1 : u + 208 <= 140737488355328. Hypothesis Hua : u mod 16 = 0.
Hypothesis Hp0 : 0 < p. Hypothesis Hp1 : p + STATE_SIZE <= zc. Hypothesis Hpa : p mod 16 = 0.
Hypothesis Hq1 : 1 <= q. Hypothesis Hn0 : 0 <= n. Hypothesis Hn1 : n < 67108864. Hypothesis Hqn : q + n <= zc.
Hypothesis Spq : ZSEP (p + STATE_SIZE <= q \/ q + n <= p).
Hypothesis Spob : ZSEP (p + STATE_SIZE <= BUF \/ BUF + 262144 <= p).
Hypothesis Sobq : ZSEP (BUF + 262144 <= q \/ q + n <= BUF).
Hypothesis Sprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p).
Hypothesis Rgp : 0 <= gp < two64. Hypothesis Rtp : 0 <= tp < two64.
Hypothesis Rs5 : 0 <= s5 < two64. Hypothesis Rs6 : 0 <= s6 < two64. Hypothesis Rs7 : 0 <= s7 < two64. Hypothesis Rs8 : 0 <= s8 < two64.
Hypothesis Rs9 : 0 <= s9 < two64. Hypothesis Rs10 : 0 <= s10 < two64. Hypothesis Rs11 : 0 <= s11 < two64.
Hypothesis MEMCPY : memcpy_spec_s.
Hypothesis ADLER : adler32_spec_s.
Hypothesis A_HEAD : arm_stmt L_HEAD HEAD.
Hypothesis A_DICTID : arm_stmt L_DICTID DICTID.
Hypothesis A_DICT : arm_stmt L_DICT DICT.
Hypothesis A_TYPE : arm_stmt L_TYPE TYPE.
Hypothesis A_TYPEDO : arm_stmt L_TYPEDO TYPEDO.
Hypothesis A_STORED : arm_stmt L_STORED STORED.
Hypothesis A_COPY_ : arm_stmt L_COPY_ COPY_.
Hypothesis A_COPY : arm_stmt L_COPY COPY.
Hypothesis A_TABLE : arm_stmt L_TABLE TABLE.
Hypothesis A_LENLENS : arm_stmt L_LENLENS LENLENS.
Hypothesis A_CODELENS : arm_stmt L_CODELENS CODELENS.
Hypothesis A_LEN_ : arm_stmt L_LEN_ LEN_.
Hypothesis A_LEN : arm_stmt L_LEN LEN.
Hypothesis A_LENEXT : arm_stmt L_LENEXT LENEXT.
Hypothesis A_DIST : arm_stmt L_DIST DIST.
Hypothesis A_DISTEXT : arm_stmt L_DISTEXT DISTEXT.
Hypothesis A_MATCH : arm_stmt L_MATCH MATCH.
Hypothesis A_LIT : arm_stmt L_LIT LIT.
Hypothesis A_CHECK : arm_stmt_ob L_CHECK CHECK.
Hypothesis A_LENGTH : arm_stmt L_LENGTH LENGTH.

Definition Kra (ra : Z) (k : positive) : Z :=
  if (k =? kRA)%positive then ra else if (k =? kSP)%positive then u
  else if (k =? kGP)%positive then gp else if (k =? kTP)%positive then tp
  else if (k =? kS0)%positive then u + 176 else if (k =? kS1)%positive then u + 168
  else if (k =? kS2)%positive then 4294967295 else if (k =? kS3)%positive then 0 else if (k =? kS4)%positive then 0
  else if (k =? kS5)%positive then s5
  else if (k =? kS6)%positive then s6 else if (k =? kS7)%positive then s7 else if (k =? kS8)%positive then s8
  else if (k =? kS9)%positive then s9 else if (k =? kS10)%positive then s10 else if (k =? kS11)%positive then s11
  else 0.
Definition cxc (w cin cout W0 ra : Z) : ictx := ICX u p q n BUF 262144 w cin cout W0 (Kra ra) zc.
Definition wok (w : Z) : Prop :=
  0 <= w /\ w + WIN_SIZE <= zc /\ w mod 16 = 0 /\
  ZSEP (w = 0 \/ (p + STATE_SIZE <= w \/ w + WIN_SIZE <= p)) /\ ZSEP (w = 0 \/ (w + WIN_SIZE <= q \/ q + n <= w)) /\
  ZSEP (w = 0 \/ (w + WIN_SIZE <= BUF \/ BUF + 262144 <= w)) /\ ZSEP (w = 0 \/ (w + WIN_SIZE <= ROM_LO_ALL \/ ROMHI_S <= w)).

Lemma ctx_ok_cxc : forall w cin cout W0 ra,
  wok w -> 0 <= cin <= n -> 0 <= cout <= 262144 -> (ra = RA_C1 \/ ra = RA_C2) ->
  ctx_ok ROMHI_S (cxc w cin cout W0 ra).
Proof.
  intros w cin cout W0 ra (W1 & W2 & W3 & W4 & W5 & W6 & W7) Hcin Hcout Hra.
  unfold ZSEP in *. pose proof two64_eq as TW64.
  unfold ctx_ok, ctx_lin, ctx_al, ctx_sep, cxc, Kra; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S BUF DATA_LO DATA_LEN] in *.
  cbv [kRA kSP kGP kTP kS0 kS1 kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11]. cbn [Pos.eqb].
  split; [| split]; split_conj; try assumption; try lia;
    unfold RA_C1, RA_C2 in Hra; destruct Hra as [-> | ->]; first [reflexivity | lia | lia_std].
Qed.

Definition u2regs (R : tree Z) : Prop :=
  zget R kSP = u /\ zget R kS0 = u + 176 /\ zget R kS1 = u + 168 /\ zget R kS2 = 4294967295 /\ zget R kS3 = 0 /\ zget R kS4 = 0 /\
  zget R kS5 = s5 /\ zget R kGP = gp /\ zget R kTP = tp /\
  zget R kS6 = s6 /\ zget R kS7 = s7 /\ zget R kS8 = s8 /\ zget R kS9 = s9 /\ zget R kS10 = s10 /\ zget R kS11 = s11.

Definition fp_u2 (w : Z) : list (Z * Z) :=
  [(u + -1024, 1136); (u + 168, 8); (u + 176, 8); (p, STATE_SIZE); (BUF, 262144); (w, if w =? 0 then 0 else WIN_SIZE)].

Definition Wv (st : ist) : Z := 8 * (n - t_cin st) + t_bits st + (262144 - t_cout st).
Definition M2v (st : ist) : Z := Wv st * 134217728 + (n - t_cin st).

Variable wph : Z.
Hypothesis Hwph : wok wph.

Definition KZE2 : Prop := forall (R : tree Z) (M : mem),
  zget R kA4 = A_ZCFREE -> zget R kA1 = p -> zget R kA0 = 0 -> zget R kS0 = u -> zget R kSP = u + -16 ->
  zget R kGP = gp -> zget R kTP = tp -> zget R kS5 = s5 ->
  zget R kS6 = s6 -> zget R kS7 = s7 -> zget R kS8 = s8 -> zget R kS9 = s9 -> zget R kS10 = s10 -> zget R kS11 = s11 ->
  mem_u64 R_segs M (u + -8) RA2 -> mem_u64 R_segs M (u + 56) p -> mem_u64 R_segs M (u + 72) A_ZCFREE -> mem_u64 R_segs M (u + 80) 0 ->
  wph = 0 -> mpostL R_segs Mza M (fp_u2 wph) ->
  realizes R_segs (zcfg R_segs T_ZE2 (zupd R []) M MD) T.
Definition KZE1 : Prop := forall (R : tree Z) (M : mem),
  zget R kA4 = A_ZCFREE -> zget R kA1 = wph -> zget R kA0 = 0 -> zget R kS0 = u -> zget R kSP = u + -16 ->
  zget R kGP = gp -> zget R kTP = tp -> zget R kS5 = s5 ->
  zget R kS6 = s6 -> zget R kS7 = s7 -> zget R kS8 = s8 -> zget R kS9 = s9 -> zget R kS10 = s10 -> zget R kS11 = s11 ->
  mem_u64 R_segs M (u + -8) RA2 -> mem_u64 R_segs M (u + 56) p -> mem_u64 R_segs M (u + 72) A_ZCFREE -> mem_u64 R_segs M (u + 80) 0 ->
  wph <> 0 -> mpostL R_segs Mza M (fp_u2 wph) ->
  realizes R_segs (zcfg R_segs T_ZE1 (zupd R []) M MD) T.
Definition KZW : Prop := forall (R : tree Z) (M : mem) (cin0 cout0 W0 ra : Z) (st : ist) (rv : Z) (lf cf : Z -> Z),
  let cx := cxc 0 cin0 cout0 W0 ra in
  (ra = RA_C1 \/ ra = RA_C2) -> 0 <= cin0 <= n -> 0 <= cout0 <= 262144 ->
  sinv cx st lf cf -> cout0 < t_cout st -> t_mode st <= DONE ->
  zget R kA3 = A_ZCALLOC -> zget R kA0 = 0 -> zget R kA1 = WIN_SIZE -> zget R kA2 = 1 ->
  zget R kS0 = BUF + t_cout st -> zget R kS1 = t_out st - (262144 - t_cout st) -> zget R kS2 = 1 -> zget R kS3 = p ->
  zget R kS4 = t_out st - (262144 - t_cout st) ->
  zget R kSP = u + -272 -> zget R kGP = gp -> zget R kTP = tp ->
  zget R kS5 = n - cin0 -> zget R kS6 = 262144 - t_cout st -> zget R kS7 = t_hold st -> zget R kS8 = t_bits st ->
  zget R kS9 = t_out st -> zget R kS11 = q + t_cin st ->
  mem_u64 R_segs M (u + -232) L_UW_RET -> mem_u64 R_segs M (u + -240) p ->
  mem_u64 R_segs M (u + -248) rv -> mem_u64 R_segs M (u + -256) (n - t_cin st) ->
  mem_u64 R_segs M (u + -264) (262144 - t_cout st) -> mem_u64 R_segs M (u + -272) (t_out st - (262144 - t_cout st)) ->
  s_std cx fin M -> st_at R_segs cx st M -> strm_at R_segs cx st M ->
  mem_arr 2 R_segs M (p + 168) N_LENS lf -> mem_arr 4 R_segs M (p + 1384) N_CODES cf ->
  wph = 0 -> mpostL R_segs Mza M (fp_u2 0) ->
  realizes R_segs (zcfg R_segs T_ZW (zupd R []) M MD) T.
Hypothesis HZE2 : KZE2.
Hypothesis HZE1 : KZE1.
Hypothesis HZW : KZW.

Definition PCALL (B : Z) : Prop := forall (site : bool) (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
  let cx := cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site) in
  ainv cx st lf cf -> M2v st < B ->
  u2regs R -> e_mem cx fin st lf cf M -> mpostL R_segs Mza M (fp_u2 wph) ->
  realizes R_segs (zcfg R_segs (pc_site site) (zupd R []) M MD) T.

Local Ltac open_u2 :=
  unfold ZSEP in Spq, Spob, Sobq, Sprom;
  zkeysb; unfold L_TAIL, L_C1, L_C2, RA_C1, RA_C2, L_EXIT, L_INFLATE, T_ZE1, T_ZE2, T_ZW, RA2 in *;
  cbv [STATE_SIZE FRA WIN_SIZE ROM_LO_ALL A_ZCALLOC A_ZCFREE BUF DATA_LO DATA_LEN] in *;
  pose proof two64_eq as TW64.

Lemma u2_tail_s : forall R M st lf cf (ra : Z),
  let cx := cxc wph (t_cin st) (t_cout st) (Wv st) ra in
  ainv cx st lf cf -> u2regs R -> e_mem cx fin st lf cf M ->
  (forall (site : bool) R' M',
     u2regs R' -> e_mem cx fin st lf cf M' -> mpostL R_segs M M' [(u + 8, 4); (u + 32, 4)] ->
     realizes R_segs (zcfg R_segs (pc_site site) (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_TAIL (zupd R []) M MD) T.
Proof.
  intros R M st lf cf ra cx AI RE EM K. subst cx.
  pose proof AI as AI'. dand AI' as (RNG_ & _ & _). unfold RNG in RNG_. unfold cxc in RNG_. icx_cbn.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. destr_conj RNG_.
  unfold u2regs in RE. destr_conj RE. open_u2. unfold pc_site, L_C1, L_C2 in K.
  pose proof EM as EM'. open_emem EM'. clear ROM Wp Wob Ww CST HK Hin SAT Hlens Hcodes.
  unfold cxc in Wstk. unfold strm_at, cxc in STRM. icx_cbn. cbv [BUF] in STRM. dand STRM as (S8 & S16 & S32 & S40 & S80 & S88).
  pose proof (mpostL_stable R_segs M [(u + 8, 4); (u + 32, 4)] ltac:(ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL R_segs M X [(u + 8, 4); (u + 32, 4)]) M) by (apply mpostL_refl).
  Local Ltac fin_tail K site EM HAG :=
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => apply (K site R' Mx) end;
    [ unfold u2regs; zkeys; split_conj; zreg
    | first [ exact EM
            | repeat match goal with H : mem_wr R_segs _ _ _ |- _ => clear H end;
              lazymatch goal with |- e_mem _ _ _ _ _ ?Mx =>
                  match goal with HP : framed _ Mx |- _ =>
                    pose proof EM as EM2; unfold cxc in EM2; open_emem EM2; icx_cbn; cbv [BUF] in *;
                    let HP' := fresh in pose proof HP as HP'; unfold framed in HP'; zreattachL HP';
                    unfold e_mem, strm_at, cxc; icx_cbn; cbv [BUF]; split_conj;
                    first [ assumption
                          | match goal with H : mem_u32 R_segs ?My ?a ?v |- mem_u32 R_segs ?My ?a ?v' => replace v' with v by lia_std; exact H end
                          | match goal with |- ?G => idtac "TAILSIDE" G end ] end end
            | match goal with |- ?G => idtac "TAILSIDE2" G end ]
    | first [exact HAG | match goal with |- ?G => idtac "TAILSIDE3" G end ] ].
  tstep1 Rfd.
  destruct (Z.eq_dec cout 262144) as [Eo | Eo].
  -
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd true.
    tstep1 Rfd.
    zstep Rfd.
    tstep1 Rfd.
    destruct (Z.eq_dec cin n) as [Ei | Ei].
    + zbr Rfd false.
      zstep Rfd.
      zbr Rfd true.
      tstep1 Rfd.
      zstep Rfd.
      fin_tail K false EM HAG.
    + zbr Rfd true.
      fin_tail K true EM HAG.
  -
    zbr Rfd true.
    tstep1 Rfd.
    destruct (Z.eq_dec cin n) as [Ei | Ei].
    + zbr Rfd true.
      zstep Rfd.
      zbr Rfd true.
      tstep1 Rfd.
      zstep Rfd.
      fin_tail K false EM HAG.
    + zbr Rfd false.
      fin_tail K true EM HAG.
Qed.

Lemma ainv_recx : forall w a b c r st lf cf r' W',
  ainv (cxc w a b c r) st lf cf -> b <= t_cout st \/ True ->
  ainv (cxc w (t_cin st) (t_cout st) W' r') st lf cf.
Proof.
  intros w a b c r st lf cf r' W' (R & Wn & Mo) _. destruct st.
  unfold ainv, RNG, WIN, MODE, tables_live, ctable_live, cxc in *. icx_cbn.
  split; [| split; [exact Wn | exact Mo]]. destr_conj R. split_conj; try assumption; lia_std.
Qed.

Ltac lia_std ::= lia_std_stock.
Lemma M2v_nonneg : forall w a b c r st lf cf, ainv (cxc w a b c r) st lf cf -> 0 <= M2v st.
Proof.
  intros w a b c r st lf cf (R & _ & _). destruct st. unfold RNG, cxc, M2v, Wv in *. icx_cbn. destr_conj R. lia_std.
Qed.
Ltac lia_std ::= lia_std_fast.

Lemma fp_call_u2 : forall w cin cout W0 ra M0 M,
  mpostL R_segs M0 M (fp_call (cxc w cin cout W0 ra)) ->
  mpostL R_segs M0 M [(u + -1024, 1024); (u, 112); (p, STATE_SIZE); (BUF, 262144); (w, if w =? 0 then 0 else WIN_SIZE)].
Proof.
  intros w cin cout W0 ra M0 M H. unfold fp_call, fp_loop, cxc, wsz in H. icx_cbn. cbv [FRA ZS_OFF ZS_SIZE] in H. cbn [app] in H.
  replace (u - 1024) with (u + -1024) in H by lia. exact H.
Qed.

Lemma fp_u2_ok : forall w, wok w -> ranges_ok (fp_u2 w).
Proof.
  intros w (W1 & W2 & _). pose proof two64_eq as TW64. unfold fp_u2. cbv [STATE_SIZE WIN_SIZE FRA BUF] in *.
  cbn [ranges_ok]. destruct (Z.eqb_spec w 0); lia_std.
Qed.

Section Handlers.
Variable B : Z.
Hypothesis IH : PCALL B.

Lemma u2_krl : forall (site : bool) cin cout W0 Mc,
  0 <= cin <= n -> 0 <= cout <= 262144 ->
  M2e (cxc wph cin cout W0 (ra_site site)) <= B ->
  framed (fun X => mpostL R_segs Mza X (fp_u2 wph)) Mc ->
  KRL (cxc wph cin cout W0 (ra_site site)) fin MD T Mc.
Proof.
  intros site cin cout W0 Mc Hcin Hcout HB HAG0 R M rc st lf cf HB' AI PRG HWle EM FRM HP. pose proof Hwph as Hw.
  pose proof AI as AI'. dand AI' as (RNG_ & _ & MODE_). pose proof (proj1 MODE_) as Hreach.
  unfold RNG, cxc in RNG_. icx_cbn.
  unfold s_regs_back, cxc, Kra in HB'. icx_cbn. zkeys. cbn [Pos.eqb] in HB'. destr_conj HB'.
  apply fp_call_u2 in HP.
  pose proof (framed_mpostL_trans _ _ _ _ _ _ HAG0 HP ltac:(intros x Hx; eapply ranges_within_outside; [| exact Hx];
              unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac)) as HAG.
  clear HAG0 HP.
  destruct st as [mode last flags cin' cout' hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. destr_conj RNG_. open_u2.
  unfold M2, M2e, Wm, cxc in PRG. icx_cbn. unfold M2e, cxc in HB. icx_cbn.
  destruct (Z.eq_dec (rc mod 18446744073709551616) 0) as [Erc | Erc].
  -
    specialize (PRG Erc).
    assert (TAIL : realizes R_segs (zcfg R_segs L_TAIL (zupd R []) M MD) T).
    { unfold L_TAIL.
      eapply (u2_tail_s R M (IST mode last flags cin' cout' hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf (ra_site site)).
      - eapply ainv_recx; [exact AI | right; exact I].
      - unfold u2regs; zkeys; split_conj; assumption.
      - exact EM.
      - intros site' R' M' RE' EM' HP'.
        match type of HAG with framed _ ?Mc' =>
          pose proof (framed_mpostL_trans _ _ _ _ _ _ HAG HP' ltac:(intros x Hx; eapply ranges_within_outside; [| exact Hx];
                      unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac)) as HAG' end.
        eapply (IH site' R' M' _ lf cf).
        + eapply ainv_recx; [exact AI | right; exact I].
        + unfold M2v, Wv; icx_cbn. lia.
        + exact RE'.
        + exact EM'.
        + exact HAG'. }
    unfold L_TAIL in TAIL.
    destruct site; unfold ra_site, RA_C1, RA_C2 in *; unfold cxc; icx_cbn; cbv [Kra]; zkeys; cbn [Pos.eqb].
    + zbr Rfd true. exact TAIL.
    + zbr Rfd false. exact TAIL.
  -
    assert (EXIT : realizes R_segs (zcfg R_segs L_EXIT (zupd R []) M MD) T).
    { unfold L_EXIT. pose proof EM as EM'. open_emem EM'.
      unfold i_cst, cxc in CST; icx_cbn; cbv [BUF] in CST. dand CST as (C64 & C88 & Cp0 & _ & _ & _ & _ & Cp72 & _).
      destruct HK as [C72 C80]. icx_cbn. destruct SAT as [Hmode _]. unfold cxc in Hmode; icx_cbn.
      unfold cxc in Wstk, Wp; icx_cbn.
      dand Hw as (W1 & W2 & W3 & _).
      eapply (u2_exit_s R [] M MD T u p wph rc 0 0 mode zc gp tp s5 s6 s7 s8 s9 s10 s11 Hh);
        try assumption; try zreg; try klia.
      + intros R' M' Hw0. intros. eapply (HZE2 R' M'); try eassumption.
        eapply (framed_mpostL_trans _ _ _ _ _ _ HAG); [eassumption |].
        intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac.
      + intros R' M' Hw1. intros. eapply (HZE1 R' M'); try eassumption.
        eapply (framed_mpostL_trans _ _ _ _ _ _ HAG); [eassumption |].
        intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac. }
    unfold L_EXIT in EXIT.
    destruct site; unfold ra_site, RA_C1, RA_C2 in *; unfold cxc; icx_cbn; cbv [Kra]; zkeys; cbn [Pos.eqb].
    + zbr Rfd false. zstep Rfd. exact EXIT.
    + zbr Rfd true. exact EXIT.
Qed.

Lemma u2_krx : forall (site : bool) cin cout W0 Mc,
  framed (fun X => mpostL R_segs Mza X (fp_u2 wph)) Mc ->
  KRX (cxc wph cin cout W0 (ra_site site)) fin MD T Mc.
Proof.
  intros site cin cout W0 Mc HAG0 R M rc m Hrc HB' STD Hm Hreach HP. pose proof Hwph as Hw.
  unfold s_regs_back, cxc, Kra in HB'. icx_cbn. zkeys. cbn [Pos.eqb] in HB'. destr_conj HB'.
  apply fp_call_u2 in HP.
  pose proof (framed_mpostL_trans _ _ _ _ _ _ HAG0 HP ltac:(intros x Hx; eapply ranges_within_outside; [| exact Hx];
              unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac)) as HAG.
  clear HAG0 HP. open_u2.
  assert (EXIT : realizes R_segs (zcfg R_segs 85680 (zupd R []) M MD) T).
  { pose proof STD as STD'. open_std STD'.
    unfold i_cst, cxc in CST; icx_cbn; cbv [BUF] in CST. dand CST as (C64 & C88 & Cp0 & _ & _ & _ & _ & Cp72 & _).
    destruct HK as [C72 C80]. unfold cxc in C72, C80, Wstk, Wp, Hm; icx_cbn.
    dand Hw as (W1 & W2 & W3 & _).
    eapply (u2_exit_s R [] M MD T u p wph rc 0 0 m zc gp tp s5 s6 s7 s8 s9 s10 s11 Hh);
      try assumption; try zreg; try klia.
    + intros R' M' Hw0. intros. eapply (HZE2 R' M'); try eassumption.
      eapply (framed_mpostL_trans _ _ _ _ _ _ HAG); [eassumption |].
      intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac.
    + intros R' M' Hw1. intros. eapply (HZE1 R' M'); try eassumption.
      eapply (framed_mpostL_trans _ _ _ _ _ _ HAG); [eassumption |].
      intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac. }
  destruct site; unfold ra_site, RA_C1, RA_C2 in *; unfold cxc; icx_cbn; cbv [Kra]; zkeys; cbn [Pos.eqb].
  - zbr Rfd false. zstep Rfd. exact EXIT.
  - zbr Rfd true. exact EXIT.
Qed.

Lemma u2_kw : forall (site : bool) cin cout W0 Mc,
  0 <= cin <= n -> 0 <= cout <= 262144 ->
  framed (fun X => mpostL R_segs Mza X (fp_u2 wph)) Mc ->
  KW (cxc wph cin cout W0 (ra_site site)) fin MD T Mc.
Proof.
  intros site cin cout W0 Mc Hcin Hcout HAG0 R M st rv lf cf Hw0 SI Hc Hmd. intros.
  match goal with HP : mpostL R_segs Mc M _ |- _ =>
    apply fp_call_u2 in HP;
    pose proof (framed_mpostL_trans _ _ _ _ _ _ HAG0 HP ltac:(intros x Hx; eapply ranges_within_outside; [| exact Hx];
                unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac)) as HAG end.
  unfold cxc in Hw0; icx_cbn. clear HAG0.
  pose proof Hw0 as Hw0'. rewrite Hw0' in *.
  eapply (HZW R M cin cout W0 (ra_site site) st rv lf cf);
    first [ destruct site; [left | right]; reflexivity | exact HAG | exact Hw0 | eassumption
          | match goal with |- ?G => idtac "KWSIDE" G end ].
Qed.
End Handlers.

Lemma pcall_step : forall B, PCALL B -> PCALL (B + 1).
Proof.
  intros B IH site R M st lf cf cx AI MB RE EM HP. subst cx. pose proof Hwph as Hw.
  pose proof AI as AI'. dand AI' as (RNG_ & _ & _). unfold RNG, cxc in RNG_. icx_cbn.
  pose proof (M2v_nonneg _ _ _ _ _ _ _ _ AI) as Hnn.
  assert (Hcin : 0 <= t_cin st <= n) by (destruct st; icx_cbn; destr_conj RNG_; lia_std).
  assert (Hcout : 0 <= t_cout st <= 262144) by (destruct st; icx_cbn; destr_conj RNG_; lia_std).
  clear RNG_.
  pose proof (ctx_ok_cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site) Hw Hcin Hcout
                ltac:(destruct site; [left | right]; reflexivity)) as CX.
  pose proof (mpostL_stable R_segs Mza (fp_u2 wph) (fp_u2_ok wph Hw)) as HST.
  change (framed (fun X => mpostL R_segs Mza X (fp_u2 wph)) M) in HP. rename HP into HAG.
  unfold u2regs in RE. destr_conj RE. open_u2.
  assert (Hfin' : forall i, 0 <= i < c_n (cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site)) -> 0 <= fin i < 256) by exact Hfin.
  assert (OBLOW : c_ob (cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site)) + c_osz (cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site))
                  <= c_u (cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site)) - FRA) by (unfold cxc; icx_cbn; cbv [BUF FRA]; lia).
  destruct site; unfold pc_site, ra_site, L_C1, L_C2, RA_C1, RA_C2 in *.
  all: zstep Rfd; zstep Rfd; zstep Rfd.
  all: lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?lc) ?Mx _) _ =>
         eapply (inflate_s _ fin MD T CX Hh Hfin' OBLOW MEMCPY ADLER
                   A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
                   A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH R' lc Mx st lf cf AI) end.
  all: first [ reflexivity
             | unfold Wm, Wv, cxc; icx_cbn; reflexivity
             | unfold s_regs_entry, cxc, Kra; icx_cbn; zkeys; cbn [Pos.eqb]; split_conj; zreg
             | exact EM
             | eapply (u2_krl B IH true); [exact Hcin | exact Hcout | unfold M2e, cxc; icx_cbn; unfold M2v in MB; lia | exact HAG]
             | eapply (u2_krl B IH false); [exact Hcin | exact Hcout | unfold M2e, cxc; icx_cbn; unfold M2v in MB; lia | exact HAG]
             | eapply (u2_krx true); [exact HAG]
             | eapply (u2_krx false); [exact HAG]
             | eapply (u2_kw true); [exact Hcin | exact Hcout | exact HAG]
             | eapply (u2_kw false); [exact Hcin | exact Hcout | exact HAG] ].
Qed.

Lemma pcall_nat : forall k : nat, PCALL (Z.of_nat k).
Proof.
  induction k as [|k IH].
  - intros site R M st lf cf cx AI MB. exfalso. pose proof (M2v_nonneg _ _ _ _ _ _ _ _ AI). cbn [Z.of_nat] in MB. lia_std.
  - rewrite Nat2Z.inj_succ. apply pcall_step. exact IH.
Qed.

Theorem pcall_all : forall B, PCALL B.
Proof.
  intros B site R M st lf cf cx AI MB.
  apply (pcall_nat (Z.to_nat (M2v st + 1)) site R M st lf cf AI). pose proof (M2v_nonneg _ _ _ _ _ _ _ _ AI). lia_std.
Qed.

End U2.
End FXG.
