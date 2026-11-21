(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U Require TBase T_Entry.

Module T_Ret.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* [comment removed for export] *)
Definition s_regs_back (cx : ictx) (rc : Z) (R : tree Z) : Prop :=
  zget R kA0 = rc /\ zget R kSP = c_u cx /\ zget R kRA = c_K cx kRA /\
  zget R kGP = c_K cx kGP /\ zget R kTP = c_K cx kTP /\
  zget R kS0 = c_K cx kS0 /\ zget R kS1 = c_K cx kS1 /\ zget R kS2 = c_K cx kS2 /\ zget R kS3 = c_K cx kS3 /\
  zget R kS4 = c_K cx kS4 /\ zget R kS5 = c_K cx kS5 /\ zget R kS6 = c_K cx kS6 /\ zget R kS7 = c_K cx kS7 /\
  zget R kS8 = c_K cx kS8 /\ zget R kS9 = c_K cx kS9 /\ zget R kS10 = c_K cx kS10 /\ zget R kS11 = c_K cx kS11.

Lemma ret_t {RCa1 : RunCtx}  : forall cx Rb l M MD T rc,
  ctx_ok ROMHI_T cx -> m_halted MD = None ->
  s_regs_ret cx rc Rb l -> i_frame cx M ->
  (forall R', s_regs_back cx rc R' -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (c_K cx kRA) (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_RET (zupd Rb l) M MD) T.
Proof.
  intros cx Rb l M MD T rc CX Hh RE FRM K.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  unfold s_regs_ret in RE. icx_cbn. destr_conj RE.
  unfold i_frame in FRM. icx_cbn. destr_conj FRM.
  zkeysb. unfold L_RET in *. pose proof two64_eq as TW64.
  do 13 (zstep Rfd).                  (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zret Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (K R') end.
  unfold s_regs_back; icx_cbn; zkeys; split_conj; zreg.
Qed.
End T_Ret.

From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U Require T_U2Cw. Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_U2Cw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require S_HeadA S_Check.


Module T_LeaveA.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import T_Uw OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.TBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_Entry.T_Loop T_Ret OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_Entry T_Check.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_LDT_T : Z := 96924.      (* [comment removed for export] *)
Definition L_UW_ARGS_T : Z := 96648.  (* [comment removed for export] *)
Definition L_LNOWIN_T : Z := 96688.   (* [comment removed for export] *)
Definition L_LRC_T : Z := 97040.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition M2 (cx : ictx) (st : ist) : Z := Wm cx st * 134217728 + (c_n cx - t_cin st).
Definition M2e (cx : ictx) : Z := c_W0 cx * 134217728 + (c_n cx - c_cin0 cx).

(* [comment removed for export] *)
Definition fp_call (cx : ictx) : list (Z * Z) := fp_loop cx ++ [(c_w cx, wsz cx)].

Lemma fp_call_widen {RCa1 : RunCtx}  : forall cx M0 M, mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx).
Proof.
  intros cx M0 M [HA HW]. split; [| exact HW]. intros x Hx. apply HA.
  unfold fp_call, fp_loop in *. cbn in Hx |- *. (first [solve [zkeep_section; tauto] | tauto]).
Qed.

Lemma wsz_facts : forall cx, 0 <= wsz cx <= WIN_SIZE /\ (c_w cx = 0 -> wsz cx = 0) /\ (c_w cx <> 0 -> wsz cx = WIN_SIZE).
Proof. intros cx. unfold wsz, WIN_SIZE. destruct (Z.eqb_spec (c_w cx) 0); lia. Qed.

(* [comment removed for export] *)
Ltac fp_call_frame HP0 :=
  lazymatch type of HP0 with mpostL ?segs ?M0 ?M ?fp =>
    let HST := fresh "HST" in let HAG := fresh "HAG" in
    pose proof (mpostL_stable segs M0 fp ltac:(ranges_ok_tac)) as HST;
    change (framed (fun X => mpostL segs M0 X fp) M) in HP0; rename HP0 into HAG end.

(* [comment removed for export] *)
Definition hideP (P : Prop) : Prop := P.

(* [comment removed for export] *)
Ltac zgen :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => let x' := fresh "gv" in set (x' := e); clearbody x'
  end.

(* [comment removed for export] *)
Lemma lor01 : forall a b, 0 <= a <= 1 -> 0 <= b <= 1 -> 0 <= Z.lor a b < 2.
Proof.
  intros a b Ha Hb.
  assert (Ha' : a = 0 \/ a = 1) by lia_std. assert (Hb' : b = 0 \/ b = 1) by lia_std.
  destruct Ha' as [-> | ->]; destruct Hb' as [-> | ->];
    [ change (Z.lor 0 0) with 0 | change (Z.lor 0 1) with 1 | change (Z.lor 1 0) with 1 | change (Z.lor 1 1) with 1 ]; lia_std.
Qed.

(* [comment removed for export] *)
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
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KRL : Prop :=
  forall (R : tree Z) (M : mem) (rc : Z) (st : ist) (lf cf : Z -> Z),
    s_regs_back cx rc R -> ainv cx st lf cf ->
    (rc mod two64 = 0 -> M2 cx st < M2e cx) -> Wm cx st <= c_W0 cx ->
    e_mem cx fin st lf cf M -> i_frame cx M ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (c_K cx kRA) (zupd R []) M MD) T.
(* [comment removed for export] *)
Definition KRX : Prop :=
  forall (R : tree Z) (M : mem) (rc m : Z),
    rc mod two64 <> 0 -> s_regs_back cx rc R -> s_std cx fin M ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 8) m -> reach m ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (c_K cx kRA) (zupd R []) M MD) T.
(* [comment removed for export] *)
Definition KW : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (rv v4 v5 : Z) (lf cf : Z -> Z),
    c_w cx = 0 -> sinv cx st lf cf -> c_cout0 cx < t_cout st -> t_mode st <= DONE ->
    zget R kA3 = A_ZCALLOC -> zget R kA0 = 0 -> zget R kA1 = WIN_SIZE -> zget R kA2 = 1 ->
    zget R kS0 = c_ob cx + t_cout st -> zget R kS1 = t_out st - (c_osz cx - t_cout st) -> zget R kS2 = 1 -> zget R kS3 = c_p cx ->
    zget R kS4 = t_out st -> zget R kS5 = v4 ->
    zget R kSP = c_u cx + -320 -> zget R kGP = c_K cx kGP -> zget R kTP = c_K cx kTP ->
    zget R kS6 = v5 -> zget R kS8 = c_n cx - t_cin st -> zget R kS10 = c_q cx + t_cin st -> zget R kS11 = rv ->
    (* a worker W04 U: the unpatched inflate's registers at updatewindow's zcalloc call: s4 = out (reloaded from its frame
       slot before the call), s8 = have, s10 = next, s11 = ret; hold is in no register (stored to the state first);
       s7 and s9 hold no model value. updatewindow's own s0 .. s3 unchanged. Its frame holds ra and the unpatched
       inflate's s0 .. s5: p, strm, bits, put, out, v4. *)
    mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -264) L_UW_RET -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -272) (c_p cx) ->
    mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -280) (c_u cx) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -288) (t_bits st) ->
    mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -296) (c_ob cx + t_cout st) ->
    mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -304) (t_out st) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -312) v4 ->
    s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> s_lo cx st M -> s_bk cx st M ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZW (zupd R []) M MD) T.

End KDefs.

Section Leave.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem).
Hypothesis CX : ctx_ok ROMHI_T cx.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < c_n cx -> 0 <= fin i < 256.
Hypothesis OBLOW : c_ob cx + c_osz cx <= c_u cx - FRA.   (* [comment removed for export] *)
Hypothesis MEMCPY : memcpy_spec_t.
Hypothesis ADLER : adler32_spec_t.

Hypothesis HKRL : KRL cx fin MD T M0.
Hypothesis HKRX : KRX cx fin MD T M0.
Hypothesis HKW : KW cx fin MD T M0.

(* [comment removed for export] *)
Local Ltac open_leave CX SI st HP0 :=
  pose proof SI as SI'; dand SI' as (RNG_ & WIN_ & PROG_ & MODE_);
  match goal with H : MODE _ _ _ _ |- _ => pose proof (reach_bounds _ (proj1 H)) as Hmb end;
  pose proof CX as CXc; open_cx CXc;
  (* [comment removed for export] *)
  repeat match goal with H : 0 <= c_K _ _ |- _ => clear H | H : c_K _ _ < _ |- _ => clear H end;
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext];
  icx_cbn;
  match goal with H : RNG _ _ _ _ |- _ => unfold RNG in H; icx_cbn; cbv [N_CODES N_LENS] in H; destr_conj H end;
  match goal with H : PROG _ _ |- _ => unfold PROG, Wm in H; icx_cbn; dand H as (PR1 & PR2 & PR3) end;
  zkeysb; unfold L_LDT_T, L_UW_ARGS_T, L_LNOWIN_T, L_LRC_T, L_LEAVE, L_UW, L_UW_RET, L_UW_CALL, L_RET, L_RET_S10, L_MEM, T_ZW, L_ZB in *;
  cbv [A_ZCALLOC A_ZCFREE A_ADLER32] in *; pose proof two64_eq as TW64;
  pose proof (proj1 (wsz_facts cx)) as Hws0; cbv [WIN_SIZE] in Hws0;
  unfold fp_call, fp_loop in HP0; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE] in HP0; cbn [app] in HP0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma leave_rc_t : forall Rb l M st rv lf cf,
  sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kA1 = 0 -> zget_l Rb l kS11 = rv -> zget_l Rb l kS8 = c_n cx - t_cin st ->
  zget_l Rb l kS2 = c_osz cx - t_cout st -> zget_l Rb l kA3 = c_u cx ->
  s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> s_lo cx st M -> s_bk cx st M ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LRC_T (zupd Rb l) M MD) T.
Proof.
  intros Rb l M st rv lf cf SI Lsp Lgp Ltp La1 Ls11 Ls8 Ls2 La3 STD SAT STRM SLO SBK Hlens Hcodes HP0.
  pose proof STD as STD0. open_std STD. open_leave CX SI st HP0.
  fp_call_frame HP0.
  (* a worker W04 U: the unpatched return-code block reads in (frame), have (s8), out (frame), left (s2, not reloaded),
     flush (a1) and ret (s11), and stores data_type (a0) through strm (a3) before the final branch on a1. *)
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C72f & _).
  pose proof SLO as SLO'. unfold s_lo in SLO'. icx_cbn. destruct SLO' as [HL HO].
  (* a worker W04 U: the return (memory after the data_type store: any memory with the frame and e_mem) *)
  assert (RET : forall RQ MQ rc,
    zget RQ kSP = c_u cx + -256 -> zget RQ kGP = c_K cx kGP -> zget RQ kTP = c_K cx kTP -> zget RQ kS11 = rc ->
    hideP (rc mod two64 = 0 -> cin <> c_cin0 cx \/ out <> c_osz cx - cout) ->
    i_frame cx MQ -> e_mem cx fin (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf MQ ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 MQ (fp_call cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 97096 (zupd RQ []) MQ MD) T).
  { intros RQ MQ rc Qsp Qgp Qtp Qs11 PRG QFRM QEM QHP. zkeys.
    zstep Rfd.                        (* a worker U: mv a0,s11 *)
    eapply (ret_t cx _ _ MQ MD T rc CX Hh).
    - unfold s_regs_ret; icx_cbn; zkeys; split_conj; zreg.
    - exact QFRM.
    - intros R9 HB. icx_cbn.
      eapply (HKRL R9 MQ rc (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf HB).
      + dand SI as (X1 & X2 & X3 & X4). split; [exact X1 | split; [exact X2 | exact X4]].
      + intros Hrc. unfold hideP in PRG. specialize (PRG Hrc). unfold M2, M2e, Wm; icx_cbn. clear HKRL HKRX HKW.
        destruct PR3 as [PR3 | [PR3 _]]; lia.
      + unfold Wm; icx_cbn. clear HKRL HKRX HKW; lia.
      + exact QEM.
      + exact QFRM.
      + exact QHP. }
  (* a worker W04 U: the final branch, on a1 (the patched block branched on a0) *)
  assert (FIN : forall RJ MJ (j : Z),
    zget RJ kSP = c_u cx + -256 -> zget RJ kGP = c_K cx kGP -> zget RJ kTP = c_K cx kTP ->
    zget RJ kS11 = rv -> zget RJ kA1 = j ->
    hideP (j mod two64 = 0 -> rv mod two64 = 0 -> cin <> c_cin0 cx \/ out <> c_osz cx - cout) ->
    i_frame cx MJ -> e_mem cx fin (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf MJ ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 MJ (fp_call cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 97088 (zupd RJ []) MJ MD) T).
  { intros RJ MJ j Rsp Rgp Rtp Rs11 Ra1 PROGRESS JFRM JEM JHP. zkeys.
    destruct (Z.eq_dec (j mod two64) 0) as [Ej|Ej].
    - zbr Rfd true.                   (* a worker U: beqz a1 taken *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (RET R' MJ rv) end;
        [ zreg | zreg | zreg | zreg | intros Hrc; exact (PROGRESS Ej Hrc) | exact JFRM | exact JEM | exact JHP ].
    - zbr Rfd false.                  (* a worker U: beqz a1 not taken *)
      zstep Rfd.                      (* a worker U: li s11,-5 *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (RET R' MJ (-5)) end;
        [ zreg | zreg | zreg | zreg | intros Hrc; exfalso; revert Hrc; cbv; discriminate | exact JFRM | exact JEM | exact JHP ]. }
  (* a worker W04 U: in = have, out = left, ret = 0: the flag is known *)
  Local Ltac rc_steps_A :=
    zstep Rfd;                        (* a worker U: ld a2 (in) *)
    zstep Rfd; zsetreg 0 ltac:(symmetry; apply Z.lxor_nilpotent);                  (* a worker U: xor a2,a2,s8 *)
    zstep Rfd;                        (* a worker U: ld a4 (out) *)
    zstep Rfd; zsetreg 0 ltac:(symmetry; apply Z.lxor_nilpotent);                  (* a worker U: xor a4,a4,s2 *)
    zstep Rfd;                        (* a worker U: add a1,a1,-4 *)
    zstep Rfd; zlit;                  (* a worker U: or a2,a2,a4 *)
    zstep Rfd; zlit;                  (* a worker U: seqz a1,a1 *)
    zstep Rfd; zlit;                  (* a worker U: seqz a2,a2 *)
    zstep Rfd; zlit;                  (* a worker U: or a1,a1,a2 *)
    zstep Rfd; match goal with H : _ mod 18446744073709551616 = 0 |- _ => zsetreg 1 ltac:(rewrite H; reflexivity) end;   (* a worker U: seqz a2,s11 *)
    zstep Rfd; zlit;                  (* a worker U: and a1,a1,a2 *)
    tstep1 Rfd.                       (* a worker U: sw a0 (data_type) *)
  (* a worker W04 U: the general case: every value generalized *)
  Local Ltac rc_steps_B :=
    zstep Rfd;                        (* a worker U: ld a2 (in) *)
    zstep Rfd; zgen;                  (* a worker U: xor a2,a2,s8 *)
    zstep Rfd;                        (* a worker U: ld a4 (out) *)
    zstep Rfd; zgen;                  (* a worker U: xor a4,a4,s2 *)
    zstep Rfd;                        (* a worker U: add a1,a1,-4 *)
    zstep Rfd; zgen;                  (* a worker U: or a2,a2,a4 *)
    zstep Rfd; zlit;                  (* a worker U: seqz a1,a1 *)
    zstep Rfd; zgen;                  (* a worker U: seqz a2,a2 *)
    zstep Rfd; zgen;                  (* a worker U: or a1,a1,a2 *)
    zstep Rfd; zgen;                  (* a worker U: seqz a2,s11 *)
    zstep Rfd; zgen;                  (* a worker U: and a1,a1,a2 *)
    tstep1 Rfd.                       (* a worker U: sw a0 (data_type) *)
  Local Ltac rc_apply FIN FRM HAG :=
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => eapply (FIN R' Mx) end; try zreg;
    try exact FRM; try exact HAG; try (unfold e_mem; icx_cbn; split_conj; assumption).
  destruct (Z.eq_dec cin (c_cin0 cx)) as [Ecin|Ecin]; [destruct (Z.eq_dec out (c_osz cx - cout)) as [Ecout|Ecout]; [destruct (Z.eq_dec (rv mod two64) 0) as [Erv|Erv]|]|].
  - (* a worker U: in = have, out = left, ret = Z_OK: the flag is 1 *)
    revert C72f HO Ls8. rewrite <- Ecin. rewrite Ecout. intros C72f HO Ls8.
    rc_steps_A. rc_apply FIN FRM HAG. intros Hj _. exfalso. revert Hj. cbv. discriminate.
  - rc_steps_B. rc_apply FIN FRM HAG. intros _ Hrv. exfalso. exact (Erv Hrv).
  - rc_steps_B. rc_apply FIN FRM HAG. intros _ _. right. exact Ecout.
  - rc_steps_B. rc_apply FIN FRM HAG. intros _ _. left. exact Ecin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma leave_uwret_t : forall Rb l M st rv uwret lf cf,
  sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kA0 = uwret -> (uwret = 0 \/ uwret = 1) ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS11 = rv -> zget_l Rb l kS1 = c_u cx -> zget_l Rb l kS4 = t_out st ->
  s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> s_lo cx st M -> s_bk cx st M ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_RET (zupd Rb l) M MD) T.
Proof.
  (* a worker W04 U: after a good return the unpatched leave reloads have and left from the stream through s1, then runs
     the totals, the check and data_type (patched: before the window step), then the return-code block. DTX is the
     data_type block (the same steps as T_Leave.leave_dt_t, which comes later in the file); TOT is the totals join. *)
  assert (DTX : forall Rb l M st rv lf cf,
    sinv cx st lf cf ->
    zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
    zget_l Rb l kS0 = c_p cx -> zget_l Rb l kA3 = c_u cx -> zget_l Rb l kA1 = 0 ->
    zget_l Rb l kS2 = c_osz cx - t_cout st ->
    zget_l Rb l kS8 = c_n cx - t_cin st -> zget_l Rb l kS11 = rv ->
    s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> s_lo cx st M -> s_bk cx st M ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LDT_T (zupd Rb l) M MD) T).
  { intros Rb l M st rv lf cf SI Lsp Lgp Ltp Ls0 La3 La1 Ls2 Ls8 Ls11 STD SAT STRM SLO SBK Hlens Hcodes HP0.
    open_std STD. open_leave CX SI st HP0.
    fp_call_frame HP0.
    pose proof SAT as SAT'. destruct SAT' as [Hmode SREST']. unfold st_rest in SREST'. icx_cbn. dand SREST' as (Hlast & _).
    pose proof STRM as STRM'. unfold strm_at in STRM'. icx_cbn. dand STRM' as (_ & _ & _ & _ & _ & S88).
    tstep1 Rfd.                         (* a worker U: lw a0 (last) *)
    tstep1 Rfd.                         (* a worker U: lw a4 (bits) *)
    zstep Rfd. zgenreg_bool lnz.        (* a worker U: snez a0,a0 *)
    zstep Rfd.                          (* a worker U: sll a0,a0,6 *)
    zsetreg (64 * lnz) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 6) with 64; rewrite ?Z.mod_small by lia; lia).
    zstep Rfd.                          (* a worker U: add a2,a4,a0 *)
    tstep1 Rfd.                         (* a worker U: addw a0,a4,a0 *)
    zbr Rfd false.                      (* a worker U: bne a0,a2 (UBSan) *)
    tstep1 Rfd.                         (* a worker U: lw a0 (mode) *)
    tstep1 Rfd.                         (* a worker U: sext.w a5,a2 *)
    zstep Rfd.                          (* a worker U: lui a2 *)
    zstep Rfd. zlit.                    (* a worker U: addw a4,a2 (TYPE) *)
    zstep Rfd.                          (* a worker U: xor a4,a0,a4 *)
    zstep Rfd. zgenreg_bool ist.        (* a worker U: seqz a4,a4 *)
    zstep Rfd.                          (* a worker U: sll a6,a4,7 *)
    zsetreg (128 * ist) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 7) with 128; rewrite ?Z.mod_small by lia; lia).
    zstep Rfd.                          (* a worker U: add a4,a5,a6 *)
    tstep1 Rfd.                         (* a worker U: addw a5,a5,a6 *)
    zbr Rfd false.                      (* a worker U: bne a5,a4 (UBSan) *)
    tstep1 Rfd.                         (* a worker U: sext.w a4,a4 *)
    zstep Rfd. zlit.                    (* a worker U: addw a5,a2 (LEN_) *)
    zstep Rfd. zlit.                    (* a worker U: addw a2,a2 (COPY_) *)
    zstep Rfd.                          (* a worker U: xor a5,a0,a5 *)
    zstep Rfd.                          (* a worker U: xor a0,a0,a2 *)
    zstep Rfd. zgenreg_bool e1.         (* a worker U: seqz a2,a5 *)
    zstep Rfd. zgenreg_bool e2.         (* a worker U: seqz a0,a0 *)
    zstep Rfd.                          (* a worker U: or a0,a2,a0 *)
    zgenreg_range eo 0 2 ltac:(apply lor01; assumption).
    zstep Rfd.                          (* a worker U: sll a2,a0,8 *)
    zsetreg (256 * eo) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; rewrite ?Z.mod_small by lia; lia).
    zstep Rfd.                          (* a worker U: add a0,a4,a2 *)
    tstep1 Rfd.                         (* a worker U: addw a2,a4,a2 *)
    zbr Rfd false.                      (* a worker U: bne a2,a0 (UBSan) *)
    clear S88 Hlast.
    lazymatch type of SI with sinv _ ?st _ _ =>
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (leave_rc_t R9 [] Mx st _ _ _ SI) end end;
    first [ zreg | icx_cbn; zreg | assumption | close_std | exact HAG
          | unfold strm_at; icx_cbn; match goal with H : strm_at _ _ _ _ |- _ => unfold strm_at in H; icx_cbn; exact H end
          | match goal with |- ?G => idtac "RCSIDE" G end ]. }
  assert (TOT : forall Rb l M st rv lf cf,
    sinv cx st lf cf ->
    zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
    zget_l Rb l kS0 = c_p cx -> zget_l Rb l kA3 = c_u cx -> zget_l Rb l kS1 = c_u cx -> zget_l Rb l kA1 = 0 ->
    zget_l Rb l kA4 = c_osz cx - t_cout st -> zget_l Rb l kS4 = t_out st ->
    zget_l Rb l kS8 = c_n cx - t_cin st -> zget_l Rb l kS11 = rv ->
    s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> s_lo cx st M -> s_bk cx st M ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96748 (zupd Rb l) M MD) T).
  { intros Rb l M st rv lf cf SI Lsp Lgp Ltp Ls0 La3 Ls1 La1 La4 Ls4 Ls8 Ls11 STD SAT STRM SLO SBK Hlens Hcodes HP0.
    open_std STD. open_leave CX SI st HP0.
    fp_call_frame HP0.
    pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
    dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C136f & _ & _ & _ & _ & _ & C72f & _).
    pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & Cp16 & _).
    pose proof (mem_u32_lo8_t _ _ _ Cp16) as Cp16b. cbn [Z.modulo Z.pos_div_eucl] in Cp16b. clear Cp16.
    pose proof STRM as STRM'. unfold strm_at in STRM'. icx_cbn. dand STRM' as (_ & _ & S24 & _).
    destruct (mem_wr_u64_exists_R M (c_u cx + 16) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (ti & Hti & Rti).
    destruct (mem_wr_u64_exists_R M (c_u cx + 40) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (to & Hto & Rto).
    destruct (mem_wr_u64_exists_R M (c_p cx + 48) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (tt & Htt & Rtt).
    zstep Rfd.                          (* a worker U: mv s2,a4 (left) *)
    tstep1 Rfd.                         (* a worker U: subw a2,s4,a4 (out - left) *)
    zsetreg (out - (c_osz cx - cout)) ltac:(first [lia | rewrite swrap32_small by lia; lia]).
    zstep Rfd.                          (* a worker U: ld a0 (in) *)
    tstep1 Rfd. zgen.                   (* a worker U: subw a0,a0,s8 *)
    zstep Rfd.                          (* a worker U: ld a4 (total_in) *)
    zstep Rfd.                          (* a worker U: ld a5 (total_out) *)
    zstep Rfd. zstep Rfd. zgen.         (* a worker U: zero-extend a0 *)
    zstep Rfd. zgen.                    (* a worker U: add a0,a4,a0 *)
    zstep Rfd. zstep Rfd. zext32.       (* a worker U: zero-extend a2 into a4 *)
    zstep Rfd. zgen.                    (* a worker U: add a5,a5,a4 *)
    tstep1 Rfd.                         (* a worker U: sd a0 (total_in) *)
    tstep1 Rfd.                         (* a worker U: sd a5 (total_out) *)
    zstep Rfd.                          (* a worker U: ld a0 (state total) *)
    zstep Rfd. zlit.                    (* a worker U: lbu a5 (wrap) *)
    zstep Rfd. zgen.                    (* a worker U: add a0,a0,a4 *)
    zstep Rfd. zlit.                    (* a worker U: and a5,a5,4 *)
    tstep1 Rfd.                         (* a worker U: sd a0 (state total) *)
    repeat match goal with H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (c_u cx + 16) _ |- _ => clear H
                          | H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (c_u cx + 40) _ |- _ => clear H
                          | H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (c_p cx + 48) _ |- _ => clear H end.
    try clear Hti; try clear Hto; try clear Htt. clear C72f Cp16b.
    zbr Rfd false.                      (* a worker U: beqz a5 (wrap & 4 is set) *)
    destruct (Z.eq_dec out (c_osz cx - cout)) as [Ecout|Ecout].
    - (* a worker U: out = left: no check *)
      zbr Rfd true.                     (* a worker U: beq s4,s2 *)
      lazymatch type of SI with sinv _ ?st _ _ =>
      lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
        eapply (DTX R9 [] Mx st _ _ _ SI) end end;
      first [ zreg | icx_cbn; zreg | icx_cbn; zkept | assumption | close_std | exact HAG | sbk
            | unfold s_lo; icx_cbn; split; assumption
            | match goal with |- ?G => idtac "DTSIDE" G end ].
    - (* a worker U: the check over the bytes written by this call *)
      zbr Rfd false.                    (* a worker U: beq s4,s2 *)
      assert (Hf0 : flags = 0).
      { dand MODE_ as (_ & Mf & _). icx_cbn.
        assert (Hn1 : flags <> -1) by (intros E; destruct (Mf E) as [_ Hc]; clear Mf HKRL HKRX HKW; lia).
        clear Mf HKRL HKRX HKW. lia. }
      pose proof SAT as SAT'. destruct SAT' as [_ SREST']. unfold st_rest in SREST'. icx_cbn. dand SREST' as (_ & Cfl & _).
      rewrite Hf0 in Cfl.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        destruct (mem_wr_u64_exists_R Mx (c_p cx + 40) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (ck & Hck & Rck) end.
      zstep Rfd.                        (* a worker U: ld a1 (next_out) *)
      tstep1 Rfd.                       (* a worker U: lw a3 (flags) *)
      zstep Rfd. zbool.                 (* a worker U: snez a0,a1 *)
      zstep Rfd.                        (* a worker U: xor a5,a1,a4 *)
      zstep Rfd.                        (* a worker U: seqz a5,a5 *)
      zsetreg 0 ltac:(symmetry; apply seqz_xor_neq; lia).
      zstep Rfd. zlit.                  (* a worker U: xor a0,a0,a5 *)
      zstep Rfd. zbool.                 (* a worker U: sltu a5,a1,a4 *)
      zstep Rfd. zlit.                  (* a worker U: not a5 *)
      zstep Rfd. zlit.                  (* a worker U: and a0,a5,a0 *)
      zbr Rfd true.                     (* a worker U: beqz a3 (flags = 0: adler32) *)
      zbr Rfd false.                    (* a worker U: beqz a0 (UBSan) *)
      zstep Rfd.                        (* a worker U: ld a0 (check) *)
      zstep Rfd. zsetreg (c_ob cx + cout - (out - (c_osz cx - cout))) ltac:(lia).   (* a worker U: sub a1,a1,a4 *)
      clear Cfl.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        destruct (mem_wr_arr_exists_R Mx (c_ob cx) (c_osz cx) Wob ltac:(lia) ltac:(lia) ltac:(lia)) as (fo & HOB & Hfo) end.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        pose proof (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 1 Mx (c_ob cx) (c_osz cx) fo (cout - (out - (c_osz cx - cout))) (out - (c_osz cx - cout)) HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc end.
      replace (c_ob cx + 1 * (cout - (out - (c_osz cx - cout)))) with (c_ob cx + cout - (out - (c_osz cx - cout))) in Hsrc by lia.
      zstep Rfd.                        (* a worker U: jal adler32 *)
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?lc) ?Mx _) _ =>
        eapply (ADLER R' lc Mx MD T ck (c_ob cx + cout - (out - (c_osz cx - cout))) (out - (c_osz cx - cout)) (out - (c_osz cx - cout)) (c_u cx + -256) _
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
      tstep1 Rfd.                       (* a worker U: sd a0 (state check) *)
      zstep Rfd.                        (* a worker U: mv a3,s1 *)
      tstep1 Rfd.                       (* a worker U: sd a0 (strm adler) *)
      zstep Rfd.                        (* a worker U: ld a1 (flush) *)
      lazymatch type of SI with sinv _ ?st _ _ =>
      lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
        eapply (DTX R9 [] Mx st _ _ _ SI) end end;
      first [ zreg | icx_cbn; zreg | icx_cbn; zkept | assumption | close_std | exact HAG | sbk
            | unfold s_lo; icx_cbn; split; assumption
            | match goal with |- ?G => idtac "DTSIDE" G end ]. }
  intros Rb l M st rv uwret lf cf SI Lsp Lgp Ltp La0 Huw Ls0 Ls11 Ls1 Ls4 STD SAT STRM SLO SBK Hlens Hcodes HP0.
  pose proof STD as STD0. pose proof HP0 as HP00. open_std STD. open_leave CX SI st HP0.
  fp_call_frame HP0.
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C136f & _ & _ & _ & _ & C80f & _).
  destruct Huw as [Uw0 | Uw1].
  - (* a worker U: a good return: reload have and left through s1, then the totals join *)
    rewrite Uw0 in La0.
    zbr Rfd true.                     (* a worker U: beqz a0 taken *)
    pose proof STRM as STRM'. unfold strm_at in STRM'. icx_cbn. dand STRM' as (_ & S8 & _ & S32 & _).
    zstep Rfd.                        (* a worker U: mv a3,s1 *)
    tstep1 Rfd.                       (* a worker U: lw s8 (avail_in) *)
    tstep1 Rfd.                       (* a worker U: lw a4 (avail_out) *)
    zstep Rfd.                        (* a worker U: ld a1 (flush) *)
    clear S8 S32.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (TOT R9 [] Mx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) rv lf cf SI) end;
      first [ zreg | icx_cbn; zreg | assumption | exact STD0 | exact HP00 ].
  - (* a worker U: updatewindow failed: mode := MEM, return Z_MEM_ERROR (the totals are not written in U) *)
    rewrite Uw1 in La0.
    zbr Rfd false.                    (* a worker U: beqz a0 not taken *)
    zstep Rfd.                        (* a worker U: ld a0 (the mode base) *)
    zstep Rfd. zlit.                  (* a worker U: add a0,a0,1 (MEM) *)
    tstep1 Rfd.                       (* a worker U: sw a0 (mode) *)
    zstep Rfd.                        (* a worker U: li a0,-4 *)
    zstep Rfd.                        (* a worker U: j to the epilogue *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (ret_t cx R9 [] Mx MD T (-4) CX Hh) end.
    + unfold s_regs_ret; icx_cbn; zkeys; split_conj; zreg.
    + exact FRM.
    + intros R9 HB.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => eapply (HKRX R9 Mx (-4) 16210) end.
      * cbv. discriminate.
      * exact HB.
      * close_std.
      * match goal with H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) _ (c_p cx + 8) 16210 |- _ => exact H end.
      * unfold reach; cbv [HEAD DICTID MEM]; lia_std.
      * exact HAG.
Qed.

End Leave.
End T_LeaveA.

Module T_Leave.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import T_Uw OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.TBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_Entry.T_Loop T_Ret OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_Entry T_Check T_LeaveA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.


Section Leave.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem).
Hypothesis CX : ctx_ok ROMHI_T cx.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < c_n cx -> 0 <= fin i < 256.
Hypothesis OBLOW : c_ob cx + c_osz cx <= c_u cx - FRA.   (* [comment removed for export] *)
Hypothesis MEMCPY : memcpy_spec_t.
Hypothesis ADLER : adler32_spec_t.

Hypothesis HKRL : KRL cx fin MD T M0.
Hypothesis HKRX : KRX cx fin MD T M0.
Hypothesis HKW : KW cx fin MD T M0.

(* [comment removed for export] *)
Local Ltac open_leave CX SI st HP0 :=
  pose proof SI as SI'; dand SI' as (RNG_ & WIN_ & PROG_ & MODE_);
  match goal with H : MODE _ _ _ _ |- _ => pose proof (reach_bounds _ (proj1 H)) as Hmb end;
  pose proof CX as CXc; open_cx CXc;
  (* [comment removed for export] *)
  repeat match goal with H : 0 <= c_K _ _ |- _ => clear H | H : c_K _ _ < _ |- _ => clear H end;
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext];
  icx_cbn;
  match goal with H : RNG _ _ _ _ |- _ => unfold RNG in H; icx_cbn; cbv [N_CODES N_LENS] in H; destr_conj H end;
  match goal with H : PROG _ _ |- _ => unfold PROG, Wm in H; icx_cbn; dand H as (PR1 & PR2 & PR3) end;
  zkeysb; unfold L_LDT_T, L_UW_ARGS_T, L_LNOWIN_T, L_LRC_T, L_LEAVE, L_UW, L_UW_RET, L_UW_CALL, L_RET, L_RET_S10, L_MEM, T_ZW, L_ZB in *;
  cbv [A_ZCALLOC A_ZCFREE A_ADLER32] in *; pose proof two64_eq as TW64;
  pose proof (proj1 (wsz_facts cx)) as Hws0; cbv [WIN_SIZE] in Hws0;
  unfold fp_call, fp_loop in HP0; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE] in HP0; cbn [app] in HP0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma leave_dt_t : forall Rb l M st rv lf cf,
  sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kA3 = c_u cx -> zget_l Rb l kA1 = 0 ->
  zget_l Rb l kS2 = c_osz cx - t_cout st ->
  zget_l Rb l kS8 = c_n cx - t_cin st -> zget_l Rb l kS11 = rv ->
  s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> s_lo cx st M -> s_bk cx st M ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LDT_T (zupd Rb l) M MD) T.
Proof.
  intros Rb l M st rv lf cf SI Lsp Lgp Ltp Ls0 La3 La1 Ls2 Ls8 Ls11 STD SAT STRM SLO SBK Hlens Hcodes HP0.
  open_std STD. open_leave CX SI st HP0.
  fp_call_frame HP0.
  (* a worker W04 U: the unpatched data_type block comes after the window step and the totals; it ends by falling into
     the return-code block (L_LRC_T), which stores data_type. The same steps as the patched block. *)
  pose proof SAT as SAT'. destruct SAT' as [Hmode SREST']. unfold st_rest in SREST'. icx_cbn. dand SREST' as (Hlast & _).
  pose proof STRM as STRM'. unfold strm_at in STRM'. icx_cbn. dand STRM' as (_ & _ & _ & _ & _ & S88).
  tstep1 Rfd.                         (* a worker U: lw a0 (last) *)
  tstep1 Rfd.                         (* a worker U: lw a4 (bits) *)
  zstep Rfd. zgenreg_bool lnz.        (* a worker U: snez a0,a0 *)
  zstep Rfd.                          (* a worker U: sll a0,a0,6 *)
  zsetreg (64 * lnz) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 6) with 64; rewrite ?Z.mod_small by lia; lia).
  zstep Rfd.                          (* a worker U: add a2,a4,a0 *)
  tstep1 Rfd.                         (* a worker U: addw a0,a4,a0 *)
  zbr Rfd false.                      (* a worker U: bne a0,a2 (UBSan) *)
  tstep1 Rfd.                         (* a worker U: lw a0 (mode) *)
  tstep1 Rfd.                         (* a worker U: sext.w a5,a2 *)
  zstep Rfd.                          (* a worker U: lui a2 *)
  zstep Rfd. zlit.                    (* a worker U: addw a4,a2 (TYPE) *)
  zstep Rfd.                          (* a worker U: xor a4,a0,a4 *)
  zstep Rfd. zgenreg_bool ist.        (* a worker U: seqz a4,a4 *)
  zstep Rfd.                          (* a worker U: sll a6,a4,7 *)
  zsetreg (128 * ist) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 7) with 128; rewrite ?Z.mod_small by lia; lia).
  zstep Rfd.                          (* a worker U: add a4,a5,a6 *)
  tstep1 Rfd.                         (* a worker U: addw a5,a5,a6 *)
  zbr Rfd false.                      (* a worker U: bne a5,a4 (UBSan) *)
  tstep1 Rfd.                         (* a worker U: sext.w a4,a4 *)
  zstep Rfd. zlit.                    (* a worker U: addw a5,a2 (LEN_) *)
  zstep Rfd. zlit.                    (* a worker U: addw a2,a2 (COPY_) *)
  zstep Rfd.                          (* a worker U: xor a5,a0,a5 *)
  zstep Rfd.                          (* a worker U: xor a0,a0,a2 *)
  zstep Rfd. zgenreg_bool e1.         (* a worker U: seqz a2,a5 *)
  zstep Rfd. zgenreg_bool e2.         (* a worker U: seqz a0,a0 *)
  zstep Rfd.                          (* a worker U: or a0,a2,a0 *)
  zgenreg_range eo 0 2 ltac:(apply lor01; assumption).
  zstep Rfd.                          (* a worker U: sll a2,a0,8 *)
  zsetreg (256 * eo) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; rewrite ?Z.mod_small by lia; lia).
  zstep Rfd.                          (* a worker U: add a0,a4,a2 *)
  tstep1 Rfd.                         (* a worker U: addw a2,a4,a2 *)
  zbr Rfd false.                      (* a worker U: bne a2,a0 (UBSan) *)
  clear S88 Hlast.
  Local Ltac to_rc SI HAG :=
    lazymatch type of SI with sinv _ ?st _ _ =>
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (leave_rc_t cx fin MD T M0 CX Hh OBLOW HKRL R9 [] Mx st _ _ _ SI) end end;
    first [ zreg | icx_cbn; zreg | assumption | close_std | exact HAG
          | unfold strm_at; icx_cbn; match goal with H : strm_at _ _ _ _ |- _ => unfold strm_at in H; icx_cbn; exact H end
          | match goal with |- ?G => idtac "RCSIDE" G end ].
  Local Ltac to_call CALL :=
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 _ _) _ => eapply (CALL R9) end;
    first [ zreg | icx_cbn; zreg | assumption | lazymatch goal with |- hideP _ => idtac end ].
  to_rc SI HAG.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem leave_t : KLEAVE cx fin MD T M0.
Proof.
  (* a worker W04 U: the unpatched leave stores next_in, avail_in, next_out, avail_out, hold and bits back FIRST, reloads
     out into s4, then makes the window decision and calls updatewindow; the totals, the check and data_type come
     after it (or straight after the decision when no window step is made). TOT is the totals join. *)
  Local Ltac to_dt SI HAG :=
    lazymatch type of SI with sinv _ ?st _ _ =>
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (leave_dt_t R9 [] Mx st _ _ _ SI) end end;
    first [ zreg | icx_cbn; zreg | icx_cbn; zkept | assumption | close_std | exact HAG | sbk
          | unfold s_lo; icx_cbn; split; assumption
          | match goal with |- ?G => idtac "DTSIDE" G end ].
  assert (TOT : forall Rb l M st rv lf cf,
    sinv cx st lf cf ->
    zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
    zget_l Rb l kS0 = c_p cx -> zget_l Rb l kA3 = c_u cx -> zget_l Rb l kS1 = c_u cx -> zget_l Rb l kA1 = 0 ->
    zget_l Rb l kA4 = c_osz cx - t_cout st -> zget_l Rb l kS4 = t_out st ->
    zget_l Rb l kS8 = c_n cx - t_cin st -> zget_l Rb l kS11 = rv ->
    s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> s_lo cx st M -> s_bk cx st M ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 96748 (zupd Rb l) M MD) T).
  { intros Rb l M st rv lf cf SI Lsp Lgp Ltp Ls0 La3 Ls1 La1 La4 Ls4 Ls8 Ls11 STD SAT STRM SLO SBK Hlens Hcodes HP0.
    open_std STD. open_leave CX SI st HP0.
    fp_call_frame HP0.
    pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
    dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C136f & _ & _ & _ & _ & _ & C72f & _).
    pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & Cp16 & _).
    pose proof (mem_u32_lo8_t _ _ _ Cp16) as Cp16b. cbn [Z.modulo Z.pos_div_eucl] in Cp16b. clear Cp16.
    pose proof STRM as STRM'. unfold strm_at in STRM'. icx_cbn. dand STRM' as (_ & _ & S24 & _).
    destruct (mem_wr_u64_exists_R M (c_u cx + 16) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (ti & Hti & Rti).
    destruct (mem_wr_u64_exists_R M (c_u cx + 40) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (to & Hto & Rto).
    destruct (mem_wr_u64_exists_R M (c_p cx + 48) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (tt & Htt & Rtt).
    zstep Rfd.                          (* a worker U: mv s2,a4 (left) *)
    tstep1 Rfd.                         (* a worker U: subw a2,s4,a4 (out - left) *)
    zsetreg (out - (c_osz cx - cout)) ltac:(first [lia | rewrite swrap32_small by lia; lia]).
    zstep Rfd.                          (* a worker U: ld a0 (in) *)
    tstep1 Rfd. zgen.                   (* a worker U: subw a0,a0,s8 *)
    zstep Rfd.                          (* a worker U: ld a4 (total_in) *)
    zstep Rfd.                          (* a worker U: ld a5 (total_out) *)
    zstep Rfd. zstep Rfd. zgen.         (* a worker U: zero-extend a0 *)
    zstep Rfd. zgen.                    (* a worker U: add a0,a4,a0 *)
    zstep Rfd. zstep Rfd. zext32.       (* a worker U: zero-extend a2 into a4 *)
    zstep Rfd. zgen.                    (* a worker U: add a5,a5,a4 *)
    tstep1 Rfd.                         (* a worker U: sd a0 (total_in) *)
    tstep1 Rfd.                         (* a worker U: sd a5 (total_out) *)
    zstep Rfd.                          (* a worker U: ld a0 (state total) *)
    zstep Rfd. zlit.                    (* a worker U: lbu a5 (wrap) *)
    zstep Rfd. zgen.                    (* a worker U: add a0,a0,a4 *)
    zstep Rfd. zlit.                    (* a worker U: and a5,a5,4 *)
    tstep1 Rfd.                         (* a worker U: sd a0 (state total) *)
    repeat match goal with H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (c_u cx + 16) _ |- _ => clear H
                          | H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (c_u cx + 40) _ |- _ => clear H
                          | H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (c_p cx + 48) _ |- _ => clear H end.
    try clear Hti; try clear Hto; try clear Htt. clear C72f Cp16b.
    zbr Rfd false.                      (* a worker U: beqz a5 (wrap & 4 is set) *)
    destruct (Z.eq_dec out (c_osz cx - cout)) as [Ecout|Ecout].
    - (* a worker U: out = left: no check *)
      zbr Rfd true.                     (* a worker U: beq s4,s2 *)
      to_dt SI HAG.
    - (* a worker U: the check over the bytes written by this call *)
      zbr Rfd false.                    (* a worker U: beq s4,s2 *)
      assert (Hf0 : flags = 0).
      { dand MODE_ as (_ & Mf & _). icx_cbn.
        assert (Hn1 : flags <> -1) by (intros E; destruct (Mf E) as [_ Hc]; clear Mf HKRL HKRX HKW; lia).
        clear Mf HKRL HKRX HKW. lia. }
      pose proof SAT as SAT'. destruct SAT' as [_ SREST']. unfold st_rest in SREST'. icx_cbn. dand SREST' as (_ & Cfl & _).
      rewrite Hf0 in Cfl.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        destruct (mem_wr_u64_exists_R Mx (c_p cx + 40) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (ck & Hck & Rck) end.
      zstep Rfd.                        (* a worker U: ld a1 (next_out) *)
      tstep1 Rfd.                       (* a worker U: lw a3 (flags) *)
      zstep Rfd. zbool.                 (* a worker U: snez a0,a1 *)
      zstep Rfd.                        (* a worker U: xor a5,a1,a4 *)
      zstep Rfd.                        (* a worker U: seqz a5,a5 *)
      zsetreg 0 ltac:(symmetry; apply seqz_xor_neq; lia).
      zstep Rfd. zlit.                  (* a worker U: xor a0,a0,a5 *)
      zstep Rfd. zbool.                 (* a worker U: sltu a5,a1,a4 *)
      zstep Rfd. zlit.                  (* a worker U: not a5 *)
      zstep Rfd. zlit.                  (* a worker U: and a0,a5,a0 *)
      zbr Rfd true.                     (* a worker U: beqz a3 (flags = 0: adler32) *)
      zbr Rfd false.                    (* a worker U: beqz a0 (UBSan) *)
      zstep Rfd.                        (* a worker U: ld a0 (check) *)
      zstep Rfd. zsetreg (c_ob cx + cout - (out - (c_osz cx - cout))) ltac:(lia).   (* a worker U: sub a1,a1,a4 *)
      clear Cfl.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        destruct (mem_wr_arr_exists_R Mx (c_ob cx) (c_osz cx) Wob ltac:(lia) ltac:(lia) ltac:(lia)) as (fo & HOB & Hfo) end.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        pose proof (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 1 Mx (c_ob cx) (c_osz cx) fo (cout - (out - (c_osz cx - cout))) (out - (c_osz cx - cout)) HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc end.
      replace (c_ob cx + 1 * (cout - (out - (c_osz cx - cout)))) with (c_ob cx + cout - (out - (c_osz cx - cout))) in Hsrc by lia.
      zstep Rfd.                        (* a worker U: jal adler32 *)
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?lc) ?Mx _) _ =>
        eapply (ADLER R' lc Mx MD T ck (c_ob cx + cout - (out - (c_osz cx - cout))) (out - (c_osz cx - cout)) (out - (c_osz cx - cout)) (c_u cx + -256) _
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
      tstep1 Rfd.                       (* a worker U: sd a0 (state check) *)
      zstep Rfd.                        (* a worker U: mv a3,s1 *)
      tstep1 Rfd.                       (* a worker U: sd a0 (strm adler) *)
      zstep Rfd.                        (* a worker U: ld a1 (flush) *)
      to_dt SI HAG. }
  intros R M st rv lf cf SI RE STD SAT SLO SBK Hlens Hcodes HPl.
  pose proof (fp_call_widen cx M0 M HPl) as HP0. clear HPl.
  open_std STD. unfold s_regs_leave in RE. destr_conj RE. zgetl_nil. open_leave CX SI st HP0.
  fp_call_frame HP0.
  pose proof SLO as SLO'. unfold s_lo in SLO'. icx_cbn. destruct SLO' as [HL HO].
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn.
  dand CST' as (C64 & C88 & Cp0 & Cp16 & Cp48 & Cp56 & Cp60 & Cp72 & Cp7144).
  pose proof SAT as SAT'. destruct SAT' as [Hmode _]. icx_cbn.
  (* a worker U: the stores back into the stream and the state, then out into s4 *)
  tstep1 Rfd.                         (* a worker U: lw a0 (wsize) *)
  tstep1 Rfd.                         (* a worker U: sd s10 (next_in) *)
  tstep1 Rfd.                         (* a worker U: sw s8 (avail_in) *)
  tstep1 Rfd.                         (* a worker U: sd s3 (next_out) *)
  zstep Rfd.                          (* a worker U: ld a4 (left) *)
  tstep1 Rfd.                         (* a worker U: sw a4 (avail_out) *)
  tstep1 Rfd.                         (* a worker U: sd s4 (hold) *)
  tstep1 Rfd.                         (* a worker U: sw s2 (bits) *)
  zstep Rfd.                          (* a worker U: ld s4 (out) *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    assert (STRM : strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) Mx)
      by (unfold strm_at; icx_cbn; split_conj; assumption) end.
  repeat match goal with H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (c_u cx) _ |- _ => clear H
                        | H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (c_u cx + 8) _ |- _ => clear H
                        | H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (c_u cx + 24) _ |- _ => clear H
                        | H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (c_u cx + 32) _ |- _ => clear H
                        | H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (c_p cx + 96) _ |- _ => clear H
                        | H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (c_p cx + 104) _ |- _ => clear H end.
  (* a worker U: the window step (updatewindow), at L_UW_ARGS_T *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (CALL : forall RJ,
    zget RJ kSP = c_u cx + -256 -> zget RJ kGP = c_K cx kGP -> zget RJ kTP = c_K cx kTP ->
    zget RJ kS0 = c_p cx -> zget RJ kA3 = c_u cx -> zget RJ kS1 = c_u cx ->
    zget RJ kS2 = bits -> zget RJ kS3 = c_ob cx + cout -> zget RJ kS4 = out -> zget RJ kA4 = c_osz cx - cout ->
    zget RJ kS8 = c_n cx - cin -> zget RJ kS10 = c_q cx + cin -> zget RJ kS11 = rv ->
    hideP (c_w cx = 0 -> c_cout0 cx < cout /\ mode <= DONE) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_ARGS_T (zupd RJ []) Mc MD) T) end.
  { intros RJ. intros. zimps. zkeys. unfold L_UW_ARGS_T.
    match goal with H : hideP _ |- _ => rename H into WHY end.
    tstep1 Rfd.                       (* a worker U: subw a2,s4,a4 (out - left) *)
    zsetreg (out - (c_osz cx - cout)) ltac:(first [lia | rewrite swrap32_small by lia; lia]).
    zstep Rfd.                        (* a worker U: mv a0,a3 *)
    zstep Rfd.                        (* a worker U: mv a1,s3 *)
    zstep Rfd.                        (* a worker U: jal updatewindow *)
    pose proof SAT as SAT'. destruct SAT' as [Hmode' SREST']. unfold st_rest in SREST'. icx_cbn. destr_conj SREST'. clear SAT.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      destruct (mem_wr_arr_exists_R Mx (c_ob cx) (c_osz cx) Wob ltac:(lia) ltac:(lia) ltac:(lia)) as (fo & HOB & Hfo) end.
    pose proof WIN_ as WIN'. unfold WIN in WIN'. icx_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?lc) ?Mx _) _ =>
      eapply (uw_entry_t MEMCPY R' lc Mx MD T (c_u cx) (c_p cx) (c_ob cx) (c_osz cx) (c_w cx) whave wnext cout (out - (c_osz cx - cout))
                (c_u cx + -256) L_UW_RET (c_p cx) (c_u cx) bits (c_ob cx + cout) out (zget_l R' lc kS5) (c_zc cx) fo Hh) end;   (* a worker W04 U: inflate's s0 .. s5 = p, strm, bits, put, out, v4 *)
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
    - (* a worker U: no window yet: updatewindow calls zcalloc (KW) *)
      intros R' M' Hw0. unfold hideP in WHY. destruct (WHY Hw0) as [WHY1 WHY2]. intros. zimps. zkeys.
      match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) _ M' _ |- _ => zreattachL HP end.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
        eapply (HKW R9 Mx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  rv _ _ lf cf Hw0 SI WHY1 WHY2) end;
        first [ zreg | icx_cbn; zreg | icx_cbn; zkept | assumption
              | match goal with H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v |- mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a' _ =>
                  replace a' with a by lia_std; first [exact H | cbv [L_UW_RET]; exact H] end
              | close_std | unfold st_at, st_rest; icx_cbn; split_conj; assumption | exact HAG
              | match goal with |- ?G => idtac "KWSIDE" G end ].
    - (* a worker U: the window exists: updatewindow returns to L_UW_RET (s0, s1, s4 restored) *)
      intros R' M' whave' wnext' Hw. intros. zimps. zkeys.
      rewrite ((proj2 (proj2 (wsz_facts cx))) Hw) in *. cbv [WIN_SIZE] in *.
      clear Cp60 Cp72.
      clear CST.
      match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) _ M' _ |- _ => unfold uw_fp in HP; cbv [WIN_SIZE] in HP; zreattachL HP end.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
        eapply (leave_uwret_t cx fin MD T M0 CX Hh OBLOW ADLER HKRL HKRX R9 [] Mx
                  (set_win (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) whave' wnext')
                  rv 0 lf cf) end;
        first [ zreg | icx_cbn; zreg | icx_cbn; zkept | unfold set_win; icx_cbn; zreg | left; reflexivity | assumption | sbk
              | apply sinv_set_win; [exact SI | exact Hw | assumption ..]
              | unfold s_std, i_cst; rewrite ((proj2 (proj2 (wsz_facts cx))) Hw); cbv [WIN_SIZE]; icx_cbn; split_conj; assumption
              | unfold st_at, st_rest, set_win; icx_cbn; split_conj; assumption
              | unfold strm_at, set_win; icx_cbn; match goal with H : strm_at _ _ _ _ |- _ => unfold strm_at in H; icx_cbn; exact H end
              | unfold s_lo, set_win; icx_cbn; match goal with H : s_lo _ _ _ |- _ => unfold s_lo in H; icx_cbn; exact H end
              | unfold fp_call; rewrite ((proj2 (proj2 (wsz_facts cx))) Hw); exact HAG
              | match goal with |- ?G => idtac "UWRETSIDE" G end ]. }
  destruct (Z.eq_dec (c_w cx) 0) as [Hw0 | Hw1].
  - (* a worker U: no window allocated yet: L_LNOWIN_T *)
    pose proof ((proj1 (proj2 (wsz_facts cx))) Hw0) as Hz.
    zbr Rfd true.                     (* a worker U: beqz a0 (wsize = 0) *)
    destruct (Z.eq_dec out (c_osz cx - cout)) as [Ec|Ec].
    + zbr Rfd true.                   (* a worker U: beq s4,a4 (nothing written): the totals *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
        eapply (TOT R9 [] Mx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) rv lf cf SI) end;
        first [ zreg | icx_cbn; zreg | assumption | close_std | exact HAG | sbk | match goal with |- ?G => idtac "TOTSIDE" G end ].
    + zbr Rfd false.                  (* a worker U: beq s4,a4 *)
      tstep1 Rfd.                     (* a worker U: lw a0 (mode) *)
      zstep Rfd.                      (* a worker U: lui a2 *)
      zstep Rfd. zlit.                (* a worker U: addw a2 (BAD - 1) *)
      destruct (Z_lt_dec 16208 mode) as [Hm|Hm].
      * zbr Rfd true.                 (* a worker U: bltu (mode past DONE): the totals *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
          eapply (TOT R9 [] Mx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) rv lf cf SI) end;
          first [ zreg | icx_cbn; zreg | assumption | close_std | exact HAG | sbk | match goal with |- ?G => idtac "TOTSIDE" G end ].
      * zbr Rfd false.                (* a worker U: bltu *)
        zstep Rfd.                    (* a worker U: li a2,4 *)
        zbr Rfd true.                 (* a worker U: bne a1,a2 (flush is not Z_FINISH): the window step *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?R9 _ _) _ => eapply (CALL R9) end;
          first [ zreg | icx_cbn; zreg | assumption | lazymatch goal with |- hideP _ => idtac end ].
        unfold hideP. intros _. cbv [DONE]. destruct PR3 as [PR3 | [PR3 _]]; split; lia.
  - (* a worker U: the window exists: the window step *)
    pose proof ((proj2 (proj2 (wsz_facts cx))) Hw1) as Hz. cbv [WIN_SIZE] in Hz.
    zbr Rfd false.                    (* a worker U: beqz a0 (wsize <> 0) *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 _ _) _ => eapply (CALL R9) end;
      first [ zreg | icx_cbn; zreg | assumption | lazymatch goal with |- hideP _ => idtac end ].
    unfold hideP. intros E. exfalso. exact (Hw1 E).
Qed.
End Leave.
End T_Leave.

Module T_Inflate.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import T_Uw OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.TBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_Entry.T_Loop T_Ret OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_Entry T_LeaveA T_Leave.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Section Inflate.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet).
Hypothesis CX : ctx_ok ROMHI_T cx.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < c_n cx -> 0 <= fin i < 256.
Hypothesis OBLOW : c_ob cx + c_osz cx <= c_u cx - FRA.
Hypothesis MEMCPY : memcpy_spec_t.
Hypothesis ADLER : adler32_spec_t.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma kret_of_krx_t : forall M0, KRX cx fin MD T M0 -> KRET cx fin MD T M0.
Proof.
  intros M0 KX R M rc m Hrc RE STD Hm Hr HP0.
  pose proof STD as STD'. dand STD' as (_ & _ & _ & _ & _ & FRM & _).
  eapply (ret_t cx R [] M MD T rc CX Hh RE FRM).
  intros R9 HB. eapply (KX R9 M rc m Hrc HB STD Hm Hr). apply fp_call_widen. exact HP0.
Qed.

Theorem inflate_t : forall Rb l M st lf cf,
  ainv cx st lf cf -> c_cin0 cx = t_cin st -> c_cout0 cx = t_cout st -> c_W0 cx = Wm cx st ->
  s_regs_entry cx Rb l -> e_mem cx fin st lf cf M ->
  KRL cx fin MD T M -> KRX cx fin MD T M -> KW cx fin MD T M ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_INFLATE (zupd Rb l) M MD) T.
Proof.
  intros Rb l M st lf cf AI H1 H2 H3 RE EM HKRL HKRX HKW.
  eapply (entry_t cx fin MD T Rb l M st lf cf CX Hh Hfin AI H1 H2 H3 RE EM).
  pose proof (leave_t cx fin MD T M CX Hh OBLOW MEMCPY ADLER HKRL HKRX HKW) as HKL.
  pose proof (kret_of_krx_t M HKRX) as HKR.
  pose proof (kall_t cx fin MD T M CX Hh Hfin HKL HKR A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY
                A_TABLE A_LENLENS A_CODELENS A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT OBLOW A_CHECK A_LENGTH
                (meas cx (st_load cx st) + 1)) as KA.
  open_K KA. exact KD.
Qed.
End Inflate.
End T_Inflate.

Module T_U2B.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.TBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_Entry.T_Loop.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* a worker 1.4 UBSan: uncompress2_z's exit is new code at 1.4, the same instructions as the plain build's (its UBSan
   checks are all at entry): *sourceLen -= len + avail_in; *destLen -= left + avail_out; err kept in s0 over
   inflateEnd. inflateEnd (with its UBSan alignment checks) is 1.3.1's code at new addresses. s5 rides through. *)
Definition L_EXIT : Z := 85888.    (* 0x14e88: uncompress2_z's exit from the inflate loop *)
Definition T_ZE1 : Z := 97772.     (* 0x17cc4: inflateEnd, jalr zfree for the window *)
Definition T_ZE2 : Z := 97796.     (* 0x17cdc: inflateEnd, jalr zfree for the state *)
Definition RA2 : Z := 85940.       (* 0x14ebc: uncompress2_z after jal inflateEnd *)

(* [comment removed for export] *)
Ltac zgen :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => let x' := fresh "gv" in set (x' := e); clearbody x'
  end.

Theorem u2_exit_t {RCa1 : RunCtx}  : forall Rb l M MD T (u p w rc len left m zc : Z) (gp tp s5 s6 s7 s8 s9 s10 s11 : Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u -> zget_l Rb l kA0 = rc -> zget_l Rb l kS0 = u + 176 -> zget_l Rb l kS1 = u + 168 ->
  zget_l Rb l kS3 = len -> zget_l Rb l kS4 = left -> zget_l Rb l kS5 = s5 ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp ->
  zget_l Rb l kS6 = s6 -> zget_l Rb l kS7 = s7 -> zget_l Rb l kS8 = s8 -> zget_l Rb l kS9 = s9 ->
  zget_l Rb l kS10 = s10 -> zget_l Rb l kS11 = s11 ->
  zc + FRA <= u -> DATA_LO + DATA_LEN <= zc -> u + 208 <= 140737488355328 -> u mod 16 = 0 -> 0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 <= w -> w + WIN_SIZE <= zc -> reach m ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 64) A_ZCALLOC -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 72) A_ZCFREE ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M p u -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 8) m -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) w ->
  (* [comment removed for export] *)
  (forall R' M', w = 0 ->
     zget R' kA3 = A_ZCFREE -> zget R' kA1 = p -> zget R' kA0 = 0 -> zget R' kS0 = u -> zget R' kSP = u + -16 ->
     zget R' kGP = gp -> zget R' kTP = tp -> zget R' kS5 = s5 ->
     zget R' kS6 = s6 -> zget R' kS7 = s7 -> zget R' kS8 = s8 -> zget R' kS9 = s9 -> zget R' kS10 = s10 -> zget R' kS11 = s11 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -8) RA2 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 80) 0 ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(u + -16, 16); (u + 168, 8); (u + 176, 8)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE2 (zupd R' []) M' MD) T) ->
  (* [comment removed for export] *)
  (forall R' M', w <> 0 ->
     zget R' kA3 = A_ZCFREE -> zget R' kA1 = w -> zget R' kA0 = 0 -> zget R' kS0 = u -> zget R' kSP = u + -16 ->
     zget R' kGP = gp -> zget R' kTP = tp -> zget R' kS5 = s5 ->
     zget R' kS6 = s6 -> zget R' kS7 = s7 -> zget R' kS8 = s8 -> zget R' kS9 = s9 -> zget R' kS10 = s10 -> zget R' kS11 = s11 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -8) RA2 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 80) 0 ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(u + -16, 16); (u + 168, 8); (u + 176, 8)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE1 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_EXIT (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u p w rc len left m zc gp tp s5 s6 s7 s8 s9 s10 s11
         Hh Lsp La0 Ls0 Ls1 Ls3 Ls4 Ls5 Lgp Ltp Ls6 Ls7 Ls8 Ls9 Ls10 Ls11
         Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hw0 Hw1 Hm Wstk Wp C64 C72 C80 C88 Cp0 Cp8 Cp72 KNW KW.
  zkeysb. unfold L_EXIT, T_ZE1, T_ZE2, RA2 in *. cbv [STATE_SIZE FRA WIN_SIZE A_ZCALLOC A_ZCFREE BUF DATA_LO DATA_LEN] in *.
  pose proof two64_eq as TW64. pose proof (reach_bounds' := Hm). unfold reach in reach_bounds'. cbv [HEAD DICTID MEM] in reach_bounds'.
  assert (Hmb : 16180 <= m <= 16210) by lia_std. clear reach_bounds'.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(u + -16, 16); (u + 168, 8); (u + 176, 8)] ltac:(ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(u + -16, 16); (u + 168, 8); (u + 176, 8)]) M) by (apply mpostL_refl).
  (* the current avail_in, *sourceLen, avail_out and *destLen *)
  destruct (mem_wr_u32_exists_R M (u + 8) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (vai & Hai & Rai).
  destruct (mem_wr_u64_exists_R M (u + 168) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (vsl & Hsl & Rsl).
  destruct (mem_wr_u32_exists_R M (u + 32) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (vao & Hao & Rao).
  destruct (mem_wr_u64_exists_R M (u + 176) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (vdl & Hdl & Rdl).
  zstep Rfd.                          (* 14e88 lwu a1,8(sp) *)
  zstep Rfd.                          (* 14e8c ld a2,0(s1) *)
  zstep Rfd.                          (* 14e90 lwu a3,32(sp) *)
  zstep Rfd. zgen.                    (* 14e94 add s3,s3,a1 *)
  zstep Rfd. zgen.                    (* 14e98 sub a1,a2,s3 *)
  zstep Rfd.                          (* 14e9c sd a1,0(s1) *)
  zstep Rfd.                          (* 14ea0 ld a1,0(s0) *)
  zstep Rfd. zgen.                    (* 14ea4 add a3,s4,a3 *)
  zstep Rfd. zgen.                    (* 14ea8 sub a1,a1,a3 *)
  zstep Rfd.                          (* 14eac sd a1,0(s0) *)
  zstep Rfd.                          (* 14eb0 mv s0,a0 *)
  zstep Rfd.                          (* 14eb4 mv a0,sp *)
  zstep Rfd.                          (* 14eb8 jal inflateEnd *)
  (* inflateEnd (0x17c50), the 1.3.1 UBSan walk: the strm / state checks with UBSan's alignment traps, then the frame *)
  zstep Rfd.                          (* mv a2,a0 *)
  zstep Rfd.                          (* li a0,-2 *)
  zbr Rfd false.                      (* beqz a2 *)
  zstep Rfd. zalign.                  (* and a1,a2,7 *)
  zbr Rfd false.                      (* bnez a1 *)
  zstep Rfd. zbr Rfd false.           (* ld a1,64(a2); beqz a1 *)
  zstep Rfd. zbr Rfd false.           (* ld a3,72(a2); beqz a3 *)
  zstep Rfd. zbr Rfd false.           (* ld a1,56(a2); beqz a1 *)
  zstep Rfd. zalign.                  (* and a4,a1,7 *)
  zbr Rfd false.                      (* bnez a4 *)
  zstep Rfd. zbr Rfd true.            (* ld a4,0(a1); beq a4,a2 *)
  tstep1 Rfd.                         (* lw a4,8(a1) *)
  zstep Rfd. zstep Rfd. zlit.         (* lui a5; addi a5,a5,204 *)
  tstep1 Rfd.                         (* addw a4,a4,a5 *)
  zstep Rfd.                          (* li a5,31 *)
  zbr Rfd false.                      (* bltu a5,a4 *)
  zstep Rfd.                          (* addi sp,sp,-16 *)
  tstep1 Rfd.                         (* sd ra,8(sp) *)
  tstep1 Rfd.                         (* sd s0,0(sp) *)
  zstep Rfd.                          (* ld a1,88(a1) *)
  destruct (Z.eq_dec w 0) as [Wz | Wnz].
  - revert Cp72. subst w. intros Cp72.
    zbr Rfd true.                     (* beqz a1: no window *)
    zstep Rfd.                        (* ld a1,56(a2) *)
    zstep Rfd.                        (* ld a3,72(a2) *)
    zstep Rfd.                        (* ld a0,80(a2) *)
    zstep Rfd.                        (* mv s0,a2 *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => apply (KNW R' Mx eq_refl) end; try zreg; try assumption.
  - zbr Rfd false.                    (* beqz a1 *)
    zstep Rfd.                        (* ld a0,80(a2) *)
    zstep Rfd.                        (* mv s0,a2 *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => apply (KW R' Mx Wnz) end; try zreg; try assumption.
Qed.
End T_U2B.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U Require Import TBase. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U Require T_Entry. Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_Entry.T_Loop. Import T_Ret. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U Require Import T_Entry. Import T_Uw. Import T_LeaveA. Import T_Leave. Import T_Inflate. Import T_U2B.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_TAIL : Z := 85876.    (* a worker 1.4 UBSan: 0x14e7c *)
Definition L_C1 : Z := 85792.      (* a worker 1.4 UBSan: 0x14e28 *)
Definition L_C2 : Z := 85860.      (* a worker 1.4 UBSan: 0x14e6c *)
Definition RA_C1 : Z := 85804.     (* [comment removed for export] *)
Definition RA_C2 : Z := 85872.     (* [comment removed for export] *)
Definition pc_site (site : bool) : Z := if site then L_C1 else L_C2.
Definition ra_site (site : bool) : Z := if site then RA_C1 else RA_C2.

Section U2.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variables (u p q n gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z) (MD : Model) (T : TSet) (Mza : mem).
(* [comment removed for export] *)
Variable zc : Z.
(* (uncompress3 1.4 UBSan): the output budget osz = the harness's destLen, 0 .. BUF_N (0 is the zm
   case), in the shape of a worker's 1.4 I8S (dest stays BUF); uncompress / uncompress2 had osz = BUF_N fixed. *)
Variable osz : Z.
Hypothesis Hosz : 0 <= osz <= 262144.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < n -> 0 <= fin i < 256.
Hypothesis Hu0 : zc + FRA <= u. Hypothesis Hzimg : DATA_LO + DATA_LEN <= zc. Hypothesis Hu1 : u + 208 <= 140737488355328. Hypothesis Hua : u mod 16 = 0.
Hypothesis Hp0 : 0 < p. Hypothesis Hp1 : p + STATE_SIZE <= zc. Hypothesis Hpa : p mod 16 = 0.
Hypothesis Hq1 : 1 <= q. Hypothesis Hn0 : 0 <= n. Hypothesis Hn1 : n < 67108864. Hypothesis Hqn : q + n <= zc.
Hypothesis Spq : ZSEP (p + STATE_SIZE <= q \/ q + n <= p).
Hypothesis Spob : ZSEP (p + STATE_SIZE <= BUF \/ BUF + 262144 <= p).
Hypothesis Sobq : ZSEP (BUF + 262144 <= q \/ q + n <= BUF).
Hypothesis Sprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_T <= p).
Hypothesis Rgp : 0 <= gp < two64. Hypothesis Rtp : 0 <= tp < two64.
Hypothesis Rs5 : 0 <= s5 < two64. Hypothesis Rs6 : 0 <= s6 < two64. Hypothesis Rs7 : 0 <= s7 < two64. Hypothesis Rs8 : 0 <= s8 < two64.
Hypothesis Rs9 : 0 <= s9 < two64. Hypothesis Rs10 : 0 <= s10 < two64. Hypothesis Rs11 : 0 <= s11 < two64.
Hypothesis MEMCPY : memcpy_spec_t.
Hypothesis ADLER : adler32_spec_t.
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

(* [comment removed for export] *)
Definition Kra (ra : Z) (k : positive) : Z :=
  if (k =? kRA)%positive then ra else if (k =? kSP)%positive then u
  else if (k =? kGP)%positive then gp else if (k =? kTP)%positive then tp
  else if (k =? kS0)%positive then u + 176 else if (k =? kS1)%positive then u + 168
  else if (k =? kS2)%positive then 4294967295 else if (k =? kS3)%positive then 0 else if (k =? kS4)%positive then 0
  else if (k =? kS5)%positive then s5
  else if (k =? kS6)%positive then s6 else if (k =? kS7)%positive then s7 else if (k =? kS8)%positive then s8
  else if (k =? kS9)%positive then s9 else if (k =? kS10)%positive then s10 else if (k =? kS11)%positive then s11
  else 0.
(* [comment removed for export] *)
Definition cxc (w cin cout W0 ra : Z) : ictx := ICX u p q n BUF osz w cin cout W0 (Kra ra) zc.
(* [comment removed for export] *)
Definition wok (w : Z) : Prop :=
  0 <= w /\ w + WIN_SIZE <= zc /\ w mod 16 = 0 /\
  ZSEP (w = 0 \/ (p + STATE_SIZE <= w \/ w + WIN_SIZE <= p)) /\ ZSEP (w = 0 \/ (w + WIN_SIZE <= q \/ q + n <= w)) /\
  ZSEP (w = 0 \/ (w + WIN_SIZE <= BUF \/ BUF + 262144 <= w)) /\ ZSEP (w = 0 \/ (w + WIN_SIZE <= ROM_LO_ALL \/ ROMHI_T <= w)).

Lemma ctx_ok_cxc : forall w cin cout W0 ra,
  wok w -> 0 <= cin <= n -> 0 <= cout <= osz -> (ra = RA_C1 \/ ra = RA_C2) ->
  ctx_ok ROMHI_T (cxc w cin cout W0 ra).
Proof.
  intros w cin cout W0 ra (W1 & W2 & W3 & W4 & W5 & W6 & W7) Hcin Hcout Hra.
  unfold ZSEP in *. pose proof two64_eq as TW64.
  unfold ctx_ok, ctx_lin, ctx_al, ctx_sep, cxc, Kra; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_T BUF DATA_LO DATA_LEN] in *.
  cbv [kRA kSP kGP kTP kS0 kS1 kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11]. cbn [Pos.eqb].
  (* [comment removed for export] *)
  split; [| split]; split_conj; try assumption; try lia;
    unfold RA_C1, RA_C2 in Hra; destruct Hra as [-> | ->]; first [reflexivity | lia | lia_std].
Qed.

(* [comment removed for export] *)
Definition u2regs (R : tree Z) : Prop :=
  zget R kSP = u /\ zget R kS0 = u + 176 /\ zget R kS1 = u + 168 /\ zget R kS2 = 4294967295 /\ zget R kS3 = 0 /\ zget R kS4 = 0 /\
  zget R kS5 = s5 /\ zget R kGP = gp /\ zget R kTP = tp /\
  zget R kS6 = s6 /\ zget R kS7 = s7 /\ zget R kS8 = s8 /\ zget R kS9 = s9 /\ zget R kS10 = s10 /\ zget R kS11 = s11.

(* [comment removed for export] *)
Definition fp_u2 (w : Z) : list (Z * Z) :=
  [(u + -1024, 1136); (u + 168, 8); (u + 176, 8); (p, STATE_SIZE); (BUF, osz); (w, if w =? 0 then 0 else WIN_SIZE)].

(* [comment removed for export] *)
Definition Wv (st : ist) : Z := 8 * (n - t_cin st) + t_bits st + (osz - t_cout st).
Definition M2v (st : ist) : Z := Wv st * 134217728 + (n - t_cin st).

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable wph : Z.
Hypothesis Hwph : wok wph.

Definition KZE2 : Prop := forall (R : tree Z) (M : mem),
  zget R kA3 = A_ZCFREE -> zget R kA1 = p -> zget R kA0 = 0 -> zget R kS0 = u -> zget R kSP = u + -16 ->
  zget R kGP = gp -> zget R kTP = tp -> zget R kS5 = s5 ->
  zget R kS6 = s6 -> zget R kS7 = s7 -> zget R kS8 = s8 -> zget R kS9 = s9 -> zget R kS10 = s10 -> zget R kS11 = s11 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -8) RA2 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 ->
  wph = 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza M (fp_u2 wph) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE2 (zupd R []) M MD) T.
Definition KZE1 : Prop := forall (R : tree Z) (M : mem),
  zget R kA3 = A_ZCFREE -> zget R kA1 = wph -> zget R kA0 = 0 -> zget R kS0 = u -> zget R kSP = u + -16 ->
  zget R kGP = gp -> zget R kTP = tp -> zget R kS5 = s5 ->
  zget R kS6 = s6 -> zget R kS7 = s7 -> zget R kS8 = s8 -> zget R kS9 = s9 -> zget R kS10 = s10 -> zget R kS11 = s11 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -8) RA2 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 ->
  wph <> 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza M (fp_u2 wph) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE1 (zupd R []) M MD) T.
(* [comment removed for export] *)
Definition KZW : Prop := forall (R : tree Z) (M : mem) (cin0 cout0 W0 ra : Z) (st : ist) (rv v4 v5 : Z) (lf cf : Z -> Z),
  let cx := cxc 0 cin0 cout0 W0 ra in
  (ra = RA_C1 \/ ra = RA_C2) -> 0 <= cin0 <= n -> 0 <= cout0 <= osz ->
  sinv cx st lf cf -> cout0 < t_cout st -> t_mode st <= DONE ->
  zget R kA3 = A_ZCALLOC -> zget R kA0 = 0 -> zget R kA1 = WIN_SIZE -> zget R kA2 = 1 ->
  zget R kS0 = BUF + t_cout st -> zget R kS1 = t_out st - (osz - t_cout st) -> zget R kS2 = 1 -> zget R kS3 = p ->
  zget R kS4 = t_out st -> zget R kS5 = v4 ->
  zget R kSP = u + -320 -> zget R kGP = gp -> zget R kTP = tp ->
  zget R kS6 = v5 -> zget R kS8 = n - t_cin st -> zget R kS10 = q + t_cin st -> zget R kS11 = rv ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -264) L_UW_RET -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -272) p ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -280) u -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -288) (t_bits st) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -296) (BUF + t_cout st) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -304) (t_out st) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -312) v4 ->
  s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> s_lo cx st M -> s_bk cx st M ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) N_CODES cf ->
  wph = 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza M (fp_u2 0) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZW (zupd R []) M MD) T.
Hypothesis HZE2 : KZE2.
Hypothesis HZE1 : KZE1.
Hypothesis HZW : KZW.

(* [comment removed for export] *)
Definition PCALL (B : Z) : Prop := forall (site : bool) (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
  let cx := cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site) in
  ainv cx st lf cf -> M2v st < B ->
  u2regs R -> e_mem cx fin st lf cf M -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza M (fp_u2 wph) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (pc_site site) (zupd R []) M MD) T.

Local Ltac open_u2 :=
  unfold ZSEP in Spq, Spob, Sobq, Sprom;
  zkeysb; unfold L_TAIL, L_C1, L_C2, RA_C1, RA_C2, L_EXIT, L_INFLATE, T_ZE1, T_ZE2, T_ZW, RA2 in *;
  cbv [STATE_SIZE FRA WIN_SIZE ROM_LO_ALL A_ZCALLOC A_ZCFREE BUF DATA_LO DATA_LEN] in *;
  pose proof two64_eq as TW64.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u2_tail_s : forall R M st lf cf (ra : Z),
  let cx := cxc wph (t_cin st) (t_cout st) (Wv st) ra in
  ainv cx st lf cf -> u2regs R -> e_mem cx fin st lf cf M ->
  (forall (site : bool) R' M',
     u2regs R' -> e_mem cx fin st lf cf M' -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(u + 8, 4); (u + 32, 4)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (pc_site site) (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TAIL (zupd R []) M MD) T.
Proof.
  intros R M st lf cf ra cx AI RE EM K. subst cx.
  pose proof AI as AI'. dand AI' as (RNG_ & _ & _). unfold RNG in RNG_. unfold cxc in RNG_. icx_cbn.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. destr_conj RNG_.
  unfold u2regs in RE. destr_conj RE. open_u2. unfold pc_site, L_C1, L_C2 in K.
  pose proof EM as EM'. open_emem EM'. clear ROM Wp Wob Ww CST HK Hin SAT Hlens Hcodes.
  unfold cxc in Wstk. unfold strm_at, cxc in STRM. icx_cbn. cbv [BUF] in STRM. dand STRM as (S8 & S16 & S32 & S40 & S80 & S88).
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(u + 8, 4); (u + 32, 4)] ltac:(ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(u + 8, 4); (u + 32, 4)]) M) by (apply mpostL_refl).
  (* [comment removed for export] *)
  Local Ltac fin_tail K site EM HAG :=
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => apply (K site R' Mx) end;
    [ unfold u2regs; zkeys; split_conj; zreg
    | first [ exact EM
            | repeat match goal with H : mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ |- _ => clear H end;
              lazymatch goal with |- e_mem _ _ _ _ _ ?Mx =>
                  match goal with HP : framed _ Mx |- _ =>
                    pose proof EM as EM2; unfold cxc in EM2; open_emem EM2; icx_cbn; cbv [BUF] in *;
                    let HP' := fresh in pose proof HP as HP'; unfold framed in HP'; zreattachL HP';
                    unfold e_mem, strm_at, cxc; icx_cbn; cbv [BUF]; split_conj;
                    first [ assumption
                          | match goal with H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v |- mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v' => replace v' with v by lia_std; exact H end
                          | match goal with |- ?G => idtac "TAILSIDE" G end ] end end
            | match goal with |- ?G => idtac "TAILSIDE2" G end ]
    | first [exact HAG | match goal with |- ?G => idtac "TAILSIDE3" G end ] ].
  tstep1 Rfd.                         (* [comment removed for export] *)
  destruct (Z.eq_dec cout osz) as [Eo | Eo].
  - (* [comment removed for export] *)
    zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    destruct (Z.eq_dec cin n) as [Ei | Ei].
    + zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zbr Rfd true.                   (* [comment removed for export] *)
      tstep1 Rfd.                     (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      fin_tail K false EM HAG.
    + zbr Rfd true.                   (* [comment removed for export] *)
      fin_tail K true EM HAG.
  - (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    destruct (Z.eq_dec cin n) as [Ei | Ei].
    + zbr Rfd true.                   (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zbr Rfd true.                   (* [comment removed for export] *)
      tstep1 Rfd.                     (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      fin_tail K false EM HAG.
    + zbr Rfd false.                  (* [comment removed for export] *)
      fin_tail K true EM HAG.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma fp_call_u2 : forall w cin cout W0 ra M0 M,
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call (cxc w cin cout W0 ra)) ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M [(u + -1024, 1024); (u, 112); (p, STATE_SIZE); (BUF, osz); (w, if w =? 0 then 0 else WIN_SIZE)].
Proof.
  intros w cin cout W0 ra M0 M H. unfold fp_call, fp_loop, cxc, wsz in H. icx_cbn. cbv [FRA ZS_OFF ZS_SIZE] in H. cbn [app] in H.
  replace (u - 1024) with (u + -1024) in H by lia. exact H.
Qed.

Lemma fp_u2_ok : forall w, wok w -> ranges_ok (fp_u2 w).
Proof.
  intros w (W1 & W2 & _). pose proof two64_eq as TW64. unfold fp_u2. cbv [STATE_SIZE WIN_SIZE FRA BUF] in *.
  cbn [ranges_ok]. destruct (Z.eqb_spec w 0); lia_std.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Handlers.
Variable B : Z.
Hypothesis IH : PCALL B.

Lemma u2_krl : forall (site : bool) cin cout W0 Mc,
  0 <= cin <= n -> 0 <= cout <= osz ->
  M2e (cxc wph cin cout W0 (ra_site site)) <= B ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza X (fp_u2 wph)) Mc ->
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
  - (* [comment removed for export] *)
    specialize (PRG Erc).
    assert (TAIL : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TAIL (zupd R []) M MD) T).
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
    + zbr Rfd true. exact TAIL.       (* [comment removed for export] *)
    + zbr Rfd false. exact TAIL.      (* [comment removed for export] *)
  - (* [comment removed for export] *)
    assert (EXIT : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_EXIT (zupd R []) M MD) T).
    { unfold L_EXIT. pose proof EM as EM'. open_emem EM'.
      unfold i_cst, cxc in CST; icx_cbn; cbv [BUF] in CST. dand CST as (C64 & C88 & Cp0 & _ & _ & _ & _ & Cp72 & _).
      destruct HK as [C72 C80]. icx_cbn. destruct SAT as [Hmode _]. unfold cxc in Hmode; icx_cbn.
      unfold cxc in Wstk, Wp; icx_cbn.
      dand Hw as (W1 & W2 & W3 & _).
      eapply (u2_exit_t R [] M MD T u p wph rc 0 0 mode zc gp tp s5 s6 s7 s8 s9 s10 s11 Hh);
        try assumption; try zreg; try klia.
      + intros R' M' Hw0. intros. eapply (HZE2 R' M'); try eassumption.
        eapply (framed_mpostL_trans _ _ _ _ _ _ HAG); [eassumption |].
        intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac.
      + intros R' M' Hw1. intros. eapply (HZE1 R' M'); try eassumption.
        eapply (framed_mpostL_trans _ _ _ _ _ _ HAG); [eassumption |].
        intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac. }
    unfold L_EXIT in EXIT.
    destruct site; unfold ra_site, RA_C1, RA_C2 in *; unfold cxc; icx_cbn; cbv [Kra]; zkeys; cbn [Pos.eqb].
    + zbr Rfd false. zstep Rfd. exact EXIT.   (* [comment removed for export] *)
    + zbr Rfd true. exact EXIT.              (* [comment removed for export] *)
Qed.

Lemma u2_krx : forall (site : bool) cin cout W0 Mc,
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza X (fp_u2 wph)) Mc ->
  KRX (cxc wph cin cout W0 (ra_site site)) fin MD T Mc.
Proof.
  intros site cin cout W0 Mc HAG0 R M rc m Hrc HB' STD Hm Hreach HP. pose proof Hwph as Hw.
  unfold s_regs_back, cxc, Kra in HB'. icx_cbn. zkeys. cbn [Pos.eqb] in HB'. destr_conj HB'.
  apply fp_call_u2 in HP.
  pose proof (framed_mpostL_trans _ _ _ _ _ _ HAG0 HP ltac:(intros x Hx; eapply ranges_within_outside; [| exact Hx];
              unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac)) as HAG.
  clear HAG0 HP. open_u2.
  assert (EXIT : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 85888 (zupd R []) M MD) T).
  { pose proof STD as STD'. open_std STD'.
    unfold i_cst, cxc in CST; icx_cbn; cbv [BUF] in CST. dand CST as (C64 & C88 & Cp0 & _ & _ & _ & _ & Cp72 & _).
    destruct HK as [C72 C80]. unfold cxc in C72, C80, Wstk, Wp, Hm; icx_cbn.
    dand Hw as (W1 & W2 & W3 & _).
    eapply (u2_exit_t R [] M MD T u p wph rc 0 0 m zc gp tp s5 s6 s7 s8 s9 s10 s11 Hh);
      try assumption; try zreg; try klia.
    + intros R' M' Hw0. intros. eapply (HZE2 R' M'); try eassumption.
      eapply (framed_mpostL_trans _ _ _ _ _ _ HAG); [eassumption |].
      intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac.
    + intros R' M' Hw1. intros. eapply (HZE1 R' M'); try eassumption.
      eapply (framed_mpostL_trans _ _ _ _ _ _ HAG); [eassumption |].
      intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac. }
  destruct site; unfold ra_site, RA_C1, RA_C2 in *; unfold cxc; icx_cbn; cbv [Kra]; zkeys; cbn [Pos.eqb].
  - zbr Rfd false. zstep Rfd. exact EXIT.   (* [comment removed for export] *)
  - zbr Rfd true. exact EXIT.              (* [comment removed for export] *)
Qed.

Lemma u2_kw : forall (site : bool) cin cout W0 Mc,
  0 <= cin <= n -> 0 <= cout <= osz ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza X (fp_u2 wph)) Mc ->
  KW (cxc wph cin cout W0 (ra_site site)) fin MD T Mc.
Proof.
  intros site cin cout W0 Mc Hcin Hcout HAG0 R M st rv v4 v5 lf cf Hw0 SI Hc Hmd. intros.
  match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mc M _ |- _ =>
    apply fp_call_u2 in HP;
    pose proof (framed_mpostL_trans _ _ _ _ _ _ HAG0 HP ltac:(intros x Hx; eapply ranges_within_outside; [| exact Hx];
                unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac)) as HAG end.
  unfold cxc in Hw0; icx_cbn. clear HAG0.
  pose proof Hw0 as Hw0'. rewrite Hw0' in *.
  eapply (HZW R M cin cout W0 (ra_site site) st rv v4 v5 lf cf);
    first [ destruct site; [left | right]; reflexivity | exact HAG | exact Hw0 | eassumption
          | match goal with |- ?G => idtac "KWSIDE" G end ].
Qed.
End Handlers.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pcall_step : forall B, PCALL B -> PCALL (B + 1).
Proof.
  intros B IH site R M st lf cf cx AI MB RE EM HP. subst cx. pose proof Hwph as Hw.
  pose proof AI as AI'. dand AI' as (RNG_ & _ & _). unfold RNG, cxc in RNG_. icx_cbn.
  pose proof (M2v_nonneg _ _ _ _ _ _ _ _ AI) as Hnn.
  assert (Hcin : 0 <= t_cin st <= n) by (destruct st; icx_cbn; destr_conj RNG_; lia_std).
  assert (Hcout : 0 <= t_cout st <= osz) by (destruct st; icx_cbn; destr_conj RNG_; lia_std).
  clear RNG_.
  pose proof (ctx_ok_cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site) Hw Hcin Hcout
                ltac:(destruct site; [left | right]; reflexivity)) as CX.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) Mza (fp_u2 wph) (fp_u2_ok wph Hw)) as HST.
  change (framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza X (fp_u2 wph)) M) in HP. rename HP into HAG.
  unfold u2regs in RE. destr_conj RE. open_u2.
  assert (Hfin' : forall i, 0 <= i < c_n (cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site)) -> 0 <= fin i < 256) by exact Hfin.
  assert (OBLOW : c_ob (cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site)) + c_osz (cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site))
                  <= c_u (cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site)) - FRA) by (unfold cxc; icx_cbn; cbv [BUF FRA]; lia).
  destruct site; unfold pc_site, ra_site, L_C1, L_C2, RA_C1, RA_C2 in *.
  all: zstep Rfd; zstep Rfd; zstep Rfd.     (* [comment removed for export] *)
  all: lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?lc) ?Mx _) _ =>
         eapply (inflate_t _ fin MD T CX Hh Hfin' OBLOW MEMCPY ADLER
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
