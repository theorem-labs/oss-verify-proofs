(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* THE CONVERTED TEXT OF THE WALK TEXT I9S/S_ZA.v, STAGE 2a (made from the
   hand text md5 ). STAGE 1: EVERY STRETCH OF STEP LINES IS ONE RUN OF THE STURDY
   DRIVER (edition 11; only its two plain forms: a run to a continuation, a run to the next open test). No step
   count and no branch direction is written; no hint run: one value equation is stated before a run.
   STAGE 2a (this edition): NO LABEL VALUE STANDS IN THE TEXT: the text's fourteen own labels and the one pc
   that the hand text writes inline are fields of the image's layout text (the layout patch of this text). The
   labels that another text names keep name and type.
   STAGE 3 (this edition): the return place and the return-code place are lemmas of their own; the window
   callee's return place and two continuation definitions are in the list form (three register maps and one
   callee frame are fields of the layout text); between the leave entry and the return the text walks (a run
   to a continuation or to a stop; at a stop a model case split, or one relation opened for one instruction;
   on). The other statements are the hand text's, word for word. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SBase S_Entry.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZGo11 SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.

Module S_Ret.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition s_regs_back (cx : ictx) (rc : Z) (R : tree Z) : Prop :=
  zget R kA0 = rc /\ zget R kSP = c_u cx /\ zget R kRA = c_K cx kRA /\
  zget R kGP = c_K cx kGP /\ zget R kTP = c_K cx kTP /\
  zget R kS0 = c_K cx kS0 /\ zget R kS1 = c_K cx kS1 /\ zget R kS2 = c_K cx kS2 /\ zget R kS3 = c_K cx kS3 /\
  zget R kS4 = c_K cx kS4 /\ zget R kS5 = c_K cx kS5 /\ zget R kS6 = c_K cx kS6 /\ zget R kS7 = c_K cx kS7 /\
  zget R kS8 = c_K cx kS8 /\ zget R kS9 = c_K cx kS9 /\ zget R kS10 = c_K cx kS10 /\ zget R kS11 = c_K cx kS11.

Lemma ret_s {RCa1 : RunCtx}  : forall cx Rb l M MD T rc,
  ctx_ok ROMHI_S cx -> m_halted MD = None ->
  s_regs_ret cx rc Rb l -> i_frame cx M ->
  (forall R', s_regs_back cx rc R' -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (c_K cx kRA) (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_RET (zupd Rb l) M MD) T.
Proof.
  intros cx Rb l M MD T rc CX Hh RE FRM K.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  unfold s_regs_ret in RE. icx_cbn. destr_conj RE.
  unfold i_frame in FRM. icx_cbn. destr_conj FRM.
  zkeysb. unfold L_RET in *. pose proof two64_eq as TW64.
  (* ONE RUN through the function's exit to the caller's continuation *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (K R') end).
  unfold s_regs_back; icx_cbn; zkeys; split_conj; zreg.
Qed.
End S_Ret.

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZAw. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAw.

Module S_LeaveA.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry.S_Loop S_Ret OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry S_Uw.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* THE LEAVE PART's FIVE OWN LABELS ARE FIELDS OF THE IMAGE's LAYOUT TEXT (no other text names them); here
   they have their old short names only. `L_LFIN` is the place where the return code is fixed (the hand text
   writes its pc inline in an asserted statement). *)
Local Notation L_LCHECK := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LCHECK (only parsing).
Local Notation L_LDT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LDT (only parsing).
Local Notation L_UW_ARGS := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_UW_ARGS (only parsing).
Local Notation L_LNOWIN := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LNOWIN (only parsing).
Local Notation L_LRC := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LRC (only parsing).
Local Notation L_LFIN := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZA_LFIN (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation fholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds (only parsing).
Local Notation qvalv := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (only parsing).

(* OPENERS OF THE LIST FORM (they only unfold, split and name): a list-form hypothesis: the meaning over the
   layout's list is unfolded, the conjunction split and its parts named; the same for a list-form goal *)
Ltac open_za_lists :=
  repeat match goal with
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval nth fst snd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_za_fin OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_za_uwret
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_za_kw OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_za_entry] in H;
             icx_cbn; destr_conj H
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds _ _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval nth fst snd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_za_kw OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_za_entry] in H;
             icx_cbn; destr_conj H
         end.
Ltac split_za_lists :=
  lazymatch goal with
  | |- OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ =>
      cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval nth fst snd
           OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_za_fin OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_za_uwret
           OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_za_kw OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_za_entry];
      icx_cbn; split_conj
  | |- OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds _ _ _ _ _ =>
      cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width
           OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval nth fst snd
           OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_za_kw OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_za_entry];
      icx_cbn; split_conj
  | |- _ => idtac
  end.

Definition M2 (cx : ictx) (st : ist) : Z := Wm cx st * 134217728 + (c_n cx - t_cin st).
Definition M2e (cx : ictx) : Z := c_W0 cx * 134217728 + (c_n cx - c_cin0 cx).

Definition fp_call (cx : ictx) : list (Z * Z) := fp_loop cx ++ [(c_w cx, wsz cx)].

Lemma fp_call_widen {RCa1 : RunCtx}  : forall cx M0 M, mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx).
Proof.
  intros cx M0 M [HA HW]. split; [| exact HW]. intros x Hx. apply HA.
  unfold fp_call, fp_loop in *. cbn in Hx |- *. (first [solve [zkeep_section; tauto] | tauto]).
Qed.

Lemma mem_u32_lo8 {RCa1 : RunCtx}  : forall M a e, mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a e -> mem_u8 (run_segments R_segs rc_inp rc_sp rc_mb) M a (e mod 256).
Proof.
  intros M a e H. unfold mem_u32, mem_u8 in *. rewrite le4_split in H.
  pose proof (mem_is_app_l (run_segments R_segs rc_inp rc_sp rc_mb) M _ _ _ H) as H0. rewrite Z_to_le_bytes_1_mod. exact H0.
Qed.

Lemma wsz_facts : forall cx, 0 <= wsz cx <= WIN_SIZE /\ (c_w cx = 0 -> wsz cx = 0) /\ (c_w cx <> 0 -> wsz cx = WIN_SIZE).
Proof. intros cx. unfold wsz, WIN_SIZE. destruct (Z.eqb_spec (c_w cx) 0); lia. Qed.

Ltac fp_call_frame HP0 :=
  lazymatch type of HP0 with mpostL ?segs ?M0 ?M ?fp =>
    let HST := fresh "HST" in let HAG := fresh "HAG" in
    pose proof (mpostL_stable segs M0 fp ltac:(ranges_ok_tac)) as HST;
    change (framed (fun X => mpostL segs M0 X fp) M) in HP0; rename HP0 into HAG end.

Definition hideP (P : Prop) : Prop := P.

Ltac zgen :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => let x' := fresh "gv" in set (x' := e); clearbody x'
  end.

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
Context {RCa1 : RunCtx}.
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem).
Definition KRL : Prop :=
  forall (R : tree Z) (M : mem) (rc : Z) (st : ist) (lf cf : Z -> Z),
    s_regs_back cx rc R -> ainv cx st lf cf ->
    (rc mod two64 = 0 -> M2 cx st < M2e cx) -> Wm cx st <= c_W0 cx ->
    e_mem cx fin st lf cf M -> i_frame cx M ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (c_K cx kRA) (zupd R []) M MD) T.
Definition KRX : Prop :=
  forall (R : tree Z) (M : mem) (rc m : Z),
    rc mod two64 <> 0 -> s_regs_back cx rc R -> s_std cx fin M ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 8) m -> reach m ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (c_K cx kRA) (zupd R []) M MD) T.
Definition KW : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (rv : Z) (lf cf : Z -> Z),
    c_w cx = 0 -> sinv cx st lf cf -> c_cout0 cx < t_cout st -> t_mode st <= DONE ->
    rholds (qvalv cx (Some st) [rv; t_out st - (c_osz cx - t_cout st)]) R [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_za_kw ->
    fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qvalv cx (Some st) [rv; t_out st - (c_osz cx - t_cout st)]) M (c_u cx) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_za_kw ->
    s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZW (zupd R []) M MD) T.

End KDefs.

Section Leave.
Context {RCa1 : RunCtx}.
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

(* THE RETURN PLACE (the hand text asserts this statement inside a proof, with its register facts inline; here it
   is a lemma of its own: the register facts are the walk base text's own map of the return place; the memory is
   any memory with the frame, the entry memory relation and the footprint). No run: the function's exit lemma
   and the caller's continuation. *)
Lemma leave_ret_s : forall RQ Mq st rc lf cf,
  sinv cx st lf cf ->
  s_regs_ret cx rc RQ [] ->
  hideP (rc mod two64 = 0 -> t_cin st <> c_cin0 cx \/ t_out st <> c_osz cx - t_cout st) ->
  i_frame cx Mq -> e_mem cx fin st lf cf Mq ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 Mq (fp_call cx) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_RET (zupd RQ []) Mq MD) T.
Proof using CX Hh OBLOW HKRL.
  intros RQ Mq st rc lf cf SI RE PRG FRMq EMq HP0.
  pose proof HP0 as HP00. open_leave CX SI st HP0.
  eapply (ret_s cx RQ [] Mq MD T rc CX Hh).
  - exact RE.
  - exact FRMq.
  - intros R9 HB. icx_cbn.
    eapply (HKRL R9 Mq rc (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf HB).
    + dand SI as (X1 & X2 & X3 & X4). split; [exact X1 | split; [exact X2 | exact X4]].
    + intros Hrc. unfold hideP in PRG. specialize (PRG Hrc). unfold M2, M2e, Wm; icx_cbn. clear HKRL.
      destruct PR3 as [PR3 | [PR3 _]]; lia.
    + unfold Wm; icx_cbn. clear HKRL; lia.
    + exact EMq.
    + exact FRMq.
    + exact HP00.
Qed.

(* THE RETURN-CODE PLACE (the hand text asserts this statement inside a proof, with its register facts inline):
   IN THE LIST FORM. The place's label and its register map are fields of the layout; the map's two bound values
   are: value 0 = the bit that the code tests at this place, value 1 = the return value so far. *)
Lemma leave_fin_s : forall RJ Mj st rv j lf cf,
  sinv cx st lf cf ->
  rholds (qvalv cx None [j; rv]) RJ [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_za_fin ->
  hideP (j mod two64 = 0 -> rv mod two64 = 0 -> t_cin st <> c_cin0 cx \/ t_out st <> c_osz cx - t_cout st) ->
  i_frame cx Mj -> e_mem cx fin st lf cf Mj ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 Mj (fp_call cx) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LFIN (zupd RJ []) Mj MD) T.
Proof using CX Hh OBLOW HKRL.
  intros RJ Mj st rv j lf cf SI RH PROGRESS FRMj EMj HP0.
  open_za_lists. zgetl_nil.
  zkeysb. unfold L_LFIN. pose proof two64_eq as TW64. unfold hideP in PROGRESS.
  destruct (Z.eq_dec (j mod two64) 0) as [Ej|Ej].
  - (* ONE RUN to the return place, the return code kept *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ =>
      eapply (leave_ret_s R' Mj st rv lf cf SI) end);
      [ unfold s_regs_ret; icx_cbn; zkeys; split_conj; zreg
      | unfold hideP; intros Hrc; exact (PROGRESS Ej Hrc) | exact FRMj | exact EMj | exact HP0 ].
  - (* ONE RUN to the return place, the return code set to the source's "no progress" code *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ =>
      eapply (leave_ret_s R' Mj st (-5) lf cf SI) end);
      [ unfold s_regs_ret; icx_cbn; zkeys; split_conj; zreg
      | unfold hideP; intros Hrc; exfalso; revert Hrc; cbv; discriminate | exact FRMj | exact EMj | exact HP0 ].
Qed.

End Leave.
End S_LeaveA.

Module S_Leave.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry.S_Loop S_Ret OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry S_Uw S_LeaveA.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* the leave part's own labels, by their short names (as in the module before) *)
Local Notation L_LCHECK := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LCHECK (only parsing).
Local Notation L_LDT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LDT (only parsing).
Local Notation L_UW_ARGS := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_UW_ARGS (only parsing).
Local Notation L_LNOWIN := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LNOWIN (only parsing).
Local Notation L_LRC := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LRC (only parsing).

Section Leave.
Context {RCa1 : RunCtx}.
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

(* ================= THE LEAVE PART: THE WALK =================
   Two places have statements of their own: the function's leave entry and the window callee's return place
   (each a lemma below). Between them the text WALKS: a run goes on until one of three continuations applies
   (the check callee's entry, the window callee's entry, the return-code place) or until the driver's own
   step does not apply. There the walk helps the step and goes on:
   at a test that the facts in hand do not decide, one model case is split (the window stands or not; output
   was made in this pass or not; the mode is past the data modes or not: the first that lets the step go); at
   a load whose fact is not in hand, one closed memory relation is opened for that one instruction (the frame,
   the output count's slot, the state, the stream, the constant fields, the hooks: the first that lets the step
   go) and closed again. So no fact stays open over a store but the few that no relation holds. The stack value
   at a callee's call is the stream's address less the layout's frame size; the values that a callee saves are
   read from the registers. *)

(* the meaning words of the list form, by their short names *)
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation qvalv := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (only parsing).

(* a cheap test for a handed-in application: the run stands at this place (else the application is not tried) *)
Local Ltac za_pc_is lbl :=
  lazymatch goal with |- realizes _ (zcfg _ ?pc _ _ _) _ =>
    let b := eval cbv in (Z.eqb pc lbl) in lazymatch b with true => idtac end end.

(* LOCAL WALK RUN (asked of the driver's owner as a run form "to a continuation or to the first instruction
   that the driver's step does not take"): the handed-in application is tried, else ONE instruction is taken by
   the driver's own one-instruction word, and so on; where that word does not apply the run STOPS THERE with
   success (the lines after help it). THE NUMERAL 400 is the run's fuel. *)
Local Ltac za_run_n tac n :=
  lazymatch n with
  | O => fail "the walk's fuel is spent before a continuation or a stop"
  | S ?m => tryif once tac then idtac else tryif once (zgo_one Rfd) then za_run_n tac m else idtac
  end.
Local Ltac za_run tac := let n := eval cbv in 400%nat in za_run_n tac n.
(* ONE instruction by the driver's own word (it must apply) *)
Local Ltac za_step := once (zgo_one Rfd).
(* the instruction at this place is a test *)
Local Ltac za_at_test :=
  let pc := zpc in
  Rfd pc ltac:(fun F E D =>
    lazymatch type of D with
    | decode_any _ = Some (Branch _ _ _ _, _) => idtac
    | _ => fail
    end).

(* THE CLOSED MEMORY RELATIONS, each opened as a copy at a given memory (they only unfold, split and name) *)
Local Ltac za_open_frame_at Mx :=
  match goal with H : i_frame cx Mx |- _ =>
    let X := fresh "FRo" in pose proof H as X; unfold i_frame in X; icx_cbn; destr_conj X end.
Local Ltac za_open_out_at Mx :=
  match goal with H : s_out cx _ Mx |- _ =>
    let X := fresh "SOo" in pose proof H as X; unfold s_out in X; icx_cbn end.
Local Ltac za_open_state_at Mx :=
  match goal with H : st_at _ cx _ Mx |- _ =>
    let X := fresh "SAo" in let Y := fresh "SRo" in
    pose proof H as X; destruct X as [X Y]; unfold st_rest in Y; icx_cbn; destr_conj Y end.
Local Ltac za_open_strm_at Mx :=
  match goal with H : strm_at _ cx _ Mx |- _ =>
    let X := fresh "STo" in pose proof H as X; unfold strm_at in X; icx_cbn; destr_conj X end.
Local Ltac za_open_cst_at Mx :=
  match goal with H : i_cst _ cx Mx |- _ =>
    let X := fresh "CSo" in pose proof H as X; unfold i_cst in X; icx_cbn; destr_conj X;
    repeat match goal with B : mem_u32 _ Mx (c_p cx + 16) _ |- _ =>
             let Y := fresh "CBo" in
             pose proof (mem_u32_lo8 _ _ _ B) as Y; cbn [Z.modulo Z.pos_div_eucl] in Y; clear B end end.
Local Ltac za_open_hooks_at Mx :=
  match goal with H : i_hooks cx Mx |- _ =>
    let X := fresh "HKo" in pose proof H as X; unfold i_hooks in X; icx_cbn; destr_conj X end.
Local Ltac za_open_all_at Mx :=
  try (za_open_frame_at Mx); try (za_open_out_at Mx); try (za_open_state_at Mx);
  try (za_open_strm_at Mx); try (za_open_cst_at Mx); try (za_open_hooks_at Mx).

(* ONE instruction with one relation opened for it: the copies are cleared after the instruction *)
Local Ltac za_one_with opener :=
  let MK := fresh "MARK" in
  pose proof I as MK;
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => opener Mx end;
  za_step;
  repeat (lazymatch goal with H : _ |- _ => lazymatch H with MK => fail | _ => clear H end end);
  clear MK.

(* the return-code place: its lemma at the model state of the invariant `SI`; the bit that the code tests
   there is left to be read from the registers *)
Local Ltac kapp_fin SI rv :=
  idtac; za_pc_is OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZA_LFIN;
  lazymatch type of SI with sinv _ ?ST ?LF ?CF =>
  lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
    eapply (leave_fin_s cx fin MD T M0 CX Hh OBLOW HKRL R' Mx ST rv _ LF CF SI) end end.

(* the check callee's entry: its specification over the output made in this pass; the output buffer's bytes
   are named at the memory of the call *)
Local Ltac kapp_adler ck cout out :=
  idtac; za_pc_is A_ADLER32;
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?LL) ?Mx _) _ =>
    match goal with WO : mem_wr _ Mx (c_ob cx) (c_osz cx) |- _ =>
      destruct (mem_wr_arr_exists_R Mx (c_ob cx) (c_osz cx) WO ltac:(lia) ltac:(lia) ltac:(lia)) as (fo & HOB & Hfo) end;
    match goal with HB : mem_arr 1 _ Mx (c_ob cx) (c_osz cx) ?FO |- _ =>
      let HS := fresh "Hsrc" in
      pose proof (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 1 Mx (c_ob cx) (c_osz cx) FO (cout - (out - (c_osz cx - cout))) (out - (c_osz cx - cout)) HB ltac:(lia) ltac:(lia) ltac:(lia)) as HS;
      replace (c_ob cx + 1 * (cout - (out - (c_osz cx - cout)))) with (c_ob cx + cout - (out - (c_osz cx - cout))) in HS by lia;
      let fr := eval cbv in (- OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_INF) in
      eapply (ADLER R' LL Mx MD T ck (c_ob cx + cout - (out - (c_osz cx - cout))) (out - (c_osz cx - cout)) (out - (c_osz cx - cout)) (c_u cx + fr) _
                (fun j => FO (cout - (out - (c_osz cx - cout)) + j)) Hh)
    end
  end.

(* the window callee's entry: its lemma; the stack value, the return place and the five saved values are read
   from the registers; the output buffer's bytes are named at the memory of the call *)
Local Ltac kapp_uw whave wnext cout out :=
  idtac; za_pc_is L_UW;
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?LL) ?Mx _) _ =>
    match goal with WO : mem_wr _ Mx (c_ob cx) (c_osz cx) |- _ =>
      destruct (mem_wr_arr_exists_R Mx (c_ob cx) (c_osz cx) WO ltac:(lia) ltac:(lia) ltac:(lia)) as (fw & HOBw & Hfw) end;
    match goal with HB : mem_arr 1 _ Mx (c_ob cx) (c_osz cx) ?FW |- _ =>
      eapply (uw_entry_s MEMCPY R' LL Mx MD T (c_u cx) (c_p cx) (c_ob cx) (c_osz cx) (c_w cx) whave wnext cout (out - (c_osz cx - cout))
                _ _ _ _ _ _ _ (c_zc cx) FW Hh)
    end
  end.

(* a goal that says the stream's relation: the relation in hand, or its fields in hand *)
Local Ltac za_strm := first [ assumption | unfold strm_at; icx_cbn; split_conj; assumption ].

(* THE SIDE GOALS OF THE THREE APPLICATIONS: a goal that is a place of the walk, a continuation, or the
   return-code place's progress premise is left for the lines after; every other goal is closed (the closers
   are the hand text's, with each fact found by its form; a memory fact that a closed relation holds is read
   from that relation) *)
Local Ltac leave_side HAG AL SEP WIN_ :=
  lazymatch goal with
  | |- realizes _ _ _ => idtac
  | |- forall M' : mem, _ => idtac
  | |- forall R' M', c_w cx = 0 -> _ => idtac
  | |- forall R' M' whave' wnext', _ => idtac
  | |- hideP _ => idtac
  | |- _ =>
      split_za_lists; cbv [FR_AD];
      first [ zreg | reflexivity | assumption | exact HAG
            | unfold e_mem; icx_cbn; split_conj; first [ assumption | za_strm ]
            | rewrite Z.mod_small by lia; reflexivity
            | exact (proj1 AL) | exact (proj1 (proj2 AL)) | exact (proj2 (proj2 AL))
            | exact (sep_p_ob _ _ SEP) | exact (sep_w_p _ _ SEP) | exact (sep_w_ob _ _ SEP)
            | let WO := fresh "WINo" in pose proof WIN_ as WO; unfold WIN in WO; icx_cbn; exact (proj2 WO)
            | lazymatch goal with
              | |- mem_u64 _ ?Mx _ _ => za_open_all_at Mx; assumption
              | |- mem_u32 _ ?Mx _ _ => za_open_all_at Mx; assumption
              end
            | match goal with WS : mem_wr _ _ _ _ |- mem_wr _ _ _ _ => eapply mem_wr_sub; [exact WS | klia | klia] end
            | let Hw := fresh "Hw" in let X := fresh "X" in
              intros Hw;
              match goal with WW : mem_wr _ _ (c_w cx) (wsz cx) |- _ =>
                pose proof WW as X; rewrite ((proj2 (proj2 (wsz_facts cx))) Hw) in X; exact X end
            | unfold ZSEP; unfold FRA in OBLOW; klia | klia
            | let i := fresh "i" in let Hi := fresh "Hi" in
              intros i Hi;
              match goal with HF : _ |- _ => solve [ apply HF ] end
            | unfold FRA in OBLOW; lia | lia ]
  end.

(* the window callee's first continuation: no window yet: the callee calls the allocator: the caller's
   continuation `HKW`, in the list form *)
Local Ltac uw_kw_cont SI rv HAG PR3 :=
  idtac;
  let RN := fresh "RN" in let MN := fresh "MN" in let HwN := fresh "HwN" in
  let WHY1 := fresh "WHY1" in let WHY2 := fresh "WHY2" in
  intros RN MN HwN;
  lazymatch type of SI with sinv _ ?ST _ _ =>
    assert (WHY1 : c_cout0 cx < t_cout ST)
      by (icx_cbn; cbv [DONE]; destruct PR3 as [PR3 | [PR3 _]]; lia);
    assert (WHY2 : t_mode ST <= DONE)
      by (icx_cbn; cbv [DONE]; destruct PR3 as [PR3 | [PR3 _]]; lia) end;
  intros; zimps; zkeys;
  match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) _ MN _ |- _ => zreattachL HP end;
  lazymatch type of SI with sinv _ ?ST ?LF ?CF =>
  lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
    eapply (HKW R9 Mx ST rv LF CF HwN SI WHY1 WHY2) end end;
  split_za_lists;
  first [ zreg | icx_cbn; zreg | icx_cbn; zkept | assumption
        | match goal with H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v |- mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a' ?v' =>
            replace a' with a by lia_std;
            first [exact H | cbv [L_UW_RET]; exact H | replace v' with v by lia_std; exact H] end
        | close_std | za_strm
        | lazymatch goal with |- st_at _ _ _ ?Mx => za_open_state_at Mx; unfold st_at, st_rest; icx_cbn; split_conj; assumption end
        | exact HAG ].

(* THE THREE MODEL CASES OF THE WALK, each split once (a case that is in hand is not split again) *)
Local Ltac leave_split_w :=
  lazymatch goal with
  | H : c_w cx = 0 |- _ => fail
  | H : c_w cx <> 0 |- _ => fail
  | |- _ =>
      let Hw := fresh "Hw" in let Hz := fresh "Hz" in
      destruct (Z.eq_dec (c_w cx) 0) as [Hw|Hw];
      [ pose proof ((proj1 (proj2 (wsz_facts cx))) Hw) as Hz
      | pose proof ((proj2 (proj2 (wsz_facts cx))) Hw) as Hz; cbv [WIN_SIZE] in Hz ]
  end.
(* where output was made the stream is a plain one (its flags word is 0): the check callee is the plain one *)
Local Ltac leave_split_o out cout flags MODE_ :=
  lazymatch goal with
  | H : out = c_osz cx - cout |- _ => fail
  | H : out <> c_osz cx - cout |- _ => fail
  | |- _ =>
      let E := fresh "Ecout" in
      destruct (Z.eq_dec out (c_osz cx - cout)) as [E|E];
      [ | let Hf := fresh "Hf0" in let Mf := fresh "Mf" in
          assert (Hf : flags = 0)
            by (dand MODE_ as (_ & Mf & _); icx_cbn;
                assert (flags <> -1)
                  by (let E1 := fresh "E1" in let Hc := fresh "Hc" in
                      intros E1; destruct (Mf E1) as [_ Hc]; clear Mf; lia);
                clear Mf; lia) ]
  end.
Local Ltac leave_split_m mode :=
  lazymatch goal with
  | H : 16208 < mode |- _ => fail
  | H : ~ 16208 < mode |- _ => fail
  | |- _ => let Hm := fresh "Hm" in destruct (Z_lt_dec 16208 mode) as [Hm|Hm]
  end.

(* the return-code place's progress premise: from the case in hand; else from the two cases split here; where
   no input was used, no output was made and the return value is 0, the bit that the code tested is a closed
   value once the two "x xor x" are 0 and the return value's test is rewritten *)
Local Ltac leave_progress rv cin cout out :=
  let Hj := fresh "Hj" in let Hrv := fresh "Hrv" in
  unfold hideP; intros Hj Hrv;
  first [ right; assumption | left; assumption
        | let Ei := fresh "Ecin" in let Eo := fresh "Ecout" in
          destruct (Z.eq_dec cin (c_cin0 cx)) as [Ei|Ei]; [ | left; exact Ei ];
          destruct (Z.eq_dec out (c_osz cx - cout)) as [Eo|Eo]; [ | right; exact Eo ];
          exfalso; revert Hj; rewrite <- ?Ei; rewrite ?Eo; rewrite ?Z.lxor_nilpotent; rewrite ?Hrv; cbv; discriminate ].

(* THE WALK. `leave_seg`: ONE RUN to the first of the three continuations or to a stop, then the side goals.
   `leave_stuck`: at a stop: a test: the model case that lets the step go is split; a load: the relation that
   lets the step go is opened for that instruction; then the walk goes on. `uwk` closes the window callee's
   second continuation (its return: the lemma of the return place). *)
Local Ltac leave_seg SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ uwk :=
  za_run ltac:(first [ kapp_adler ck cout out | kapp_uw whave wnext cout out | kapp_fin SI rv ]);
  leave_side HAG AL SEP WIN_;
  lazymatch goal with
  | |- realizes _ _ _ => leave_stuck SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ uwk
  | |- forall M' : mem, _ =>
      let MN := fresh "MN" in let RN := fresh "RN" in let HPN := fresh "HPN" in
      intros MN RN HPN; intros; zimps; zkeys;
      repeat match goal with
             | H : mem_arr 1 _ _ (c_ob cx + _ - _) _ _ |- _ => clear H
             | H : mem_arr 1 _ _ (c_ob cx) (c_osz cx) _ |- _ => clear H
             end;
      apply mpost_mpostL1 in HPN; cbv [FR_AD] in HPN; zreattachL HPN;
      leave_seg SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ uwk
  | |- forall R' M', c_w cx = 0 -> _ => uw_kw_cont SI rv HAG PR3
  | |- forall R' M' whave' wnext', _ => uwk
  | |- hideP _ => leave_progress rv cin cout out
  end
with leave_stuck SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ uwk :=
  tryif za_at_test
  then first [ leave_split_w; za_step; leave_seg SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ uwk
             | leave_split_o out cout flags MODE_; za_step; leave_seg SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ uwk
             | leave_split_m mode; za_step; leave_seg SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ uwk ]
  else first [ za_one_with za_open_frame_at; leave_seg SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ uwk
             | za_one_with za_open_out_at; leave_seg SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ uwk
             | za_one_with za_open_state_at; leave_seg SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ uwk
             | za_one_with za_open_strm_at; leave_seg SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ uwk
             | za_one_with za_open_cst_at; leave_seg SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ uwk
             | za_one_with za_open_hooks_at; leave_seg SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ uwk ].

(* THE WINDOW CALLEE's RETURN PLACE, IN THE LIST FORM (another text names the hand statement of this place: the
   hand statement is proved from this one in a small text of its own). The place's register map is a field of
   the layout; its two bound values are: value 0 = the callee's return value, value 1 = the return value so
   far. *)
Lemma leave_uwret_l : forall Rb l M st rv uwret lf cf,
  sinv cx st lf cf ->
  rholds (qvalv cx (Some st) [uwret; rv]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_za_uwret ->
  (uwret = 0 \/ uwret = 1) ->
  s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_RET (zupd Rb l) M MD) T.
Proof.
  intros Rb l M st rv uwret lf cf SI RH Huw STD SAT STRM Hlens Hcodes HP0.
  open_za_lists.
  open_std STD. open_leave CX SI st HP0.
  fp_call_frame HP0.
  (* the totals and the check value: unknown values of known widths (no relation holds them) *)
  destruct (mem_wr_u64_exists_R M (c_u cx + 16) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (ti & Hti & Rti).
  destruct (mem_wr_u64_exists_R M (c_u cx + 40) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (to & Hto & Rto).
  destruct (mem_wr_u64_exists_R M (c_p cx + 48) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (tt & Htt & Rtt).
  destruct (mem_wr_u64_exists_R M (c_p cx + 40) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (ck & Hck & Rck).
  (* A VALUE EQUATION STATED BEFORE THE RUNS (no hint run): the zero-extension of the output made in this pass *)
  pose proof (zext32_shift (out - (c_osz cx - cout)) ltac:(zlia)) as Hzx.
  destruct Huw as [Uw0 | Uw1]; subst uwret.
  - (* the callee returned 0: the rest of the leave part: THE WALK *)
    leave_seg SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ idtac.
  - (* the callee returned 1: ONE RUN to the function's exit, with the source's "no memory" code; this run
       reads the frame and writes the state's mode: the frame's slots are opened ALL; the state's closed
       relation is not needed after it *)
    pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn. destr_conj FRM'.
    clear SAT.
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (ret_s cx R9 [] Mx MD T (-4) CX Hh) end).
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

(* the window callee's second continuation in the lemma of the leave entry: the callee returned (a window
   stands): the lemma of the return place at the state with the window's two fields as the callee left them.
   The constant fields and the state's fields are opened before the callee's footprint is taken off (the
   callee rewrites two of the constant fields and the window's two fields of the state). *)
Local Ltac uw_ret_cont SI rv HAG :=
  idtac;
  let RN := fresh "RN" in let MN := fresh "MN" in let whN := fresh "whN" in let wnN := fresh "wnN" in
  let HwN := fresh "HwN" in
  intros RN MN whN wnN HwN;
  first
  [ (* in a case with no window this continuation cannot come *)
    solve [ exfalso; apply HwN; assumption ]
  | intros; zimps; zkeys;
    rewrite ((proj2 (proj2 (wsz_facts cx))) HwN) in *; cbv [WIN_SIZE] in *;
    match goal with H : i_cst _ cx _ |- _ =>
      let X := fresh "CSo" in
      let C1 := fresh "C1" in let C2 := fresh "C2" in let C3 := fresh "C3" in let C4 := fresh "C4" in
      let C5 := fresh "C5" in let C6 := fresh "C6" in let C7 := fresh "C7" in let C8 := fresh "C8" in
      let C9 := fresh "C9" in
      pose proof H as X; unfold i_cst in X; icx_cbn;
      dand X as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9);
      clear C7 C8; clear H end;
    match goal with H : st_at _ cx _ ?Mo |- _ => za_open_state_at Mo; clear H end;
    match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) _ MN _ |- _ => unfold uw_fp in HP; cbv [WIN_SIZE] in HP; zreattachL HP end;
    lazymatch type of SI with sinv _ ?ST ?LF ?CF =>
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (leave_uwret_l R9 [] Mx (set_win ST whN wnN) rv 0 LF CF) end end;
    split_za_lists;
    first [ zreg | icx_cbn; zreg | icx_cbn; zkept | left; reflexivity | assumption
          | apply sinv_set_win; [exact SI | exact HwN | assumption ..]
          | unfold s_std, i_cst; rewrite ((proj2 (proj2 (wsz_facts cx))) HwN); cbv [WIN_SIZE]; icx_cbn; split_conj; assumption
          | unfold st_at, st_rest, set_win; icx_cbn; split_conj; assumption
          | unfold strm_at, set_win; icx_cbn; match goal with H : strm_at _ _ _ _ |- _ => unfold strm_at in H; icx_cbn; exact H end
          | unfold strm_at, set_win; icx_cbn; split_conj; assumption
          | unfold fp_call; rewrite ((proj2 (proj2 (wsz_facts cx))) HwN); exact HAG ] ].

(* THE FUNCTION's LEAVE ENTRY *)
Theorem leave_s : KLEAVE cx fin MD T M0.
Proof using CX Hh OBLOW MEMCPY ADLER HKRL HKRX HKW.
  intros RR M st rv lf cf SI RE STD SAT SOUT Hlens Hcodes HPl.
  pose proof (fp_call_widen cx M0 M HPl) as HP0. clear HPl.
  open_std STD. unfold s_regs_leave in RE. destr_conj RE. zgetl_nil. open_leave CX SI st HP0.
  fp_call_frame HP0.
  (* the totals and the check value: unknown values of known widths (no relation holds them) *)
  destruct (mem_wr_u64_exists_R M (c_u cx + 16) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (ti & Hti & Rti).
  destruct (mem_wr_u64_exists_R M (c_u cx + 40) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (to & Hto & Rto).
  destruct (mem_wr_u64_exists_R M (c_p cx + 48) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (tt & Htt & Rtt).
  destruct (mem_wr_u64_exists_R M (c_p cx + 40) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (ck & Hck & Rck).
  (* A VALUE EQUATION STATED BEFORE THE RUNS (no hint run): the zero-extension of the output made in this pass *)
  pose proof (zext32_shift (out - (c_osz cx - cout)) ltac:(zlia)) as Hzx.
  (* THE WALK from the entry *)
  leave_seg SI rv ck whave wnext cin cout out flags mode MODE_ HAG PR3 AL SEP WIN_ ltac:(uw_ret_cont SI rv HAG).
Qed.
End Leave.
End S_Leave.

Module S_Inflate.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry.S_Loop S_Ret OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry S_Uw S_LeaveA S_Leave.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Section Inflate.
Context {RCa1 : RunCtx}.
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
  intros M0 KX RR M rc m Hrc RE STD Hm Hr HP0.
  pose proof STD as STD'. dand STD' as (_ & _ & _ & _ & _ & FRM & _).
  eapply (ret_s cx RR [] M MD T rc CX Hh RE FRM).
  intros R9 HB. eapply (KX R9 M rc m Hrc HB STD Hm Hr). apply fp_call_widen. exact HP0.
Qed.

Theorem inflate_s : forall Rb l M st lf cf,
  ainv cx st lf cf -> c_cin0 cx = t_cin st -> c_cout0 cx = t_cout st -> c_W0 cx = Wm cx st ->
  s_regs_entry cx Rb l -> e_mem cx fin st lf cf M ->
  KRL cx fin MD T M -> KRX cx fin MD T M -> KW cx fin MD T M ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_INFLATE (zupd Rb l) M MD) T.
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
End S_Inflate.


Module S_U2B.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* the outer function's exit; the two callee calls of the stream's end function and the return place after it.
   ALL FOUR ARE FIELDS OF THE IMAGE's LAYOUT TEXT. The first has its old short name only; the other three are
   named by other texts: they keep name and type, and their value is the layout's field. *)
Local Notation L_EXIT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_EXIT (only parsing).
Local Notation LT_ZE1 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.T_ZE1 (only parsing).
Local Notation LT_ZE2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.T_ZE2 (only parsing).
Local Notation LRA2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.RA2 (only parsing).
Definition T_ZE1 : Z := LT_ZE1.
Definition T_ZE2 : Z := LT_ZE2.
Definition RA2 : Z := LRA2.

Ltac zgen :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => let x' := fresh "gv" in set (x' := e); clearbody x'
  end.

Theorem u2_exit_s {RCa1 : RunCtx}  : forall Rb l M MD T (u p w rc len left m zc : Z) (gp tp s5 s6 s7 s8 s9 s10 s11 : Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u -> zget_l Rb l kA0 = rc -> zget_l Rb l kS0 = u + 168 -> zget_l Rb l kS1 = u + 160 ->
  zget_l Rb l kS3 = len -> zget_l Rb l kS4 = left -> zget_l Rb l kS5 = s5 ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp ->
  zget_l Rb l kS6 = s6 -> zget_l Rb l kS7 = s7 -> zget_l Rb l kS8 = s8 -> zget_l Rb l kS9 = s9 ->
  zget_l Rb l kS10 = s10 -> zget_l Rb l kS11 = s11 ->
  zc + FRA <= u -> DATA_LO + DATA_LEN <= zc -> u + 208 <= 140737488355328 -> 0 < p -> p + STATE_SIZE <= zc ->
  0 <= w -> w + WIN_SIZE <= zc -> reach m ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 64) A_ZCALLOC -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 72) A_ZCFREE ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M p u -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 8) m -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) w ->
  (forall R' M', w = 0 ->
     zget R' kA4 = A_ZCFREE -> zget R' kA1 = p -> zget R' kA0 = 0 -> zget R' kS0 = u -> zget R' kSP = u + -16 ->
     zget R' kGP = gp -> zget R' kTP = tp -> zget R' kS5 = s5 ->
     zget R' kS6 = s6 -> zget R' kS7 = s7 -> zget R' kS8 = s8 -> zget R' kS9 = s9 -> zget R' kS10 = s10 -> zget R' kS11 = s11 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -8) RA2 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 80) 0 ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(u + -16, 16); (u + 160, 8); (u + 168, 8)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE2 (zupd R' []) M' MD) T) ->
  (forall R' M', w <> 0 ->
     zget R' kA4 = A_ZCFREE -> zget R' kA1 = w -> zget R' kA0 = 0 -> zget R' kS0 = u -> zget R' kSP = u + -16 ->
     zget R' kGP = gp -> zget R' kTP = tp -> zget R' kS5 = s5 ->
     zget R' kS6 = s6 -> zget R' kS7 = s7 -> zget R' kS8 = s8 -> zget R' kS9 = s9 -> zget R' kS10 = s10 -> zget R' kS11 = s11 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -8) RA2 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 80) 0 ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(u + -16, 16); (u + 160, 8); (u + 168, 8)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE1 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_EXIT (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u p w rc len left m zc gp tp s5 s6 s7 s8 s9 s10 s11
         Hh Lsp La0 Ls0 Ls1 Ls3 Ls4 Ls5 Lgp Ltp Ls6 Ls7 Ls8 Ls9 Ls10 Ls11
         Hu0 Hzimg Hu1 Hp0 Hp1 Hw0 Hw1 Hm Wstk Wp C64 C72 C80 C88 Cp0 Cp8 Cp72 KNW KW.
  zkeysb. unfold L_EXIT, T_ZE1, T_ZE2, RA2, LT_ZE1, LT_ZE2, LRA2 in *. cbv [STATE_SIZE FRA WIN_SIZE A_ZCALLOC A_ZCFREE BUF DATA_LO DATA_LEN] in *.
  pose proof two64_eq as TW64. pose proof (reach_bounds' := Hm). unfold reach in reach_bounds'. cbv [HEAD DICTID MEM] in reach_bounds'.
  assert (Hmb : 16180 <= m <= 16210) by lia_std. clear reach_bounds'.
  (* the frame list of the two continuations is read from the first continuation's statement *)
  lazymatch type of KNW with context [cons (?a0, ?n0) (cons (?a1, ?n1) (cons (?a2, ?n2) nil))] =>
    pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(a0, n0); (a1, n1); (a2, n2)] ltac:(ranges_ok_tac)) as HST;
    assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(a0, n0); (a1, n1); (a2, n2)]) M) by (apply mpostL_refl)
  end.
  (* the four values that the exit reads from the frame: unknown values of known widths (two are fields of the
     stream; the other two stand at the addresses that the statement gives two registers) *)
  destruct (mem_wr_u32_exists_R M (u + 8) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (vai & Hai & Rai).
  lazymatch type of Ls1 with _ = ?a =>
    destruct (mem_wr_u64_exists_R M a ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (vsl & Hsl & Rsl) end.
  destruct (mem_wr_u32_exists_R M (u + 32) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (vao & Hao & Rao).
  lazymatch type of Ls0 with _ = ?a =>
    destruct (mem_wr_u64_exists_R M a ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (vdl & Hdl & Rdl) end.
  (* ONE RUN: the two counts are written back, the stream's end function is entered and its checks of the
     state pass; it stops at the test of the window *)
  zto_branch Rfd.
  destruct (Z.eq_dec w 0) as [Wz | Wnz].
  - (* no window: ONE RUN to the call that frees the state *)
    revert Cp72. subst w. intros Cp72.
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => apply (KNW R' Mx eq_refl) end);
      try zreg; try assumption.
  - (* a window: ONE RUN to the call that frees it *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => apply (KW R' Mx Wnz) end);
      try zreg; try assumption.
Qed.
End S_U2B.

Module S_U2C.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry.S_Loop S_Ret OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry S_Uw S_LeaveA S_Leave S_Inflate S_U2B.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* the outer loop's tail, its two call sites of the inner function and their two return places: FIELDS OF THE
   IMAGE's LAYOUT TEXT. The first three have their old short names only; the two return places are named by
   another text: they keep name and type, and their value is the layout's field. *)
Local Notation L_TAIL := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_TAIL (only parsing).
Local Notation L_C1 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_C1 (only parsing).
Local Notation L_C2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CALL2 (only parsing).
Local Notation LRA_C1 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.RA_C1 (only parsing).
Local Notation LRA_C2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.RA_C2 (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation fholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds (only parsing).
Local Notation qvalv := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (only parsing).
Definition RA_C1 : Z := LRA_C1.
Definition RA_C2 : Z := LRA_C2.
(* the labels of the module before, by their short names *)
Local Notation L_EXIT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_EXIT (only parsing).
Local Notation LT_ZE1 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.T_ZE1 (only parsing).
Local Notation LT_ZE2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.T_ZE2 (only parsing).
Local Notation LRA2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.RA2 (only parsing).
Definition pc_site (site : bool) : Z := if site then L_C1 else L_C2.
Definition ra_site (site : bool) : Z := if site then RA_C1 else RA_C2.

Section U2.
Context {RCa1 : RunCtx}.
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
  else if (k =? kS0)%positive then u + 168 else if (k =? kS1)%positive then u + 160
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
    unfold RA_C1, RA_C2, LRA_C1, LRA_C2 in Hra; destruct Hra as [-> | ->]; first [reflexivity | lia | lia_std].
Qed.

Definition u2regs (R : tree Z) : Prop :=
  zget R kSP = u /\ zget R kS0 = u + 168 /\ zget R kS1 = u + 160 /\ zget R kS2 = 4294967295 /\ zget R kS3 = 0 /\ zget R kS4 = 0 /\
  zget R kS5 = s5 /\ zget R kGP = gp /\ zget R kTP = tp /\
  zget R kS6 = s6 /\ zget R kS7 = s7 /\ zget R kS8 = s8 /\ zget R kS9 = s9 /\ zget R kS10 = s10 /\ zget R kS11 = s11.

Definition fp_u2 (w : Z) : list (Z * Z) :=
  [(u + -1024, 1136); (u + 160, 8); (u + 168, 8); (p, STATE_SIZE); (BUF, 262144); (w, if w =? 0 then 0 else WIN_SIZE)].

Definition Wv (st : ist) : Z := 8 * (n - t_cin st) + t_bits st + (262144 - t_cout st).
Definition M2v (st : ist) : Z := Wv st * 134217728 + (n - t_cin st).

Variable wph : Z.
Hypothesis Hwph : wok wph.

Definition KZE2 : Prop := forall (R : tree Z) (M : mem),
  zget R kA4 = A_ZCFREE -> zget R kA1 = p -> zget R kA0 = 0 -> zget R kS0 = u -> zget R kSP = u + -16 ->
  zget R kGP = gp -> zget R kTP = tp -> zget R kS5 = s5 ->
  zget R kS6 = s6 -> zget R kS7 = s7 -> zget R kS8 = s8 -> zget R kS9 = s9 -> zget R kS10 = s10 -> zget R kS11 = s11 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -8) RA2 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 ->
  wph = 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza M (fp_u2 wph) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE2 (zupd R []) M MD) T.
Definition KZE1 : Prop := forall (R : tree Z) (M : mem),
  zget R kA4 = A_ZCFREE -> zget R kA1 = wph -> zget R kA0 = 0 -> zget R kS0 = u -> zget R kSP = u + -16 ->
  zget R kGP = gp -> zget R kTP = tp -> zget R kS5 = s5 ->
  zget R kS6 = s6 -> zget R kS7 = s7 -> zget R kS8 = s8 -> zget R kS9 = s9 -> zget R kS10 = s10 -> zget R kS11 = s11 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -8) RA2 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 ->
  wph <> 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza M (fp_u2 wph) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE1 (zupd R []) M MD) T.
Definition KZW_l : Prop := forall (R : tree Z) (M : mem) (cin0 cout0 W0 ra : Z) (st : ist) (rv : Z) (lf cf : Z -> Z),
  let cx := cxc 0 cin0 cout0 W0 ra in
  (ra = RA_C1 \/ ra = RA_C2) -> 0 <= cin0 <= n -> 0 <= cout0 <= 262144 ->
  sinv cx st lf cf -> cout0 < t_cout st -> t_mode st <= DONE ->
  rholds (qvalv cx (Some st) [rv; t_out st - (c_osz cx - t_cout st)]) R [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_za_kw ->
  fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qvalv cx (Some st) [rv; t_out st - (c_osz cx - t_cout st)]) M (c_u cx) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_za_kw ->
  s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) N_CODES cf ->
  wph = 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza M (fp_u2 0) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZW (zupd R []) M MD) T.
Hypothesis HZE2 : KZE2.
Hypothesis HZE1 : KZE1.
Hypothesis HZW : KZW_l.

Definition PCALL (B : Z) : Prop := forall (site : bool) (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
  let cx := cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site) in
  ainv cx st lf cf -> M2v st < B ->
  u2regs R -> e_mem cx fin st lf cf M -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza M (fp_u2 wph) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (pc_site site) (zupd R []) M MD) T.

Local Ltac open_u2 :=
  unfold ZSEP in Spq, Spob, Sobq, Sprom;
  zkeysb; unfold L_TAIL, L_C1, L_C2, RA_C1, RA_C2, LRA_C1, LRA_C2, L_EXIT, L_INFLATE, T_ZE1, T_ZE2, LT_ZE1, LT_ZE2, T_ZW, RA2, LRA2 in *;
  cbv [STATE_SIZE FRA WIN_SIZE ROM_LO_ALL A_ZCALLOC A_ZCFREE BUF DATA_LO DATA_LEN] in *;
  pose proof two64_eq as TW64.

(* THE APPLICATION HANDED TO THE TAIL's RUNS (the continuation `K` at one of the two call sites) AND ITS THREE
   SIDE GOALS' CLOSERS (the hand text defines them as one tactic inside the proof) *)
Local Ltac kapp_tail K site :=
  idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => apply (K site R' Mx) end.
Local Ltac side_tail_regs := unfold u2regs; zkeys; split_conj; zreg.
Local Ltac side_tail_mem EM :=
  first [ exact EM
        | repeat match goal with H : mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ |- _ => clear H end;
          lazymatch goal with |- e_mem _ _ _ _ _ ?Mx =>
              match goal with HP : framed _ Mx |- _ =>
                pose proof EM as EM2; unfold cxc in EM2; open_emem EM2; icx_cbn; cbv [BUF] in *;
                let HP' := fresh in pose proof HP as HP'; unfold framed in HP'; zreattachL HP';
                unfold e_mem, strm_at, cxc; icx_cbn; cbv [BUF]; split_conj;
                first [ assumption
                      | match goal with H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v |- mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v' => replace v' with v by lia_std; exact H end ] end end ].
Local Ltac side_tail_fp HAG :=
  first [exact HAG ].

Lemma u2_tail_s : forall R M st lf cf (ra : Z),
  let cx := cxc wph (t_cin st) (t_cout st) (Wv st) ra in
  ainv cx st lf cf -> u2regs R -> e_mem cx fin st lf cf M ->
  (forall (site : bool) R' M',
     u2regs R' -> e_mem cx fin st lf cf M' -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(u + 8, 4); (u + 32, 4)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (pc_site site) (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TAIL (zupd R []) M MD) T.
Proof.
  intros RR M st lf cf ra cx AI RE EM K. subst cx.
  pose proof AI as AI'. dand AI' as (RNG_ & _ & _). unfold RNG in RNG_. unfold cxc in RNG_. icx_cbn.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. destr_conj RNG_.
  unfold u2regs in RE. destr_conj RE. open_u2. unfold pc_site, L_C1, L_C2 in K.
  pose proof EM as EM'. open_emem EM'. clear ROM Wp Wob Ww CST HK Hin SAT Hlens Hcodes.
  unfold cxc in Wstk. unfold strm_at, cxc in STRM. icx_cbn. cbv [BUF] in STRM. dand STRM as (S8 & S16 & S32 & S40 & S80 & S88).
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(u + 8, 4); (u + 32, 4)] ltac:(ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(u + 8, 4); (u + 32, 4)]) M) by (apply mpostL_refl).
  (* THE CASE TREE: a run to an open test, a case split, and at each leaf one run to the continuation `K` at
     one of the two call sites *)
  zto_branch Rfd.
  destruct (Z.eq_dec cout 262144) as [Eo | Eo].
  - (* the output buffer is full *)
    zto_branch Rfd.
    destruct (Z.eq_dec cin n) as [Ei | Ei].
    + zuntil Rfd (kapp_tail K false); [ side_tail_regs | side_tail_mem EM | side_tail_fp HAG ].
    + zuntil Rfd (kapp_tail K true); [ side_tail_regs | side_tail_mem EM | side_tail_fp HAG ].
  - (* room is left in the output buffer *)
    zto_branch Rfd.
    destruct (Z.eq_dec cin n) as [Ei | Ei].
    + zuntil Rfd (kapp_tail K false); [ side_tail_regs | side_tail_mem EM | side_tail_fp HAG ].
    + zuntil Rfd (kapp_tail K true); [ side_tail_regs | side_tail_mem EM | side_tail_fp HAG ].
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
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call (cxc w cin cout W0 ra)) ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M [(u + -1024, 1024); (u, 112); (p, STATE_SIZE); (BUF, 262144); (w, if w =? 0 then 0 else WIN_SIZE)].
Proof.
  intros w cin cout W0 ra M0 M H. unfold fp_call, fp_loop, cxc, wsz in H. icx_cbn. cbv [FRA ZS_OFF ZS_SIZE] in H. cbn [app] in H.
  lazymatch type of H with context [u - ?k] => replace (u - k) with (u + - k) in H by lia end. exact H.
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
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza X (fp_u2 wph)) Mc ->
  KRL (cxc wph cin cout W0 (ra_site site)) fin MD T Mc.
Proof.
  intros site cin cout W0 Mc Hcin Hcout HB HAG0 RR M rc st lf cf HB' AI PRG HWle EM FRM HP. pose proof Hwph as Hw.
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
    assert (TAIL : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TAIL (zupd RR []) M MD) T).
    { unfold L_TAIL.
      eapply (u2_tail_s RR M (IST mode last flags cin' cout' hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
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
    destruct site; unfold ra_site, RA_C1, RA_C2, LRA_C1, LRA_C2 in *; unfold cxc; icx_cbn; cbv [Kra]; zkeys; cbn [Pos.eqb].
    + zuntil Rfd (idtac; exact TAIL).
    + zuntil Rfd (idtac; exact TAIL).
  - (* the inner function returned another code: to the outer function's exit *)
    assert (EXIT : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_EXIT (zupd RR []) M MD) T).
    { unfold L_EXIT. pose proof EM as EM'. open_emem EM'.
      unfold i_cst, cxc in CST; icx_cbn; cbv [BUF] in CST. dand CST as (C64 & C88 & Cp0 & _ & _ & _ & _ & Cp72 & _).
      destruct HK as [C72 C80]. icx_cbn. destruct SAT as [Hmode _]. unfold cxc in Hmode; icx_cbn.
      unfold cxc in Wstk, Wp; icx_cbn.
      dand Hw as (W1 & W2 & W3 & _).
      eapply (u2_exit_s RR [] M MD T u p wph rc 0 0 mode zc gp tp s5 s6 s7 s8 s9 s10 s11 Hh);
        try assumption; try zreg; try klia.
      + intros R' M' Hw0. intros. eapply (HZE2 R' M'); try eassumption.
        eapply (framed_mpostL_trans _ _ _ _ _ _ HAG); [eassumption |].
        intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac.
      + intros R' M' Hw1. intros. eapply (HZE1 R' M'); try eassumption.
        eapply (framed_mpostL_trans _ _ _ _ _ _ HAG); [eassumption |].
        intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac. }
    unfold L_EXIT in EXIT.
    destruct site; unfold ra_site, RA_C1, RA_C2, LRA_C1, LRA_C2 in *; unfold cxc; icx_cbn; cbv [Kra]; zkeys; cbn [Pos.eqb].
    + zuntil Rfd (idtac; exact EXIT).
    + zuntil Rfd (idtac; exact EXIT).
Qed.

Lemma u2_krx : forall (site : bool) cin cout W0 Mc,
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza X (fp_u2 wph)) Mc ->
  KRX (cxc wph cin cout W0 (ra_site site)) fin MD T Mc.
Proof.
  intros site cin cout W0 Mc HAG0 RR M rc m Hrc HB' STD Hm Hreach HP. pose proof Hwph as Hw.
  unfold s_regs_back, cxc, Kra in HB'. icx_cbn. zkeys. cbn [Pos.eqb] in HB'. destr_conj HB'.
  apply fp_call_u2 in HP.
  pose proof (framed_mpostL_trans _ _ _ _ _ _ HAG0 HP ltac:(intros x Hx; eapply ranges_within_outside; [| exact Hx];
              unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac)) as HAG.
  clear HAG0 HP. open_u2.
  assert (EXIT : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_EXIT (zupd RR []) M MD) T).
  { pose proof STD as STD'. open_std STD'.
    unfold i_cst, cxc in CST; icx_cbn; cbv [BUF] in CST. dand CST as (C64 & C88 & Cp0 & _ & _ & _ & _ & Cp72 & _).
    destruct HK as [C72 C80]. unfold cxc in C72, C80, Wstk, Wp, Hm; icx_cbn.
    dand Hw as (W1 & W2 & W3 & _).
    eapply (u2_exit_s RR [] M MD T u p wph rc 0 0 m zc gp tp s5 s6 s7 s8 s9 s10 s11 Hh);
      try assumption; try zreg; try klia.
    + intros R' M' Hw0. intros. eapply (HZE2 R' M'); try eassumption.
      eapply (framed_mpostL_trans _ _ _ _ _ _ HAG); [eassumption |].
      intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac.
    + intros R' M' Hw1. intros. eapply (HZE1 R' M'); try eassumption.
      eapply (framed_mpostL_trans _ _ _ _ _ _ HAG); [eassumption |].
      intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac. }
  destruct site; unfold ra_site, RA_C1, RA_C2, LRA_C1, LRA_C2 in *; unfold cxc; icx_cbn; cbv [Kra]; zkeys; cbn [Pos.eqb].
  - zuntil Rfd (idtac; exact EXIT).
  - zuntil Rfd (idtac; exact EXIT).
Qed.

Lemma u2_kw : forall (site : bool) cin cout W0 Mc,
  0 <= cin <= n -> 0 <= cout <= 262144 ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza X (fp_u2 wph)) Mc ->
  KW (cxc wph cin cout W0 (ra_site site)) fin MD T Mc.
Proof.
  intros site cin cout W0 Mc Hcin Hcout HAG0 RR M st rv lf cf Hw0 SI Hc Hmd. intros.
  match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mc M _ |- _ =>
    apply fp_call_u2 in HP;
    pose proof (framed_mpostL_trans _ _ _ _ _ _ HAG0 HP ltac:(intros x Hx; eapply ranges_within_outside; [| exact Hx];
                unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; ranges_within_tac)) as HAG end.
  unfold cxc in Hw0; icx_cbn. clear HAG0.
  pose proof Hw0 as Hw0'. rewrite Hw0' in *.
  eapply (HZW RR M cin cout W0 (ra_site site) st rv lf cf);
    first [ destruct site; [left | right]; reflexivity | exact HAG | exact Hw0 | eassumption ].
Qed.
End Handlers.

Lemma pcall_step : forall B, PCALL B -> PCALL (B + 1).
Proof.
  intros B IH site RR M st lf cf cx AI MB RE EM HP. subst cx. pose proof Hwph as Hw.
  pose proof AI as AI'. dand AI' as (RNG_ & _ & _). unfold RNG, cxc in RNG_. icx_cbn.
  pose proof (M2v_nonneg _ _ _ _ _ _ _ _ AI) as Hnn.
  assert (Hcin : 0 <= t_cin st <= n) by (destruct st; icx_cbn; destr_conj RNG_; lia_std).
  assert (Hcout : 0 <= t_cout st <= 262144) by (destruct st; icx_cbn; destr_conj RNG_; lia_std).
  clear RNG_.
  pose proof (ctx_ok_cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site) Hw Hcin Hcout
                ltac:(destruct site; [left | right]; reflexivity)) as CX.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) Mza (fp_u2 wph) (fp_u2_ok wph Hw)) as HST.
  change (framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza X (fp_u2 wph)) M) in HP. rename HP into HAG.
  unfold u2regs in RE. destr_conj RE. open_u2.
  assert (Hfin' : forall i, 0 <= i < c_n (cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site)) -> 0 <= fin i < 256) by exact Hfin.
  assert (OBLOW : c_ob (cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site)) + c_osz (cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site))
                  <= c_u (cxc wph (t_cin st) (t_cout st) (Wv st) (ra_site site)) - FRA) by (unfold cxc; icx_cbn; cbv [BUF FRA]; lia).
  destruct site; unfold pc_site, ra_site, L_C1, L_C2, RA_C1, RA_C2, LRA_C1, LRA_C2 in *.
  (* at either call site: ONE RUN to the inner function's entry *)
  all: zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?LL) ?Mx _) _ =>
         eapply (inflate_s _ fin MD T CX Hh Hfin' OBLOW MEMCPY ADLER
                   A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
                   A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH R' LL Mx st lf cf AI) end).
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
  - intros site RR M st lf cf cx AI MB. exfalso. pose proof (M2v_nonneg _ _ _ _ _ _ _ _ AI). cbn [Z.of_nat] in MB. lia_std.
  - rewrite Nat2Z.inj_succ. apply pcall_step. exact IH.
Qed.

Theorem pcall_all_l : forall B, PCALL B.
Proof.
  intros B site RR M st lf cf cx AI MB.
  apply (pcall_nat (Z.to_nat (M2v st + 1)) site RR M st lf cf AI). pose proof (M2v_nonneg _ _ _ _ _ _ _ _ AI). lia_std.
Qed.

End U2.
End S_U2C.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import SBase. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_Entry. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry.S_Loop. Import S_Ret. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import S_Entry. Import S_Uw. Import S_LeaveA. Import S_Leave. Import S_Inflate. Import S_U2A. Import S_U2B. Import S_U2C.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Lemma le_cell_range : forall k bs i, 0 < k <= 8 -> 0 <= le_cell k bs i < 2 ^ (8 * k).
Proof.
  intros k bs i Hk. unfold le_cell.
  pose proof (bytes_le_to_Z_nonneg (firstn (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs))) as H0.
  pose proof (bytes_le_to_Z_bound (firstn (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs))) as H1.
  pose proof (firstn_le_length (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs)) as Hl.
  assert (2 ^ (8 * Z.of_nat (length (firstn (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs)))) <= 2 ^ (8 * k)).
  { apply Z.pow_le_mono_r; lia. }
  lia.
Qed.

Lemma mem_wr_arrk_exists {RCa1 : RunCtx}  : forall k M base n,
  0 < k <= 8 -> 0 <= n -> 0 <= base -> base + k * n <= two64 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M base (k * n) ->
  exists f, mem_arr k (run_segments R_segs rc_inp rc_sp rc_mb) M base n f /\ (forall i, 0 <= f i < 2 ^ (8 * k)).
Proof.
  intros k M base n Hk Hn Hb Hbn W.
  destruct (mem_wr_readable (run_segments R_segs rc_inp rc_sp rc_mb) wr_rd_R M base (k * n) W ltac:(lia)) as (bs & Hbs & Hlen).
  exists (le_cell k bs). split.
  - apply (mem_arr_of_bytes (run_segments R_segs rc_inp rc_sp rc_mb) k M base n bs Hbs); lia.
  - intros i. apply le_cell_range. exact Hk.
Qed.

Section ZA.
Context {RCa1 : RunCtx}.
Variables (u p q n gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z) (MD : Model) (T : TSet).
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

Definition st_init (vlen vofs vext vlb vdb vnc vnl vnd vsh : Z) : ist :=
  IST HEAD 0 (-1) 0 0 0 0 262144 0 vlen vofs vext (CDyn 0) (CDyn 0) vlb vdb vnc vnl vnd vsh 0 0 0.

Lemma ainv_init : forall (lf cf : Z -> Z) vlen vofs vext vlb vdb vnc vnl vnd vsh W0 ra,
  (forall i, 0 <= i < N_LENS -> 0 <= lf i < 65536) -> (forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296) ->
  0 <= vlen < 4294967296 -> 0 <= vofs < 4294967296 -> 0 <= vext < 4294967296 -> 0 <= vlb < 4294967296 -> 0 <= vdb < 4294967296 ->
  0 <= vnc < 4294967296 -> 0 <= vnl < 4294967296 -> 0 <= vnd < 4294967296 -> 0 <= vsh < 4294967296 ->
  ainv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 0 0 W0 ra) (st_init vlen vofs vext vlb vdb vnc vnl vnd vsh) lf cf.
Proof.
  intros lf cf vlen vofs vext vlb vdb vnc vnl vnd vsh W0 ra Hlf Hcf R1 R2 R3 R4 R5 R6 R7 R8 R9.
  pose proof two64_eq as TW64.
  unfold ainv, RNG, WIN, MODE, st_init, cxc; icx_cbn. cbv [N_CODES N_LENS WIN_SIZE]. cbv [N_CODES N_LENS] in Hlf, Hcf.
  split; [| split].
  - split_conj; first [assumption | lia_std | change (2 ^ 0) with 1; lia_std].
  - split; [intros _; split; reflexivity | intros C; exfalso; exact (C eq_refl)].
  - split_conj.
    + left. reflexivity.
    + intros _. split; [left; reflexivity | reflexivity].
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. unfold codes_liveP. cbv [LEN_ LIT HEAD]. lia_std.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros [E|E]; exfalso; revert E; cbv; discriminate.
Qed.

(* THE ENTRY STATE IN THE LIST FORM: the register facts, the four frame slots below the stream (at distances from
   the stream's address) and the extent of the writable stack range are fields of the layout text; the one bound
   value of the two lists is the input's length; the context record is the text's own, built for no window, no
   input used and no output made *)
Theorem za_cps_l : forall Rb l M,
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 0 0 0 0) None [n]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_za_entry ->
  rom_ok M -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (u + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.ZA_STK_LO) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.ZA_STK_LEN -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin ->
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds (run_segments R_segs rc_inp rc_sp rc_mb) (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 0 0 0 0) None [n]) M u OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_za_entry ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u) q -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 8) 0 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 64) A_ZCALLOC -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 ->
  KZE2 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M 0 ->
  KZW_l u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc 0 ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZA (zupd Rb l) M MD) T.
Proof.
  intros Rb l M RE ROM Wstk Wp Hin FE S8 S16 S72 S80 S88 HZE2 HZW.
  (* the two lists are opened (unfold, split, name); the stack range's two fields are unfolded *)
  open_za_lists. cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.ZA_STK_LO OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.ZA_STK_LEN] in Wstk.
  pose proof two64_eq as TW64.
  assert (Hwph : wok p q n zc 0).
  { unfold wok, ZSEP. cbv [WIN_SIZE ]. pose proof Hzimg as Hz'. cbv [DATA_LO DATA_LEN] in Hz'. split_conj; try lia_std; try (left; reflexivity). reflexivity. }
  eapply (za_prefix_s Rb l M MD T u p q n zc gp tp s5 s6 s7 s8 s9 s10 s11 fin Hh); try eassumption.
  intros R' M' vlen vofs vext vlb vdb vnc vnl vnd vsh.
  intros Gsp Gs0 Gs1 Gs2 Gs3 Gs4 Gs5 Ggp Gtp Gs6 Gs7 Gs8 Gs9 Gs10 Gs11
         ROM' Wstk' Wp' Hin' T8 T16 T32 T40 T64 T72 T80 T88
         P0 P8 P12 P16 P24 P48 P56 P60 P64 P68 P72 P80 P88 P92 P96 P100 P104 P112 P120 P124 P128 P132 P136 P140 P144 P7144
         Rlen Rofs Rext Rlb Rdb Rnc Rnl Rnd Rsh HP.
  zkeys. unfold ZSEP in *. cbv [STATE_SIZE FRA ROM_LO_ALL BUF A_ZCALLOC A_ZCFREE HEAD] in *.
  destruct (mem_wr_arrk_exists 2 M' (p + 168) 320 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(eapply mem_wr_sub; [exact Wp' | lia | lia])) as (lf & Hlens & Hlf).
  destruct (mem_wr_arrk_exists 4 M' (p + 1384) 1444 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(eapply mem_wr_sub; [exact Wp' | lia | lia])) as (cf & Hcodes & Hcf).
  change (2 ^ (8 * 2)) with 65536 in Hlf. change (2 ^ (8 * 4)) with 4294967296 in Hcf.
  pose proof (ainv_init lf cf vlen vofs vext vlb vdb vnc vnl vnd vsh (8 * (n - 0) + 0 + (262144 - 0)) RA_C2
                ltac:(intros i _; apply Hlf) ltac:(intros i _; apply Hcf) Rlen Rofs Rext Rlb Rdb Rnc Rnl Rnd Rsh) as AI.
  assert (HZE1 : KZE1 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M 0) by (intros R1 M1; intros; exfalso; lia_std).
  eapply (pcall_all_l u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hfin Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn
            Spq Spob Sobq Sprom Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 MEMCPY ADLER
            A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
            A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH 0 Hwph HZE2 HZE1 HZW
            (M2v n (st_init vlen vofs vext vlb vdb vnc vnl vnd vsh) + 1) false R' M' (st_init vlen vofs vext vlb vdb vnc vnl vnd vsh) lf cf).
  - exact AI.
  - lia.
  - unfold u2regs. zkeys. split_conj; assumption.
  - unfold e_mem, cxc, st_init, i_cst, i_hooks, st_at, st_rest, strm_at, cp_addr, wsz; icx_cbn. cbv [STATE_SIZE o_codes BUF A_ZCALLOC A_ZCFREE N_LENS N_CODES].
    cbn [Z.eqb].
    split_conj; try assumption;
      first [ apply buf_writable
            | intros i Hi; exfalso; lia_std
            | match goal with H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v |- mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v' => replace v' with v by lia_std; exact H
                            | H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v |- mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v' => replace v' with v by lia_std; exact H end ].
  - eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_u2 u p 0)) HP).
    intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; cbn [Z.eqb]; ranges_within_tac.
Qed.
End ZA.
