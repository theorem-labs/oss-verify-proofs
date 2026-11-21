(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I7U Require TBase.

Module T_Loop.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I7U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma reach_cases : forall m, reach m ->
  m = HEAD \/ m = DICTID \/ m = DICT \/ m = TYPE \/ m = TYPEDO \/ m = STORED \/ m = COPY_ \/ m = COPY \/
  m = TABLE \/ m = LENLENS \/ m = CODELENS \/ m = LEN_ \/ m = LEN \/ m = LENEXT \/ m = DIST \/ m = DISTEXT \/
  m = MATCH \/ m = LIT \/ m = CHECK \/ m = LENGTH \/ m = DONE \/ m = BAD \/ m = MEM.
Proof. intros m H. unfold reach in H. cbv [HEAD DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM] in *. lia. Qed.

Lemma reach_bounds : forall m, reach m -> 16180 <= m <= 16210.
Proof. intros m H. unfold reach in H. cbv [HEAD DICTID MEM] in H. lia. Qed.

Section Loop.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem).
Hypothesis CX : ctx_ok ROMHI_T cx.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < c_n cx -> 0 <= fin i < 256.

(* [comment removed for export] *)
Local Ltac open_join KM SI RE CX st :=
  pose proof KM as KM'; open_kmem KM';
  match goal with H : s_std _ _ _ |- _ => open_std H end;
  match goal with H : st_at _ _ _ _ |- _ => destruct H as [Hmode SREST] end;
  pose proof SI as SI'; dand SI' as (RNG_ & WIN_ & PROG_ & MODE_);
  match goal with H : MODE _ _ _ _ |- _ => pose proof (reach_bounds _ (proj1 H)) as Hmb end;
  pose proof CX as CX0;
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]; open_cx CX;
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext];
  icx_cbn;
  unfold s_regs_disp, s_regs_arm, s_regs_redisp, s_fix, s_vars in RE; icx_cbn; destr_conj RE; zgetl_nil;
  zkeysb; unfold L_DISP, L_REDISP, L_REDISP_A1, L_BADMSG_A0, L_BADMSG_A5, L_BADMSG_A5B, L_BADMSG_A1,
    L_LEAVE, L_LEAVE_LD, L_LEAVE_LD2, L_RET, L_MEM, L_DONE in *;
  cbv [JTAB_ADDR] in *; pose proof two64_eq as TW64.

Local Ltac regs_tac := unfold s_regs_disp, s_regs_arm, s_regs_redisp, s_regs_leave, s_regs_leave_ld, s_regs_leave_ld2, s_regs_ret, s_fix, s_vars;
                       icx_cbn; cbv [JTAB_ADDR]; zkeys; split_conj; zreg.

(* [comment removed for export] *)
Local Ltac frame_cells FRM :=
  let F := fresh "FRM'" in pose proof FRM as F; unfold i_frame in F; icx_cbn;
  dand F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C136 & _ & _ & _ & _ & C80 & _).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kredisp_of_kdisp : forall B, KDISP cx fin MD T M0 B -> KREDISP cx fin MD T M0 B.
Proof.
  intros B K R M st lf cf SI MB RE KM. open_join KM SI RE CX st. frame_cells FRM.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
    eapply (K R' Mx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI MB) end.
  - regs_tac.
  - exact KM.
Qed.

Lemma kredisp_a1_of_kdisp : forall B, KDISP cx fin MD T M0 B -> KREDISP_A1 cx fin MD T M0 B.
Proof.
  intros B K R M st lf cf SI MB RE Ra3 KM. open_join KM SI RE CX st. frame_cells FRM. zgetl_nil.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
    eapply (K R' Mx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI MB) end.
  - regs_tac.
  - exact KM.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac badmsg_tail K last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext lf cf SI MB SREST HAG :=
  lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
    eapply (K R' Mx (IST BAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI MB) end;
  [ regs_tac
  | unfold k_mem; icx_cbn; split_conj;
    first [ assumption | close_std | unfold st_at, st_rest; icx_cbn; cbv [BAD]; split_conj; assumption
          | unfold s_ret; icx_cbn; assumption | unfold s_lo; icx_cbn; split_conj; assumption | exact HAG | sbk ] ].

Local Ltac open_bad KM CX st RE :=
  pose proof KM as KM'; open_kmem KM';
  match goal with H : s_std _ _ _ |- _ => open_std H end;
  match goal with H : st_at _ _ _ _ |- _ => destruct H as [Hmode SREST] end;
  pose proof CX as CX0;
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]; open_cx CX;
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext];
  icx_cbn; unfold s_fix in RE; icx_cbn; destr_conj RE; zgetl_nil;
  zkeysb; unfold L_DISP, L_REDISP_A1, L_BADMSG_A0, L_BADMSG_A5, L_BADMSG_A5B, L_BADMSG_A1 in *; cbv [JTAB_ADDR] in *;
  pose proof two64_eq as TW64;
  match goal with H : mpostL _ _ _ _ |- _ => fp_frame_from H end; clear KM;
  match goal with H : st_rest _ _ _ _ |- _ => unfold st_rest in H end;
  match goal with H : s_ret _ _ _ |- _ => unfold s_ret in H end;
  match goal with H : s_lo _ _ _ |- _ => unfold s_lo in H end;
  icx_cbn;
  match goal with H : _ /\ _ |- _ => idtac end;
  repeat match goal with H : mem_u32 _ _ _ _ /\ _ |- _ => destr_conj H | H : mem_u64 _ _ _ _ /\ _ |- _ => destr_conj H end.

Lemma kbadmsg_a0_of_kdisp : forall B, KDISP cx fin MD T M0 B -> KBADMSG_A0 cx fin MD T M0 B.
Proof.
  intros B K R M st lf cf SI MB Rsp Rgp Rtp Rs11 Rs0 Rs9 Rs7 Rs2 Rs3 Rs1 Ha0 KM. unfold bad_of in SI, MB.
  assert (RE : True) by exact I.
  open_bad KM CX st RE. zgetl_nil. frame_cells FRM.
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  badmsg_tail K last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext lf cf SI MB SREST HAG.
Qed.

Lemma kbadmsg_a5_of_kdisp : forall B, KDISP cx fin MD T M0 B -> KBADMSG_A5 cx fin MD T M0 B.
Proof.
  intros B K R M st lf cf SI MB RE Ra4 Ra2 Rs2 Rs3 Rs1 Ha5 KM. unfold bad_of in SI, MB.
  open_bad KM CX st RE. zgetl_nil.
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  badmsg_tail K last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext lf cf SI MB SREST HAG.
Qed.

Lemma kbadmsg_a5b_of_kdisp : forall B, KDISP cx fin MD T M0 B -> KBADMSG_A5B cx fin MD T M0 B.
Proof.
  intros B K R M st lf cf SI MB RE Ra4 Ra2 Rs2 Rs3 Rs1 KM.
  pose proof KM as KM'. open_kmem KM'. pose proof CX as CX0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]; open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. unfold s_fix in RE; icx_cbn; destr_conj RE; zgetl_nil.
  zkeysb. unfold L_DISP, L_BADMSG_A5B in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
    eapply (K R' Mx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI MB) end.
  - regs_tac.
  - exact KM.
Qed.

Lemma kbadmsg_a1_of_kdisp : forall B, KDISP cx fin MD T M0 B -> KBADMSG_A1 cx fin MD T M0 B.
Proof.
  intros B K R M st lf cf SI MB Rsp Rgp Rtp Rs11 Rs0 Rra Ra7 Rs7 Rs2 Rs3 Rs1 Ha1 KM. unfold bad_of in SI, MB.
  assert (RE : True) by exact I.
  open_bad KM CX st RE. zgetl_nil. frame_cells FRM.
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  badmsg_tail K last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext lf cf SI MB SREST HAG.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kleave_ld_of_kleave : KLEAVE cx fin MD T M0 -> KLEAVE_LD cx fin MD T M0.
Proof.
  intros K R M st lf cf SI RE STD SAT SRET SLO SBK Hlens Hcodes HP0.
  pose proof STD as STD0. open_std STD. pose proof CX as CX0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]; open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. unfold s_regs_leave_ld in RE; icx_cbn; destr_conj RE; zgetl_nil. unfold s_ret in SRET. icx_cbn.
  zkeysb. unfold L_LEAVE_LD, L_LEAVE in *. pose proof two64_eq as TW64.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
    eapply (K R' Mx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf SI) end;
    try assumption.
  regs_tac.
Qed.

Lemma kleave_ld2_of_kleave : KLEAVE cx fin MD T M0 -> KLEAVE_LD2 cx fin MD T M0.
Proof.
  intros K R M st lf cf SI RE STD SAT SRET SLO SBK Hlens Hcodes HP0.
  pose proof STD as STD0. open_std STD. pose proof CX as CX0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]; open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. unfold s_regs_leave_ld2 in RE; icx_cbn; destr_conj RE; zgetl_nil. unfold s_ret in SRET. icx_cbn.
  zkeysb. unfold L_LEAVE_LD2, L_LEAVE in *. pose proof two64_eq as TW64. frame_cells FRM.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
    eapply (K R' Mx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf SI) end;
    try assumption.
  regs_tac.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kall_of_kdisp : forall B, KDISP cx fin MD T M0 B -> KLEAVE cx fin MD T M0 -> KRET cx fin MD T M0 -> KALL cx fin MD T M0 B.
Proof.
  intros B K KL KR. unfold KALL; split_conj.
  - exact K.
  - apply kredisp_of_kdisp; exact K.
  - apply kredisp_a1_of_kdisp; exact K.
  - apply kbadmsg_a0_of_kdisp; exact K.
  - apply kbadmsg_a5_of_kdisp; exact K.
  - apply kbadmsg_a5b_of_kdisp; exact K.
  - apply kbadmsg_a1_of_kdisp; exact K.
  - exact KL.
  - apply kleave_ld_of_kleave; exact KL.
  - apply kleave_ld2_of_kleave; exact KL.
  - exact KR.
Qed.

Lemma kdisp_mono : forall B B', B' <= B -> KDISP cx fin MD T M0 B -> KDISP cx fin MD T M0 B'.
Proof. intros B B' HB K R M st lf cf SI MB. apply (K R M st lf cf SI). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Step.
Hypothesis KL : KLEAVE cx fin MD T M0.
Hypothesis KR : KRET cx fin MD T M0.
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
Hypothesis OBLOW : c_ob cx + c_osz cx <= c_u cx - FRA.
Hypothesis A_CHECK : arm_stmt_ob L_CHECK CHECK.
Hypothesis A_LENGTH : arm_stmt L_LENGTH LENGTH.

Lemma kdisp_step : forall B, KDISP cx fin MD T M0 B -> KDISP cx fin MD T M0 (B + 1).
Proof.
  intros B K R M st lf cf SI MB RE KM.
  assert (KA : KALL cx fin MD T M0 (meas cx st)).
  { apply kall_of_kdisp; [| exact KL | exact KR]. eapply kdisp_mono; [| exact K]. lia. }
  clear K. open_join KM SI RE CX st.
  pose proof (rom_jtab_arr M ROM) as HJ.
  pose proof (reach_cases mode (proj1 MODE_)) as CASES.
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C104 & C96 & _).
  cbv [JTAB_ADDR] in C96.
  clear RNG_ WIN_ PROG_ MODE_ FRM CST HK Hin Wstk Wp Wob Ww SREST SRET SLO Hlens Hcodes HP0 SBK.
  cbv [HEAD DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM] in CASES.
  Local Ltac disp :=
    tstep1 Rfd;                       (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    zbr Rfd true;                     (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    tstep Rfd; zlit;                  (* [comment removed for export] *)
    zstep Rfd; zlit;                  (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
  Local Ltac arm A CX0 SI KM KA :=
    lazymatch type of SI with sinv _ ?st ?lf ?cf =>
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (A _ fin MD T M0 R' l' Mx st lf cf CX0 Hh Hfin eq_refl SI); [regs_tac | exact KM | exact KA] end end.
  decompose [or] CASES; clear CASES; match goal with Hc : mode = _ |- _ => rewrite Hc in *; clear Hc; try clear mode end.
  - disp. arm A_HEAD CX0 SI KM KA.
  - disp. arm A_DICTID CX0 SI KM KA.
  - disp. arm A_DICT CX0 SI KM KA.
  - disp. arm A_TYPE CX0 SI KM KA.
  - disp. arm A_TYPEDO CX0 SI KM KA.
  - disp. arm A_STORED CX0 SI KM KA.
  - disp. arm A_COPY_ CX0 SI KM KA.
  - disp. arm A_COPY CX0 SI KM KA.
  - disp. arm A_TABLE CX0 SI KM KA.
  - disp. arm A_LENLENS CX0 SI KM KA.
  - disp. arm A_CODELENS CX0 SI KM KA.
  - disp. arm A_LEN_ CX0 SI KM KA.
  - disp. arm A_LEN CX0 SI KM KA.
  - disp. arm A_LENEXT CX0 SI KM KA.
  - disp. arm A_DIST CX0 SI KM KA.
  - disp. arm A_DISTEXT CX0 SI KM KA.
  - disp. arm A_MATCH CX0 SI KM KA.
  - disp. arm A_LIT CX0 SI KM KA.
  - disp. lazymatch type of SI with sinv _ ?st ?lf ?cf =>
          lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
            eapply (A_CHECK _ fin MD T M0 R' l' Mx st lf cf CX0 OBLOW Hh Hfin eq_refl SI); [regs_tac | exact KM | exact KA] end end.
  - disp. arm A_LENGTH CX0 SI KM KA.
  - (* [comment removed for export] *)
    disp. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KL R' Mx (IST 16208 last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) 1 lf cf SI) end;
      [regs_tac | | | | | | | ]; pose proof KM as KM'; open_kmem KM'; try assumption.
  - (* [comment removed for export] *)
    disp.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KL R' Mx (IST 16209 last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) (-3) lf cf SI) end;
      [regs_tac | | | | | | | ]; pose proof KM as KM'; open_kmem KM'; try assumption.
  - (* [comment removed for export] *)
    disp. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KR R' Mx (-4) 16210) end;
      [ cbv; discriminate | regs_tac | | | unfold reach; cbv [HEAD DICTID MEM]; lia_std | ];
      pose proof KM as KM'; open_kmem KM'; try assumption;
      match goal with H : st_at _ _ _ _ |- _ => exact (proj1 H) end.
Qed.

(* [comment removed for export] *)
Lemma loop_nat : forall k : nat, KDISP cx fin MD T M0 (Z.of_nat k).
Proof.
  induction k as [|k IH].
  - intros R M st lf cf SI MB. exfalso. pose proof (meas_nonneg _ _ _ _ SI). cbn [Z.of_nat] in MB. lia.
  - rewrite Nat2Z.inj_succ. apply kdisp_step. exact IH.
Qed.

Theorem loop_t : forall B, KDISP cx fin MD T M0 B.
Proof. intros B. apply (kdisp_mono (Z.of_nat (Z.to_nat B))); [lia | apply loop_nat]. Qed.

(* [comment removed for export] *)
Theorem kall_t : forall B, KALL cx fin MD T M0 B.
Proof. intros B. apply kall_of_kdisp; [apply loop_t | exact KL | exact KR]. Qed.
End Step.

End Loop.
End T_Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I7U Require Import TBase. Import T_Loop.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* [comment removed for export] *)
Definition mode_load (m : Z) : Z := if m =? TYPE then TYPEDO else m.
Definition st_load (cx : ictx) (st : ist) : ist :=
  IST (mode_load (t_mode st)) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st)
      (c_osz cx - t_cout st) 0
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma mode_load_reach : forall m, reach m -> reach (mode_load m) /\ 16180 <= mode_load m <= 16210.
Proof.
  intros m H. unfold mode_load, reach in *. cbv [HEAD DICTID MEM TYPE TYPEDO] in *.
  destruct (Z.eqb_spec m 16191); lia_std.
Qed.
Lemma mode_load_eq : forall m v, mode_load m = v -> v <> TYPEDO -> m = v.
Proof. intros m v E Hv. revert E. unfold mode_load. destruct (Z.eqb_spec m TYPE); intros E; [congruence | exact E]. Qed.
(* [comment removed for export] *)
Lemma mode_load_live : forall m, codes_liveP (mode_load m) -> codes_liveP m.
Proof. intros m. unfold codes_liveP, mode_load. cbv [TYPE TYPEDO LEN_ LIT]. destruct (Z.eqb_spec m 16191); lia_std. Qed.

(* [comment removed for export] *)
Lemma sinv_load : forall cx st lf cf,
  ctx_ok ROMHI_T cx -> ainv cx st lf cf ->
  c_cin0 cx = t_cin st -> c_cout0 cx = t_cout st -> c_W0 cx = Wm cx st ->
  sinv cx (st_load cx st) lf cf.
Proof.
  intros cx st lf cf CX (R & W & Mo) H1 H2 H3.
  split; [| split; [exact W | split]].
  - (* [comment removed for export] *) pose proof (proj1 CX) as L. unfold ctx_lin in L. clear CX W Mo.
    destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
    destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
    unfold RNG, st_load in *. icx_cbn. cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL] in L.
    destr_conj R. destr_conj L. pose proof two64_eq as TW64.
    split_conj; try assumption; lia_std.
  - (* [comment removed for export] *) clear CX W Mo R. destruct cx, st. unfold PROG, Wm, st_load in *. icx_cbn. split; [lia_std | split; [lia_std | left; lia_std]].
  - (* [comment removed for export] *) clear CX W R H1 H2 H3. dand Mo as (Mr & Mf & Mll & Mcl & Mlive & Mle & Mdi & Mde & Mma & Mco).
    destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
    destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
    unfold MODE, st_load in *. icx_cbn. split_conj.
    + exact (proj1 (mode_load_reach mode Mr)).
    + intros Hf. destruct (Mf Hf) as [Hm Hc]. split; [|exact Hc].
      assert (Hm' : mode <> TYPE) by (clear - Hm; cbv [TYPE HEAD BAD] in *; lia_std).   (* [comment removed for export] *)
      unfold mode_load. destruct (Z.eqb_spec mode TYPE); [contradiction | exact Hm].
    + intros E. apply Mll. apply (mode_load_eq _ _ E). cbv; discriminate.
    + intros E. assert (E' : mode = CODELENS) by (apply (mode_load_eq _ _ E); cbv; discriminate).
      dand (Mcl E') as (A1 & A2 & A3 & A4 & A5 & A6 & A7). split_conj; assumption.
    + intros Hl. exact (Mlive (mode_load_live _ Hl)).
    + intros E. apply Mle. apply (mode_load_eq _ _ E). cbv; discriminate.
    + intros E. apply Mdi. apply (mode_load_eq _ _ E). cbv; discriminate.
    + intros E. apply Mde. apply (mode_load_eq _ _ E). cbv; discriminate.
    + intros E. apply Mma. apply (mode_load_eq _ _ E). cbv; discriminate.
    + intros [E|E]; apply Mco; [left | right]; apply (mode_load_eq _ _ E); cbv; discriminate.
Qed.

(* [comment removed for export] *)
Definition e_mem {RCa1 : RunCtx}  (cx : ictx) (fin : Z -> Z) (st : ist) (lf cf : Z -> Z) (M : mem) : Prop :=
  rom_ok M /\
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -1024) 1232 /\ mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx) STATE_SIZE /\
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (c_ob cx) (c_osz cx) /\ mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (c_w cx) (wsz cx) /\
  i_cst (run_segments R_segs rc_inp rc_sp rc_mb) cx M /\ i_hooks cx M /\ mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_q cx) (c_n cx) fin /\
  st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M /\ strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf /\
  s_bk cx st M.   (* [comment removed for export] *)
Ltac open_emem H := let ROM := ident:(ROM) in let Wstk := ident:(Wstk) in let Wp := ident:(Wp) in let Wob := ident:(Wob) in let Ww := ident:(Ww) in let CST := ident:(CST) in let HK := ident:(HK) in let Hin := ident:(Hin) in let SAT := ident:(SAT) in let STRM := ident:(STRM) in let Hlens := ident:(Hlens) in let Hcodes := ident:(Hcodes) in let SBK := ident:(SBK) in (first [ dand H as (ROM & Wstk & Wp & Wob & Ww & CST & HK & Hin & SAT & STRM & Hlens & Hcodes & SBK)
        | let S := fresh "SBK" in dand H as (ROM & Wstk & Wp & Wob & Ww & CST & HK & Hin & SAT & STRM & Hlens & Hcodes & S) ]).

Theorem entry_t {RCa1 : RunCtx}  : forall cx fin MD T Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ainv cx st lf cf -> c_cin0 cx = t_cin st -> c_cout0 cx = t_cout st -> c_W0 cx = Wm cx st ->
  s_regs_entry cx Rb l -> e_mem cx fin st lf cf M ->
  KDISP cx fin MD T M (meas cx (st_load cx st) + 1) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_INFLATE (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T Rb l M st lf cf CX Hh Hfin AI Hc1 Hc2 Hc3 RE EM K.
  pose proof (sinv_load cx st lf cf CX AI Hc1 Hc2 Hc3) as SI.
  open_emem EM. destruct SAT as [Hmode SREST].
  pose proof AI as AI'. dand AI' as (RNG_ & WIN_ & MODE_).
  pose proof (proj1 MODE_) as Hreach. pose proof CX as CX0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX. dand AL as (ALu & ALp & ALw).
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst cin0 cout0.
  pose proof (proj2 (mode_load_reach mode Hreach)) as Hmlb. pose proof (reach_bounds _ Hreach) as Hmb.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  unfold s_regs_entry in RE. icx_cbn. destr_conj RE.
  zkeysb. unfold L_INFLATE, L_DISP in *. cbv [A_ZCALLOC A_ZCFREE] in *. pose proof two64_eq as TW64.
  fp_frame_init (fp_loop (ICX u p q n ob osz w cin cout W0 K0 zc)) M.
  zstep Rfd.                          (* [comment removed for export] *)
  do 13 (tstep1 Rfd).                 (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd. zalign.                  (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
    pose proof HK as HK'; destruct HK' as [C72 C80];
    pose proof CST as CST'; unfold i_cst in CST'; icx_cbn; dand CST' as (C64 & _ & Cp0 & _) end.
  zstep Rfd. zbr Rfd true.            (* [comment removed for export] *)
  zstep Rfd. zbr Rfd true.            (* [comment removed for export] *)
  zstep Rfd. zbr Rfd true.            (* [comment removed for export] *)
  zstep Rfd. zalign.                  (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd. zbr Rfd true.            (* [comment removed for export] *)
  clear C72 C80 C64 Cp0.
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd. zstep Rfd. zlit.         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
    pose proof STRM as STRM'; unfold strm_at in STRM'; icx_cbn; dand STRM' as (S8 & _ & S32 & _) end.
  zstep Rfd. zbr Rfd true.            (* [comment removed for export] *)
  zstep Rfd. zbr Rfd true.            (* [comment removed for export] *)
  clear S8 S32.
  zstep Rfd. zstep Rfd.               (* [comment removed for export] *)
  zstep Rfd. zstep Rfd. zstep Rfd.    (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?lc) ?Mc _) _ =>
  assert (J : forall RJ Mq,
    zget RJ kSP = u + -256 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP ->
    zget RJ kS0 = p -> zget RJ kA3 = u -> zget RJ kA1 = 0 ->
    zget RJ kA4 = 7160 -> zget RJ kA5 = 16384 -> zget RJ kRA = 16209 ->
    zget RJ kS3 = ob + cout -> zget RJ kS10 = q + cin ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 8) (mode_load mode) ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mc Mq [(p + 8, 4)] ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 86968 (* [comment removed for export] *) (zupd RJ []) Mq MD) T) end.
  { intros RJ Mq. intros. zimps. zkeys.
    match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) _ Mq _ |- _ => clear Hmode; zreattachL HP end.
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      pose proof STRM as STRM'; unfold strm_at in STRM'; icx_cbn; dand STRM' as (_ & S16 & _ & S40 & S80 & S88) end.
    tstep1 Rfd.                       (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    clear S16 S40 S80 S88 STRM.
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd. tstep1 Rfd.            (* [comment removed for export] *)
    zstep Rfd. tstep1 Rfd.            (* [comment removed for export] *)
    zstep Rfd. tstep1 Rfd.            (* [comment removed for export] *)
    zstep Rfd. tstep1 Rfd.            (* [comment removed for export] *)
    zstep Rfd. tstep1 Rfd.            (* [comment removed for export] *)
    zstep Rfd. zlit. tstep1 Rfd.      (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd. znot.                  (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd. zlit.                  (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd. zstep Rfd. zlit.       (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (K R' Mx (st_load (ICX u p q n ob osz w cin cout W0 K0 zc)
                 (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) lf cf SI) end.
    - lia.
    - unfold s_regs_disp, s_fix, s_vars, st_load; icx_cbn; cbv [JTAB_ADDR]; zkeys; split_conj; zreg.
    - unfold k_mem, st_load; icx_cbn. split_conj.
      + unfold s_std; icx_cbn; split_conj; try assumption.
        unfold i_frame; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; try assumption.
        all: match goal with H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v |- mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v' =>
               replace v' with v by lia_std; exact H end.
      + unfold st_at; icx_cbn. split; [assumption | exact SREST].
      + unfold s_ret; icx_cbn. assumption.
      + unfold s_lo; icx_cbn. split; assumption.
      + exact Hlens.
      + exact Hcodes.
      + exact HAG.
      + (* [comment removed for export] *)
        dand SBK as (c & Hc & Hc0 & Hc1 & Hc2). exists c. icx_cbn. split; [exact Hc | split; [exact Hc0 |]].
        unfold mode_load. destruct (Z.eqb_spec mode TYPE) as [Em|Em];
          [cbv [TYPEDO LENEXT DIST]; split; intros E; exfalso; lia_std | split; assumption]. }
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
    pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) Mc [(p + 8, 4)] ltac:(ranges_ok_tac)) as HST2;
    assert (HAG2 : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mc X [(p + 8, 4)]) Mc) by (apply mpostL_refl) end.
  destruct (Z.eq_dec mode 16191) as [Em | Em].
  - (* [comment removed for export] *)
    zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => apply (J R' Mx) end;
      first [ zreg | assumption | exact HAG2
            | unfold mode_load; cbv [TYPE TYPEDO]; rewrite Em; cbn [Z.eqb Pos.eqb]; first [zreg | assumption] ].
  - (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => apply (J R' Mx) end;
      first [ zreg | assumption | exact HAG2
            | unfold mode_load; cbv [TYPE TYPEDO]; destruct (Z.eqb_spec mode 16191); [lia_std | first [zreg | assumption]] ].
Qed.
