(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* The entry text of the plain uncompress walk, in the run form: every stretch of step lines is ONE RUN of the
   driver (to the next join point's continuation, or to the next open branch); no step count and no branch
   direction is written; the one inner join point of the entry takes its label and its register map from the
   layout text (a list; its meaning by the shared meaning function). Every statement that a text outside this
   one uses is word for word the hand text's. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SBase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZGo11 SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.

Module S_Loop.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
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

Lemma reach_cases : forall m, reach m ->
  m = HEAD \/ m = DICTID \/ m = DICT \/ m = TYPE \/ m = TYPEDO \/ m = STORED \/ m = COPY_ \/ m = COPY \/
  m = TABLE \/ m = LENLENS \/ m = CODELENS \/ m = LEN_ \/ m = LEN \/ m = LENEXT \/ m = DIST \/ m = DISTEXT \/
  m = MATCH \/ m = LIT \/ m = CHECK \/ m = LENGTH \/ m = DONE \/ m = BAD \/ m = MEM.
Proof. intros m H. unfold reach in H. cbv [HEAD DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM] in *. lia. Qed.

Lemma reach_bounds : forall m, reach m -> 16180 <= m <= 16210.
Proof. intros m H. unfold reach in H. cbv [HEAD DICTID MEM] in H. lia. Qed.

Section Loop.
Context {RCa1 : RunCtx}.
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem).
Hypothesis CX : ctx_ok ROMHI_S cx.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < c_n cx -> 0 <= fin i < 256.

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
  unfold s_regs_disp, s_regs_d10, s_regs_d0, s_regs_arm, s_regs_reload, s_fix, s_vars in RE; icx_cbn; destr_conj RE; zgetl_nil;
  zkeysb; unfold L_DISP, L_DISP0, L_DISP10, L_SETMODE, L_RELOAD_A1, L_RELOAD_RA, L_RELOAD, L_BADMSG_S11, L_BADMSG_S10, L_BADMSG_A3,
    L_LEAVE, L_LEAVE_LD, L_RET, L_MEM, L_DONE in *;
  cbv [JTAB_ADDR] in *; pose proof two64_eq as TW64.

Local Ltac st_of mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext :=
  constr:(IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext).

Local Ltac regs_tac := unfold s_regs_disp, s_regs_d10, s_regs_d0, s_regs_arm, s_regs_leave, s_regs_leave_ld, s_regs_ret, s_fix, s_vars;
                       icx_cbn; cbv [JTAB_ADDR]; zkeys; split_conj; zreg.

(* the application of a join point's continuation: it applies only when the goal's pc is that join point.
   Its body starts with `idtac;` so that it runs where the driver runs it, not where it is written. *)
Local Ltac kapp K s lf cf SI MB :=
  idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => eapply (K R' Mx s lf cf SI MB) end.

Lemma kdisp_of_kd0 : forall B, KD0 cx fin MD T M0 B -> KDISP cx fin MD T M0 B.
Proof.
  intros B K R M st lf cf SI MB RE KM. open_join KM SI RE CX st.
  zuntil Rfd (kapp K (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI MB).
  - regs_tac.
  - exact KM.
Qed.

Lemma kdisp10_of_kd0 : forall B, KD0 cx fin MD T M0 B -> KDISP10 cx fin MD T M0 B.
Proof.
  intros B K R M st lf cf SI MB RE KM. open_join KM SI RE CX st.
  zuntil Rfd (kapp K (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI MB).
  - regs_tac.
  - exact KM.
Qed.

Lemma ksetmode_of_kd0 : forall B, KD0 cx fin MD T M0 B -> KSETMODE cx fin MD T M0 B.
Proof.
  intros B K R M st m lf cf SI MB RE STD Hm SREST SRET SOUT Hlens Hcodes HP0.
  assert (KM : True) by exact I.
  pose proof STD as STD0. open_std STD.
  pose proof SI as SI'; dand SI' as (RNG_ & WIN_ & PROG_ & MODE_).
  pose proof (reach_bounds _ (proj1 MODE_)) as Hmb. pose proof CX as CX0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]; open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. unfold s_regs_d0, s_fix, s_vars in RE; icx_cbn; destr_conj RE; zgetl_nil.
  zkeysb. unfold L_SETMODE, L_DISP0 in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  clear STD0. unfold st_rest in SREST. unfold s_ret in SRET. unfold s_out in SOUT. icx_cbn. destr_conj SREST.
  zuntil Rfd (kapp K (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI MB).
  - regs_tac.
  - unfold k_mem; icx_cbn; split_conj;
      first [ assumption | close_std | unfold st_at, st_rest; icx_cbn; split_conj; assumption
            | unfold s_ret; icx_cbn; assumption | unfold s_out; icx_cbn; assumption | exact HAG ].
Qed.

Lemma kreload_of_kdisp : forall B, KDISP cx fin MD T M0 B -> KRELOAD cx fin MD T M0 B.
Proof.
  intros B K R M st lf cf SI MB RE KM. open_join KM SI RE CX st.
  repeat match goal with H : ?b = ?b -> _ |- _ => specialize (H eq_refl) | H : true = false -> _ |- _ => clear H | H : false = true -> _ |- _ => clear H end.
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn. destr_conj FRM'.
  zuntil Rfd (kapp K (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI MB).
  - regs_tac.
  - exact KM.
Qed.

Lemma kreload_ra_of_kdisp : forall B, KDISP cx fin MD T M0 B -> KRELOAD_RA cx fin MD T M0 B.
Proof.
  intros B K R M st lf cf SI MB RE KM. pose proof (kreload_of_kdisp B K) as K'. open_join KM SI RE CX st.
  repeat match goal with H : ?b = ?b -> _ |- _ => specialize (H eq_refl) | H : true = false -> _ |- _ => clear H | H : false = true -> _ |- _ => clear H end.
  (* the frame's facts are opened *)
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn. destr_conj FRM'.
  zuntil Rfd (kapp K' (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI MB).
  - unfold s_regs_reload; icx_cbn; cbv [JTAB_ADDR]; zkeys; split_conj; try zreg; intros HH; try discriminate HH; zreg.
  - exact KM.
Qed.

Lemma kreload_a1_of_kdisp : forall B, KDISP cx fin MD T M0 B -> KRELOAD_A1 cx fin MD T M0 B.
Proof.
  intros B K R M st lf cf SI MB RE KM. pose proof (kreload_ra_of_kdisp B K) as K'. open_join KM SI RE CX st.
  repeat match goal with H : ?b = ?b -> _ |- _ => specialize (H eq_refl) | H : true = false -> _ |- _ => clear H | H : false = true -> _ |- _ => clear H end.
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn. destr_conj FRM'.
  zuntil Rfd (kapp K' (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI MB).
  - unfold s_regs_reload; icx_cbn; cbv [JTAB_ADDR]; zkeys; split_conj; try zreg; intros HH; try discriminate HH; zreg.
  - exact KM.
Qed.

Local Ltac bad_mem HAG :=
  unfold k_mem; icx_cbn; split_conj;
  first [ assumption | close_std | unfold st_at, st_rest; icx_cbn; cbv [BAD]; split_conj; assumption
        | unfold s_ret; icx_cbn; assumption | unfold s_out; icx_cbn; first [ exact I | assumption ] | exact HAG ].

Lemma kbadmsg_s11_of_kdisp : forall B, KDISP cx fin MD T M0 B -> KBADMSG_S11 cx fin MD T M0 B.
Proof.
  intros B K R M st lf cf SI MB RE Ha2 KM. unfold bad_of in SI, MB.
  pose proof KM as KM'; open_kmem KM'; open_std STD; destruct SAT as [Hmode SREST].
  pose proof CX as CX0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]; open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. unfold s_regs_disp, s_fix, s_vars in RE; icx_cbn; destr_conj RE; zgetl_nil.
  zkeysb. unfold L_BADMSG_S11, L_DISP in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0. clear KM. unfold st_rest in SREST. unfold s_ret in SRET. unfold s_out in SOUT. icx_cbn. destr_conj SREST.
  zuntil Rfd (kapp K (IST BAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI MB);
  [ regs_tac | bad_mem HAG ].
Qed.

Lemma kbadmsg_s10_of_kdisp10 : forall B, KDISP10 cx fin MD T M0 B -> KBADMSG_S10 cx fin MD T M0 B.
Proof.
  intros B K R M st lf cf SI MB RE Ha2 KM. unfold bad_of in SI, MB.
  pose proof KM as KM'; open_kmem KM'; open_std STD; destruct SAT as [Hmode SREST].
  pose proof CX as CX0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]; open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. unfold s_regs_d10, s_fix, s_vars in RE; icx_cbn; destr_conj RE; zgetl_nil.
  zkeysb. unfold L_BADMSG_S10, L_DISP10 in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0. clear KM. unfold st_rest in SREST. unfold s_ret in SRET. unfold s_out in SOUT. icx_cbn. destr_conj SREST.
  zuntil Rfd (kapp K (IST BAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI MB);
  [ regs_tac | bad_mem HAG ].
Qed.

Lemma kbadmsg_a3_of_kdisp : forall B, KDISP cx fin MD T M0 B -> KBADMSG_A3 cx fin MD T M0 B.
Proof.
  (* this statement's register premises are taken in without a count, and the memory relation is found by
     its form *)
  intros B K R M st lf cf SI MB RF. intros.
  match goal with H : k_mem _ _ _ _ _ _ _ |- _ => rename H into KM end.
  unfold bad_of in SI, MB.
  pose proof KM as KM'; open_kmem KM'; open_std STD; destruct SAT as [Hmode SREST].
  pose proof CX as CX0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]; open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. unfold s_fix in RF; icx_cbn; destr_conj RF; zgetl_nil.
  zkeysb. unfold L_BADMSG_A3, L_DISP in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0. clear KM. unfold st_rest in SREST. unfold s_ret in SRET. unfold s_out in SOUT. icx_cbn. destr_conj SREST.
  zuntil Rfd (kapp K (IST BAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI MB);
  [ regs_tac | bad_mem HAG ].
Qed.

Lemma kleave_ld_of_kleave : KLEAVE cx fin MD T M0 -> KLEAVE_LD cx fin MD T M0.
Proof.
  intros K R M st lf cf SI RE STD SAT SRET SOUT Hlens Hcodes HP0.
  pose proof STD as STD0. open_std STD. pose proof CX as CX0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]; open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. unfold s_regs_leave_ld in RE; icx_cbn; destr_conj RE; zgetl_nil. unfold s_ret in SRET. icx_cbn.
  zkeysb. unfold L_LEAVE_LD, L_LEAVE in *. pose proof two64_eq as TW64.
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
    eapply (K R' Mx (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf SI) end);
    try assumption.
  regs_tac.
Qed.

Lemma kall_of_kd0 : forall B, KD0 cx fin MD T M0 B -> KLEAVE cx fin MD T M0 -> KRET cx fin MD T M0 -> KALL cx fin MD T M0 B.
Proof.
  intros B K KL KR.
  pose proof (kdisp_of_kd0 B K) as KD. pose proof (kdisp10_of_kd0 B K) as KD10.
  unfold KALL; split_conj.
  - exact KD.
  - exact KD10.
  - exact K.
  - apply ksetmode_of_kd0; exact K.
  - apply kreload_a1_of_kdisp; exact KD.
  - apply kreload_ra_of_kdisp; exact KD.
  - apply kreload_of_kdisp; exact KD.
  - apply kbadmsg_s11_of_kdisp; exact KD.
  - apply kbadmsg_s10_of_kdisp10; exact KD10.
  - apply kbadmsg_a3_of_kdisp; exact KD.
  - exact KL.
  - apply kleave_ld_of_kleave; exact KL.
  - exact KR.
Qed.

Lemma kd0_mono : forall B B', B' <= B -> KD0 cx fin MD T M0 B -> KD0 cx fin MD T M0 B'.
Proof. intros B B' HB K R M st lf cf SI MB. apply (K R M st lf cf SI). lia. Qed.

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

Lemma kd0_step : forall B, KD0 cx fin MD T M0 B -> KD0 cx fin MD T M0 (B + 1).
Proof.
  intros B K R M st lf cf SI MB RE KM.
  assert (KA : KALL cx fin MD T M0 (meas cx st)).
  { apply kall_of_kd0; [| exact KL | exact KR]. eapply kd0_mono; [| exact K]. lia. }
  clear K. open_join KM SI RE CX st.
  pose proof (rom_jtab_arr M ROM) as HJ.
  pose proof (reach_cases mode (proj1 MODE_)) as CASES.
  clear RNG_ WIN_ PROG_ MODE_ FRM CST HK Hin Wstk Wp Wob Ww SREST SRET SOUT Hlens Hcodes HP0.
  cbv [HEAD DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM] in CASES.
  (* the arm's statement applies only at the arm's label: each case below is ONE RUN from the dispatch to it *)
  Local Ltac arm A CX0 SI KM KA :=
    idtac;
    lazymatch type of SI with sinv _ ?st ?lf ?cf =>
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (A _ fin MD T M0 R' l' Mx st lf cf CX0 Hh Hfin eq_refl SI); [regs_tac | exact KM | exact KA] end end.
  decompose [or] CASES; clear CASES; match goal with Hc : mode = _ |- _ => rewrite Hc in *; clear Hc; try clear mode end.
  - zuntil Rfd (arm A_HEAD CX0 SI KM KA).
  - zuntil Rfd (arm A_DICTID CX0 SI KM KA).
  - zuntil Rfd (arm A_DICT CX0 SI KM KA).
  - zuntil Rfd (arm A_TYPE CX0 SI KM KA).
  - zuntil Rfd (arm A_TYPEDO CX0 SI KM KA).
  - zuntil Rfd (arm A_STORED CX0 SI KM KA).
  - zuntil Rfd (arm A_COPY_ CX0 SI KM KA).
  - zuntil Rfd (arm A_COPY CX0 SI KM KA).
  - zuntil Rfd (arm A_TABLE CX0 SI KM KA).
  - zuntil Rfd (arm A_LENLENS CX0 SI KM KA).
  - zuntil Rfd (arm A_CODELENS CX0 SI KM KA).
  - zuntil Rfd (arm A_LEN_ CX0 SI KM KA).
  - zuntil Rfd (arm A_LEN CX0 SI KM KA).
  - zuntil Rfd (arm A_LENEXT CX0 SI KM KA).
  - zuntil Rfd (arm A_DIST CX0 SI KM KA).
  - zuntil Rfd (arm A_DISTEXT CX0 SI KM KA).
  - zuntil Rfd (arm A_MATCH CX0 SI KM KA).
  - zuntil Rfd (arm A_LIT CX0 SI KM KA).
  - zuntil Rfd (idtac; lazymatch type of SI with sinv _ ?st ?lf ?cf =>
          lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
            eapply (A_CHECK _ fin MD T M0 R' l' Mx st lf cf CX0 OBLOW Hh Hfin eq_refl SI); [regs_tac | exact KM | exact KA] end end).
  - zuntil Rfd (arm A_LENGTH CX0 SI KM KA).
  - (* the source's mode DONE: the leave with the source's return code 1 *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KL R' Mx (IST DONE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) 1 lf cf SI) end);
      [regs_tac | | | | | | ]; pose proof KM as KM'; open_kmem KM'; try assumption.
  - (* the source's mode BAD: the leave with the source's return code -3 *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KL R' Mx (IST BAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) (-3) lf cf SI) end);
      [regs_tac | | | | | | ]; pose proof KM as KM'; open_kmem KM'; try assumption.
  - (* the source's mode MEM: the return with the source's return code -4 *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KR R' Mx (-4) MEM) end);
      [ cbv; discriminate | regs_tac | | | unfold reach; cbv [HEAD DICTID MEM]; lia_std | ];
      pose proof KM as KM'; open_kmem KM'; try assumption;
      match goal with H : st_at _ _ _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma loop_nat : forall k : nat, KD0 cx fin MD T M0 (Z.of_nat k).
Proof.
  induction k as [|k IH].
  - intros R M st lf cf SI MB. exfalso. pose proof (meas_nonneg _ _ _ _ SI). cbn [Z.of_nat] in MB. lia.
  - rewrite Nat2Z.inj_succ. apply kd0_step. exact IH.
Qed.

Theorem loop_s : forall B, KD0 cx fin MD T M0 B.
Proof. intros B. apply (kd0_mono (Z.of_nat (Z.to_nat B))); [lia | apply loop_nat]. Qed.

Theorem kall_s : forall B, KALL cx fin MD T M0 B.
Proof. intros B. apply kall_of_kd0; [apply loop_s | exact KL | exact KR]. Qed.
End Step.

End Loop.
End S_Loop.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import SBase. Import S_Loop.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

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
Lemma mode_load_live : forall m, codes_liveP (mode_load m) -> codes_liveP m.
Proof. intros m. unfold codes_liveP, mode_load. cbv [TYPE TYPEDO LEN_ LIT]. destruct (Z.eqb_spec m 16191); lia_std. Qed.

Lemma sinv_load : forall cx st lf cf,
  ctx_ok ROMHI_S cx -> ainv cx st lf cf ->
  c_cin0 cx = t_cin st -> c_cout0 cx = t_cout st -> c_W0 cx = Wm cx st ->
  sinv cx (st_load cx st) lf cf.
Proof.
  intros cx st lf cf CX (R & W & Mo) H1 H2 H3.
  split; [| split; [exact W | split]].
  - pose proof (proj1 CX) as L. unfold ctx_lin in L. clear CX W Mo.
    destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
    destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
    unfold RNG, st_load in *. icx_cbn. cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL] in L.
    destr_conj R. destr_conj L. pose proof two64_eq as TW64.
    split_conj; try assumption; lia_std.
  - clear CX W Mo R. destruct cx, st. unfold PROG, Wm, st_load in *. icx_cbn. split; [lia_std | split; [lia_std | left; lia_std]].
  - clear CX W R H1 H2 H3. dand Mo as (Mr & Mf & Mll & Mcl & Mlive & Mle & Mdi & Mde & Mma & Mco).
    destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
    destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
    unfold MODE, st_load in *. icx_cbn. split_conj.
    + exact (proj1 (mode_load_reach mode Mr)).
    + intros Hf. destruct (Mf Hf) as [Hm Hc]. split; [|exact Hc].
      assert (Hm' : mode <> TYPE) by (clear - Hm; cbv [TYPE HEAD BAD] in *; lia_std).
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

Definition e_mem {RCa1 : RunCtx}  (cx : ictx) (fin : Z -> Z) (st : ist) (lf cf : Z -> Z) (M : mem) : Prop :=
  rom_ok M /\
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -1024) 1232 /\ mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx) STATE_SIZE /\
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (c_ob cx) (c_osz cx) /\ mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (c_w cx) (wsz cx) /\
  i_cst (run_segments R_segs rc_inp rc_sp rc_mb) cx M /\ i_hooks cx M /\ mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_q cx) (c_n cx) fin /\
  st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M /\ strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf.
Ltac open_emem H := dand H as (ROM & Wstk & Wp & Wob & Ww & CST & HK & Hin & SAT & STRM & Hlens & Hcodes).

Theorem entry_s {RCa1 : RunCtx}  : forall cx fin MD T Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ainv cx st lf cf -> c_cin0 cx = t_cin st -> c_cout0 cx = t_cout st -> c_W0 cx = Wm cx st ->
  s_regs_entry cx Rb l -> e_mem cx fin st lf cf M ->
  KD0 cx fin MD T M (meas cx (st_load cx st) + 1) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_INFLATE (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T Rb l M st lf cf CX Hh Hfin AI Hc1 Hc2 Hc3 RE EM K.
  pose proof (sinv_load cx st lf cf CX AI Hc1 Hc2 Hc3) as SI.
  open_emem EM. destruct SAT as [Hmode SREST].
  pose proof AI as AI'. dand AI' as (RNG_ & WIN_ & MODE_).
  pose proof (proj1 MODE_) as Hreach. pose proof CX as CX0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst cin0 cout0.
  pose proof (proj2 (mode_load_reach mode Hreach)) as Hmlb. pose proof (reach_bounds _ Hreach) as Hmb.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  unfold s_regs_entry in RE. icx_cbn. destr_conj RE.
  zkeysb. unfold L_INFLATE, L_DISP0 in *. cbv [A_ZCALLOC A_ZCFREE] in *. pose proof two64_eq as TW64.
  fp_frame_init (fp_loop (ICX u p q n ob osz w cin cout W0 K0 zc)) M.
  (* the facts of the hooks, of the constants and of the stream that the entry reads: opened ONCE, before the
     run (the hand text opens each beside the load that reads it; the base text's store step carries every
     open fact across each store, or drops it where the store writes it) *)
  pose proof HK as HK'; destruct HK' as [C72 C80].
  pose proof CST as CST'; unfold i_cst in CST'; icx_cbn; dand CST' as (C64 & _ & Cp0 & _).
  pose proof STRM as STRM'; unfold strm_at in STRM'; icx_cbn; dand STRM' as (S8 & S16 & S32 & S40 & S80 & S88).
  (* ONE RUN: from the function's entry to the test of the mode (the first branch that the facts in hand do
     not decide) *)
  zto_branch Rfd.
  (* the join point after the mode test. ITS LABEL AND ITS REGISTER MAP ARE THE IMAGE's LAYOUT's (a list; its
     meaning by the shared meaning function): no register and no address is named here *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (J : forall RJ Mq,
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
      (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval (ICX u p q n ob osz w cin cout W0 K0 zc)
         (Some (st_load (ICX u p q n ob osz w cin cout W0 K0 zc)
                  (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext))) 0)
      RJ [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_entry_j ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 8) (mode_load mode) ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mc Mq [(p + 8, 4)] ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ENTRY_J (zupd RJ []) Mq MD) T) end.
  { intros RJ Mq RJH. intros.
    cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_entry_j] in RJH.
    cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ENTRY_J].
    unfold st_load in RJH. icx_cbn. destr_conj RJH. zgetl_nil.
    zimps. zkeys.
    (* the facts opened before the first run speak of the memory before this join point: they go; the
       stream's facts are opened again from the stream's relation once it is carried to this memory, and the
       relation itself goes before the run (the run writes the stream) *)
    try clear C72; try clear C80; try clear C64; try clear Cp0;
    try clear S8; try clear S16; try clear S32; try clear S40; try clear S80; try clear S88.
    match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) _ Mq _ |- _ => clear Hmode; zreattachL HP end.
    pose proof STRM as STRM'; unfold strm_at in STRM'; icx_cbn; dand STRM' as (T8 & T16 & T32 & T40 & T80 & T88).
    clear STRM.
    (* ONE RUN: from the join point to the first dispatch *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (K R' Mx (st_load (ICX u p q n ob osz w cin cout W0 K0 zc)
                 (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) lf cf SI) end).
    - lia.
    - unfold s_regs_d0, s_fix, s_vars, st_load; icx_cbn; cbv [JTAB_ADDR]; zkeys; split_conj; zreg.
    - unfold k_mem, st_load; icx_cbn. split_conj.
      + unfold s_std; icx_cbn; split_conj; try assumption.
        unfold i_frame; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; assumption.
      + unfold st_at; icx_cbn. split; [assumption | exact SREST].
      + unfold s_ret; icx_cbn. assumption.
      + unfold s_out; icx_cbn; first [ exact I | assumption ].
      + exact Hlens.
      + exact Hcodes.
      + exact HAG. }
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
    pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) Mc [(p + 8, 4)] ltac:(ranges_ok_tac)) as HST2;
    assert (HAG2 : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mc X [(p + 8, 4)]) Mc) by (apply mpostL_refl) end.
  destruct (Z.eq_dec mode 16191) as [Em | Em].
  - (* the mode is the source's TYPE: ONE RUN to the join point *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => apply (J R' Mx) end);
      [ cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_entry_j];
        unfold st_load; icx_cbn; split_conj | | ];
      first [ zreg | assumption | exact HAG2
            | unfold mode_load; cbv [TYPE TYPEDO]; rewrite Em; cbn [Z.eqb Pos.eqb]; first [zreg | assumption] ].
  - (* any other mode: ONE RUN to the join point *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => apply (J R' Mx) end);
      [ cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_entry_j];
        unfold st_load; icx_cbn; split_conj | | ];
      first [ zreg | assumption | exact HAG2
            | unfold mode_load; cbv [TYPE TYPEDO]; destruct (Z.eqb_spec mode 16191); [lia_std | first [zreg | assumption]] ].
Qed.
