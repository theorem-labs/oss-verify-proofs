(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* THE CHECK TEXT IN THE RUN FORM. EVERY STRETCH OF STEP LINES IS ONE RUN OF THE STURDY DRIVER (NO HINT RUN);
   no step count and no branch direction is written. The machine facts that three statements held are lists
   of the LAYOUT TEXT; the text's five own labels are layout fields. ONE hand statement that another text
   names stands in the bridge text, proved there from its list-form statement of this text. The hand text's value replacements are
   TWO VALUE EQUATIONS (one lemma of this text, one of the kit) stated BEFORE the runs. ONE branch is split on
   its own condition by the driver's split form. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SBase S_Type.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZGo11 SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.

Module S_HeadA.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Type.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* THE TEXT's OWN LABELS ARE FIELDS OF THE LAYOUT TEXT; here they have their short names only *)
Local Notation L_DICT_CALL := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_DICT_CALL (only parsing).
Local Notation L_ADLER_RET1 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ADLER_RET1 (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation qval := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval (only parsing).

Ltac mode_consts :=
  cbv [reach codes_liveP HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.
Ltac mode_solve Mf tac :=
  split_conj;
  first [ right; lia_std
        | left; lia_std
        | intros X; exfalso; lia_std
        | intros Hf; exfalso; destruct (Mf Hf) as [Hx _]; lia_std
        | tac ].

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma hold_u64 : forall h b, 0 <= b <= 40 -> 0 <= h < 2 ^ b -> 0 <= h < 18446744073709551616.
Proof.
  intros h b Hb Hh. assert (2 ^ b <= 2 ^ 40) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 40) with 1099511627776 in *. lia.
Qed.
Lemma shiftr_lt_pow2 : forall h b k, 0 <= k <= b -> 0 <= h < 2 ^ b -> 0 <= Z.shiftr h k < 2 ^ (b - k).
Proof.
  intros h b k Hk Hh. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (b - k)) with b by lia. lia.
Qed.
Lemma pullbyte_bound : forall h b c, 0 <= b -> 0 <= h < 2 ^ b -> 0 <= c < 256 ->
  0 <= h + c * 2 ^ b < 2 ^ (b + 8).
Proof.
  intros h b c Hb Hh Hc. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  assert (0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.
Lemma smod64_nz : forall x, -9223372036854775808 <= x < 9223372036854775808 -> x <> 0 ->
  x mod 18446744073709551616 <> 0.
Proof. intros x Hx Hnz. lia. Qed.
Lemma swrap32_big : forall x, 2147483648 <= x < 4294967296 -> bv_swrap 32 x = x - 4294967296.
Proof.
  intros x Hx. rewrite <- (swrap32_mod32 x).
  replace (x mod 4294967296) with ((x - 4294967296) mod 4294967296) by lia.
  rewrite swrap32_mod32. apply swrap32_small. lia.
Qed.
Lemma swrap32_nz : forall x, 0 <= x < 4294967296 -> x <> 0 -> bv_swrap 32 x mod 18446744073709551616 <> 0.
Proof.
  intros x Hx Hnz. destruct (Z_lt_dec x 2147483648).
  - rewrite swrap32_small by lia. lia.
  - rewrite swrap32_big by lia. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition hd_st (st : ist) (m flags cin hold bits : Z) : ist :=
  IST m (t_last st) flags cin (t_cout st) hold bits (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_hd : forall cx st lf cf m flags cin hold bits,
  sinv cx st lf cf -> (t_mode st <? CHECK) = true ->
  (m = HEAD \/ m = DICTID \/ m = DICT \/ m = TYPE \/ m = TYPEDO \/ m = STORED \/ m = CHECK \/ m = LENGTH \/ m = DONE \/ m = BAD) ->
  (flags = t_flags st \/ flags = 0) -> (flags = -1 -> m = HEAD \/ m = BAD) ->
  t_cin st <= cin <= c_n cx -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> bits <= 8 * cin ->
  8 * (c_n cx - cin) + bits <= 8 * (c_n cx - t_cin st) + t_bits st ->
  sinv cx (hd_st st m flags cin hold bits) lf cf.
Proof.
  intros cx st lf cf m flags cin hold bits (RG & W & P & Mo) Hlt Hm Hfl Hfm Hc Hb Hh Hbc HW. apply Z.ltb_lt in Hlt.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags' cin' cout hold' bits' out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_cin t_bits t_flags] in *. icx_cbn.
  unfold RNG in RG. icx_cbn. destr_conj RG.
  split; [| split; [exact W | split]].
  - unfold RNG, hd_st; icx_cbn. split_conj; try assumption; try lia_std.
  - unfold PROG, hd_st, Wm in *; icx_cbn. mode_consts. lia_std.
  - pose proof (proj1 (proj2 Mo)) as Mf. clear W P. unfold MODE in Mo. unfold MODE, hd_st; icx_cbn.
    assert (Hco : flags' = -1 -> cout = 0) by (intros E; exact (proj2 (Mf E))). clear Mo Mf. mode_consts.
    destruct Hm as [Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|Hm]]]]]]]]]; subst m;
    (split_conj;
      first [ right; lia_std | left; lia_std | intros X; exfalso; lia_std
            | intros X; split; [ destruct (Hfm X); [left | right]; lia_std | apply Hco; lia_std ] ]).
Qed.

Lemma meas_hd : forall cx st m flags cin hold bits,
  8 * (c_n cx - cin) + bits < 8 * (c_n cx - t_cin st) + t_bits st \/
  (8 * (c_n cx - cin) + bits <= 8 * (c_n cx - t_cin st) + t_bits st /\ rank m < rank (t_mode st)) ->
  meas cx (hd_st st m flags cin hold bits) < meas cx st.
Proof.
  intros cx st m flags cin hold bits H.
  destruct H as [H | [H1 H2]].
  - apply meas_dec_W. unfold Wm, hd_st in *. destruct cx, st; icx_cbn. cbn in *. lia_std.
  - apply meas_dec_rank; [| unfold hd_st; cbn; exact H2]. unfold Wm, hd_st in *. destruct cx, st; icx_cbn. cbn in *. lia_std.
Qed.

Lemma flags_not_m1 : forall cx st lf cf, sinv cx st lf cf -> t_mode st <> HEAD -> t_mode st <> BAD -> t_flags st <> -1.
Proof. intros cx st lf cf (_ & _ & _ & Mo) H1 H2 Hf. destruct (proj1 (proj2 Mo) Hf) as [[E|E] _]; congruence. Qed.


Section WITH_ADLER_NULL.
Context {RCa1 : RunCtx}.
Hypothesis ADLN : adler32_null_spec_s.

(* THE OPENER OF THIS PART's ONE LIST (it only unfolds, splits and names) *)
Local Ltac open_dict_list :=
  repeat match goal with
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_dict] in H;
             icx_cbn; destr_conj H
         end.

(* THE LIST FORM of the hand statement that the bridge text holds: the place's machine facts are the layout's list *)
Lemma dict_body_l : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DICT -> sinv cx st lf cf ->
  rholds (qval cx (Some st) 0) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_dict ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DICT (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RH KM K.
  pose proof CX as CX0. pose proof SI as SI0.
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. unfold s_out in SOUT.
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags t_cin t_cout t_hold t_bits t_out] in *. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_. pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  open_dict_list.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  destruct (mem_wr_u32_exists_R M (p + 24) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (hd & Hhd & Rhd).
  (* the frame's slots are opened ALL *)
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn. destr_conj FRM'.
  zkeysb. unfold L_DICT, L_DICT_CALL, L_ADLER_RET1, L_NEED_DICT, L_RET, L_TYPE in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  (* ONE RUN to the test of the value just read *)
  zto_branch Rfd.
  destruct (Z.eq_dec hd 0) as [Hd0 | Hd0].
  -
    subst hd.
    destruct (mem_wr_u64_exists_R M (u + 16) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (ti & Hti & Rti).
    (* ONE RUN to the return place *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => eapply (KRT R' Mx 2 DICT) end).
    + cbv. discriminate.
    + unfold s_regs_ret; icx_cbn; zkeys; split_conj; zreg.
    + close_std.
    + exact Hmode.
    + cbv [reach DICT DICTID MEM HEAD]. right; lia.
    + exact HAG.
  -
    pose proof (swrap32_nz hd ltac:(lia) Hd0) as Hnz. pose proof (smod64_nz hd ltac:(lia) Hd0) as Hnz'.
    (* ONE RUN to the callee's call *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RR ?lc') ?Mx _) _ =>
      eapply (ADLN RR lc' Mx MD T _ Hh) end); [zreg | zreg | zreg | reflexivity |].
    (* the callee's continuation: its premises are taken in without a count *)
    intros R2. intros.
    zimps. zkeys.
    pose proof (sinv_hd _ _ lf cf TYPE flags cin hold bits SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(cbn; intros E; exfalso; exact (Hfl E))
                  ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST DICT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  TYPE flags cin hold bits ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MB1.
    (* ONE RUN to the next arm's entry *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (arm_TYPE_s (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                (hd_st (IST DICT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) TYPE flags cin hold bits)
                lf cf CX0 Hh Hfin eq_refl SI1) end).
    + unfold s_regs_arm, s_fix, s_vars, hd_st; icx_cbn; zkeys; split_conj; try zreg; zkept.
    + unfold k_mem, hd_st; icx_cbn; split_conj;
        [ close_std | split; [assumption | exact SREST] | exact SRET | unfold s_out; icx_cbn; assumption | exact Hlens | exact Hcodes | exact HAG ].
    + eapply KALL_mono; [| unfold KALL; split_conj; eassumption]. lia.
Qed.

(* the part's closing theorem: the arm's machine premise is opened into its facts and the layout's list is
   closed from them *)
Theorem arm_DICT_s : arm_stmt L_DICT DICT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  unfold s_regs_arm, s_fix, s_vars in RE. destr_conj RE.
  eapply (dict_body_l cx fin MD T M0 Rb l M st lf cf); try eassumption.
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_dict].
  split_conj; assumption.
Qed.

End WITH_ADLER_NULL.
End S_HeadA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import SBase S_Type. Import S_HeadA.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* the text's own labels and the list form's meaning words, by their short names *)
Local Notation L_CHECK_LOOP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CHECK_LOOP (only parsing).
Local Notation L_CHECK_BODY := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CHECK_BODY (only parsing).
Local Notation L_CHECK_CMP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CHECK_CMP (only parsing).
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation rkeeps := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps (only parsing).
Local Notation qval := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval (only parsing).

Ltac mode_consts :=
  cbv [reach codes_liveP HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.

(* a footprint list of this arm; its frame part is handed in where the list is used: two values (a distance
   and a width) and the ranges of a frame list of the layout; none is written in this text *)
Definition fp_check (u p da wa : Z) (sl : list (Z * Z)) : list (Z * Z) :=
  [(p + 8, 4); (p + 40, 16); (u + da, wa)] ++ sl ++ [(u + 40, 16); (u + 96, 8)].

Definition ck_st (st : ist) (m cin hold bits out : Z) : ist :=
  IST m (t_last st) (t_flags st) cin (t_cout st) hold bits out (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

(* THE LAYOUT's FRAME LIST OF THE OUTPUT COUNT, read at a memory (the quantities text's meaning word): its
   opener for a fact in hand, and its closing word for a goal: the opened goal is a fact in hand, or it is
   the list's empty meaning *)
Ltac open_slot H :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_out] in H.
Ltac slot_fact :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_out];
  unfold ck_st; icx_cbn; first [ assumption | exact I ].

Lemma sinv_ck : forall cx st lf cf m cin hold bits out,
  sinv cx st lf cf -> t_flags st = 0 ->
  (m = CHECK \/ m = LENGTH \/ m = DONE \/ m = BAD) ->
  t_cin st <= cin <= c_n cx -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> bits <= 8 * cin ->
  8 * (c_n cx - cin) + bits <= 8 * (c_n cx - t_cin st) + t_bits st ->
  (out = t_out st /\ (CHECK < t_mode st -> CHECK < m)) \/ (out = c_osz cx - t_cout st /\ CHECK < m) ->
  sinv cx (ck_st st m cin hold bits out) lf cf.
Proof.
  intros cx st lf cf m cin hold bits out (RG & W & P & Mo) Hf0 Hm Hc Hb Hh Hbc HW Hout.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin' cout hold' bits' out' ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_cin t_bits t_flags t_out t_cout] in *. icx_cbn. subst flags.
  unfold RNG in RG. icx_cbn. destr_conj RG.
  split; [| split; [exact W | split]].
  - unfold RNG, ck_st; icx_cbn. split_conj; try assumption; try lia_std.
  - unfold PROG, ck_st, Wm in *; icx_cbn. mode_consts. lia_std.
  - clear W P. unfold MODE in Mo. unfold MODE, ck_st; icx_cbn. clear Mo. mode_consts.
    destruct Hm as [Hm|[Hm|[Hm|Hm]]]; subst m;
    (split_conj; first [ right; lia_std | left; lia_std | intros X; exfalso; lia_std ]).
Qed.

Lemma meas_ck : forall cx st m cin hold bits out,
  8 * (c_n cx - cin) + bits < 8 * (c_n cx - t_cin st) + t_bits st \/
  (8 * (c_n cx - cin) + bits <= 8 * (c_n cx - t_cin st) + t_bits st /\ rank m < rank (t_mode st)) ->
  meas cx (ck_st st m cin hold bits out) < meas cx st.
Proof.
  intros cx st m cin hold bits out H.
  destruct H as [H | [H1 H2]].
  - apply meas_dec_W. unfold Wm, ck_st in *. destruct cx, st; icx_cbn. cbn in *. lia_std.
  - apply meas_dec_rank; [| unfold ck_st; cbn; exact H2]. unfold Wm, ck_st in *. destruct cx, st; icx_cbn. cbn in *. lia_std.
Qed.

(* OPENERS OF THE LIST FORM (they only unfold, split and name): every list-form hypothesis: the meaning over
   the layout's lists is unfolded, the conjunction split and its parts named; the same for a goal *)
Local Ltac open_check_lists :=
  repeat match goal with
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd ck_st
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_body OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_cmp
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_loop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_lv
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_dn] in H;
             icx_cbn; destr_conj H
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_check_loop] in H; destr_conj H
         end.
Local Ltac split_check_lists :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd ck_st
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_body OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_cmp
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_loop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_lv
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_dn OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_check_loop];
  icx_cbn; split_conj.

(* THE VALUE EQUATION OF THIS TEXT (the form the machine leaves = the value the hand text names). It is
   stated before the run that needs it; the other value equation this text states is the kit's own lemma. *)
Lemma check_pull_eq : forall c j, 0 <= j < 64 -> Z.shiftl c (j mod 64) = c * 2 ^ j.
Proof. intros c j Hj. rewrite (Z.mod_small j) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Section WITH_ADLER.
Context {RCa1 : RunCtx}.
Hypothesis ADLER : adler32_spec_s.

Lemma check_main : forall cx fin MD T M0 Rb l M st lf cf (cin1 hold1 bits1 : Z),
  ctx_ok ROMHI_S cx -> c_ob cx + c_osz cx <= c_u cx - FRA -> m_halted MD = None ->
  (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = CHECK -> sinv cx st lf cf ->
  rholds (qval cx (Some (ck_st st (t_mode st) cin1 hold1 bits1 (t_out st))) 0) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_body ->
  t_cin st <= cin1 <= c_n cx -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
  8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CHECK_BODY (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf cin1 hold1 bits1 CX OBLOW Hh Hfin Hm SI RH Hc1 Hb1 Hh1 Hbc1 HW1 KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof KM as KM0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. unfold FRA in OBLOW. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags t_cin t_cout t_hold t_bits t_out] in *. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  assert (Hf0 : flags = 0) by lia. subst flags. clear Hfl.
  open_check_lists.
  pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh64.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & H16 & _).
  pose proof SREST as SR'. unfold st_rest in SR'. icx_cbn. dand SR' as (_ & H24 & _).
  (* the frame's facts: taken whole here, opened ALL after the asserted statement below *)
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  pose proof SOUT as Q80. unfold s_out in Q80. icx_cbn.
  destruct (mem_wr_u64_exists_R M (u + 40) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (to & Hto & Rto).
  destruct (mem_wr_u64_exists_R M (p + 48) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (tt & Htt & Rtt).
  destruct (mem_wr_u64_exists_R M (p + 40) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (ck & Hck & Rck).
  clear Ww FRM CST HK Hmode SREST SRET SOUT Hlens Hcodes Hin.
  zkeysb. unfold L_CHECK_BODY, L_CHECK_CMP, L_DISP, L_LEAVE in *. cbv [A_ADLER32] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  (* the footprint's handed-in frame part: two values from the layout's named sizes and the ranges of the
     layout's frame list of the output count *)
  let DA := eval vm_compute in (- OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_INF - OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_AD) in
  let WA := eval vm_compute in OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_AD in
  let SL := eval cbv [map OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_out] in
              (map (fun s => (u + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off s,
                              match OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width s with OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.W8 => 8 | OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.W4 => 4 end))
                   OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_out) in
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_check u p DA WA SL) ltac:(unfold fp_check; cbn [app]; ranges_ok_tac)) as HSTc;
  assert (HAGc : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (fp_check u p DA WA SL)) M) by (apply mpostL_refl).
  unfold fp_check in HSTc, HAGc. cbn [app] in HSTc, HAGc.
  (* the footprint is bound from the fact in hand; the output count's place is the layout's frame list *)
  lazymatch type of HAGc with framed (fun X => mpostL _ _ X ?FPC) _ =>
  assert (REATT : forall Mq m' c1 h1 b1 o1,
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 8) m' ->
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds (run_segments R_segs rc_inp rc_sp rc_mb)
      (qval (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (Some (ck_st (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                         m' c1 h1 b1 o1)) 0)
      Mq u OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_out ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M Mq FPC ->
    k_mem (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
          (ck_st (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                 m' c1 h1 b1 o1) lf cf Mq) end.
  { intros Mq m' c1 h1 b1 o1 Hm8 Ho1 HPq. open_slot Ho1.
    clear HST HAG Wstk Wp Wob ROM HSTc HAGc H16 H24 FRM' Q80 Hto Htt Hck.
    open_kmem KM0. open_std STD. destruct SAT as [Hmode SREST]. clear Hmode.
    unfold st_rest in SREST. icx_cbn.
    dand SREST as (H12 & H24 & H64 & H68 & H92 & H96 & H100 & H104 & H112 & H120 & H124 & H128 & H132 & H136 & H140 & H144).
    fp_frame_from HP0.
    cbv [N_LENS N_CODES] in Hlens, Hcodes.
    (* the slot's old fact goes before the facts are carried over (the footprint holds the slot; the new
       fact is a premise of this statement) *)
    clear SOUT.
    zreattachL HPq.
    unfold k_mem; split_conj;
      [ close_std
      | unfold st_at, st_rest, ck_st; icx_cbn; split_conj; assumption
      | unfold s_ret, ck_st in *; icx_cbn; assumption | unfold s_out, ck_st in *; icx_cbn; exact Ho1
      | assumption | assumption | exact HAG ]. }
  (* the frame's slots are opened ALL *)
  destr_conj FRM'.
  (* the value equation of this stretch's value replacements (the kit's own lemma): stated before the run *)
  pose proof (zext32_shift (out - (osz - cout)) ltac:(lia)) as Hzx.
  (* ONE RUN to the test of the output count *)
  zto_branch Rfd.
  (* the place where the two ways meet: ITS LABEL AND ITS MAP ARE THE LAYOUT's; its memory premises are bound
     from the facts in hand *)
  lazymatch type of HAG with framed (fun X => mpostL _ _ X ?FPL) _ =>
  lazymatch type of HAGc with framed (fun X => mpostL _ _ X ?FPC) _ =>
  lazymatch type of Wstk with mem_wr _ _ ?SA ?SN =>
  lazymatch type of Wp with mem_wr _ _ ?PA ?PN =>
  assert (CMP : forall RC Mq c,
    rholds (qval (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
              (Some (ck_st (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                           CHECK cin1 hold1 bits1 out)) 0)
      RC [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_cmp ->
    mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) Mq SA SN -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) Mq PA PN ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 28) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 40) c ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X FPL) Mq ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X FPC) Mq ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CHECK_CMP (zupd RC []) Mq MD) T) end end end end.
  { intros RC Mq c RJH. clear HAG HAGc Wstk Wp Wob ROM Hck H24 H16 Q80.
    intros Wstk Wp H24 Hck HAG HAGc.
    open_check_lists. zgetl_nil.
    unfold L_CHECK_CMP. zkeys.
    (* the model facts of the two ways out of this place: stated before the runs *)
    pose proof (sinv_ck _ _ lf cf BAD cin1 hold1 bits1 (osz - cout) SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto]))
                  ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(right; split; [reflexivity | cbv; reflexivity])) as SIB.
    pose proof (meas_ck (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  BAD cin1 hold1 bits1 (osz - cout) ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MBB.
    pose proof (sinv_ck _ _ lf cf DONE cin1 0 0 (osz - cout) SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto]))
                  ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(right; split; [reflexivity | cbv; reflexivity])) as SID.
    (* ONE RUN to the test of the check value *)
    zto_branch Rfd.
    (* that test is split by the driver's split form (it writes no way); then ONE RUN on each way, to
       whichever of the two join points that way reaches *)
    zbranch_split Rfd;
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      first [ eapply (KD R' Mx (ck_st (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                                 BAD cin1 hold1 bits1 (osz - cout)) lf cf SIB MBB)
            | eapply (KL R' Mx (ck_st (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                                 DONE cin1 0 0 (osz - cout)) 1 lf cf SID) ] end);
    first
      [ solve [ unfold s_regs_disp, s_fix, s_vars, ck_st; icx_cbn; zkeys; split_conj; zreg ]
      | solve [ unfold s_regs_leave, ck_st; icx_cbn; zkeys; split_conj; zreg ]
      | solve [ apply REATT; [assumption | slot_fact | exact HAGc] ]
      | (lazymatch type of HAGc with framed _ ?Mx =>
           destruct (REATT Mx DONE cin1 0 0 (osz - cout) ltac:(assumption) ltac:(slot_fact) HAGc) as (STD' & SAT' & _ & SOUT' & Hl' & Hc' & HP') end;
         first [ exact STD' | exact SAT' | exact SOUT' | exact Hl' | exact Hc' | exact HP' ]) ]. }
  destruct (Z.eq_dec out (osz - cout)) as [Ecout | Ecout].
  -
    (* ONE RUN to the place where the two ways meet *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RC ?Mx _) _ => apply (CMP RC Mx ck) end);
      [ split_check_lists | .. ]; first [zreg | assumption].
  -
    (* the facts of the output buffer that the callee's call reads: stated before the run *)
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      destruct (mem_wr_arr_exists_R Mx ob osz Wob ltac:(lia) ltac:(lia) ltac:(lia)) as (fo & HOB & Hfo) end.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      pose proof (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 1 Mx ob osz fo (cout - (out - (osz - cout))) (out - (osz - cout)) HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc end.
    replace (ob + 1 * (cout - (out - (osz - cout)))) with (ob + cout - (out - (osz - cout))) in Hsrc by lia.
    clear HOB.
    (* ONE RUN to the callee's call; two of the callee's values are found by its own premises *)
    zuntil Rfd
      (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?lc) ?Mx _) _ =>
        eapply (ADLER R' lc Mx MD T ck (ob + cout - (out - (osz - cout))) (out - (osz - cout)) (out - (osz - cout)) _ _
                  (fun j => fo (cout - (out - (osz - cout)) + j)) Hh) end);
      try zreg.
    all: lazymatch goal with
         | |- forall M' : mem, _ => idtac
         | |- _ => cbv [FR_AD]; first [ reflexivity | exact Hsrc | assumption | rewrite Z.mod_small by lia; reflexivity
                         | eapply mem_wr_sub; [exact Wstk | lia | lia] | intros i Hi; apply Hfo; lia | lia ]
         end.
    intros M' R' HP. intros. zimps. zkeys.
    clear Hsrc.
    apply mpost_mpostL1 in HP. cbv [FR_AD] in HP. zreattachL HP.
    (* ONE RUN to the place where the two ways meet *)
    zuntil Rfd (idtac; lazymatch goal with Hnew : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (p + 40) ?c' |- realizes _ (zcfg _ _ ?RC ?Mx _) _ =>
      apply (CMP RC Mx c') end);
      [ split_check_lists | .. ]; first [zreg | assumption].
Qed.

(* THE LOOP LEMMA, IN THE LIST FORM. `st0` is a model state; the lemma speaks of `st0` with its input count,
   hold and bit count set to the values it binds. The loop's head, its leave and its body's continuation each
   have a map in the layout; what the loop leaves alone is the layout's KEEP LIST. *)
Lemma check_loop : forall (k : nat) cx fin MD T Rb l M (st0 : ist) (cinj holdj j : Z),
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_S cx ->
  32 - 8 * Z.of_nat k <= j < 40 - 8 * Z.of_nat k -> (1 <= k <= 4)%nat -> 0 <= j ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  rholds (qval cx (Some (ck_st st0 (t_mode st0) cinj holdj j (t_out st0))) 0) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_loop ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_q cx) (c_n cx) fin ->
  (forall R' hold' j',   (* the leave: no input left *)
     rholds (qval cx (Some (ck_st st0 (t_mode st0) (c_n cx) hold' j' (t_out st0))) 0) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_lv ->
     j' = j + 8 * (c_n cx - cinj) -> 0 <= hold' < 2 ^ j' -> c_n cx - cinj < Z.of_nat k ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_check_loop ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD (zupd R' []) M MD) T) ->
  (forall R' hold' j',   (* the body: enough bits in hand *)
     rholds (qval cx (Some (ck_st st0 (t_mode st0) (cinj + Z.of_nat k) hold' j' (t_out st0))) 0) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_check_dn ->
     j' = j + 8 * Z.of_nat k -> 0 <= hold' < 2 ^ j' -> Z.of_nat k <= c_n cx - cinj ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_check_loop ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CHECK_BODY (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CHECK_LOOP (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M st0 cinj holdj j Hh Hfin CXl Hj Hk Hj0 Hc Hhj Hjc RH Hin KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S] in CXl; destr_conj CXl.
  open_check_lists.
  zkeysb. unfold L_CHECK_LOOP, L_CHECK_BODY, L_LEAVE_LD in *. pose proof two64_eq as TW64.
  assert (Hj40 : 2 ^ j <= 2 ^ 39) by (apply Z.pow_le_mono_r; lia). change (2 ^ 39) with 549755813888 in Hj40.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  -
    (* no input left: ONE RUN to the leave *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj j) end);
      [ split_check_lists | | | | split_check_lists ]; try zreg; try lia.
    all: replace (j + 8 * (n - cinj)) with j by lia; lia.
  - pose proof (Hfin cinj ltac:(lia)) as Hb0.
    pose proof (pullbyte_bound holdj j (fin cinj) ltac:(lia) Hhj Hb0) as Hpb.
    (* the value equation of the body's one value replacement: stated before the run *)
    pose proof (check_pull_eq (fin cinj) j ltac:(lia)) as Hsh.
    (* ONE RUN through the loop's body to its exit test *)
    zto_branch Rfd.
    destruct k as [|k'].
    +
      (* the last round: ONE RUN to the body's continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KDN R' (fin cinj * 2 ^ j + holdj) (j + 8)) end);
        [ split_check_lists | | | | split_check_lists ]; try zreg; try lia.
    + (* THE BACK EDGE: ONE RUN back to the loop's head, where the induction hypothesis applies *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') _ _) _ =>
        eapply (IH (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' M st0 (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) Hh Hfin) end);
        [ unfold ctx_lin; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S]; split_conj; assumption || lia
        | lia | lia | lia | icx_cbn; lia | lia | icx_cbn; lia
        | split_check_lists; zreg | exact Hin | | ].
      * (* the inner leave gives the outer leave: the same place, the model values re-said *)
        intros R' hold' j' RH' Hj' Hb' Hlt' KP'. icx_cbn. eapply (KLV R' hold' j').
        -- first [ exact RH'
                 | (open_check_lists; zgetl_nil; split_check_lists; cbv beta iota delta [zget_l alookup];
                    first [ assumption | (etransitivity; [ eassumption | lia ]) ]) ].
        -- lia.
        -- assumption.
        -- lia.
        -- first [ exact KP' | (open_check_lists; split_check_lists; zkept) ].
      * intros R' hold' j' RH' Hj' Hb' Hle' KP'. icx_cbn. eapply (KDN R' hold' j').
        -- first [ exact RH'
                 | (open_check_lists; zgetl_nil; split_check_lists; cbv beta iota delta [zget_l alookup];
                    first [ assumption | (etransitivity; [ eassumption | lia ]) ]) ].
        -- lia.
        -- assumption.
        -- lia.
        -- first [ exact KP' | (open_check_lists; split_check_lists; zkept) ].
Qed.

Lemma check_body : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> c_ob cx + c_osz cx <= c_u cx - FRA -> m_halted MD = None ->
  (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = CHECK -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CHECK (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX OBLOW Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof KM as KM0. pose proof K as KA0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof (proj1 CX) as CXl. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags] in Hm, Hfl. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  assert (Hf0 : flags = 0) by lia. subst flags. clear Hfl.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & H16 & _).
  clear ROM Wob Ww FRM CST HK Hmode SREST SRET SOUT Hlens Hcodes.
  zkeysb. unfold L_CHECK, L_CHECK_LOOP, L_CHECK_BODY, L_LEAVE_LD in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  (* ONE RUN to the test of the bit count *)
  zto_branch Rfd.
  destruct (Z_lt_dec 31 bits) as [Hb32 | Hb32].
  - (* enough bits in hand: ONE RUN to the body *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (check_main (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf cin hold bits CX0 OBLOW Hh Hfin eq_refl SI0) end);
      [ split_check_lists; zreg | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
  - (* not enough bits: ONE RUN to the loop's head *)
    assert (Hkk : exists k : nat, 32 - 8 * Z.of_nat k <= bits < 40 - 8 * Z.of_nat k /\ (1 <= k <= 4)%nat).
    { exists (Z.to_nat (4 - bits / 8)).
      rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (check_loop k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' Mx
                (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                cin hold bits Hh Hfin CXl Hk1 Hk2) end);
      [ lia | icx_cbn; lia | lia | lia | split_check_lists; zreg | exact Hin | | ].
    +
      (* the loop's leave: the leave place's continuation applies as it stands *)
      intros R' hold' j' RH'. icx_cbn. intros. open_check_lists. zgetl_nil. zimps. zkeys. unfold L_LEAVE_LD in *.
      pose proof (sinv_ck _ _ lf cf CHECK n hold' j' out SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto]))
                    ltac:(cbn; lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia)
                    ltac:(left; split; [reflexivity | intros X; exact X])) as SI1.
      clear H16. open_kmem KM0. destruct SAT as [Hmode SREST].
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KLL Rx Mx _ lf cf SI1) end.
      * unfold s_regs_leave_ld, ck_st; icx_cbn; zkeys; split_conj; try zreg; zkept.
      * exact STD.
      * unfold ck_st; split; [exact Hmode | exact SREST].
      * exact SRET.
      * exact SOUT.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      (* the loop's body continuation: the body's statement applies as it stands *)
      intros R' hold' j' RH'. icx_cbn. intros. open_check_lists. zgetl_nil. zimps. zkeys. unfold L_CHECK_BODY in *.
      eapply (check_main (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' [] M
                (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf (cin + Z.of_nat k) hold' j' CX0 OBLOW Hh Hfin eq_refl SI0);
        [ split_check_lists; (first [zreg | zkeys; cbv [zget_l alookup]; first [zkept | lia]])
        | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
Qed.

Theorem arm_CHECK_s : arm_stmt_ob L_CHECK CHECK.
Proof. intros cx fin MD T M0 Rb l M st lf cf CX OBLOW Hh Hfin Hm SI RE KM K. eapply check_body; eassumption. Qed.

End WITH_ADLER.

Lemma length_body {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENGTH -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LENGTH (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. unfold s_out in SOUT.
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags] in Hm, Hfl. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  assert (Hf0 : flags = 0) by lia. subst flags. clear Hfl.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & H16 & _).
  pose proof SREST as SR'. unfold st_rest in SR'. icx_cbn. dand SR' as (_ & H24 & _).
  zkeysb. unfold L_LENGTH, L_LEAVE in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (sinv_ck _ _ lf cf DONE cin hold bits out SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto]))
                ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                ltac:(left; split; [reflexivity | intros _; cbv; reflexivity])) as SI1.
  (* ONE RUN to the leave place *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
    eapply (KL R' Mx (ck_st (IST LENGTH last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                             DONE cin hold bits out) 1 lf cf SI1) end).
  - unfold s_regs_leave, ck_st; icx_cbn; zkeys; split_conj; zreg.
  - close_std.
  - unfold ck_st; split; [assumption | exact SREST].
  - unfold s_out, ck_st; icx_cbn; assumption.
  - exact Hlens.
  - exact Hcodes.
  - exact HAG.
Qed.

Theorem arm_LENGTH_s {RCa1 : RunCtx}  : arm_stmt L_LENGTH LENGTH.
Proof. intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K. eapply length_body; eassumption. Qed.
