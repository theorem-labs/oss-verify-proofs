(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S Require SBase S_Type.

Module S_HeadA.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_Type.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Definition L_DICT_CALL : Z := 87772.
Definition L_ADLER_RET1 : Z := 87796.

End FXG.
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
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.
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
End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

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
  intros cx st lf cf m flags cin hold bits (R & W & P & Mo) Hlt Hm Hfl Hfm Hc Hb Hh Hbc HW. apply Z.ltb_lt in Hlt.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags' cin' cout hold' bits' out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_cin t_bits t_flags] in *. icx_cbn.
  unfold RNG in R. icx_cbn. destr_conj R.
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
Hypothesis ADLN : adler32_null_spec_s.

Lemma dict_body : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DICT -> sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -224 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kA0 = c_u cx -> zget_l Rb l kS4 = 16209 ->
  zget_l Rb l kS6 = c_p cx + 168 -> zget_l Rb l kS9 = JTAB_ADDR ->
  zget_l Rb l kS2 = c_n cx - t_cin st -> zget_l Rb l kS3 = c_ob cx + t_cout st -> zget_l Rb l kRA = c_osz cx - t_cout st ->
  zget_l Rb l kS7 = t_hold st -> zget_l Rb l kS8 = t_bits st ->
  zget_l Rb l kS11 = c_q cx + t_cin st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_DICT (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI LSP LGP LTP L9 LA0 L5 L21 L24 L8 L3 L2 L7 L0 L10 KM K.
  pose proof CX as CX0. pose proof SI as SI0.
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags t_cin t_cout t_hold t_bits t_out] in *. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_. pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  destruct (mem_wr_u32_exists_R M (p + 24) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (hd & Hhd & Rhd).
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q104 & Q96 & Q88 & Q72 & Q56 & _).
  zkeysb. unfold L_DICT, L_DICT_CALL, L_ADLER_RET1, L_NEED_DICT, L_RET, L_TYPE in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  tstep1 Rfd.
  destruct (Z.eq_dec hd 0) as [Hd0 | Hd0].
  -
    subst hd. zbr Rfd false.
    (* 1.4: the need-dictionary exit also adds the input consumed in this call to strm->total_in *)
    destruct (mem_wr_u64_exists_R M (u + 16) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (ti & Hti & Rti).
    zstep Rfd.                        (* j the need-dict exit *)
    tstep1 Rfd.                       (* sw ra,32(a0): avail_out *)
    tstep1 Rfd.                       (* sd s7,96(s0): hold *)
    tstep1 Rfd.                       (* sw s8,104(s0): bits *)
    tstep1 Rfd.                       (* ld a1,16(a0): total_in *)
    tstep1 Rfd.                       (* ld a2,56(sp): n - cin0 *)
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* subw; slli; srli; add *)
    tstep1 Rfd.                       (* sd s11,0(a0): next_in *)
    tstep1 Rfd.                       (* sw s2,8(a0): avail_in *)
    tstep1 Rfd.                       (* sd a1,16(a0): total_in *)
    tstep1 Rfd.                       (* sd s3,24(a0): next_out *)
    zstep Rfd.                        (* li s5,2 *)
    zstep Rfd.                        (* j L_RET *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => eapply (KRT R' Mx 2 DICT) end.
    + cbv. discriminate.
    + unfold s_regs_ret; icx_cbn; zkeys; split_conj; zreg.
    + close_std.
    + exact Hmode.
    + cbv [reach DICT DICTID MEM HEAD]. right; lia.
    + exact HAG.
  -
    pose proof (swrap32_nz hd ltac:(lia) Hd0) as Hnz. pose proof (smod64_nz hd ltac:(lia) Hd0) as Hnz'.
    zbr Rfd true.
    zstep Rfd. zstep Rfd. zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R ?lc') ?Mx _) _ =>
      eapply (ADLN R lc' Mx MD T _ Hh) end; [zreg | zreg | zreg | reflexivity |].
    intros R2 E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
    zimps. zkeys.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_hd _ _ lf cf TYPE flags cin hold bits SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(cbn; intros E; exfalso; exact (Hfl E))
                  ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST DICT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  TYPE flags cin hold bits ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (arm_TYPE_s (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                (hd_st (IST DICT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) TYPE flags cin hold bits)
                lf cf CX0 Hh Hfin eq_refl SI1) end.
    + unfold s_regs_arm, s_fix, s_vars, hd_st; icx_cbn; zkeys; split_conj; try zreg; zkept.
    + unfold k_mem, hd_st; icx_cbn; split_conj;
        [ close_std | split; [assumption | exact SREST] | exact SRET | exact SOUT | exact Hlens | exact Hcodes | exact HAG ].
    + eapply KALL_mono; [| unfold KALL; split_conj; eassumption]. lia.
Qed.

Theorem arm_DICT_s : arm_stmt L_DICT DICT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  unfold s_regs_arm, s_fix, s_vars in RE. destr_conj RE. eapply dict_body; eassumption.
Qed.

End WITH_ADLER_NULL.
End FXG.
End S_HeadA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S Require Import SBase S_Type. Import S_HeadA.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Definition L_CHECK_LOOP : Z := 87596.
Definition L_CHECK_BODY : Z := 89596.
Definition L_CHECK_CMP : Z := 90676.

End FXG.
Ltac mode_consts :=
  cbv [reach codes_liveP HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac zbr_hyp_with bv F E D :=
  eapply (zu_branch_b bv); [zexact F | zexact E | zexact D | zhalted | znorm; first [assumption | zcond_tac] | ];
  zcbv_iota; znorm.
Tactic Notation "zbrH" tactic0(fd) constr(bv) :=
  let pc := zpc in fd pc ltac:(fun F E D => zbr_hyp_with bv F E D).
Ltac zgen :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => let x' := fresh "gv" in set (x' := e); clearbody x'
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Definition fp_check (u p : Z) : list (Z * Z) :=
  [(p + 8, 4); (p + 40, 16); (u + -256, 32); (u + -144, 8); (u + 40, 16); (u + 96, 8)].

Definition ck_st (st : ist) (m cin hold bits out : Z) : ist :=
  IST m (t_last st) (t_flags st) cin (t_cout st) hold bits out (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_ck : forall cx st lf cf m cin hold bits out,
  sinv cx st lf cf -> t_flags st = 0 ->
  (m = CHECK \/ m = LENGTH \/ m = DONE \/ m = BAD) ->
  t_cin st <= cin <= c_n cx -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> bits <= 8 * cin ->
  8 * (c_n cx - cin) + bits <= 8 * (c_n cx - t_cin st) + t_bits st ->
  (out = t_out st /\ (CHECK < t_mode st -> CHECK < m)) \/ (out = c_osz cx - t_cout st /\ CHECK < m) ->
  sinv cx (ck_st st m cin hold bits out) lf cf.
Proof.
  intros cx st lf cf m cin hold bits out (R & W & P & Mo) Hf0 Hm Hc Hb Hh Hbc HW Hout.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin' cout hold' bits' out' ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_cin t_bits t_flags t_out t_cout] in *. icx_cbn. subst flags.
  unfold RNG in R. icx_cbn. destr_conj R.
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

Section WITH_ADLER.
Hypothesis ADLER : adler32_spec_s.

Lemma check_main : forall cx fin MD T M0 Rb l M st lf cf (cin1 hold1 bits1 : Z),
  ctx_ok ROMHI_S cx -> c_ob cx + c_osz cx <= c_u cx - FRA -> m_halted MD = None ->
  (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = CHECK -> sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -224 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kA0 = c_u cx -> zget_l Rb l kA1 = 0 ->
  zget_l Rb l kS6 = c_p cx + 168 -> zget_l Rb l kT6 = -16180 -> zget_l Rb l kT4 = 30 -> zget_l Rb l kS9 = JTAB_ADDR ->
  zget_l Rb l kS4 = 16209 -> zget_l Rb l kA3 = 5 ->
  zget_l Rb l kS2 = c_n cx - cin1 -> zget_l Rb l kS3 = c_ob cx + t_cout st -> zget_l Rb l kRA = c_osz cx - t_cout st ->
  zget_l Rb l kS11 = c_q cx + cin1 -> zget_l Rb l kS10 = c_q cx + cin1 ->
  zget_l Rb l kS7 = hold1 -> zget_l Rb l kS8 = bits1 ->
  t_cin st <= cin1 <= c_n cx -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
  8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_CHECK_BODY (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf cin1 hold1 bits1 CX OBLOW Hh Hfin Hm SI
         LSP LGP LTP L9 LA0 LA1 LRA LT6 LT4 LT5 L5 LA3 L8 L3 L2 L10 L11 L7 L0 Hc1 Hb1 Hh1 Hbc1 HW1 KM K.
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
  pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh64.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & H16 & _).
  pose proof SREST as SR'. unfold st_rest in SR'. icx_cbn. dand SR' as (_ & H24 & _).
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q104 & Q96 & Q88 & _).
  pose proof SOUT as Q80. unfold s_out in Q80. icx_cbn.
  destruct (mem_wr_u64_exists_R M (u + 40) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (to & Hto & Rto).
  destruct (mem_wr_u64_exists_R M (p + 48) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (tt & Htt & Rtt).
  destruct (mem_wr_u64_exists_R M (p + 40) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (ck & Hck & Rck).
  clear Ww FRM CST HK Hmode SREST SRET SOUT Hlens Hcodes Hin.
  zkeysb. unfold L_CHECK_BODY, L_CHECK_CMP, L_DISP, L_LEAVE in *. cbv [A_ADLER32] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (mpostL_stable R_segs M (fp_check u p) ltac:(unfold fp_check; ranges_ok_tac)) as HSTc.
  assert (HAGc : framed (fun X => mpostL R_segs M X (fp_check u p)) M) by (apply mpostL_refl).
  unfold fp_check in HSTc, HAGc.
  assert (REATT : forall Mq m' c1 h1 b1 o1,
    mem_u32 R_segs Mq (p + 8) m' -> mem_u64 R_segs Mq (u + -144) o1 ->
    mpostL R_segs M Mq [(p + 8, 4); (p + 40, 16); (u + -256, 32); (u + -144, 8); (u + 40, 16); (u + 96, 8)] ->
    k_mem (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
          (ck_st (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                 m' c1 h1 b1 o1) lf cf Mq).
  { intros Mq m' c1 h1 b1 o1 Hm8 Ho1 HPq.
    clear HST HAG Wstk Wp Wob ROM HSTc HAGc H16 H24 Q104 Q96 Q88 Q80 Hto Htt Hck.
    open_kmem KM0. open_std STD. destruct SAT as [Hmode SREST]. clear Hmode.
    unfold st_rest in SREST. icx_cbn.
    dand SREST as (H12 & H24 & H64 & H68 & H92 & H96 & H100 & H104 & H112 & H120 & H124 & H128 & H132 & H136 & H140 & H144).
    fp_frame_from HP0.
    cbv [N_LENS N_CODES] in Hlens, Hcodes.
    zreattachL HPq.
    unfold k_mem; split_conj;
      [ close_std
      | unfold st_at, st_rest, ck_st; icx_cbn; split_conj; assumption
      | unfold s_ret, ck_st in *; icx_cbn; assumption | unfold s_out, ck_st in *; icx_cbn; exact Ho1
      | assumption | assumption | exact HAG ]. }
  tstep1 Rfd.
  tstep1 Rfd.
  zsetreg (out - (osz - cout)) ltac:(first [lia | rewrite swrap32_small by lia; lia]).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zstep Rfd. zext32.
  zstep Rfd. zgen.
  tstep1 Rfd.
  zstep Rfd. zlit.
  zstep Rfd. zgen.
  tstep1 Rfd.
  zbr Rfd false.
  try clear Hto; try clear Htt.
  lazymatch type of HAG with framed (fun X => mpostL _ _ X ?FPL) _ =>
  assert (CMP : forall RC Mq c,
    zget RC kSP = u + -224 -> zget RC kGP = K0 kGP -> zget RC kTP = K0 kTP -> zget RC kS0 = p ->
    zget RC kA0 = u -> zget RC kA1 = 0 -> zget RC kS6 = p + 168 -> zget RC kT6 = -16180 ->
    zget RC kT4 = 30 -> zget RC kS9 = 67008 -> zget RC kS4 = 16209 -> zget RC kA3 = 5 -> zget RC kA4 = 4 ->
    zget RC kS2 = n - cin1 -> zget RC kS3 = ob + cout -> zget RC kRA = osz - cout ->
    zget RC kS11 = q + cin1 -> zget RC kS10 = q + cin1 -> zget RC kS7 = hold1 -> zget RC kS8 = bits1 ->
    mem_wr R_segs Mq (u + -1024) 1232 -> mem_wr R_segs Mq p 7176 ->
    mem_u32 R_segs Mq (p + 28) 0 -> mem_u64 R_segs Mq (p + 40) c ->
    framed (fun X => mpostL R_segs M0 X FPL) Mq ->
    framed (fun X => mpostL R_segs M X [(p + 8, 4); (p + 40, 16); (u + -256, 32); (u + -144, 8); (u + 40, 16); (u + 96, 8)]) Mq ->
    realizes R_segs (zcfg R_segs L_CHECK_CMP (zupd RC []) Mq MD) T) end.
  { intros RC Mq c. clear HAG HAGc Wstk Wp Wob ROM Hck H24 H16 Q104 Q96 Q88 Q80.
    intros E3 E4 E5 E26 E11 E12 E2 E32 E30 E31 E22 E14 E15 E25 E20 E19 E27 E28 E24 E9 Wstk Wp H24 Hck HAG HAGc.
    unfold L_CHECK_CMP. zkeys.
    zbr Rfd false.
    tstep1 Rfd.
    zstep Rfd.
    zbr Rfd false.
    do 13 (zstep Rfd).
    zgenreg sw.
    zstep Rfd.
    destruct (zcond BC_NE sw c) eqn:Hcc.
    -
      zbrH Rfd true.
      zstep Rfd. zstep Rfd. zlit.
      tstep1 Rfd.
      tstep1 Rfd.
      tstep1 Rfd.
      zstep Rfd.
      pose proof (sinv_ck _ _ lf cf BAD cin1 hold1 bits1 (osz - cout) SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto]))
                    ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(right; split; [reflexivity | cbv; reflexivity])) as SI1.
      pose proof (meas_ck (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    BAD cin1 hold1 bits1 (osz - cout) ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MB1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
        eapply (KD R' Mx (ck_st (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                                 BAD cin1 hold1 bits1 (osz - cout)) lf cf SI1 MB1) end.
      + unfold s_regs_disp, s_fix, s_vars, ck_st; icx_cbn; zkeys; split_conj; zreg.
      + apply REATT; [assumption | assumption | exact HAGc].
    -
      zbrH Rfd false.
      zstep Rfd. zstep Rfd.
      zstep Rfd.
      tstep1 Rfd.
      zstep Rfd. zlit.
      tstep1 Rfd.
      zbr Rfd false.
      tstep1 Rfd.
      zbr Rfd true.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd. zlit.
      tstep1 Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_ck _ _ lf cf DONE cin1 0 0 (osz - cout) SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto]))
                    ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(right; split; [reflexivity | cbv; reflexivity])) as SI1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
        destruct (REATT Mx DONE cin1 0 0 (osz - cout) ltac:(assumption) ltac:(assumption) HAGc) as (STD' & SAT' & _ & SOUT' & Hl' & Hc' & HP');
        eapply (KL R' Mx (ck_st (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                                 DONE cin1 0 0 (osz - cout)) 1 lf cf SI1) end.
      + unfold s_regs_leave, ck_st; icx_cbn; zkeys; split_conj; zreg.
      + exact STD'.
      + exact SAT'.
      + exact SOUT'.
      + exact Hl'.
      + exact Hc'.
      + exact HP'. }
  destruct (Z.eq_dec out (osz - cout)) as [Ecout | Ecout].
  -
    zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RC ?Mx _) _ => apply (CMP RC Mx ck) end; first [zreg | assumption].
  -
    zbr Rfd false.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (ob + cout - (out - (osz - cout))) ltac:(lia).
    zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      destruct (mem_wr_arr_exists_R Mx ob osz Wob ltac:(lia) ltac:(lia) ltac:(lia)) as (fo & HOB & Hfo) end.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      pose proof (mem_arr_sub R_segs 1 Mx ob osz fo (cout - (out - (osz - cout))) (out - (osz - cout)) HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc end.
    replace (ob + 1 * (cout - (out - (osz - cout)))) with (ob + cout - (out - (osz - cout))) in Hsrc by lia.
    clear HOB.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?lc) ?Mx _) _ =>
      eapply (ADLER R' lc Mx MD T ck (ob + cout - (out - (osz - cout))) (out - (osz - cout)) (out - (osz - cout)) (u + -224) _
                (fun j => fo (cout - (out - (osz - cout)) + j)) Hh) end;
      try zreg.
    all: lazymatch goal with
         | |- forall M' : mem, _ => idtac
         | |- _ => cbv [FR_AD]; first [ reflexivity | exact Hsrc | assumption | rewrite Z.mod_small by lia; reflexivity
                         | eapply mem_wr_sub; [exact Wstk | lia | lia] | intros i Hi; apply Hfo; lia | lia ]
         end.
    intros M' R' HP. intros. zimps. zkeys.
    clear Hsrc.
    apply mpost_mpostL1 in HP. cbv [FR_AD] in HP. zreattachL HP.
    zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd. zlit.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with Hnew : mem_u64 R_segs ?Mx (p + 40) ?c' |- realizes _ (zcfg _ _ ?RC ?Mx _) _ =>
      apply (CMP RC Mx c') end; first [zreg | assumption].
Qed.


Lemma check_loop : forall (k : nat) cx fin MD T Rb l M (cinj holdj j : Z),
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_S cx ->
  32 - 8 * Z.of_nat k <= j < 40 - 8 * Z.of_nat k -> (1 <= k <= 4)%nat -> 0 <= j ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS8 = j -> zget_l Rb l kA4 = j ->
  zget_l Rb l kS11 = c_q cx + cinj -> zget_l Rb l kS2 = c_n cx - cinj -> zget_l Rb l kS7 = holdj ->
  mem_arr 1 R_segs M (c_q cx) (c_n cx) fin ->
  (forall R' hold' j',
     zget R' kS11 = c_q cx + c_n cx -> zget R' kS2 = 0 -> zget R' kS7 = hold' -> zget R' kS8 = j' ->
     j' = j + 8 * (c_n cx - cinj) -> 0 <= hold' < 2 ^ j' -> c_n cx - cinj < Z.of_nat k ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kA3 = zget_l Rb l kA3 ->
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
     zget R' kA3 = zget_l Rb l kA3 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kS3 = zget_l Rb l kS3 ->
     zget R' kS4 = zget_l Rb l kS4 ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kT4 = zget_l Rb l kT4 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kT6 = zget_l Rb l kT6 ->
     realizes R_segs (zcfg R_segs L_CHECK_BODY (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_CHECK_LOOP (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M cinj holdj j Hh Hfin CXl Hj Hk Hj0 Hc Hhj Hjc L9 L0 LA4 L10 L8 L7 Hin KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S] in CXl; destr_conj CXl.
  zkeysb. unfold L_CHECK_LOOP, L_CHECK_BODY, L_LEAVE_LD in *. pose proof two64_eq as TW64.
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

Lemma check_body : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> c_ob cx + c_osz cx <= c_u cx - FRA -> m_halted MD = None ->
  (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = CHECK -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_CHECK (zupd Rb l) M MD) T.
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
  tstep1 Rfd.
  zbr Rfd false.
  zstep Rfd.
  destruct (Z_lt_dec 31 bits) as [Hb32 | Hb32].
  - zbr Rfd true.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (check_main (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf cin hold bits CX0 OBLOW Hh Hfin eq_refl SI0) end;
      [ (icx_cbn; zreg) .. | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
  - zbr Rfd false.
    zstep Rfd.
    assert (Hkk : exists k : nat, 32 - 8 * Z.of_nat k <= bits < 40 - 8 * Z.of_nat k /\ (1 <= k <= 4)%nat).
    { exists (Z.to_nat (4 - bits / 8)).
      rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (check_loop k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' Mx cin hold bits Hh Hfin CXl Hk1 Hk2) end;
      [ lia | icx_cbn; lia | lia | lia | (icx_cbn; zreg) .. | exact Hin | | ].
    +
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_LEAVE_LD in *.
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
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_CHECK_BODY in *.
      eapply (check_main (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' [] M
                (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf (cin + Z.of_nat k) hold' j' CX0 OBLOW Hh Hfin eq_refl SI0);
        [ (icx_cbn; first [zreg | zkeys; cbv [zget_l alookup]; first [zkept | lia]]) .. | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
Qed.

Theorem arm_CHECK_s : arm_stmt_ob L_CHECK CHECK.
Proof. intros cx fin MD T M0 Rb l M st lf cf CX OBLOW Hh Hfin Hm SI RE KM K. eapply check_body; eassumption. Qed.

End WITH_ADLER.

Lemma length_body : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENGTH -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_LENGTH (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
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
  tstep1 Rfd.
  zstep Rfd.
  zbr Rfd false.
  tstep1 Rfd.
  zbr Rfd true.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zlit.
  clear H16 H24.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  pose proof (sinv_ck _ _ lf cf DONE cin hold bits out SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto]))
                ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                ltac:(left; split; [reflexivity | intros _; cbv; reflexivity])) as SI1.
  lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
    eapply (KL R' Mx (ck_st (IST LENGTH last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                             DONE cin hold bits out) 1 lf cf SI1) end.
  - unfold s_regs_leave, ck_st; icx_cbn; zkeys; split_conj; zreg.
  - close_std.
  - unfold ck_st; split; [assumption | exact SREST].
  - exact SOUT.
  - exact Hlens.
  - exact Hcodes.
  - exact HAG.
Qed.

Theorem arm_LENGTH_s : arm_stmt L_LENGTH LENGTH.
Proof. intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K. eapply length_body; eassumption. Qed.
End FXG.
