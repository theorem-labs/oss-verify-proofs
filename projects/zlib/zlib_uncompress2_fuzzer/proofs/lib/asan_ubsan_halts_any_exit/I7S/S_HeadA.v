(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require Import SBase S_Type.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_DICT_CALL : Z := 87800.
Definition L_ADLER_RET1 : Z := 87824.

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
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.
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
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

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
