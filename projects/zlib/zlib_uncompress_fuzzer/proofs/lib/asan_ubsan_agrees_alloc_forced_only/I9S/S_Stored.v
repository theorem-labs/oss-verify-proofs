(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I9S Require SBase.

Module S_StoredA.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I9S.SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Definition L_STORED_LOOP : Z := 87308.
Definition L_STORED_BODY : Z := 87968.
Definition L_STORED_BAD  : Z := 89272.
Definition L_COPY_MEMCPY : Z := 88080.
Definition L_COPY_DONE : Z := 88156.
Definition L_MEMCPY_RET : Z := 88108.

End FXG.
Ltac mode_consts :=
  cbv [reach codes_liveP HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.
Ltac mode_solve Mf tac :=
  split_conj;
  first [ right; lia_std
        | intros X; exfalso; lia_std
        | intros Hf; exfalso; destruct (Mf Hf) as [Hx _]; lia_std
        | tac ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

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
Lemma land7_mod : forall b, 0 <= b -> Z.land b 7 = b mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma landm8 : forall b, 0 <= b -> Z.land b (-8) = b - b mod 8.
Proof.
  intros b Hb. change (-8) with (Z.lnot 7). rewrite <- Z.ldiff_land.
  change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
Qed.
Lemma land24 : forall b, 0 <= b < 32 -> Z.land b 24 = b - b mod 8.
Proof.
  intros b Hb. rewrite <- landm8 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z_lt_le_dec i 5) as [L|L].
  - f_equal. destruct (Z.eq_dec i 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec i 1) as [->|]; [reflexivity|].
    destruct (Z.eq_dec i 2) as [->|]; [reflexivity|]. destruct (Z.eq_dec i 3) as [->|]; [reflexivity|].
    replace i with 4 by lia. reflexivity.
  - replace (Z.testbit b i) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|].
    apply Z.lt_le_trans with 5; [| lia]. apply Z.log2_lt_pow2; [lia|]. change (2 ^ 5) with 32. lia.
Qed.
Lemma smod64_nz : forall x, -9223372036854775808 <= x < 9223372036854775808 -> x <> 0 ->
  x mod 18446744073709551616 <> 0.
Proof. intros x Hx Hnz. lia. Qed.
Lemma low16_of_shift : forall h, 0 <= h < 18446744073709551616 ->
  Z.shiftr (Z.shiftl h 48 mod 18446744073709551616) 48 = h mod 65536.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 48) with 281474976710656. lia.
Qed.
Lemma zext32_id : forall x, 0 <= x < 4294967296 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 32 = x.
Proof. intros. apply zext32_shift. assumption. Qed.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Definition set_st (st : ist) (m cin cout hold bits len : Z) : ist :=
  IST m (t_last st) (t_flags st) cin cout hold bits (t_out st) (t_ret st)
      len (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma flags_not_m1 : forall cx st lf cf, sinv cx st lf cf -> t_mode st <> HEAD -> t_mode st <> BAD -> t_flags st <> -1.
Proof. intros cx st lf cf (_ & _ & _ & Mo) H1 H2 Hf. destruct (proj1 (proj2 Mo) Hf) as [[E|E] _]; congruence. Qed.

Lemma sinv_set : forall cx st lf cf m cin cout hold bits len,
  sinv cx st lf cf -> t_flags st <> -1 -> (t_mode st <? CHECK) = true ->
  (m = TYPE \/ m = STORED \/ m = COPY_ \/ m = COPY \/ m = BAD) ->
  ((m = COPY_ \/ m = COPY) -> len < 65536) ->
  t_cin st <= cin <= c_n cx -> t_cout st <= cout <= c_osz cx ->
  0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> bits <= 8 * cin -> 0 <= len < 4294967296 ->
  8 * (c_n cx - cin) + bits + (c_osz cx - cout) + (cout - t_cout st) <= Wm cx st ->
  sinv cx (set_st st m cin cout hold bits len) lf cf.
Proof.
  intros cx st lf cf m cin cout hold bits len (R & W & P & Mo) Hfl Hlt Hm Hlen Hc Ho Hb Hh Hbc Hl HW. apply Z.ltb_lt in Hlt.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin' cout' hold' bits' out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_cin t_cout t_flags] in *. icx_cbn. unfold Wm in HW. icx_cbn.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [| split; [exact W | split]].
  - unfold RNG, set_st; icx_cbn. split_conj; try assumption; try lia_std.
  - unfold PROG, set_st, Wm in *; icx_cbn. cbn [t_mode] in Hlt. mode_consts. lia_std.
  - pose proof (proj1 (proj2 Mo)) as Mf. clear Mo W P. unfold MODE, set_st; icx_cbn. mode_consts.
    mode_solve Mf ltac:(intros X; split_conj; lia_std).
Qed.

Lemma meas_set : forall cx st m cin cout hold bits len,
  8 * (c_n cx - cin) + bits + (c_osz cx - cout) < Wm cx st \/
  (8 * (c_n cx - cin) + bits + (c_osz cx - cout) <= Wm cx st /\ rank m < rank (t_mode st)) ->
  meas cx (set_st st m cin cout hold bits len) < meas cx st.
Proof.
  intros cx st m cin cout hold bits len H.
  destruct H as [H | [H1 H2]].
  - apply meas_dec_W. unfold Wm, set_st in *. destruct cx, st; icx_cbn. cbn in *. lia_std.
  - apply meas_dec_rank; [| unfold set_st; cbn; exact H2]. unfold Wm, set_st in *. destruct cx, st; icx_cbn. cbn in *. lia_std.
Qed.

Section WITH_MEMCPY.
Hypothesis MEMCPY : memcpy_spec_s.

Lemma copy_body : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = COPY -> t_length st < 65536 -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_COPY (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm HL16 SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & WIN_ & PROG_ & MODE_).
  pose proof (flags_not_m1 _ _ _ _ SI0 ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_length t_flags] in Hm, HL16, Hfl. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn. clear WIN_ MODE_.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  assert (H92 : mem_u32 R_segs M (p + 108) length) by (unfold st_rest in SREST; icx_cbn; destr_conj SREST; assumption).
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q104 & Q96 & _ & Q72 & _).
  zkeysb. unfold L_COPY, L_COPY_MEMCPY, L_COPY_DONE, L_MEMCPY_RET, L_RELOAD, L_DISP, L_LEAVE_LD, L_SETMODE in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  tstep1 Rfd.
  destruct (Z.eq_dec length 0) as [HL0 | HL0].
  {
    subst length. zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_set _ _ lf cf TYPE cin cout hold bits 0 SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(cbv [COPY_ COPY TYPE]; lia)
                  ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
    pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST COPY last flags cin cout hold bits out ret 0 offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  TYPE cin cout hold bits 0 ltac:(right; split; [unfold Wm; cbn; lia | vm_compute; reflexivity])) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KSM R' Mx _ COPY lf cf SI1 MB1) end.
    - unfold s_regs_d0, s_fix, s_vars, set_st; icx_cbn; cbv [TYPE]; zkeys; split_conj; zreg.
    - close_std.
    - exact Hmode.
    - unfold set_st; icx_cbn. exact SREST.
    - exact SRET.
    - exact SOUT.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  pose proof (smod64_nz length ltac:(lia) HL0) as Hnz.
  zbr Rfd false.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?M1 _) _ =>
  assert (JL : forall RJ,
    zget RJ kSP = u + -224 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA0 = u -> zget RJ kA1 = 0 ->
    zget RJ kS2 = n - cin -> zget RJ kS3 = ob + cout -> zget RJ kRA = osz - cout ->
    zget RJ kS11 = q + cin -> zget RJ kS7 = hold -> zget RJ kS8 = bits ->
    realizes R_segs (zcfg R_segs 93620 (zupd RJ []) M1 MD) T);
  [| assert (JM : forall RJ copy,
    zget RJ kSP = u + -224 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA0 = u -> zget RJ kA1 = 0 -> zget RJ kS6 = p + 168 -> zget RJ kS9 = 67008 ->
    zget RJ kS2 = n - cin -> zget RJ kS3 = ob + cout -> zget RJ kRA = osz - cout ->
    zget RJ kS11 = q + cin -> zget RJ kS7 = hold -> zget RJ kS8 = bits -> zget RJ kS4 = copy ->
    1 <= copy -> copy <= length -> copy <= n - cin -> copy <= osz - cout ->
    realizes R_segs (zcfg R_segs 88080 (zupd RJ []) M1 MD) T) ] end.
  {
    intros RJ. intros. zkeys.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KLL R' Mx (IST COPY last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI0) end.
    - unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SRET.
    - exact SOUT.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  {
    intros RJ copy. intros. zkeys.
    zstep Rfd. zstep Rfd.
    zsetreg copy ltac:(symmetry; apply zext32_id; lia).
    zstep Rfd. zstep Rfd. zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (mem_arr_sub R_segs 1 _ q n fin cin copy Hin ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc.
    apply mem_arr8_mem_is in Hsrc.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R ?lc') ?Mx _) _ =>
      eapply (MEMCPY R lc' Mx MD T (ob + cout) (q + 1 * cin) _ copy _ Hh) end.
    - zreg. - zreg. - zreg. - zreg. - reflexivity.
    - exact Hsrc.
    - rewrite length_map, zseq_length. lia.
    - eapply mem_wr_sub; [exact Wob | lia | lia].
    - lia. - lia. - lia. - lia. - zlia.
    - intros M2 R2 HP HD HS HW E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
      zimps. clear HD HS Hsrc. apply mpost_mpostL1 in HP. zreattachL HP.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      tstep1 Rfd.
      zstep Rfd.
      tstep1 Rfd.
      tstep1 Rfd.
      tstep1 Rfd.
      unfold st_rest in SREST. icx_cbn.
      dand SREST as (C12 & C24 & C64 & C68 & _ & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
      tstep1 Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_set _ _ lf cf COPY (cin + copy) (cout + copy) hold bits (length - copy) SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(intros _; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST COPY last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    COPY (cin + copy) (cout + copy) hold bits (length - copy) ltac:(left; unfold Wm; cbn; lia)) as MB1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
        eapply (KRL R' Mx _ lf cf SI1 MB1) end.
      + unfold s_regs_reload, set_st; icx_cbn; zkeys; split_conj; try zreg; try (intros _; zreg); try (intros C; discriminate C).
      + unfold k_mem, set_st; icx_cbn; split_conj;
          [ close_std
          | unfold st_at, st_rest; icx_cbn; split_conj; assumption
          | exact SRET | exact SOUT | exact Hlens | exact Hcodes | exact HAG ]. }
  destruct (Z_lt_dec length (n - cin)) as [C1 | C1].
  - zbr Rfd true.
    destruct (Z_lt_dec length (osz - cout)) as [C2 | C2].
    + zbr Rfd true.
      zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JM R' length) end; first [zreg | lia].
    + zbr Rfd false.
      zstep Rfd.
      destruct (Z.eq_dec (osz - cout) 0) as [C3 | C3].
      * zbr Rfd false.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JL R') end; first [zreg | lia].
      * zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JM R' (osz - cout)) end; first [zreg | lia].
  - zbr Rfd false.
    zstep Rfd.
    destruct (Z_lt_dec (n - cin) (osz - cout)) as [C2 | C2].
    + zbr Rfd false.
      destruct (Z.eq_dec (n - cin) 0) as [C3 | C3].
      * zbr Rfd false.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JL R') end; first [zreg | lia].
      * zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JM R' (n - cin)) end; first [zreg | lia].
    + zbr Rfd true.
      zstep Rfd.
      destruct (Z.eq_dec (osz - cout) 0) as [C3 | C3].
      * zbr Rfd false.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JL R') end; first [zreg | lia].
      * zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JM R' (osz - cout)) end; first [zreg | lia].
Qed.

Lemma copy_len_bound : forall cx st lf cf, sinv cx st lf cf -> (t_mode st = COPY_ \/ t_mode st = COPY) -> t_length st < 65536.
Proof.
  intros cx st lf cf (_ & _ & _ & Mo) Hm. unfold MODE in Mo. destr_conj Mo.
  match goal with H : t_mode st = COPY_ \/ t_mode st = COPY -> _ |- _ => exact (H Hm) end.
Qed.

Theorem arm_COPY_s : arm_stmt L_COPY COPY.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  eapply copy_body; try eassumption. apply (copy_len_bound _ _ _ _ SI). right; exact Hm.
Qed.

Theorem arm_COPY__s : arm_stmt L_COPY_ COPY_.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof (copy_len_bound _ _ _ _ SI (or_introl Hm)) as HL16.
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_length t_flags] in Hm, HL16, Hfl. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_. pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  pose proof RE as RE0. unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  zkeysb. unfold L_COPY_, L_COPY in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.
  tstep1 Rfd.
  pose proof (sinv_set _ _ lf cf COPY cin cout hold bits length SI Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(intros _; exact HL16)
                ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
  pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                (IST COPY_ last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                COPY cin cout hold bits length ltac:(right; split; [unfold Wm; cbn; lia | vm_compute; reflexivity])) as MB1.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
    eapply (copy_body (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
              (set_st (IST COPY_ last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY cin cout hold bits length)
              lf cf CX0 Hh Hfin eq_refl ltac:(cbn; exact HL16) SI1) end.
  - unfold s_regs_arm, s_fix, s_vars, set_st; icx_cbn; zkeys; split_conj; zreg.
  - unfold k_mem, set_st; icx_cbn; split_conj;
      [ close_std | split; [assumption | exact SREST] | exact SRET | exact SOUT | exact Hlens | exact Hcodes | exact HAG ].
  - eapply KALL_mono; [| exact K]. lia.
Qed.

End WITH_MEMCPY.
End FXG.
End S_StoredA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I9S Require Import SBase. Import S_StoredA.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Section WITH_MEMCPY.
Hypothesis MEMCPY : memcpy_spec_s.

Lemma stored_loop : forall (k : nat) cx fin MD T Rb l M (cin0' cinj holdj j : Z),
  let cx' := cx in
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_S cx ->
  j = 32 - 8 * Z.of_nat k -> (1 <= k <= 4)%nat ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS8 = j -> zget_l Rb l kA3 = j ->
  zget_l Rb l kA4 = c_q cx + cinj -> zget_l Rb l kS11 = c_q cx + cinj ->
  zget_l Rb l kS2 = c_n cx - cinj -> zget_l Rb l kS7 = holdj ->
  mem_arr 1 R_segs M (c_q cx) (c_n cx) fin ->
  (forall R' hold',
     zget R' kA4 = c_q cx + c_n cx -> zget R' kS2 = 0 -> zget R' kS7 = hold' ->
     zget R' kS8 = j + 8 * (c_n cx - cinj) -> 0 <= hold' < 2 ^ (j + 8 * (c_n cx - cinj)) -> c_n cx - cinj < Z.of_nat k ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kS3 = zget_l Rb l kS3 ->
     zget R' kS4 = zget_l Rb l kS4 -> 
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kT4 = zget_l Rb l kT4 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kT6 = zget_l Rb l kT6 ->
     realizes R_segs (zcfg R_segs L_LEAVE_A4 (zupd R' []) M MD) T) ->
  (forall R' hold',
     zget R' kS11 = c_q cx + cinj + Z.of_nat k -> zget R' kS2 = c_n cx - cinj - Z.of_nat k -> zget R' kS7 = hold' ->
     zget R' kS8 = 32 -> 0 <= hold' < 2 ^ 32 -> Z.of_nat k <= c_n cx - cinj ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kS3 = zget_l Rb l kS3 ->
     zget R' kS4 = zget_l Rb l kS4 -> 
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kT4 = zget_l Rb l kT4 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kT6 = zget_l Rb l kT6 ->
     realizes R_segs (zcfg R_segs L_STORED_BODY (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_STORED_LOOP (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M cin0' cinj holdj j cx' Hh Hfin CXl Hj Hk Hc Hhj Hjc L9 L0 LA3 LA4 L10 L8 L7 Hin KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. subst cx'.
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S] in CXl; destr_conj CXl.
  zkeysb. unfold L_STORED_LOOP, L_STORED_BODY, L_LEAVE_A4 in *. pose proof two64_eq as TW64.
  assert (Hj32 : 2 ^ j <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 32) with 4294967296 in Hj32.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  -
    zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj) end; try zreg; try lia.
    + replace (j + 8 * (n - cinj)) with j by lia. lia.
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
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KDN R' (fin cinj * 2 ^ j + holdj)) end; try zreg; try lia.
      replace 32 with (j + 8) by lia. lia.
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') _ _) _ =>
        eapply (IH (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' M cin0' (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) Hh Hfin) end;
        [ unfold ctx_lin; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S]; split_conj; assumption || lia
        | lia | lia | icx_cbn; lia | lia | icx_cbn; lia
        | (icx_cbn; zreg) .. | exact Hin | | ].
      * intros R' hold'. icx_cbn. intros. eapply KLV; try eassumption; try lia; try zkept.
        all: replace (j + 8 * (n - cinj)) with (j + 8 + 8 * (n - (cinj + 1))) by lia; assumption.
      * intros R' hold'. icx_cbn. intros. eapply KDN; try eassumption; try lia; try zkept.
        all: assumption.
Qed.

Theorem arm_STORED_s : arm_stmt L_STORED STORED.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof KM as KM0. pose proof K as KA0.
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof (proj1 CX) as CXl. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags] in Hm, Hfl. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_. pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  assert (Hk : 0 <= bits mod 8 <= bits) by (Z.to_euclidean_division_equations; lia).
  pose proof (shiftr_lt_pow2 hold bits (bits mod 8) ltac:(lia) ltac:(lia)) as Hsh.
  zkeysb. unfold L_STORED, L_STORED_LOOP, L_STORED_BODY, L_STORED_BAD, L_LEAVE_A4, L_LEAVE, L_LEAVE_LD, L_BADMSG_S10, L_COPY_ in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.
  zsetreg (bits mod 8) ltac:(symmetry; apply land7_mod; lia).
  zstep Rfd.
  zstep Rfd.
  zsetreg (Z.shiftr hold (bits mod 8))
    ltac:(rewrite (Z.mod_small hold) by lia; rewrite (Z.mod_small (bits mod 8)) by (Z.to_euclidean_division_equations; lia); reflexivity).
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (BODY : forall RJ cin1 hold1 bits1,
    zget RJ kSP = u + -224 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA0 = u -> zget RJ kA1 = 0 -> zget RJ kS6 = p + 168 -> zget RJ kT6 = -16180 ->
    zget RJ kT4 = 30 -> zget RJ kS9 = 67008 -> zget RJ kS4 = 16209 ->
    zget RJ kS2 = n - cin1 -> zget RJ kS3 = ob + cout -> zget RJ kRA = osz - cout ->
    zget RJ kS11 = q + cin1 -> zget RJ kS7 = hold1 -> zget RJ kS8 = bits1 ->
    cin <= cin1 <= n -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (n - cin1) + bits1 = 8 * (n - cin) + (bits - bits mod 8) ->
    realizes R_segs (zcfg R_segs 87968 (zupd RJ []) Mc MD) T) end.
  { intros RJ cin1 hold1 bits1. intros. zkeys.
    pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh1.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (hold1 mod 65536) ltac:(symmetry; apply low16_of_shift; lia).
    zstep Rfd.
    zsetreg (Z.lxor (Z.shiftr hold1 16) (hold1 mod 65536)) ltac:(rewrite (Z.mod_small hold1 18446744073709551616) by lia; reflexivity).
    assert (Hx : 0 <= Z.lxor (Z.shiftr hold1 16) (hold1 mod 65536) < 18446744073709551616).
    { change 18446744073709551616 with (2 ^ 64). apply lxor_bound.
      - pose proof (shiftr_lt_pow2 hold1 bits1 16 ltac:(lia) ltac:(assumption)) as X.
        assert (2 ^ (bits1 - 16) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
      - Z.to_euclidean_division_equations; lia. }
    assert (Hm16 : 0 <= hold1 mod 65536 < 65536) by (Z.to_euclidean_division_equations; lia).
    destruct (Z.eq_dec (Z.lxor (Z.shiftr hold1 16) (hold1 mod 65536)) 65535) as [EQ | NE].
    -
      rewrite EQ.
      zstep Rfd. zlit.
      zbr Rfd false.
      zstep Rfd.
      unfold st_rest in SREST. icx_cbn.
      dand SREST as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
      tstep1 Rfd.
      zstep Rfd.
      zstep Rfd.
      tstep1 Rfd.
      zstep Rfd.
      zbr Rfd true.
      pose proof (sinv_set _ _ lf cf COPY_ cin1 cout 0 0 (hold1 mod 65536) SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(intros _; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    COPY_ cin1 cout 0 0 (hold1 mod 65536) ltac:(left; unfold Wm; cbn; lia)) as MB1.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
        eapply (arm_COPY__s MEMCPY (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                  (set_st (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY_ cin1 cout 0 0 (hold1 mod 65536))
                  lf cf CX0 Hh Hfin eq_refl SI1) end.
      + unfold s_regs_arm, s_fix, s_vars, set_st; icx_cbn; zkeys; split_conj; zreg.
      + unfold k_mem, set_st; icx_cbn; split_conj;
          [ close_std | unfold st_at, st_rest; icx_cbn; split_conj; assumption | exact SRET | exact SOUT | exact Hlens | exact Hcodes | exact HAG ].
      + eapply KALL_mono; [| exact KA0]. lia.
    -
      zstep Rfd. zlit.
      assert (Hne : Z.lxor (Z.shiftr hold1 16) (hold1 mod 65536) mod 18446744073709551616 <> 65535) by (rewrite Z.mod_small by lia; exact NE).
      zbr Rfd true.
      zstep Rfd. zstep Rfd. zlit.
      zstep Rfd.
      pose proof (sinv_set _ _ lf cf BAD cin1 cout hold1 bits1 length SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(cbv [COPY_ COPY BAD]; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    BAD cin1 cout hold1 bits1 length ltac:(right; split; [unfold Wm; cbn; lia | vm_compute; reflexivity])) as MB1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
        eapply (KB10 R' Mx (set_st (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                               STORED cin1 cout hold1 bits1 length) lf cf) end.
      + unfold bad_of, set_st; cbn. exact SI1.
      + unfold bad_of, set_st; cbn. unfold set_st in MB1; cbn in MB1. exact MB1.
      + unfold s_regs_d10, s_fix, s_vars, set_st; icx_cbn; zkeys; split_conj; zreg.
      + zreg.
      + unfold k_mem, set_st; icx_cbn; split_conj;
          [ close_std | split; [exact Hmode | exact SREST] | exact SRET | exact SOUT | exact Hlens | exact Hcodes | exact HAG ]. }
  destruct (Z_lt_dec 31 bits) as [Hb32 | Hb32].
  -
    zbr Rfd true.
    zstep Rfd.
    zsetreg (bits - bits mod 8) ltac:(symmetry; apply landm8; lia).
    assert (Hmono : 2 ^ (bits - bits mod 8) <= 2 ^ bits) by (apply Z.pow_le_mono_r; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (BODY R' cin (Z.shiftr hold (bits mod 8)) (bits - bits mod 8)) end;
      first [zreg | lia | Z.to_euclidean_division_equations; lia].
  -
    zbr Rfd false.
    zstep Rfd.
    zsetreg (bits - bits mod 8) ltac:(symmetry; apply land24; lia).
    zstep Rfd.
    zstep Rfd.
    assert (Hkk : exists k : nat, bits - bits mod 8 = 32 - 8 * Z.of_nat k /\ (1 <= k <= 4)%nat).
    { exists (Z.to_nat (4 - bits / 8)). rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (stored_loop k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' Mx cin0 cin (Z.shiftr hold (bits mod 8)) (bits - bits mod 8) Hh Hfin CXl Hk1 Hk2) end;
      [ icx_cbn; lia | exact Hsh | lia | zreg .. | exact Hin | | ].
    +
      intros R' hold'. icx_cbn. intros. zimps. zkeys. unfold L_LEAVE_A4, L_LEAVE_LD in *.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_set _ _ lf cf STORED n cout hold' (bits - bits mod 8 + 8 * (n - cin)) length SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(cbv [COPY_ COPY STORED]; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KLL Rx Mx _ lf cf SI1) end.
      * unfold s_regs_leave_ld, set_st; icx_cbn; zkeys; split_conj; try zreg. all: zkept.
      * close_std.
      * unfold set_st; split; [exact Hmode | exact SREST].
      * exact SRET.
      * exact SOUT.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' hold'. icx_cbn. intros. zimps. zkeys. unfold L_STORED_BODY in *.
      apply (BODY R' (cin + Z.of_nat k) hold' 32); try zkept; try lia.
Qed.

End WITH_MEMCPY.
End FXG.
