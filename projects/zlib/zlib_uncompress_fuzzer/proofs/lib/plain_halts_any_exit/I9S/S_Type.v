(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* THE BLOCK-TYPE WALK TEXT IN THE RUN FORM. Every stretch of step lines of the hand text is ONE RUN of the
   sturdy driver: no step count and no branch direction is written. The text's three own labels are fields of
   the layout text. The inner lemma and the two inner join points take the walk base text's own map of the
   dispatch, at a state that the statement binds. THERE IS NO VALUE HINT: each value replacement of the hand
   text is a model fact in hand before its run, by a named lemma whose left side is the machine form. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import SBase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZGo11 SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Ltac mode_consts :=
  cbv [reach codes_liveP HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.
Ltac mode_solve Mf tac :=
  split_conj;
  first [ right; lia_std
        | intros X; exfalso; lia_std
        | intros Hf; exfalso; destruct (Mf Hf) as [Hx _]; lia_std
        | tac ].

(* the text's three own labels are fields of the layout text; here they have their short names only *)
Local Notation L_TYPEDO_LAST := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_TYPEDO_LAST (only parsing).
Local Notation L_TYPEDO_BODY := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_TYPEDO_BODY (only parsing).
Local Notation L_TYPEDO_DROP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_TYPEDO_DROP (only parsing).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma pow2_le_40 : forall b, 0 <= b <= 40 -> 2 ^ b <= 2 ^ 40.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.

Lemma hold_u64 : forall h b, 0 <= b <= 40 -> 0 <= h < 2 ^ b -> 0 <= h < 18446744073709551616.
Proof. intros h b Hb Hh. pose proof (pow2_le_40 b Hb). change (2 ^ 40) with 1099511627776 in *. lia. Qed.

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

Lemma bits2_of_shift : forall h, 0 <= h < 18446744073709551616 ->
  Z.shiftr (Z.shiftl h 61 mod 18446744073709551616) 62 = (h / 2) mod 4.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 61) with 2305843009213693952. change (2 ^ 62) with 4611686018427387904. lia.
Qed.

Lemma smod64_nz : forall x, -9223372036854775808 <= x < 9223372036854775808 -> x <> 0 ->
  x mod 18446744073709551616 <> 0.
Proof. intros x Hx Hnz. lia. Qed.

Lemma land7_mod : forall b, 0 <= b -> Z.land b 7 = b mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma landm8 : forall b, 0 <= b -> Z.land b (-8) = b - b mod 8.
Proof.
  intros b Hb. change (-8) with (Z.lnot 7). rewrite <- Z.ldiff_land.
  change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
Qed.
Lemma land1_mod : forall h, 0 <= h -> Z.land h 1 = h mod 2.
Proof. intros. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma lor8_small : forall b, 0 <= b < 8 -> Z.lor b 8 = b + 8.
Proof.
  intros b Hb.
  assert (C : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7) by lia.
  decompose [or] C; subst; reflexivity.
Qed.

(* THE MACHINE FORMS OF THREE VALUES, each equal to its model form (the left side is the form the machine's
   step leaves; the numerals are widths of the instruction set and values of the source) *)
Lemma mf_drop_hold : forall h, 0 <= h < 18446744073709551616 ->
  Z.shiftr (h mod 18446744073709551616) 3 = Z.shiftr h 3.
Proof. intros h Hh. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma mf_bb_hold : forall h b, 0 <= h < 18446744073709551616 -> 0 <= b ->
  Z.shiftr (h mod 18446744073709551616) (Z.land b 7 mod 64) = Z.shiftr h (b mod 8).
Proof.
  intros h b Hh Hb. rewrite land7_mod by lia. rewrite (Z.mod_small h) by lia.
  rewrite (Z.mod_small (b mod 8)) by lia. reflexivity.
Qed.

Lemma mf_pull_byte : forall f b, 0 <= b < 64 -> Z.shiftl f (b mod 64) = f * 2 ^ b.
Proof. intros f b Hb. rewrite (Z.mod_small b) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition bytebits_st (st : ist) : ist :=
  IST CHECK (t_last st) (t_flags st) (t_cin st) (t_cout st)
      (Z.shiftr (t_hold st) (t_bits st mod 8)) (t_bits st - t_bits st mod 8) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Definition typedo_st (st : ist) (m cin1 hold1 bits1 : Z) (fx : bool) : ist :=
  IST m (Z.land hold1 1) (t_flags st) cin1 (t_cout st) (Z.shiftr hold1 3) (bits1 - 3) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st)
      (if fx then CLenfix else t_lc st) (if fx then CDistfix else t_dc st)
      (if fx then 9 else t_lb st) (if fx then 5 else t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

(* the state `st` with its input count, its hold and its bit count set to the given values: the state at which
   the walk base text's map is taken at this text's inner join points *)
Definition reg_st (st : ist) (cin1 hold1 bits1 : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) cin1 (t_cout st) hold1 bits1 (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_bytebits : forall cx st lf cf,
  sinv cx st lf cf -> (t_mode st = TYPE \/ t_mode st = TYPEDO) ->
  sinv cx (bytebits_st st) lf cf /\ meas cx (bytebits_st st) < meas cx st.
Proof.
  intros cx st lf cf (RG & W & P & Mo) Hm.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode] in Hm.
  unfold RNG in RG. icx_cbn. destr_conj RG.
  assert (Hk : 0 <= bits mod 8 <= bits) by (Z.to_euclidean_division_equations; lia_std).
  pose proof (shiftr_lt_pow2 hold bits (bits mod 8) ltac:(lia_std) ltac:(lia_std)) as Hsh.
  assert (Hmono : 2 ^ (bits - bits mod 8) <= 2 ^ bits) by (apply Z.pow_le_mono_r; lia_std).
  split.
  - split; [| split; [exact W | split]].
    + unfold RNG, bytebits_st; icx_cbn. split_conj; try assumption; try lia_std.
    + unfold PROG, bytebits_st, Wm in *; icx_cbn. mode_consts. lia_std.
    + pose proof (proj1 (proj2 Mo)) as Mf. clear Mo W P. unfold MODE, bytebits_st; icx_cbn. mode_consts.
      mode_solve Mf fail.
  - apply meas_dec_rank; [unfold Wm, bytebits_st; icx_cbn; lia_std|].
    unfold bytebits_st; cbn [t_mode]. unfold rank. mode_consts.
    destruct Hm as [-> | ->]; cbn; lia_std.
Qed.

Lemma sinv_typedo : forall cx st lf cf m cin1 hold1 bits1 fx,
  sinv cx st lf cf -> (t_mode st = TYPE \/ t_mode st = TYPEDO) ->
  t_cin st <= cin1 <= c_n cx -> 3 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
  8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  (m = STORED \/ m = TABLE \/ m = BAD \/ m = LEN_) -> (fx = true <-> m = LEN_) ->
  sinv cx (typedo_st st m cin1 hold1 bits1 fx) lf cf /\ meas cx (typedo_st st m cin1 hold1 bits1 fx) < meas cx st.
Proof.
  intros cx st lf cf m cin1 hold1 bits1 fx (RG & W & P & Mo) Hm Hc Hb Hh Hbc HW Hm' Hfx.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_cin t_bits] in Hm, Hc, HW. icx_cbn.
  unfold RNG in RG. icx_cbn. destr_conj RG.
  pose proof (shiftr_lt_pow2 hold1 bits1 3 ltac:(lia_std) Hh) as Hsh.
  assert (Hl1 : 0 <= Z.land hold1 1 < 2) by (rewrite land1_mod by lia_std; Z.to_euclidean_division_equations; lia_std).
  split.
  - split; [| split; [exact W | split]].
    + unfold RNG, typedo_st; icx_cbn. split_conj; try assumption; try lia_std.
      * destruct fx; [lia_std | assumption].
      * destruct fx; [lia_std | assumption].
      * destruct fx; [lia_std | assumption].
      * destruct fx; [lia_std | assumption].
      * destruct fx; [exact I | assumption].
      * destruct fx; [exact I | assumption].
    + unfold PROG, typedo_st, Wm in *; icx_cbn. mode_consts. lia_std.
    + pose proof (proj1 (proj2 Mo)) as Mf. clear Mo W P. unfold MODE, typedo_st; icx_cbn. mode_consts.
      mode_solve Mf ltac:(intros Hlv; assert (m = 16199) by lia_std; assert (Efx : fx = true) by (apply Hfx; assumption); subst fx;
                          unfold tables_live; cbn; split; reflexivity).
  - apply meas_dec_W. unfold Wm, typedo_st; icx_cbn. lia_std.
Qed.

Lemma mem_u32_eqmod {RCa1 : RunCtx}  : forall M a e e', e mod 4294967296 = e' mod 4294967296 ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a e -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a e'.
Proof.
  intros M a e e' E H. unfold mem_u32 in *.
  rewrite <- (Z_to_le_bytes_mod32 4 e) in H by lia. rewrite E, Z_to_le_bytes_mod32 in H by lia. exact H.
Qed.

Section TYPEDO_CODE.
Context {RCa1 : RunCtx}.

Lemma typedo_drop : forall cx fin MD T M0 (B : Z) RR M st' lf cf hold1 bits1,
  ctx_ok ROMHI_S cx -> m_halted MD = None ->
  sinv cx st' lf cf -> meas cx st' < B ->
  t_hold st' = Z.shiftr hold1 3 -> t_bits st' = bits1 - 3 -> 3 <= bits1 <= 40 -> 0 <= hold1 < two64 ->
  s_regs_disp cx (reg_st st' (t_cin st') hold1 bits1) RR [] ->
  k_mem cx fin M0 st' lf cf M ->
  KDISP cx fin MD T M0 B ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TYPEDO_DROP (zupd RR []) M MD) T.
Proof.
  intros cx fin MD T M0 B RR M st' lf cf hold1 bits1 CX Hh SI MB Eh Eb Hb1 Hh1 RDH KM KD.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  unfold s_regs_disp, s_fix, s_vars, reg_st in RDH. icx_cbn. destr_conj RDH.
  zkeysb. unfold L_TYPEDO_DROP, L_DISP in *. zgetl_nil. pose proof two64_eq as TW64.
  (* the model's facts of the hold and of the bit count after the block's head bits: in hand before the run *)
  pose proof (mf_drop_hold hold1 ltac:(lia)) as HVh.
  pose proof (swrap32_small (bits1 + -3) ltac:(lia)) as HVb.
  (* ONE RUN to the dispatch *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ => eapply (KD RX MX st' lf cf SI MB) end).
  - unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys. rewrite Eh, Eb. split_conj; zreg.
  - exact KM.
Qed.

Definition fp_typedo_f (p : Z) : list (Z * Z) := [(p + 8, 8); (p + 120, 24)].
Definition fp_typedo_d (u p : Z) : list (Z * Z) := [(p + 8, 8); (u + 48, 8)].

Lemma typedo_body : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  (t_mode st = TYPE \/ t_mode st = TYPEDO) -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TYPEDO (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof KM as KM0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & WIN_ & PROG_ & MODE_).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode] in Hm. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  assert (H12 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 12) last) by (unfold st_rest in SREST; icx_cbn; dand SREST as (H12 & _); exact H12).
  clear ROM Wob Ww CST HK Hmode SREST SRET SOUT Hlens Hcodes WIN_ MODE_.
  (* the frame's slots are opened ALL, before the runs *)
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn. destr_conj FRM'. clear FRM.
  zkeysb. unfold L_TYPEDO, L_TYPEDO_LAST, L_TYPEDO_BODY, L_TYPEDO_DROP, L_SETMODE, L_DISP, L_LEAVE_LD in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_typedo_f p) ltac:(unfold fp_typedo_f; ranges_ok_tac)) as HSTf.
  assert (HAGf : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (fp_typedo_f p)) M) by (apply mpostL_refl).
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_typedo_d u p) ltac:(unfold fp_typedo_d; ranges_ok_tac)) as HSTd.
  assert (HAGd : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (fp_typedo_d u p)) M) by (apply mpostL_refl).
  unfold fp_typedo_f, fp_typedo_d in HSTf, HAGf, HSTd, HAGd.
  destruct (Z.eq_dec last 0) as [Hl0 | Hl0].
  2: {
    pose proof (smod64_nz last ltac:(lia) Hl0) as Hnz.
    destruct (sinv_bytebits _ _ lf cf SI0 Hm) as [SI1 MB1].
    (* the model's facts of the hold shifted and of the bit count rounded down to a byte: in hand before the
       run *)
    pose proof (mf_bb_hold hold bits ltac:(lia) ltac:(lia)) as HVh.
    pose proof (landm8 bits ltac:(lia)) as HVb.
    clear HSTf HAGf HSTd HAGd. open_kmem KM0. destruct SAT as [Hmode SREST].
    (* ONE RUN from the case entry to the place that sets the mode *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ =>
      eapply (KSM RX MX (bytebits_st (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext))
                  mode lf cf SI1 MB1) end);
      [ unfold s_regs_d0, s_fix, s_vars, bytebits_st; icx_cbn; cbv [CHECK]; zkeys; split_conj; zreg
      | exact STD | exact Hmode | unfold bytebits_st; exact SREST
      | unfold s_ret, bytebits_st in *; icx_cbn; exact SRET | unfold s_out, bytebits_st in *; icx_cbn; exact SOUT | exact Hlens | exact Hcodes | exact HAG ]. }
  subst last.
  (* J: the body's place. ITS FACTS ARE THE WALK BASE TEXT's OWN MAP OF THE DISPATCH, at the state with the input
     count, the hold and the bit count that the statement binds *)
  assert (J : forall RJ cin1 hold1 bits1,
    s_regs_disp (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (reg_st (IST mode 0 flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
         cin1 hold1 bits1) RJ [] ->
    cin <= cin1 <= n -> 3 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (n - cin1) + bits1 = 8 * (n - cin) + bits ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TYPEDO_BODY (zupd RJ []) M MD) T).
  { intros RJ cin1 hold1 bits1 RJH. intros.
    unfold s_regs_disp, s_fix, s_vars, reg_st in RJH. icx_cbn. destr_conj RJH. zgetl_nil.
    cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_TYPEDO_BODY]. zkeys. clear H12 Hin.
    pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh1.
    (* DROP: the place where the block's head bits are dropped: THE SAME MAP AT THE SAME STATE; the memory's
       facts of the mode, of the last-block flag and (the block with the preset tables) of those tables *)
    assert (DROP : forall RD Mq m fx,
      (m = STORED \/ m = TABLE \/ m = BAD \/ m = LEN_) -> (fx = true <-> m = LEN_) ->
      s_regs_disp (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
        (reg_st (IST mode 0 flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
           cin1 hold1 bits1) RD [] ->
      mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 8) m -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 12) (Z.land hold1 1) ->
      (fx = true -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 120) LENFIX_ADDR /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 128) DISTFIX_ADDR /\
                    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 136) 9 /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 140) 5) ->
      (fx = true -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M Mq [(p + 8, 8); (p + 120, 24)]) -> (fx = false -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M Mq [(p + 8, 8); (u + 48, 8)]) ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TYPEDO_DROP (zupd RD []) Mq MD) T).
    { intros RD Mq m fx Hm1 Hfx RDH Mm Ml HT HPa HPb.
      destruct (sinv_typedo (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST mode 0 flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  lf cf m cin1 hold1 bits1 fx SI0 Hm ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) Hm1 Hfx) as [SI1 MB1].
      clear HAGf HSTf HAGd HSTd HST HAG Wstk Wp.
      (* the frame's opened slots speak of the memory before this place: they go *)
      repeat match goal with HF : mem_u64 _ M (u + _) _ |- _ => clear HF end.
      open_kmem KM0. open_std STD. destruct SAT as [Hmode SREST]. clear Hmode.
      (* the fact of the output count's slot is opened before the memory's facts are carried over *)
      unfold s_out in SOUT.
      unfold st_rest in SREST. icx_cbn.
      dand SREST as (_ & H24 & H64 & H68 & H92 & H96 & H100 & H104 & H112 & H120 & H124 & H128 & H132 & H136 & H140 & H144).
      fp_frame_from HP0.
      destruct fx;
        [ dand (HT eq_refl) as (T1 & T2 & T3 & T4); clear HT H104 H112 H120 H124; pose proof (HPa eq_refl) as HPq
        | clear HT; pose proof (HPb eq_refl) as HPq ]; clear HPa HPb.
      all: cbv [N_LENS N_CODES] in Hlens, Hcodes.
      all: zreattachL HPq.
      all: eapply (typedo_drop (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 _ RD Mq _ lf cf hold1 bits1 CX0 Hh SI1 MB1);
        [ reflexivity | reflexivity | lia | lia
        | first [ exact RDH
                | (unfold s_regs_disp, s_fix, s_vars, reg_st, typedo_st in RDH |- *; icx_cbn; exact RDH) ]
        | unfold k_mem; split_conj;
          [ close_std
          | unfold st_at, st_rest, typedo_st; icx_cbn; cbv [cp_addr LENFIX_ADDR DISTFIX_ADDR o_codes]; icx_cbn; split_conj; assumption
          | unfold s_ret, typedo_st in *; icx_cbn; assumption
          | unfold s_out, typedo_st in *; icx_cbn; first [ exact I | assumption ]
          | assumption | assumption | exact HAG ]
        | exact KD ]. }
    (* the drop place's continuation for each of the four block types, by a name *)
    pose proof (fun RX MX => DROP RX MX LEN_ true) as DFX.
    pose proof (fun RX MX => DROP RX MX TABLE false) as DTB.
    pose proof (fun RX MX => DROP RX MX BAD false) as DBD.
    pose proof (fun RX MX => DROP RX MX STORED false) as DST.
    assert (Hc4 : 0 <= (hold1 / 2) mod 4 < 4) by (Z.to_euclidean_division_equations; lia).
    (* the model's fact of the block's two type bits: in hand before the run, by the lemma above *)
    pose proof (bits2_of_shift hold1 ltac:(lia)) as HB2.
    (* ONE RUN to the test of the block type *)
    zto_branch Rfd.
    destruct (Z.eq_dec ((hold1 / 2) mod 4) 1) as [E1 | E1].
    {
      clear HAGd HSTd.
      (* ONE RUN to the drop place (the block with the preset tables) *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ => apply (DFX RX MX) end);
        [ cbv [LEN_ STORED TABLE BAD]; lia | split; [cbv [LEN_]; lia | reflexivity]
        | unfold s_regs_disp, s_fix, s_vars, reg_st; icx_cbn; zkeys; split_conj; zreg | assumption | assumption
        | intros _;
          lazymatch goal with HH : mem_u64 _ _ (p + 136) 21474836489 |- _ =>
            pose proof (mem_u32_eqmod _ _ 21474836489 9 ltac:(reflexivity) (mem_u64_lo32 _ _ _ _ HH)) as Hlb;
            pose proof (mem_u64_hi32 _ _ _ _ HH) as Hdb;
            change (Z.shiftr 21474836489 32) with 5 in Hdb; replace (p + 136 + 4) with (p + 140) in Hdb by lia
          end; split_conj; assumption
        | intros _; exact HAGf | discriminate ]. }
    clear HAGf HSTf.
    destruct (Z_lt_dec 1 ((hold1 / 2) mod 4)) as [L2 | L2].
    {
      (* ONE RUN to the test that tells the two block types left *)
      zto_branch Rfd.
      destruct (Z.eq_dec ((hold1 / 2) mod 4) 2) as [E2 | E2].
      -
        (* ONE RUN to the drop place *)
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ => apply (DTB RX MX) end);
          [ cbv [LEN_ STORED TABLE BAD]; lia | split; [discriminate | cbv [LEN_ TABLE]; lia]
          | unfold s_regs_disp, s_fix, s_vars, reg_st; icx_cbn; zkeys; split_conj; zreg | assumption | assumption | discriminate | discriminate | intros _; exact HAGd ].
      -
        (* ONE RUN to the drop place *)
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ => apply (DBD RX MX) end);
          [ cbv [LEN_ STORED TABLE BAD]; lia | split; [discriminate | cbv [LEN_ BAD]; lia]
          | unfold s_regs_disp, s_fix, s_vars, reg_st; icx_cbn; zkeys; split_conj; zreg | assumption | assumption | discriminate | discriminate | intros _; exact HAGd ]. }
    (* ONE RUN to the drop place *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ => apply (DST RX MX) end);
      [ cbv [LEN_ STORED TABLE BAD]; lia | split; [discriminate | cbv [LEN_ STORED]; lia]
      | unfold s_regs_disp, s_fix, s_vars, reg_st; icx_cbn; zkeys; split_conj; zreg | assumption | assumption | discriminate | discriminate | intros _; exact HAGd ]. }
  clear HAGf HSTf HAGd HSTd.
  destruct (Z_lt_dec 2 bits) as [Hb3 | Hb3].
  - (* ONE RUN from the case entry to the body's place *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ => apply (J RX cin hold bits) end);
      [ unfold s_regs_disp, s_fix, s_vars, reg_st; icx_cbn; zkeys; split_conj | .. ]; first [zreg | lia].
  - (* the hold is short of a block head *)
    destruct (Z.eq_dec (n - cin) 0) as [Hv0 | Hv0].
    +
      open_kmem KM0. destruct SAT as [Hmode SREST].
      (* the leave's continuation at this lemma's state, by a name *)
      pose proof (fun RX MX => KLL RX MX (IST mode 0 flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI0) as KLV.
      (* ONE RUN from the case entry to the leave place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ => eapply (KLV RX MX) end);
        [ unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg
        | exact STD | split; [exact Hmode | exact SREST] | exact SRET | exact SOUT | exact Hlens | exact Hcodes | exact HAG ].
    +
      pose proof (Hfin cin ltac:(lia)) as Hb0.
      pose proof (pullbyte_bound hold bits (fin cin) ltac:(lia) ltac:(lia) Hb0) as Hpb.
      (* the model's facts of the pulled byte, shifted, and of the bit count plus a byte: in hand before the run *)
      pose proof (mf_pull_byte (fin cin) bits ltac:(lia)) as HVp.
      pose proof (lor8_small bits ltac:(lia)) as HVb.
      (* the body's place with one more input byte in the hold, by a name *)
      pose proof (fun RX => J RX (cin + 1) (hold + fin cin * 2 ^ bits) (bits + 8)) as JN.
      (* ONE RUN from the case entry to the body's place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ => apply (JN RX) end);
        [ unfold s_regs_disp, s_fix, s_vars, reg_st; icx_cbn; zkeys; split_conj | .. ]; first [zreg | lia].
Qed.

End TYPEDO_CODE.

Theorem arm_TYPEDO_s {RCa1 : RunCtx}  : arm_stmt L_TYPEDO TYPEDO.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  eapply typedo_body; try eassumption. right; exact Hm.
Qed.

Theorem arm_TYPE_s {RCa1 : RunCtx}  : arm_stmt L_TYPE TYPE.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof KM as KM0. open_kmem KM. pose proof STD as STD0. open_std STD.
  pose proof CX as CX0. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  (* the frame's slots are opened ALL, before the run *)
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn. destr_conj FRM'.
  pose proof RE as RE0. unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  zkeysb. unfold L_TYPE, L_TYPEDO in *. pose proof two64_eq as TW64.
  (* ONE RUN to the entry of the block-type case *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RX ?LX) ?MX _) _ =>
    eapply (typedo_body (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 RX LX MX st lf cf CX0 Hh Hfin (or_introl Hm) SI) end).
  - unfold s_regs_arm, s_fix, s_vars; icx_cbn; zkeys; split_conj; zreg.
  - exact KM0.
  - exact K.
Qed.
