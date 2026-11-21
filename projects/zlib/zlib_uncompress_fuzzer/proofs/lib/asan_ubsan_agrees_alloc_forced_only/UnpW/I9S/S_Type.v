(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S Require Import SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fxG : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
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
Section FXG. Context {fxG : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
Definition L_TYPEDO_LAST : Z := 86944.  (* [comment removed for export] *)
Definition L_TYPEDO_BODY : Z := 87908.  (* [comment removed for export] *)
Definition L_TYPEDO_DROP : Z := 89492.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FXG. Context {fxG : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

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

(* [comment removed for export] *)
Lemma pullbyte_bound : forall h b c, 0 <= b -> 0 <= h < 2 ^ b -> 0 <= c < 256 ->
  0 <= h + c * 2 ^ b < 2 ^ (b + 8).
Proof.
  intros h b c Hb Hh Hc. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  assert (0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

(* [comment removed for export] *)
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

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fxG : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bytebits_st (st : ist) : ist :=
  IST CHECK (t_last st) (t_flags st) (t_cin st) (t_cout st)
      (Z.shiftr (t_hold st) (t_bits st mod 8)) (t_bits st - t_bits st mod 8) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

(* [comment removed for export] *)
Definition typedo_st (st : ist) (m cin1 hold1 bits1 : Z) (fx : bool) : ist :=
  IST m (Z.land hold1 1) (t_flags st) cin1 (t_cout st) (Z.shiftr hold1 3) (bits1 - 3) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st)
      (if fx then CLenfix else t_lc st) (if fx then CDistfix else t_dc st)
      (if fx then 9 else t_lb st) (if fx then 5 else t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_bytebits : forall cx st lf cf,
  sinv cx st lf cf -> (t_mode st = TYPE \/ t_mode st = TYPEDO) ->
  sinv cx (bytebits_st st) lf cf /\ meas cx (bytebits_st st) < meas cx st.
Proof.
  intros cx st lf cf (R & W & P & Mo) Hm.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode] in Hm.
  unfold RNG in R. icx_cbn. destr_conj R.
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
  intros cx st lf cf m cin1 hold1 bits1 fx (R & W & P & Mo) Hm Hc Hb Hh Hbc HW Hm' Hfx.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_cin t_bits] in Hm, Hc, HW. icx_cbn.
  unfold RNG in R. icx_cbn. destr_conj R.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mem_u32_eqmod : forall M a e e', e mod 4294967296 = e' mod 4294967296 ->
  mem_u32 R_segs M a e -> mem_u32 R_segs M a e'.
Proof.
  intros M a e e' E H. unfold mem_u32 in *.
  rewrite <- (Z_to_le_bytes_mod32 4 e) in H by lia. rewrite E, Z_to_le_bytes_mod32 in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma i_frame_flush5 : forall cx M, i_frame cx M -> mem_u64 R_segs M (c_u cx + -192) (-5).
Proof. intros cx M H. unfold i_frame in H. destr_conj H. assumption. Qed.

Section TYPEDO_CODE.

(* [comment removed for export] *)
Lemma typedo_drop : forall cx fin MD T M0 (B : Z) R M st' lf cf hold1 bits1,
  ctx_ok ROMHI_S cx -> m_halted MD = None ->
  sinv cx st' lf cf -> meas cx st' < B ->
  t_hold st' = Z.shiftr hold1 3 -> t_bits st' = bits1 - 3 -> 3 <= bits1 <= 40 -> 0 <= hold1 < two64 ->
  s_fix cx R [] ->
  zget R kS9 = c_n cx - t_cin st' -> zget R kS4 = c_ob cx + t_cout st' -> zget R kS3 = c_osz cx - t_cout st' ->
  zget R kS10 = c_q cx + t_cin st' -> zget R kS8 = hold1 -> zget R kS1 = bits1 -> zget R kS7 = t_out st' ->
  k_mem cx fin M0 st' lf cf M ->
  KDISP cx fin MD T M0 B ->
  realizes R_segs (zcfg R_segs L_TYPEDO_DROP (zupd R []) M MD) T.
Proof.
  intros cx fin MD T M0 B R M st' lf cf hold1 bits1 CX Hh SI MB Eh Eb Hb1 Hh1 FX E8 E3 E2 E11 E7 E0 E77 KM KD.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  unfold s_fix in FX. icx_cbn. destr_conj FX.
  zkeysb. unfold L_TYPEDO_DROP, L_DISP in *. zgetl_nil. pose proof two64_eq as TW64.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (Z.shiftr hold1 3) ltac:(rewrite (Z.mod_small hold1) by lia; reflexivity).
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (bits1 - 3) ltac:(symmetry; rewrite ?swrap32_small by lia; first [reflexivity | lia]).
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => eapply (KD R' Mx st' lf cf SI MB) end.
  - unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys. rewrite Eh, Eb. split_conj; zreg.
  - exact KM.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fp_typedo_f (p : Z) : list (Z * Z) := [(p + 8, 8); (p + 120, 24)].     (* [comment removed for export] *)
Definition fp_typedo_d (u p : Z) : list (Z * Z) := [(p + 8, 8); (u + 48, 8)].    (* [comment removed for export] *)

Lemma typedo_body : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  (t_mode st = TYPE \/ t_mode st = TYPEDO) -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_TYPEDO (zupd Rb l) M MD) T.
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
  (* [comment removed for export] *)
  assert (H12 : mem_u32 R_segs M (p + 12) last) by (unfold st_rest in SREST; icx_cbn; dand SREST as (H12 & _); exact H12).
  (* [comment removed for export] *)
  clear ROM Wob Ww CST HK Hmode SREST SRET SOUT Hlens Hcodes WIN_ MODE_. unfold i_frame in FRM; icx_cbn; dand FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR120 & FR128 & FR136 & FR144 & FR152 & _ & _ & _ & _ & _ & _ & _ & _). (* a worker 1.4: the frame slots the inflate_fixed reloads read *)
  zkeysb. unfold L_TYPEDO, L_TYPEDO_LAST, L_TYPEDO_BODY, L_TYPEDO_DROP, L_SETMODE, L_DISP, L_LEAVE_LD in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (mpostL_stable R_segs M (fp_typedo_f p) ltac:(unfold fp_typedo_f; ranges_ok_tac)) as HSTf.
  assert (HAGf : framed (fun X => mpostL R_segs M X (fp_typedo_f p)) M) by (apply mpostL_refl).
  pose proof (mpostL_stable R_segs M (fp_typedo_d u p) ltac:(unfold fp_typedo_d; ranges_ok_tac)) as HSTd.
  assert (HAGd : framed (fun X => mpostL R_segs M X (fp_typedo_d u p)) M) by (apply mpostL_refl).
  unfold fp_typedo_f, fp_typedo_d in HSTf, HAGf, HSTd, HAGd.
  tstep1 Rfd.                         (* [comment removed for export] *)
  destruct (Z.eq_dec last 0) as [Hl0 | Hl0].
  2: { (* [comment removed for export] *)
    pose proof (smod64_nz last ltac:(lia) Hl0) as Hnz.
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (bits mod 8) ltac:(symmetry; apply land7_mod; lia).
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (bits - bits mod 8) ltac:(symmetry; apply landm8; lia).
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (Z.shiftr hold (bits mod 8))
      ltac:(rewrite (Z.mod_small hold) by lia; rewrite (Z.mod_small (bits mod 8)) by (Z.to_euclidean_division_equations; lia); reflexivity).
    zstep Rfd.                        (* [comment removed for export] *)
    destruct (sinv_bytebits _ _ lf cf SI0 Hm) as [SI1 MB1].
    clear H12 HSTf HAGf HSTd HAGd. open_kmem KM0. destruct SAT as [Hmode SREST].
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KSM R' Mx (bytebits_st (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext))
                  mode lf cf SI1 MB1) end;
      [ unfold s_regs_d0, s_fix, s_vars, bytebits_st; icx_cbn; cbv [CHECK]; zkeys; split_conj; zreg
      | exact STD | exact Hmode | unfold bytebits_st; exact SREST
      | unfold s_ret, bytebits_st in *; icx_cbn; exact SRET | unfold s_out, bytebits_st in *; icx_cbn; exact SOUT | exact Hlens | exact Hcodes | exact HAG ]. }
  (* [comment removed for export] *)
  subst last. zbr Rfd false.          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (J : forall RJ cin1 hold1 bits1,
    zget RJ kSP = u + -240 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA0 = u -> zget RJ kA1 = 0 -> zget RJ kRA = p + 168 -> zget RJ kT6 = -16180 ->
    zget RJ kT4 = 30 -> zget RJ kT5 = 67008 -> zget RJ kS6 = 16209 ->
    zget RJ kS9 = n - cin1 -> zget RJ kS4 = ob + cout -> zget RJ kS3 = osz - cout ->
    zget RJ kS10 = q + cin1 -> zget RJ kS8 = hold1 -> zget RJ kS1 = bits1 -> zget RJ kS7 = out ->
    cin <= cin1 <= n -> 3 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (n - cin1) + bits1 = 8 * (n - cin) + bits ->
    realizes R_segs (zcfg R_segs 87908 (zupd RJ []) M MD) T).
  { intros RJ cin1 hold1 bits1. intros. zkeys. clear H12 Hin.
    pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh1.
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg ((hold1 / 2) mod 4) ltac:(symmetry; apply bits2_of_shift; lia).
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (DROP : forall RD Mq m fx,
      (m = STORED \/ m = TABLE \/ m = BAD \/ m = LEN_) -> (fx = true <-> m = LEN_) ->
      zget RD kSP = u + -240 -> zget RD kGP = K0 kGP -> zget RD kTP = K0 kTP -> zget RD kS0 = p ->
      zget RD kA0 = u -> zget RD kA1 = 0 -> zget RD kRA = p + 168 -> zget RD kT6 = -16180 ->
      zget RD kT4 = 30 -> zget RD kT5 = 67008 -> zget RD kS6 = 16209 ->
      zget RD kS9 = n - cin1 -> zget RD kS4 = ob + cout -> zget RD kS3 = osz - cout ->
      zget RD kS10 = q + cin1 -> zget RD kS8 = hold1 -> zget RD kS1 = bits1 -> zget RD kS7 = out ->
      mem_u32 R_segs Mq (p + 8) m -> mem_u32 R_segs Mq (p + 12) (Z.land hold1 1) ->
      (fx = true -> mem_u64 R_segs Mq (p + 120) 67422 /\ mem_u64 R_segs Mq (p + 128) 69470 /\
                    mem_u32 R_segs Mq (p + 136) 9 /\ mem_u32 R_segs Mq (p + 140) 5) ->
      (fx = true -> mpostL R_segs M Mq [(p + 8, 8); (p + 120, 24)]) -> (fx = false -> mpostL R_segs M Mq [(p + 8, 8); (u + 48, 8)]) ->
      realizes R_segs (zcfg R_segs 89492 (zupd RD []) Mq MD) T).
    { intros RD Mq m fx Hm1 Hfx E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E16 E17 E18 E19 Mm Ml HT HPa HPb.
      destruct (sinv_typedo (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST mode 0 flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  lf cf m cin1 hold1 bits1 fx SI0 Hm ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) Hm1 Hfx) as [SI1 MB1].
      (* [comment removed for export] *)
      clear HAGf HSTf HAGd HSTd HST HAG Wstk Wp.
      open_kmem KM0. open_std STD. destruct SAT as [Hmode SREST]. clear Hmode.
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
        | unfold s_fix; icx_cbn; zkeys; split_conj; assumption
        | assumption | assumption | assumption | assumption | assumption | assumption | assumption
        | unfold k_mem; split_conj;
          [ close_std
          | unfold st_at, st_rest, typedo_st; icx_cbn; cbv [cp_addr LENFIX_ADDR DISTFIX_ADDR o_codes]; icx_cbn; split_conj; assumption
          | unfold s_ret, typedo_st in *; icx_cbn; assumption
          | unfold s_out; exact I
          | assumption | assumption | exact HAG ]
        | exact KD ]. }
    (* [comment removed for export] *)
    assert (Hc4 : 0 <= (hold1 / 2) mod 4 < 4) by (Z.to_euclidean_division_equations; lia).
    Local Ltac drop_apply DROP m fx :=
      lazymatch goal with HPq : framed _ ?Mx |- realizes _ (zcfg _ _ ?RD ?Mx _) _ => apply (DROP RD Mx m fx) end.
    destruct (Z.eq_dec ((hold1 / 2) mod 4) 1) as [E1 | E1].
    { (* [comment removed for export] *)
      clear HAGd HSTd.
      zbr Rfd false.                  (* [comment removed for export] *)
      zbr Rfd true.                   (* [comment removed for export] *)
      (* a worker 1.4: TYPE's fixed path CALLS inflate_fixed (0x17c90) instead of inlining fixedtables *)
      zstep Rfd. zstep Rfd.                       (* U: mv a0,s0; jal inflate_fixed *)
      zstep Rfd. zstep Rfd. zstep Rfd.            (* auipc a1; li a2,5; auipc a3 *)
      zstep Rfd. zlit.                            (* addi a1: lenfix *)
      zstep Rfd. zlit.                            (* slli a2,a2,32 *)
      zstep Rfd. zlit.                            (* addi a3: distfix *)
      zstep Rfd. zlit.                            (* addi a2,a2,9 *)
      tstep1 Rfd. tstep1 Rfd. tstep1 Rfd.         (* sd a1,120(a0); sd a3,128(a0); sd a2,136(a0) *)
      zstep Rfd.                                  (* ret *)
      tstep1 Rfd. zstep Rfd. tstep1 Rfd. tstep1 Rfd. (* U: ld t5,104(sp); li t4,30; ld t6,96(sp); ld ra,88(sp) *)
      tstep1 Rfd. tstep1 Rfd.                     (* U: ld a1,112(sp); ld a0,120(sp) *)
      zstep Rfd. zstep Rfd.                       (* addi a2,s4,-10; li a3,6 *)
      tstep1 Rfd.                                 (* sw a2,8(s0) *)
      zbr Rfd true.                               (* bne a1,a3 *)
      lazymatch goal with H120 : mem_u64 _ ?Mx (p + 136) 21474836489 |- realizes _ (zcfg _ _ ?RD ?Mx _) _ =>
        pose proof (mem_u32_eqmod _ _ 21474836489 9 ltac:(reflexivity) (mem_u64_lo32 _ _ _ _ H120)) as Hlb;
        pose proof (mem_u64_hi32 _ _ _ _ H120) as Hdb;
        change (Z.shiftr 21474836489 32) with 5 in Hdb; replace (p + 136 + 4) with (p + 140) in Hdb by lia;
        apply (DROP RD Mx LEN_ true) end;
        [ cbv [LEN_ STORED TABLE BAD]; lia | split; [cbv [LEN_]; lia | reflexivity]
        | zreg .. | assumption | assumption | intros _; split_conj; assumption | intros _; exact HAGf | discriminate ]. }
    clear HAGf HSTf.
    destruct (Z_lt_dec 1 ((hold1 / 2) mod 4)) as [L2 | L2].
    { (* [comment removed for export] *)
      zbr Rfd true.                   (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      destruct (Z.eq_dec ((hold1 / 2) mod 4) 2) as [E2 | E2].
      - (* [comment removed for export] *)
        zbr Rfd false.                (* [comment removed for export] *)
        zstep Rfd. zstep Rfd. zlit.   (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        tstep1 Rfd.                   (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?RD ?Mx _) _ => apply (DROP RD Mx TABLE false) end;
          [ cbv [LEN_ STORED TABLE BAD]; lia | split; [discriminate | cbv [LEN_ TABLE]; lia]
          | zreg .. | assumption | assumption | discriminate | discriminate | intros _; exact HAGd ].
      - (* [comment removed for export] *)
        zbr Rfd true.                 (* [comment removed for export] *)
        zstep Rfd. zstep Rfd. zlit.   (* [comment removed for export] *)
        tstep1 Rfd.                   (* [comment removed for export] *)
        zstep Rfd. zstep Rfd. zlit.   (* [comment removed for export] *)
        tstep1 Rfd.                   (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?RD ?Mx _) _ => apply (DROP RD Mx BAD false) end;
          [ cbv [LEN_ STORED TABLE BAD]; lia | split; [discriminate | cbv [LEN_ BAD]; lia]
          | zreg .. | assumption | assumption | discriminate | discriminate | intros _; exact HAGd ]. }
    (* [comment removed for export] *)
    zbr Rfd false.                    (* [comment removed for export] *)
    zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd. zstep Rfd. zlit.       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?RD ?Mx _) _ => apply (DROP RD Mx STORED false) end;
      [ cbv [LEN_ STORED TABLE BAD]; lia | split; [discriminate | cbv [LEN_ STORED]; lia]
      | zreg .. | assumption | assumption | discriminate | discriminate | intros _; exact HAGd ]. }
  (* [comment removed for export] *)
  clear HAGf HSTf HAGd HSTd.
  destruct (Z_lt_dec 2 bits) as [Hb3 | Hb3].
  - zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?RJ _ _) _ => apply (J RJ cin hold bits) end; first [zreg | lia].
  - zbr Rfd false.                    (* [comment removed for export] *)
    destruct (Z.eq_dec (n - cin) 0) as [Hv0 | Hv0].
    + (* [comment removed for export] *)
      zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      clear H12. open_kmem KM0. destruct SAT as [Hmode SREST].
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
        eapply (KLL R' Mx (IST mode 0 flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI0) end;
        [ unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg
        | exact STD | split; [exact Hmode | exact SREST] | exact SRET | exact SOUT | exact Hlens | exact Hcodes | exact HAG ].
    + (* [comment removed for export] *)
      zbr Rfd true.                   (* [comment removed for export] *)
      pose proof (Hfin cin ltac:(lia)) as Hb0.
      tstep1 Rfd.                     (* [comment removed for export] *)
      tstep1 Rfd.                     (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (fin cin * 2 ^ bits) ltac:(rewrite (Z.mod_small bits) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (bits + 8) ltac:(symmetry; apply lor8_small; lia).
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      pose proof (pullbyte_bound hold bits (fin cin) ltac:(lia) ltac:(lia) Hb0) as Hpb.
      lazymatch goal with |- realizes _ (zcfg _ _ ?RJ _ _) _ => apply (J RJ (cin + 1) (hold + fin cin * 2 ^ bits) (bits + 8)) end;
        first [zreg | lia].
Qed.

End TYPEDO_CODE.

Theorem arm_TYPEDO_s : arm_stmt L_TYPEDO TYPEDO.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  eapply typedo_body; try eassumption. right; exact Hm.
Qed.

Theorem arm_TYPE_s : arm_stmt L_TYPE TYPE.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof KM as KM0. open_kmem KM. pose proof STD as STD0. open_std STD.
  pose proof (i_frame_flush5 _ _ FRM) as F48.
  pose proof CX as CX0. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  pose proof RE as RE0. unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  zkeysb. unfold L_TYPE, L_TYPEDO in *. pose proof two64_eq as TW64.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
    eapply (typedo_body (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx st lf cf CX0 Hh Hfin (or_introl Hm) SI) end.
  - unfold s_regs_arm, s_fix, s_vars; icx_cbn; zkeys; split_conj; zreg.
  - exact KM0.
  - exact K.
Qed.
End FXG.
