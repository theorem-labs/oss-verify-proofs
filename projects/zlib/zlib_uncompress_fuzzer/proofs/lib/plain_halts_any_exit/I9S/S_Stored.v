(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* THE WALK's STORED-BLOCK TEXT IN THE RUN FORM AND THE LIST FORM (the sturdy track; made
   from the hand text of that name). EVERY STRETCH OF STEP LINES IS A RUN OF THE STURDY DRIVER, with the hand
   text's value replacements handed to the runs as HINTS. THERE ARE NO INLINE REGISTER FACTS: the text's six own
   labels, three register maps of the loop lemma, the register map at the callee's call and one KEEP LIST come
   from the image's LAYOUT TEXT; the asserted statements at the walk's own places are register maps that the
   walk's base text already has, taken at a state that the statement binds. No register and no pc is named in
   this text; the same bytes serve every image that has a layout text. *)
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

Module S_StoredA.
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

(* THE TEXT's SIX OWN LABELS ARE FIELDS OF THE IMAGE's LAYOUT TEXT; here they have their short names only *)
Local Notation L_STORED_LOOP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_STORED_LOOP (only parsing).
Local Notation L_STORED_BODY := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_STORED_BODY (only parsing).
Local Notation L_STORED_BAD := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_STORED_BAD (only parsing).
Local Notation L_COPY_MEMCPY := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_COPY_MEMCPY (only parsing).
Local Notation L_COPY_DONE := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_COPY_DONE (only parsing).
Local Notation L_MEMCPY_RET := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_MEMCPY_RET (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation rkeeps := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps (only parsing).
Local Notation qval := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval (only parsing).

Ltac mode_consts :=
  cbv [reach codes_liveP HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.
Ltac mode_solve Mf tac :=
  split_conj;
  first [ right; lia_std
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
(* THREE HINT LEMMAS (each is the equation that a value replacement of the hand text proved in place: machine
   form = nicer form; a run's hint names the lemma) *)
Lemma shl_mod_small : forall a j b, 0 <= j < b -> Z.shiftl a (j mod b) = a * 2 ^ j.
Proof.
  intros a j b [Hj0 Hj1]. rewrite (Z.mod_small j b) by (split; assumption).
  apply Z.shiftl_mul_pow2. exact Hj0.
Qed.

Lemma shr_mod_small : forall h s b1 b2, 0 <= h < b1 -> 0 <= s < b2 -> Z.shiftr (h mod b1) (s mod b2) = Z.shiftr h s.
Proof.
  intros h s b1 b2 Hh Hs. rewrite (Z.mod_small h b1) by exact Hh. rewrite (Z.mod_small s b2) by exact Hs.
  reflexivity.
Qed.

Lemma mod_u64_id : forall h, 0 <= h < 18446744073709551616 -> h mod 18446744073709551616 = h.
Proof. intros h Hh. apply Z.mod_small. exact Hh. Qed.

Lemma zext32_id : forall x, 0 <= x < 4294967296 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 32 = x.
Proof. intros. apply zext32_shift. assumption. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition set_st (st : ist) (m cin cout hold bits len : Z) : ist :=
  IST m (t_last st) (t_flags st) cin cout hold bits (t_out st) (t_ret st)
      len (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

(* OPENERS OF THE LIST FORM (they only unfold, split and name): every list-form hypothesis: the meaning over
   the layout's lists is unfolded, the conjunction split and its parts named; the same for a goal *)
Ltac open_lists :=
  repeat match goal with
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_copy_memcpy OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_stored_loop
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_stored_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_stored_dn] in H;
             unfold set_st in H; icx_cbn; destr_conj H
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_stored_loop] in H; destr_conj H
         end.
Ltac split_lists :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_copy_memcpy OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_stored_loop
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_stored_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_stored_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_stored_loop];
  unfold set_st; icx_cbn; split_conj.

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
Context {RCa1 : RunCtx}.
Hypothesis MEMCPY : memcpy_spec_s.

Lemma copy_body : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = COPY -> t_length st < 65536 -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_COPY (zupd Rb l) M MD) T.
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
  assert (H92 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 108) length) by (unfold st_rest in SREST; icx_cbn; destr_conj SREST; assumption).
  (* the frame's slots are opened ALL (the hand text took three of them by their position in the frame) *)
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn. destr_conj FRM'.
  (* the return slot's fact is opened too *)
  pose proof SRET as SRETu. unfold s_ret in SRETu. icx_cbn.
  zkeysb. unfold L_COPY, L_COPY_MEMCPY, L_COPY_DONE, L_MEMCPY_RET, L_RELOAD, L_DISP, L_LEAVE, L_LEAVE_LD, L_SETMODE in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  (* ONE RUN to the test of the length *)
  zto_branch Rfd.
  destruct (Z.eq_dec length 0) as [HL0 | HL0].
  { (* the length is 0 *)
    subst length.
    pose proof (sinv_set _ _ lf cf TYPE cin cout hold bits 0 SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(cbv [COPY_ COPY TYPE]; lia)
                  ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
    pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST COPY last flags cin cout hold bits out ret 0 offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  TYPE cin cout hold bits 0 ltac:(right; split; [unfold Wm; cbn; lia | vm_compute; reflexivity])) as MB1.
    (* THE RUN ENDS AT THE DISPATCH, and the dispatch's continuation is applied at the memory after the mode's
       store. *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KD R' Mx _ lf cf SI1 MB1) end).
    - unfold s_regs_disp, s_fix, s_vars, set_st; icx_cbn; cbv [TYPE]; zkeys; split_conj; zreg.
    - unfold k_mem, set_st; icx_cbn; split_conj;
        first [ close_std
              | (unfold st_at; icx_cbn; split; [ assumption | exact SREST ])
              | exact SRET | first [ assumption | (unfold s_out; exact I) ] | (unfold s_out; exact I)
              | exact Hlens | exact Hcodes | exact HAG ]. }
  pose proof (smod64_nz length ltac:(lia) HL0) as Hnz.
  (* (the length test's branch is the first instruction of the next run below) *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?M1 _) _ =>
  (* JL: the leave place: ITS REGISTER FACTS ARE THE WALK BASE TEXT's OWN MAP OF THAT PLACE at this lemma's
     state. JM: the callee's call: its register map is the layout's list; `copy` is the value the statement
     binds. *)
  (* JL STANDS AT THE LEAVE PLACE, with the base text's own register map of that place and the state's return
     value *)
  assert (JL : forall RJ,
    s_regs_leave (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST COPY last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret RJ [] ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE (zupd RJ []) M1 MD) T);
  [| assert (JM : forall RJ copy,
    rholds (qval (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
              (Some (IST COPY last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) copy)
      RJ [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_copy_memcpy ->
    1 <= copy -> copy <= length -> copy <= n - cin -> copy <= osz - cout ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_COPY_MEMCPY (zupd RJ []) M1 MD) T) ] end.
  { (* JL *)
    intros RJ RJH.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KL R' Mx (IST COPY last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf SI0) end.
    (* the premises of the leave place's continuation, each closed BY ITS FORM (their count is the base text's) *)
    all: first [ exact RJH
               | (unfold s_regs_leave in RJH |- *; icx_cbn; destr_conj RJH; zgetl_nil; zkeys; split_conj; zreg)
               | close_std
               | (split; [exact Hmode | exact SREST])
               | exact SRET
               | exact Hlens | exact Hcodes | exact HAG
               | assumption | (unfold s_out; exact I) ]. }
  { (* JM *)
    intros RJ copy RJH. intros. open_lists. zgetl_nil. cbv [JTAB_ADDR] in *.
    cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_COPY_MEMCPY]. zkeys.
    pose proof (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 1 _ q n fin cin copy Hin ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc.
    apply mem_arr8_mem_is in Hsrc.
    (* ONE RUN to the callee's call, with ONE VALUE HINT (the copy count's sign extension is the identity) *)
    zuntil_h Rfd (first [ zhint zext32_id ])
      (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R ?lc') ?Mx _) _ =>
         eapply (MEMCPY R lc' Mx MD T (ob + cout) (q + 1 * cin) _ copy _ Hh) end).
    - zreg. - zreg. - zreg. - zreg. - reflexivity.
    - exact Hsrc.
    - rewrite length_map, zseq_length. lia.
    - eapply mem_wr_sub; [exact Wob | lia | lia].
    - lia. - lia. - lia. - lia. - zlia.
    - intros M2 R2 HP HD HS HW E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
      zimps. clear HD HS Hsrc. apply mpost_mpostL1 in HP. zreattachL HP.
      (* the state's facts are opened before the run (the hand text opens them beside the store that writes
         one of them) *)
      unfold st_rest in SREST. icx_cbn.
      dand SREST as (C12 & C24 & C64 & C68 & _ & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
      pose proof (sinv_set _ _ lf cf COPY (cin + copy) (cout + copy) hold bits (length - copy) SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(intros _; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST COPY last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    COPY (cin + copy) (cout + copy) hold bits (length - copy) ltac:(left; unfold Wm; cbn; lia)) as MB1.
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
        eapply (KRL R' Mx _ lf cf SI1 MB1) end).
      + unfold s_regs_reload, set_st; icx_cbn; zkeys; split_conj; try zreg; try (intros _; zreg); try (intros C; discriminate C).
      + unfold k_mem, set_st; icx_cbn; split_conj;
          [ close_std
          | unfold st_at, st_rest; icx_cbn; split_conj; assumption
          | exact SRET | first [ assumption | (unfold s_out; exact I) ] | exact Hlens | exact Hcodes | exact HAG ]. }
  (* THE CASE TREE: each `zto_branch` takes the branch that the case split above it decided and stops at the
     next open test; each leaf is one run to a join point *)
  zto_branch Rfd.
  destruct (Z_lt_dec length (n - cin)) as [C1 | C1].
  - zto_branch Rfd.
    destruct (Z_lt_dec length (osz - cout)) as [C2 | C2].
    + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JM R' length) end); [ split_lists | .. ]; first [zreg | lia].
    + zto_branch Rfd.
      destruct (Z.eq_dec (osz - cout) 0) as [C3 | C3].
      * zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JL R') end); unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
      * zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JM R' (osz - cout)) end); [ split_lists | .. ]; first [zreg | lia].
  - zto_branch Rfd.
    destruct (Z_lt_dec (n - cin) (osz - cout)) as [C2 | C2].
    + zto_branch Rfd.
      destruct (Z.eq_dec (n - cin) 0) as [C3 | C3].
      * zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JL R') end); unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
      * zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JM R' (n - cin)) end); [ split_lists | .. ]; first [zreg | lia].
    + zto_branch Rfd.
      destruct (Z.eq_dec (osz - cout) 0) as [C3 | C3].
      * zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JL R') end); unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
      * zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (JM R' (osz - cout)) end); [ split_lists | .. ]; first [zreg | lia].
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
  pose proof (sinv_set _ _ lf cf COPY cin cout hold bits length SI Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(intros _; exact HL16)
                ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
  pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                (IST COPY_ last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                COPY cin cout hold bits length ltac:(right; split; [unfold Wm; cbn; lia | vm_compute; reflexivity])) as MB1.
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
    eapply (copy_body (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
              (set_st (IST COPY_ last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY cin cout hold bits length)
              lf cf CX0 Hh Hfin eq_refl ltac:(cbn; exact HL16) SI1) end).
  - unfold s_regs_arm, s_fix, s_vars, set_st; icx_cbn; zkeys; split_conj; zreg.
  - unfold k_mem, set_st; icx_cbn; split_conj;
      [ close_std | split; [assumption | exact SREST] | exact SRET | first [ assumption | (unfold s_out; exact I) ] | exact Hlens | exact Hcodes | exact HAG ].
  - eapply KALL_mono; [| exact K]. lia.
Qed.

End WITH_MEMCPY.
End S_StoredA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import SBase. Import S_StoredA.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* the text's own labels and the list form's meaning words, by their short names (as in the first part) *)
Local Notation L_STORED_LOOP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_STORED_LOOP (only parsing).
Local Notation L_STORED_BODY := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_STORED_BODY (only parsing).
Local Notation L_STORED_BAD := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_STORED_BAD (only parsing).
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation rkeeps := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps (only parsing).
Local Notation qval := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval (only parsing).

Section WITH_MEMCPY.
Context {RCa1 : RunCtx}.
Hypothesis MEMCPY : memcpy_spec_s.

(* THE LOOP LEMMA, IN THE LIST FORM. `st0` is a model state; the lemma speaks of `st0` with its input count,
   hold and bit count set to the values it binds. The loop's head, its leave and its body's continuation
   each have a register map in the layout; the registers that the loop leaves alone are the layout's KEEP
   LIST. No register and no pc is named. *)
Lemma stored_loop : forall (k : nat) cx fin MD T Rb l M (st0 : ist) (cin0' cinj holdj j : Z),
  let cx' := cx in
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_S cx ->
  j = 32 - 8 * Z.of_nat k -> (1 <= k <= 4)%nat ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  rholds (qval cx (Some (set_st st0 (t_mode st0) cinj (t_cout st0) holdj j (t_length st0))) 0)
    Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_stored_loop ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_q cx) (c_n cx) fin ->
  (forall R' hold',   (* the leave: no input left *)
     rholds (qval cx (Some (set_st st0 (t_mode st0) (c_n cx) (t_cout st0) hold' (j + 8 * (c_n cx - cinj)) (t_length st0))) 0)
       R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_stored_lv ->
     0 <= hold' < 2 ^ (j + 8 * (c_n cx - cinj)) -> c_n cx - cinj < Z.of_nat k ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_stored_loop ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_A4 (zupd R' []) M MD) T) ->
  (forall R' hold',   (* the body: 32 bits in hand *)
     rholds (qval cx (Some (set_st st0 (t_mode st0) (cinj + Z.of_nat k) (t_cout st0) hold' 32 (t_length st0))) 0)
       R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_stored_dn ->
     0 <= hold' < 2 ^ 32 -> Z.of_nat k <= c_n cx - cinj ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_stored_loop ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_STORED_BODY (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_STORED_LOOP (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M st0 cin0' cinj holdj j cx' Hh Hfin CXl Hj Hk Hc Hhj Hjc RH Hin KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. subst cx'.
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S] in CXl; destr_conj CXl.
  open_lists.
  zkeysb. unfold L_STORED_LOOP, L_STORED_BODY, L_LEAVE_A4 in *. pose proof two64_eq as TW64.
  assert (Hj32 : 2 ^ j <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 32) with 4294967296 in Hj32.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  - (* no input left: ONE RUN to the leave *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj) end);
      [ split_lists | | | split_lists ]; try zreg; try lia.
    + replace (j + 8 * (n - cinj)) with j by lia. lia.
  - pose proof (Hfin cinj ltac:(lia)) as Hb0.
    pose proof (pullbyte_bound holdj j (fin cinj) ltac:(lia) Hhj Hb0) as Hpb.
    (* ONE RUN through the loop's body to its exit test, with ONE VALUE HINT (the pulled byte, shifted) *)
    zto_branch_h Rfd (first [ zhint shl_mod_small ]).
    destruct k as [|k'].
    + (* the last round: ONE RUN to the body's continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KDN R' (fin cinj * 2 ^ j + holdj)) end);
        [ split_lists | | | split_lists ]; try zreg; try lia.
      replace 32 with (j + 8) by lia. lia.
    + (* THE BACK EDGE: ONE RUN back to the loop's head, where the induction hypothesis applies *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') _ _) _ =>
        eapply (IH (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' M st0 cin0' (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) Hh Hfin) end);
        [ unfold ctx_lin; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S]; split_conj; assumption || lia
        | lia | lia | icx_cbn; lia | lia | icx_cbn; lia
        | split_lists; zreg | exact Hin | | ].
      * (* the inner leave gives the outer leave: the same place, the model values re-said *)
        intros R' hold' RH' Hb' Hlt' KP'. icx_cbn. eapply (KLV R' hold').
        -- open_lists; zgetl_nil; split_lists; cbv beta iota delta [zget_l alookup];
             first [ assumption | (etransitivity; [ eassumption | lia ]) ].
        -- replace (j + 8 * (n - cinj)) with (j + 8 + 8 * (n - (cinj + 1))) by lia; assumption.
        -- lia.
        -- first [ exact KP' | (open_lists; split_lists; zkept) ].
      * intros R' hold' RH' Hb' Hle' KP'. icx_cbn. eapply (KDN R' hold').
        -- open_lists; zgetl_nil; split_lists; cbv beta iota delta [zget_l alookup];
             first [ assumption | (etransitivity; [ eassumption | lia ]) ].
        -- assumption.
        -- lia.
        -- first [ exact KP' | (open_lists; split_lists; zkept) ].
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
  (* ONE RUN to the test of the bit count, with TWO VALUE HINTS (the bits below a byte; the hold shifted) *)
  zto_branch_h Rfd (first
    [ zhint land7_mod
    | zhint_by shr_mod_small ltac:(first [ lia | Z.to_euclidean_division_equations; lia ]) ]).
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  (* BODY: the body's place: ITS REGISTER FACTS ARE THE WALK BASE TEXT's OWN MAP OF AN ARM's ENTRY, at the
     state with the input count, the hold and the bit count that the statement binds *)
  assert (BODY : forall RJ cin1 hold1 bits1,
    s_regs_arm (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (set_st (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
         STORED cin1 cout hold1 bits1 length) RJ [] ->
    cin <= cin1 <= n -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (n - cin1) + bits1 = 8 * (n - cin) + (bits - bits mod 8) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_STORED_BODY (zupd RJ []) Mc MD) T) end.
  { intros RJ cin1 hold1 bits1 RJH. intros.
    unfold s_regs_arm, s_fix, s_vars, set_st in RJH. icx_cbn. destr_conj RJH. zgetl_nil.
    cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_STORED_BODY]. cbv [JTAB_ADDR] in *. zkeys.
    pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh1.
    (* ONE RUN to the test of the stored length's check, with TWO VALUE HINTS (the low half; the two halves
       combined) *)
    zto_branch_h Rfd (first [ zhint low16_of_shift | zhint mod_u64_id ]).
    assert (Hx : 0 <= Z.lxor (Z.shiftr hold1 16) (hold1 mod 65536) < 18446744073709551616).
    { change 18446744073709551616 with (2 ^ 64). apply lxor_bound.
      - pose proof (shiftr_lt_pow2 hold1 bits1 16 ltac:(lia) ltac:(assumption)) as X.
        assert (2 ^ (bits1 - 16) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
      - Z.to_euclidean_division_equations; lia. }
    assert (Hm16 : 0 <= hold1 mod 65536 < 65536) by (Z.to_euclidean_division_equations; lia).
    destruct (Z.eq_dec (Z.lxor (Z.shiftr hold1 16) (hold1 mod 65536)) 65535) as [EQ | NE].
    -
      rewrite EQ.
      unfold st_rest in SREST. icx_cbn.
      dand SREST as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
      pose proof (sinv_set _ _ lf cf COPY_ cin1 cout 0 0 (hold1 mod 65536) SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(intros _; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    COPY_ cin1 cout 0 0 (hold1 mod 65536) ltac:(left; unfold Wm; cbn; lia)) as MB1.
      (* ONE RUN to the copy arm's entry *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
        eapply (arm_COPY__s MEMCPY (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                  (set_st (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY_ cin1 cout 0 0 (hold1 mod 65536))
                  lf cf CX0 Hh Hfin eq_refl SI1) end).
      + unfold s_regs_arm, s_fix, s_vars, set_st; icx_cbn; zkeys; split_conj; zreg.
      + unfold k_mem, set_st; icx_cbn; split_conj;
          [ close_std | unfold st_at, st_rest; icx_cbn; split_conj; assumption | exact SRET | first [ assumption | (unfold s_out; exact I) ] | exact Hlens | exact Hcodes | exact HAG ].
      + eapply KALL_mono; [| exact KA0]. lia.
    - (* the check fails: ONE RUN to the error place *)
      assert (Hne : Z.lxor (Z.shiftr hold1 16) (hold1 mod 65536) mod 18446744073709551616 <> 65535) by (rewrite Z.mod_small by lia; exact NE).
      pose proof (sinv_set _ _ lf cf BAD cin1 cout hold1 bits1 length SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(cbv [COPY_ COPY BAD]; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    BAD cin1 cout hold1 bits1 length ltac:(right; split; [unfold Wm; cbn; lia | vm_compute; reflexivity])) as MB1.
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
        eapply (KB10 R' Mx (set_st (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                               STORED cin1 cout hold1 bits1 length) lf cf) end).
      + unfold bad_of, set_st; cbn. exact SI1.
      + unfold bad_of, set_st; cbn. unfold set_st in MB1; cbn in MB1. exact MB1.
      + unfold s_regs_d10, s_fix, s_vars, set_st; icx_cbn; zkeys; split_conj; zreg.
      + zreg.
      + unfold k_mem, set_st; icx_cbn; split_conj;
          [ close_std | split; [exact Hmode | exact SREST] | exact SRET | first [ assumption | (unfold s_out; exact I) ] | exact Hlens | exact Hcodes | exact HAG ]. }
  destruct (Z_lt_dec 31 bits) as [Hb32 | Hb32].
  - (* enough bits in hand: ONE RUN to the body, with ONE VALUE HINT (the bit count rounded down to a byte) *)
    assert (Hmono : 2 ^ (bits - bits mod 8) <= 2 ^ bits) by (apply Z.pow_le_mono_r; lia).
    zuntil_h Rfd (first [ zhint landm8 ])
      (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (BODY R' cin (Z.shiftr hold (bits mod 8)) (bits - bits mod 8)) end);
      [ unfold s_regs_arm, s_fix, s_vars, set_st; icx_cbn; cbv [JTAB_ADDR]; zkeys; split_conj | .. ];
      first [zreg | lia | Z.to_euclidean_division_equations; lia].
  - (* not enough bits: ONE RUN to the loop's head, with ONE VALUE HINT (the same value by another mask) *)
    assert (Hkk : exists k : nat, bits - bits mod 8 = 32 - 8 * Z.of_nat k /\ (1 <= k <= 4)%nat).
    { exists (Z.to_nat (4 - bits / 8)). rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    zuntil_h Rfd (first [ zhint land24 ])
      (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
         eapply (stored_loop k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' Mx
                   (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                   cin0 cin (Z.shiftr hold (bits mod 8)) (bits - bits mod 8) Hh Hfin CXl Hk1 Hk2) end);
      [ icx_cbn; lia | exact Hsh | lia | split_lists; zreg | exact Hin | | ].
    + (* the loop's leave: ONE RUN to the leave place *)
      intros R' hold' RH' Hb' Hlt' KP'. icx_cbn. open_lists. zgetl_nil. zimps. zkeys. unfold L_LEAVE_A4, L_LEAVE_LD in *.
      pose proof (sinv_set _ _ lf cf STORED n cout hold' (bits - bits mod 8 + 8 * (n - cin)) length SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(cbv [COPY_ COPY STORED]; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      (* this run too ends AT THE LEAVE PLACE; the return slot's fact is opened here; the premises of the leave
         place's continuation are closed each BY ITS FORM *)
      pose proof SRET as SRETu. unfold s_ret in SRETu. icx_cbn. unfold L_LEAVE in *.
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KL Rx Mx _ ret lf cf SI1) end).
      all: first
        [ (lazymatch goal with |- s_regs_leave _ _ _ _ _ => idtac end;
           unfold s_regs_leave, set_st; icx_cbn; zkeys; split_conj; first [ zreg | zkept ])
        | close_std
        | (unfold set_st; split; [exact Hmode | exact SREST])
        | exact SRET | exact Hlens | exact Hcodes | exact HAG
        | assumption | (unfold s_out; exact I) ].
    + (* the loop's body continuation: the body's statement applies as it stands *)
      intros R' hold' RH' Hb' Hle' KP'. icx_cbn. open_lists. zgetl_nil. zimps. zkeys.
      apply (BODY R' (cin + Z.of_nat k) hold' 32);
        [ unfold s_regs_arm, s_fix, s_vars, set_st; icx_cbn; cbv [JTAB_ADDR]; zkeys; split_conj;
          cbv beta iota delta [zget_l alookup] | .. ];
        try zkept; try lia.
Qed.

End WITH_MEMCPY.
