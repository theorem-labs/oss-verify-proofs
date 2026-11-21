(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK Require IConj.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require U7LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U Require TBase T_Tok.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S Require S_Type.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S Require S_StoredA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S Require S_Stored.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S Require S_HeadA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S Require S_Head.

Module T_Type.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S.S_Type.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_TYPEDO_BODY_T : Z := 88352.
Definition L_TYPEDO_DROP_T : Z := 90484.

Lemma mem_u32_eqmod_t {RCa1 : RunCtx}  : forall M a e e', e mod 4294967296 = e' mod 4294967296 ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a e -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a e'.
Proof.
  intros M a e e' E H. unfold mem_u32 in *.
  rewrite <- (Z_to_le_bytes_mod32 4 e) in H by lia. rewrite E, Z_to_le_bytes_mod32 in H by lia. exact H.
Qed.

Section TYPEDO_CODE.
Context {RCa1 : RunCtx}.

Lemma typedo_drop_t : forall cx fin MD T M0 (B : Z) R M st' lf cf hold1 bits1,
  ctx_ok ROMHI_T cx -> m_halted MD = None ->
  sinv cx st' lf cf -> meas cx st' < B ->
  t_hold st' = Z.shiftr hold1 3 -> t_bits st' = bits1 - 3 -> 3 <= bits1 <= 40 -> 0 <= hold1 < two64 ->
  zget R kSP = c_u cx + -256 -> zget R kGP = c_K cx kGP -> zget R kTP = c_K cx kTP -> zget R kS0 = c_p cx ->
  zget R kA3 = c_u cx -> zget R kS2 = c_u cx -> zget R kA1 = 0 -> zget R kRA = 16209 ->
  zget R kS10 = c_q cx + t_cin st' -> zget R kS7 = c_n cx - t_cin st' -> zget R kS1 = c_ob cx + t_cout st' ->
  zget R kS9 = hold1 -> zget R kS3 = bits1 ->
  k_mem cx fin M0 st' lf cf M ->
  KDISP cx fin MD T M0 B ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TYPEDO_DROP_T (zupd R []) M MD) T.
Proof.
  intros cx fin MD T M0 B R M st' lf cf hold1 bits1 CX Hh SI MB Eh Eb Hb1 Hh1 E3 E4 E5 E28 E14 E9 E12 E2 E26 E24 E19 E20 E10 KM KD.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX. icx_cbn.
  zkeysb. unfold L_TYPEDO_DROP_T, L_DISP in *. pose proof two64_eq as TW64.
  zstep Rfd.
  zsetreg (Z.shiftr hold1 3) ltac:(rewrite (Z.mod_small hold1) by lia; reflexivity).
  zstep Rfd.
  zsetreg (bits1 - 3) ltac:(symmetry; rewrite ?swrap32_small by lia; first [reflexivity | lia]).
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ => eapply (KD R' Mx st' lf cf SI MB) end.
  - unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys. rewrite Eh, Eb. split_conj; zreg.
  - exact KM.
Qed.

Definition fp_typedo_f (p : Z) : list (Z * Z) := [(p + 8, 8); (p + 120, 24)].
Definition fp_typedo_d (u p : Z) : list (Z * Z) := [(p + 8, 8); (u + 48, 8)].

Lemma typedo_body_t : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
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
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _ & _ & _ & _ & Q80 & _).   (* the inflate_fixed reloads read 80(sp), 136(sp) *)
  clear ROM Wob Ww FRM CST HK Hmode SREST SRET SLO Hlens Hcodes WIN_ MODE_.
  zkeysb. unfold L_TYPEDO, L_TYPEDO_BODY_T, L_TYPEDO_DROP_T, L_DISP, L_LEAVE_LD2 in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_typedo_f p) ltac:(unfold fp_typedo_f; ranges_ok_tac)) as HSTf.
  assert (HAGf : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (fp_typedo_f p)) M) by (apply mpostL_refl).
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_typedo_d u p) ltac:(unfold fp_typedo_d; ranges_ok_tac)) as HSTd.
  assert (HAGd : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (fp_typedo_d u p)) M) by (apply mpostL_refl).
  unfold fp_typedo_f, fp_typedo_d in HSTf, HAGf, HSTd, HAGd.
  assert (REATT : forall Mq m la (fx : bool) c1 h1 b1,
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 8) m -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 12) la ->
    (fx = true -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 120) 67422 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 128) 69470 /\
                  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 136) 9 /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 140) 5) ->
    (fx = true -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M Mq [(p + 8, 8); (p + 120, 24)]) -> (fx = false -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M Mq [(p + 8, 8); (u + 48, 8)]) ->
    m <> LENEXT -> m <> DIST ->
    k_mem (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
          (IST m la flags c1 cout h1 b1 out ret length offset extra
               (if fx then CLenfix else lc) (if fx then CDistfix else dc) (if fx then 9 else lb) (if fx then 5 else db)
               ncode nlen ndist shave nx whave wnext) lf cf Mq).
  { intros Mq m la fx c1 h1 b1 Hm8 Hm12 HT HPa HPb Hne1 Hne2.
    clear HAGf HSTf HAGd HSTd HST HAG Wstk Wp H12 Q136 Hin.
    open_kmem KM0. open_std STD. destruct SAT as [Hmode SREST]. clear Hmode.
    unfold st_rest in SREST. icx_cbn.
    dand SREST as (_ & H24 & H64 & H68 & H92 & H96 & H100 & H104 & H112 & H120 & H124 & H128 & H132 & H136 & H140 & H144).
    fp_frame_from HP0.
    destruct fx;
      [ dand (HT eq_refl) as (T1 & T2 & T3 & T4); clear HT H104 H112 H120 H124; pose proof (HPa eq_refl) as HPq
      | clear HT; pose proof (HPb eq_refl) as HPq ]; clear HPa HPb.
    all: cbv [N_LENS N_CODES] in Hlens, Hcodes.
    all: zreattachL HPq.
    all: unfold k_mem; split_conj;
      [ close_std
      | unfold st_at, st_rest; icx_cbn; cbv [cp_addr LENFIX_ADDR DISTFIX_ADDR o_codes]; icx_cbn; split_conj; assumption
      | unfold s_ret in *; icx_cbn; assumption
      | unfold s_lo in *; icx_cbn; assumption
      | assumption | assumption | exact HAG
      | lazymatch goal with |- s_bk _ _ ?MX => match goal with H : s_bk _ _ MX |- _ => eapply (s_bk_other _ _ _ _ H); cbn [t_mode]; assumption end end ]. }
  tstep1 Rfd.
  destruct (Z.eq_dec last 0) as [Hl0 | Hl0].
  2: {
    pose proof (smod64_nz last ltac:(lia) Hl0) as Hnz.
    zbr Rfd false.
    zstep Rfd.
    zsetreg (bits mod 8) ltac:(symmetry; apply land7_mod; lia).
    zstep Rfd.
    zsetreg (bits - bits mod 8) ltac:(symmetry; apply landm8; lia).
    zstep Rfd.
    zsetreg (Z.shiftr hold (bits mod 8))
      ltac:(rewrite (Z.mod_small hold) by lia; rewrite (Z.mod_small (bits mod 8)) by (Z.to_euclidean_division_equations; lia); reflexivity).
    zstep Rfd. zlit.
    clear HSTf HAGf Q136.
    tstep1 Rfd.
    zstep Rfd.
    destruct (sinv_bytebits _ _ lf cf SI0 Hm) as [SI1 MB1].
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KD R' Mx (bytebits_st (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext))
                 lf cf SI1 MB1) end.
    - unfold s_regs_disp, s_fix, s_vars, bytebits_st; icx_cbn; zkeys; split_conj; zreg.
    - lazymatch goal with |- k_mem _ _ _ _ _ _ ?Mx => apply (REATT Mx CHECK last false) end;
        [ assumption | assumption | discriminate | discriminate | intros _; exact HAGd
        | cbv; intros EE; discriminate EE | cbv; intros EE; discriminate EE ]. }
  subst last. zbr Rfd true.
  zstep Rfd.
  assert (J : forall RJ cin1 hold1 bits1,
    zget RJ kSP = u + -256 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA3 = u -> zget RJ kS2 = u -> zget RJ kA1 = 0 -> zget RJ kRA = 16209 ->
    zget RJ kS7 = n - cin1 -> zget RJ kS1 = ob + cout -> zget RJ kS10 = q + cin1 -> zget RJ kS9 = hold1 -> zget RJ kS3 = bits1 ->
    cin <= cin1 <= n -> 3 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (n - cin1) + bits1 = 8 * (n - cin) + bits ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TYPEDO_BODY_T (zupd RJ []) M MD) T).
  { intros RJ cin1 hold1 bits1. intros. unfold L_TYPEDO_BODY_T. zkeys. clear H12 Hin.
    pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh1.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg ((hold1 / 2) mod 4) ltac:(symmetry; apply bits2_of_shift; lia).
    zstep Rfd.
    tstep1 Rfd.
    assert (DROP : forall RD Mq m fx,
      (m = STORED \/ m = TABLE \/ m = BAD \/ m = LEN_) -> (fx = true <-> m = LEN_) ->
      zget RD kSP = u + -256 -> zget RD kGP = K0 kGP -> zget RD kTP = K0 kTP -> zget RD kS0 = p ->
      zget RD kA3 = u -> zget RD kS2 = u -> zget RD kA1 = 0 -> zget RD kRA = 16209 ->
      zget RD kS7 = n - cin1 -> zget RD kS1 = ob + cout -> zget RD kS10 = q + cin1 -> zget RD kS9 = hold1 -> zget RD kS3 = bits1 ->
      mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 8) m -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 12) (Z.land hold1 1) ->
      (fx = true -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 120) 67422 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 128) 69470 /\
                    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 136) 9 /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 140) 5) ->
      (fx = true -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M Mq [(p + 8, 8); (p + 120, 24)]) -> (fx = false -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M Mq [(p + 8, 8); (u + 48, 8)]) ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TYPEDO_DROP_T (zupd RD []) Mq MD) T).
    { intros RD Mq m fx Hm1 Hfx E3 E4 E5 E28 E14 E9 E12 E2 E24 E19 E26 E20 E10 Mm Ml HT HPa HPb.
      destruct (sinv_typedo (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST mode 0 flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  lf cf m cin1 hold1 bits1 fx SI0 Hm ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) Hm1 Hfx) as [SI1 MB1].
      eapply (typedo_drop_t (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 _ RD Mq _ lf cf hold1 bits1 CX0 Hh SI1 MB1);
        [ reflexivity | reflexivity | lia | lia
        | (icx_cbn; assumption) ..
        | unfold typedo_st; cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
                                 t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext];
          apply (REATT Mq m (Z.land hold1 1) fx); first [ assumption | clear - Hm1; cbv [STORED TABLE BAD LEN_ LENEXT DIST] in *; lia ]
        | exact KD ]. }
    assert (Hc4 : 0 <= (hold1 / 2) mod 4 < 4) by (Z.to_euclidean_division_equations; lia).
    destruct (Z.eq_dec ((hold1 / 2) mod 4) 1) as [E1 | E1].
    {
      clear HAGd HSTd.
      zbr Rfd false.
      zbr Rfd true.
      (* TYPE's fixed path CALLS inflate_fixed (0x18b78; with UBSan's NULL / alignment checks)
         instead of inlining fixedtables; ra (16209) and flush come back from the frame (80(sp), 136(sp)) *)
      zstep Rfd. zstep Rfd.                       (* mv a0,s0; jal inflate_fixed *)
      zbr Rfd false.                              (* beqz a0 *)
      assert (ALp : p mod 16 = 0) by (clear - AL; unfold ctx_al in AL; cbn in AL; tauto). zstep Rfd. zalign.   (* and a1,a0,7 *)
      zbr Rfd false.                              (* bnez a1 *)
      zstep Rfd. zstep Rfd. zstep Rfd.            (* auipc a1; li a2,5; auipc a3 *)
      zstep Rfd. zlit.                            (* addi a1: lenfix *)
      zstep Rfd. zlit.                            (* slli a2,a2,32 *)
      zstep Rfd. zlit.                            (* addi a3: distfix *)
      zstep Rfd. zlit.                            (* addi a2,a2,9 *)
      tstep1 Rfd. tstep1 Rfd. tstep1 Rfd.         (* sd a1,120(a0); sd a3,128(a0); sd a2,136(a0) *)
      zstep Rfd.                                  (* ret *)
      tstep1 Rfd.                                 (* ld ra,80(sp) *)
      zstep Rfd.                                  (* li a0,-2 *)
      tstep1 Rfd.                                 (* ld a1,136(sp) *)
      zstep Rfd.                                  (* mv a3,s2 *)
      zstep Rfd.                                  (* addi a2,ra,-10 *)
      zstep Rfd.                                  (* li a4,6 *)
      tstep1 Rfd.                                 (* sw a2,8(s0) *)
      zbr Rfd true.                               (* bne a1,a4: flush is not Z_TREES *)
      lazymatch goal with H120 : mem_u64 _ ?Mx (p + 136) 21474836489 |- realizes _ (zcfg _ _ ?RD ?Mx _) _ =>
        pose proof (mem_u32_eqmod_t _ _ 21474836489 9 ltac:(reflexivity) (mem_u64_lo32 _ _ _ _ H120)) as Hlb;
        pose proof (mem_u64_hi32 _ _ _ _ H120) as Hdb;
        change (Z.shiftr 21474836489 32) with 5 in Hdb; replace (p + 136 + 4) with (p + 140) in Hdb by lia;
        apply (DROP RD Mx LEN_ true) end;
        [ cbv [LEN_ STORED TABLE BAD]; lia | split; [cbv [LEN_]; lia | reflexivity]
        | zreg .. | assumption | assumption | intros _; split_conj; assumption | intros _; exact HAGf | discriminate ]. }
    clear HAGf HSTf.
    destruct (Z_lt_dec 1 ((hold1 / 2) mod 4)) as [L2 | L2].
    {
      zbr Rfd true.
      zstep Rfd.
      destruct (Z.eq_dec ((hold1 / 2) mod 4) 2) as [E2 | E2].
      -
        zbr Rfd false.
        zstep Rfd. zstep Rfd. zlit.
        zstep Rfd.
        tstep1 Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ ?RD ?Mx _) _ => apply (DROP RD Mx TABLE false) end;
          [ cbv [LEN_ STORED TABLE BAD]; lia | split; [discriminate | cbv [LEN_ TABLE]; lia]
          | zreg .. | assumption | assumption | discriminate | discriminate | intros _; exact HAGd ].
      -
        zbr Rfd true.
        zstep Rfd. zstep Rfd. zlit.
        tstep1 Rfd.
        zstep Rfd. zstep Rfd. zlit.
        tstep1 Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ ?RD ?Mx _) _ => apply (DROP RD Mx BAD false) end;
          [ cbv [LEN_ STORED TABLE BAD]; lia | split; [discriminate | cbv [LEN_ BAD]; lia]
          | zreg .. | assumption | assumption | discriminate | discriminate | intros _; exact HAGd ]. }
    zbr Rfd false.
    zbr Rfd false.
    zstep Rfd. zstep Rfd. zlit.
    zstep Rfd.
    tstep1 Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RD ?Mx _) _ => apply (DROP RD Mx STORED false) end;
      [ cbv [LEN_ STORED TABLE BAD]; lia | split; [discriminate | cbv [LEN_ STORED]; lia]
      | zreg .. | assumption | assumption | discriminate | discriminate | intros _; exact HAGd ]. }
  clear HAGf HSTf HAGd HSTd.
  destruct (Z_lt_dec 2 bits) as [Hb3 | Hb3].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RJ _ _) _ => apply (J RJ cin hold bits) end; first [zreg | lia].
  - zbr Rfd false.
    destruct (Z.eq_dec (n - cin) 0) as [Hv0 | Hv0].
    +
      zbr Rfd false.
      zstep Rfd.
      clear H12 Q136. open_kmem KM0. destruct SAT as [Hmode SREST].
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
        eapply (KLL2 R' Mx (IST mode 0 flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI0) end;
        [ unfold s_regs_leave_ld2; icx_cbn; zkeys; split_conj; zreg
        | exact STD | split; [exact Hmode | exact SREST] | exact SRET | exact SLO | sbk | exact Hlens | exact Hcodes | exact HAG ].
    +
      zbr Rfd true.
      pose proof (Hfin cin ltac:(lia)) as Hb0.
      zstep Rfd.
      zstep Rfd.
      zbr Rfd true.
      tstep1 Rfd.
      zstep Rfd.
      zsetreg (fin cin * 2 ^ bits) ltac:(rewrite (Z.mod_small bits) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      zstep Rfd.
      zsetreg (bits + 8) ltac:(symmetry; apply lor8_small; lia).
      tstep1 Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (pullbyte_bound hold bits (fin cin) ltac:(lia) ltac:(lia) Hb0) as Hpb.
      lazymatch goal with |- realizes _ (zcfg _ _ ?RJ _ _) _ => apply (J RJ (cin + 1) (hold + fin cin * 2 ^ bits) (bits + 8)) end;
        first [zreg | lia].
Qed.

End TYPEDO_CODE.

Theorem arm_TYPEDO_t {RCa1 : RunCtx}  : arm_stmt L_TYPEDO TYPEDO.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  eapply typedo_body_t; try eassumption. right; exact Hm.
Qed.

Theorem arm_TYPE_t {RCa1 : RunCtx}  : arm_stmt L_TYPE TYPE.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof KM as KM0. open_kmem KM. pose proof STD as STD0. open_std STD.
  assert (F48 : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -208) (-5)) by (unfold i_frame in FRM; destr_conj FRM; assumption).
  pose proof CX as CX0. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  pose proof RE as RE0. unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  zkeysb. unfold L_TYPE, L_TYPEDO in *. pose proof two64_eq as TW64.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd true.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
    eapply (typedo_body_t (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx st lf cf CX0 Hh Hfin (or_introl Hm) SI) end.
  - unfold s_regs_arm, s_fix, s_vars; icx_cbn; zkeys; split_conj; zreg.
  - exact KM0.
  - exact K.
Qed.
End T_Type.

Module T_StoredA.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S.S_StoredA.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_COPY_MEMCPY_T : Z := 88552.
Definition L_COPY_DONE_T : Z := 88688.

Section WITH_MEMCPY.
Context {RCa1 : RunCtx}.
Hypothesis MEMCPY : memcpy_spec_t.

Lemma copy_body_t : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = COPY -> t_length st < 65536 -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_COPY (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm HL16 SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. destruct SLO as [HL HO].
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
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _ & _ & _ & _ & Q80 & _).
  zkeysb. unfold L_COPY, L_COPY_MEMCPY_T, L_COPY_DONE_T, L_REDISP, L_DISP, L_LEAVE_LD in *. cbv [A_MEMCPY] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  tstep1 Rfd.
  destruct (Z.eq_dec length 0) as [HL0 | HL0].
  {
    subst length. zbr Rfd true.
    zstep Rfd. zlit.
    tstep1 Rfd.
    zstep Rfd.
    pose proof (sinv_set _ _ lf cf TYPE cin cout hold bits 0 SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(cbv [COPY_ COPY TYPE]; lia)
                  ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
    pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST COPY last flags cin cout hold bits out ret 0 offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  TYPE cin cout hold bits 0 ltac:(right; split; [unfold Wm; cbn; lia | vm_compute; reflexivity])) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KD R' Mx _ lf cf SI1 MB1) end.
    - unfold s_regs_disp, s_fix, s_vars, set_st; icx_cbn; cbv [TYPE]; zkeys; split_conj; zreg.
    - unfold k_mem, set_st; icx_cbn; split_conj;
        [ close_std | split; [assumption | exact SREST] | exact SRET | split; [exact HL | exact HO] | exact Hlens | exact Hcodes | exact HAG | sbk ]. }
  pose proof (smod64_nz length ltac:(lia) HL0) as Hnz.
  zbr Rfd false.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?M1 _) _ =>
  assert (JL : forall RJ,
    zget RJ kSP = u + -256 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA3 = u -> zget RJ kS2 = u -> zget RJ kA1 = 0 ->
    zget RJ kS10 = q + cin -> zget RJ kS7 = n - cin -> zget RJ kS1 = ob + cout -> zget RJ kS9 = hold -> zget RJ kS3 = bits ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD (zupd RJ []) M1 MD) T);
  [| assert (JM : forall RJ copy,
    zget RJ kSP = u + -256 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA3 = u -> zget RJ kS2 = u -> zget RJ kA1 = 0 ->
    zget RJ kS10 = q + cin -> zget RJ kS7 = n - cin -> zget RJ kS1 = ob + cout -> zget RJ kS9 = hold -> zget RJ kS3 = bits ->
    zget RJ kS4 = copy ->
    1 <= copy -> copy <= length -> copy <= n - cin -> copy <= osz - cout ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_COPY_MEMCPY_T (zupd RJ []) M1 MD) T) ] end.
  {
    intros RJ. intros. unfold L_LEAVE_LD. zkeys.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KLL R' Mx (IST COPY last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI0) end.
    - unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SRET.
    - split; [exact HL | exact HO].
    - sbk.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  {
    intros RJ copy. intros. unfold L_COPY_MEMCPY_T. zkeys.
    zstep Rfd. zstep Rfd.
    zsetreg copy ltac:(symmetry; apply zext32_id; lia).
    zstep Rfd. zstep Rfd. zstep Rfd.
    zstep Rfd.
    pose proof (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 1 _ q n fin cin copy Hin ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc.
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
      zbr Rfd true.
      zbr Rfd true.
      zbr Rfd true.
      zstep Rfd.
      zbr Rfd true.
      zbr Rfd true.
      zbr Rfd true.
      tstep1 Rfd.
      tstep1 Rfd.
      zstep Rfd.
      tstep1 Rfd.
      tstep1 Rfd.
      tstep1 Rfd.
      unfold st_rest in SREST. icx_cbn.
      dand SREST as (C12 & C24 & C64 & C68 & _ & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
      tstep1 Rfd.
      zstep Rfd. zstep Rfd.
      pose proof (sinv_set _ _ lf cf COPY (cin + copy) (cout + copy) hold bits (length - copy) SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(intros _; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST COPY last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    COPY (cin + copy) (cout + copy) hold bits (length - copy) ltac:(left; unfold Wm; cbn; lia)) as MB1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
        eapply (KRD R' Mx _ lf cf SI1 MB1) end.
      + unfold s_regs_redisp, set_st; icx_cbn; zkeys; split_conj; zreg.
      + unfold k_mem, set_st; icx_cbn; split_conj;
          [ close_std
          | unfold st_at, st_rest; icx_cbn; split_conj; assumption
          | exact SRET
          | unfold s_lo; icx_cbn; replace (osz - (cout + copy)) with (osz - cout - copy) by lia; split; assumption
          | exact Hlens | exact Hcodes | exact HAG | sbk ]. }
  destruct (Z_lt_dec length (n - cin)) as [C1 | C1].
  - zbr Rfd true.
    zstep Rfd.
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

Theorem arm_COPY_t : arm_stmt L_COPY COPY.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  eapply copy_body_t; try eassumption. apply (copy_len_bound _ _ _ _ SI). right; exact Hm.
Qed.

Theorem arm_COPY__t : arm_stmt L_COPY_ COPY_.
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
  zstep Rfd. zlit.
  tstep1 Rfd.
  pose proof (sinv_set _ _ lf cf COPY cin cout hold bits length SI Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(intros _; exact HL16)
                ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
  pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                (IST COPY_ last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                COPY cin cout hold bits length ltac:(right; split; [unfold Wm; cbn; lia | vm_compute; reflexivity])) as MB1.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
    eapply (copy_body_t (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
              (set_st (IST COPY_ last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY cin cout hold bits length)
              lf cf CX0 Hh Hfin eq_refl ltac:(cbn; exact HL16) SI1) end.
  - unfold s_regs_arm, s_fix, s_vars, set_st; icx_cbn; zkeys; split_conj; zreg.
  - unfold k_mem, set_st; icx_cbn; split_conj;
      [ close_std | split; [assumption | exact SREST] | exact SRET | exact SLO | exact Hlens | exact Hcodes | exact HAG | sbk ].
  - eapply KALL_mono; [| exact K]. lia.
Qed.

End WITH_MEMCPY.
End T_StoredA.

Module T_Stored.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S.S_StoredA OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S.S_Stored.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U.TBase T_StoredA.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_STORED_LOOP_T : Z := 87652.
Definition L_STORED_BODY_T : Z := 88424.
Definition L_LEAVEX_ST_T : Z := 96140.

Section WITH_MEMCPY.
Context {RCa1 : RunCtx}.
Hypothesis MEMCPY : memcpy_spec_t.

Lemma stored_loop_t : forall (k : nat) cx fin MD T Rb l M (cin0' j0 cinj holdj j : Z),
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_T cx ->
  j = 32 - 8 * Z.of_nat k -> (1 <= k <= 4)%nat ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj -> j = j0 + 8 * (cinj - cin0') ->
  zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kS2 = c_u cx -> zget_l Rb l kA3 = c_u cx -> zget_l Rb l kA1 = 0 ->
  zget_l Rb l kS10 = c_q cx + cin0' -> zget_l Rb l kS7 = c_n cx - cin0' -> zget_l Rb l kA5 = j0 ->
  zget_l Rb l kS3 = j -> zget_l Rb l kT0 = j ->
  zget_l Rb l kA6 = c_q cx + cinj -> zget_l Rb l kT1 = c_q cx + cinj ->
  zget_l Rb l kA2 = c_n cx - cinj -> zget_l Rb l kS9 = holdj ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_q cx) (c_n cx) fin -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -120) 0 ->
  (forall R' hold',
     zget R' kS9 = hold' -> 0 <= hold' < 2 ^ (j0 + 8 * (c_n cx - cin0')) -> c_n cx - cinj < Z.of_nat k ->
     zget R' kA3 = c_u cx -> zget R' kA1 = 0 ->
     zget R' kS10 = c_q cx + cin0' -> zget R' kS7 = c_n cx - cin0' -> zget R' kA5 = j0 ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kS2 = zget_l Rb l kS2 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVEX_ST_T (zupd R' []) M MD) T) ->
  (forall R' hold',
     zget R' kA4 = c_q cx + cinj + Z.of_nat k -> zget R' kA2 = c_n cx - cinj - Z.of_nat k -> zget R' kS9 = hold' ->
     zget R' kS3 = 32 -> 0 <= hold' < 2 ^ 32 -> Z.of_nat k <= c_n cx - cinj ->
     zget R' kA3 = c_u cx -> zget R' kA1 = 0 ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kS2 = zget_l Rb l kS2 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kS11 = zget_l Rb l kS11 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_STORED_BODY_T (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_STORED_LOOP_T (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M cin0' j0 cinj holdj j Hh Hfin CXl Hj Hk Hc Hhj Hjc Hjj LSP LS0 LA3 LA1 L9 L7 LA5 L1 LT0 LA6 LT1 LA2 L3 Hin Q136 KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_T] in CXl; destr_conj CXl.
  zkeysb. unfold L_STORED_LOOP_T, L_STORED_BODY_T, L_LEAVEX_ST_T in *. pose proof two64_eq as TW64.
  assert (Hj32 : 2 ^ j <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 32) with 4294967296 in Hj32.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  -
    zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj) end; try zreg; try lia.
    all: replace (j0 + 8 * (n - cin0')) with j by lia; lia.
  - zbr Rfd true.
    pose proof (Hfin cinj ltac:(lia)) as Hb0.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (fin cinj * 2 ^ j) ltac:(rewrite (Z.mod_small j) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
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
        eapply (IH (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' M cin0' j0 (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) Hh Hfin) end;
        [ unfold ctx_lin; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_T]; split_conj; assumption || lia
        | lia | lia | icx_cbn; lia | lia | icx_cbn; lia | lia
        | (icx_cbn; zreg) .. | exact Hin | exact Q136 | | ].
      * intros R' hold'. icx_cbn. intros. eapply KLV; try eassumption; try lia; try zkept.
      * intros R' hold'. icx_cbn. intros. eapply KDN; try eassumption; try lia; try zkept.
Qed.

Theorem arm_STORED_t : arm_stmt L_STORED STORED.
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
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _).
  pose proof SRET as SRET'. unfold s_ret in SRET'. icx_cbn.
  zkeysb. unfold L_STORED, L_STORED_LOOP_T, L_STORED_BODY_T, L_LEAVEX_ST_T, L_LEAVE, L_BADMSG_A5, L_COPY_ in *.
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
    zget RJ kSP = u + -256 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA3 = u -> zget RJ kS2 = u -> zget RJ kA1 = 0 -> zget RJ kRA = 16209 -> zget RJ kS11 = -3 ->
    zget RJ kA4 = q + cin1 -> zget RJ kA2 = n - cin1 -> zget RJ kS1 = ob + cout -> zget RJ kS9 = hold1 -> zget RJ kS3 = bits1 ->
    cin <= cin1 <= n -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (n - cin1) + bits1 = 8 * (n - cin) + (bits - bits mod 8) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_STORED_BODY_T (zupd RJ []) Mc MD) T) end.
  { intros RJ cin1 hold1 bits1. intros. unfold L_STORED_BODY_T. zkeys.
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
    zstep Rfd. zlit.
    destruct (Z.eq_dec (Z.lxor (Z.shiftr hold1 16) (hold1 mod 65536)) 65535) as [EQ | NE].
    -
      rewrite EQ.
      zbr Rfd false.
      zstep Rfd.
      unfold st_rest in SREST. icx_cbn.
      dand SREST as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
      tstep1 Rfd.
      zstep Rfd. zlit.
      zstep Rfd.
      tstep1 Rfd.
      zstep Rfd. zstep Rfd.
      zstep Rfd.
      zbr Rfd true.
      pose proof (sinv_set _ _ lf cf COPY_ cin1 cout 0 0 (hold1 mod 65536) SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(intros _; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    COPY_ cin1 cout 0 0 (hold1 mod 65536) ltac:(left; unfold Wm; cbn; lia)) as MB1.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
        eapply (arm_COPY__t MEMCPY (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                  (set_st (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY_ cin1 cout 0 0 (hold1 mod 65536))
                  lf cf CX0 Hh Hfin eq_refl SI1) end.
      + unfold s_regs_arm, s_fix, s_vars, set_st; icx_cbn; zkeys; split_conj; zreg.
      + unfold k_mem, set_st; icx_cbn; split_conj;
          [ close_std | unfold st_at, st_rest; icx_cbn; split_conj; assumption | exact SRET | exact SLO | exact Hlens | exact Hcodes | exact HAG | sbk ].
      + eapply KALL_mono; [| exact KA0]. lia.
    -
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
        eapply (KB5 R' Mx (set_st (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                              STORED cin1 cout hold1 bits1 length) lf cf) end.
      + unfold bad_of, set_st; cbn. exact SI1.
      + unfold bad_of, set_st; cbn. unfold set_st in MB1; cbn in MB1. exact MB1.
      + unfold s_fix; icx_cbn; zkeys; split_conj; zreg.
      + unfold set_st; icx_cbn; zreg.
      + unfold set_st; icx_cbn; zreg.
      + unfold set_st; icx_cbn; zreg.
      + unfold set_st; icx_cbn; zreg.
      + unfold set_st; icx_cbn; zreg.
      + lazymatch goal with |- 0 <= ?x < _ => assert (EA5 : x = 66266) by zreg; rewrite EA5 end. lia.
      + unfold k_mem, set_st; icx_cbn; split_conj;
          [ close_std | split; [exact Hmode | exact SREST] | exact SRET | exact SLO | exact Hlens | exact Hcodes | exact HAG | sbk ]. }
  destruct (Z_lt_dec 31 bits) as [Hb32 | Hb32].
  -
    zbr Rfd true.
    zstep Rfd.
    zsetreg (bits - bits mod 8) ltac:(symmetry; apply landm8; lia).
    zstep Rfd. zstep Rfd.
    assert (Hmono : 2 ^ (bits - bits mod 8) <= 2 ^ bits) by (apply Z.pow_le_mono_r; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (BODY R' cin (Z.shiftr hold (bits mod 8)) (bits - bits mod 8)) end;
      first [zreg | lia | Z.to_euclidean_division_equations; lia].
  -
    zbr Rfd false.
    zstep Rfd.
    zsetreg (bits - bits mod 8) ltac:(symmetry; apply land24; lia).
    zstep Rfd. zstep Rfd. zstep Rfd.
    zstep Rfd. zstep Rfd.
    assert (Hkk : exists k : nat, bits - bits mod 8 = 32 - 8 * Z.of_nat k /\ (1 <= k <= 4)%nat).
    { exists (Z.to_nat (4 - bits / 8)). rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (stored_loop_t k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' Mx cin (bits - bits mod 8) cin (Z.shiftr hold (bits mod 8)) (bits - bits mod 8) Hh Hfin CXl Hk1 Hk2) end;
      [ icx_cbn; lia | exact Hsh | lia | lia | (icx_cbn; zreg) .. | exact Hin | exact Q136 | | ].
    +
      intros R' hold'. icx_cbn. intros. zimps. zkeys. unfold L_LEAVEX_ST_T in *.
      zstep Rfd.
      zstep Rfd.
      zsetreg (8 * (n - cin)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; rewrite ?Z.mod_small by lia; lia).
      zstep Rfd. zext32.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_set _ _ lf cf STORED n cout hold' (bits - bits mod 8 + 8 * (n - cin)) length SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(cbv [COPY_ COPY STORED]; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KL Rx Mx _ ret lf cf SI1) end.
      * unfold s_regs_leave, set_st; icx_cbn; zkeys; split_conj; try zreg. all: zkept.
      * close_std.
      * unfold set_st; split; [exact Hmode | exact SREST].
      * exact SLO.
      * sbk.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' hold'. icx_cbn. intros. zimps. zkeys. unfold L_STORED_BODY_T in *.
      apply (BODY R' (cin + Z.of_nat k) hold' 32); try zkept; try lia.
Qed.

End WITH_MEMCPY.
End T_Stored.

Module T_HeadA.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S.S_HeadA.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U.TBase T_Type.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_DICT_CALL_T : Z := 88192.
Definition L_ADLER_RET1_T : Z := 88208.

Section WITH_ADLER_NULL.
Context {RCa1 : RunCtx}.
Hypothesis ADLN : adler32_null_spec_t.

Lemma dict_body_t : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DICT -> sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kA3 = c_u cx -> zget_l Rb l kS2 = c_u cx ->
  zget_l Rb l kS10 = c_q cx + t_cin st -> zget_l Rb l kS7 = c_n cx - t_cin st ->
  zget_l Rb l kS1 = c_ob cx + t_cout st -> zget_l Rb l kS9 = t_hold st -> zget_l Rb l kS3 = t_bits st ->
  zget_l Rb l kS11 = -3 ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DICT (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI LSP LGP LTP L11 LA3 LS0 L9 L7 L2 L3 L1 L10 KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. destruct SLO as [HL HO].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags t_cin t_cout t_hold t_bits t_out] in *. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_. pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  destruct (mem_wr_u32_exists_R M (p + 24) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (hd & Hhd & Rhd).
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _ & _ & _ & _ & Q80 & Q72 & _).   (* the need-dict exit reads in at 72(sp) *)
  unfold s_lo in HL, HO. icx_cbn.
  zkeysb. unfold L_DICT, L_DICT_CALL_T, L_ADLER_RET1_T, L_NEED_DICT, L_RET, L_TYPE in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  tstep1 Rfd.
  destruct (Z.eq_dec hd 0) as [Hd0 | Hd0].
  -
    subst hd. zbr Rfd false.
    (* a worker 1.4 UBSan: the need-dictionary exit (0x177d8) also adds the input consumed in this call to
       strm->total_in; left (112(sp)) and in (72(sp)) come from the frame *)
    destruct (mem_wr_u64_exists_R M (u + 16) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (ti & Hti & Rti).
    zstep Rfd.                        (* j the need-dict exit *)
    tstep1 Rfd.                       (* ld a0,112(sp): left *)
    tstep1 Rfd.                       (* sw a0,32(a3): avail_out *)
    tstep1 Rfd.                       (* sd s9,96(s0): hold *)
    tstep1 Rfd.                       (* sw s3,104(s0): bits *)
    tstep1 Rfd.                       (* ld a0,16(a3): total_in *)
    tstep1 Rfd.                       (* ld a1,72(sp): n - cin0 *)
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* subw; slli; srli; add *)
    tstep1 Rfd.                       (* sd s10,0(a3): next_in *)
    tstep1 Rfd.                       (* sw s7,8(a3): avail_in *)
    tstep1 Rfd.                       (* sd a0,16(a3): total_in *)
    tstep1 Rfd.                       (* sd s1,24(a3): next_out *)
    zstep Rfd.                        (* li a0,2 *)
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
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R ?lc') ?Mx _) _ =>
      eapply (ADLN R lc' Mx MD T (u + -256) _ Hh) end.
    all: lazymatch goal with
         | |- forall M' : mem, _ => idtac
         | |- _ => cbv [FR_AD]; first [ zreg | reflexivity | lia | eapply mem_wr_sub; [exact Wstk | lia | lia] ]
         end.
    intros M2 R2 HP E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
    zimps. zkeys.
    apply mpost_mpostL1 in HP. cbv [FR_AD] in HP. zreattachL HP.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zlit.
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_hd _ _ lf cf TYPE flags cin hold bits SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(cbn; intros E; exfalso; exact (Hfl E))
                  ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST DICT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  TYPE flags cin hold bits ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (arm_TYPE_t (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                (hd_st (IST DICT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) TYPE flags cin hold bits)
                lf cf CX0 Hh Hfin eq_refl SI1) end.
    + unfold s_regs_arm, s_fix, s_vars, hd_st; icx_cbn; zkeys; split_conj; try zreg; zkept.
    + unfold k_mem, hd_st; icx_cbn; split_conj;
        [ close_std | split; [assumption | exact SREST] | exact SRET | unfold s_lo; icx_cbn; split; [exact HL | exact HO]
        | exact Hlens | exact Hcodes | exact HAG | sbk ].
    + eapply KALL_mono; [| exact KA0]. lia.
Qed.

Theorem arm_DICT_t : arm_stmt L_DICT DICT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  unfold s_regs_arm, s_fix, s_vars in RE. destr_conj RE. eapply dict_body_t; eassumption.
Qed.

End WITH_ADLER_NULL.
End T_HeadA.

Module T_HeadB.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S.S_HeadA.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U.TBase T_Type T_HeadA.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_DICTID_LOOP_T : Z := 87516.
Definition L_DICTID_BODY_T : Z := 88096.
Definition L_LEAVEX_DI_T : Z := 96120.

Section WITH_ADLER_NULL.
Context {RCa1 : RunCtx}.
Hypothesis ADLN : adler32_null_spec_t.

Lemma dictid_loop_t : forall (k : nat) cx fin MD T Rb l M (cinj holdj j : Z),
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_T cx ->
  32 - 8 * Z.of_nat k <= j < 40 - 8 * Z.of_nat k -> (1 <= k <= 4)%nat -> 0 <= j ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kS2 = c_u cx -> zget_l Rb l kA3 = c_u cx -> zget_l Rb l kA1 = 0 ->
  zget_l Rb l kA7 = j -> zget_l Rb l kA6 = c_q cx + cinj -> zget_l Rb l kA4 = c_q cx + cinj ->
  zget_l Rb l kA0 = c_n cx - cinj -> zget_l Rb l kS9 = holdj ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_q cx) (c_n cx) fin -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -120) 0 ->
  (forall R' hold' j',
     zget R' kS9 = hold' -> j' = j + 8 * (c_n cx - cinj) -> 0 <= hold' < 2 ^ j' -> c_n cx - cinj < Z.of_nat k ->
     zget R' kA3 = c_u cx -> zget R' kA1 = 0 ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kS2 = zget_l Rb l kS2 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA ->
     zget R' kS10 = zget_l Rb l kS10 -> zget R' kS7 = zget_l Rb l kS7 -> zget R' kS3 = zget_l Rb l kS3 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVEX_DI_T (zupd R' []) M MD) T) ->
  (forall R' hold' j',
     zget R' kA2 = c_q cx + cinj + Z.of_nat k -> zget R' kA0 = c_n cx - cinj - Z.of_nat k -> zget R' kS9 = hold' ->
     j' = j + 8 * Z.of_nat k -> 0 <= hold' < 2 ^ j' -> Z.of_nat k <= c_n cx - cinj ->
     zget R' kA3 = c_u cx -> zget R' kA1 = 0 ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kS2 = zget_l Rb l kS2 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kS11 = zget_l Rb l kS11 ->
     zget R' kS10 = zget_l Rb l kS10 -> zget R' kS7 = zget_l Rb l kS7 -> zget R' kS3 = zget_l Rb l kS3 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DICTID_BODY_T (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DICTID_LOOP_T (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M cinj holdj j Hh Hfin CXl Hj Hk Hj0 Hc Hhj Hjc LSP LS0 LA3 LA1 LA7 LA6 LA4 LA0 L3 Hin Q136 KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_T] in CXl; destr_conj CXl.
  zkeysb. unfold L_DICTID_LOOP_T, L_DICTID_BODY_T, L_LEAVEX_DI_T in *. pose proof two64_eq as TW64.
  assert (Hj40 : 2 ^ j <= 2 ^ 39) by (apply Z.pow_le_mono_r; lia). change (2 ^ 39) with 549755813888 in Hj40.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  -
    zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj j) end; try zreg; try lia.
  - zbr Rfd true.
    pose proof (Hfin cinj ltac:(lia)) as Hb0.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd true.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (fin cinj * 2 ^ j) ltac:(rewrite (Z.mod_small j) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
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
        [ unfold ctx_lin; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_T]; split_conj; assumption || lia
        | lia | lia | lia | icx_cbn; lia | lia | icx_cbn; lia
        | (icx_cbn; zreg) .. | exact Hin | exact Q136 | | ].
      * intros R' hold' j'. icx_cbn. intros. eapply KLV; try eassumption; try lia; try zkept.
      * intros R' hold' j'. icx_cbn. intros. eapply KDN; try eassumption; try lia; try zkept.
Qed.

Lemma dictid_body_t : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DICTID -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DICTID (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof (proj1 CX) as CXl. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags] in Hm, Hfl. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_. pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _).
  pose proof SRET as SRET'. unfold s_ret in SRET'. icx_cbn.
  zkeysb. unfold L_DICTID, L_DICTID_LOOP_T, L_DICTID_BODY_T, L_LEAVEX_DI_T, L_LEAVE, L_DICT in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (BODY : forall RJ cin1 hold1 bits1,
    zget RJ kSP = u + -256 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA3 = u -> zget RJ kS2 = u -> zget RJ kRA = 16209 -> zget RJ kS11 = -3 ->
    zget RJ kS1 = ob + cout -> zget RJ kA2 = q + cin1 -> zget RJ kA0 = n - cin1 -> zget RJ kS9 = hold1 ->
    cin <= cin1 <= n -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (n - cin1) + bits1 = 8 * (n - cin) + bits ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DICTID_BODY_T (zupd RJ []) Mc MD) T) end.
  { intros RJ cin1 hold1 bits1. intros. unfold L_DICTID_BODY_T. zkeys.
    pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh1.
    zstep Rfd.
    do 10 (zstep Rfd).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zstep Rfd.
    zgenreg_range chk 0 18446744073709551616
      ltac:(rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; [apply Z.mod_pos_bound|]; lia | apply Z.div_lt_upper_bound; [lia|]; eapply Z.lt_le_trans; [apply Z.mod_pos_bound; lia|]; cbn; lia]).
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_hd _ _ lf cf DICT flags cin1 0 0 SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(cbn; intros E; exfalso; exact (Hfl E))
                  ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST DICTID last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  DICT flags cin1 0 0 ltac:(left; cbn; lia)) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (dict_body_t ADLN (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                (hd_st (IST DICTID last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) DICT flags cin1 0 0)
                lf cf CX0 Hh Hfin eq_refl SI1) end;
      [ (unfold hd_st; icx_cbn; zkeys; zreg) ..
      | unfold k_mem, hd_st; icx_cbn; split_conj;
        [ close_std | split; [assumption | exact SREST] | exact SRET | exact SLO | exact Hlens | exact Hcodes | exact HAG | sbk ]
      | eapply KALL_mono; [| exact KA0]; lia ]. }
  destruct (Z_lt_dec 31 bits) as [Hb32 | Hb32].
  - zbr Rfd true.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (BODY R' cin hold bits) end; first [zreg | lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
    assert (Hkk : exists k : nat, 32 - 8 * Z.of_nat k <= bits < 40 - 8 * Z.of_nat k /\ (1 <= k <= 4)%nat).
    { exists (Z.to_nat (4 - bits / 8)).
      rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (dictid_loop_t k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' Mx cin hold bits Hh Hfin CXl Hk1 Hk2) end;
      [ lia | icx_cbn; lia | lia | lia | (icx_cbn; zreg) .. | exact Hin | exact Q136 | | ].
    +
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_LEAVEX_DI_T in *.
      zstep Rfd.
      zstep Rfd.
      zsetreg (8 * (n - cin)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; rewrite ?Z.mod_small by lia; lia).
      zstep Rfd. zext32.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_hd _ _ lf cf DICTID flags n hold' j' SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(cbn; intros E; exfalso; exact (Hfl E))
                    ltac:(cbn; lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia)) as SI1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KL Rx Mx _ ret lf cf SI1) end.
      * unfold s_regs_leave, hd_st; icx_cbn; zkeys; split_conj; try zreg. all: zkept.
      * close_std.
      * unfold hd_st; split; [exact Hmode | exact SREST].
      * exact SLO.
      * sbk.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_DICTID_BODY_T in *.
      apply (BODY R' (cin + Z.of_nat k) hold' j'); try zkept; try lia.
Qed.

Theorem arm_DICTID_t : arm_stmt L_DICTID DICTID.
Proof. intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K. eapply dictid_body_t; eassumption. Qed.

End WITH_ADLER_NULL.
End T_HeadB.

Module T_Head.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S.S_HeadA OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S.S_Head.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_HEAD_LOOP_T : Z := 87196.
Definition L_HEAD_BODY_T : Z := 90592.
Definition L_HEAD_WERR_T : Z := 95700.   (* 0x17574 *)
Definition L_HEAD_FIN_T : Z := 95868.
Definition L_LEAVEX_HD_T : Z := 95952.

Definition fp_head_t (u p : Z) : list (Z * Z) :=
  [(p + 8, 4); (p + 28, 20); (u + 48, 8); (u + 96, 8); (u + -384, 128)].

Section WITH_ADLER_NULL.
Context {RCa1 : RunCtx}.
Hypothesis ADLN : adler32_null_spec_t.

Lemma head_main_t : forall cx fin MD T M0 Rb l M st lf cf (cin1 hold1 bits1 : Z),
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = HEAD -> sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS2 = c_u cx -> zget_l Rb l kRA = 16209 -> zget_l Rb l kA4 = 5 ->
  zget_l Rb l kS1 = c_ob cx + t_cout st ->
  zget_l Rb l kS4 = c_q cx + cin1 -> zget_l Rb l kS11 = c_n cx - cin1 ->
  zget_l Rb l kS9 = hold1 -> zget_l Rb l kA2 = bits1 ->
  t_cin st <= cin1 <= c_n cx -> 16 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
  8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_HEAD_BODY_T (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf cin1 hold1 bits1 CX Hh Hfin Hm SI
         LSP LGP LTP L11 LS0 LRA LA4 L2 L4 L10 L3 LA2 Hc1 Hb1 Hh1 Hbc1 HW1 KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof KM as KM0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags t_cin t_cout t_hold t_bits t_out] in *. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh64.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & _ & H48 & H56 & _).
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _ & _ & _ & _ & Q80 & _).
  pose proof (rom_mod31_u64 M ROM) as H31.
  pose proof SREST as SR'. unfold st_rest in SR'. icx_cbn. dand SR' as (_ & H24 & _).
  clear ROM Wob Ww FRM CST HK Hmode SREST SRET SLO Hlens Hcodes Hin.
  zkeysb. unfold L_HEAD_BODY_T, L_HEAD_WERR_T, L_HEAD_FIN_T, L_DISP in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_head_t u p) ltac:(unfold fp_head_t; ranges_ok_tac)) as HSTh.
  assert (HAGh : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (fp_head_t u p)) M) by (apply mpostL_refl).
  unfold fp_head_t in HSTh, HAGh.
  assert (EXIT : forall RX Mq m' flags' hold' bits',
    sinv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                m' flags' cin1 hold' bits') lf cf ->
    meas (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                m' flags' cin1 hold' bits') <
    meas (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ->
    zget RX kSP = u + -256 -> zget RX kGP = K0 kGP -> zget RX kTP = K0 kTP -> zget RX kS0 = p ->
    zget RX kA3 = u -> zget RX kS2 = u -> zget RX kA1 = 0 -> zget RX kRA = 16209 ->
    zget RX kS10 = q + cin1 -> zget RX kS7 = n - cin1 -> zget RX kS1 = ob + cout ->
    zget RX kS9 = hold' -> zget RX kS3 = bits' ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 8) m' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 28) flags' ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M Mq [(p + 8, 4); (p + 28, 20); (u + 48, 8); (u + 96, 8); (u + -384, 128)] ->
    m' <> LENEXT -> m' <> DIST ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DISP (zupd RX []) Mq MD) T).
  { intros RX Mq m' flags' hold' bits' SI1 MB1 E3 E4 E5 E28 E14 E9 E12 E2 E26 E24 E19 E20 E10 Hm8 Hf24 HPq Hne1 Hne2.
    clear HST HAG Wstk Wp HSTh HAGh H48 H56 H31 Q136 Q80 H24.
    open_kmem KM0. open_std STD. destruct SAT as [Hmode SREST]. clear Hmode.
    unfold st_rest in SREST. icx_cbn.
    dand SREST as (H12 & _ & H64 & H68 & H92 & H96 & H100 & H104 & H112 & H120 & H124 & H128 & H132 & H136 & H140 & H144).
    fp_frame_from HP0.
    cbv [N_LENS N_CODES] in Hlens, Hcodes.
    zreattachL HPq.
    eapply (KD RX Mq (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                            m' flags' cin1 hold' bits') lf cf SI1 MB1).
    - unfold s_regs_disp, s_fix, s_vars, hd_st; icx_cbn; zkeys; split_conj; zreg.
    - unfold k_mem; split_conj;
      [ close_std
      | unfold st_at, st_rest, hd_st; icx_cbn; split_conj; assumption
      | unfold s_ret, hd_st in *; icx_cbn; assumption
      | unfold s_lo, hd_st in *; icx_cbn; assumption
      | assumption | assumption | exact HAG
      | lazymatch goal with |- s_bk _ _ ?MX => match goal with H : s_bk _ _ MX |- _ => eapply (s_bk_other _ _ _ _ H); cbn [t_mode]; assumption end end ]. }
  zstep Rfd. zlit.
  zbr Rfd true.
  tstep1 Rfd.
  zbr Rfd true.
  zstep Rfd. zlit.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zlit.
  zstep Rfd.
  zstep Rfd. zlit.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd. zlit.
  zstep Rfd. zlit.
  zstep Rfd.
  zgenreg pr.
  clear H31 H48.
  destruct (zcond BC_GEU pr 595056260442243601) eqn:Hc31.
  {
    zbrH Rfd true.
    clear H56.
    zstep Rfd. zstep Rfd. zlit.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd. zstep Rfd. zstep Rfd.
    zstep Rfd.
    pose proof (sinv_hd _ _ lf cf BAD flags cin1 hold1 bits1 SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(intros _; right; reflexivity)
                  ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  BAD flags cin1 hold1 bits1 ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?Mx _) _ => apply (EXIT RX Mx BAD flags hold1 bits1 SI1 MB1) end;
      first [zreg | assumption | exact HAGh | cbv; intros EE; discriminate EE]. }
  zbrH Rfd false.
  zstep Rfd.
  zstep Rfd.
  zgenreg mth.
  zstep Rfd.
  destruct (zcond BC_NE mth 8) eqn:Hcm.
  {
    zbrH Rfd true.
    clear H56.
    zstep Rfd. zstep Rfd. zlit.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd. zstep Rfd. zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_hd _ _ lf cf BAD flags cin1 hold1 bits1 SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(intros _; right; reflexivity)
                  ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  BAD flags cin1 hold1 bits1 ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?Mx _) _ => apply (EXIT RX Mx BAD flags hold1 bits1 SI1 MB1) end;
      first [zreg | assumption | exact HAGh | cbv; intros EE; discriminate EE]. }
  zbrH Rfd false.
  (* len = BITS(4) + 8 is checked against 15 first,
     then against wbits only when wbits != 0, and wbits is set to len only when it was 0. Here wbits = 15. *)
  zstep Rfd.                          (* 17528 srli a0,s9,4 *)
  zsetreg (Z.shiftr hold1 4) ltac:(rewrite (Z.mod_small hold1) by lia; reflexivity).
  zstep Rfd.                          (* 1752c andi a1,a0,15 *)
  zgenreg len4.
  zstep Rfd.                          (* 17530 li a3,7 *)
  pose proof (shiftr_lt_pow2 hold1 bits1 4 ltac:(lia) Hh1) as Hsh4.
  (* the window-size error exit (0x17574) *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (WERR : forall RW,
    zget RW kSP = u + -256 -> zget RW kGP = K0 kGP -> zget RW kTP = K0 kTP -> zget RW kS0 = p -> zget RW kS2 = u ->
    zget RW kS1 = ob + cout -> zget RW kS4 = q + cin1 -> zget RW kS11 = n - cin1 ->
    zget RW kA2 = bits1 -> zget RW kA0 = Z.shiftr hold1 4 ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_HEAD_WERR_T (zupd RW []) Mc MD) T) end.
  { intros RW. intros. unfold L_HEAD_WERR_T. zkeys. clear H56.
    tstep1 Rfd.                       (* addiw s3,a2,-4 *)
    zstep Rfd. zstep Rfd. zlit.       (* auipc; addi: the message *)
    zstep Rfd.                        (* mv a3,s2 *)
    tstep1 Rfd.                       (* sd a1,48(s2) *)
    tstep1 Rfd.                       (* ld ra,80(sp) *)
    tstep1 Rfd.                       (* sw ra,8(s0) *)
    zstep Rfd. zstep Rfd. zstep Rfd. (* mv s10,s4; mv s7,s11; mv s9,a0 *) zstep Rfd. zstep Rfd. zstep Rfd.   (* j 1637c; ld a1,136(sp); li a0,-2 *)
    zstep Rfd.                        (* j *)
    pose proof (sinv_hd _ _ lf cf BAD flags cin1 (Z.shiftr hold1 4) (bits1 - 4) SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity)
                  ltac:(intros _; right; reflexivity)
                  ltac:(cbn; lia) ltac:(lia) ltac:(exact Hsh4) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  BAD flags cin1 (Z.shiftr hold1 4) (bits1 - 4) ltac:(left; cbn; lia)) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?Mx _) _ => apply (EXIT RX Mx BAD flags (Z.shiftr hold1 4) (bits1 - 4) SI1 MB1) end;
      first [zreg | assumption | exact HAGh | cbv; intros EE; discriminate EE]. }
  destruct (zcond BC_LTU 7 len4) eqn:Hc7.
  { zbrH Rfd true.                    (* bltu a3,a1: len > 15 *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?RW _ _) _ => apply (WERR RW); zreg end. }
  zbrH Rfd false.
  tstep1 Rfd.                         (* 17538 lw a4,68(s0): wbits *)
  zstep Rfd.                          (* 1753c addi a3,a1,8 *)
  zgenreg lenp8.
  zbr Rfd false.                      (* 17540 beqz a4: wbits = 15 *)
  destruct (zcond BC_GEU 15 lenp8) eqn:Hc15.
  2: { zbrH Rfd false.                (* bgeu a4,a3 not taken: len > wbits *)
       lazymatch goal with |- realizes _ (zcfg _ _ ?RW _ _) _ => apply (WERR RW); zreg end. }
  zbrH Rfd true.                      (* 17544 bgeu a4,a3 *)
  zbr Rfd true.                       (* 175a8 bnez a4: wbits kept *)
  clear WERR Hsh4.
  zstep Rfd.
  zstep Rfd.
  zgenreg dmax.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd. zstep Rfd. zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R ?lc') ?Mx _) _ =>
    eapply (ADLN R lc' Mx MD T (u + -256) _ Hh) end.
  all: lazymatch goal with
       | |- forall M' : mem, _ => idtac
       | |- _ => cbv [FR_AD]; first [ zreg | reflexivity | lia | eapply mem_wr_sub; [exact Wstk | lia | lia] ]
       end.
  intros Ma Ra HP E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
  zimps. zkeys.
  apply mpost_mpostL1 in HP. cbv [FR_AD] in HP. zreattachL HP.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zgenreg hs.
  zstep Rfd. zlit.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (FIN : forall RF m', (m' = DICTID \/ m' = TYPE) ->
    zget RF kSP = u + -256 -> zget RF kGP = K0 kGP -> zget RF kTP = K0 kTP -> zget RF kS0 = p -> zget RF kS2 = u ->
    zget RF kS1 = ob + cout -> zget RF kS4 = q + cin1 -> zget RF kS11 = n - cin1 -> zget RF kA0 = m' ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_HEAD_FIN_T (zupd RF []) Mc MD) T) end.
  { intros RF m' Hm'. intros. unfold L_HEAD_FIN_T. zkeys.
    assert (Rm' : 0 <= m' < 4294967296) by (destruct Hm' as [-> | ->]; cbv [DICTID TYPE]; lia).
    zstep Rfd. zstep Rfd.
    tstep1 Rfd.
    zstep Rfd. zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_hd _ _ lf cf m' 0 cin1 0 0 SI0 eq_refl ltac:(destruct Hm' as [-> | ->]; (first [solve [zkeep_section; tauto] | tauto])) ltac:(right; reflexivity)
                  ltac:(intros E; discriminate E)
                  ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  m' 0 cin1 0 0 ltac:(left; cbn; lia)) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?Mx _) _ => apply (EXIT RX Mx m' 0 0 0 SI1 MB1) end;
      first [zreg | assumption | exact HAGh | clear - Hm'; cbv [DICTID TYPE LENEXT DIST] in *; lia]. }
  destruct (zcond BC_GE hs 0) eqn:Hcs.
  - zbrH Rfd true.
    zstep Rfd. zlit.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RF _ _) _ => apply (FIN RF TYPE); [right; reflexivity | zreg ..] end.
  - zbrH Rfd false.
    zstep Rfd. zlit.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RF _ _) _ => apply (FIN RF DICTID); [left; reflexivity | zreg ..] end.
Qed.

Lemma head_loop_t : forall (k : nat) cx fin MD T Rb l M (cinj holdj j : Z),
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_T cx ->
  16 - 8 * Z.of_nat k <= j < 24 - 8 * Z.of_nat k -> (1 <= k <= 2)%nat -> 0 <= j ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  zget_l Rb l kA5 = j -> zget_l Rb l kA2 = j -> zget_l Rb l kA1 = c_q cx + cinj -> zget_l Rb l kA6 = c_q cx + cinj ->
  zget_l Rb l kS11 = c_n cx - cinj -> zget_l Rb l kS9 = holdj ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_q cx) (c_n cx) fin ->
  (forall R' hold' j',
     zget R' kS9 = hold' -> j' = j + 8 * (c_n cx - cinj) -> 0 <= hold' < 2 ^ j' -> c_n cx - cinj < Z.of_nat k ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kS2 = zget_l Rb l kS2 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA ->
     zget R' kS10 = zget_l Rb l kS10 -> zget R' kS7 = zget_l Rb l kS7 -> zget R' kS3 = zget_l Rb l kS3 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVEX_HD_T (zupd R' []) M MD) T) ->
  (forall R' hold' j',
     zget R' kS4 = c_q cx + cinj + Z.of_nat k -> zget R' kS11 = c_n cx - cinj - Z.of_nat k ->
     zget R' kA2 = j' -> zget R' kS9 = hold' ->
     j' = j + 8 * Z.of_nat k -> 0 <= hold' < 2 ^ j' -> Z.of_nat k <= c_n cx - cinj ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kS2 = zget_l Rb l kS2 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kA4 = zget_l Rb l kA4 ->
     zget R' kS10 = zget_l Rb l kS10 -> zget R' kS7 = zget_l Rb l kS7 -> zget R' kS3 = zget_l Rb l kS3 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_HEAD_BODY_T (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_HEAD_LOOP_T (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M cinj holdj j Hh Hfin CXl Hj Hk Hj0 Hc Hhj Hjc LA5 LA2 LA1 LA6 L10 L3 Hin KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_T] in CXl; destr_conj CXl.
  zkeysb. unfold L_HEAD_LOOP_T, L_HEAD_BODY_T, L_LEAVEX_HD_T in *. pose proof two64_eq as TW64.
  assert (Hj24 : 2 ^ j <= 2 ^ 23) by (apply Z.pow_le_mono_r; lia). change (2 ^ 23) with 8388608 in Hj24.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  -
    zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj j) end; try zreg; try lia.
  - zbr Rfd true.
    pose proof (Hfin cinj ltac:(lia)) as Hb0.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd true.
    zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
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
        [ unfold ctx_lin; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_T]; split_conj; assumption || lia
        | lia | lia | lia | icx_cbn; lia | lia | icx_cbn; lia
        | (icx_cbn; zreg) .. | exact Hin | | ].
      * intros R' hold' j'. icx_cbn. intros. eapply KLV; try eassumption; try lia; try zkept.
      * intros R' hold' j'. icx_cbn. intros. eapply KDN; try eassumption; try lia; try zkept.
Qed.

Lemma head_body_t : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = HEAD -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_HEAD (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof KM as KM0. pose proof K as KA0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof (proj1 CX) as CXl. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags] in Hm. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & H16 & _).
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _).
  pose proof SRET as SRET'. unfold s_ret in SRET'. icx_cbn.
  clear ROM Wob Ww FRM CST HK Hmode SREST SRET SLO Hlens Hcodes.
  zkeysb. unfold L_HEAD, L_HEAD_LOOP_T, L_HEAD_BODY_T, L_LEAVEX_HD_T, L_LEAVE in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  tstep1 Rfd.
  zbr Rfd false.
  zstep Rfd.
  destruct (Z_lt_dec 15 bits) as [Hb16 | Hb16].
  - zbr Rfd true.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (head_main_t (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf cin hold bits CX0 Hh Hfin eq_refl SI0) end;
      [ (icx_cbn; zreg) .. | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
    assert (Hkk : exists k : nat, 16 - 8 * Z.of_nat k <= bits < 24 - 8 * Z.of_nat k /\ (1 <= k <= 2)%nat).
    { exists (Z.to_nat (2 - bits / 8)).
      rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (head_loop_t k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' Mx cin hold bits Hh Hfin CXl Hk1 Hk2) end;
      [ lia | icx_cbn; lia | lia | lia | (icx_cbn; zreg) .. | exact Hin | | ].
    +
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_LEAVEX_HD_T in *.
      zstep Rfd.
      zstep Rfd.
      zsetreg (8 * (n - cin)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; rewrite ?Z.mod_small by lia; lia).
      zstep Rfd. zext32.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_hd _ _ lf cf HEAD flags n hold' j' SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(intros _; left; reflexivity)
                    ltac:(cbn; lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia)) as SI1.
      clear H16. open_kmem KM0. destruct SAT as [Hmode SREST].
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KL Rx Mx _ ret lf cf SI1) end.
      * unfold s_regs_leave, hd_st; icx_cbn; zkeys; split_conj; try zreg. all: zkept.
      * exact STD.
      * unfold hd_st; split; [exact Hmode | exact SREST].
      * exact SLO.
      * sbk.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_HEAD_BODY_T in *.
      eapply (head_main_t (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' [] M
                (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf (cin + Z.of_nat k) hold' j' CX0 Hh Hfin eq_refl SI0);
        [ (icx_cbn; first [zreg | zkeys; cbv [zget_l alookup]; first [zkept | lia]]) .. | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
Qed.

Theorem arm_HEAD_t : arm_stmt L_HEAD HEAD.
Proof. intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K. eapply head_body_t; eassumption. Qed.

End WITH_ADLER_NULL.
End T_Head.

