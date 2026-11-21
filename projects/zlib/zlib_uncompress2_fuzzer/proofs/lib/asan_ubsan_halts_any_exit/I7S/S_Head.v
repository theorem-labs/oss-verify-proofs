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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require Import SBase S_Type S_HeadA.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_HEAD_LOOP : Z := 87056.
Definition L_HEAD_BODY : Z := 89504.
Definition L_HEAD_WERR : Z := 93320.
Definition L_HEAD_FIN : Z := 93484.

End FXG.
Ltac zbr_hyp_with bv F E D :=
  eapply (zu_branch_b bv); [zexact F | zexact E | zexact D | zhalted | znorm; first [assumption | zcond_tac] | ];
  zcbv_iota; znorm.
Tactic Notation "zbrH" tactic0(fd) constr(bv) :=
  let pc := zpc in fd pc ltac:(fun F E D => zbr_hyp_with bv F E D).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition fp_head (u p : Z) : list (Z * Z) := [(p + 8, 4); (p + 28, 20); (u + 48, 8); (u + 96, 8)].

Section WITH_ADLER_NULL.
Hypothesis ADLN : adler32_null_spec_s.

Lemma head_main : forall cx fin MD T M0 Rb l M st lf cf (cin1 hold1 bits1 : Z),
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = HEAD -> sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -224 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kA0 = c_u cx -> zget_l Rb l kA1 = 0 ->
  zget_l Rb l kS6 = c_p cx + 168 -> zget_l Rb l kT6 = -16180 -> zget_l Rb l kT4 = 30 -> zget_l Rb l kS9 = JTAB_ADDR ->
  zget_l Rb l kS4 = 16209 -> zget_l Rb l kA2 = 5 ->
  zget_l Rb l kS2 = c_n cx - cin1 -> zget_l Rb l kS3 = c_ob cx + t_cout st -> zget_l Rb l kRA = c_osz cx - t_cout st ->
  zget_l Rb l kS11 = c_q cx + cin1 -> zget_l Rb l kS10 = c_q cx + cin1 ->
  zget_l Rb l kS7 = hold1 -> zget_l Rb l kS8 = bits1 ->
  t_cin st <= cin1 <= c_n cx -> 16 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
  8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_HEAD_BODY (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf cin1 hold1 bits1 CX Hh Hfin Hm SI
         LSP LGP LTP L9 LA0 LA1 LRA LT6 LT4 LT5 L5 LA2 L8 L3 L2 L10 L11 L7 L0 Hc1 Hb1 Hh1 Hbc1 HW1 KM K.
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
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q104 & Q96 & _ & Q72 & _).
  pose proof (rom_mod31_u64 M ROM) as H31.
  pose proof SREST as SR'. unfold st_rest in SR'. icx_cbn. dand SR' as (_ & H24 & _).
  clear ROM Wob Ww FRM CST HK Hmode SREST SRET SOUT Hlens Hcodes Hin.
  zkeysb. unfold L_HEAD_BODY, L_HEAD_WERR, L_HEAD_FIN, L_BADMSG_S11 in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (mpostL_stable R_segs M (fp_head u p) ltac:(unfold fp_head; ranges_ok_tac)) as HSTh.
  assert (HAGh : framed (fun X => mpostL R_segs M X (fp_head u p)) M) by (apply mpostL_refl).
  unfold fp_head in HSTh, HAGh.
  assert (EXIT : forall (ra1 : bool) RX Mq m' flags' hold' bits',
    sinv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                m' flags' cin1 hold' bits') lf cf ->
    meas (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                m' flags' cin1 hold' bits') <
    meas (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ->
    zget RX kSP = u + -224 -> zget RX kGP = K0 kGP -> zget RX kTP = K0 kTP -> zget RX kS0 = p ->
    zget RX kA0 = u -> zget RX kS4 = 16209 -> zget RX kS10 = q + cin1 -> zget RX kS2 = n - cin1 ->
    zget RX kS3 = ob + cout -> zget RX kS1 = osz - cout -> zget RX kS7 = hold' -> zget RX kS8 = bits' ->
    zget RX kS6 = p + 168 -> zget RX kS9 = 67008 -> (ra1 = true -> zget RX kA1 = 0) ->
    mem_u32 R_segs Mq (p + 8) m' -> mem_u32 R_segs Mq (p + 28) flags' ->
    mpostL R_segs M Mq [(p + 8, 4); (p + 28, 20); (u + 48, 8); (u + 96, 8)] ->
    realizes R_segs (zcfg R_segs (if ra1 then L_RELOAD_RA else L_RELOAD_A1) (zupd RX []) Mq MD) T).
  { intros ra1 RX Mq m' flags' hold' bits' SI1 MB1 E3 E4 E5 E26 E11 E22 E28 E25 E20 E19 E24 E9 E21 E27 EA1 Hm8 Hf24 HPq.
    clear HST HAG Wstk Wp HSTh HAGh H48 H56 H31 Q104 Q96 Q72 H24.
    open_kmem KM0. open_std STD. destruct SAT as [Hmode SREST]. clear Hmode.
    unfold st_rest in SREST. icx_cbn.
    dand SREST as (H12 & _ & H64 & H68 & H92 & H96 & H100 & H104 & H112 & H120 & H124 & H128 & H132 & H136 & H140 & H144).
    fp_frame_from HP0.
    cbv [N_LENS N_CODES] in Hlens, Hcodes.
    zreattachL HPq.
    destruct ra1;
      [ change (if true then L_RELOAD_RA else L_RELOAD_A1) with L_RELOAD_RA;
        eapply (KRRA RX Mq (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                              m' flags' cin1 hold' bits') lf cf SI1 MB1)
      | change (if false then L_RELOAD_RA else L_RELOAD_A1) with L_RELOAD_A1;
        eapply (KRA1 RX Mq (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                              m' flags' cin1 hold' bits') lf cf SI1 MB1) ].
    1,3: unfold s_regs_reload, hd_st; icx_cbn; zkeys; split_conj; first [assumption | intros; discriminate | solve [intros _; apply EA1; reflexivity] | zreg].
    all: unfold k_mem; split_conj;
      [ close_std
      | unfold st_at, st_rest, hd_st; icx_cbn; split_conj; assumption
      | unfold s_ret, hd_st in *; icx_cbn; assumption | unfold s_out, hd_st in *; icx_cbn; assumption
      | assumption | assumption | exact HAG ]. }
  zstep Rfd. zlit.
  zbr Rfd true.
  tstep1 Rfd.
  zbr Rfd true.
  zstep Rfd. zlit.
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
  destruct (zcond BC_LTU pr 595056260442243601) eqn:Hc31.
  2: {
    zbrH Rfd false.
    zstep Rfd. zstep Rfd. zlit.
    zstep Rfd.
    pose proof (sinv_hd _ _ lf cf BAD flags cin1 hold1 bits1 SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(intros _; right; reflexivity)
                  ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  BAD flags cin1 hold1 bits1 ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MB1.
    clear HSTh HAGh H56 Q104 Q96 Q72 H24 EXIT. open_kmem KM0. destruct SAT as [Hmode SREST].
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (KB11 R' Mx (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                                  HEAD flags cin1 hold1 bits1) lf cf SI1 MB1) end.
    - unfold s_regs_disp, s_fix, s_vars, hd_st; icx_cbn; zkeys; split_conj; zreg.
    - lazymatch goal with |- 0 <= ?x < _ => assert (EA2 : x = 66636) by zreg; rewrite EA2 end. lia.
    - unfold k_mem, hd_st; icx_cbn; split_conj;
        [ exact STD | split; [exact Hmode | exact SREST] | exact SRET | exact SOUT | exact Hlens | exact Hcodes | exact HP0 ]. }
  zbrH Rfd true.
  zstep Rfd.
  zstep Rfd.
  zgenreg mth.
  zstep Rfd.
  destruct (zcond BC_NE mth 8) eqn:Hcm.
  {
    zbrH Rfd true.
    clear H56.
    zstep Rfd. zstep Rfd. zlit.
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    pose proof (sinv_hd _ _ lf cf BAD flags cin1 hold1 bits1 SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(intros _; right; reflexivity)
                  ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  BAD flags cin1 hold1 bits1 ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?Mx _) _ => apply (EXIT false RX Mx BAD flags hold1 bits1 SI1 MB1) end;
      first [zreg | assumption | intros; discriminate | exact HAGh]. }
  zbrH Rfd false.                     (* bne a0,a1: the method is 8 *)
  (* 1.4 (the HEAD rider): len = BITS(4) + 8 is checked against 15 first, then against wbits only when wbits != 0,
     and wbits is set to len only when it was 0 (1.3.1 set it before the check). Here wbits = 15, so the state is as at
     1.3.1; only the instruction order moved. *)
  zstep Rfd.                          (* 16bec srli a1,s7,4 *)
  zsetreg (Z.shiftr hold1 4) ltac:(rewrite (Z.mod_small hold1) by lia; reflexivity).
  zstep Rfd.                          (* 16bf0 andi a0,a1,15 *)
  zgenreg len4.
  zstep Rfd.                          (* 16bf4 li a2,7 *)
  pose proof (shiftr_lt_pow2 hold1 bits1 4 ltac:(lia) Hh1) as Hsh4.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (WERR : forall RW,
    zget RW kSP = u + -224 -> zget RW kGP = K0 kGP -> zget RW kTP = K0 kTP -> zget RW kS0 = p ->
    zget RW kS4 = 16209 -> zget RW kS2 = n - cin1 -> zget RW kS3 = ob + cout -> zget RW kS1 = osz - cout ->
    zget RW kS10 = q + cin1 -> zget RW kS8 = bits1 -> zget RW kA1 = Z.shiftr hold1 4 ->
    zget RW kS6 = p + 168 -> zget RW kS9 = 67008 ->
    realizes R_segs (zcfg R_segs L_HEAD_WERR (zupd RW []) Mc MD) T) end.
  { intros RW. intros. unfold L_HEAD_WERR. zkeys. clear H56.
    tstep1 Rfd.                       (* addiw s8,s8,-4 *)
    zstep Rfd. zstep Rfd. zlit.       (* auipc; addi: the message *)
    tstep1 Rfd.                       (* ld a0,96(sp) *)
    tstep1 Rfd.                       (* sd a2,48(a0) *)
    tstep1 Rfd.                       (* ld s4,72(sp) *)
    tstep1 Rfd.                       (* sw s4,8(s0) *)
    zstep Rfd.                        (* mv s7,a1 *)
    zstep Rfd.                        (* j *)
    pose proof (sinv_hd _ _ lf cf BAD flags cin1 (Z.shiftr hold1 4) (bits1 - 4) SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity)
                  ltac:(intros _; right; reflexivity)
                  ltac:(cbn; lia) ltac:(lia) ltac:(exact Hsh4) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  BAD flags cin1 (Z.shiftr hold1 4) (bits1 - 4) ltac:(left; cbn; lia)) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?Mx _) _ => apply (EXIT false RX Mx BAD flags (Z.shiftr hold1 4) (bits1 - 4) SI1 MB1) end;
      first [zreg | assumption | intros; discriminate | exact HAGh]. }
  destruct (zcond BC_LTU 7 len4) eqn:Hc7.
  { zbrH Rfd true.                    (* bltu a2,a0: len > 15 *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?RW _ _) _ => apply (WERR RW); zreg end. }
  zbrH Rfd false.
  tstep1 Rfd.                         (* 16bfc lw a3,68(s0): wbits *)
  zstep Rfd.                          (* 16c00 addi a2,a0,8 *)
  zgenreg lenp8.
  zbr Rfd false.                      (* 16c04 beqz a3: wbits = 15 *)
  destruct (zcond BC_GEU 15 lenp8) eqn:Hc15.
  2: { zbrH Rfd false.                (* bgeu a3,a2 not taken: len > wbits *)
       lazymatch goal with |- realizes _ (zcfg _ _ ?RW _ _) _ => apply (WERR RW); zreg end. }
  zbrH Rfd true.                      (* bgeu a3,a2 *)
  zbr Rfd true.                       (* 16c58 bnez a3: wbits kept *)
  clear WERR Hsh4.
  zstep Rfd.                          (* li a1,256 *)
  zstep Rfd.                          (* sllw a0,a1,a0 *)
  zgenreg dmax.
  tstep1 Rfd.                         (* sw zero,28(s0) *)
  tstep1 Rfd.                         (* sw a0,32(s0) *)
  zstep Rfd. zstep Rfd. zstep Rfd.   (* li a0; li a1; li a2 *)
  zstep Rfd.                          (* jal adler32 *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R ?lc') ?Mx _) _ =>
    eapply (ADLN R lc' Mx MD T _ Hh) end; [zreg | zreg | zreg | reflexivity |].
  intros R2 E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
  zimps. zkeys.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zgenreg hs.
  zstep Rfd. zlit.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (FIN : forall RF m', (m' = DICTID \/ m' = TYPE) ->
    zget RF kSP = u + -224 -> zget RF kGP = K0 kGP -> zget RF kTP = K0 kTP -> zget RF kS0 = p ->
    zget RF kS4 = 16209 -> zget RF kS2 = n - cin1 -> zget RF kS3 = ob + cout -> zget RF kS1 = osz - cout ->
    zget RF kS10 = q + cin1 -> zget RF kA0 = m' ->
    zget RF kS6 = p + 168 -> zget RF kS9 = 67008 ->
    realizes R_segs (zcfg R_segs L_HEAD_FIN (zupd RF []) Mc MD) T) end.
  { intros RF m' Hm'. intros. unfold L_HEAD_FIN. zkeys.
    assert (Rm' : 0 <= m' < 4294967296) by (destruct Hm' as [-> | ->]; cbv [DICTID TYPE]; lia).
    zstep Rfd. zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    pose proof (sinv_hd _ _ lf cf m' 0 cin1 0 0 SI0 eq_refl ltac:(destruct Hm' as [-> | ->]; (first [solve [zkeep_section; tauto] | tauto])) ltac:(right; reflexivity)
                  ltac:(intros E; discriminate E)
                  ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  m' 0 cin1 0 0 ltac:(left; cbn; lia)) as MB1.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?Mx _) _ => apply (EXIT true RX Mx m' 0 0 0 SI1 MB1) end;
      first [zreg | assumption | intros _; zreg | exact HAGh]. }
  destruct (zcond BC_GE hs 0) eqn:Hcs.
  - zbrH Rfd true.
    zstep Rfd. zlit.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RF _ _) _ => apply (FIN RF TYPE); [right; reflexivity | zreg ..] end.
  - zbrH Rfd false.
    zstep Rfd. zlit.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RF _ _) _ => apply (FIN RF DICTID); [left; reflexivity | zreg ..] end.
Qed.


Lemma head_loop : forall (k : nat) cx fin MD T Rb l M (cinj holdj j : Z),
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_S cx ->
  16 - 8 * Z.of_nat k <= j < 24 - 8 * Z.of_nat k -> (1 <= k <= 2)%nat -> 0 <= j ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS8 = j -> zget_l Rb l kA3 = j ->
  zget_l Rb l kS11 = c_q cx + cinj -> zget_l Rb l kS2 = c_n cx - cinj -> zget_l Rb l kS7 = holdj ->
  mem_arr 1 R_segs M (c_q cx) (c_n cx) fin ->
  (forall R' hold' j',
     zget R' kS11 = c_q cx + c_n cx -> zget R' kS2 = 0 -> zget R' kS7 = hold' -> zget R' kS8 = j' ->
     j' = j + 8 * (c_n cx - cinj) -> 0 <= hold' < 2 ^ j' -> c_n cx - cinj < Z.of_nat k ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kA2 = zget_l Rb l kA2 ->
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
     zget R' kA2 = zget_l Rb l kA2 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kS3 = zget_l Rb l kS3 ->
     zget R' kS4 = zget_l Rb l kS4 ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kT4 = zget_l Rb l kT4 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kT6 = zget_l Rb l kT6 ->
     realizes R_segs (zcfg R_segs L_HEAD_BODY (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_HEAD_LOOP (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M cinj holdj j Hh Hfin CXl Hj Hk Hj0 Hc Hhj Hjc L9 L0 LA3 L10 L8 L7 Hin KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S] in CXl; destr_conj CXl.
  zkeysb. unfold L_HEAD_LOOP, L_HEAD_BODY, L_LEAVE_LD in *. pose proof two64_eq as TW64.
  assert (Hj24 : 2 ^ j <= 2 ^ 23) by (apply Z.pow_le_mono_r; lia). change (2 ^ 23) with 8388608 in Hj24.
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

Lemma head_body : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = HEAD -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_HEAD (zupd Rb l) M MD) T.
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
  clear ROM Wob Ww FRM CST HK Hmode SREST SRET SOUT Hlens Hcodes.
  zkeysb. unfold L_HEAD, L_HEAD_LOOP, L_HEAD_BODY, L_LEAVE_LD in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  tstep1 Rfd.
  zbr Rfd false.
  zstep Rfd.
  destruct (Z_lt_dec 15 bits) as [Hb16 | Hb16].
  - zbr Rfd true.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (head_main (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf cin hold bits CX0 Hh Hfin eq_refl SI0) end;
      [ (icx_cbn; zreg) .. | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
  - zbr Rfd false.
    zstep Rfd.
    assert (Hkk : exists k : nat, 16 - 8 * Z.of_nat k <= bits < 24 - 8 * Z.of_nat k /\ (1 <= k <= 2)%nat).
    { exists (Z.to_nat (2 - bits / 8)).
      rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (head_loop k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' Mx cin hold bits Hh Hfin CXl Hk1 Hk2) end;
      [ lia | icx_cbn; lia | lia | lia | (icx_cbn; zreg) .. | exact Hin | | ].
    +
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_LEAVE_LD in *.
      pose proof (sinv_hd _ _ lf cf HEAD flags n hold' j' SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(intros _; left; reflexivity)
                    ltac:(cbn; lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia)) as SI1.
      clear H16. open_kmem KM0. destruct SAT as [Hmode SREST].
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KLL Rx Mx _ lf cf SI1) end.
      * unfold s_regs_leave_ld, hd_st; icx_cbn; zkeys; split_conj; try zreg; zkept.
      * exact STD.
      * unfold hd_st; split; [exact Hmode | exact SREST].
      * exact SRET.
      * exact SOUT.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_HEAD_BODY in *.
      eapply (head_main (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' [] M
                (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf (cin + Z.of_nat k) hold' j' CX0 Hh Hfin eq_refl SI0);
        [ (icx_cbn; first [zreg | zkeys; cbv [zget_l alookup]; first [zkept | lia]]) .. | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
Qed.

Theorem arm_HEAD_s : arm_stmt L_HEAD HEAD.
Proof. intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K. eapply head_body; eassumption. Qed.

End WITH_ADLER_NULL.
End FXG.
