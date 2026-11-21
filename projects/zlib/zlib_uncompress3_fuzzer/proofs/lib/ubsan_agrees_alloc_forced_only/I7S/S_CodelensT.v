(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItCovIface InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require Import ItBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require Import SBase.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require Import S_Type S_MatchL S_DistL S_LenL S_LenF S_ClDefs.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_LENS_RET : Z := 89272.
Definition L_DTAB : Z := 89800.
Definition L_DISTS_RET : Z := 89852.
Definition L_TBLERR : Z := 89868.
Definition L_CL_OK : Z := 91792.

Lemma mem_u64_eqv {RCa1 : RunCtx}  : forall M a v v', v = v' -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v'.
Proof. intros M a v v' <- H. exact H. Qed.
Lemma mem_u64_mod {RCa1 : RunCtx}  : forall M a v, mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a (v mod 18446744073709551616).
Proof. intros M a v H. unfold mem_u64 in *. change 18446744073709551616 with two64. rewrite Z_to_le_bytes_mod by lia_std. exact H. Qed.

Lemma le_cell2_range : forall bs i, 0 <= le_cell 2 bs i < 65536.
Proof.
  intros bs i. unfold le_cell.
  set (l := firstn (Z.to_nat 2) (skipn (Z.to_nat (2 * i)) bs)).
  pose proof (bytes_le_to_Z_bound l) as R. pose proof (bytes_le_to_Z_nonneg l) as R0.
  assert (L : (length l <= 2)%nat) by (subst l; rewrite length_firstn; cbn; lia_std).
  assert (P : 2 ^ (8 * Z.of_nat (length l)) <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia_std).
  change (2 ^ 16) with 65536 in P. lia_std.
Qed.
Lemma work_arr {RCa1 : RunCtx}  : forall M p, mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> 0 <= p -> p + 7176 <= two64 ->
  exists wf, mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 wf /\ (forall i, 0 <= i < 288 -> 0 <= wf i < 65536).
Proof.
  intros M p W Hp1 Hp2.
  destruct (mem_wr_readable (run_segments R_segs rc_inp rc_sp rc_mb) wr_rd_R M (p + 808) 576 ltac:(eapply mem_wr_sub; [exact W | lia_std | lia_std]) ltac:(lia_std)) as [bs [A B]].
  exists (le_cell 2 bs). split.
  - apply (mem_arr_of_bytes (run_segments R_segs rc_inp rc_sp rc_mb) 2 M (p + 808) 288 bs A); try lia_std.
  - intros i _. apply le_cell2_range.
Qed.

Lemma rom_it_tabs {RCa1 : RunCtx}  : forall M, rom_ok M ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M LBASE_ADDR 31 (arr_get lbase_a) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M LEXT_ADDR 31 (arr_get lext_a) /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M DBASE_ADDR 32 (arr_get dbase_a) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M DEXT_ADDR 32 (arr_get dext_a).
Proof.
  intros M H. cbv [LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR]. split_conj.
  - eapply mem_arr_ext; [apply rom_lbase_arr; exact H | intros; apply lbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_lext_arr; exact H | intros; apply lext_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dbase_arr; exact H | intros; apply dbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dext_arr; exact H | intros; apply dext_f_model; assumption].
Qed.

Lemma i_frame_slots {RCa1 : RunCtx}  : forall cx M, i_frame cx M ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -208) (c_p cx + 1384) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -192) (c_p cx + 160) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -216) (c_p cx + 136) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -200) (c_p cx + 808) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -128) (c_u cx) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -120) 0 /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -136) (-16180) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -224) (c_p cx + 140).
Proof. intros cx M H. unfold i_frame in H. destr_conj H. split_conj; assumption. Qed.

Ltac ist_cbn := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in *.

Lemma rng_dc : forall cx st lf cf, sinv cx st lf cf -> match t_dc st with CDyn o => 0 <= o /\ o <= N_CODES | _ => True end.
Proof. intros cx st lf cf (R & _). unfold RNG in R. destr_conj R. assumption. Qed.

Lemma pow2_pos : forall b, 0 <= b -> 0 < 2 ^ b.
Proof. intros b Hb. apply Z.pow_pos_nonneg; lia_std. Qed.

Definition st_tab (st : ist) (m rv lb : Z) (dc : codeptr) (db nx : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) rv
      (t_length st) (t_offset st) (t_extra st) (CDyn 0) dc lb db
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) nx (t_whave st) (t_wnext st).

Lemma sinv_cl_bad : forall cx st lf cf cf' rv lb dc db nx,
  sinv cx st lf cf -> t_mode st = CODELENS -> 0 <= rv < 18446744073709551616 ->
  0 <= lb < 4294967296 -> 0 <= db < 4294967296 ->
  match dc with CDyn o => 0 <= o /\ o <= N_CODES | _ => True end -> 0 <= nx -> nx <= N_CODES ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_tab st BAD rv lb dc db nx) lf cf' /\ meas cx (st_tab st BAD rv lb dc db nx) < meas cx st.
Proof.
  intros cx st lf cf cf' rv lb dc db nx (R & W & P & Mo) Hm Hrv Hlb Hdb Hdc Hnx1 Hnx2 Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc0 lb0 db0 ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_tab, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  assert (Mf : flags = -1 -> (CODELENS = HEAD \/ CODELENS = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split; [unfold PROG in P; icx_cbn; prog_transfer P |]]] |].
  - clear W P Mf. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear W P. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_cl_len_ : forall cx st lf cf cf' lb o2 db nx,
  sinv cx st lf cf -> t_mode st = CODELENS ->
  1 <= lb -> lb <= 15 -> 1 <= db -> db <= 15 -> 0 <= o2 -> o2 <= nx -> nx <= N_CODES ->
  tab_ok LENS (rdc cf' (CDyn 0)) lb o2 = true -> tab_ok DISTS (rdc cf' (CDyn o2)) db (nx - o2) = true ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_tab st LEN_ 0 lb (CDyn o2) db nx) lf cf' /\ meas cx (st_tab st LEN_ 0 lb (CDyn o2) db nx) < meas cx st.
Proof.
  intros cx st lf cf cf' lb o2 db nx (R & W & P & Mo) Hm Hlb1 Hlb2 Hdb1 Hdb2 Ho1 Ho2 Hnx TL TD Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc0 lb0 db0 ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_tab, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  assert (Mf : flags = -1 -> (CODELENS = HEAD \/ CODELENS = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split; [unfold PROG in P; icx_cbn; prog_transfer P |]]] |].
  - clear W P Mf TL TD. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear W P. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [mode_vacuous |].
    split; [mode_vacuous |].
    split; [intros _; unfold tables_live; cbn [t_lc t_dc t_lb t_db t_nx]; cbv [N_CODES]; split_conj; try reflexivity; try assumption; lia_std |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Section CLT.
Context {RCa1 : RunCtx}.
Hypothesis ITABLE : itable_spec_s.
Hypothesis IFAST : ifast_spec_s.

Lemma lenu_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LEN_ -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEN_ (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof (sinv_len_ cx st lf cf SI Hmd) as [SI1 ME1].
  open_kmem KM. destruct SAT as [Hmode SREST].
  dand RG as (FIX & VARS & G27).
  pose proof CX as CX0. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold s_fix, s_vars in FIX, VARS. icx_cbn. destr_conj FIX. destr_conj VARS.
  open_std STD. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold st_le in SI1, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1, ME1.
  zkeysb. unfold L_LEN_, L_LEN in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.
  clear Hmode.
  tstep1 Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (len_s IFAST _ fin MD T M0 Rx lx Mx
              (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI1) end.
  - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [LEN]; assumption | exact SREST | exact SRET | exact SOUT | exact HAG].
  - eapply KALL_mono; [| exact K]. clear - ME1. lia.
Qed.

Local Ltac itable_pre SEP AL Wstk LF15 :=
  first [ lazymatch goal with
       | |- zget_l _ _ _ = _ => cbv [cty o_lens o_next o_work o_lenbits o_distbits]; zreg
       | |- Z.land _ _ = _ => reflexivity
       | |- _ \/ _ => first [ left; cbv [o_lenbits]; reflexivity | right; cbv [o_distbits]; reflexivity ]
       | |- ZSEP _ => unfold ZSEP; pose proof (sep_p_rom _ _ SEP) as D; cbn [c_p] in D; cbv [STATE_SIZE ROM_LO_ALL DEXT_ADDR ROMHI_S] in D |- *; clear - D; lia
       | |- _ mod 16 = 0 => first [ exact (proj1 (proj2 AL)) | apply mod0_add; [lia | exact (proj1 AL) | reflexivity] ]
       | |- mem_wr _ _ _ _ => first [ assumption | cbv [FR_IT]; eapply mem_wr_sub; [exact Wstk | lia | lia] ]
       | |- mem_arr _ _ _ _ _ _ => assumption
       | |- mem_u64 _ _ _ _ => first [ assumption | eapply mem_u64_eqv; [| eassumption]; cbv [o_codes]; lia ]
       | |- mem_u32 _ _ _ _ => assumption
       | |- forall i : Z, _ -> _ <= _ < _ => assumption
       | |- _ = CODES -> _ => intros X; discriminate X
       | |- _ = DISTS -> _ => first [ intros X; discriminate X | intros _; lia ]
       | |- forall s : Z, _ -> _ <= 15 => intros s Hs; first [ replace (0 + s) with s by lia | idtac ]; apply LF15; lia
       | |- forall R' M', _ => idtac
       | |- _ => cbv [FRA STATE_SIZE N_LENS N_CODES FR_IT ENOUGH_LENS ENOUGH_DISTS DEXT_ADDR]; cbn [it_room]; cbv [ENOUGH_LENS ENOUGH_DISTS]; first [assumption | lia]
       end | match goal with |- ?G => idtac "ITFAIL" G end ].

Theorem cldone_s : cldone_stmt.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hhave SI RG KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (MC : t_mode st = CODELENS -> 257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            t_shave st <= t_nlen st + t_ndist st /\ (forall i, 0 <= i < t_shave st -> lf i <= 15) /\ ctable_live st cf) by mode_get MODE_.
  specialize (MC Hm). dand MC as (Hnl1 & Hnl2 & Hnd1 & Hnd2 & Hsh & Hlf15 & _). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  assert (LF15 : forall i, 0 <= i < nlen + ndist -> lf i <= 15) by (intros i Hi; apply Hlf15; lia). clear Hlf15 Hsh Hhave.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  match goal with H : forall i, _ -> 0 <= cf i < 4294967296 |- _ => rename H into Rcf end.
  pose proof (rng_dc _ _ _ _ SI0) as Hdc. cbn [t_dc] in Hdc. cbv [N_CODES] in Hdc.
  unfold s_regs_cld, s_fix, s_vars in RG. icx_cbn. destr_conj RG.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (i_frame_slots _ _ FRM) as FS. icx_cbn. cbv [JTAB_ADDR] in FS.
  dand FS as (S16 & S32 & S8 & S24 & S96 & S104 & S88 & S0).
  unfold st_rest in SREST. icx_cbn.
  dand SREST as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
  pose proof SRET as SRET'. unfold s_ret in SRET'. icx_cbn. clear SRET.
  assert (Rdb : 0 <= db < 4294967296) by lia. pose proof (Rlf 256 ltac:(lia)) as R256.
  prune_rng.
  zkeysb. unfold L_CL_DONE, L_LENS_RET, L_DTAB, L_DISTS_RET, L_TBLERR, L_CL_OK, L_BADMSG_S10, L_RELOAD_A1, L_ITABLE, L_LEN_ in *.
  cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  tstep1 Rfd.
  destruct (Z.eq_dec (lf 256) 0) as [Hz | Hnz].
  {
    zbr Rfd true.
    zstep Rfd. zstep Rfd. zlit.
    zstep Rfd.
    pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
    cbn [t_mode] in MB. change (rank CODELENS) with 20 in MB.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KB10 Rx Mx (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf
                (sinv_bad_of _ _ _ _ SI0)) end.
    - clear - MB. lia.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - lazymatch goal with |- 0 <= ?x < _ => assert (EA2 : x = 66659) by zreg; rewrite EA2 end. lia.
    - unfold k_mem, st_at, st_rest, s_ret, s_out; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std.
      all: first [exact HAG | unfold s_out in SOUT; icx_cbn; exact SOUT]. }
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    destruct (work_arr Mx p Wp ltac:(lia) ltac:(rewrite TW64; lia)) as (wf & Hwork & Rwf);
    dand (rom_it_tabs Mx ROM) as (RT1 & RT2 & RT3 & RT4) end.
  lazymatch goal with H120 : mem_u32 _ ?Mx (p + 136) 9, H144 : mem_u64 _ ?Mx (p + 160) (p + 1384) |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    rename H120 into C120n; rename H144 into C144n end.
  pose proof ITABLE as ITABLE1. unfold itable_spec_s, itable_spec_at in ITABLE1.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ITABLE1 Rx lx Mx MD T LENS p 0 nlen 0 9 (p + 136) (u + -224) 89272 zc lf cf wf Hh) end.
  all: itable_pre SEP AL Wstk LF15.
  clear ITABLE1.
  intros R' M' cf' wf' Hrv Hret3 Hcf' Hwf' Rcf' Rwf' HP Hlens' Hcodes' Hwork' Hnext' Hbits' KE.
  set (r := inflate_table _ _ _ _ _ _ _ _) in *.
  assert (BR : it_ret r = 0 ->
     tab_ok LENS (rdc cf' (CDyn 0)) (it_bits r) (it_table r - 0) = true /\ 1 <= it_bits r <= 15 /\
     0 + 2 ^ it_bits r <= it_table r <= 0 + it_room LENS /\ (forall i, 0 <= i < N_CODES -> ~ (0 <= i < it_table r) -> cf' i = cf i)).
  { intros Hr0. apply (tab_ok_of_itable LENS lf cf wf cf' 0 nlen 0 9); cbv [N_LENS N_CODES]; cbn [it_room]; cbv [ENOUGH_LENS]; try assumption; try lia.
    - intros s Hs. replace (0 + s) with s by lia. apply LF15. lia.
    - intros X; discriminate X.
    - intros X; discriminate X. }
  assert (FS1 : it_ret r <> 0 -> it_table r = 0 /\ it_bits r = 9).
  { intros Hne. exact (inflate_table_fail_shape LENS (arr_init N_LENS lf) 0 nlen (arr_init N_CODES cf) 0 9 (arr_init N_WORK wf) Hne). }
  clearbody r.
  unfold kept_eq in KE. zkeys. destr_conj KE. zimps.
  clear Hwork RT1 RT2 RT3 RT4 C120n C144n Hcodes Hlens.
  unfold it_fp in HP. cbv [o_next o_work o_codes o_lenbits N_WORK N_CODES FR_IT] in HP. zreattachL HP.
  cbv [o_lens o_codes o_work o_next o_lenbits N_LENS N_CODES N_WORK] in Hlens', Hcodes', Hwork', Hnext', Hbits'.
  cbv [N_CODES] in Rcf', BR. cbv [N_WORK] in Rwf'. cbn [it_room] in BR. cbv [ENOUGH_LENS] in BR.
  destruct (Z.eq_dec (it_ret r) 0) as [Hr0 | Hnz1].
  2: {
    destruct (FS1 Hnz1) as [Ht0 Hb9]. clear BR FS1.
    assert (Hrm : exists rm, it_ret r mod 18446744073709551616 = rm /\ rm <> 0 /\ 0 <= rm < 18446744073709551616).
    { exists (it_ret r mod 18446744073709551616). split; [reflexivity|].
      destruct Hret3 as [E | [E | E]]; [exfalso; exact (Hnz1 E) | rewrite E | rewrite E];
        [ rewrite Z.mod_small by lia_std; lia_std
        | replace ((-1) mod 18446744073709551616) with 18446744073709551615 by reflexivity; lia_std ]. }
    dand Hrm as (rm & Hrm & Hrm0 & Hrm1).
    zbr Rfd false.
    zstep Rfd.
    lazymatch goal with H : mem_u64 _ ?Mx (u + -160) _ |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      apply mem_u64_mod in H; rewrite Hrm in H end.
    zstep Rfd. zstep Rfd. zlit.
    zstep Rfd.
    zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_cl_bad _ _ lf cf cf' rm (it_bits r) dc db (it_table r) SI0 eq_refl (conj (proj1 Hrm1) (proj2 Hrm1))
                  ltac:(lia) ltac:(lia) Hdc ltac:(lia) ltac:(cbv [N_CODES]; lia) ltac:(cbv [N_CODES]; exact Rcf')) as [SI1 ME1].
    unfold st_tab in SI1, ME1. ist_cbn.
    rewrite Ht0 in *. rewrite Hb9 in *.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KRA1 Rx Mx _ lf cf' SI1 ME1) end.
    + unfold s_regs_reload; icx_cbn; zkeys; split_conj; try zreg. all: intros C; discriminate C.
    + unfold k_mem, st_at, st_rest, s_ret, s_out; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [BAD]; assumption | exact HAG | unfold s_out in SOUT; icx_cbn; exact SOUT | eapply mem_u64_eqv; [| eassumption]; lia ]. }
  dand (BR Hr0) as (TOK1 & Hb15 & Htab1 & Hout1). clear BR FS1.
  rewrite Hr0 in Hrv. rewrite Z.sub_0_r in TOK1.
  pose proof (pow2_pos (it_bits r) ltac:(lia)) as Hpw1.
  zbr Rfd true.
  zstep Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zsetreg (2 * nlen) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 1) with 2; rewrite ?Z.mod_small by lia; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    dand (rom_it_tabs Mx ROM) as (RT1 & RT2 & RT3 & RT4) end.
  lazymatch goal with H124 : mem_u32 _ ?Mx (p + 140) 6, H112 : mem_u64 _ ?Mx (p + 128) _ |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    rename H124 into C124n; rename H112 into C112n end.
  pose proof ITABLE as ITABLE2. unfold itable_spec_s, itable_spec_at in ITABLE2.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ITABLE2 Rx lx Mx MD T DISTS p nlen ndist (it_table r) 6 (p + 140) (u + -224) 89852 zc lf cf' wf' Hh) end.
  all: itable_pre SEP AL Wstk LF15.
  clear ITABLE2.
  intros R'' M'' cf'' wf'' Hrv2 Hret32 Hcf'' Hwf'' Rcf'' Rwf'' HP2 Hlens'' Hcodes'' Hwork'' Hnext'' Hbits'' KE2.
  set (r2 := inflate_table _ _ _ _ _ _ _ _) in *.
  assert (BR2 : it_ret r2 = 0 ->
     tab_ok DISTS (rdc cf'' (CDyn (it_table r))) (it_bits r2) (it_table r2 - it_table r) = true /\ 1 <= it_bits r2 <= 15 /\
     it_table r + 2 ^ it_bits r2 <= it_table r2 <= it_table r + it_room DISTS /\
     (forall i, 0 <= i < N_CODES -> ~ (it_table r <= i < it_table r2) -> cf'' i = cf' i)).
  { intros Hr0'. apply (tab_ok_of_itable DISTS lf cf' wf' cf'' nlen ndist (it_table r) 6); cbv [N_LENS N_CODES]; cbn [it_room]; cbv [ENOUGH_DISTS]; try assumption; try lia.
    - intros s Hs. apply LF15. lia.
    - intros X; discriminate X. }
  assert (FS2 : it_ret r2 <> 0 -> it_table r2 = it_table r /\ it_bits r2 = 6).
  { intros Hne. exact (inflate_table_fail_shape DISTS (arr_init N_LENS lf) nlen ndist (arr_init N_CODES cf') (it_table r) 6 (arr_init N_WORK wf') Hne). }
  clearbody r2.
  unfold kept_eq in KE2. zkeys. destr_conj KE2. zimps.
  clear RT1 RT2 RT3 RT4 C124n Hcodes' Hlens' Hwork' Hnext'.
  unfold it_fp in HP2. cbv [o_next o_work o_codes o_distbits N_WORK N_CODES FR_IT] in HP2. zreattachL HP2.
  cbv [o_lens o_codes o_work o_next o_distbits N_LENS N_CODES N_WORK] in Hlens'', Hcodes'', Hwork'', Hnext'', Hbits''.
  cbv [N_CODES] in Rcf'', BR2. cbn [it_room] in BR2. cbv [ENOUGH_DISTS] in BR2.
  zstep Rfd.
  destruct (Z.eq_dec (it_ret r2) 0) as [Hr20 | Hnz2].
  -
    dand (BR2 Hr20) as (TOK2 & Hb25 & Htab2 & Hout2). clear BR2 FS2.
    rewrite Hr20 in *.
    pose proof (pow2_pos (it_bits r2) ltac:(lia)) as Hpw2.
    zbr Rfd true.
    zstep Rfd.
    zstep Rfd. zlit.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd false.
    assert (TOK1' : tab_ok LENS (rdc cf'' (CDyn 0)) (it_bits r) (it_table r) = true).
    { eapply tab_ok_ext_rd; [| exact TOK1]. intros i Hi. unfold rdc. apply Hout2; cbv [N_CODES]; lia. }
    pose proof (sinv_cl_len_ _ _ lf cf cf'' (it_bits r) (it_table r) (it_bits r2) (it_table r2) SI0 eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv [N_CODES]; lia)
                  TOK1' TOK2 ltac:(cbv [N_CODES]; exact Rcf'')) as [SI1 ME1].
    unfold st_tab in SI1, ME1. ist_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (lenu_s (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (IST LEN_ last flags cin cout hold bits out 0 length offset extra (CDyn 0) (CDyn (it_table r)) (it_bits r) (it_bits r2)
                     ncode nlen ndist shave (it_table r2) whave wnext)
                lf cf'' CX0 Hh Hfin eq_refl SI1) end.
    + unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    + unfold k_mem, st_at, st_rest, s_ret, s_out; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [LEN_]; assumption | exact HAG | unfold s_out in SOUT; icx_cbn; exact SOUT | eapply mem_u64_eqv; [| eassumption]; lia ].
    + eapply KALL_mono; [| exact KA0]. clear - ME1. lia.
  -
    destruct (FS2 Hnz2) as [Ht2 Hb6]. clear BR2 FS2.
    assert (Hrm : exists rm, it_ret r2 mod 18446744073709551616 = rm /\ rm <> 0 /\ 0 <= rm < 18446744073709551616).
    { exists (it_ret r2 mod 18446744073709551616). split; [reflexivity|].
      destruct Hret32 as [E | [E | E]]; [exfalso; exact (Hnz2 E) | rewrite E | rewrite E];
        [ rewrite Z.mod_small by lia_std; lia_std
        | replace ((-1) mod 18446744073709551616) with 18446744073709551615 by reflexivity; lia_std ]. }
    dand Hrm as (rm & Hrm & Hrm0 & Hrm1).
    lazymatch goal with H : mem_u64 _ ?Mx (u + -160) _ |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      apply mem_u64_mod in H; rewrite Hrm in H end.
    zbr Rfd false.
    zstep Rfd. zstep Rfd. zlit.
    zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_cl_bad _ _ lf cf cf'' rm (it_bits r) (CDyn (it_table r)) (it_bits r2) (it_table r2) SI0 eq_refl (conj (proj1 Hrm1) (proj2 Hrm1))
                  ltac:(lia) ltac:(lia) ltac:(cbv [N_CODES]; lia) ltac:(lia) ltac:(cbv [N_CODES]; lia) ltac:(cbv [N_CODES]; exact Rcf'')) as [SI1 ME1].
    unfold st_tab in SI1, ME1. ist_cbn.
    rewrite Ht2 in *. rewrite Hb6 in *.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KRA1 Rx Mx _ lf cf'' SI1 ME1) end.
    + unfold s_regs_reload; icx_cbn; zkeys; split_conj; try zreg. all: intros C; discriminate C.
    + unfold k_mem, st_at, st_rest, s_ret, s_out; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [BAD]; assumption | exact HAG | unfold s_out in SOUT; icx_cbn; exact SOUT | eapply mem_u64_eqv; [| eassumption]; lia ].
Qed.

End CLT.
