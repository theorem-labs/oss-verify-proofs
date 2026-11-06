(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import SFModel Arr SysStep FP ITree Nodes Decode.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.PG Require Import Printf_lib F_printf_iface.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.G3 Require Import LeptFormats LeptShapes Printf_sn2.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import FX_lib F_memset F_memcpy F_fwritex F_pop_arg F_printf_iface F_printf_core.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import F_printf_snsink F_sn_write F_towrite F_vfprintf F_vsnprintf.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import F_pkit R_m2s I_consts I_qck F_achk D_kit.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import I_pck I_pcbits I_pcseg I_pchead I_pcfmt I_vprintfw I_vfsnw I_vsnw I_vsnw2.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import F_vfprintf_sn2 F_vsnprintf2 I_pcgen I_vsngen I_vfsn_g2 I_leptfmt I_leptargs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma largs_args_ok2 : forall sh ws strs m lo D dn sp, lstrs_ok m lo D dn sh ws strs ->
  args_ok lo lo 0 (lo + 8) 0 D dn m lo sp lo ws (largs sh ws strs).
Proof.
  induction sh as [|[[k nx] t] r IH]; intros ws strs m lo D dn sp H; [cbn [largs]; destruct ws; exact I|].
  destruct ws as [|w ws']; [destruct H|]. cbn [lstrs_ok largs] in *.
  destruct k; cbn [args_ok].
  - destruct H as [(sl & BY & NZ & PAD & S0 & SB & CHK & SEP & L96) Hr]. split; [| exact (IH ws' (tl strs) m lo D dn sp Hr)].
    cbn [arg_ok]. exists sl. unfold zlength. rewrite length_map.
    assert (E : zb (map bv_unsigned (hd [] strs)) = hd [] strs).
    { generalize (hd [] strs). induction l as [|b l IHl]; [reflexivity|]. unfold zb in *. cbn [map]. rewrite IHl. f_equal.
      exact (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned 8 b). }
    rewrite E. split; [exact BY|].
    split. { apply Forall_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as (b & <- & Hb).
             pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
             destruct (Z.eq_dec (bv_unsigned b) 0) as [E0|E0]; [| lia]. exfalso. apply NZ.
             replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    split; [exact PAD|]. split; [exact S0|]. split; [left; lia|]. split; [left; lia|].
    split; [split; [left; lia|]; split; [left; lia|]; destruct SEP; [right; lia | left; lia]|]. split; [left; lia|]. exact CHK.
  - split; [| exact (IH ws' strs m lo D dn sp H)]. cbn [arg_ok]. exact (sx32w_ok w).
  - split; [| exact (IH ws' strs m lo D dn sp H)]. cbn [arg_ok]. reflexivity.
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma ivsn_lept_evt2 : forall (usp D n ap lo A : Z) (f t0f : list Z) (ks : list lkind) (sh : pshape) (ws : list word)
    (strs : list (list byte)) (junk : list byte) (dn : nat) (r cap : Z) (d o : list Z)
    (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : mem) (g : word),
  In (f, ks, (t0f, sh)) LEPT_SHAPES -> (length sh <= length ws)%nat ->
  stk asegs m lo usp -> lo <= usp - 8064 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
  va_area m ap ws -> (forall i w, nth_error ws i = Some w -> ro_cells asegs m (ap + 8 * Z.of_nat i) [C8 w]) ->
  usp <= ap -> ap + 8 * Z.of_nat (length ws) <= 2^47 ->
  lstrs_ok m lo D (Z.of_nat dn) sh ws strs ->
  printf_model (OUT_sn2b cap) OUTFP_sn2 f (largs sh ws strs) ([], []) = ITree.Ret (Ok (r, (d, o))) -> r = zlength (d ++ o) -> zlength (d ++ o) <= cap ->
  fp_calls (length f) f (largs sh ws strs) = [] -> pass1_ok f = true ->
  0 <= cap -> cap <= n - 1 -> cap < Z.of_nat dn -> 1 <= n -> n < 2^31 ->
  cstr_at m A (zb8 (t0f ++ pshape_bytes sh)) -> 65536 <= A -> A + zlength f <= STATIC_SPLIT ->
  rw_cells asegs m D [CB dn junk] -> chkr m D (Z.of_nat dn) ->
  D + Z.of_nat dn <= lo -> 0x627000 <= D -> (D + Z.of_nat dn <= ap \/ ap + 8 * Z.of_nat (length ws) <= D) ->
  ictx m -> (forall p n, lo <= p -> p + n <= usp -> chkr m p n) -> chkr m A (zlength f) -> rod_chk m ->
  pfcells m -> vsncells m -> ssp_cells m g -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
      ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch [(lo, usp); (D, D + Z.of_nat dn)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
      /\ exists junk', rw_cells asegs m' D [CB dn junk'])
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 ap) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4c908) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until g.
  intros ROW LWS ST LO HSH Q47 Q16 VAA SLOTS QAP APH LS MODEL ER RCAP FPC P1 CAP0 CAPN CAPD N1 NH CSF A0 ASS DST CHD DSEP D0 DAP IC STKC FMTC ROD PFC VSN SSP MI.
  set (sargs := lsargs sh ws strs).
  destruct (lept_fmt_split f ks t0f sh sargs ROW) as (EF & OK0 & OKD & L1 & EKS & SOK).
  pose proof (ptail_fill sh sargs) as PTF.
  pose proof (chkr_chk_ok _ _ _ FMTC) as CKF.
  pose proof (chkr_bound _ _ _ CHD) as (DB0 & DB1).
  pose proof (Printf_pieces.zlength_nonneg' (d ++ o)) as O0.
  assert (PCX : pctx m) by (destruct IC as ((G2 & G1 & RM & SHC & RI) & _ & _ & M2S); split; [exact M2S| split; assumption]).
  assert (LF : zlength f = Z.of_nat (length t0f) + Z.of_nat (length (pshape_bytes sh)) + 1).
  { rewrite EF, PTF. unfold zlength. rewrite !length_app. cbn [length]. lia. }
  unfold kHighShadowEnd, kHighMemEnd, STATIC_SPLIT in *.
  assert (PF0 : pfmt_ok m usp lo A ap t0f (fill sh sargs)).
  { rewrite <- PTF in CSF. split; [exact OK0|]. split; [exact OKD|]. split; [exact L1|]. split; [exact CSF|].
    rewrite PTF. split; [lia|]. split; [replace (Z.of_nat (length t0f) + Z.of_nat (length (pshape_bytes sh)) + 1) with (zlength f) by lia; exact CKF|].
    split; [apply (pargs_weaken _ m (2^64)); [apply (largs_pargs sh ws strs m lo D (Z.of_nat dn) ap LS SLOTS); lia | lia]|].
    split; [exact QAP|]. rewrite length_fill. lia. }
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (ivsn_walkA_gen RIP usp D n A ap lo t0f (fill sh sargs));
      first [exact ST | exact PF0 | exact PCX | exact PFC | exact VSN | exact MI | lia | (unfold kHighShadowEnd; lia)]. }
  cbv beta. intros ms1 P. unfold ivsnA_post in P.
  destruct P as (m1 & u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & j8 & junkf & -> & MU1 & WM1 & MI1 & ST1 & FRt & FRb).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  pose proof CHD as (_ & _ & (RIMD & _)). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIMD.
  pose proof (cstr_bound _ _ _ CSF) as (_ & AB1).
  set (dnz := Z.of_nat dn) in *.
  (* [comment removed for export] *)
  pose proof (rw_cells_transport asegs _ _ _ _ _ DST MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as DST1.
  destruct SSP as (SSP1 & SSP2). unfold got_ssp, ssp_guard in SSP1, SSP2.
  pose proof (ro_cells_transport asegs _ _ _ _ _ SSP1 MU1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as SSP1'.
  pose proof (ro_cells_transport asegs _ _ _ _ _ SSP2 MU1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as SSP2'.
  assert (VAA1 : va_area m1 ap ws).
  { unfold va_area in *. apply (bytes_at_agree asegs m m1 _ _ VAA). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside].
    rewrite u64s_length in Hx. lia. }
  (* [comment removed for export] *)
  assert (MUX : forall m', munch (VSN_W lo (usp + -2160) D dn) m1 m' -> munch [(lo, usp); (D, D + dnz)] m m').
  { intros m' MU'. apply (munch_trans _ m m1 m').
    - eapply munch_weaken; [| exact MU1]. unfold sub_fp; intros x Hx; cbn [outside] in *; lia.
    - eapply munch_weaken; [| exact MU']. unfold sub_fp, VSN_W; intros x Hx; cbn [outside] in *; lia. }
  assert (HWs : forall x, x < lo -> ~ (D <= x < D + dnz) -> outside [(lo, usp); (D, D + dnz)] x) by (intros x H1 H2; cbn [outside]; lia).
  assert (HSs : forall x, SHADOW_LO <= x < SHADOW_HI -> outside [(lo, usp); (D, D + dnz)] x)
    by (intros x Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia).
  pose proof (vsnprintf_proof2 RIP PCLEPT (ivfsn_lept2 RIP)) as VS. unfold vsnprintf_stmt2 in VS. cbv zeta in VS.
  eapply evt_cut.
  { eapply VS with (F := F) (fc := fc) (m := m1) (D := D) (n := n) (A := A) (VA := ap) (dn := dn) (junkd := junk)
               (fmt := f) (slots := ws) (args := largs sh ws strs) (lo := lo) (canary := g) (r := r) (d := d) (o := o) (cap := cap)
               (F0 := lo) (B0 := lo) (BS0 := 0) (ap0 := lo);
      clear VS; rewrite ?EU2160; unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT, kHighShadowEnd.
    all: first [ reflexivity | exact DST1 | exact VAA1 | exact MODEL | exact FPC | exact P1 | exact ST1
               | (split; [exact SSP1' | exact SSP2']) | exact MI1 | exact I
               | (lazymatch goal with |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ <= _ < _)%Z => idtac | |- (_ <= _ <= _)%Z => idtac
                                    | |- (_ < _ <= _)%Z => idtac | |- (_ < _ < _)%Z => idtac | |- _ \/ _ => idtac end;
                  fold dnz; rewrite ?u64s_length; unfold zlength in *; first [lia | Z.div_mod_to_equations; lia])
               | idtac ].
    - (* [comment removed for export] *)
      destruct PF0 as (_ & _ & _ & CSA & _). destruct CSA as (BYA & _).
      assert (EZ : zb f = zb8 (t0f ++ ptail (fill sh sargs)) ++ [z8]).
      { unfold zb, zb8. rewrite EF at 1. rewrite app_assoc. rewrite (map_app _ (t0f ++ ptail (fill sh sargs)) [0]). reflexivity. }
      rewrite EZ.
      apply (bytes_at_agree asegs m m1 _ _ BYA). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside].
      rewrite length_app, length_zb8, PTF, length_app in Hx. change (length [z8]) with 1%nat in Hx. unfold zlength in *. lia.
    - (* [comment removed for export] *)
      rewrite EF. apply Forall_app. split; [| apply Forall_app; split; [| repeat constructor; lia]].
      + pose proof (txt_ok_bytes _ OK0) as H. rewrite forallb_forall in H. apply Forall_forall. intros c Hc. specialize (H c Hc).
        apply andb_prop in H. destruct H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
      + rewrite PTF. exact (pshape_bytes_range sh SOK).
    - (* [comment removed for export] *)
      intros m' MU'. pose proof (MUX m' MU') as MUm.
      apply (largs_args_ok2 sh ws strs m' lo D dnz (usp + -2160)).
      exact (lstrs_ok_munch sh ws strs _ m m' lo D dnz LS MUm HWs HSs).
    - Z.div_mod_to_equations; lia.
    - apply (ictx_munch _ m m1 IC MU1 WM1). intros x Hx; cbn [in_rl ICR outside] in *; lia.
    - intros p n' H1 H2. apply (chkr_munch _ m m1 p n' (STKC p n' H1 ltac:(lia)) MU1).
      intros x Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia.
    - apply (chkr_munch _ m m1 _ _ FMTC MU1). intros x Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia.
    - destruct ROD as (R1 & R2 & R3). split; [| split]; [apply (chkr_munch _ m m1 _ _ R1 MU1) | apply (chkr_munch _ m m1 _ _ R2 MU1)
        | apply (chkr_munch _ m m1 _ _ R3 MU1)]; intros x Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia.
    - apply (chkr_munch _ m m1 _ _ CHD MU1). intros x Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia.
    - unfold SHADOW_LO, SHADOW_HI. fold dnz. lia.
    - (* [comment removed for export] *)
      intros m' MU' WM'. pose proof (MUX m' MU') as MUm. pose proof (wmono_trans _ _ _ _ WM1 WM') as WMm.
      assert (HWm : forall x, x < lo \/ usp <= x -> ~ (D <= x < D + dnz) -> outside [(lo, usp); (D, D + dnz)] x) by (intros x H1 H2; cbn [outside]; lia).
      destruct PF0 as (_ & _ & _ & CSA & ABL & CHKA & _).
      exists t0f, (fill sh sargs). split; [exact EF|]. split; [exact OK0|]. split; [exact OKD|]. split; [exact L1|].
      split. { apply (cstr_agree m m' _ _ CSA). apply (agree_of_munch _ _ _ _ MUm). intros x Hx. cbn [outside].
               rewrite length_zb8, length_app, PTF in Hx. lia. }
      split; [exact ABL|].
      split. { eapply chk_ok_agree; [exact CHKA | lia | rewrite PTF; lia |]. apply (agree_of_munch _ _ _ _ MUm). intros x Hx. cbn [outside]. lia. }
      split. { apply (largs_pargs sh ws strs m' lo D dnz ap (lstrs_ok_munch sh ws strs _ m m' lo D dnz LS MUm HWs HSs)); [| lia].
               intros i w Hi. apply (ro_cells_agree asegs m m' _ _ (SLOTS i w Hi)). apply (agree_of_munch _ _ _ _ MUm). intros x Hx.
               cbn [cells_size csize Nat.add] in Hx. cbn [outside].
               assert (Z.of_nat i < Z.of_nat (length ws)) by (apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hi; discriminate). lia. }
      split; [rewrite length_fill; lia|].
      split. { apply (pctx_munch _ m m' PCX MUm WMm). intros x Hx; unfold in_PCR in Hx; cbn [outside]; lia. }
      apply (pfcells_munch _ m m' PFC MUm WMm). intros x Hx; unfold in_PFR in Hx; cbn [outside]; lia. }
  cbv beta. intros ms2 P. unfold vsnprintf_post2 in P. rewrite ?EU2160 in P.
  destruct P as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & Ft & fc' & rest2 & m2 & -> & MU2 & WM2 & MI2 & FRM2 & FOK2
                 & ST2 & SSP' & DST2).
  unfold VSN_W in MU2.
  pose proof (rw_cells_transport asegs _ _ _ _ _ FRt MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRt2.
  pose proof (rw_cells_transport asegs _ _ _ _ _ FRb MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRb2.
  pose proof (MUX m2 MU2) as MU12. pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM12.
  assert (CHK2' : chk_ok m2 D (r + 1)).
  { apply chkr_chk_ok. apply (chkr_munch _ m m2 _ _ (chkr_sub _ _ _ D (r + 1) CHD ltac:(lia) ltac:(fold dnz; lia) ltac:(lia)) MU12). exact HSs. }
  assert (M2S2 : m2s_cells m2).
  { pose proof (ictx_munch _ m m2 IC MU12 WM12 ltac:(intros x Hx; cbn [in_rl ICR outside] in *; lia)) as (_ & _ & _ & X). exact X. }
  replace (ret_pc (Z_to_bv 64 0x50100)) with (Z_to_bv 64 0x50100) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* [comment removed for export] *)
  eapply evt_mono.
  { eapply (ivsn_walkC RIP usp D n r lo j8 junkf);
      first [exact ST2 | exact FRt2 | exact FRb2 | exact CHK2' | exact M2S2 | exact MI2 | lia | (unfold kHighShadowEnd; lia) | (unfold zlength in *; lia)]. }
  cbv beta. intros ms3 (m3 & w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & -> & MU3 & WM3 & MI3 & ST3).
  exists m3, w0, w1, w2, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, Ft, fc'. split; [reflexivity|].
  split. { apply (munch_trans _ m m2 m3); [exact MU12|].
           eapply munch_weaken; [| exact MU3]. unfold sub_fp; intros x Hx; cbn [outside] in *; lia. }
  split; [exact (wmono_trans _ _ _ _ WM12 WM3)|]. split; [exact MI3|]. split; [exact ST3|].
  eexists. apply (rw_cells_transport asegs _ _ _ _ _ DST2 MU3 WM3). cbn [disjoint_from cells_size csize Nat.add]. fold dnz. lia.
Qed.

End WithRIP.
