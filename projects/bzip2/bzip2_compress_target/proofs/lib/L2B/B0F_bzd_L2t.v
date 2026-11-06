(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read RT_liveprim RT_globals. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_globals.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA D_libiface.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt L2StmtD B0_fs_L2f B0_sessK B0F_decK B0F_decX B0F_bzd_L2a B0F_bzd_L2k.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzTables CmpMem AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzInv BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState BzDBlock BzDOut BzDOK BzDOKp BzDFrame DecCutFB B0F_decV S0_bzd_loop1 S0F_bzd_loop1 S0F_bzd_loop3s B0F_bzdV B0F_bzd_skV B0F_bzd_skT B0F_bzd_sk4 B0F_bzd_sk5.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_bzd_loop1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_bzdV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_bzd_skV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma dstate10A_agree : forall (m m' : mem) S strm small h0 nbu0 cf0 d0 r0 js,
  dstate10A m S strm small h0 nbu0 cf0 d0 r0 js -> agree_on (fun x => S <= x < S + 64144) m m' -> dstate10A m' S strm small h0 nbu0 cf0 d0 r0 js.
Proof.
  intros m m' S strm small h0 nbu0 cf0 d0 r0 js (HD & HW & NBU & NBR & CF & CFL & MID & T0 & L160 & L40 & NIU & CCC & DR & SAVE) AG.
  unfold dstate10A.
  split. { apply (n_rw_cells_agree b0segs m m' _ _ HD). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. lia. }
  split; [exact HW|].
  split. { apply (n_rw_cells_agree b0segs m m' _ _ NBU). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. lia. }
  split; [exact NBR|].
  split. { apply (n_u32arr_agree b0segs m m' _ _ CF). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. rewrite CFL in Hx. lia. }
  split; [exact CFL|].
  split. { apply (n_rw_cells_agree b0segs m m' _ _ MID). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. lia. }
  split; [exact T0|]. split; [exact L160|]. split; [exact L40|]. split; [exact NIU|]. split; [exact CCC|].
  split. { apply (drest_agree m m' S r0 _ DR AG). intros x Hx. lia. }
  apply (n_rw_cells_agree b0segs m m' _ _ SAVE). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma dpureF_rebase0 : forall cx b0 payload J d s, bs_len b0 = b_len cx -> dpureF cx b0 payload J d s -> dpureF cx (bs_of cx J s) payload J d s.
Proof.
  intros cx b0 payload J d s BL DP. unfold dpureF, jk_static in DP |- *.
  cbn [bs_of bs_q1 bs_q2 bs_tol bs_toh bs_bzalloc bs_bzfree bs_opaque bs_av bs_ai bs_len]. rewrite BL in DP. decompose [and] DP.
  repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try lia.
Qed.

Section BZDT.
Context {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis DEC10 : decompress10_contract RT.
Hypothesis DEC14 : decompress14_contract RT.
Hypothesis AF_PRIM : af_live_primary RT.
Hypothesis VSR : B0F_bzd_skV.SMALLR_aspec.

Theorem bzDecompress_cps : bzDecompress_contract RT.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx payload db0
         h0 nbu0 cf0 d0 r0 js b0 zp zn op on lo usp W
         FDO MST Ha0 TP CEQ DS10 STRM0 S10 PAY PLEN DB0 LDB0 LIB0 DLIVE DPURE N0 TT0 L160 L40 FRMAX LIVEMAX CRED ART0 MI0 ST0 LOW LOR SPT AL.
  subst a0. intros T c Hc Hk.
  destruct DLIVE as (SLIV & ZLIV & ZLO & ZHI & OLIV & OLO & OHI & TLIV & L16LIV & L4LIV & (fS & kS & FSIN & FSLO & FSHI) & T8 & ZSH).
  pose proof DPURE as (LEN0 & DLEN0 & SM01 & NR & S16 & TT16 & L1616 & L416 & SEP).
  pose proof SEP as (D1 & D2 & D3 & D4 & D5 & D6 & _). cbv zeta in D1, D2, D3, D4, D5, D6. unfold disj in D1, D2, D3, D4, D5, D6.
  pose proof alloc_ceiling_range as ACR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  unfold RT_STACK, BZD_STACK, DEC_STACK in LOR.
  pose proof (af_live_range RT AF Σ m _ _ ART0 SLIV) as (SL0 & SL1 & SLI). pose proof (af_live_range RT AF Σ m _ _ ART0 OLIV) as (OL0 & OL1 & OLI).
  pose proof (af_frames_range RT AF Σ m _ _ ART0 FSIN) as (FS0 & FS1 & _). pose proof (af_frames_align RT AF Σ m _ _ ART0 FSIN) as (FS64 & FSSEG).
  pose proof (af_live_offshadow RT AF Σ m _ _ ART0 SLIV) as SOFF. pose proof (af_live_offshadow RT AF Σ m _ _ ART0 OLIV) as OOFF.
  pose proof (af_frames_hi RT AF Σ m _ _ ART0 FSIN) as FOFF.
  pose proof (af_sp0_range RT AF Σ m ART0) as (_ & SP0T).
  pose proof (AF_PRIM Σ m _ _ ART0 SLIV ltac:(clear; lia)) as IE.
  unfold SEGTOP_A in *.
  set (P := usp - 368).
  assert (PE : P = usp - 368) by reflexivity.
  (* [comment removed for export] *)
  assert (WCL : forall x, ~ outside W x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold W in Hx. cbn [outside] in Hx.
    assert (C : (b_s cx <= x < b_s cx + 64144) \/ (b_strm cx <= x < b_strm cx + 80) \/ (b_dst cx <= x < b_dst cx + b_dlen cx)) by (clear - Hx; lia).
    destruct C as [C|[C|C]].
    - right; right; left. exists (b_s cx), 64144. split; [exact SLIV| exact C].
    - right; right; right; left. exists fS, kS. split; [exact FSIN| clear - C FSLO FSHI; lia].
    - right; right; left. exists op, on. split; [exact OLIV| clear - C OLO OHI; lia]. }
  destruct (act_setup_nf RT AF Σ m lo P usp W ART0 LOW ltac:(unfold RT_STACK; clear - PE LOR; lia) ltac:(clear - PE; lia) SPT
              ltac:(clear - PE AL; Z.div_mod_to_equations; lia) WCL) as (G & SOK).
  assert (PU : bv_unsigned (Z_to_bv 64 P) = P) by exact (P_unsigned G).
  (* [comment removed for export] *)
  set (SHS := b_s cx / 8 + 2147450880). assert (SHSE : SHS = b_s cx / 8 + 2147450880) by reflexivity.
  assert (ANS : sanchor (b_s cx) SHS) by (split; [clear - S16; Z.div_mod_to_equations; lia| reflexivity]).
  clearbody SHS.
  set (z0 := BZC cx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B0F_decK.DG1 B0F_decK.DSV payload lo m [] (Z_to_bv 64 P)).
  assert (ZOK0 : bzdctx_okA z0 SHS).
  { apply (bz_ctx_ok RT AF Σ m z0 SHS zp zn op on fS kS ART0 CEQ FSIN FSLO FSHI T8 SLIV ZLIV ZLO ZHI OLIV OLO OHI TLIV L16LIV L4LIV DPURE ANS); cbn [z0 z_lo z_sp z_spi z_payload z_cx].
    - clear - LOW CEQ. lia.
    - fold usp. clear - LOR. lia.
    - rewrite PU. reflexivity.
    - rewrite PU. replace (P + 368) with usp by (clear - PE; lia). apply Z_to_bv_bv_unsigned.
    - exact PLEN.
    - exact IE. }
  (* [comment removed for export] *)
  pose proof DS10 as (HD0 & HW0 & _).
  destruct (fs_aconsts_of_art RT AF Σ m ART0) as [AC _].
  assert (SHTR : 0x7fff8000 <= shad (b_strm cx) /\ shad (b_strm cx) + 10 <= 0x10007fff8000).
  { unfold USTACK_TOP, STACK_WIN, shad, SHB in *. clear - FS0 FS1 FSLO FSHI SP0T. Z.div_mod_to_equations. lia. }
  assert (APPE : app_fp (B0F_bzd_sk4.WEA z0)).
  { unfold B0F_bzd_sk4.WEA. cbn [z0 z_spi app_fp]. rewrite PU. unfold SH_LO, SH_HI. split; [right; clear - PE LOR LOW CEQ ACR; lia| exact I]. }
  assert (SHs0 : shzW b0segs (B0F_bzd_sk4.WEA z0) m (b_s cx) (b_s cx + 64144))
    by exact (live_reader RT AF Σ m (b_s cx) 64144 _ ART0 SLIV ltac:(clear - S16; Z.div_mod_to_equations; lia) eq_refl APPE).
  assert (SHt0 : shzW b0segs (B0F_bzd_sk4.WEA z0) m (b_strm cx) (b_strm cx + 80)).
  { apply (strm_reader m (b_strm cx) (shad (b_strm cx)) _); [split; [exact T8| reflexivity]| clear - FS0 FSLO; lia| clear - FS1 FSHI CEQ ACR; lia| exact ZSH| exact APPE]. }
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (B0F_bzd_sk4.B0_bzd_entry z0 SHS _ ZOK0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m h0 b0);
    [exact HD0| exact (proj1 HW0)| exact (proj1 (proj2 HW0))| exact STRM0| exact (proj1 (proj2 S10))| exact AC| exact ST0| exact (kmem_inv_N _ _ MI0)| exact SHs0| exact SHt0|].
  clear Hc SHs0 SHt0 APPE.
  intros m1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 w0 w8 w40 w48 w56 w64 w72 w88 w224 w232 HD1 SM1 AC1 FRS1 FSV1 ST1n NMI1 MU1 WM1.
  apply evt_done. intros c1 Hc1.
  unfold B0F_bzd_sk4.WEA in MU1. cbn [z0 z_spi z_cx z_lo] in HD1, SM1, FRS1, FSV1, ST1n, MU1. rewrite PU in FRS1, FSV1, ST1n, MU1.
  destruct (stk_split b0segs m lo P usp ST0 ltac:(clear - PE LOR; lia)) as [ST0P _].
  destruct (after_l1 AF G Σ _ m m1 SOK ART0 MI0 ST0P (presi_refl _ _ _ _ m) NMI1 MU1 WM1
              ltac:(per_interval; left; match goal with HX : _ <= _ < _ |- _ => clear - HX PE; lia end)) as (ART1 & MI1 & ST1 & PR1 & STEP1).
  assert (AG1 : agree_on (fun x => x < P) m m1).
  { apply (agree_of_nmunch [(P, P + 368)] m m1 _ MU1). intros x Hx. cbn [outside NFrame.outside KFrame.outside]. clear - Hx. lia. }
  assert (DS1 : dstate10A m1 (b_s cx) (b_strm cx) (b_small cx) h0 nbu0 cf0 d0 r0 js).
  { apply (dstate10A_agree m m1 _ _ _ _ _ _ _ _ _ DS10). eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in Hx |- *. clear - Hx SL1 LOW CEQ LOR PE. lia. }
  pose proof (af_live_range RT AF Σ m _ _ ART0 ZLIV) as (ZL0 & ZL1 & _).
  assert (PAY1 : bytes_at b0segs m1 (b_src cx) payload).
  { apply (bytes_at_agree b0segs m m1 _ _ PAY). eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in Hx |- *. clear - Hx PLEN ZHI ZL1 LOW CEQ LOR PE. lia. }
  assert (DB1 : u8arr b0segs m1 (b_dst cx) db0).
  { apply (n_u8arr_agree b0segs m m1 _ _ DB0). eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in Hx |- *. clear - Hx LDB0 OHI OL1 LOW CEQ LOR PE. lia. }
  assert (ZSH1 : bytes_at b0segs m1 (shad (b_strm cx)) (repeat z8 10)).
  { apply (bytes_at_agree b0segs m m1 _ _ ZSH). eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in Hx |- *. rewrite repeat_length in Hx. change (Z.of_nat 10) with 10 in Hx.
    clear - Hx SHTR LOW CEQ LOR PE ACR. lia. }
  assert (LIB1 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m1) by (apply (B0_sessK.lib_of_munch _ m m1 LIB0 MU1); intros x Hx; cbn [outside NFrame.outside KFrame.outside]; clear - Hx LOW CEQ LOR PE ACR; lia).
  assert (DLIVE1 : dliveA RT Σ m1 cx zp zn op on).
  { unfold dliveA. repeat (split; [assumption|]). split; [exists fS, kS; split; [exact FSIN| split; [exact FSLO| exact FSHI]]| split; [exact T8| exact ZSH1]]. }
  (* [comment removed for export] *)
  unfold ZRA in Hc1. cbn [z0 z_spi z_gp z_tp z_cx z_s3 z_s5 z_s7 z_s9 z_F z_fc] in Hc1.
  assert (S0C : bv_unsigned (Z_to_bv 64 SHS) <= bv_unsigned (Z_to_bv 64 P) \/ bv_unsigned (Z_to_bv 64 SHS) mod 8 <> 0 \/ 2 ^ 63 <= bv_unsigned (Z_to_bv 64 SHS)).
  { left. rewrite PU. rewrite unsigned_lit by (clear - SHSE SL0 SL1 LOW CEQ ACR; Z.div_mod_to_equations; lia). clear - SHSE SL0 SL1 PE LOR LOW CEQ ACR. Z.div_mod_to_equations. lia. }
  assert (CRED10 : DEC10_COST <= rt_credit RT Σ) by (unfold BZD_COST in CRED; clear - CRED LEN0; lia).
  refine (cps_realizes bsegs _ _ T c1
            (DEC10 Σ PMc (Z_to_bv 64 0x840b8) (Z_to_bv 64 P) gp tp y5 y6 y7 (Z_to_bv 64 SHS) (Z_to_bv 64 (b_s cx + 1096)) (Z_to_bv 64 (b_s cx)) y11 y12 y13 y14 y15 y16 y17
               _ _ _ _ _ _ _ _ _ _ y28 y29 y30 y31 F fc m1 cx payload h0 nbu0 cf0 d0 r0 js b0 zp zn op on lo
               FDO MST eq_refl TP CEQ eq_refl S0C DS1 SM1 S10 PAY1 PLEN LIB1 DLIVE1 DPURE N0 TT0 L160 L40 FRMAX LIVEMAX CRED10 ART1 MI1
               ltac:(rewrite PU; exact ST1) LOW ltac:(rewrite PU; unfold RT_STACK, DEC_STACK; clear - PE LOR; lia) ltac:(rewrite PU; clear - PE SPT; lia)
               ltac:(rewrite PU; clear - PE AL; Z.div_mod_to_equations; lia)) Hc1 _).
  clear Hc1. intros c2 (Σ1 & n & tt & l16 & l4 & Hq & LV1 & FR1 & SP1 & CR1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hq) as (ms2 & (m2 & u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F2 & fc2 & junkD & POST) & Hc2). clear Hq.
  cbv zeta in POST.
  destruct (decompress (dst_init junkD 0 (b_small cx)) (dstrm_init (map bv_unsigned payload) (b_dlen cx))) as [[rv dF] sF] eqn:EDEC.
  destruct POST as (-> & ART2 & MI2 & ST2 & LIB2 & DLIVE2 & DPURE2 & DBOK & ARMS & STEP2).
  rewrite PU in ST2, STEP2.
  rewrite (ret_pc_even 0x840b8 ltac:(lia) eq_refl) in Hc2.
  (* [comment removed for export] *)
  assert (SK1 : sig_ok RT (rt_sp0 RT Σ) false 0 8 (rt_frames RT Σ) (rt_live RT Σ) Σ1).
  { split; [rewrite FR1; reflexivity|]. split; [exact SP1|]. intros e He. rewrite LV1. apply in_or_app. right. exact He. }
  assert (W10C : forall x, ~ KFrame.outside [(b_s cx, b_s cx + 64144); (b_strm cx, b_strm cx + 20)] x -> (b_s cx <= x < b_s cx + 64144) \/ (b_strm cx <= x < b_strm cx + 20)).
  { intros x Hx. cbn [KFrame.outside] in Hx. clear - Hx. lia. }
  pose proof (pres_step G Σ _ m1 m2 SOK PR1 STEP2 ltac:(intros x Hx; right; unfold W; cbn [outside NFrame.outside KFrame.outside]; destruct (W10C x Hx) as [C|C]; clear - C; lia)) as PR2.
  assert (AGU : agree_on (fun x => P <= x < usp) m1 m2).
  { apply (agree_of_pres_fp _ _ _ _ m1 m2 _ STEP2). intros x Hx. split; [left; unfold USTACK_TOP in *; clear - Hx SPT PE; lia|].
    cbn [KFrame.outside]. clear - Hx SL1 FS1 FSHI LOW CEQ LOR PE. lia. }
  assert (FRS2 : rw_cells b0segs m2 P (bzd_slots (b_s cx) SHS w0 w8 w40 w48 w56 w64 w72 w88 w224 w232)).
  { apply (n_rw_cells_agree b0segs m1 m2 _ _ FRS1). eapply agree_sub; [exact AGU|]. intros x Hx. cbv beta in Hx |- *. unfold bzd_slots in Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx PE. lia. }
  assert (FSV2 : rw_cells b0segs m2 (P + 264) (FSAVA z0)).
  { apply (n_rw_cells_agree b0segs m1 m2 _ _ FSV1). eapply agree_sub; [exact AGU|]. intros x Hx. cbv beta in Hx |- *. unfold FSAVA in Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx PE. lia. }
  assert (DB2 : u8arr b0segs m2 (b_dst cx) db0).
  { apply (n_u8arr_agree b0segs m1 m2 _ _ DB1). apply (agree_of_pres_fp _ _ _ _ m1 m2 _ STEP2). intros x Hx. cbv beta in Hx. rewrite LDB0 in Hx. split.
    - right; right; left. exists op, on. split; [exact OLIV| clear - Hx OLO OHI; lia].
    - cbn [KFrame.outside]. clear - Hx D3 D5. lia. }
  assert (TL2 : agree_on (fun x => b_strm cx + 44 <= x < b_strm cx + 80) m m2).
  { apply (agree_trans _ m m1 m2).
    - eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in Hx |- *. clear - Hx FS1 FSHI LOW CEQ LOR PE. lia.
    - apply (agree_of_pres_fp _ _ _ _ m1 m2 _ STEP2). intros x Hx. cbv beta in Hx. split.
      + right; right; right; left. exists fS, kS. split; [exact FSIN| clear - Hx FSLO FSHI; lia].
      + cbn [KFrame.outside]. clear - Hx D1. lia. }
  assert (SP1' : rt_sp0 RT Σ1 - STACK_WIN <= usp) by (rewrite SP1; clear - LOW LOR; lia).
  assert (DB0K : n = 0 /\ tt = 0 /\ l16 = 0 /\ l4 = 0 \/ 1 <= n) by (destruct DBOK as [D|[D _]]; [left; exact D| right; clear - D; lia]).
  assert (MODEL : bzDecompress (dst_init junkD 0 (b_small cx)) (dstrm_init (map bv_unsigned payload) (b_dlen cx)) = K_L (Datatypes.S (length payload)) (rv, dF, sF)).
  { rewrite (bz_model (dst_init junkD 0 (b_small cx)) (dstrm_init (map bv_unsigned payload) (b_dlen cx)) eq_refl). cbn [s_in dstrm_init]. rewrite length_map, EDEC. reflexivity. }
  destruct ARMS as [(J' & DML2 & DP2 & PW2 & NB1) | (RVC & ST13 & SOUT & SAVO & NE0 & (h & dm & ai & til & tih & HD2 & HS2 & HST2 & HNE2 & MID2 & MT & M16 & M4 & STRM2 & AI2))].
  2:{ (* [comment removed for export] *)
    assert (BLK0 : tt = 0 /\ l16 = 0 /\ l4 = 0) by (destruct DB0K as [(_ & A & B & C)|N1]; [auto| exfalso; clear - N1 NE0; lia]).
    destruct BLK0 as (-> & -> & ->). subst n.
    change (dblocks 0 0 0 0) with (@nil (Z * Z)) in LV1. cbn [app] in LV1.
    set (z2 := BZC cx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 B0F_decK.DG1 B0F_decK.DSV payload lo m2 [] (Z_to_bv 64 P)).
    assert (ZOK2 : bzdctx_okA z2 SHS) by exact ZOK0.
    assert (SHs2 : shzW b0segs [] m2 (b_s cx) (b_s cx + 64144))
      by exact (live_reader RT AF Σ1 m2 (b_s cx) 64144 [] ART2 ltac:(rewrite LV1; exact SLIV) ltac:(clear - S16; Z.div_mod_to_equations; lia) eq_refl I).
    assert (RVR : -5 <= rv <= 4 /\ rv <> 4) by (unfold BZ_OK, BZ_DATA_ERROR_MAGIC in RVC; clear - RVC; lia).
    eapply (l1_realizes RT AF Σ1 PMc _ T c2 MST Hc2).
    eapply (B0F_bzd_sk5.B0_bzd_Lraw z2 SHS _ ZOK2 [] m2 (Z_to_bv 64 0x840b8) u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 s3 s5 s7 s9 u3 u4 u5 u6
              w0 w8 w40 w48 w56 w64 w72 w88 w224 w232 m2 h rv);
      [ exact HD2| exact HST2| unfold BZ_X_OUTPUT in HNE2; exact HNE2| exact (proj1 RVR)| exact (proj2 RVR)
      | cbn [z2 z_spi z_cx]; rewrite PU; exact FRS2| cbn [z2 z_spi z_cx]; rewrite PU; exact FSV2| cbn [z2 z_spi z_lo]; rewrite PU; exact ST2| exact SHs2| apply munch_refl|].
    clear Hc2. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ST3. apply evt_done. intros c3 Hc3.
    cbn [z2 z_ra z_sp z_gp z_tp z_s0 z_s1 z_s2 z_s3 z_s4 z_s5 z_s6 z_s7 z_s8 z_s9 z_s10 z_s11 z_F z_fc z_lo] in Hc3, ST3. fold usp in ST3.
    apply Hk. exists Σ1, 0, 0, 0, 0.
    split; [| split; [exact LV1| split; [exact FR1| split; [exact SP1| unfold BZD_COST; clear - CR1 LEN0; lia]]]].
    eapply ASTA_conseq; [exact Hc3|]. intros ms <-.
    exists m2, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F2, fc2, junkD, h, dm, (bupd b0 ai til tih), db0, db0.
    cbv zeta. rewrite MODEL. rewrite (K_L_ret _ rv dF sF ltac:(unfold BZ_STREAM_END; exact (proj2 RVR)) ltac:(unfold BZ_X_OUTPUT; clear - ST13; lia)).
    destruct S10 as (BWF & BS & BSRC & BLEN & BDST & BDLEN & BZA & BZF & BOP & BAI & BAV & BTIL).
    split; [reflexivity|]. split; [exact ART2|]. split; [exact MI2|]. split; [exact ST3|]. split; [exact LIB2|].
    split; [exact DLIVE2|]. split; [exact DPURE2|]. split; [exact DBOK|].
    split; [exact HD2|]. split; [exact HS2|]. split; [exact MID2|]. split; [exact MT|]. split; [exact M16|]. split; [exact M4|].
    split; [exact STRM2|].
    split. { unfold bzs_wf in BWF |- *. unfold bupd. cbn [bs_q1 bs_q2 bs_ai bs_len bs_av bs_dlen]. clear - BWF AI2 BAI. lia. }
    split; [exact BS|]. split; [exact BDST|]. split; [exact BDLEN|]. split; [exact BZF|]. split; [exact BOP|].
    split. { unfold bupd. cbn [bs_av]. rewrite BAV, BDLEN, SAVO. reflexivity. }
    split; [exact DB2|]. split; [exact LDB0|].
    split. { unfold s_output. rewrite SOUT. reflexivity. }
    split. { unfold s_output. rewrite SOUT, SAVO. cbn [rev length]. clear. lia. }
    split; [exact (proj1 RVR)|].
    exact (pres_final_nf RT AF Σ lo P usp W m m m2 ART0 LOW ltac:(clear - PE LOR; lia) ltac:(clear - PE; lia) (munch_refl _ m) PR2). }
  (* [comment removed for export] *)
  destruct S10 as (BWF & BS & BSRC & BLEN & BDST & BDLEN & BZA & BZF & BOP & BAI & BAV & BTIL).
  assert (NB : 1 <= n <= 9 /\ ((b_small cx = 0 /\ tt <> 0 /\ l16 = 0 /\ l4 = 0) \/ (b_small cx = 1 /\ tt = 0 /\ l16 <> 0 /\ l4 <> 0))).
  { destruct DBOK as [(E & _)|D]; [exfalso; clear - E NB1; lia| exact D]. }
  set (cx1 := cx_blocks cx n tt l16 l4) in *.
  set (z1 := BZC cx1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 B0F_decK.DG1 B0F_decK.DSV payload lo m2 [] (Z_to_bv 64 P)).
  pose proof DLIVE2 as (SLK & ZLK & _ & _ & OLK & _ & _ & TLK & L16LK & L4LK & _).
  assert (ZOK1 : bzdctx_okA z1 SHS).
  { apply (bz_ctx_ok RT AF Σ1 m2 z1 SHS zp zn op on fS kS ART2 ltac:(rewrite SP1; exact CEQ) ltac:(rewrite FR1; exact FSIN) FSLO FSHI T8 SLK ZLK ZLO ZHI OLK OLO OHI TLK L16LK L4LK DPURE2 ANS);
      cbn [z1 z_lo z_sp z_spi z_payload z_cx].
    - clear - LOW CEQ. lia.
    - fold usp. clear - LOR. lia.
    - rewrite PU. reflexivity.
    - rewrite PU. replace (P + 368) with usp by (clear - PE; lia). apply Z_to_bv_bv_unsigned.
    - exact PLEN.
    - cbn [cx1 cx_blocks b_s]. exact IE. }
  rewrite LV1 in SLK, ZLK, OLK, TLK, L16LK, L4LK.
  assert (GZ : act_geom RT lo (bv_unsigned (Z_to_bv 64 P)) usp (rt_sp0 RT Σ) false 0 8 2147450881 0 0 (rt_frames RT Σ) (rt_live RT Σ) W) by (rewrite PU; exact G).
  assert (NN0 : b_small cx1 = 0 -> b_tt cx1 <> 0).
  { cbn [cx1 cx_blocks b_small b_tt]. intros E. destruct NB as (_ & [(_ & TN & _)|(E1 & _)]); [exact TN| exfalso; clear - E E1; lia]. }
  assert (NN1 : b_small cx1 = 1 -> b_ll16 cx1 <> 0 /\ b_ll4 cx1 <> 0).
  { cbn [cx1 cx_blocks b_small b_ll16 b_ll4]. intros E. destruct NB as (_ & [(E0 & _)|(_ & _ & N16 & N4)]); [exfalso; clear - E E0; lia| exact (conj N16 N4)]. }
  assert (BNEW : forall x, ~ outside (blk_ivls cx1) x -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold blk_ivls in Hx. cbn [cx1 cx_blocks b_small b_tt b_ll16 b_ll4 b_n] in Hx.
    assert (FRI : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ1)) by (intros e He; rewrite FR1; exact He).
    destruct NB as (_ & [(E & TN & E16 & E4)|(E & ET & N16 & N4)]); rewrite E in Hx; cbn [Z.eqb outside NFrame.outside KFrame.outside] in Hx.
    - assert (C : tt <= x < tt + 400000 * n) by (clear - Hx; lia).
      apply (newlive_not_caller RT AF Σ1 m2 _ _ usp _ tt (400000 * n) ART2 LV1); [| exact FRI| exact SP1'| exact C].
      unfold dblocks. rewrite (proj2 (Z.eqb_neq tt 0) TN). apply in_or_app. right. apply in_or_app. right. left. reflexivity.
    - assert (C : (l16 <= x < l16 + 200000 * n) \/ (l4 <= x < l4 + 50000 * n)) by (clear - Hx; lia).
      destruct C as [C|C].
      + apply (newlive_not_caller RT AF Σ1 m2 _ _ usp _ l16 (200000 * n) ART2 LV1); [| exact FRI| exact SP1'| exact C].
        unfold dblocks. rewrite (proj2 (Z.eqb_neq l16 0) N16). apply in_or_app. right. apply in_or_app. left. left. reflexivity.
      + apply (newlive_not_caller RT AF Σ1 m2 _ _ usp _ l4 (50000 * n) ART2 LV1); [| exact FRI| exact SP1'| exact C].
        unfold dblocks. rewrite (proj2 (Z.eqb_neq l4 0) N4). apply in_or_app. left. left. reflexivity. }
  (* [comment removed for export] *)
  assert (WCOUT : forall x, (0x10000 <= x < 0x62b000) \/ (0x7fff7000 <= x < 0x10007fff8000) -> outside W x).
  { intros x Hx. unfold W. cbn [outside NFrame.outside KFrame.outside]. split; [clear - Hx SLI SOFF; lia|]. split; [clear - Hx FSSEG FOFF FSLO FSHI; lia|].
    split; [clear - Hx OLI OOFF OLO OHI DLEN0; lia| exact I]. }
  assert (SHTC : forall x, shad (b_strm cx) <= x < shad (b_strm cx) + 10 -> in_fframe_shadow (rt_frames RT Σ) x).
  { intros x Hx. exists fS, kS. split; [exact FSIN|]. unfold shad, SHB in *.
    pose proof FSHI as FSHI'. revert FSHI'. generalize (fs_size kS). intros fsz FSHI'. clear - Hx FSLO FSHI' FS64 T8. Z.div_mod_to_equations. lia. }
  assert (KZSH : forall m', PRESI usp (rt_frames RT Σ) (rt_live RT Σ) W m m' -> bytes_at b0segs m' (shad (b_strm cx)) (repeat z8 10)).
  { intros m' PR. apply (bytes_at_agree b0segs m m' _ _ ZSH). intros a Ha. cbv beta in Ha. rewrite repeat_length in Ha. change (Z.of_nat 10) with 10 in Ha.
    apply PR. split; [right; right; right; right; exact (SHTC _ Ha)| apply WCOUT; right; clear - Ha SHTR; lia]. }
  assert (KLIB : forall m', PRESI usp (rt_frames RT Σ) (rt_live RT Σ) W m m' -> OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m').
  { intros m' PR. apply (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_locA m m' LIB0). intros a (lo' & hi' & HIn & Hx). refine (PR a _).
    assert (R : 857056 <= bv_unsigned a < 858080 \/ 858336 <= bv_unsigned a < 858392 \/ 858432 <= bv_unsigned a < 860480).
    { unfold OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__.LIB_FP in HIn. cbn [In] in HIn. destruct HIn as [HI|[HI|[HI|[]]]]; injection HI as <- <-; [left| right; left| right; right]; exact Hx. }
    clear HIn Hx. split.
    - right; left. exact (B0_sessK.lib_static _ R).
    - apply WCOUT. left. clear - R. lia. }
  set (LIVEK := dblocks n tt l16 l4 ++ rt_live RT Σ) in *.
  set (f := Datatypes.S (length payload)).
  assert (FZ : Z.of_nat f = b_len cx + 1) by (unfold f; rewrite Nat2Z.inj_succ, PLEN; clear; lia).
  set (CMIN := rt_credit RT Σ1 - Z.of_nat f).
  assert (CMIN0 : 0 <= CMIN) by (unfold CMIN, BZD_COST in *; clear - CR1 CRED FZ; lia).
  set (R0 := K_L f (rv, dF, sF)).
  (* [comment removed for export] *)
  assert (HKZ : forall c' (Σ' : rts RT) (m' : mem) (rv' : Z) (J'' : jk) (d' : dst) (s' : dstrm) (dbytes rest : list byte)
      (q0 q1 q2 g1 g2 g3 g4 g5 g6 g7 q3 q4 q5 q6 : word) F' fc',
    (rv', d', s') = R0 ->
    ASTA RT Σ' PMc (eq (MS (mkR ra sp gp tp q0 q1 q2 s0 s1 (Z_to_bv 64 rv') g1 g2 g3 g4 g5 g6 g7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
                           F' (ret_pc ra) fc' None m' (seg_rom b0segs))) c' ->
    INVZ RT z1 (rt_sp0 RT Σ) (rt_frames RT Σ) (rt_live RT Σ) W m LIVEK Σ' m' -> CMIN <= rt_credit RT Σ' <= rt_credit RT Σ ->
    dmem DI_B0 cx1 B0F_decK.DG1 B0F_decK.DSV payload m' (dvF cx1 J'' d' s') -> FDESTA z1 m' s' dbytes rest -> stk bsegs m' lo usp ->
    dpureF cx1 (bs_of cx1 J'' s') payload J'' d' s' -> -5 <= rv' <= 4 ->
    realizes bsegs c' T).
  { intros c' Σ' m' rv' J'' d' s' dbytes rest q0 q1 q2 g1 g2 g3 g4 g5 g6 g7 q3 q4 q5 q6 F' fc' ER Hc' IV' CRB DM' FD' ST' DP' RV'.
    pose proof IV' as (SK' & LV' & ART' & MI' & PR' & TL').
    apply Hk. exists Σ', n, tt, l16, l4.
    split; [| split; [exact LV'| split; [rewrite (proj1 SK'); reflexivity| split; [exact (proj1 (proj2 SK'))| unfold CMIN, BZD_COST in *; clear - CRB CR1 FZ; lia]]]].
    eapply ASTA_conseq; [exact Hc'|]. intros ms <-.
    exists m', q0, q1, q2, g1, g2, g3, g4, g5, g6, g7, q3, q4, q5, q6, F', fc', junkD, (hd_of cx1 J'' d'), (mid_of cx1 d'), (bs_of cx1 J'' s'), dbytes, rest.
    cbv zeta. rewrite MODEL. change (K_L (Datatypes.S (length payload)) (rv, dF, sF)) with R0. rewrite <- ER.
    pose proof (dmemL_of m' cx1 _ _ _ _ DM') as DML'. destruct DML' as (HD' & _ & _ & MID' & _ & _ & STRM' & _ & _).
    cbn [dv_h dv_d dv_b dvF] in HD', MID', STRM'.
    destruct FD' as (DB' & LDB' & EDB' & LOUT'). cbn [z1 z_cx cx1 cx_blocks b_dst b_dlen] in DB', LDB', LOUT'.
    destruct (bz_strm_tail m m' (b_strm cx) b0 (bs_of cx1 J'' s') STRM0 STRM' TL') as (_ & EF & EO).
    split; [reflexivity|]. split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact (KLIB m' PR')|].
    split. { exact (bz_dlive RT z1 SHS _ _ _ _ m ZOK1 FRMAX LIVEK zp zn op on fS kS SLK ZLK ZLO ZHI OLK OLO OHI TLK L16LK L4LK FSIN FSLO FSHI KZSH Σ' m' IV'). }
    split; [exact DPURE2|]. split; [exact DBOK|].
    split; [exact HD'|]. split; [reflexivity|]. split; [exact MID'|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact STRM'|].
    split. { pose proof (dpureF_jwf _ _ _ _ _ _ DP') as JW. unfold jk_wf in JW. pose proof (in_rel_length _ _ (dpureF_in _ _ _ _ _ _ DP')) as IRL.
             pose proof (f_equal (@length byte) EDB') as X. rewrite length_app, length_map, length_rev in X.
             unfold bzs_wf. cbn [bs_of bs_q1 bs_q2 bs_ai bs_len bs_av bs_dlen cx1 cx_blocks b_len b_dlen]. clear - JW IRL X LOUT' LDB' LEN0 DLEN0 PLEN. lia. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite EF; exact BZF|]. split; [rewrite EO; exact BOP|]. split; [reflexivity|].
    split; [exact DB'|]. split; [exact LDB'|].
    split; [unfold s_output; exact EDB'|]. split; [unfold s_output; rewrite length_rev; exact LOUT'|].
    split; [exact RV'|].
    exact (pres_final_nf RT AF Σ lo P usp W m m m' ART0 LOW ltac:(clear - PE LOR; lia) ltac:(clear - PE; lia) (munch_refl _ m) PR'). }
  (* [comment removed for export] *)
  pose proof (decompress_frame (dst_init junkD 0 (b_small cx)) (dstrm_init (map bv_unsigned payload) (b_dlen cx)) ltac:(cbn; unfold BZ_X_OUTPUT, BZ_X_MAGIC_1; clear; lia)
                ltac:(cbn; unfold BZ_X_MAGIC_1; clear; lia)) as DF.
  rewrite EDEC in DF. destruct DF as (Fout & Fav & _ & Fcc & _ & _ & Fst). cbn [s_out s_avail_out dstrm_init] in Fout, Fav.
  assert (CC0 : d_cccrc dF = 0) by (rewrite Fcc; reflexivity).
  destruct (dec_img RT AF AF_DRV Σ1 m2 ART2 LIB2) as (_ & _ & _ & CRC2).
  assert (CH : FCHA (bz_setm0 z1 m2 F2 fc2) SHS w0 m2 J' dF sF db0 db0 w8 w40 w48 w56 w64 w72 w88 w224 w232).
  { unfold FCHA, FIMGA, FDESTA. cbn [bz_setm0 z1 z_cx z_g1 z_sv z_payload z_spi z_lo cx1 cx_blocks b_s b_dst b_dlen]. rewrite PU, Fout, Fav.
    split; [exact (dmem_of_L RT AF AF_DRV Σ1 m2 cx1 _ _ ART2 LIB2 DML2)|]. split; [exact CRC2|].
    split; [split; [exact DB2| split; [exact LDB0| split; [reflexivity| cbn [length]; clear; lia]]]|].
    split; [exact FRS2|]. split; [exact FSV2|]. split; [exact ST2| exact (proj1 (fs_aconsts_of_art RT AF Σ1 m2 ART2))]. }
  assert (FF : S0F_bzd_loop1.FFACTS (bz_setm0 z1 m2 F2 fc2) J' rv dF sF).
  { unfold S0F_bzd_loop1.FFACTS. cbn [bz_setm0 z1 z_cx z_payload cx1 cx_blocks b_dlen].
    split; [exact (dpureF_rebase0 cx1 b0 payload J' dF sF BLEN DP2)|]. split; [exact Fst|]. split; [rewrite CC0; clear; lia|].
    split; [rewrite Fav; clear - DLEN0; lia| exact PW2]. }
  assert (FUEL : d_state dF = BZ_X_OUTPUT -> b_len cx1 / 6 - d_blockNo dF < Z.of_nat f).
  { intros _. cbn [cx1 cx_blocks b_len]. rewrite FZ. pose proof DP2 as DPX. unfold dpureF in DPX. destruct DPX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BN0 & _).
    clear - BN0 LEN0. Z.div_mod_to_equations. lia. }
  refine (bzd_loop_l2_1 RT AF AF_DRV DEC14 VSR z1 SHS w0 (rt_sp0 RT Σ) (rt_frames RT Σ) (rt_live RT Σ) W GZ m PMc FDO MST T ZOK1 TP eq_refl eq_refl NB1 NN0 NN1 DPURE2
            ltac:(cbn [z1 z_lo z_spi]; rewrite PU; unfold RT_STACK, DEC_STACK; clear - PE LOR; lia) FRMAX CEQ
            LIVEK zp zn op on fS kS SLK ZLK ZLO ZHI OLK OLO OHI TLK L16LK L4LK FSIN FSLO FSHI
            ltac:(intros x Hx; unfold W; cbn [z1 z_cx cx1 cx_blocks b_s b_strm b_dst b_dlen outside NFrame.outside KFrame.outside] in Hx |- *; clear - Hx; lia)
            BNEW KLIB KZSH CMIN CMIN0 (rt_credit RT Σ) R0 HKZ f Σ1 m2 F2 fc2
            (Z_to_bv 64 0x840b8) u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 s3 s5 s7 s9 u3 u4 u5 u6 w8 w40 w48 w56 w64 w72 w88 w224 w232 rv J' dF sF db0 db0 c2
            (conj SK1 (conj LV1 (conj ART2 (conj MI2 (conj PR2 TL2))))) ltac:(unfold CMIN; clear; lia) ltac:(clear - CR1; lia) CH FF FUEL eq_refl Hc2).
Qed.
End BZDT.
