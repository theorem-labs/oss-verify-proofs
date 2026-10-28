(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ITree Nodes Decode SysStep RzCPS NodesA. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad Stdio Canon PrintfModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_pieces.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtP Require Import Printf_bridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow X_bridge X_bridge2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s I_consts I_qck RT_iface D_iface D_defs D_kit D_clx I_iodefs I_lift F_achk F_printf_iface Printf_stdio_iface F_stdout_write F_fwritex_stdout F_vfprintf_stdout I_pcbits I_pchead I_pcfmt I_vprintfw I_vpbridge F_fwrite FX_lib F_pop_arg F_pkit X_open I_read.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pf_consts (m : mem) : Prop :=
  pfcells m /\ ictx m /\ acc ctasegs m 0x1db09 4 /\ acc ctasegs m PFX_A 10 /\ acc ctasegs m XDIG_A 16 /\ acc ctasegs m NULLS_A 7
  (* [comment removed for export] *)
  /\ acc ctasegs m 0x212eb 17 /\ acc ctasegs m 0x3cd30 21 /\ acc ctasegs m 0x3cd45 23 /\ acc ctasegs m 0x2efb9 33.

Section XVprintf.
Variable RT : rt_sig.


Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis AF_PF : forall Σ m, ART RT Σ m -> pf_consts m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Lemma rng_class_sub : forall Σ p n p' n', rng_class RT Σ p n -> p <= p' -> p' + n' <= p + n -> rng_class RT Σ p' n'.
Proof.
  intros Σ p n p' n' H H1 H2. unfold rng_class in *.
  destruct H as [(q & k & IN & A1 & A2) | [(f & k & IN & A1 & A2) | [(A1 & A2) | (A1 & A2)]]].
  - left. exists q, k. split; [exact IN| lia].
  - right; left. exists f, k. split; [exact IN| lia].
  - right; right; left. lia.
  - right; right; right. lia.
Qed.

(* [comment removed for export] *)
Lemma chkr_of : forall Σ m p n, ART RT Σ m -> 0 < n <= 2^40 -> acc ctasegs m p n -> rng_class RT Σ p n -> chkr m p n.
Proof using AF_SHW.
  intros Σ m p n ART0 Hn AC RC. split; [exact AC|]. split.
  - intros i Hi. destruct (AF_SHW Σ m (p + i) 1 ART0 ltac:(lia) (rng_class_sub Σ p n (p + i) 1 RC ltac:(lia) ltac:(lia))) as (QW & _).
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & _). exists w1. exact W1.
  - destruct (AF_SHW Σ m p n ART0 ltac:(lia) RC) as (_ & RIM). split; [exact RIM| lia].
Qed.

Theorem vprintf_ok : vprintf_emit0_icontract RT OUT_repA ERR_repA IO_FPA.
Proof using AF RIP AF_SHW AF_PF.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so ap lo
    Ha0 Ha1 VA APS SO HFD OUT0 (g & SG1 & SG2) ART0 MI0 CALL.
  subst a0 a1. intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  destruct (AF_PF Σ m ART0) as (PFC & IC & ACCF & ACCP & ACCX & ACCN & _).
  assert (LO0 : 0x7fff7f800000 <= lo) by ul.
  assert (CHKF : chk_ok m 0x1db09 4).
  { apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [lia|]. intros _. split; [exact ACCF|]. right; right; right. ul. }
  assert (PCX : pctx m).
  { destruct IC as ((G2 & G1 & RM & SHC & RI) & _ & _ & M2S). split; [exact M2S| split; assumption]. }
  (* [comment removed for export] *)
  set (Qfin := fun (x : unit * stdout_st) (ms' : machine_state) => exists (m3 : mem),
         (exists (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
            ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7'
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m3 (seg_rom ctasegs))
         /\ munch [(lo, usp); (0x5af608, 0x5af608 + 232); (0xbc9f08, 0xbc9f08 + 1024)] m m3 /\ wmono ctasegs m m3
         /\ mem_inv ctasegs m3 /\ stk ctasegs m3 lo usp /\ stdout_file m3 (snd x)).
  assert (IMPL : impl ctasegs (at_node ctasegs) (emit_prog so) (epost Qfin)
                   (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FMT_emit) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vprintf m)).
  assert (L1 : lo <= usp - 2416) by ul.
  assert (L2 : kHighShadowEnd + 8 <= lo) by ul.
  assert (L3 : usp <= 2^47) by ul.
  pose proof (rw_cells_bound ctasegs m ap _ VA) as APB. cbn [cells_size csize Nat.add] in APB.
  assert (L4 : 0 <= ap < 2^63) by ul.
  { eapply impl_evt;
      [exact (vprintf_walkA RIP usp ap lo ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m ST L1 L2 L3 SPA L4 CHKF PCX PFC MI0)|].
    intros ms1 (m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & -> & MU1 & WM1 & MI1 & ST1 & FRf & FRv).
    assert (AG1 : agree_on (fun x => x < usp - 2416 \/ usp <= x) m m1).
    { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [lia| exact I]. }
    assert (EU96 : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; ul).
    (* [comment removed for export] *)
    assert (SF1 : stdout_file m1 (vso_get so)).
    { apply (stdout_file_agree so m m1); [| exact WM1| exact OUT0]. apply (agree_sub _ _ _ _ AG1). intros x Hx. ul. }
    assert (BY1 : bytes_at ctasegs m1 0x1db09 (zb [37; 100; 10; 0])) by (apply img_bytes; [exact MI1 | lia | cbn; lia | vm_compute; reflexivity]).
    assert (VA1 : va_area m1 ap [Z_to_bv 64 0]).
    { pose proof (rw_cells_agree ctasegs m m1 _ _ VA ltac:(apply (agree_sub _ _ _ _ AG1); intros x Hx; cbn [cells_size csize Nat.add] in Hx; ul) WM1) as V.
      exact (proj2 (proj1 V)). }
    assert (SSP1 : ssp_cells m1 g).
    { split.
      - apply (ro_cells_agree ctasegs m m1 _ _ SG1). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul.
      - apply (ro_cells_agree ctasegs m m1 _ _ SG2). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul. }
    assert (IC1 : ictx m1) by (apply (ictx_munch _ m m1 IC MU1 WM1); intros ?x ?Hx; cbn [in_rl ICR outside] in *; ul).
    assert (CHM : forall p n, chkr m p n -> chkr m1 p n).
    { intros p n H. apply (chkr_munch _ m m1 p n H MU1). intros x Hx. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in Hx. ul. }
    pose proof (stk_split ctasegs m1 lo (lo + 64) (usp + -96) ST1 ltac:(ul)) as (ST1a & ST1b).
    assert (STKC : forall p n, lo + 64 <= p -> p + n <= usp + -96 -> chkr m1 p n).
    { intros p n H1 H2. apply CHM. destruct (Z_lt_le_dec 0 n) as [NP|NN].
      - apply (chkr_of Σ m p n ART0); [ul| | ].
        + apply (af_acc_stack RT AF Σ m p n ART0); ul.
        + right; right; left. ul.
      - split; [intros i Hi; lia| split; [intros i Hi; lia|]]. split; [| lia]. unfold region_in_mem, kLowMemEnd, kHighMemEnd. right. ul. }
    assert (FMTC : chkr m1 0x1db09 4) by (apply CHM; apply (chkr_of Σ m _ _ ART0); [lia| exact ACCF| right; right; right; ul]).
    assert (ROD : rod_chk m1).
    { split; [| split]; apply CHM; (apply (chkr_of Σ m _ _ ART0); [lia| assumption| right; right; right; unfold PFX_A, XDIG_A, NULLS_A; ul]). }
    assert (CHBUF : chkr m1 RSTDOUT_BUF 1024).
    { apply CHM. apply (chkr_of Σ m _ _ ART0); [lia| | right; right; right; ul].
      apply (af_acc_static RT AF Σ m _ _ ART0); [lia|]. intros i Hi.
      split; [apply client_static_intro; lia| lia]. }
    pose proof (vfprintf_stdout_proof vso_get vso_set vso_GS vso_SS
                  (fwritex_stdout_proof RIP (fun St get set GS SS => stdout_writefn_proof get set GS SS)) RIP) as VF.
    unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
    pose proof (VF (Z_to_bv 64 0x1b2490) (Z_to_bv 64 (usp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 121609) (Z_to_bv 64 5961224)
                  (Z_to_bv 64 5961224) (Z_to_bv 64 121609) (Z_to_bv 64 ap) a3' a4' a5' a6' a7' (Z_to_bv 64 ap) s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6' F fc m1 so 0x1db09 ap [37; 100; 10; 0] [Z_to_bv 64 0] [PA_i 0] pieces_emit_0 2 (lo + 64) g) as IM.
    clear VF. unfold Monad.implM in IM.
    eapply impl_post_evt''.
    { apply IM; clear IM; rewrite ?EU96.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact SF1.
      - exact BY1.
      - repeat constructor; lia.
      - vm_compute; reflexivity.
      - exact VA1.
      - cbn [args_ok arg_ok]. split; [| exact I]. split; [lia| reflexivity].
      - vm_compute; reflexivity.
      - vm_compute; reflexivity.
      - exact ST1b.
      - unfold VF_DEPTH; ul.
      - unfold GLOBALS_TOP; ul.
      - ul.
      - exact SSP1.
      - exact MI1.
      - exact I.
      - lia.
      - unfold zlength, STATIC_SPLIT; cbn; lia.
      - lia.
      - unfold zlength; cbn; lia.
      - ul.
      - exact IC1.
      - exact STKC.
      - exact FMTC.
      - exact ROD.
      - exact CHBUF. }
    intros [|[xr st']] ms2 H2; [apply evt_done; exact I|].
    cbn [epost fst snd] in H2 |- *.
    destruct H2 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc2 & m2 & -> & MU2 & WM2 & MI2
                    & _ & _ & ST2 & SF2 & SSP2).
    rewrite EU96 in MU2, ST2.
    rewrite (ret_pc_even 0x1b2490) by lia.
    assert (AG2 : agree_on (fun x => usp + -96 <= x) m1 m2).
    { apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn. split; [lia|]. split; [ul| split; [ul| exact I]]. }
    pose proof (rw_cells_agree ctasegs m1 m2 _ _ FRf ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRf2.
    pose proof (rw_cells_agree ctasegs m1 m2 _ _ FRv ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRv2.
    eapply evt_mono.
    { apply (vprintf_walkB usp ap (lo + 64) junk (Z_to_bv 64 0x1b2490) ra gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 121609) (Z_to_bv 64 5961224)
               b0 b1 b2 b3 b4 b5 b6 b7 s2 (Z_to_bv 64 ap) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 Ft fc2 m2
               ST2 ltac:(lia) L3 FRf2 FRv2 MI2). }
    intros ms3 ((w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & RS3) & ST3).
    exists m2. split.
    { rewrite RS3. do 17 eexists. reflexivity. }
    split.
    { apply (munch_merge [(usp - 2416, usp)] [(lo + 64, usp + -96); (0x5af608, 0x5af608 + 232); (0xbc9f08, 0xbc9f08 + 1024)] _ m m1 m2 MU1 MU2).
      intros x Hx. cbn in Hx |- *. intuition lia. }
    split; [exact (wmono_trans ctasegs m m1 m2 WM1 WM2)|]. split; [exact MI2|].
    split; [| exact SF2]. apply (stk_merge ctasegs m2 lo (lo + 64) usp); [| exact ST3| ul].
    exact (stk_transport_disjoint ctasegs _ _ _ _ _ ST1a MU2 WM2 ltac:(cbn [disjoint_from]; ul)). }
  assert (IMPL2 : impl ctasegs (at_node ctasegs) (emit_prog so) (epost (fun x ms' => Qfin x ms' /\ snd x = emit0_next so))
                   (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FMT_emit) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vprintf m)).
  { eapply impl_mono; [eapply impl_tforall; [exact (leaves_emit so SO)| exact IMPL]|].
    intros [|x] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I| split; assumption]. }
  (* [comment removed for export] *)
  assert (RZ : realizes ctasegs c (TT (emit_prog so) (fun _ => t_emit [] T))).
  { apply (impl_realizes ctasegs SEGTOP_A asegs_wx asegs_below [1] _ (rt_allow RT Σ) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
             (fun x ms' => Qfin x ms' /\ snd x = emit0_next so) (fun _ => t_emit [] T)
             (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FMT_emit) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vprintf m) c
             (ASTA_PM_mat_stable RT AF Σ F0 fs0)); [| exact (tok_emit so SO)| exact Hc| exact IMPL2|].
    - intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
    - intros x ms' c' (HQ & HX) Hc'.
      assert (R : realizes ctasegs c' T).
      { apply Hk. eapply ASTA_conseq; [exact Hc'|]. intros ms <-.
        destruct HQ as (m3 & (v & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->)
                        & MU3 & WM3 & MI3 & ST3 & SF3).
        exists v, m3. split.
        { rewrite ESP. do 16 eexists. reflexivity. }
        split; [split; [| split; [exact MI3| split; [exact WM3| exact ST3]]]|].
        - apply (af_frame RT AF Σ m m3 lo ART0); [ul| | exact WM3].
          intros a Ha. apply MU3. cbn. split; [intros Hin; apply Ha; left; ul|].
          split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia|].
          split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia| exact I].
        - split; [| split].
          + intros a Ha Hout. apply MU3. cbn in Hout |- *. destruct Hout as (O1 & O2 & O3 & _). split; [| split; [lia| split; [lia| exact I]]].
            destruct (aclient_split RT AF Σ m usp _ ART0 Ha); ul.
          + rewrite <- HX. exact SF3.
          + intros ERR0. apply (stderr_wfile0_agree m m3); [| exact WM3| exact ERR0].
            apply (agree_of_munch _ _ _ _ MU3). intros y Hy. cbn. split; [ul| split; [lia| split; [lia| exact I]]]. }
      eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty ctasegs _ _ R). }
  eapply rz_conseq; [exact RZ|].
  eapply t_eq_trans; [apply (TT_emit so (fun _ => t_emit [] T) SO (t_emit_has_nil [] T))|].
  eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl.
Qed.
End XVprintf.
