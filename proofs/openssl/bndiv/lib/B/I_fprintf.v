(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ITree Nodes Decode SysStep ImageA RzCPS NodesA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Monad Stdio Canon PrintfModel PrintfFormats ProgDetDriver.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.P Require Import Printf_pieces Printf_bridge.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_m2s I_consts I_qck RT_iface D_iface D_defs D_kit D_clx. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import X_bridge. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import X_bridge2 I_iodefs I_lift F_achk F_printf_iface Printf_stdio_iface F_stdio_write F_fwritex_stderr F_stdio_flush F_fprintf I_pck I_pcbits I_pchead I_pcfmt I_vprintfw I_fprintfw I_fpbridge I_vprintf F_fwrite FX_lib F_pop_arg F_pkit X_open I_read.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma map_to_bytes_unsigned' : forall (s : list byte), zb (map bv_unsigned s) = s.
Proof. intros s. unfold zb. rewrite map_map. erewrite map_ext; [apply map_id|]. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma Forall_byte_of_forallb : forall l, forallb (fun c => (0 <=? c) && (c <? 256)) l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
  intros l H. apply Forall_forall. intros c Hc. rewrite forallb_forall in H. specialize (H c Hc).
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Section XFprintf.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis AF_PF : forall Σ m, ART RT Σ m -> pf_consts m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.


(* [comment removed for export] *)
Definition fp_ps (c : fp_case) : list (list Z) :=
  match c with
  | FPusage _ s => pieces_usage (map bv_unsigned s)
  | FPcannot_open _ s => pieces_cannot_open (map bv_unsigned s)
  | FPread_error _ s => pieces_read_error (map bv_unsigned s)
  | FPtoo_big => pieces_too_big
  end.

Lemma concat_fp_ps : forall c, concat (fp_ps c) = fp_msg c.
Proof.
  intros [a s | a s | a s |]; cbn [fp_ps fp_msg].
  - apply concat_pieces_usage.
  - unfold pieces_cannot_open, msg_cannot_open. cbn [concat]. rewrite !app_nil_l, ?app_nil_r. rewrite ?app_assoc. reflexivity.
  - unfold pieces_read_error, msg_read_error. cbn [concat]. rewrite !app_nil_l, ?app_nil_r. rewrite ?app_assoc. reflexivity.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Definition fp_Qfin (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem) (x : unit * unit)
    (ms' : machine_state) : Prop :=
  exists (m3 : mem),
    (exists (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
       ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m3 (seg_rom bsegs))
    /\ munch [(lo, usp); (0x5e7168, 0x5e7168 + 232)] m m3 /\ wmono bsegs m m3
    /\ mem_inv bsegs m3 /\ stk bsegs m3 lo usp /\ stderr_wfile0 m3.

(* [comment removed for export] *)
Lemma args_ok_lo_mono : forall Fp B BS m lo lo' sp ap slots args, args_ok Fp B BS m lo sp ap slots args -> lo <= lo' ->
  args_ok Fp B BS m lo' sp ap slots args.
Proof.
  intros Fp B BS m lo lo' sp ap slots. induction slots as [|w slots IH]; intros args H Hl.
  - destruct args; cbn in *; [exact I| exact H].
  - destruct args as [|a args]; [cbn; exact I|]. cbn [args_ok] in *. destruct H as [H1 H2]. split; [| exact (IH args H2 Hl)].
    destruct a; cbn [arg_ok] in *; try exact H1.
    destruct H1 as (sl & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). exists sl.
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [destruct B5 as [B5|B5]; [left; lia| right; exact B5]|]. exact (conj B6 (conj B7 (conj B8 B9))).
Qed.

(* [comment removed for export] *)
Lemma fp_tail : forall (m m2 : mem) (usp lo : Z) (g : word) (A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z)
    (a2v a3v a4v a5v a6v a7v : word) (junk : list byte)
    ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc,
  munch [(usp - 2432, usp)] m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
  stk bsegs m2 lo (usp + -112) -> 0x7fff7f800000 <= lo -> lo + 0x10000 <= usp -> usp <= 2^47 ->
  rw_cells bsegs m2 (usp + -112) (fpfr usp junk ra s0 s1 s2) ->
  rw_cells bsegs m2 (usp + -48) [C8 a2v; C8 a3v; C8 a4v; C8 a5v; C8 a6v; C8 a7v] ->
  stderr_wfile0 m2 -> ssp_cells m2 g -> ictx m2 -> (forall p n, lo + 64 <= p -> p + n <= usp + -112 -> chkr m2 p n) ->
  chkr m2 A (zlength fmt) -> rod_chk m2 ->
  bytes_at bsegs m2 A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
  args_ok RSTDERR (usp + -112 - 352) 80 m2 lo (usp + -112) (usp + -112 - VF_FRAME) [a2v; a3v; a4v; a5v; a6v; a7v] args ->
  printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
  65536 <= A -> A + zlength fmt <= STATIC_SPLIT -> Forall (fun p => zlength p <= OUT_MAX) ps ->
  impl bsegs (at_node bsegs) (stderr_prog [] ps tt) (epost (fp_Qfin ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m))
    (MS (mkR (Z_to_bv 64 0x1acb18) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 0x5e7168)
             (Z_to_bv 64 0x5e7168) (Z_to_bv 64 A) (Z_to_bv 64 (usp + -48)) a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -48))
             s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55edb0) fc None m2 (seg_rom bsegs)).
Proof using RIP.
  intros until fc. intros MU2 WM2 MI2 ST2 LO0 LOR L3 FRp1 FRva ERR2 SSP2 IC2 STKC FMTC ROD BY HF P1 AOK PP FPC HA0 HA1 SZ.
  assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
  pose proof (stk_split bsegs m2 lo (lo + 64) (usp + -112) ST2 ltac:(lia)) as (ST2a & ST2b).
  pose proof (vfprintf_stderr_proof (St := unit)
                (fwritex_stderr_proof RIP (fun St => @stdio_write_proof St))
                (stdio_write_flush_proof (fun St => @stdio_write_proof St)) RIP) as VF.
  unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
  pose proof (VF (Z_to_bv 64 0x1acb18) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 0x5e7168)
                (Z_to_bv 64 0x5e7168) (Z_to_bv 64 A) (Z_to_bv 64 (usp + -48)) a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -48))
                s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 tt A (usp + -48) fmt [a2v; a3v; a4v; a5v; a6v; a7v] args ps r (lo + 64) g) as IM.
  clear VF. unfold Monad.implM in IM.
  eapply impl_post_evt''.
  { apply (stderr_bridge bsegs ps [] tt (fun st' ms' => vfprintf_stderr_post (Z_to_bv 64 0x1acb18) (Z_to_bv 64 (usp + -112)) gp tp
              (Z_to_bv 64 A) (Z_to_bv 64 0x5e7168) (Z_to_bv 64 (usp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 F (lo + 64) g m2 st' ms')); [exact SZ|].
    apply IM; clear IM; rewrite ?EU112.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact (stderr_wfile0_wfile m2 ERR2).
    - exact BY.
    - exact HF.
    - exact P1.
    - exact (proj2 (proj1 FRva)).
    - exact (args_ok_lo_mono _ _ _ _ lo (lo + 64) _ _ _ _ AOK ltac:(lia)).
    - exact PP.
    - exact FPC.
    - exact ST2b.
    - unfold VF_DEPTH; lia.
    - unfold GLOBALS_TOP; lia.
    - lia.
    - exact SSP2.
    - exact MI2.
    - exact I.
    - exact HA0.
    - exact HA1.
    - lia.
    - unfold zlength; cbn; lia.
    - unfold kHighShadowEnd; lia.
    - exact IC2.
    - exact STKC.
    - exact FMTC.
    - exact ROD. }
  intros [|[xr st']] ms3 H3; [apply evt_done; exact I|].
  cbn [epost fst snd] in H3 |- *.
  destruct H3 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc3 & m3 & -> & MU3 & WM3 & MI3
                  & _ & _ & ST3 & ERR3 & SSP3).
  rewrite EU112 in MU3, ST3.
  rewrite (ret_pc_even 0x1acb18) by lia.
  assert (AG3 : agree_on (fun x => usp + -112 <= x) m2 m3).
  { apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn. split; [lia|]. split; [lia| exact I]. }
  unfold fpfr in FRp1.
  pose proof (rw_cells_agree bsegs m2 m3 _ _ FRp1 ltac:(apply (agree_sub _ _ _ _ AG3); intros x Hx; cbn in Hx; lia) WM3) as FRp3.
  pose proof (rw_cells_agree bsegs m2 m3 _ _ FRva ltac:(apply (agree_sub _ _ _ _ AG3); intros x Hx; cbn in Hx; lia) WM3) as FRva3.
  eapply evt_mono.
  { apply (fprintf_walkB usp (lo + 64) junk a2v a3v a4v a5v a6v a7v (Z_to_bv 64 0x1acb18) ra gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 A)
             (Z_to_bv 64 0x5e7168) b0 b1 b2 b3 b4 b5 b6 b7 s2 (Z_to_bv 64 (usp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 Ft fc3 m3
             ST3 ltac:(lia) L3 FRp3 FRva3 MI3). }
  intros ms4 ((w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & RS4) & ST4).
  exists m3. split.
  { rewrite RS4. do 17 eexists. reflexivity. }
  split.
  { apply (munch_merge [(usp - 2432, usp)] [(lo + 64, usp + -112); (0x5e7168, 0x5e7168 + 232)] _ m m2 m3 MU2 MU3).
    intros x Hx. cbn in Hx |- *. intuition lia. }
  split; [exact (wmono_trans bsegs m m2 m3 WM2 WM3)|]. split; [exact MI3|]. split; [| exact ERR3].
  apply (stk_merge bsegs m3 lo (lo + 64) usp); [| exact ST4| lia].
  exact (stk_transport_disjoint bsegs _ _ _ _ _ ST2a MU3 WM3 ltac:(cbn [disjoint_from]; lia)).
Qed.

Theorem fprintf_ok : fprintf_stderr_icontract RT OUT_repA ERR_repA IO_FPA.
Proof using AF RIP AF_SHW AF_PF.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c errp lo
    Ha0 Ha1 Ha2 Herrp HSTR HFD ERR0 (g & SG1 & SG2) ART0 MI0 CALL.
  subst a0 a1 a2 errp. intros T c' Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  destruct (AF_PF Σ m ART0) as (PFC & IC & ACCF & ACCP & ACCX & ACCN & ACCU & ACCO & ACCR & ACCT).
  assert (LO0 : 0x7fff7f800000 <= lo) by ul.
  assert (L3 : usp <= 2^47) by ul.
  assert (PCX : pctx m).
  { destruct IC as ((G2 & G1 & RM & SHC & RI) & _ & _ & M2S). split; [exact M2S| split; assumption]. }
  (* [comment removed for export] *)
  set (Qfin := fp_Qfin ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m).
  assert (IMPL : impl bsegs (at_node bsegs) (stderr_prog [] (fp_ps c) tt) (epost Qfin)
                   (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 (fp_fmt c))
                      (Z_to_bv 64 (fp_arg c)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fprintf m)).
  { eapply impl_evt with (P := fun ms' => impl bsegs (at_node bsegs) (stderr_prog [] (fp_ps c) tt) (epost Qfin) ms');
      [| intros ms' H; exact H].
    eapply evt_cut; [exact (fprintf_walkA1 usp lo ra gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 (fp_fmt c))
                               (Z_to_bv 64 (fp_arg c)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                               ST ltac:(ul) ltac:(ul) L3 PFC MI0)|].
    intros ms1 (m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & -> & MU1 & WM1 & MI1 & ST1 & FRp1 & FRva).
    assert (AG1 : agree_on (fun x => x < usp - 128 \/ usp <= x) m m1).
    { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [lia| exact I]. }
    assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; ul).
    assert (PCX1 : pctx m1) by (apply (pctx_munch _ m m1 PCX MU1 WM1); intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; ul).
    assert (CHM : forall p n, chk_ok m p n -> 0 <= p -> p + n <= 2^47 -> chk_ok m1 p n).
    { intros p n H Hp1 Hp2. apply (chk_ok_agree m m1 p n H Hp1 Hp2). apply (agree_sub _ _ _ _ AG1). intros x Hx. ul. }
    pose proof (munch_weaken [(usp - 128, usp)] [(usp - 2432, usp)] m m1 ltac:(unfold sub_fp; cbn [outside]; intros; lia) MU1) as MUacc.
    clear MU1.
    assert (ERR1 : stderr_wfile0 m1) by (apply (stderr_wfile0_agree m m1); [apply (agree_sub _ _ _ _ AG1); intros x Hx; ul| exact WM1| exact ERR0]).
    assert (SSP1 : ssp_cells m1 g).
    { split.
      - apply (ro_cells_agree bsegs m m1 _ _ SG1). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul.
      - apply (ro_cells_agree bsegs m m1 _ _ SG2). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul. }
    assert (IC1 : ictx m1) by (apply (ictx_munch _ m m1 IC MUacc WM1); intros ?x ?Hx; cbn [in_rl ICR outside] in *; ul).
    assert (PFC1 : pfcells m1) by (apply (pfcells_munch _ m m1 PFC MUacc WM1); intros ?x ?Hx; unfold in_PFR in Hx; cbn [outside]; ul).
    destruct c as [a s | a s | a s |].
    - (* [comment removed for export] *)
      destruct (HSTR a s eq_refl) as (BYs & NZ & LEN & CHS & SPAa & slack & SLK & SLKM & SLKB).
      pose proof (bytes_at_bound _ _ _ _ BYs) as BYB. rewrite length_app in BYB. cbn [length] in BYB.
      assert (CHKS : chk_ok m a (Z.of_nat (length s) + 1)).
      { apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [ul|]. intros Hn. destruct CHS as (CH & _). exact (CH Hn). }
      assert (CS1 : cstr_at m1 a s).
      { split; [| exact NZ]. apply (bytes_at_agree bsegs m m1 _ _ BYs). apply (agree_sub _ _ _ _ AG1). intros x Hx.
        rewrite length_app in Hx; cbn [length] in Hx. ul. }
      assert (SLOT1 : ro_cells bsegs m1 (usp + -48) [C8 (Z_to_bv 64 a)]).
      { pose proof (proj1 (F_fwritex.rw_cells_app bsegs _ _ [_] _) FRva) as (H & _). exact (proj1 H). }
      call (pcom_usage_spec RIP);
        [ reflexivity | reflexivity | exact SLOT1 | rewrite EU112; lia | ul | exact CS1 | ul | right; rewrite EU112; lia | ul
        | apply CHM; [exact CHKS| lia| ul] | rewrite EU112; exact ST1 | rewrite EU112; ul | unfold kHighShadowEnd; ul
        | rewrite EU112; ul | rewrite EU112; Z.div_mod_to_equations; lia
        | apply CHM; [apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [lia| intros _; split; [exact ACCU| right; right; right; ul]]| lia| ul]
        | exact PCX1 | exact MI1 | ].
      rename POST into ST2. rewrite EU112 in ST2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (PFC2 : pfcells mm) by (apply (pfcells_munch _ m mm PFC MUacc ltac:(assumption)); intros ?x ?Hx; unfold in_PFR in Hx; cbn [outside]; ul) end.
      destruct PFC2 as (_ & _ & _ & _ & RVF2).
      eapply evt_cut; [apply (fprintf_walkA2 usp junk ra s0 s1 s2); [exact FRp1| exact RVF2| exact L3| ul| assumption]|].
      intros ms2 (a3'' & ->).
      apply evt_done.
      lazymatch goal with |- impl _ _ _ _ (MS _ _ _ _ _ ?mm _) => set (m2 := mm) in * end.
      assert (CHR : forall p n, chkr m p n -> chkr m2 p n).
      { intros p n H. apply (chkr_munch _ m m2 p n H MUacc). intros y Hy. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in Hy. ul. }
      assert (AG2 : agree_on (fun x => x < usp - 2432 \/ usp <= x) m m2).
      { apply (agree_of_munch _ _ _ _ MUacc). intros y Hy. cbn. split; [lia| exact I]. }
      eapply (fp_tail m m2 usp lo g 0x210ec PrintfFormats.FMT_usage [PA_s (map bv_unsigned s)] (pieces_usage (map bv_unsigned s))
                (14 + zlength (map bv_unsigned s))).
      + exact MUacc.
      + assumption.
      + assumption.
      + exact ST2.
      + exact LO0.
      + ul.
      + exact L3.
      + exact FRp1.
      + exact FRva.
      + apply (stderr_wfile0_agree m m2); [apply (agree_sub _ _ _ _ AG2); intros y Hy; ul| assumption| exact ERR0].
      + split.
        * apply (ro_cells_agree bsegs m m2 _ _ SG1). apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn in Hy. ul.
        * apply (ro_cells_agree bsegs m m2 _ _ SG2). apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn in Hy. ul.
      + apply (ictx_munch _ m m2 IC MUacc ltac:(assumption)); intros ?y ?Hy; cbn [in_rl ICR outside] in *; ul.
      + intros p n H1 H2. apply CHR. destruct (Z_lt_le_dec 0 n) as [NP|NN].
        * apply (chkr_of RT AF_SHW Σ m p n ART0); [ul| | ].
          -- apply (af_acc_stack RT AF Σ m p n ART0); ul.
          -- right; right; left. ul.
        * split; [intros i Hi; lia| split; [intros i Hi; lia|]]. split; [| lia]. unfold region_in_mem, kLowMemEnd, kHighMemEnd. right. ul.
      + replace (zlength PrintfFormats.FMT_usage) with 17 by reflexivity.
        apply CHR. apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| exact ACCU| right; right; right; ul].
      + split; [| split]; apply CHR; (apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| assumption| right; right; right; unfold PFX_A, XDIG_A, NULLS_A; ul]).
      + apply img_bytes; [assumption | lia | cbn; lia | vm_compute; reflexivity].
      + apply Forall_byte_of_forallb. vm_compute. reflexivity.
      + exact pass1_ok_usage.
      + cbn [args_ok arg_ok]. split; [| exact I]. exists slack. cbn [fp_arg].
        rewrite (unsigned_lit a) by ul. rewrite map_to_bytes_unsigned'.
        assert (EZL : zlength (map bv_unsigned s) = Z.of_nat (length s)) by (unfold zlength; rewrite length_map; reflexivity).
        rewrite EZL. unfold zlength at 1.
        destruct CHS as (CHS1 & _).
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
        * apply (proj2 (bytes_at_app bsegs m2 a s (Z_to_bv 8 0 :: slack))). split.
          -- apply (bytes_at_agree bsegs m m2 _ _ (proj1 (proj1 (bytes_at_app bsegs m a s [Z_to_bv 8 0]) BYs))).
             apply (agree_sub _ _ _ _ AG2). intros y Hy. ul.
          -- apply (proj2 (bytes_at_app bsegs m2 _ [Z_to_bv 8 0] slack)). split.
             ++ apply (bytes_at_agree bsegs m m2 _ _ (proj2 (proj1 (bytes_at_app bsegs m a s [Z_to_bv 8 0]) BYs))).
                apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn [length] in Hy. ul.
             ++ cbn [length]. replace (a + Z.of_nat (length s) + Z.of_nat 1) with (a + Z.of_nat (length s) + 1) by lia.
                apply (bytes_at_agree bsegs m m2 _ _ SLK). apply (agree_sub _ _ _ _ AG2). intros y Hy. ul.
        * apply Forall_forall. intros zc Hzc. apply in_map_iff in Hzc. destruct Hzc as (b & <- & Hb).
          pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
          split; [| lia]. destruct (Z.eq_dec (bv_unsigned b) 0) as [E0|E0]; [| lia].
          exfalso. apply NZ. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity.
        * exact SLKM.
        * ul.
        * right. lia.
        * right. ul.
        * right. ul.
        * right. unfold VF_FRAME. ul.
        * apply CHR. apply (chkr_of RT AF_SHW Σ m _ _ ART0); [ul| | ]; apply CHS1; lia.
      + apply printf_pieces_usage. unfold zlength, INT_MAX. rewrite length_map. lia.
      + apply fp_calls_s. left; reflexivity.
      + lia.
      + unfold zlength, STATIC_SPLIT; cbn; lia.
      + unfold pieces_usage. repeat constructor; unfold OUT_MAX, zlength; rewrite ?length_map; cbn; lia.
    - (* [comment removed for export] *)
      destruct (HSTR a s eq_refl) as (BYs & NZ & LEN & CHS & SPAa & slack & SLK & SLKM & SLKB).
      pose proof (bytes_at_bound _ _ _ _ BYs) as BYB. rewrite length_app in BYB. cbn [length] in BYB.
      assert (CHKS : chk_ok m a (Z.of_nat (length s) + 1)).
      { apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [ul|]. intros Hn. destruct CHS as (CH & _). exact (CH Hn). }
      assert (CS1 : cstr_at m1 a s).
      { split; [| exact NZ]. apply (bytes_at_agree bsegs m m1 _ _ BYs). apply (agree_sub _ _ _ _ AG1). intros x Hx.
        rewrite length_app in Hx; cbn [length] in Hx. ul. }
      assert (SLOT1 : ro_cells bsegs m1 (usp + -48) [C8 (Z_to_bv 64 a)]).
      { pose proof (proj1 (F_fwritex.rw_cells_app bsegs _ _ [_] _) FRva) as (H & _). exact (proj1 H). }
      call (pcom_copen_spec RIP);
        [ reflexivity | reflexivity | exact SLOT1 | rewrite EU112; lia | ul | exact CS1 | ul | right; rewrite EU112; lia | ul
        | apply CHM; [exact CHKS| lia| ul] | rewrite EU112; exact ST1 | rewrite EU112; ul | unfold kHighShadowEnd; ul
        | rewrite EU112; ul | rewrite EU112; Z.div_mod_to_equations; lia
        | apply CHM; [apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [lia| intros _; split; [exact ACCO| right; right; right; ul]]| lia| ul]
        | exact PCX1 | exact MI1 | ].
      rename POST into ST2. rewrite EU112 in ST2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (PFC2 : pfcells mm) by (apply (pfcells_munch _ m mm PFC MUacc ltac:(assumption)); intros ?x ?Hx; unfold in_PFR in Hx; cbn [outside]; ul) end.
      destruct PFC2 as (_ & _ & _ & _ & RVF2).
      eapply evt_cut; [apply (fprintf_walkA2 usp junk ra s0 s1 s2); [exact FRp1| exact RVF2| exact L3| ul| assumption]|].
      intros ms2 (a3'' & ->).
      apply evt_done.
      lazymatch goal with |- impl _ _ _ _ (MS _ _ _ _ _ ?mm _) => set (m2 := mm) in * end.
      assert (CHR : forall p n, chkr m p n -> chkr m2 p n).
      { intros p n H. apply (chkr_munch _ m m2 p n H MUacc). intros y Hy. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in Hy. ul. }
      assert (AG2 : agree_on (fun x => x < usp - 2432 \/ usp <= x) m m2).
      { apply (agree_of_munch _ _ _ _ MUacc). intros y Hy. cbn. split; [lia| exact I]. }
      eapply (fp_tail m m2 usp lo g 0x3d197 PrintfFormats.FMT_cannot_open [PA_s (map bv_unsigned s)] (pieces_cannot_open (map bv_unsigned s))
                (18 + zlength (map bv_unsigned s))).
      + exact MUacc.
      + assumption.
      + assumption.
      + exact ST2.
      + exact LO0.
      + ul.
      + exact L3.
      + exact FRp1.
      + exact FRva.
      + apply (stderr_wfile0_agree m m2); [apply (agree_sub _ _ _ _ AG2); intros y Hy; ul| assumption| exact ERR0].
      + split.
        * apply (ro_cells_agree bsegs m m2 _ _ SG1). apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn in Hy. ul.
        * apply (ro_cells_agree bsegs m m2 _ _ SG2). apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn in Hy. ul.
      + apply (ictx_munch _ m m2 IC MUacc ltac:(assumption)); intros ?y ?Hy; cbn [in_rl ICR outside] in *; ul.
      + intros p n H1 H2. apply CHR. destruct (Z_lt_le_dec 0 n) as [NP|NN].
        * apply (chkr_of RT AF_SHW Σ m p n ART0); [ul| | ].
          -- apply (af_acc_stack RT AF Σ m p n ART0); ul.
          -- right; right; left. ul.
        * split; [intros i Hi; lia| split; [intros i Hi; lia|]]. split; [| lia]. unfold region_in_mem, kLowMemEnd, kHighMemEnd. right. ul.
      + replace (zlength PrintfFormats.FMT_cannot_open) with 21 by reflexivity.
        apply CHR. apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| exact ACCO| right; right; right; ul].
      + split; [| split]; apply CHR; (apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| assumption| right; right; right; unfold PFX_A, XDIG_A, NULLS_A; ul]).
      + apply img_bytes; [assumption | lia | cbn; lia | vm_compute; reflexivity].
      + apply Forall_byte_of_forallb. vm_compute. reflexivity.
      + exact pass1_ok_cannot_open.
      + cbn [args_ok arg_ok]. split; [| exact I]. exists slack. cbn [fp_arg].
        rewrite (unsigned_lit a) by ul. rewrite map_to_bytes_unsigned'.
        assert (EZL : zlength (map bv_unsigned s) = Z.of_nat (length s)) by (unfold zlength; rewrite length_map; reflexivity).
        rewrite EZL. unfold zlength at 1.
        destruct CHS as (CHS1 & _).
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
        * apply (proj2 (bytes_at_app bsegs m2 a s (Z_to_bv 8 0 :: slack))). split.
          -- apply (bytes_at_agree bsegs m m2 _ _ (proj1 (proj1 (bytes_at_app bsegs m a s [Z_to_bv 8 0]) BYs))).
             apply (agree_sub _ _ _ _ AG2). intros y Hy. ul.
          -- apply (proj2 (bytes_at_app bsegs m2 _ [Z_to_bv 8 0] slack)). split.
             ++ apply (bytes_at_agree bsegs m m2 _ _ (proj2 (proj1 (bytes_at_app bsegs m a s [Z_to_bv 8 0]) BYs))).
                apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn [length] in Hy. ul.
             ++ cbn [length]. replace (a + Z.of_nat (length s) + Z.of_nat 1) with (a + Z.of_nat (length s) + 1) by lia.
                apply (bytes_at_agree bsegs m m2 _ _ SLK). apply (agree_sub _ _ _ _ AG2). intros y Hy. ul.
        * apply Forall_forall. intros zc Hzc. apply in_map_iff in Hzc. destruct Hzc as (b & <- & Hb).
          pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
          split; [| lia]. destruct (Z.eq_dec (bv_unsigned b) 0) as [E0|E0]; [| lia].
          exfalso. apply NZ. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity.
        * exact SLKM.
        * ul.
        * right. lia.
        * right. ul.
        * right. ul.
        * right. unfold VF_FRAME. ul.
        * apply CHR. apply (chkr_of RT AF_SHW Σ m _ _ ART0); [ul| | ]; apply CHS1; lia.
      + apply printf_pieces_cannot_open. unfold zlength, INT_MAX. rewrite length_map. lia.
      + apply fp_calls_s. right; left; reflexivity.
      + lia.
      + unfold zlength, STATIC_SPLIT; cbn; lia.
      + unfold pieces_cannot_open. repeat constructor; unfold OUT_MAX, zlength; rewrite ?length_map; cbn; lia.
    - (* [comment removed for export] *)
      destruct (HSTR a s eq_refl) as (BYs & NZ & LEN & CHS & SPAa & slack & SLK & SLKM & SLKB).
      pose proof (bytes_at_bound _ _ _ _ BYs) as BYB. rewrite length_app in BYB. cbn [length] in BYB.
      assert (CHKS : chk_ok m a (Z.of_nat (length s) + 1)).
      { apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [ul|]. intros Hn. destruct CHS as (CH & _). exact (CH Hn). }
      assert (CS1 : cstr_at m1 a s).
      { split; [| exact NZ]. apply (bytes_at_agree bsegs m m1 _ _ BYs). apply (agree_sub _ _ _ _ AG1). intros x Hx.
        rewrite length_app in Hx; cbn [length] in Hx. ul. }
      assert (SLOT1 : ro_cells bsegs m1 (usp + -48) [C8 (Z_to_bv 64 a)]).
      { pose proof (proj1 (F_fwritex.rw_cells_app bsegs _ _ [_] _) FRva) as (H & _). exact (proj1 H). }
      call (pcom_rerr_spec RIP);
        [ reflexivity | reflexivity | exact SLOT1 | rewrite EU112; lia | ul | exact CS1 | ul | right; rewrite EU112; lia | ul
        | apply CHM; [exact CHKS| lia| ul] | rewrite EU112; exact ST1 | rewrite EU112; ul | unfold kHighShadowEnd; ul
        | rewrite EU112; ul | rewrite EU112; Z.div_mod_to_equations; lia
        | apply CHM; [apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [lia| intros _; split; [exact ACCR| right; right; right; ul]]| lia| ul]
        | exact PCX1 | exact MI1 | ].
      rename POST into ST2. rewrite EU112 in ST2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (PFC2 : pfcells mm) by (apply (pfcells_munch _ m mm PFC MUacc ltac:(assumption)); intros ?x ?Hx; unfold in_PFR in Hx; cbn [outside]; ul) end.
      destruct PFC2 as (_ & _ & _ & _ & RVF2).
      eapply evt_cut; [apply (fprintf_walkA2 usp junk ra s0 s1 s2); [exact FRp1| exact RVF2| exact L3| ul| assumption]|].
      intros ms2 (a3'' & ->).
      apply evt_done.
      lazymatch goal with |- impl _ _ _ _ (MS _ _ _ _ _ ?mm _) => set (m2 := mm) in * end.
      assert (CHR : forall p n, chkr m p n -> chkr m2 p n).
      { intros p n H. apply (chkr_munch _ m m2 p n H MUacc). intros y Hy. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in Hy. ul. }
      assert (AG2 : agree_on (fun x => x < usp - 2432 \/ usp <= x) m m2).
      { apply (agree_of_munch _ _ _ _ MUacc). intros y Hy. cbn. split; [lia| exact I]. }
      eapply (fp_tail m m2 usp lo g 0x3d1ac PrintfFormats.FMT_read_error [PA_s (map bv_unsigned s)] (pieces_read_error (map bv_unsigned s))
                (20 + zlength (map bv_unsigned s))).
      + exact MUacc.
      + assumption.
      + assumption.
      + exact ST2.
      + exact LO0.
      + ul.
      + exact L3.
      + exact FRp1.
      + exact FRva.
      + apply (stderr_wfile0_agree m m2); [apply (agree_sub _ _ _ _ AG2); intros y Hy; ul| assumption| exact ERR0].
      + split.
        * apply (ro_cells_agree bsegs m m2 _ _ SG1). apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn in Hy. ul.
        * apply (ro_cells_agree bsegs m m2 _ _ SG2). apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn in Hy. ul.
      + apply (ictx_munch _ m m2 IC MUacc ltac:(assumption)); intros ?y ?Hy; cbn [in_rl ICR outside] in *; ul.
      + intros p n H1 H2. apply CHR. destruct (Z_lt_le_dec 0 n) as [NP|NN].
        * apply (chkr_of RT AF_SHW Σ m p n ART0); [ul| | ].
          -- apply (af_acc_stack RT AF Σ m p n ART0); ul.
          -- right; right; left. ul.
        * split; [intros i Hi; lia| split; [intros i Hi; lia|]]. split; [| lia]. unfold region_in_mem, kLowMemEnd, kHighMemEnd. right. ul.
      + replace (zlength PrintfFormats.FMT_read_error) with 23 by reflexivity.
        apply CHR. apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| exact ACCR| right; right; right; ul].
      + split; [| split]; apply CHR; (apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| assumption| right; right; right; unfold PFX_A, XDIG_A, NULLS_A; ul]).
      + apply img_bytes; [assumption | lia | cbn; lia | vm_compute; reflexivity].
      + apply Forall_byte_of_forallb. vm_compute. reflexivity.
      + exact pass1_ok_read_error.
      + cbn [args_ok arg_ok]. split; [| exact I]. exists slack. cbn [fp_arg].
        rewrite (unsigned_lit a) by ul. rewrite map_to_bytes_unsigned'.
        assert (EZL : zlength (map bv_unsigned s) = Z.of_nat (length s)) by (unfold zlength; rewrite length_map; reflexivity).
        rewrite EZL. unfold zlength at 1.
        destruct CHS as (CHS1 & _).
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
        * apply (proj2 (bytes_at_app bsegs m2 a s (Z_to_bv 8 0 :: slack))). split.
          -- apply (bytes_at_agree bsegs m m2 _ _ (proj1 (proj1 (bytes_at_app bsegs m a s [Z_to_bv 8 0]) BYs))).
             apply (agree_sub _ _ _ _ AG2). intros y Hy. ul.
          -- apply (proj2 (bytes_at_app bsegs m2 _ [Z_to_bv 8 0] slack)). split.
             ++ apply (bytes_at_agree bsegs m m2 _ _ (proj2 (proj1 (bytes_at_app bsegs m a s [Z_to_bv 8 0]) BYs))).
                apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn [length] in Hy. ul.
             ++ cbn [length]. replace (a + Z.of_nat (length s) + Z.of_nat 1) with (a + Z.of_nat (length s) + 1) by lia.
                apply (bytes_at_agree bsegs m m2 _ _ SLK). apply (agree_sub _ _ _ _ AG2). intros y Hy. ul.
        * apply Forall_forall. intros zc Hzc. apply in_map_iff in Hzc. destruct Hzc as (b & <- & Hb).
          pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
          split; [| lia]. destruct (Z.eq_dec (bv_unsigned b) 0) as [E0|E0]; [| lia].
          exfalso. apply NZ. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity.
        * exact SLKM.
        * ul.
        * right. lia.
        * right. ul.
        * right. ul.
        * right. unfold VF_FRAME. ul.
        * apply CHR. apply (chkr_of RT AF_SHW Σ m _ _ ART0); [ul| | ]; apply CHS1; lia.
      + apply printf_pieces_read_error. unfold zlength, INT_MAX. rewrite length_map. lia.
      + apply fp_calls_s. right; right; left; reflexivity.
      + lia.
      + unfold zlength, STATIC_SPLIT; cbn; lia.
      + unfold pieces_read_error. repeat constructor; unfold OUT_MAX, zlength; rewrite ?length_map; cbn; lia.
    - (* [comment removed for export] *)
      call (pcom_toobig_spec RIP);
        [ reflexivity | reflexivity | rewrite EU112; exact ST1 | rewrite EU112; ul | unfold kHighShadowEnd; ul
        | rewrite EU112; ul | rewrite EU112; Z.div_mod_to_equations; lia | ul
        | apply CHM; [apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [lia| intros _; split; [exact ACCT| right; right; right; ul]]| lia| ul]
        | exact PCX1 | exact MI1 | ].
      rename POST into ST2. rewrite EU112 in ST2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (PFC2 : pfcells mm) by (apply (pfcells_munch _ m mm PFC MUacc ltac:(assumption)); intros ?y ?Hy; unfold in_PFR in Hy; cbn [outside]; ul) end.
      destruct PFC2 as (_ & _ & _ & _ & RVF2).
      eapply evt_cut; [apply (fprintf_walkA2 usp junk ra s0 s1 s2); [exact FRp1| exact RVF2| exact L3| ul| assumption]|].
      intros ms2 (a3'' & ->).
      apply evt_done.
      lazymatch goal with |- impl _ _ _ _ (MS _ _ _ _ _ ?mm _) => set (m2 := mm) in * end.
      assert (CHR : forall p n, chkr m p n -> chkr m2 p n).
      { intros p n H. apply (chkr_munch _ m m2 p n H MUacc). intros y Hy. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in Hy. ul. }
      assert (AG2 : agree_on (fun x => x < usp - 2432 \/ usp <= x) m m2).
      { apply (agree_of_munch _ _ _ _ MUacc). intros y Hy. cbn. split; [lia| exact I]. }
      eapply (fp_tail m m2 usp lo g 0x2ef35 PrintfFormats.FMT_too_big [PA_u 67108864] pieces_too_big 38).
      + exact MUacc.
      + assumption.
      + assumption.
      + exact ST2.
      + exact LO0.
      + ul.
      + exact L3.
      + exact FRp1.
      + exact FRva.
      + apply (stderr_wfile0_agree m m2); [apply (agree_sub _ _ _ _ AG2); intros y Hy; ul| assumption| exact ERR0].
      + split.
        * apply (ro_cells_agree bsegs m m2 _ _ SG1). apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn in Hy. ul.
        * apply (ro_cells_agree bsegs m m2 _ _ SG2). apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn in Hy. ul.
      + apply (ictx_munch _ m m2 IC MUacc ltac:(assumption)); intros ?y ?Hy; cbn [in_rl ICR outside] in *; ul.
      + intros p n H1 H2. apply CHR. destruct (Z_lt_le_dec 0 n) as [NP|NN].
        * apply (chkr_of RT AF_SHW Σ m p n ART0); [ul| | ].
          -- apply (af_acc_stack RT AF Σ m p n ART0); ul.
          -- right; right; left. ul.
        * split; [intros i Hi; lia| split; [intros i Hi; lia|]]. split; [| lia]. unfold region_in_mem, kLowMemEnd, kHighMemEnd. right. ul.
      + replace (zlength PrintfFormats.FMT_too_big) with 33 by reflexivity.
        apply CHR. apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| exact ACCT| right; right; right; ul].
      + split; [| split]; apply CHR; (apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| assumption| right; right; right; unfold PFX_A, XDIG_A, NULLS_A; ul]).
      + apply img_bytes; [assumption | lia | cbn; lia | vm_compute; reflexivity].
      + apply Forall_byte_of_forallb. vm_compute. reflexivity.
      + exact pass1_ok_too_big.
      + cbn [args_ok arg_ok fp_arg]. split; [| exact I]. split; [lia| reflexivity].
      + exact printf_pieces_too_big.
      + exact fp_calls_too_big.
      + lia.
      + unfold zlength, STATIC_SPLIT; cbn; lia.
      + unfold pieces_too_big. repeat constructor; unfold OUT_MAX, zlength; cbn; lia. }
  assert (MSGB : zlength (fp_msg c) <= 2^26).
  { destruct c as [a s | a s | a s |]; cbn [fp_msg];
      try (destruct (HSTR a s eq_refl) as (_ & _ & LEN & _)); unfold msg_usage, msg_cannot_open, msg_read_error, msg_too_big, zlength;
      rewrite ?length_app, ?length_map; cbn; lia. }
  assert (TOK : tok [2] (stderr_prog [] (fp_ps c) tt)).
  { apply tok_stderr_fprintf. cbn [app]. rewrite concat_fp_ps. exact MSGB. }
  assert (RZ : realizes bsegs c' (TT (stderr_prog [] (fp_ps c) tt) (fun _ => t_emit [] T))).
  { apply (impl_realizes bsegs SEGTOP_A asegs_wx asegs_below [2] _ (rt_allow RT Σ) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
             Qfin (fun _ => t_emit [] T)
             (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 (fp_fmt c))
                (Z_to_bv 64 (fp_arg c)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fprintf m) c'
             (ASTA_PM_mat_stable RT AF Σ F0 fs0)); [| exact TOK| exact Hc| exact IMPL|].
    - intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
    - intros x ms' c2 HQ Hc2.
      assert (R : realizes bsegs c2 T).
      { apply Hk. eapply ASTA_conseq; [exact Hc2|]. intros ms <-.
        destruct HQ as (m3 & (v & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->)
                        & MU3 & WM3 & MI3 & ST3 & ERR3).
        exists v, m3. split.
        { rewrite ESP. do 16 eexists. reflexivity. }
        split; [split; [| split; [exact MI3| split; [exact WM3| exact ST3]]]|].
        - apply (af_frame RT AF Σ m m3 lo ART0); [ul| | exact WM3].
          intros a Ha. apply MU3. cbn. split; [intros Hin; apply Ha; left; ul|].
          split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia| exact I].
        - split; [| split].
          + intros a Ha Hout. apply MU3. cbn in Hout |- *. destruct Hout as (O1 & O2 & O3 & _). split; [| split; [lia| exact I]].
            destruct (aclient_split RT AF Σ m usp _ ART0 Ha); ul.
          + exact ERR3.
          + intros so OUT0. apply (stdout_file_agree so m m3); [| exact WM3| exact OUT0].
            apply (agree_of_munch _ _ _ _ MU3). intros y Hy. cbn. split; [ul| split; [lia| exact I]]. }
      eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty bsegs _ _ R). }
  eapply rz_conseq; [exact RZ|].
  eapply t_eq_trans; [apply (TT_stderr_fprintf (fp_ps c) [] tt (fun _ => t_emit [] T)); [cbn [app]; rewrite concat_fp_ps; exact MSGB| apply t_emit_has_nil]|].
  cbn [app]. rewrite concat_fp_ps.
  eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl.
Qed.
End XFprintf.
