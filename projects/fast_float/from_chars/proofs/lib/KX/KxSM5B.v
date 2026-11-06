(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxFrame FxCall FxRgs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_app2 B_rt_stmt B_rt_tls.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.

Module B_smalloc5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Perf.   (* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas B_rt_tls.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_tls OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_rt_m2s.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac lia4 ::= first [ lia_t1 | lia_t2 | lia_d1 | lia_app2 | lia_t3 ].  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation BSEGS := AsanUbsan.M.loaded_segments.
Tactic Notation "show" string(tag) := match goal with |- ?g => idtac tag g end.

(* [comment removed for export] *)
Notation K := 5%Z.
Notation ENTRY := 0x4b3d0%Z.
Notation NFR := 512%Z.        (* [comment removed for export] *)
Notation SZ := 2048%Z.          (* [comment removed for export] *)
Notation SHN := 256%Z.          (* [comment removed for export] *)
Notation FLOFF := 35840%Z.     (* [comment removed for export] *)
Notation FROFF := 5279744%Z.   (* [comment removed for export] *)
Notation HOFF := 40%Z.         (* [comment removed for export] *)

Lemma fk_nframes_5 : fk_nframes K = NFR. Proof. reflexivity. Qed.
Lemma fk_size_5 : fk_size K = SZ. Proof. reflexivity. Qed.
Lemma fk_hint_5 : forall FS, fk_hint FS K = (FS + HOFF)%Z. Proof. intros. reflexivity. Qed.
Lemma fk_flags_5 : forall FS, fk_flags FS K = (FS + FLOFF)%Z.
Proof. intros. unfold fk_flags. change (32 * Z.shiftl (Z.shiftr 1023 (10 - K)) (10 - K))%Z with (FLOFF - 4096)%Z. lia. Qed.
Lemma fk_frame_5 : forall FS pos, fk_frame FS K pos = (FS + FROFF + pos * SZ)%Z.
Proof. intros. unfold fk_frame. rewrite fk_size_5. lia. Qed.

Lemma land_511 : forall h, (0 <= h)%Z -> Z.land h 511 = (h mod 512)%Z.
Proof. intros h Hh. change 511%Z with (2^9 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. Qed.

Ltac solve_W_ok_rt := solve_W_rt.  (* [comment removed for export] *)

Section Proof.
  Hypothesis TLS : tls_chain_stmt.
  Hypothesis M2S : m2s_stmt 0x4b690.

  #[using="TLS M2S"] Lemma smalloc5_spec : smalloc5_stmt.
  Proof. LiaFast.lf_pins (fun (TLS M2S : LiaFast.U) => LiaFast.u0).
    unfold smalloc5_stmt, smalloc_stmt.
    intros until fl.
    rewrite !fk_nframes_5, !fk_size_5, !fk_hint_5, !fk_flags_5, !fk_frame_5.
    unfold smalloc_post, smalloc_W.
    rewrite !fk_nframes_5, !fk_size_5, !fk_hint_5, !fk_flags_5, !fk_frame_5.
    change (Z.to_nat (SZ / 8)) with 256%nat. change (SZ / 8)%Z with 256%Z. change (Z.to_nat (SZ - 40)) with 2008%nat.
    intros Htp RTH FSC HINT Hh FL LEN NTH SLOT SHS ST SP1 SP2 SP3 AL16 SEPFS PRG PRT RDJ1 RDJ2 RA.
    subst tp.
    remember (rt_FS v) as FS eqn:HFS.
    remember (h mod NFR)%Z as pos eqn:Hpos.
    assert (Hposr : (0 <= pos < NFR)%Z) by (subst pos; apply Z.mod_pos_bound; lia).
    unfold fs_cells_ok in FSC.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
      pose proof (munch_refl [(bv_unsigned sp - SMALLOC_NEED, bv_unsigned sp); (FS + HOFF, FS + 48);
                              (FS + FLOFF + pos, FS + FLOFF + pos + 1);
                              (FS + FROFF + pos * SZ, FS + FROFF + pos * SZ + SZ);
                              (ASAN_B + (FS + FROFF + pos * SZ) / 8, ASAN_B + (FS + FROFF + pos * SZ) / 8 + 256)]%Z m0) as MU;
      pose proof (wmono_refl BSEGS m0) as WM
    end.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (u8arr_bound _ _ _ _ FL) as Bfl.
    pose proof RTH as RTH0. open_RT RTH0.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Hc1 & Hc2 & Ht1 & Ht2 & Hb1 & Hb2).
    rewrite <- HFS in *.
    clear RT1 RT2 RT2b RT3 RT4 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb.
    unfold rt_disj in RDJ1, RDJ2.
    set (F := (FS + FROFF + pos * SZ)%Z) in *.
    assert (HF : (app2r (F) (F + SZ))%Z /\ (F + SZ <= FS + 11571200 /\ FS + 36352 <= F /\ F mod 2048 = 0)%Z).
    { subst F. split; [destruct HFS1 as [[X1 X2]|X1]; [left; split; nia | right; nia] |]. Z.div_mod_to_equations. nia. }
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 6 step. (* [comment removed for export] *)
    do 2 step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as Usp.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply TLS with (v := v) | ] end.
    { reflexivity. }
    { reflexivity. }
    { eapply RT_transport; [exact RTH | exact MU | solve_W_ok_rt]. }
    { rewrite Usp. replace (bv_unsigned sp + -32 - 176)%Z with (bv_unsigned sp + -208)%Z by lia. exact ST. }
    { rewrite Usp. lia. } { rewrite Usp. lia. } { rewrite Usp. lia. } { rewrite Usp. Z.div_mod_to_equations. lia. }
    { exact PRG. } { exact PRT. }
    { rewrite Usp. unfold rt_disj. lia. }
    { rewrite unsigned_lit by lia. reflexivity. }
    lazymatch goal with |- forall ms', tls_chain_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc ms' -> _ => post_call BSEGS mc end.
    clear RTH.
    rewrite ?Usp in *.
    lazymatch goal with H : RT ?m2 v |- _ => rename H into RTH end.
    pose proof RTH as RTH1. open_RT RTH1. rewrite <- ?HFS in *.
    clear RT2 RT2b RT3 RT5 RT6 RT7 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb RTP.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit h) by lia. rewrite (land_511 h) by lia. rewrite <- Hpos.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (u8arr_read BSEGS mc (FS + FLOFF)%Z fl pos (Z_to_bv 8 0) (Z_to_bv 64 (FS + FLOFF + pos)) FL NTH ltac:(lia) eq_refl) as RD end.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (u8arr_store_ok BSEGS mc (FS + FLOFF)%Z fl pos (Z_to_bv 64 (FS + FLOFF + pos)) FL ltac:(lia) eq_refl) as SOK end.
    step. (* [comment removed for export] *)
    change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
      pose proof (u8arr_write BSEGS mc (FS + FLOFF)%Z fl pos (Z_to_bv 8 1) FL ltac:(lia)) as FL' end.
    clear FL. store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit pos) by lia. rewrite (Z.shiftl_mul_pow2 pos 11) by lia.
    lazymatch goal with |- context [Z_to_bv 64 (FS + ?a + (?b + pos * 2 ^ 11))%Z] =>
      replace (Z_to_bv 64 (FS + a + (b + pos * 2 ^ 11)))%Z with (Z_to_bv 64 F) by (subst F; f_equal; lia) end.
    (* [comment removed for export] *)
    carve_frame 8%nat SLOT. rename FR0 into FRT.
    destruct (stk_split BSEGS _ F (F + 32)%Z (F + 2040)%Z SLOT ltac:(lia)) as [SLO SMID]. clear SLOT.
    carve_frame 8%nat SLO. rename FR0 into FRR.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply M2S | post_call BSEGS mc ] end.
    1:{ split; assumption. }
    1:{ assumption. }
    1:{ rewrite unsigned_lit by lia. lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    rewrite (unsigned_lit F) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    carve_frame 256%nat SHS.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      stash_all_but mc FR0;
      pose proof (munch_refl [(ASAN_B + F / 8, ASAN_B + F / 8 + 256)]%Z mc) as MUr;
      pose proof (wmono_refl BSEGS mc) as WMr end.
    do 32 step. (* [comment removed for export] *)
    unstash_all MUr WMr. clear MUr WMr.
    do 5 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    carve_frame 24%nat SLO.
    carve_frame 2008%nat SMID.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with
      | H1 : rw_cells BSEGS mc (F + 0)%Z [CB 24 ?j1], H2 : rw_cells BSEGS mc (F + 24)%Z ?c2,
        H3 : rw_cells BSEGS mc (F + 32)%Z [CB 2008 ?j3], H4 : rw_cells BSEGS mc (F + 2040)%Z ?c4 |- _ =>
          assert (FRAME : rw_cells BSEGS mc F ([CB 24 j1] ++ c2 ++ [CB 2008 j3] ++ c4));
          [ apply (proj2 (rw_cells_app _ _ _ _ _)); split; [rewrite <- (Z.add_0_r F); exact H1|];
            cbn [cells_size csize Nat.add]; change (Z.of_nat 24) with 24%Z;
            apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H2|];
            cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8%Z;
            replace (F + 24 + 8)%Z with (F + 32)%Z by lia;
            apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H3|];
            cbn [cells_size csize Nat.add]; change (Z.of_nat 2008) with 2008%Z;
            replace (F + 32 + 2008)%Z with (F + 2040)%Z by lia; exact H4
          | clear H1 H2 H3 H4; cbn [app] in FRAME ]
      end end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with
      | H : rw_cells BSEGS mc (ASAN_B + F / 8 + 0)%Z ?cs |- _ =>
          rewrite (Z.add_0_r (ASAN_B + F / 8)%Z) in H;
          pose proof (rw_cells_merge BSEGS mc (ASAN_B + F / 8)%Z [] cs [] ltac:(rewrite app_nil_r; cbn [app]; exact H)) as SHADOW;
          clear H; cbn [app cells_size csize Nat.add] in SHADOW;
          replace (cells_bytes cs) with (zeros 256) in SHADOW by (vm_compute; reflexivity)
      end end.
    finish.
    all: try (rewrite ?Z_to_bv_bv_unsigned; exact FRAME).
    all: try (match goal with H : rw_cells _ ?mc ?A [C8 (Z_to_bv 64 ?x)] |- rw_cells _ ?mc ?A [C8 (Z_to_bv 64 (?x mod 2 ^ 64))] =>
          replace (Z_to_bv 64 (x mod 2^64)) with (Z_to_bv 64 x); [exact H|];
          apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
          change (2 ^ Z.of_N 64)%Z with (2^64)%Z; rewrite Z.mod_mod by lia; reflexivity end).
    all: try (eapply munch_ext; [exact MU | cbn; intros; lia]).
  Qed.
End Proof.
End B_smalloc5.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_app2 OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_tls OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_rt_m2s OSSVerify.Proofs.fast_float.from_chars.lib.KX.KxSM5B.B_smalloc5.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn M4B_lm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4B_lm.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun KxTac KxRtB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition RGS0 : list region :=
  [ RG SWB SWS RW TEmpty;
    track (RGz (fsc 40) 8 RW TEmpty) 0 (bv8 H5);
    RG (fsc FL5) P5 RZ TEmpty;
    RG (ladd (fsc FL5) P5) (lconst 1) RZ TEmpty;
    RG (ladd (fsc (FL5 + 1)) P5) (laddc (lscale (-1) P5) 511) RZ TEmpty;
    RG (ladd (fsc AR5) (lscale 2048 P5)) (lconst 2048) RW TEmpty;
    RG (ladd (fsh AR5) (lscale 256 P5)) (lconst 256) RW TEmpty;
    fs_hdr_c; sb_uar_t ] ++ rt_rgs_t ++ relro_rgs.
Lemma RGS0_eq : SM5_RGS false = RGS0. Proof. reflexivity. Qed.
Definition RGS1 : list region :=
  [ RG SWB SWS RW TEmpty;
    track (RGz (fsc 40) 8 RW TEmpty) 0 (bv8 (laddc H5 1));
    RG (fsc FL5) P5 RZ TEmpty;
    track (RG (ladd (fsc FL5) P5) (lconst 1) RZ TEmpty) 0 [BK 1];
    RG (ladd (fsc (FL5 + 1)) P5) (laddc (lscale (-1) P5) 511) RZ TEmpty;
    track (track (RG (ladd (fsc AR5) (lscale 2048 P5)) (lconst 2048) RW TEmpty) 24 (bv8 SP)) 2040 (bv8 FLB5);
    track (RG (ladd (fsh AR5) (lscale 256 P5)) (lconst 256) RW TEmpty) 0 (List.repeat (BK 0) 256);
    fs_hdr_c; sb_uar_t ] ++ rt_rgs_t ++ relro_rgs.
Lemma RGS1_eq : SM5_RGS true = RGS1. Proof. reflexivity. Qed.

Section SM5.
Variable E : valu.
Variable ms : machine_state.
Hypothesis Hd : sden BSEGS E SM5_P0 ms.

Local Abbreviation ra := (bv_unsigned (E 5%positive)).
Local Abbreviation sp := (bv_unsigned (E 4%positive)).
Local Abbreviation fsp := (bv_unsigned (E 10%positive)).
Local Abbreviation h4 := (bv_unsigned (E 13%positive)).
Local Abbreviation p4 := (bv_unsigned (E 14%positive)).
Local Abbreviation ctx := (bv_unsigned (E 15%positive)).
Local Abbreviation thr := (bv_unsigned (E 16%positive)).
Local Abbreviation blk := (bv_unsigned (E 17%positive)).
Local Abbreviation beg := (bv_unsigned (E 18%positive)).
Local Abbreviation tlsb := (bv_unsigned (E 19%positive)).
Local Abbreviation tlse := (bv_unsigned (E 20%positive)).
Local Abbreviation fbv := (bv_unsigned (E 21%positive)).
Local Abbreviation swb := (bv_unsigned (E 23%positive)).
Local Abbreviation sws := (bv_unsigned (E 24%positive)).

#[using="Type"] Lemma Bnd : forall x : positive, 0 <= bv_unsigned (E x) < two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. pose proof (bv_unsigned_in_range _ (E x)) as X. unfold bv_modulus in X. exact X. Qed.

(* [comment removed for export] *)
Ltac open_facts :=
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & HF & _); cbn [s_facts SM5_P0] in HF;
  unfold SM5_F, fks5_facts, rt_facts, two_class, two_class4k, stack_facts in HF; cbn [app] in HF;
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [?F H] end;
  cbn [fact_ok] in *;
  repeat match goal with H : context [lden E ?l] |- _ => progress lnorm_s_in H end;
  rewrite ?u_Z_to_bv in *; unfold vz in *; unfold KHI, KTOP, IMG_END, SH_LO in *.

#[using="Type"] Lemma rt_app_of_wrapped : forall x n, 6537216 <= x -> x + n <= 2 ^ 47 -> 0 <= n ->
  0 <= (-17594333495296 + (1 * x + 0)) mod two64 <= 2 ^ 64 + 2147446784 - n - 17594333495296 -> rt_app x n /\ app2r x (x + n).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x n H1 H2 H3 H4. unfold rt_app, app2r, KHI, KTOP. destruct (Z.le_gt_cases 17594333495296 x) as [Hh|Hl].
  - split; right; lia.
  - assert (Hm : (-17594333495296 + (1 * x + 0)) mod two64 = x - 17594333495296 + two64)
      by (symmetry; apply Z.mod_unique with (q := -1); unfold two64; lia).
    rewrite Hm in H4. unfold two64 in H4. split; left; lia.
Qed.
#[using="Type"] Lemma rt_app_of_wrapped4k : forall x n, 4096 <= x -> x + n <= 2 ^ 47 -> 0 <= n ->
  0 <= (-17594333495296 + (1 * x + 0)) mod two64 <= 2 ^ 64 + 2147446784 - n - 17594333495296 -> rt_app x n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x n H1 H2 H3 H4. unfold rt_app, KHI. destruct (Z.le_gt_cases 17594333495296 x) as [Hh|Hl].
  - right; lia.
  - left. assert (Hm : (-17594333495296 + (1 * x + 0)) mod two64 = x - 17594333495296 + two64)
      by (symmetry; apply Z.mod_unique with (q := -1); unfold two64; lia).
    rewrite Hm in H4. unfold two64 in H4. lia.
Qed.

#[using="ms Hd"] Lemma sm5_facts :
  ra mod 2 = 0 /\ 0 <= p4 <= 511 /\ h4 mod 512 = p4 /\
  6537216 <= 4096 * fsp <= 2 ^ 47 - 11571200 /\
  6537216 <= ctx <= 2 ^ 47 - 160 /\ 4096 <= thr <= 2 ^ 47 - 80 /\ 4096 <= blk <= 2 ^ 47 - 32 /\
  1 <= beg <= 2 ^ 64 - 1 /\ 1 <= fbv <= 255 /\
  (ctx + 160 <= 4096 * fsp \/ 4096 * fsp + 11571200 <= ctx) /\
  (thr + 80 <= 4096 * fsp \/ 4096 * fsp + 11571200 <= thr) /\
  (blk + 32 <= 4096 * fsp \/ 4096 * fsp + 11571200 <= blk) /\
  17594333495296 <= sp - 208 /\ sp <= 2 ^ 47 /\ sp mod 16 = 0 /\
  208 <= sp - swb <= 2 ^ 30 /\ 0 <= swb + sws - sp <= 2 ^ 30 /\
  0 <= sp - 208 - 4096 * fsp - 11571200 <= 2 ^ 47 /\
  app2r (4096 * fsp) (4096 * fsp + 11571200) /\ rt_app ctx 160 /\ rt_app thr 80 /\ rt_app blk 32.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts.
  pose proof (Bnd 4%positive) as B4. pose proof (Bnd 10%positive) as B10. pose proof (Bnd 13%positive) as B11.
  pose proof (Bnd 14%positive) as B12. pose proof (Bnd 15%positive) as B15. pose proof (Bnd 16%positive) as B16.
  pose proof (Bnd 17%positive) as B17. pose proof (Bnd 23%positive) as B23. pose proof (Bnd 24%positive) as B24.
  assert (X : 6537216 <= 4096 * fsp <= 2 ^ 47 - 11571200)
    by (clear -F2; change (6537216 / 4096) with 1596 in F2; change ((2 ^ 47 - 11571200) / 4096) with 34359735543 in F2; lia).
  change (2 ^ 1) with 2 in F. change (2 ^ 9) with 512 in F1. change (2 ^ 4) with 16 in F19.
  refine (conj F (conj F0 (conj _ (conj X (conj F4 (conj F6 (conj F8 (conj F10 (conj F11 (conj _ (conj _ (conj _ (conj _ (conj _ (conj F19 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))))))))).
  - clear -F1 B11 B12 F0. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F15 B10 B15 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F16 B10 B16 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F17 B10 B17 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F18 B4. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F18 B4. unfold two64 in *. Z.div_mod_to_equations. lia.
  - destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & HG & _). cbn [s_rgs SM5_P0] in HG. rewrite RGS0_eq in HG. unfold RGS0 in HG. cbn [app] in HG.
    apply Forall_cons_iff in HG as [G0 _]. destruct (rg_flat BSEGS E _ _ G0) as (Z1 & Z2). unfold rsz in Z1, Z2. cbn [rg_base rg_size] in Z1, Z2.
    unfold SWB, SWS in Z1, Z2. repeat rewrite lden_lvar in Z1. repeat rewrite lden_lvar in Z2.
    clear -F18 F20 F21 B4 B23 B24 Z1 Z2. unfold two64 in *. Z.div_mod_to_equations. lia.
  - destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & HG & _). cbn [s_rgs SM5_P0] in HG. rewrite RGS0_eq in HG. unfold RGS0 in HG. cbn [app] in HG.
    apply Forall_cons_iff in HG as [G0 _]. destruct (rg_flat BSEGS E _ _ G0) as (Z1 & Z2). unfold rsz in Z1, Z2. cbn [rg_base rg_size] in Z1, Z2.
    unfold SWB, SWS in Z1, Z2. repeat rewrite lden_lvar in Z1. repeat rewrite lden_lvar in Z2.
    clear -F18 F20 F21 B4 B23 B24 Z1 Z2. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F22 B4 B10 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - apply (proj2 (rt_app_of_wrapped (4096 * fsp) 11571200 ltac:(lia) ltac:(lia) ltac:(lia)
                     ltac:(replace (-17594333495296 + (1 * (4096 * fsp) + 0)) with (-17594333495296 + (4096 * fsp + 0)) by ring; exact F3))).
  - exact (proj1 (rt_app_of_wrapped ctx 160 ltac:(lia) ltac:(lia) ltac:(lia) F5)).
  - exact ((rt_app_of_wrapped4k thr 80 ltac:(lia) ltac:(lia) ltac:(lia) F7)).
  - exact ((rt_app_of_wrapped4k blk 32 ltac:(lia) ltac:(lia) ltac:(lia) F9)).
Qed.

Definition v0 : rt_vals := RTV (4096 * fsp) ctx thr tlsb tlse blk beg.

Ltac rget_norm_in H := repeat match type of H with context [rget ?T ?k] =>
  let v := eval vm_compute in (rget T k) in change (rget T k) with v in H end.

(* [comment removed for export] *)
Ltac open_sm4 :=
  destruct (sden_0 _ _ _ _ Hd) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm);
  cbn [s_pc s_regs s_rgs s_facts s_resv SM5_P0] in Hpc, Hresv, HR, HG, HD, HF; rewrite RGS0_eq in HG, HD;
  pose proof sm5_facts as FCT;
  pose proof (Bnd 5%positive) as Bra; pose proof (Bnd 4%positive) as Bsp; pose proof (Bnd 10%positive) as Bfsp;
  pose proof (Bnd 13%positive) as Bh4; pose proof (Bnd 14%positive) as Bp4; pose proof (Bnd 15%positive) as Bctx;
  pose proof (Bnd 16%positive) as Bthr; pose proof (Bnd 17%positive) as Bblk; pose proof (Bnd 18%positive) as Bbeg;
  pose proof (Bnd 23%positive) as Bswb; pose proof (Bnd 24%positive) as Bsws;
  unfold RGS0, rt_rgs_t, relro_rgs in HG; cbn [app] in HG;
  apply Forall_cons_iff in HG as [G0 HG]; apply Forall_cons_iff in HG as [G1 HG]; apply Forall_cons_iff in HG as [G2 HG];
  apply Forall_cons_iff in HG as [G3 HG]; apply Forall_cons_iff in HG as [G4 HG]; apply Forall_cons_iff in HG as [G5 HG];
  apply Forall_cons_iff in HG as [G6 HG]; apply Forall_cons_iff in HG as [G7 HG]; apply Forall_cons_iff in HG as [G8 HG];
  apply Forall_cons_iff in HG as [G9 HG]; apply Forall_cons_iff in HG as [G10 HG]; apply Forall_cons_iff in HG as [G11 HG];
  apply Forall_cons_iff in HG as [G12 HG]; apply Forall_cons_iff in HG as [G13 HG]; apply Forall_cons_iff in HG as [G14 HG];
  apply Forall_cons_iff in HG as [G15 HG]; apply Forall_cons_iff in HG as [G16 HG]; apply Forall_cons_iff in HG as [G17 HG];
  apply Forall_cons_iff in HG as [G18 HG]; apply Forall_cons_iff in HG as [G19 HG]; apply Forall_cons_iff in HG as [G20 HG];
  apply Forall_cons_iff in HG as [G21 HG].

(* [comment removed for export] *)
Ltac ubase := lnorm; rewrite u_Z_to_bv; unfold vz; rewrite ?Z.add_0_l, ?Z.add_0_r, ?Z.mul_1_l.

#[using="ms Hd"] Lemma sm5_pos : h4 mod 512 = p4.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  pose proof sm5_facts as (_ & _ & Hm & _). exact Hm.
Qed.

#[using="ms Hd"] Lemma sm5_win : 208 <= sp - swb <= 2 ^ 30 /\ 0 <= swb + sws - sp <= 2 ^ 30.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  pose proof sm5_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W1 & W2 & _). exact (conj W1 W2).
Qed.

#[using="E Hd"] Lemma sm5_tp : getr (ms_regs ms) 4 = Z_to_bv 64 6395968.
Proof. LiaFast.lf_pins (fun (E Hd : LiaFast.U) => LiaFast.u0). open_sm4. pose proof (HR 4%bv) as X. rget_norm_in X. rewrite X. reflexivity. Qed.
#[using="Hd"] Lemma sm5_sp : getr (ms_regs ms) 2 = E 4%positive.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0). open_sm4. pose proof (HR 2%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar. Qed.
#[using="Hd"] Lemma sm5_ra : getr (ms_regs ms) 1 = E 5%positive.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0). open_sm4. pose proof (HR 1%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar. Qed.

#[using="Hd"] Lemma sm5_hint : rw_cells BSEGS (ms_mem ms) (4096 * fsp + 40) [C8 (Z_to_bv 64 h4)].
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_sm4. pose proof (track_bytes_at BSEGS E (ms_mem ms) _ 0 _ G1 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X.
  unfold bv8 in X. rewrite map_bden_bv8 in X. cbn [rg_base RGz] in X.
  assert (B : bv_unsigned (lden E (fsc 40)) = 4096 * fsp + 40).
  { ubase. rewrite Z.mod_small; [ring|]. destruct FCT as (_ & _ & _ & Hf & _). clear -Hf. unfold KHI, KTOP, two64 in *. lia. }
  rewrite B, Z.add_0_r in X. lnorm_in X. split; [split; [exact (conj I I)|]|].
  - rewrite Z_to_bv_bv_unsigned. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact X.
  - cbn [cells_size csize]. change (Z.of_nat (8 + 0)) with 8.
    exact (wr_at_of_rg BSEGS E _ _ _ _ G1 ltac:(left; reflexivity) ltac:(cbn [track rg_base RGz]; exact B) eq_refl).
Qed.

(* [comment removed for export] *)
Ltac const_cells G o :=
  let X := fresh "X" in
  pose proof (track_bytes_at BSEGS E (ms_mem ms) _ o _ G ltac:(clear; lia) ltac:(cbn; clear; lia)) as X;
  cbn [rg_base RGz track] in X; change (bv_unsigned (lden E (lconst ?z))) with (z mod two64) in X;
  rewrite Z.mod_small in X by (unfold two64; clear; lia);
  apply (ro_cells_of_bytes BSEGS _ _ _ _ X); [vm_compute; reflexivity | cbn; tauto].

#[using="Hd"] Lemma sm5_fs : fs_cells_ok (4096 * fsp) (ms_mem ms).
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_sm4. unfold fs_cells_ok, fs_hdr_c in *.
  pose proof (track_bytes_at BSEGS E (ms_mem ms) _ 0 _ G7 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X.
  cbn [rg_base RGz] in X.
  assert (B : bv_unsigned (lden E (fsc 88)) = 4096 * fsp + 88).
  { ubase. rewrite Z.mod_small; [ring|]. destruct FCT as (_ & _ & _ & Hf & _). clear -Hf. unfold KHI, KTOP, two64 in *. lia. }
  rewrite B, Z.add_0_r in X. apply (ro_cells_of_bytes BSEGS _ _ _ _ X); [vm_compute; reflexivity | cbn; tauto].
Qed.

#[using="Hd"] Lemma sm5_RT : RT (ms_mem ms) v0.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_sm4. unfold RT. cbn [rt_FS rt_ctx rt_thr rt_tlsb rt_tlse rt_blk rt_beg v0].
  destruct FCT as (_ & _ & _ & Hf & Hc & Ht & Hb & Hg & Hfb & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fapp & Capp & Tapp & Bapp). unfold KHI, KTOP in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))).
  - unfold sb_uar_t in G8. const_cells G8 0.
  - (* [comment removed for export] *)
    pose proof (cont_bytes_at BSEGS E (ms_mem ms) _ 0 [BK 1] G9 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(vm_compute; reflexivity)) as Y.
    cbn [rg_base] in Y. change (bv_unsigned (lden E (lconst 941792))) with 941792 in Y.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ Y); [vm_compute; reflexivity | cbn; tauto].
  - pose proof (cont_bytes_at BSEGS E (ms_mem ms) _ 4 (bkn 4 0) G9 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(vm_compute; reflexivity)) as Y.
    cbn [rg_base] in Y. change (bv_unsigned (lden E (lconst 941792))) with 941792 in Y.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ Y); [vm_compute; reflexivity | cbn; tauto].
  - const_cells G10 0.
  - const_cells G11 0.
  - exists (Z_to_bv 8 fbv). split.
    + pose proof (track_bytes_at BSEGS E (ms_mem ms) _ 0 _ G13 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 1540657))) with 1540657 in X. rewrite Z.add_0_r in X.
      split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. cbn [List.map bden] in X. lnorm_in X. rewrite Z.shiftr_0_r in X. exact X.
    + rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by (clear -Hfb; lia). clear -Hfb; lia.
  - const_cells G12 0.
  - const_cells G14 0.
  - (* [comment removed for export] *)
    split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
    + pose proof (cont_bytes_at BSEGS E (ms_mem ms) _ 0 (bk8 6396000) G15 ltac:(clear; lia) ltac:(cbn; clear; lia)
                    ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X. rewrite Z.add_0_r in X.
      apply (bytes_at_ext BSEGS _ _ _ _ X). apply bytes_eqb_eq. vm_compute. reflexivity.
    + pose proof (cont_le8 BSEGS E (ms_mem ms) _ 8 FS G15 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
      lnorm_in X. rewrite Z.add_0_l, Z.add_0_r in X. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E (ms_mem ms) _ 16 BLK G15 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
    lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - pose proof (cont_bytes_at BSEGS E (ms_mem ms) _ 48 (bk8 6398016) G15 ltac:(clear; lia) ltac:(cbn; clear; lia)
                  ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ X); [vm_compute; reflexivity | cbn; tauto].
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E (ms_mem ms) _ 0 CTX G16 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6532072))) with 6532072 in X.
    lnorm_in X. rewrite ?Z.add_0_r in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E (ms_mem ms) _ 0 THR G17 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. rewrite (u_ctx152 E ltac:(clear -Hc; lia)), Z.add_0_r in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
    + pose proof (cont_le8 BSEGS E (ms_mem ms) _ 0 TLSB G18 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. rewrite (u_thr48 E ltac:(clear -Ht; lia)), Z.add_0_r in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
    + pose proof (cont_le8 BSEGS E (ms_mem ms) _ 8 TLSE G18 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. rewrite (u_thr48 E ltac:(clear -Ht; lia)) in X. lnorm_in X. rewrite !Z_to_bv_bv_unsigned, length_le8.
      replace (thr + 48 + Z.of_nat 8) with (thr + 48 + 8) by lia. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E (ms_mem ms) _ 0 BEG G19 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. rewrite (u_blk24 E ltac:(clear -Hb; lia)), Z.add_0_r in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj Fapp (conj _ (conj _ (conj Capp (conj _ (conj Tapp (conj _ (conj Bapp _))))))))))))).
    all: clear -Hf Hc Ht Hb Hg; unfold two64 in *; lia.
Qed.

#[using="Hd"] Lemma sm5_fl : u8arr BSEGS (ms_mem ms) (4096 * fsp + 35840) (repeat (Z_to_bv 8 0) 512).
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_sm4. destruct FCT as (_ & Hp & _ & Hf & _). unfold KHI, KTOP in Hf.
  assert (B2 : bv_unsigned (lden E (fsc FL5)) = 4096 * fsp + 35840) by (ubase; rewrite Z.mod_small; [ring|clear -Hf; unfold two64; lia]).
  assert (Z2 : rsz E (RG (fsc FL5) P5 RZ TEmpty) = p4) by (unfold rsz; cbn [rg_size]; lnorm; reflexivity).
  assert (B3 : bv_unsigned (lden E (ladd (fsc FL5) P5)) = 4096 * fsp + 35840 + p4)
    by (ubase; rewrite Z.mod_small; [ring|clear -Hf Hp; unfold two64; lia]).
  assert (Z3 : rsz E (RG (ladd (fsc FL5) P5) (lconst 1) RZ TEmpty) = 1) by reflexivity.
  assert (B4 : bv_unsigned (lden E (ladd (fsc (FL5 + 1)) P5)) = 4096 * fsp + 35841 + p4)
    by (ubase; rewrite Z.mod_small; [ring|clear -Hf Hp; unfold two64; lia]).
  assert (Z4 : rsz E (RG (ladd (fsc (FL5 + 1)) P5) (laddc (lscale (-1) P5) 511) RZ TEmpty) = 511 - p4)
    by (unfold rsz; cbn [rg_size]; ubase; clear -Hp Bp4; unfold two64 in *; lia).
  assert (HB : forall i, 0 <= i < 512 ->
             mrd BSEGS (ms_mem ms) (wa (4096 * fsp + 35840 + i)) = Some (Z_to_bv 8 0) /\
             wview BSEGS (ms_mem ms) (wa (4096 * fsp + 35840 + i)) <> None).
  { intros i Hi. destruct (Z.ltb_spec i p4) as [H1|H1]; [|destruct (Z.eqb_spec i p4) as [H2|H2]].
    - pose proof (rz_bytes BSEGS E _ _ i G2 eq_refl eq_refl ltac:(rewrite Z2; clear -Hi H1; lia)) as X.
      cbn [rg_base] in X. rewrite B2 in X. exact X.
    - subst i. pose proof (rz_bytes BSEGS E _ _ 0 G3 eq_refl eq_refl ltac:(rewrite Z3; clear; lia)) as X.
      cbn [rg_base] in X. rewrite B3, Z.add_0_r in X. exact X.
    - pose proof (rz_bytes BSEGS E _ _ (i - p4 - 1) G4 eq_refl eq_refl ltac:(rewrite Z4; clear -Hi H1 H2; lia)) as X.
      cbn [rg_base] in X. rewrite B4 in X. replace (4096 * fsp + 35841 + p4 + (i - p4 - 1)) with (4096 * fsp + 35840 + i) in X by ring.
      exact X. }
  split.
  - split; [clear -Hf; lia|]. split; [rewrite repeat_length; clear -Hf; unfold two64; lia|].
    intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi. exact (proj1 (HB (Z.of_nat i) ltac:(clear -Hi; lia))).
  - split; [clear -Hf; lia|]. split; [rewrite repeat_length; clear -Hf; unfold two64; lia|].
    intros i Hi. rewrite repeat_length in Hi. exact (proj2 (HB i ltac:(clear -Hi; lia))).
Qed.

#[using="Hd"] Lemma sm5_slot : stk BSEGS (ms_mem ms) (4096 * fsp + 5279744 + p4 * 2048) (4096 * fsp + 5279744 + p4 * 2048 + 2048).
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_sm4. destruct FCT as (_ & Hp & _ & Hf & _). unfold KHI, KTOP in Hf.
  apply (stk_of_rg BSEGS E _ _ _ _ G5 ltac:(left; reflexivity)); cbn [rg_base].
  - ubase. rewrite Z.mod_small; [ring|clear -Hf Hp; unfold two64; lia].
  - unfold rsz. cbn [rg_size]. change (bv_unsigned (lden E (lconst 2048))) with 2048. ring.
Qed.

#[using="Hd"] Lemma sm5_slsh : stk BSEGS (ms_mem ms) (2147450880 + (4096 * fsp + 5279744 + p4 * 2048) / 8)
                   (2147450880 + (4096 * fsp + 5279744 + p4 * 2048) / 8 + 2048 / 8).
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_sm4. destruct FCT as (_ & Hp & _ & Hf & _). unfold KHI, KTOP in Hf.
  replace (4096 * fsp + 5279744 + p4 * 2048) with ((512 * fsp + 659968 + p4 * 256) * 8) by ring.
  rewrite Z.div_mul by discriminate.
  apply (stk_of_rg BSEGS E _ _ _ _ G6 ltac:(left; reflexivity)); cbn [rg_base].
  - ubase. rewrite Z.mod_small; [ring|clear -Hf Hp; unfold two64; lia].
  - unfold rsz. cbn [rg_size]. change (bv_unsigned (lden E (lconst 256))) with 256. change (2048 / 8) with 256. ring.
Qed.

#[using="Hd"] Lemma sm5_stk : stk BSEGS (ms_mem ms) (sp - 208) sp.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_sm4. pose proof sm5_win as (W1 & W2).
  assert (S0 : stk BSEGS (ms_mem ms) swb (swb + sws)).
  { apply (stk_of_rg BSEGS E _ _ _ _ G0 ltac:(left; reflexivity)); cbn [rg_base]; [lnorm; reflexivity|].
    unfold rsz. cbn [rg_size]. lnorm. ring. }
  destruct (stk_split BSEGS _ _ (sp - 208) _ S0 ltac:(clear -W1 W2; lia)) as (_ & S1).
  destruct (stk_split BSEGS _ _ sp _ S1 ltac:(clear -W1 W2; lia)) as (S2 & _). exact S2.
Qed.

#[using="E Hd"] Lemma sm5_pr1 : pristine (ms_mem ms) 892928 917504.
Proof. LiaFast.lf_pins (fun (E Hd : LiaFast.U) => LiaFast.u0).
  open_sm4. exact (pristine_of_rg_ro BSEGS E _ _ 892928 24576 G20 eq_refl eq_refl eq_refl).
Qed.
#[using="E Hd"] Lemma sm5_pr2 : pristine (ms_mem ms) 918096 918488.
Proof. LiaFast.lf_pins (fun (E Hd : LiaFast.U) => LiaFast.u0).
  open_sm4. exact (pristine_of_rg_ro BSEGS E _ _ 918096 392 G21 eq_refl eq_refl eq_refl).
Qed.

#[using="ms Hd"] Lemma sm5_rtd1 : rt_disj v0 (sp - 208) sp.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & HF & _). cbn [s_facts SM5_P0] in HF.
  assert (HO : Forall (fact_ok E) (rt_out 208)).
  { rewrite Forall_forall in HF |- *. intros f Hf. apply HF. unfold SM5_F. apply in_cons. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hf. }
  destruct (rt_out_ok E 208 ltac:(lia) HO) as (O1 & O2 & O3).
  unfold rt_disj. cbn [rt_ctx rt_thr rt_blk v0]. clear -O1 O2 O3. repeat split; lia.
Qed.

#[using="ms Hd"] Lemma sm5_rtd2 : rt_disj v0 (4096 * fsp) (4096 * fsp + 11571200).
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  pose proof sm5_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & C1 & C2 & C3 & _).
  unfold rt_disj. cbn [rt_ctx rt_thr rt_blk v0]. clear -C1 C2 C3. repeat split; lia.
Qed.

Ltac rget_norm := repeat match goal with |- context [rget ?T ?k] =>
  let v := eval vm_compute in (rget T k) in change (rget T k) with v end.

Ltac getr_mkR_norm := rewrite getr_mkR;
  match goal with |- context [Z.to_nat (bv_unsigned ?r)] =>
    let v := eval vm_compute in (Z.to_nat (bv_unsigned r)) in change (Z.to_nat (bv_unsigned r)) with v end; cbn beta iota.

Definition Eq (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : valu :=
  upds E [(205%positive, t0); (206%positive, t1); (207%positive, t2); (211%positive, a1); (212%positive, a2); (213%positive, a3);
          (214%positive, a4); (215%positive, a5); (216%positive, a6); (217%positive, a7); (228%positive, t3); (229%positive, t4);
          (230%positive, t5); (231%positive, t6)].

#[using="Type"] Lemma Eq_agree : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6, agree 200 E (Eq t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Proof. LiaFast.lf_pins LiaFast.u0. intros. apply upds_agree. repeat constructor; cbn [fst]; lia. Qed.

(* [comment removed for export] *)
#[using="ms Hd"] Lemma sm5_vals :
  bv_unsigned (lden E (fsc 40)) = 4096 * fsp + 40 /\
  bv_unsigned (lden E (ladd (fsc FL5) P5)) = 4096 * fsp + 35840 + p4 /\
  bv_unsigned (lden E (ladd (fsc AR5) (lscale 2048 P5))) = 4096 * fsp + 5279744 + p4 * 2048 /\
  bv_unsigned (lden E (ladd (fsh AR5) (lscale 256 P5))) = 2147450880 + (4096 * fsp + 5279744 + p4 * 2048) / 8.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  pose proof sm5_facts as (_ & Hp & _ & Hf & _). unfold KHI, KTOP in Hf. pose proof (Bnd 10%positive). pose proof (Bnd 14%positive).
  replace (4096 * fsp + 5279744 + p4 * 2048) with ((512 * fsp + 659968 + p4 * 256) * 8) by ring. rewrite Z.div_mul by discriminate.
  split; [|split; [|split]]; ubase; rewrite Z.mod_small; try ring; clear -Hf Hp; unfold two64 in *; lia.
Qed.

#[using="ms Hd"] Lemma sm5_HW : forall x,
  (forall j Rj, In j [0%nat; 1%nat; 3%nat; 5%nat; 6%nat] -> nth_error RGS0 j = Some Rj ->
     ~ (bv_unsigned (lden E (rg_base Rj)) <= x < bv_unsigned (lden E (rg_base Rj)) + rsz E Rj)) ->
  Frame.outside [(sp - 208, sp); (4096 * fsp + 40, 4096 * fsp + 40 + 8); (4096 * fsp + 35840 + p4, 4096 * fsp + 35840 + p4 + 1);
                 (4096 * fsp + 5279744 + p4 * 2048, 4096 * fsp + 5279744 + p4 * 2048 + 2048);
                 (2147450880 + (4096 * fsp + 5279744 + p4 * 2048) / 8, 2147450880 + (4096 * fsp + 5279744 + p4 * 2048) / 8 + 2048 / 8)] x.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  intros x H. pose proof sm5_win as (W1 & W2). pose proof sm5_vals as (V1 & V3 & V5 & V6).
  pose proof (H 0%nat _ ltac:(cbn; tauto) eq_refl) as N0. pose proof (H 1%nat _ ltac:(cbn; tauto) eq_refl) as N1.
  pose proof (H 3%nat _ ltac:(cbn; tauto) eq_refl) as N3. pose proof (H 5%nat _ ltac:(cbn; tauto) eq_refl) as N5.
  pose proof (H 6%nat _ ltac:(cbn; tauto) eq_refl) as N6. clear H.
  unfold rsz in N0, N1, N3, N5, N6. cbn [rg_base rg_size track RGz] in N0, N1, N3, N5, N6.
  rewrite V1 in N1. rewrite V3 in N3. rewrite V5 in N5. rewrite V6 in N6.
  lnorm_in N0. change (bv_unsigned (lden E (lconst 8))) with 8 in N1. change (bv_unsigned (lden E (lconst 1))) with 1 in N3.
  change (bv_unsigned (lden E (lconst 2048))) with 2048 in N5. change (bv_unsigned (lden E (lconst 256))) with 256 in N6.
  cbn [Frame.outside]. clear -N0 N1 N3 N5 N6 W1 W2. repeat split; lia.
Qed.

#[using="Hd"] Lemma sm5_run : exists ms' E', isteps BSEGS ms ms' /\
  sden BSEGS E' (with_pc SM5_Q (bv_unsigned (lden E (rget (s_regs SM5_P0) ra_key)))) ms' /\
  agree (s_next SM5_P0) E E' /\ (forall x, fr_pt E (s_rgs SM5_P0) x -> ms_mem ms' x = ms_mem ms x) /\ fpeq ms ms'.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  destruct (sden_0 _ _ _ _ Hd) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm).
  cbn [s_pc s_regs s_rgs s_facts s_resv SM5_P0] in Hpc, Hresv, HR, HG, HD, HF. rewrite RGS0_eq in HG, HD. unfold rsv_ok in Hresv.
  pose proof sm5_facts as FCT. pose proof sm5_win as (W1 & W2). pose proof (Bnd 4%positive) as Bsp.
  pose proof (Bnd 10%positive) as Bfsp. pose proof (Bnd 13%positive) as Bh4. pose proof (Bnd 14%positive) as Bp4.
  destruct FCT as (Fra & Fp4 & _ & Ffsp & _ & _ & _ & _ & _ & _ & _ & _ & Fsp & FspK & Fsp16 & _ & _ & C18 & _). unfold KHI, KTOP in Ffsp.
  pose proof (smalloc5_spec tls_chain_spec m2s_spec) as SM. unfold smalloc5_stmt, smalloc_stmt in SM.
  specialize (SM (getr (ms_regs ms) 1) (getr (ms_regs ms) 2) (getr (ms_regs ms) 3) (getr (ms_regs ms) 4) (getr (ms_regs ms) 5)
                 (getr (ms_regs ms) 6) (getr (ms_regs ms) 7) (getr (ms_regs ms) 8) (getr (ms_regs ms) 9) (getr (ms_regs ms) 10)
                 (getr (ms_regs ms) 11) (getr (ms_regs ms) 12) (getr (ms_regs ms) 13) (getr (ms_regs ms) 14) (getr (ms_regs ms) 15)
                 (getr (ms_regs ms) 16) (getr (ms_regs ms) 17) (getr (ms_regs ms) 18) (getr (ms_regs ms) 19) (getr (ms_regs ms) 20)
                 (getr (ms_regs ms) 21) (getr (ms_regs ms) 22) (getr (ms_regs ms) 23) (getr (ms_regs ms) 24) (getr (ms_regs ms) 25)
                 (getr (ms_regs ms) 26) (getr (ms_regs ms) 27) (getr (ms_regs ms) 28) (getr (ms_regs ms) 29) (getr (ms_regs ms) 30)
                 (getr (ms_regs ms) 31) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) v0 h4 (repeat (Z_to_bv 8 0) 512)).
  cbv zeta in SM. rewrite !fk_nframes_5, !fk_size_5, !fk_hint_5, !fk_flags_5, !fk_frame_5 in SM. cbn [rt_FS v0] in SM.
  rewrite sm5_pos in SM.
  assert (Husp : bv_unsigned (getr (ms_regs ms) 2) = sp) by (rewrite sm5_sp; reflexivity).
  assert (Hura : bv_unsigned (getr (ms_regs ms) 1) = ra) by (rewrite sm5_ra; reflexivity).
  rewrite Husp, Hura in SM.
  assert (HK : evt BSEGS (smalloc_post 5 (getr (ms_regs ms) 1) (getr (ms_regs ms) 2) (getr (ms_regs ms) 3) (getr (ms_regs ms) 4)
                 (getr (ms_regs ms) 8) (getr (ms_regs ms) 9) (getr (ms_regs ms) 18) (getr (ms_regs ms) 19) (getr (ms_regs ms) 20)
                 (getr (ms_regs ms) 21) (getr (ms_regs ms) 22) (getr (ms_regs ms) 23) (getr (ms_regs ms) 24) (getr (ms_regs ms) 25)
                 (getr (ms_regs ms) 26) (getr (ms_regs ms) 27) (ms_fregs ms) (ms_fcsr ms) (4096 * fsp) h4 (repeat (Z_to_bv 8 0) 512)
                 (ms_mem ms)) (kms BSEGS ms)).
  { unfold kms. rewrite Hpc, Hresv. apply SM.
    - exact sm5_tp.
    - exact sm5_RT.
    - exact sm5_fs.
    - exact sm5_hint.
    - exact Bh4.
    - exact sm5_fl.
    - rewrite repeat_length. reflexivity.
    - rewrite nth_error_repeat by (clear -Fp4; lia). reflexivity.
    - exact sm5_slot.
    - exact sm5_slsh.
    - exact sm5_stk.
    - clear -Fsp. lia.
    - exact Fsp.
    - exact FspK.
    - exact Fsp16.
    - clear -C18. lia.
    - exact sm5_pr1.
    - exact sm5_pr2.
    - exact sm5_rtd1.
    - exact sm5_rtd2.
    - exact Fra. }
  clear SM.
  destruct (kit_run BSEGS _ ms Hsvc HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  unfold smalloc_post in Hpost. cbv zeta in Hpost.
  rewrite !fk_nframes_5, !fk_size_5, !fk_hint_5, !fk_flags_5, !fk_frame_5, sm5_pos in Hpost.
  destruct Hpost as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & junk1 & junk2 & m' & Hms2 & MU & WM & ST' & HI' & FL' & SL' & SH').
  subst ms2. unfold smalloc_W in MU. rewrite !fk_nframes_5, !fk_size_5, !fk_hint_5, !fk_flags_5, !fk_frame_5, sm5_pos in MU.
  rewrite Husp in MU, ST'.
  assert (Hmem : ms_mem ms1 = m') by (destruct Heq as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  exists ms1, (Eq t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  split; [exact Hst|]. split; [|split; [|split]].
  - eapply (sden_of_kit BSEGS _ _ ms1); [ | | exact Heq | | exact Hfrm | | | | ].
    + rewrite state_wf_with_pc. exact (proj1 (proj2 SM5_wf)).
    + reflexivity.
    + cbn [s_pc with_pc s_regs SM5_P0]. rget_norm. lnorm. rewrite Z_to_bv_bv_unsigned. rewrite sm5_ra. apply ret_pc_even_w.
      exact (proj1 sm5_facts).
    + (* [comment removed for export] *)
      apply regs_ok_of_cases. intros n Hn. cbn [s_regs with_pc SM5_Q].
      do 32 (destruct n as [|n];
               [ getr_mkR_norm; rget_norm;
                 first [ reflexivity
                       | (rewrite (HR _); rget_norm; lnorm; reflexivity)
                       | (lnorm; reflexivity)
                       | (lnorm; f_equal; unfold vz; change (Eq t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 10%positive) with (E 10%positive);
                          change (Eq t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 14%positive) with (E 14%positive); ring) ]
               |]).
      lia.
    + (* [comment removed for export] *)
      assert (Hwr : forallb (rwf 200) (s_rgs SM5_Q) = true) by (vm_compute; reflexivity).
      rewrite Forall_forall. intros R HRin. apply (rg_ok_agree BSEGS 200 E _ _ R); [rewrite forallb_forall in Hwr; exact (Hwr R HRin) | apply Eq_agree|].
      revert R HRin. rewrite <- Forall_forall. cbn [s_rgs with_pc SM5_Q]. rewrite RGS1_eq. unfold RGS1.
      pose proof HG as HG'. unfold RGS0, rt_rgs_t, relro_rgs in HG'. cbn [app] in HG'.
      assert (UW : forall i R, nth_error RGS0 i = Some R -> ~ In i [0%nat; 1%nat; 3%nat; 5%nat; 6%nat] -> rg_ok BSEGS E (ms_mem ms) R -> rg_ok BSEGS E m' R).
      { intros i R Hi Hni HR0. exact (rg_ok_unwritten BSEGS E (ms_mem ms) m' RGS0 _ _ i R HD Hi Hni MU sm5_HW HR0). }
      apply Forall_cons_iff in HG' as [G0 HG']. apply Forall_cons_iff in HG' as [G1 HG']. apply Forall_cons_iff in HG' as [G2 HG'].
      apply Forall_cons_iff in HG' as [G3 HG']. apply Forall_cons_iff in HG' as [G4 HG']. apply Forall_cons_iff in HG' as [G5 HG'].
      apply Forall_cons_iff in HG' as [G6 HG']. apply Forall_cons_iff in HG' as [G7 HG']. apply Forall_cons_iff in HG' as [G8 HG'].
      apply Forall_cons_iff in HG' as [G9 HG']. apply Forall_cons_iff in HG' as [G10 HG']. apply Forall_cons_iff in HG' as [G11 HG'].
      apply Forall_cons_iff in HG' as [G12 HG']. apply Forall_cons_iff in HG' as [G13 HG']. apply Forall_cons_iff in HG' as [G14 HG'].
      apply Forall_cons_iff in HG' as [G15 HG']. apply Forall_cons_iff in HG' as [G16 HG']. apply Forall_cons_iff in HG' as [G17 HG'].
      apply Forall_cons_iff in HG' as [G18 HG']. apply Forall_cons_iff in HG' as [G19 HG']. apply Forall_cons_iff in HG' as [G20 HG'].
      apply Forall_cons_iff in HG' as [G21 HG']. clear HG'.
      pose proof sm5_vals as (V1 & V3 & V5 & V6).
      unfold rt_rgs_t, relro_rgs. cbn [app].
      pose proof (rgs_disj_nth E _ 0 1 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D1.
      pose proof (rgs_disj_nth E _ 0 3 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D3.
      pose proof (rgs_disj_nth E _ 0 5 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D5.
      pose proof (rgs_disj_nth E _ 0 6 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D6.
      unfold rg_disj, rsz in D1, D3, D5, D6. cbn [rg_base rg_size track RGz] in D1, D3, D5, D6.
      rewrite V1 in D1. rewrite V3 in D3. rewrite V5 in D5. rewrite V6 in D6. lnorm_in D1. lnorm_in D3. lnorm_in D5. lnorm_in D6.
      change (bv_unsigned (Z_to_bv 64 (8 + 0))) with 8 in D1. change (bv_unsigned (Z_to_bv 64 (1 + 0))) with 1 in D3.
      change (bv_unsigned (Z_to_bv 64 (2048 + 0))) with 2048 in D5. change (bv_unsigned (Z_to_bv 64 (256 + 0))) with 256 in D6.
      constructor.
      { (* [comment removed for export] *)
        apply (rw_mix BSEGS E (ms_mem ms) m' _ _ (sp - 208) sp G0 eq_refl eq_refl MU ST').
        intros k Hk. unfold rsz in Hk. cbn [rg_base rg_size] in Hk |- *. lnorm_in Hk. lnorm.
        cbn [Frame.outside]. clear -Hk W1 W2 D1 D3 D5 D6. lia. }
      constructor.
      { (* [comment removed for export] *)
        destruct HI' as ((_ & HIb) & HIw). cbn [cells_bytes cbytes cells_size csize] in HIb, HIw. rewrite app_nil_r in HIb.
        change (Z.of_nat (8 + 0)) with 8 in HIw.
        apply track_of_bytes_at; [ | clear; lia | apply Z.leb_le; vm_compute; reflexivity | ].
        - apply (rg_ok_of_u8arr BSEGS E m' _ (4096 * fsp + 40) (le8 (Z_to_bv 64 ((h4 + 1) mod 2 ^ 64))));
            [reflexivity | reflexivity | exact V1 | reflexivity | split; [exact HIb | rewrite length_le8; exact HIw]].
        - cbn [rg_base RGz]. rewrite V1, Z.add_0_r. unfold bv8. rewrite map_bden_bv8.
          replace (lden E (laddc H5 1)) with (Z_to_bv 64 ((h4 + 1) mod 2 ^ 64)); [exact HIb|].
          lnorm. apply Z_to_bv_eqm. unfold eqm, two64, vz. rewrite Z.mod_mod by discriminate. f_equal. ring. }
      constructor; [exact (UW 2%nat _ eq_refl ltac:(cbn; intuition discriminate) G2)|].
      constructor.
      { (* [comment removed for export] *)
        destruct FL' as ((FLb1 & FLb2 & FLb) & (FLw1 & FLw2 & FLw)). rewrite upd_length, repeat_length in FLb2, FLb, FLw2, FLw.
        pose proof sm5_facts as (_ & Hp & _). pose proof (Bnd 14%positive) as Bp.
        apply (rg_ok_track1 BSEGS E m' _ (4096 * fsp + 35840 + p4) (BK 1)); [reflexivity | reflexivity | reflexivity | exact V3 | clear -FLb2 Hp; unfold two64; lia | |].
        - pose proof (FLb (Z.to_nat p4) ltac:(clear -Hp; lia)) as X. rewrite Z2Nat.id in X by (clear -Hp; lia).
          rewrite nth_error_upd_same in X by (rewrite repeat_length; clear -Hp; lia). exact X.
        - pose proof (FLw p4 ltac:(clear -Hp; lia)) as X. exact X. }
      constructor; [exact (UW 4%nat _ eq_refl ltac:(cbn; intuition discriminate) G4)|].
      constructor.
      { (* [comment removed for export] *)
        destruct SL' as ((SLwf & SLb) & SLw). cbn [cells_bytes cbytes cells_size csize] in SLb, SLw. rewrite app_nil_r in SLb.
        destruct SLwf as (J1 & _ & J2 & _ & _). cbn [cell_wf] in J1, J2.
        assert (B5 : bv_unsigned (lden E (rg_base (RG (ladd (fsc AR5) (lscale 2048 P5)) (lconst 2048) RW TEmpty))) =
                     4096 * fsp + 5279744 + p4 * 2048) by exact V5.
        apply track_of_bytes_at; [ | clear; lia | apply Z.leb_le; vm_compute; reflexivity | ].
        - apply track_of_bytes_at; [ | clear; lia | apply Z.leb_le; vm_compute; reflexivity | ].
          + eapply (rg_ok_of_u8arr BSEGS E m' _ (4096 * fsp + 5279744 + p4 * 2048)); [reflexivity | reflexivity | exact V5 | | split; [exact SLb|]].
            * rewrite !length_app, length_le8, J1, J2. reflexivity.
            * rewrite !length_app, length_le8, J1, J2. exact SLw.
          + cbn [rg_base]. rewrite V5. unfold bv8. rewrite map_bden_bv8.
            replace (lden E SP) with (E 4%positive) by (lnorm; reflexivity).
            apply bytes_at_app in SLb as (_ & SLb). rewrite J1 in SLb. apply bytes_at_app in SLb as (SLb & _).
            rewrite sm5_sp, Z_to_bv_bv_unsigned in SLb. exact SLb.
        - cbn [rg_base track]. rewrite V5. unfold bv8. rewrite map_bden_bv8.
          replace (lden E FLB5) with (Z_to_bv 64 (4096 * fsp + 35840 + p4)) by (lnorm; f_equal; unfold vz; ring).
          apply bytes_at_app in SLb as (_ & SLb). rewrite J1 in SLb. apply bytes_at_app in SLb as (_ & SLb).
          rewrite length_le8 in SLb. apply bytes_at_app in SLb as (_ & SLb). rewrite J2 in SLb. change (Z.to_nat (2048 - 40)) with 2008%nat in SLb.
          replace (4096 * fsp + 5279744 + p4 * 2048 + Z.of_nat 24 + Z.of_nat 8 + Z.of_nat 2008) with (4096 * fsp + 5279744 + p4 * 2048 + 2040)
            in SLb by (clear; lia). exact SLb. }
      constructor.
      { (* [comment removed for export] *)
        destruct SH' as ((SHwf & SHb) & SHw). cbn [cells_bytes cbytes cells_size csize] in SHb, SHw. rewrite app_nil_r in SHb.
        apply track_of_bytes_at; [ | clear; lia | apply Z.leb_le; vm_compute; reflexivity | ].
        - apply (rg_ok_of_u8arr BSEGS E m' _ (2147450880 + (4096 * fsp + 5279744 + p4 * 2048) / 8) (zeros 256));
            [reflexivity | reflexivity | exact V6 | reflexivity | split; [exact SHb | exact SHw]].
        - cbn [rg_base]. rewrite V6, Z.add_0_r. apply (bytes_at_ext BSEGS _ _ _ _ SHb). apply bytes_eqb_eq. vm_compute. reflexivity. }
      constructor; [exact (UW 7%nat _ eq_refl ltac:(cbn; intuition discriminate) G7)|].
      constructor; [exact (UW 8%nat _ eq_refl ltac:(cbn; intuition discriminate) G8)|].
      constructor; [exact (UW 9%nat _ eq_refl ltac:(cbn; intuition discriminate) G9)|].
      constructor; [exact (UW 10%nat _ eq_refl ltac:(cbn; intuition discriminate) G10)|].
      constructor; [exact (UW 11%nat _ eq_refl ltac:(cbn; intuition discriminate) G11)|].
      constructor; [exact (UW 12%nat _ eq_refl ltac:(cbn; intuition discriminate) G12)|].
      constructor; [exact (UW 13%nat _ eq_refl ltac:(cbn; intuition discriminate) G13)|].
      constructor; [exact (UW 14%nat _ eq_refl ltac:(cbn; intuition discriminate) G14)|].
      constructor; [exact (UW 15%nat _ eq_refl ltac:(cbn; intuition discriminate) G15)|].
      constructor; [exact (UW 16%nat _ eq_refl ltac:(cbn; intuition discriminate) G16)|].
      constructor; [exact (UW 17%nat _ eq_refl ltac:(cbn; intuition discriminate) G17)|].
      constructor; [exact (UW 18%nat _ eq_refl ltac:(cbn; intuition discriminate) G18)|].
      constructor; [exact (UW 19%nat _ eq_refl ltac:(cbn; intuition discriminate) G19)|].
      constructor; [exact (UW 20%nat _ eq_refl ltac:(cbn; intuition discriminate) G20)|].
      constructor; [exact (UW 21%nat _ eq_refl ltac:(cbn; intuition discriminate) G21)|].
      constructor.
    + (* [comment removed for export] *)
      apply (rgs_disj_agree 200 E); [vm_compute; reflexivity | apply Eq_agree|].
      apply (rgs_disj_shape E (s_rgs SM5_P0)); [apply shape_eqb_eq; exact (proj2 (proj2 SM5_wf)) | exact HD].
    + (* [comment removed for export] *)
      cbn [s_facts with_pc SM5_Q].
      assert (Hw : forallb (fwf 200) SM5_F = true) by (vm_compute; reflexivity).
      rewrite forallb_forall in Hw. rewrite Forall_forall in HF |- *. intros f Hf.
      exact (fact_ok_agree 200 E _ f (Hw f Hf) (Eq_agree _ _ _ _ _ _ _ _ _ _ _ _ _ _) (HF f Hf)).
  - apply upds_agree. repeat constructor; cbn [fst s_next SM5_P0]; lia.
  - (* [comment removed for export] *)
    intros x Hx. rewrite Hmem. apply MU.
    destruct Hx as [Hout|Hrt].
    + unfold FxStep.outside in Hout. cbn [s_rgs SM5_P0] in Hout. rewrite RGS0_eq in Hout. unfold RGS0, rt_rgs_t, relro_rgs in Hout. cbn [app] in Hout.
      apply Forall_cons_iff in Hout as [O0 Hout]. apply Forall_cons_iff in Hout as [O1 Hout].
      apply Forall_cons_iff in Hout as [O2 Hout]. apply Forall_cons_iff in Hout as [O3 Hout].
      apply Forall_cons_iff in Hout as [O4 Hout]. apply Forall_cons_iff in Hout as [O5 Hout].
      apply Forall_cons_iff in Hout as [O6 Hout]. clear Hout.
      unfold rsz in O0, O1, O3, O5, O6. cbn [rg_base rg_size track RGz] in O0, O1, O3, O5, O6.
      lnorm_in O0. lnorm_in O1. lnorm_in O3. lnorm_in O5. lnorm_in O6.
      rewrite !u_Z_to_bv in O1, O3, O5, O6. unfold vz in *.
      rewrite !Z.mod_small in O1, O3, O5, O6 by (clear -Ffsp Fp4 Bfsp Bp4; unfold two64 in *; lia).
      pose proof (bv_unsigned_in_range _ x) as Bx. unfold bv_modulus in Bx. change (2 ^ Z.of_N 64) with two64 in Bx.
      cbn [Frame.outside]. clear -O0 O1 O3 O5 O6 W1 W2 Bx. unfold two64 in *. repeat split; lia.
    + apply sm5_HW. cbn [s_rgs SM5_P0] in Hrt. rewrite RGS0_eq in Hrt.
      exact (rt_frame E RGS0 [0%nat; 1%nat; 3%nat; 5%nat; 6%nat] x HD ltac:(vm_compute; reflexivity) Hrt).
  - destruct Heq as (_ & HFr & _ & _ & _ & HFc & _). cbn [ms_fregs ms_fcsr with_rom MS] in HFr, HFc. split; [exact HFr | exact HFc].
Qed.

End SM5.

Theorem sm5_kfn_fp : kfn_ok_fp BSEGS SM5_P0 SM5_Q.
Proof. intros E ms Hd. exact (sm5_run E ms Hd). Qed.
Theorem sm5_kfn : kfn_ok BSEGS SM5_P0 SM5_Q.
Proof. exact (kfn_okP_ok BSEGS fpeq _ _ sm5_kfn_fp). Qed.
