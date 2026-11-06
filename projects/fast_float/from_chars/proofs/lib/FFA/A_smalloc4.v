(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Perf.   (* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt A_rt_lemmas A_rt_tls A_rt_m2s.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
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
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation ASEGS := Asan.M.loaded_segments.
Tactic Notation "show" string(tag) := match goal with |- ?g => idtac tag g end.

(* [comment removed for export] *)
Notation K := 4%Z.
Notation ENTRY := 0x4ad74%Z.
Notation NFR := 1024%Z.        (* [comment removed for export] *)
Notation SZ := 1024%Z.          (* [comment removed for export] *)
Notation SHN := 128%Z.          (* [comment removed for export] *)
Notation FLOFF := 34816%Z.     (* [comment removed for export] *)
Notation FROFF := 4231168%Z.   (* [comment removed for export] *)
Notation HOFF := 32%Z.         (* [comment removed for export] *)

Lemma fk_nframes_4 : fk_nframes K = NFR. Proof. reflexivity. Qed.
Lemma fk_size_4 : fk_size K = SZ. Proof. reflexivity. Qed.
Lemma fk_hint_4 : forall FS, fk_hint FS K = (FS + HOFF)%Z. Proof. intros. reflexivity. Qed.
Lemma fk_flags_4 : forall FS, fk_flags FS K = (FS + FLOFF)%Z.
Proof. intros. unfold fk_flags. change (32 * Z.shiftl (Z.shiftr 1023 (10 - K)) (10 - K))%Z with (FLOFF - 4096)%Z. lia. Qed.
Lemma fk_frame_4 : forall FS pos, fk_frame FS K pos = (FS + FROFF + pos * SZ)%Z.
Proof. intros. unfold fk_frame. rewrite fk_size_4. lia. Qed.

Lemma land_1023 : forall h, (0 <= h)%Z -> Z.land h 1023 = (h mod 1024)%Z.
Proof. intros h Hh. change 1023%Z with (2^10 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. Qed.

Ltac solve_W_ok_rt := solve_W_rt.  (* [comment removed for export] *)

Section Proof.
  Hypothesis TLS : tls_chain_stmt.
  Hypothesis M2S : m2s_stmt 0x4b200.

  #[using="TLS M2S"] Lemma smalloc4_spec : smalloc4_stmt.
  Proof. LiaFast.lf_pins (fun (TLS M2S : LiaFast.U) => LiaFast.u0).
    unfold smalloc4_stmt, smalloc_stmt.
    intros until fl.
    rewrite !fk_nframes_4, !fk_size_4, !fk_hint_4, !fk_flags_4, !fk_frame_4.
    unfold smalloc_post, smalloc_W.
    rewrite !fk_nframes_4, !fk_size_4, !fk_hint_4, !fk_flags_4, !fk_frame_4.
    change (Z.to_nat (SZ / 8)) with 128%nat. change (SZ / 8)%Z with 128%Z. change (Z.to_nat (SZ - 40)) with 984%nat.
    intros Htp RTH FSC HINT Hh FL LEN NTH SLOT SHS ST SP1 SP2 SP3 AL16 SEPFS PRG PRT RDJ1 RDJ2 RA.
    subst tp.
    remember (rt_FS v) as FS eqn:HFS.
    remember (h mod NFR)%Z as pos eqn:Hpos.
    assert (Hposr : (0 <= pos < NFR)%Z) by (subst pos; apply Z.mod_pos_bound; lia).
    unfold fs_cells_ok in FSC.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
      pose proof (munch_refl [(bv_unsigned sp - SMALLOC_NEED, bv_unsigned sp); (FS + HOFF, FS + 40);
                              (FS + FLOFF + pos, FS + FLOFF + pos + 1);
                              (FS + FROFF + pos * SZ, FS + FROFF + pos * SZ + SZ);
                              (ASAN_B + (FS + FROFF + pos * SZ) / 8, ASAN_B + (FS + FROFF + pos * SZ) / 8 + 128)]%Z m0) as MU;
      pose proof (wmono_refl ASEGS m0) as WM
    end.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (u8arr_bound _ _ _ _ FL) as Bfl.
    pose proof RTH as RTH0. open_RT RTH0.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Hc1 & Hc2 & Ht1 & Ht2 & Hb1 & Hb2).
    rewrite <- HFS in *.
    clear RT1 RT2 RT2b RT3 RT4 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb.
    unfold rt_disj in RDJ1, RDJ2.
    set (F := (FS + FROFF + pos * SZ)%Z) in *.
    assert (HF : (app2r (F) (F + SZ))%Z /\ (F + SZ <= FS + 11571200 /\ FS + 36352 <= F /\ F mod 1024 = 0)%Z).
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
    lazymatch goal with |- forall ms', tls_chain_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc ms' -> _ => post_call ASEGS mc end.
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
    rewrite (unsigned_lit h) by lia. rewrite (land_1023 h) by lia. rewrite <- Hpos.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (u8arr_read ASEGS mc (FS + FLOFF)%Z fl pos (Z_to_bv 8 0) (Z_to_bv 64 (FS + FLOFF + pos)) FL NTH ltac:(lia) eq_refl) as RD end.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (u8arr_store_ok ASEGS mc (FS + FLOFF)%Z fl pos (Z_to_bv 64 (FS + FLOFF + pos)) FL ltac:(lia) eq_refl) as SOK end.
    step. (* [comment removed for export] *)
    change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
      pose proof (u8arr_write ASEGS mc (FS + FLOFF)%Z fl pos (Z_to_bv 8 1) FL ltac:(lia)) as FL' end.
    clear FL. store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit pos) by lia. rewrite (Z.shiftl_mul_pow2 pos 10) by lia.
    lazymatch goal with |- context [Z_to_bv 64 (FS + ?a + (?b + pos * 2 ^ 10))%Z] =>
      replace (Z_to_bv 64 (FS + a + (b + pos * 2 ^ 10)))%Z with (Z_to_bv 64 F) by (subst F; f_equal; lia) end.
    (* [comment removed for export] *)
    carve_frame 8%nat SLOT. rename FR0 into FRT.
    destruct (stk_split ASEGS _ F (F + 32)%Z (F + 1016)%Z SLOT ltac:(lia)) as [SLO SMID]. clear SLOT.
    carve_frame 8%nat SLO. rename FR0 into FRR.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply M2S | post_call ASEGS mc ] end.
    1:{ split; assumption. }
    1:{ assumption. }
    1:{ rewrite unsigned_lit by lia. lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    rewrite (unsigned_lit F) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    carve_frame 128%nat SHS.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      stash_all_but mc FR0;
      pose proof (munch_refl [(ASAN_B + F / 8, ASAN_B + F / 8 + 128)]%Z mc) as MUr;
      pose proof (wmono_refl ASEGS mc) as WMr end.
    do 16 step. (* [comment removed for export] *)
    unstash_all MUr WMr. clear MUr WMr.
    do 5 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    carve_frame 24%nat SLO.
    carve_frame 984%nat SMID.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with
      | H1 : rw_cells ASEGS mc (F + 0)%Z [CB 24 ?j1], H2 : rw_cells ASEGS mc (F + 24)%Z ?c2,
        H3 : rw_cells ASEGS mc (F + 32)%Z [CB 984 ?j3], H4 : rw_cells ASEGS mc (F + 1016)%Z ?c4 |- _ =>
          assert (FRAME : rw_cells ASEGS mc F ([CB 24 j1] ++ c2 ++ [CB 984 j3] ++ c4));
          [ apply (proj2 (rw_cells_app _ _ _ _ _)); split; [rewrite <- (Z.add_0_r F); exact H1|];
            cbn [cells_size csize Nat.add]; change (Z.of_nat 24) with 24%Z;
            apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H2|];
            cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8%Z;
            replace (F + 24 + 8)%Z with (F + 32)%Z by lia;
            apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H3|];
            cbn [cells_size csize Nat.add]; change (Z.of_nat 984) with 984%Z;
            replace (F + 32 + 984)%Z with (F + 1016)%Z by lia; exact H4
          | clear H1 H2 H3 H4; cbn [app] in FRAME ]
      end end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with
      | H : rw_cells ASEGS mc (ASAN_B + F / 8 + 0)%Z ?cs |- _ =>
          rewrite (Z.add_0_r (ASAN_B + F / 8)%Z) in H;
          pose proof (rw_cells_merge ASEGS mc (ASAN_B + F / 8)%Z [] cs [] ltac:(rewrite app_nil_r; cbn [app]; exact H)) as SHADOW;
          clear H; cbn [app cells_size csize Nat.add] in SHADOW;
          replace (cells_bytes cs) with (zeros 128) in SHADOW by (vm_compute; reflexivity)
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
