(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim StrFun ScanInt ScanIntProps.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy F_memchr Printf_lib F_errno_location.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_rfile F_intscan_lib F_intscan_J F_strtol.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S2.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (S : Z) (str : list byte) (E base : Z) (ejunk : list byte) (errv canary : word) (lo : Z).
  Hypothesis HE : (E <> 0%Z -> rw_cells rsegs m E [CB 8 ejunk]).
  Hypothesis LO : (lo <= bv_unsigned sp - 528)%Z.
  Hypothesis SG0 : (375432 + 8 <= lo)%Z.
  Hypothesis Q1 : (bv_unsigned sp < 2^63)%Z.
  Hypothesis TP : (4096 + 164 <= bv_unsigned tp)%Z.
  Hypothesis T0 : (4096 <= S)%Z.
  Hypothesis SPT : (S + Z.of_nat (length str) + 1 <= bv_unsigned sp - 528 \/ bv_unsigned sp <= S)%Z.
  Hypothesis SG2 : (S + Z.of_nat (length str) + 1 <= 172368 \/ 172368 + 8 <= S)%Z.
  Hypothesis SG3 : (S + Z.of_nat (length str) + 1 <= 375432 \/ 375432 + 8 <= S)%Z.
  Hypothesis SE1 : (bv_unsigned tp - 164 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned tp - 164)%Z.
  Hypothesis SE3 : (bv_unsigned tp - 164 + 4 <= S \/ S + Z.of_nat (length str) + 1 <= bv_unsigned tp - 164)%Z.
  Hypothesis SE4 : (bv_unsigned tp - 164 + 4 <= 172368 \/ 172368 + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis SE5 : (bv_unsigned tp - 164 + 4 <= 375432 \/ 375432 + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis HE2 : (E <> 0 -> (E + 8 <= lo \/ bv_unsigned sp <= E) /\ (E + 8 <= S \/ S + Z.of_nat (length str) + 1 <= E) /\
             (E + 8 <= bv_unsigned tp - 164 \/ bv_unsigned tp - 164 + 4 <= E) /\
             (E + 8 <= 172368 \/ 172368 + 8 <= E) /\ (E + 8 <= 375432 \/ 375432 + 8 <= E) /\ 0 <= E /\ E + 8 <= 2^64)%Z.

  Definition tail_stmt (tpc : Z) : Prop :=
    forall (m1 : word -> option byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (J : rfj) (co : Z) (fR : shfile) (ev : word) (txt : list Z) (p : Z),
    munch [(bv_unsigned sp - 528, bv_unsigned sp); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z m m1 ->
    wmono rsegs m m1 -> mem_inv rsegs m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -288 - 240) -> stk rsegs m1 (bv_unsigned sp + -288 - 240) (bv_unsigned sp + -288) ->
    rw_cells rsegs m1 (bv_unsigned sp + -288) (rf_cells S co fR J) ->
    bytes_at rsegs m1 S (zbytes txt) -> zbytes txt = str ++ [Z_to_bv 8 0] ->
    ssp_cells m1 canary -> rw_cells rsegs m1 (bv_unsigned tp - 164) [C4 ev] ->
    rw_cells rsegs m1 (bv_unsigned sp + -288 + Z.of_nat 232) [C8 canary; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    sh_stdio fR = false -> (0 <= sh_cnt0 fR <= sh_rpos fR)%Z -> (sh_rpos fR <= p)%Z -> (0 <= p <= Z.of_nat (length str))%Z ->
    evt rsegs (strtol_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str E canary lo m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -288)) gp tp x5 x6 x7 (Z_to_bv 64 E) (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 base) (Z_to_bv 64 375432) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 tpc) fc None m1 (seg_rom rsegs)).

  #[using="ejunk HE LO SG0 Q1 TP T0 SPT SG2 SG3 SE1 SE3 SE4 SE5 HE2"] Lemma L_tail_ll : tail_stmt 0x23e2c.
  Proof.
    unfold tail_stmt. intros until p. intros MU WM MI STlo ST FC BY ZB [SSP1 SSP2] ERR FRhi RS RC RR PP.
    unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (rw_cells_bound _ _ _ _ ERR) as BER. cbn [cells_size csize Nat.add] in BER.
    rewrite ZB in BY. pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    assert (HE' : E <> 0%Z -> rw_cells rsegs m1 E [CB 8 ejunk]).
    { intros N. destruct (HE2 N) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      eapply rw_cells_transport; [exact (HE N) | exact MU | exact WM | cbn; lia]. }
    apply (munch_weaken _ [(bv_unsigned sp - 528, bv_unsigned sp); (E, E + 8); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z) in MU.
    2:{ unfold sub_fp; cbn [outside]; intros; lia. }
    stash HE. stash HE2. stash SG2. stash SG3. stash SE3. stash SE4. stash SE5.
    pose_word_ranges.
    unfold rf_cells, rf_rend in FC. rewrite RS in FC.
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

    cut_cells FC 4%nat FCb (bv_unsigned sp + -264)%Z.
    cut_cells FCb 8%nat FCc (bv_unsigned sp + -200)%Z.
    cut_cells FCc 1%nat FCd (bv_unsigned sp + -192)%Z.
    cut_cells FCd 16%nat FCe (bv_unsigned sp + -88)%Z.
    cut_cells FCe 1%nat FCf (bv_unsigned sp + -80)%Z.
    apply stk_of_rw_cells in FCb. apply stk_of_rw_cells in FCd. apply stk_of_rw_cells in FCf.
    cbn [cells_size csize Nat.add] in FCb, FCd, FCf.
    replace (bv_unsigned sp + -264 + Z.of_nat 64)%Z with (bv_unsigned sp + -200)%Z in FCb by lia.
    replace (bv_unsigned sp + -192 + Z.of_nat 104)%Z with (bv_unsigned sp + -88)%Z in FCd by lia.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in FCf by lia.
    change (Z.of_nat 232) with 232%Z in FRhi. replace (bv_unsigned sp + -288 + 232)%Z with (bv_unsigned sp + -56)%Z in FRhi by lia.
    zs. brf K1.
    -
      zs. zs. zs. br K2.
      zs. zs. zs. zs. zs. zs. zs.
      pose proof (stk_merge _ _ _ _ _ STlo ST ltac:(lia)) as ST2. clear STlo ST.
      release_frame FC ST2 (bv_unsigned sp + -264)%Z.
      pose proof (stk_merge _ _ _ _ _ ST2 FCb ltac:(lia)) as ST3. clear ST2 FCb.
      release_frame FCc ST3 (bv_unsigned sp + -192)%Z.
      pose proof (stk_merge _ _ _ _ _ ST3 FCd ltac:(lia)) as ST2. clear ST3 FCd.
      release_frame FCe ST2 (bv_unsigned sp + -80)%Z.
      pose proof (stk_merge _ _ _ _ _ ST2 FCf ltac:(lia)) as ST3. clear ST2 FCf. rename ST3 into ST2.
      release_frame FRhi ST2 (bv_unsigned sp).
      zs.
      apply evt_done. unfold strtol_post, STRTOL_DEPTH, got_ssp, ssp_guard.
      do 16 eexists. exists ev, (sh_rpos fR - sh_cnt0 fR)%Z.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST2|].
      split; [exact BY|]. split; [exact SSP1|]. split; [exact SSP2|]. split; [exact ERR|].
      split; [lia|]. intros N; exfalso; unstash; mlia2.
    -
      unfold hidden in HE2. assert (NE : E <> 0%Z) by (intros EE; rewrite EE in K1; apply K1; reflexivity).
      destruct (HE2 NE) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). specialize (HE' NE).
      pose proof (rw_cells_bound _ _ _ _ HE') as BE. cbn [cells_size csize Nat.add] in BE.
      stash D1. stash D2. stash D3. stash D4. stash D5. stash HE2.
      zs. zs. zs. zs. zs. zs. unfold hidden in D1, D2, D3, D4, D5. zs. stash D1. stash D2. stash D3. stash D4. stash D5.
      zs. zs. zs. br K2.
      zs. zs. zs. zs. zs. zs. zs.
      pose proof (stk_merge _ _ _ _ _ STlo ST ltac:(lia)) as ST2. clear STlo ST.
      release_frame FC ST2 (bv_unsigned sp + -264)%Z.
      pose proof (stk_merge _ _ _ _ _ ST2 FCb ltac:(lia)) as ST3. clear ST2 FCb.
      release_frame FCc ST3 (bv_unsigned sp + -192)%Z.
      pose proof (stk_merge _ _ _ _ _ ST3 FCd ltac:(lia)) as ST2. clear ST3 FCd.
      release_frame FCe ST2 (bv_unsigned sp + -80)%Z.
      pose proof (stk_merge _ _ _ _ _ ST2 FCf ltac:(lia)) as ST3. clear ST2 FCf. rename ST3 into ST2.
      release_frame FRhi ST2 (bv_unsigned sp).
      zs.
      apply evt_done. unfold strtol_post, STRTOL_DEPTH, got_ssp, ssp_guard.
      do 16 eexists. exists ev, (sh_rpos fR - sh_cnt0 fR)%Z.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST2|].
      split; [exact BY|]. split; [exact SSP1|]. split; [exact SSP2|]. split; [exact ERR|].
      split; [lia|]. intros _.
      match goal with H : rw_cells _ _ E [C8 ?w] |- _ =>
        replace w with (Z_to_bv 64 (S + (sh_rpos fR - sh_cnt0 fR))) in H; [exact H|] end.
      apply Z_to_bv_eqm. rewrite ?land_W64. Z.div_mod_to_equations. lia.
  Qed.
End S2.

Lemma strtoll_proof : strtox_stmt strtoll_entry.
  Proof.
    unfold strtox_stmt, strtoll_entry, STRTOL_DEPTH. intros until lo. intros BY HE ERR SSP1 SSP2 ST MI Hbase LO SG0 Q1 TP T0 T1 L40 SPT SG2 SG3 SE1 SE3 SE4 SE5 HE2.
    unfold got_ssp, ssp_guard in *.
    stash HE. stash HE2. stash SG2. stash SG3. stash SE3. stash SE4. stash SE5.
    pose proof (munch_refl [(bv_unsigned sp - 528, bv_unsigned sp); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof (rw_cells_bound _ _ _ _ ERR) as BER. cbn [cells_size csize Nat.add] in BER.
    pose_word_ranges.
    zs. carve_frame 288%nat ST.
    assert (LJ : length junk = 288%nat) by (destruct FR as [[[LJ _] _] _]; exact LJ).
    do 6 zs.
    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.

    apply (rw_cells_split_CB _ _ _ [] 8 _ _ [4;4]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (rw_cells_split_CB _ _ _ [_;_;_;_] 64 _ _ [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (rw_cells_split_CB _ _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_] 136 _ _ [8;8;8;4;4;8;4;4;4;4;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    conv_cells FR [0;4;5;6;7;8;9;10;11;13;14;15;16;17;18;19;20;21;23;24;25;26;27;28;29;30;31;32]%nat.
    repeat match type of FR with context [le_bytes_to_word ?b] => let w := fresh "jw" in set (w := le_bytes_to_word b) in FR; clearbody w end.
    lazymatch type of FR with rw_cells _ _ _ (_ :: CB 4 ?b :: _) => set (pd0 := b) in FR end.
    match type of FR with context [CB 4 ?b] => lazymatch b with pd0 => fail | _ => set (pd1 := b) in FR end end.
    assert (HJ : length pd0 = 4%nat /\ length pd1 = 4%nat).
    { pose proof (proj1 (proj1 FR)) as WF. cbn [cells_wf cell_wf] in WF. LiaTuning.ctauto. }
    clearbody pd0 pd1. clear LJ junk.

    lazymatch type of FR with rw_cells _ ?mm ?A ?cs =>
      let cs1 := eval cbn [firstn] in (firstn 33 cs) in let cs2 := eval cbn [skipn] in (skipn 33 cs) in
      change (rw_cells rsegs mm A (cs1 ++ cs2)) in FR;
      destruct (proj1 (rw_cells_app rsegs mm A cs1 cs2) FR) as [FCf FRhi]; clear FR; cbn [cells_size csize Nat.add] in FRhi end.
    lazymatch type of FCf with rw_cells _ _ _ [C4 ?w0; CB 4 ?p0; C8 _; C8 _; C8 ?w24; C8 ?w32; C8 ?w40; C8 ?w48; C8 ?w56; C8 ?w64; C8 ?w72; C8 ?w80; C8 _;
                                            C8 ?w96; C8 ?w104; C8 ?w112; C4 ?w120; C4 ?w124; C8 ?w128; C4 ?w136; C4 ?w140; C4 ?w144; CB 4 ?p1;
                                            C8 ?w152; C8 ?w160; C8 ?w168; C8 ?w176; C8 ?w184; C8 ?w192; C8 ?w200; C8 ?w208; C8 ?w216; C8 ?w224] =>
      pose (J := mkJ w0 p0 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 w112 w120 w124 w128 w136 w140 w144 p1 w152 w160 w168 w176 w208 w216 w224);
      set (she := w184); set (shl := w192); set (shc := w200) end.
    set (txt := map bv_unsigned (str ++ [Z_to_bv 8 0])).
    set (fi := mkSh txt 0 0 0 false false).
    lazymatch type of FCf with rw_cells _ ?mm ?A _ =>
      assert (FC0 : rw_cells rsegs mm A (rf_cells_raw S 0 fi J she shl shc))
        by (unfold rf_cells_raw, rf_rend, J, fi, she, shl, shc; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale]; unfold M64; hyp_cells) end.
    clear FCf.

    assert (ZB : zbytes txt = str ++ [Z_to_bv 8 0]) by (unfold txt; apply zbytes_bytes).
    assert (LT : length txt = (length str + 1)%nat) by (unfold txt; rewrite length_map, length_app; cbn; lia).
    assert (BYT : Forall (fun c => 0 <= c < 256)%Z txt).
    { unfold txt. apply Forall_map. apply Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. cbn. lia. }
    assert (IN0 : In 0%Z txt). { unfold txt. rewrite map_app. apply in_or_app. right. left. reflexivity. }
    destruct (first_nul_spec txt IN0) as (PL & PNUL & PNZ). set (p := Z.of_nat (first_nul txt)) in *.
    assert (OKi : sh_ok S txt fi). { unfold sh_ok, fi, zlength; cbn. repeat split; try reflexivity; try lia; try (intros X; discriminate X). }
    destruct HJ as [HJ0 HJ1].
    pose proof shlim_spec as SL. unfold shlim_stmt in SL.
    zs. zs. zs.
    callw (eapply SL with (txt := txt); [exact FC0 | exact OKi | exact HJ0 | exact HJ1 | lia | lia | intros X; discriminate X | hyp]).
    clear SL. match goal with H : rw_cells _ ?m' _ (rf_cells _ _ _ _) |- _ => rename H into FC1 end.
    change (sh_lim0 fi) with (stf0 txt) in FC1.
    destruct (intscan_strtol txt base IN0 BYT Hbase) as (fR & HM & RB & RS & RC & RR). fold p in RR.
    assert (RJ0 : RFJ S txt p J 0 0 1 (stf0 txt)).
    { unfold RFJ, sh_ok, stf0, zlength; cbn. repeat split; try reflexivity; try lia; try (intros X; discriminate X). }
    pose proof intscan_spec as IS. unfold intscan_stmt, intscan_post, is_W, IS_DEPTH, INTSCAN, got_ssp, ssp_guard in IS.
    zs. zs. zs. zs.
    match goal with H : stk _ ?mm lo _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split _ _ _ (bv_unsigned sp + -288 - 240)%Z _ H ltac:(lia)) as [STlo SThi]; clear H end.
    zs. callw (eapply IS with (pre := []) (post := []) (p := p) (txt := txt);
      [ exact HM | intros X; discriminate X | exact BYT | unfold zlength; lia | exact PNUL | exact FC1 | exact RJ0 | lia | lia | split; assumption
      | rewrite ZB; hyp | unfold ssp_cells, got_ssp, ssp_guard; split; hyp | hyp | lia | lia | unstash; unfold zlength; lia
      | exact SThi | lia | lia | lia | lia | unstash; unfold zlength; lia | lia | unstash; unfold zlength; lia | unstash; unfold zlength; lia | lia
      | unstash; lia | unstash; lia | unstash; unfold zlength; lia | unstash; lia | unstash; lia | exact Hbase | lia | lia | hyp ]).
    clear IS. unstash.
    eapply L_tail_ll; try eassumption; try LiaTuning.alia.
  Qed.
