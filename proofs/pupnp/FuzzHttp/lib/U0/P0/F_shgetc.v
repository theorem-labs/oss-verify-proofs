(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim StrFun ScanInt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy F_memchr Printf_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Export F_shgetc_B.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition uflow_res (txt : list Z) (off p : Z) : Z := if (off <? p)%Z then znth txt off else -1.

Definition uflow_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p off : Z) (txt : list Z) (shend : Z) (shl shc canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (uflow_res txt off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(q - 128, q); (Fp, Fp + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (q - 128) (q)
    /\ rw_cells rsegs m' Fp (ss_cells T (T + off + sread_len off p) (T + win p off) (Z_to_bv 64 M64) (T + win p off) shend shl shc)
    /\ bytes_at rsegs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition uflow_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p off rpos rend shend : Z) (txt pre post : list Z) (mode shl shc canary : word),
  rw_cells rsegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
  (mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
  rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
  bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk rsegs m (q - 128) (q) -> (4096 <= q - 128)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 128 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 128)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv rsegs m ->
  evt rsegs (uflow_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p off txt shend shl shc canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 UFLOW) fc None m (seg_rom rsegs)).

Lemma uflow_spec : uflow_stmt.
Proof.
  unfold uflow_stmt. intros until canary. intros FC Hmode TXT Hp Hoff BY [SSP1 SSP2] T0 T1 Rrp Rre Rsh SEP3 ST SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1 MI.
  pose proof (munch_refl [(q - 128, q); (Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof TXT as TXT'. destruct TXT' as (Htxt & NZ & BYT & AL & L40).
  pose proof (rw_cells_bound _ _ _ _ FC) as B. cbn [cells_size csize Nat.add ss_cells] in B.
  assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length.
  pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite LTX in BB.
  unfold UFLOW, got_ssp, ssp_guard, M64 in *. unfold zlength in *. pose_word_ranges.
  zs. carve_frame 64%nat ST.
  do 6 zs.
  zs. zs. zs. zs. zs.
  pose proof toread_spec as TRS. unfold toread_stmt in TRS.
  destruct (stk_split _ _ _ (q - 80)%Z _ ST ltac:(lia)) as [ST1 ST2].
  assert (LT3 : length txt = (length pre + S (length post))%nat) by (rewrite Htxt, length_app; reflexivity).
  zs. callw (eapply TRS; [hyp | exact Hmode | lia | lia | lia | lia | lia | replace (q + -64 - 16)%Z with (q - 80)%Z by lia; exact ST2 | lia | lia | lia | lia | lia | hyp]).
  rename POST into FC1. rename PC into ST2. replace (q + -64 - 16)%Z with (q - 80)%Z in ST2 by lia. unfold ss_cells, w0, STRING_READ in FC1.

  lazymatch goal with FR' : rw_cells _ ?mc (q + -64)%Z (CB 16 ?bs :: ?rest) |- _ =>
    pose proof (rw_cells_split_CB rsegs mc (q + -64)%Z [] 16 bs rest [15; 1]%nat FR' eq_refl) as FR2; clear FR'; cbn [mk_CB_cells app] in FR2;
    pose proof (proj1 (rw_cells_app rsegs mc (q + -64)%Z [_] _) FR2) as [J15 FR3]; clear FR2;
    pose proof (proj1 (rw_cells_app rsegs mc _ [_] _) FR3) as [DC0 FR]; clear FR3 end.
  cbn [cells_size csize Nat.add] in DC0, FR.
  lazymatch type of DC0 with rw_cells _ _ ?a _ => replace a with (q + -49)%Z in DC0 by lia end.
  lazymatch type of FR with rw_cells _ _ ?a _ => replace a with (q + -48)%Z in FR by lia end.
  destruct (rw_cells_CB1 _ _ _ DC0) as [dj DC]. clear DC0.
  zs. zs. br K0.
  zs. zs. zs. zs. zs.
  pose proof (stk_merge _ _ _ _ _ ST1 ST2 ltac:(lia)) as ST3. clear ST1 ST2.
  pose proof sread_spec as SRS. unfold sread_stmt, STRING_READ in SRS.
  zs. replace (ret_pc (Z_to_bv 64 130896)) with (Z_to_bv 64 130896) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  callw (eapply SRS with (off := off) (pre := pre) (post := post);
    [unfold ss_cells, w0; hyp | exact TXT | exact Hp | exact Hoff | hyp | replace (q + -64 + 15)%Z with (q + -49)%Z by lia; exact DC | lia | lia | lia | lia | lia
    | lia | unfold zlength; lia | unfold zlength; lia
    | replace (q + -64 - 64)%Z with (q - 128)%Z by lia; exact ST3 | lia | lia | lia | lia | lia | unfold zlength; lia | lia | lia | hyp ]).
  rename PC into ST. replace (q + -64 - 64)%Z with (q - 128)%Z in ST by lia. rename PC1 into DC2. rename POST into BY3. rename PC0 into FC2.
  assert (Rch : (0 <= znth txt off < 256)%Z).
  { destruct (Z.lt_ge_cases off (Z.of_nat (length txt))).
    - apply (proj1 (Forall_forall _ _) BYT). apply znth_In. unfold zlength. lia.
    - rewrite znth_ge by (unfold zlength; lia). lia. }
  unfold sread_len, uflow_res in *. destruct (Z.ltb_spec0 off p).
  - zs. br K1. zs. cbv beta. rewrite (unsigned_lit8 (znth txt off)) by lia.
    do 3 zs. br K2; try (exfalso; apply K2; reflexivity).
    do 8 zs.
    release_frame J15 ST (q + -49)%Z. release_frame DC2 ST (q + -48)%Z. release_frame FR ST q.
    apply evt_done. unfold uflow_post, uflow_res, sread_len. replace (off <? p) with true by (symmetry; apply Z.ltb_lt; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact FC2|]. split; [exact BY3|]. split; [exact SSP1 | exact SSP2].
  - zs. br K1.
    do 3 zs. br K2; try (exfalso; apply K2; reflexivity).
    do 8 zs.
    release_frame J15 ST (q + -49)%Z. release_frame DC2 ST (q + -48)%Z. release_frame FR ST q.
    apply evt_done. unfold uflow_post, uflow_res, sread_len. replace (off <? p) with false by (symmetry; apply Z.ltb_ge; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact FC2|]. split; [exact BY3|]. split; [exact SSP1 | exact SSP2].
Qed.

Definition shgetc_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p co : Z) (f : shfile) (txt : list Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (sh_getc f))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(q - 160, q); (Fp, Fp + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (q - 160) q
    /\ rw_cells rsegs m' Fp (rf_cells T (win p co) (snd (sh_getc f)) ssJ)
    /\ bytes_at rsegs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition shgetc_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p co : Z) (f : shfile) (txt pre post : list Z) (canary : word),
  rw_cells rsegs m Fp (rf_cells T co f ssJ) ->
  sh_stdio f = true -> sh_n f = p -> sh_buf f = txt ->
  sh_rpos f = co -> (0 <= co <= p)%Z -> (sh_shlim_neg f = true -> co = p) -> (0 <= sh_cnt0 f <= sh_rpos f)%Z ->
  rtext T txt pre post -> p = zlength pre -> bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk rsegs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 160 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 160)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv rsegs m ->
  evt rsegs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p co f txt canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SHGETC) fc None m (seg_rom rsegs)).

Lemma shgetc_spec : shgetc_stmt.
Proof.
  unfold shgetc_stmt. intros until canary. intros FC ST0 Hn Hbuf Hrp Hco Hlat Hc0 TXT Hp BY [SSP1 SSP2] T0 T1 SEP3 ST SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1 MI.
  pose proof (munch_refl [(q - 160, q); (Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof TXT as TXT'. destruct TXT' as (Htxt & NZ & BYT & AL & L40).
  assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length.
  assert (LT3 : length txt = (length pre + S (length post))%nat) by (rewrite Htxt, length_app; reflexivity).
  pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite LTX in BB.
  destruct f as [buf rpos cnt0 n st sn]. cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg] in *. subst st n buf rpos.
  unfold rf_cells, rf_rend in FC. cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg] in FC.
  assert (J4 : length (j_pad0 ssJ) = 4%nat /\ length (j_pad1 ssJ) = 4%nat) by (split; reflexivity).
  cbn [ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
  pose proof (rw_cells_bound _ _ _ _ FC) as B. cbn [cells_size csize Nat.add] in B.
  unfold SHGETC, got_ssp, ssp_guard, STRING_READ, M64 in *. unfold zlength in *.
  pose proof (win_range p co Hco) as WR.
  zs. carve_frame 32%nat ST.
  do 10 zs.

  assert (EOFT : forall m1 (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) j8 she shl shc cnt,
    cnt = (p - cnt0)%Z -> co = p ->
    mem_inv rsegs m1 -> munch [(q - 160, q); (Fp, Fp + 232)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (q - 160) (q + -32) ->
    rw_cells rsegs m1 (q + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs m1 Fp (rf_cells_raw T p (mkSh txt p cnt0 p true true) ssJ she shl shc) ->
    bytes_at rsegs m1 T (zbytes txt) -> rw_cells rsegs m1 172368 [C8 (Z_to_bv 64 375432)] -> rw_cells rsegs m1 375432 [C8 canary] ->
    sh_getc {| sh_buf := txt; sh_rpos := co; sh_cnt0 := cnt0; sh_n := p; sh_stdio := true; sh_shlim_neg := sn |} = ((-1)%Z, mkSh txt p cnt0 p true true) ->
    evt rsegs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p co
                 {| sh_buf := txt; sh_rpos := co; sh_cnt0 := cnt0; sh_n := p; sh_stdio := true; sh_shlim_neg := sn |} txt canary m)
      (MS (mkR x1 (Z_to_bv 64 (q + -32)) gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 cnt) (Z_to_bv 64 T) (Z_to_bv 64 (T + p)) x12 x13 x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x20c08) fc None m1 (seg_rom rsegs))).
  { clear FC MI MU WM ST FR BY SSP1 SSP2.
    intros m1 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 j8 she shl shc cnt Ecnt Eco MI MU WM ST FR FC BY SSP1 SSP2 EG. subst cnt.
    unfold rf_cells_raw, rf_rend in FC.
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
    do 11 zs.
    release_frame FR ST q.
    apply evt_done. unfold shgetc_post. rewrite EG. cbn [fst snd].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split. { unfold rf_cells, rf_rend. cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale].
             unfold STRING_READ, M64. replace (win p co) with p by (subst co; unfold win; rewrite Z.sub_diag; reflexivity).
             replace (- cnt0)%Z with (p - cnt0 + (T - (T + p)))%Z by lia. hyp. }
    split; [exact BY|]. unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2]. }
  destruct sn.
  -
    pose proof (Hlat eq_refl) as Eco. subst co.
    replace (if true then 18446744073709551615%Z else 0%Z) with 18446744073709551615%Z in * by reflexivity.
    zs. br K1; try (exfalso; clear -K1; lia).
    zs. br K2.
    eapply EOFT; try hyp; try lia.
    all: try (unfold sh_getc; cbn [sh_stdio sh_rpos sh_n negb sh_buf sh_cnt0]; rewrite Z.eqb_refl; reflexivity).
    all: unfold rf_cells_raw, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale];
         unfold STRING_READ, M64; hyp.
  -
    clear Hlat.
    replace (if false then 18446744073709551615%Z else 0%Z) with 0%Z in * by reflexivity.
    pose proof uflow_spec as UFS. unfold uflow_stmt, got_ssp, ssp_guard, UFLOW in UFS.
    assert (Rch : (0 <= znth txt co < 256)%Z).
    { destruct (Z.lt_ge_cases co (Z.of_nat (length txt))).
      - apply (proj1 (Forall_forall _ _) BYT). apply znth_In. unfold zlength. lia.
      - rewrite znth_ge by (unfold zlength; lia). lia. }
    zs. br K1; try (exfalso; clear -K1; lia).
    zs. zs.
    callw (eapply UFS with (off := co) (pre := pre) (post := post) (p := p);
      [ unfold ss_cells, w0, zero4, STRING_READ, M64; hyp
      | right; reflexivity | exact TXT | exact Hp | | hyp | unfold ssp_cells, got_ssp, ssp_guard; split; hyp | | | | | |
      | replace (q + -32 - 128)%Z with (q - 160)%Z by lia; hyp | | | | | | | | | | hyp ]; unfold zlength; lia).
    rename PC into ST. replace (q + -32 - 128)%Z with (q - 160)%Z in ST by lia. rename PC0 into FC. clear BY SSP1 SSP2. rename PC1 into BY. destruct POST as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold uflow_res, sread_len in *. unfold ss_cells, w0, zero4 in FC.
    destruct (Z.ltb_spec0 co p).
    +
      zs. br K2; try (exfalso; clear -K2 Rch; lia).
      do 5 zs. br K3; try (exfalso; clear -K3; lia).
      do 5 zs. zs. br K4; try (exfalso; clear -K4; lia).
      do 5 zs.
      release_frame FR ST q.
      apply evt_done. unfold shgetc_post. unfold sh_getc. cbn [sh_stdio sh_rpos sh_n negb sh_buf sh_cnt0 fst snd].
      replace (co =? p) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb fst snd sh_stdio sh_rpos sh_n sh_buf sh_cnt0 sh_shlim_neg].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [hyp|]. split; [exact ST|].
      split. { unfold rf_cells, rf_rend. cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale].
               unfold STRING_READ, M64 in *. hyp_cells. }
      split; [exact BY|]. unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
    +
      assert (Ep : co = p) by lia. subst co.
      replace (T + p + 0)%Z with (T + p)%Z in FC by lia.
      replace (win p p) with p in FC by (unfold win; rewrite Z.sub_diag; reflexivity).
      zs. br K2; try (exfalso; clear -K2; lia).
      zs. zs.
      eapply EOFT; try hyp; try lia.
      all: try (unfold sh_getc; cbn [sh_stdio sh_rpos sh_n negb sh_buf sh_cnt0]; rewrite Z.eqb_refl; reflexivity).
      all: unfold rf_cells_raw, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale];
           unfold STRING_READ, M64 in *; hyp.
Qed.
