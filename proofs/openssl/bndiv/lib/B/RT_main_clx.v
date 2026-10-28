(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require PropExec.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Stdio.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx D_libkit FX_Layout FX_Exit FX_Stdio_iface I_iodefs X_atexit X_xdefs RT_state RT_client_kit. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import SegRw. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_main_shape R_depot_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pristine (m : mem) (r : Z * Z) : Prop := forall a, fst r <= a < snd r -> mrd bsegs m (wa a) = seg_rom bsegs (wa a).

Definition CLX_PRISTINE : list (Z * Z) :=
  [ (0x5e7140, 0x5e7460);          (* [comment removed for export] *)
    (0x5e7460, 0x6a0320);          (* [comment removed for export] *)
    (0xbfb0c0, 0xbfb0c4);          (* [comment removed for export] *)
    (0xbfb548, 0xbfb550);          (* [comment removed for export] *)
    (0x6a0390, 0x6a0391);          (* [comment removed for export] *)
    (0xbdadb4, 0xbdadb9);          (* [comment removed for export] *)
    (0xbd6050, 0xbd6051);          (* [comment removed for export] *)
    (0xbd6051, 0xbd6055) ]         (* [comment removed for export] *)
  ++ LIB_PRISTINE.                  (* [comment removed for export] *)

Definition CLX_RW : list (saddr * list scell) :=
  [ (SA LB_lit 0xbdada8, [SC_num 4 LN_tid]);                                                  (* [comment removed for export] *)
    (SA LB_lit 0xbfaea0, [SC_lit 1 0; SC_any 3; SC_lit 4 0; SC_lit 4 1; SC_any 4; SC_lit 8 0xbfaeb8; SC_lit 8 0; SC_lit 8 0x557954; SC_any 8]);   (* [comment removed for export] *)
    (SA LB_lit 0xbfafc0, [SC_lit 8 0x1dd8a8; SC_any 8]);                                      (* [comment removed for export] *)
    (SA LB_lit 0xbfb0e0, [SC_any 1; SC_any 1; SC_any 1; SC_lit 1 0; SC_any 4]);               (* [comment removed for export] *)
    (SA LB_lit 0x6a0340, [SC_lit 8 1]);                                                       (* [comment removed for export] *)
    (SA LB_lit 0xbfbdb8, [SC_lit 8 0x1c0a60]) ].                                              (* [comment removed for export] *)

Record clx_facts (L : layoutA) (m : mem) : Prop := mkCF {
  cf_tid : 1 <= l_tid L < 2 ^ 31;
  cf_pristine : Forall (pristine m) CLX_PRISTINE;
  cf_rw : Forall (rw_fact L m) CLX_RW
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pristine_bytes_at : forall (m : mem) lo hi a bs, pristine m (lo, hi) -> 0 <= lo -> hi <= 2 ^ 64 -> lo <= a -> a + Z.of_nat (length bs) <= hi ->
  img_bytesb a bs = true -> bytes_at bsegs m a bs.
Proof.
  intros m lo hi a bs P H0 H64 H1 H2 HB. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  rewrite (P (a + Z.of_nat i)) by (cbn [fst snd]; lia).
  exact (img_bytesb_nth bs a i b HB E).
Qed.

Lemma pristine_rw : forall (m : mem) lo hi a cs, pristine m (lo, hi) -> 0 <= lo -> hi <= 2 ^ 64 -> cells_wf cs -> lo <= a -> a + Z.of_nat (cells_size cs) <= hi ->
  img_bytesb a (cells_bytes cs) = true -> seg_rw_ok bsegs a (Z.of_nat (cells_size cs)) = true -> rw_cells bsegs m a cs.
Proof.
  intros m lo hi a cs P H0 H64 W H1 H2 HB HS. split; [split; [exact W|]|].
  - apply (pristine_bytes_at m lo hi a _ P H0 H64 H1); [|exact HB]. rewrite (cells_bytes_length cs W). exact H2.
  - exact (proj1 (seg_rw_ok_sound bsegs a _ HS m)).
Qed.

Lemma pristine_sub : forall (m : mem) lo hi lo' hi', pristine m (lo, hi) -> lo <= lo' -> hi' <= hi -> pristine m (lo', hi').
Proof. intros m lo hi lo' hi' P H1 H2 a Ha. apply P. cbn [fst snd] in *. lia. Qed.

(* [comment removed for export] *)
Lemma seg_rw_c8 : forall (m : mem) a, seg_rw_ok bsegs a 8 = true -> exists v, rw_cells bsegs m a [C8 v].
Proof.
  intros m a H. destruct (seg_rw_ok_sound bsegs a 8 H m) as [W S].
  destruct (stk_bytes_n bsegs m a 8 S) as (bs & Hl & B).
  exists (le_bytes_to_word bs). split; [split; [cbn; tauto|] | exact W].
  cbn [cells_bytes cbytes]. rewrite app_nil_r, (R_depot_defs.dep_le8_of_bytes bs Hl). exact B.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition w8 (z : Z) : list byte := le8 (Z_to_bv 64 z).
Definition STDIN_J0 : list byte := le4 (Z_to_bv 64 9) ++ le4 (Z_to_bv 64 0).
Definition STDIN_J1 : list byte := w8 0x55d37c ++ w8 0.
Definition STDIN_J2 : list byte := w8 0.
Definition STDIN_J3 : list byte := w8 0x55d3a8 ++ w8 0 ++ w8 0x55d4c0 ++ w8 0xbfb560 ++ w8 0x400 ++ w8 0 ++ w8 0 ++ w8 0 ++ w8 0 ++ le4 (Z_to_bv 64 0).
Definition STDIN_J4 : list byte := repeat (Z_to_bv 8 0) 88.

Definition zbytes (l : list byte) : list byte := l.

(* [comment removed for export] *)
Lemma img_stdout : img_bytesb RSTDOUT (cells_bytes (file_cells (Z_to_bv 64 5) 0 0 0 F_STDOUT_WRITE RSTDOUT_BUF 1024 1 (Z_to_bv 64 0) 10 (repeat (Z_to_bv 8 0) 80))) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma img_stderr : img_bytesb RSTDERR (cells_bytes (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0xbfb558 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80))) = true.
Proof. vm_compute. reflexivity. Qed.
Definition stdin_cells : list cell :=
  [CB 8 (zbytes STDIN_J0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (zbytes STDIN_J1); C8 (Z_to_bv 64 0); CB 8 (zbytes STDIN_J2);
   C8 (Z_to_bv 64 0); CB 76 (zbytes STDIN_J3); C4 (Z_to_bv 64 0xffffffff); CB 88 (zbytes STDIN_J4)].
Lemma img_stdin : img_bytesb RSTDIN (cells_bytes stdin_cells) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma img_used : img_bytesb 0x5e7250 (cells_bytes [C8 (Z_to_bv 64 0x5e7168)]) = true /\ img_bytesb 0x5e7430 (cells_bytes [C8 (Z_to_bv 64 0x5e7348)]) = true
  /\ img_bytesb 0x5e7340 (cells_bytes [C8 (Z_to_bv 64 0x5e7258)]) = true.
Proof. vm_compute. repeat split. Qed.
Lemma img_zero_cells : img_bytesb 0xbfb0c0 (cells_bytes [C4 (Z_to_bv 64 0)]) = true /\ img_bytesb 0xbfb548 (cells_bytes [C8 (Z_to_bv 64 0)]) = true
  /\ img_bytesb 0x6a0390 (cells_bytes [C1 (Z_to_bv 8 0)]) = true /\ img_bytesb (0xbdae50 + -156) (cells_bytes [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0)]) = true
  /\ img_bytesb 0xbd6050 (cells_bytes [C1 (Z_to_bv 8 0)]) = true.
Proof. vm_compute. repeat split. Qed.
Lemma img_incb : img_bytesb 0xbd6051 (cells_bytes [CB 3 (repeat (Z_to_bv 8 0) 3); C1 (Z_to_bv 8 0)]) = true /\ seg_rw_ok bsegs 0xbd6051 4 = true.
Proof. vm_compute. repeat split. Qed.

(* [comment removed for export] *)
Lemma seg_rw_clx : seg_rw_ok bsegs 0x5e7140 (0x5e7460 - 0x5e7140) = true /\ seg_rw_ok bsegs RSTDOUT_BUF 1024 = true
  /\ seg_rw_ok bsegs 0xbfb0c0 4 = true /\ seg_rw_ok bsegs 0xbfb548 8 = true /\ seg_rw_ok bsegs 0x6a0390 1 = true
  /\ seg_rw_ok bsegs (0xbdae50 + -156) 5 = true /\ seg_rw_ok bsegs SSP_GUARD 8 = true /\ seg_rw_ok bsegs g_read_stage 65536 = true.
Proof. vm_compute. repeat split. Qed.

Lemma seg_rw_sub : forall a n a' n', seg_rw_ok bsegs a n = true -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> forall m : mem, wr_at bsegs m a' n'.
Proof.
  intros a n a' n' H H1 H2 H3 m. destruct (seg_rw_ok_sound bsegs a n H m) as [(W0 & W1 & W) _].
  split; [lia|]. split; [lia|]. intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
Qed.

(* [comment removed for export] *)
Lemma cb1_c1 : forall (j : list byte), length j = 1%nat -> exists b, j = [b].
Proof. intros [|b [|]] H; try discriminate. exists b. reflexivity. Qed.
Lemma cb8_c8 : forall (j : list byte), length j = 8%nat -> exists v : word, le8 v = j.
Proof.
  intros j Hl. exists (Z_to_bv 64 (bytes_le_to_Z j)). unfold le8, word_to_le_bytes.
  pose proof (AS.PropExec.bytes_le_to_Z_bound j) as Bd. pose proof (AS.PropExec.bytes_le_to_Z_nonneg j) as Bn. rewrite Hl in Bd.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Bd; lia).
  rewrite <- Hl at 1. apply Z_to_le_bytes_of_bytes.
Qed.
Lemma cb4_c4 : forall (j : list byte), length j = 4%nat -> exists v : word, le4 v = j.
Proof.
  intros j Hl. exists (Z_to_bv 64 (bytes_le_to_Z j)). unfold le4.
  pose proof (AS.PropExec.bytes_le_to_Z_bound j) as Bd. pose proof (AS.PropExec.bytes_le_to_Z_nonneg j) as Bn. rewrite Hl in Bd.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Bd; lia).
  rewrite <- Hl at 1. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma relist : forall (m : mem) A cs cs', rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells bsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' E. split; [split; [exact Hwf'| rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.

Section Clx.
Variables (L : layoutA) (m : mem).
Hypothesis CF : clx_facts L m.

Lemma cf_pr : forall r, In r CLX_PRISTINE -> pristine m r.
Proof. exact (proj1 (Forall_forall _ _) (cf_pristine L m CF)). Qed.
Lemma cf_get : forall e, In e CLX_RW -> exists junks, rw_cells bsegs m (den_addr L (fst e)) (den_cells L (snd e) junks).
Proof. intros e H. exact (proj1 (Forall_forall _ _) (cf_rw L m CF) e H). Qed.

Ltac in_lit := repeat (first [left; reflexivity | right]).
Ltac clxrw H e := destruct (cf_get e ltac:(unfold CLX_RW; in_lit)) as (?junks & H);
  cbn [den_cells den_cell den_addr den_base den_num wcell fst snd hd tl] in H; rewrite ?Z.add_0_l in H.

(* [comment removed for export] *)
Lemma musl_data_rw : forall a cs, cells_wf cs -> 0x5e7140 <= a -> a + Z.of_nat (cells_size cs) <= 0x5e7460 -> img_bytesb a (cells_bytes cs) = true -> rw_cells bsegs m a cs.
Proof.
  intros a cs W H1 H2 HB. pose proof (cf_pr (0x5e7140, 0x5e7460) ltac:(unfold CLX_PRISTINE; in_lit)) as P.
  split; [split; [exact W|]|].
  - apply (pristine_bytes_at m 0x5e7140 0x5e7460 a _ P); [lia| lia| exact H1| rewrite (cells_bytes_length cs W); exact H2| exact HB].
  - apply (seg_rw_sub _ _ _ _ (proj1 seg_rw_clx)); lia.
Qed.

Lemma main_out : OUT_repA stdout_init m.
Proof.
  unfold OUT_repA, stdout_file. cbn [so_active so_first so_lbf_nl so_buf stdout_init].
  destruct (seg_rw_blob bsegs m RSTDOUT_BUF 1024 (proj1 (proj2 seg_rw_clx))) as (bs & Hb).
  exists (Z_to_bv 64 5), (Z_to_bv 64 0), (repeat (Z_to_bv 8 0) 80), bs.
  split; [apply musl_data_rw; [cbn; repeat split| lia| cbn; lia| exact img_stdout]|].
  split; [reflexivity|]. split; [exact Hb|]. split; [reflexivity|]. split; [unfold zlength; cbn; lia|]. intros _. reflexivity.
Qed.

Lemma main_err : ERR_repA m.
Proof.
  unfold ERR_repA, stderr_wfile0.
  exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, 0, (repeat (Z_to_bv 8 0) 80).
  split; [apply musl_data_rw; [cbn; repeat split| lia| cbn; lia| exact img_stderr]|].
  split; [reflexivity|]. split; [left; reflexivity| lia].
Qed.

Lemma main_xenv : XENVA m.
Proof.
  pose proof img_used as (U1 & U2 & U3). pose proof img_zero_cells as (Z1 & Z2 & Z3 & _ & _).
  pose proof seg_rw_clx as (_ & _ & S1 & S2 & S3 & _).
  unfold XENVA. split; [| exists (repeat (Z_to_bv 8 0) 3);
    apply (pristine_rw m 0xbd6051 0xbd6055); [apply cf_pr; unfold CLX_PRISTINE; in_lit| lia| lia| cbn; tauto| lia| cbn; lia| exact (proj1 img_incb)| exact (proj2 img_incb)]].
  clxrw TX (SA LB_lit 0xbfaea0, [SC_lit 1 0; SC_any 3; SC_lit 4 0; SC_lit 4 1; SC_any 4; SC_lit 8 0xbfaeb8; SC_lit 8 0; SC_lit 8 0x557954; SC_any 8]).
  clxrw TA (SA LB_lit 0xbfafc0, [SC_lit 8 0x1dd8a8; SC_any 8]).
  pose proof TX as [[WfX _] _]. cbn [cells_wf cell_wf] in WfX. destruct WfX as (_ & WX2 & _ & _ & WX3 & _ & _ & _ & WX4 & _).
  pose proof TA as [[WfA _] _]. cbn [cells_wf cell_wf] in WfA. destruct WfA as (_ & WA2 & _).
  destruct (cb8_c8 _ WX4) as (f1 & EF1). destruct (cb8_c8 _ WA2) as (a1v & EA1).
  exists f1, a1v. unfold XENVT.
  split.
  { clxrw T (SA LB_lit 0xbdada8, [SC_num 4 LN_tid]). exists (l_tid L). split; [exact (cf_tid L m CF)| exact T]. }
  split.
  { exists (hd [] (tl junks)), (hd [] (tl (tl (tl (tl junks))))).
    apply (relist m _ _ _ TX); [cbn [cells_wf cell_wf]; repeat split; try assumption; apply length_le8|]. cbn [cells_bytes cbytes]. rewrite EF1. reflexivity. }
  split; [apply (relist m _ _ _ TA); [cbn [cells_wf cell_wf]; repeat split; apply length_le8|]; cbn [cells_bytes cbytes]; rewrite EA1; reflexivity|].
  split; [apply (pristine_rw m 0xbfb0c0 0xbfb0c4); [apply cf_pr; unfold CLX_PRISTINE; in_lit| lia| lia| cbn; tauto| lia| cbn; lia| exact Z1| exact S1]|].
  split.
  { clxrw T (SA LB_lit 0xbfb0e0, [SC_any 1; SC_any 1; SC_any 1; SC_lit 1 0; SC_any 4]).
    pose proof T as [[Wf _] _]. cbn [cells_wf cell_wf] in Wf. destruct Wf as (W1 & W2 & W3 & _ & W4 & _).
    destruct (cb1_c1 _ W1) as (c1 & E1). destruct (cb1_c1 _ W2) as (c2 & E2). destruct (cb1_c1 _ W3) as (c3 & E3). destruct (cb4_c4 _ W4) as (t & E4).
    exists c1, c2, c3, t.
    apply (relist m _ _ _ T); [cbn [cells_wf cell_wf]; tauto|]. cbn [cells_bytes cbytes]. rewrite E1, E2, E3, E4. reflexivity. }
  split; [apply (pristine_rw m 0xbfb548 0xbfb550); [apply cf_pr; unfold CLX_PRISTINE; in_lit| lia| lia| cbn; tauto| lia| cbn; lia| exact Z2| exact S2]|].
  split; [apply musl_data_rw; [cbn; tauto| lia| cbn; lia| exact U1]|].
  split; [apply musl_data_rw; [cbn; tauto| lia| cbn; lia| exact U2]|].
  split.
  { unfold stdin_file. exists (zbytes STDIN_J0), (zbytes STDIN_J1), (zbytes STDIN_J2), (zbytes STDIN_J3), (zbytes STDIN_J4).
    apply musl_data_rw; [cbn; repeat split| lia| cbn; lia| exact img_stdin]. }
  split; [apply musl_data_rw; [cbn; tauto| lia| cbn; lia| exact U3]|].
  split; [exact (cf_pr (0x5e7460, 0x6a0320) ltac:(unfold CLX_PRISTINE; in_lit))|].
  split; [clxrw T (SA LB_lit 0x6a0340, [SC_lit 8 1]); exact T|].
  apply (pristine_rw m 0x6a0390 0x6a0391); [apply cf_pr; unfold CLX_PRISTINE; in_lit| lia| lia| cbn; tauto| lia| cbn; lia| exact Z3| exact S3].
Qed.

Lemma main_lib : lib_startA m.
Proof.
  pose proof img_zero_cells as (_ & _ & _ & _ & Z5).
  unfold lib_startA, lib_pristineA. split; [split|].
  - intros a (lo & hi & Hin & Ha).
    exact (cf_pr (lo, hi) ltac:(unfold CLX_PRISTINE; apply in_or_app; right; exact Hin) a Ha).
  - clxrw T (SA LB_lit 0xbfbdb8, [SC_lit 8 0x1c0a60]). exact T.
  - apply (pristine_rw m 0xbd6050 0xbd6051); [apply cf_pr; unfold CLX_PRISTINE; in_lit| lia| lia| cbn; tauto| lia| cbn; lia| exact Z5| exact seg_rw_latch].
Qed.

(* [comment removed for export] *)
Theorem main_clx : CLX OUT_repA ERR_repA XENVA lib_startA stdout_init m.
Proof.
  pose proof img_zero_cells as (_ & _ & _ & Z4 & _).
  pose proof seg_rw_clx as (_ & _ & _ & _ & _ & S4 & S5 & S6).
  unfold CLX.
  split; [exact main_out|]. split; [exact main_err|]. split; [exact main_xenv|]. split; [exact main_lib|].
  split; [destruct (seg_rw_c8 m SSP_GUARD S5) as (g & G); exists g; exact (proj1 G)|].
  split; [exact (errno_exists m)|].
  split; [exact (proj2 (seg_rw_ok_sound bsegs g_read_stage 65536 S6 m))|].
  split; [exact (latch_exists m)|].
  unfold cancel_cells.
  apply (pristine_rw m 0xbdadb4 0xbdadb9); [apply cf_pr; unfold CLX_PRISTINE; in_lit| lia| lia| cbn; tauto| lia| cbn; lia| exact Z4| exact S4].
Qed.

End Clx.
