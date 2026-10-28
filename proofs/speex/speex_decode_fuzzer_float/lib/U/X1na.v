(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hv X1nb X1mc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c4.
Local Ltac plia_gen stock ::= plia_size stock.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Definition nb_decode_stmtW : Prop := nb_decode_stmt (ptr:=bptr) io_notify stderr_wfile ssp_cells.

Local Ltac pristine TP :=
apply rw_cells_of_pristine;
[ exact TP
| cbn; repeat split
| unfold RTABLES_LO, NB_SUBMODES_PTR, NB_GOT_STDERR, NB_STDERR_VAR, NB_GOT_LSP_HIGH, NB_GOT_LSP_NB; cbn; lia
| match goal with |- ?a + Z.of_nat ?n <= ?h => let v := eval cbv in (Z.of_nat n) in change (a + v <= h) end;
unfold RTABLES_HI, NB_SUBMODES_PTR, NB_GOT_STDERR, NB_STDERR_VAR, NB_GOT_LSP_HIGH, NB_GOT_LSP_NB; cbn; lia
| vm_compute; reflexivity ].

Lemma rw_ro_cells : forall m A cs, rw_cells rsegs m A cs -> ro_cells rsegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.

Lemma nb_tables_of_pristine : forall m, rtables_pristine m -> nb_tables m.
Proof.
intros m TP. unfold nb_tables.
split. { apply (u8arr_of_rw_cells rsegs m NB_SUBMODES_PTR (length (u64s (map (Z_to_bv 64) nb_submode_ptrs)))). pristine TP. }
split. { intros r Hr. unfold nb_smrecs in Hr.
repeat (destruct Hr as [<-|Hr]; [apply rw_ro_cells; unfold smrec_cells; cbv zeta; pristine TP|]). destruct Hr. }
split. { intros r p Hr Hp. unfold nb_smrecs in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn in Hp; first [discriminate | injection Hp as <-; apply rw_ro_cells; unfold ltp_par_cells; cbn -[rw_cells]; pristine TP] |]).
destruct Hr. }
split. { intros r p Hr Hp. unfold nb_smrecs in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn in Hp; first [discriminate | injection Hp as <-; apply rw_ro_cells; unfold scb_par_cells; cbn -[rw_cells]; pristine TP] |]).
destruct Hr. }
split; [apply rw_ro_cells; pristine TP|]. split; [apply rw_ro_cells; pristine TP|].
unfold lsp_cdbk_got. split; apply rw_ro_cells; pristine TP.
Qed.

Lemma u8arr_nil : forall m A, 0 <= A <= 2^64 -> u8arr rsegs m A [].
Proof.
intros m A HA. split; [apply bytes_at_nil; exact HA|]. cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma u8arr_join : forall m A a b, u8arr rsegs m A a -> u8arr rsegs m (A + Z.of_nat (length a)) b -> u8arr rsegs m A (a ++ b).
Proof.
intros m A a b [Ba Wa] [Bb Wb]. split.
- apply bytes_at_app. split; assumption.
- rewrite app_length, Nat2Z.inj_add. apply wr_at_app; [lia| lia|]. split; assumption.
Qed.

Lemma u8arr_len_bound : forall m A bs, u8arr rsegs m A bs -> 0 <= A /\ A + Z.of_nat (length bs) <= 2^64.
Proof. intros m A bs U. exact (u8arr_bound rsegs m A bs U). Qed.

Lemma f32_bytes_length : forall ws, length (cells_bytes (f32 ws)) = (4 * length ws)%nat.
Proof. intros ws. rewrite (cells_bytes_length (f32 ws) (cells_wf_f32 ws)). apply cells_size_f32. Qed.

Lemma f32_as_u8arr : forall m A ws, rw_cells rsegs m A (f32 ws) ->
u8arr rsegs m A (cells_bytes (f32 ws)) /\ length (cells_bytes (f32 ws)) = (4 * length ws)%nat.
Proof.
intros m A ws H. pose proof (rw_cells_f32_CB _ _ _ _ H) as [[_ B] W]. split; [| apply f32_bytes_length].
unfold u8arr. rewrite f32_bytes_length.
split; [cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B|].
cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r in W. exact W.
Qed.

Lemma u8arr_as_f32 : forall m A bs (n : nat), u8arr rsegs m A bs -> length bs = (4 * n)%nat ->
exists ws, length ws = n /\ rw_cells rsegs m A (f32 ws).
Proof.
intros m A bs n U L. apply (rw_cells_CB_f32 rsegs m A n bs).
destruct U as [B W]. split; [split; [cbn; split; [exact L| exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B] |].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, <- L. exact W.
Qed.

Lemma u8arr_window : forall m D bs i n,
u8arr rsegs m D bs -> 0 <= i -> 0 <= n -> i + n <= Z.of_nat (length bs) ->
u8arr rsegs m D (firstn (Z.to_nat i) bs)
/\ rw_cells rsegs m (D + i) [CB (Z.to_nat n) (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs))]
/\ u8arr rsegs m (D + i + n) (skipn (Z.to_nat (i + n)) bs).
Proof.
intros m D bs i n [B W] Hi Hn Hin.
rewrite <- (firstn_skipn (Z.to_nat i) bs) in B. apply bytes_at_app in B. destruct B as [B1 B23].
rewrite firstn_length_le in B23 by lia. rewrite Z2Nat.id in B23 by lia.
rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) bs)) in B23. apply bytes_at_app in B23. destruct B23 as [B2 B3].
rewrite firstn_length_le in B3 by (rewrite skipn_length; lia). rewrite Z2Nat.id in B3 by lia.
rewrite skipn_skipn in B3. replace (Z.to_nat n + Z.to_nat i)%nat with (Z.to_nat (i + n)) in B3 by lia.
pose proof W as (W0 & W1 & Wi).
split; [| split].
- split; [exact B1|]. rewrite firstn_length_le by lia. rewrite Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros k Hk. apply Wi. lia.
- split; [split|].
+ cbn. rewrite firstn_length_le by (rewrite skipn_length; lia). split; [reflexivity| exact I].
+ cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B2.
+ cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros k Hk.
replace (D + i + k) with (D + (i + k)) by lia. apply Wi. lia.
- split; [exact B3|]. rewrite skipn_length. split; [lia|]. split; [lia|]. intros k Hk.
replace (D + i + n + k) with (D + (i + n + k)) by lia. apply Wi. lia.
Qed.

Lemma out_window : forall m OUT outb k,
u8arr rsegs m OUT outb -> Z.of_nat (length outb) = HOUT_BYTES -> 160 <= k -> 4 * k + 640 <= HOUT_BYTES ->
exists ows iws mid tail,
length ows = 160%nat /\ length iws = 160%nat /\
rw_cells rsegs m OUT (f32 ows) /\ rw_cells rsegs m (OUT + 4 * k) (f32 iws) /\
u8arr rsegs m (OUT + 640) mid /\ Z.of_nat (length mid) = 4 * k - 640 /\
u8arr rsegs m (OUT + 4 * k + 640) tail /\ Z.of_nat (length tail) = HOUT_BYTES - 4 * k - 640.
Proof.
intros m OUT outb k U L Hk Hk2. unfold HOUT_BYTES in *.
destruct (u8arr_window m OUT outb (4 * k) 640 U ltac:(lia) ltac:(lia) ltac:(lia)) as (A1 & B1 & C1).
assert (LA1 : Z.of_nat (length (firstn (Z.to_nat (4 * k)) outb)) = 4 * k) by (rewrite firstn_length_le by lia; lia).
destruct (u8arr_window m OUT (firstn (Z.to_nat (4 * k)) outb) 0 640 A1 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & B2 & C2).
rewrite Z.add_0_r in B2, C2.
apply u8arr_of_rw_cells in B1. apply u8arr_of_rw_cells in B2.
destruct (u8arr_as_f32 m (OUT + 4 * k) _ 160 B1) as (iws & Li & XI).
{ rewrite firstn_length_le; [reflexivity|]. rewrite skipn_length. lia. }
destruct (u8arr_as_f32 m OUT _ 160 B2) as (ows & Lo & XO).
{ rewrite firstn_length_le; [reflexivity|]. rewrite skipn_length. lia. }
exists ows, iws, (skipn (Z.to_nat (0 + 640)) (firstn (Z.to_nat (4 * k)) outb)), (skipn (Z.to_nat (4 * k + 640)) outb).
split; [exact Lo|]. split; [exact Li|]. split; [exact XO|]. split; [exact XI|].
split; [exact C2|]. split; [rewrite skipn_length; lia|].
split; [exact C1|]. rewrite skipn_length. lia.
Qed.

Lemma out_unwindow : forall m OUT k ows iws mid tail,
rw_cells rsegs m OUT (f32 ows) -> length ows = 160%nat ->
u8arr rsegs m (OUT + 640) mid -> Z.of_nat (length mid) = 4 * k - 640 ->
rw_cells rsegs m (OUT + 4 * k) (f32 iws) -> length iws = 160%nat ->
u8arr rsegs m (OUT + 4 * k + 640) tail -> Z.of_nat (length tail) = HOUT_BYTES - 4 * k - 640 ->
exists outb, u8arr rsegs m OUT outb /\ Z.of_nat (length outb) = HOUT_BYTES.
Proof.
intros m OUT k ows iws mid tail XO Lo UM LM XI Li UT LT.
destruct (f32_as_u8arr m OUT ows XO) as [UO LUO]. destruct (f32_as_u8arr m _ iws XI) as [UI LUI].
exists (cells_bytes (f32 ows) ++ mid ++ cells_bytes (f32 iws) ++ tail).
split.
- apply u8arr_join; [exact UO|]. rewrite LUO, Lo. change (Z.of_nat (4 * 160)) with 640.
apply u8arr_join; [exact UM|]. replace (OUT + 640 + Z.of_nat (length mid)) with (OUT + 4 * k) by lia.
apply u8arr_join; [exact UI|]. rewrite LUI, Li. change (Z.of_nat (4 * 160)) with 640. exact UT.
- rewrite !app_length, LUO, LUI, Lo, Li. unfold HOUT_BYTES in *. lia.
Qed.

Lemma stereo_split : forall m STEREO stb,
rw_cells rsegs m STEREO [CB 24 stb] ->
exists sws rest, length sws = 2%nat /\ rw_cells rsegs m STEREO (f32 sws) /\ rw_cells rsegs m (STEREO + 8) [CB 16 rest].
Proof.
intros m STEREO stb X.
pose proof (rw_cells_split_CB rsegs m STEREO [] 24 stb [] [8%nat; 16%nat] X eq_refl) as X2.
cbn [app mk_CB_cells] in X2.
apply (rw_cells_app rsegs m STEREO [CB 8 (firstn 8 stb)]) in X2. destruct X2 as [X8 X16]. cbn [cells_size csize Nat.add] in X16.
destruct (rw_cells_CB_f32 rsegs m STEREO 2 (firstn 8 stb)) as (sws & Ls & XS); [exact X8|].
exists sws, (firstn 16 (skipn 8 stb)). split; [exact Ls|]. split; [exact XS| exact X16].
Qed.

Lemma stereo_join : forall m STEREO sws rest,
rw_cells rsegs m STEREO (f32 sws) -> length sws = 2%nat -> rw_cells rsegs m (STEREO + 8) [CB 16 rest] ->
exists stb, rw_cells rsegs m STEREO [CB 24 stb].
Proof.
intros m STEREO sws rest XS Ls X16.
pose proof (rw_cells_f32_CB rsegs m STEREO sws XS) as X8. rewrite Ls in X8. change (4 * 2)%nat with 8%nat in X8.
assert (X : rw_cells rsegs m STEREO ([CB 8 (cells_bytes (f32 sws))] ++ [CB 16 rest])).
{ apply rw_cells_app. split; [exact X8|]. cbn [cells_size csize Nat.add]. exact X16. }
pose proof (rw_cells_merge rsegs m STEREO [] ([CB 8 (cells_bytes (f32 sws))] ++ [CB 16 rest]) []) as M.
rewrite app_nil_r in M. cbn [app] in M. specialize (M X).
cbn [cells_size csize cells_bytes cbytes Nat.add app] in M. rewrite app_nil_r in M.
eexists. exact M.
Qed.

Definition isv_k (st : nb_state bptr) : Z := match nb_innov_save st with Some k => k | None => 160 end.

Lemma isv_k_ok : forall st, isave_ok (DecNB st) -> 160 <= isv_k st /\ 4 * isv_k st + 640 <= HOUT_BYTES.
Proof.
intros st H. unfold isv_k. cbn in H. destruct (nb_innov_save st) as [k|]; unfold HOUT_BYTES in *; lia.
Qed.

Theorem rdec_nb {RCEIL : RunCeiling} : nb_decode_stmtW -> forall st, rdec_at A_nb_decode (DecNB st).
Proof.
intros NBDEC st. unfold nb_decode_stmtW, nb_decode_stmt in NBDEC. unfold rdec_at. intros until canary.
intros REP DEP ISOK _ ND LAP BRL BR BOK OWN DRANGE DAP UOUT LOUT OUT4 XST ST4 TP SE SS LAY STK LO SPX SP16 MI FRM -> -> ->.
cbn [decst_rep] in REP. destruct REP as [ELBD NREP].
pose proof (isv_k_ok st ISOK) as [K1 K2].
set (k := isv_k st) in *.

assert (BS : rblock_range S NBSTATE_SIZEOF).
{ apply (BRL (nb_blk st, S, NBSTATE_SIZEOF)). rewrite ELBD. left. reflexivity. }
assert (DS : apart Dc (sb_buf_size b) S NBSTATE_SIZEOF).
{ apply (DAP (nb_blk st, S, NBSTATE_SIZEOF)). rewrite ELBD. left. reflexivity. }
first [ sf_destruct 5%nat BS as S0 S16 _ SCE SWIN | sf_fb; destruct BS as (S0 & S16 & _ & SCE & SWIN) ]. first [ sf_destruct 5%nat DRANGE as D0 D16 DSZ0 DCE DWIN | sf_fb; destruct DRANGE as (D0 & D16 & DSZ0 & DCE & DWIN) ].
first [ sf_destruct 10%nat LAY as CB_ CO CS CL ABO ABS AOS ABL AOL ASL | sf_fb; destruct LAY as (CB_ & CO & CS & CL & ABO & ABS & AOS & ABL & AOL & ASL) ].
unfold rdec_depth in LO.
pose proof (u8arr_len_bound _ _ _ UOUT) as [O0 OHI]. rewrite LOUT in OHI.
assert (LAYW : nb_layout S OUT BITS Dc (sb_buf_size b) STEREO (OUT + 4 * k) lo (bv_unsigned sp)).
{ unfold nb_layout, nb_win, apart, NB_GLOBALS_TOP, NBSTATE_SIZEOF, BITS_SIZEOF, HOUT_BYTES in *.
unfold alloc_ceiling in *. unfold apart in DS.
repeat match goal with |- _ /\ _ => split end; try lia. }

first [ pose proof (out_window m OUT outb k UOUT LOUT K1 K2) as sfP_; sf_destruct 12%nat sfP_ as ows iws mid tail Lo Li XO XI UM LM UT LT | sf_fb; destruct (out_window m OUT outb k UOUT LOUT K1 K2) as (ows & iws & mid & tail & Lo & Li & XO & XI & UM & LM & UT & LT) ].
first [ pose proof (stereo_split m STEREO stb XST) as sfP_; sf_destruct 5%nat sfP_ as sws rest Ls XS X16 | sf_fb; destruct (stereo_split m STEREO stb XST) as (sws & rest & Ls & XS & X16) ].
pose proof (nb_tables_of_pristine m TP) as TAB.

cbn [speex_decode speex_decode_n dec_depth].
eapply implM_bind.
{ eapply (X1hv.implM_leaves rsegs).
- apply (nb_decode_leaves2 io_notify st b st0).
- eapply (NBDEC S OUT BITS Dc STEREO (OUT + 4 * k) st b ows iws sws lo canary st0);
try eassumption; try reflexivity.
+ unfold isv_k in *. destruct (nb_innov_save st); [reflexivity| exact I].
+ cbn. unfold alloc_ceiling in SCE. unfold NBSTATE_SIZEOF in *. lia. }
intros [[r st'] b'] s' ms' [POST LEAF]. cbn in LEAF. destruct LEAF as (RR & BSIM & [EBLK EISV]).
first [ sf_destruct 28%nat POST as kk F' fc' m' ows' iws' sws' -> MU WM MI' FRM' FSK STK' NREP' EXC' BR' BOK' XO' Lo' XI' Li' XS' Ls' TAB' SE' SS' -> | sf_fb; destruct POST as (kk & F' & fc' & m' & ows' & iws' & sws' & -> & MU & WM & MI' & FRM' & FSK & STK' & NREP' & EXC' & BR' & BOK' & XO' & Lo' & XI' & Li' & XS' & Ls' & TAB' & SE' & SS' & ->) ].
apply implM_ret. apply evt_done.

assert (UM' : u8arr rsegs m' (OUT + 640) mid).
{ eapply u8arr_transport; [exact UM| exact MU| exact WM|].
unfold nb_W. cbn. clear - LM K1 K2 AOL SCE CO ABO AOS. unfold NBSTATE_SIZEOF, BITS_SIZEOF, NB_RSTDERR, alloc_ceiling, HOUT_BYTES, apart in *.
repeat match goal with |- _ /\ _ => split end; lia. }
assert (UT' : u8arr rsegs m' (OUT + 4 * k + 640) tail).
{ eapply u8arr_transport; [exact UT| exact MU| exact WM|].
unfold nb_W. cbn. clear - LT K1 K2 AOL SCE CO ABO AOS. unfold NBSTATE_SIZEOF, BITS_SIZEOF, NB_RSTDERR, alloc_ceiling, HOUT_BYTES, apart in *.
repeat match goal with |- _ /\ _ => split end; lia. }
assert (X16' : rw_cells rsegs m' (STEREO + 8) [CB 16 rest]).
{ eapply rw_cells_munch_out; [exact X16| exact MU| exact WM|].
unfold nb_W. cbn. clear - K1 K2 ASL SCE CS AOS ABS. unfold NBSTATE_SIZEOF, BITS_SIZEOF, NB_RSTDERR, alloc_ceiling, HOUT_BYTES, apart in *.
repeat match goal with |- _ /\ _ => split end; lia. }
destruct (out_unwindow m' OUT k ows' iws' mid tail XO' Lo' UM' LM XI' Li' UT' LT) as (outb' & UOUT' & LOUT').
destruct (stereo_join m' STEREO sws' rest XS' Ls' X16') as (stb' & XST').
destruct kk as [kt0 kt1 kt2 ka1 ka2 ka3 ka4 ka5 ka6 ka7 kt3 kt4 kt5 kt6]. unfold callR. cbn [c_t0 c_t1 c_t2 c_a1 c_a2 c_a3 c_a4 c_a5 c_a6 c_a7 c_t3 c_t4 c_t5 c_t6].
unfold rdec_post.
first [ unshelve sf_eexists 19%nat; [ exact (kt0) | exact (kt1) | exact (kt2) | exact (ka1) | exact (ka2) | exact (ka3) | exact (ka4) | exact (ka5) | exact (ka6) | exact (ka7) | exact (kt3) | exact (kt4) | exact (kt5) | exact (kt6) | exact (F') | exact (fc') | exact (m') | exact (outb') | exact (stb') | ] | sf_fb; exists kt0, kt1, kt2, ka1, ka2, ka3, ka4, ka5, ka6, ka7, kt3, kt4, kt5, kt6, F', fc', m', outb', stb' ].
split; [reflexivity|]. split; [exact RR|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|].
split; [exact FRM'|].
split. { eapply munch_weaken_to; [exact MU|]. intros x Hx. unfold sbW, blocks_ivs in Hx. rewrite ELBD in Hx. cbn in Hx.
unfold nb_W. cbn. clear - Hx K1 K2. first [ sf_destruct 7%nat Hx as W0 W1 W2 W3 W4 W5 _ | sf_fb; destruct Hx as (W0 & W1 & W2 & W3 & W4 & W5 & _) ].
unfold HOUT_BYTES, NB_RSTDERR in *.
split; [exact W0|]. split; [exact W5|]. split; [intros C; apply W2; lia|]. split; [intros C; apply W2; lia|].
split; [exact W1|]. split; [intros C; apply W3; lia|]. split; [exact W4| exact I]. }
split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
split. { cbn [decst_rep]. split; [rewrite EBLK; exact ELBD| exact NREP']. }
split; [exact EXC'|].
split; [exact BR'|]. split; [exact BOK'|].
destruct BSIM as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
split; [exact UOUT'|]. split; [exact LOUT'|]. split; [exact XST'|].
split; [exact SE'|]. split; [exact SS'|]. reflexivity.
Qed.
