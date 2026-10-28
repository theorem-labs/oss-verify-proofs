(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.

Lemma combine_app1 {A B} : forall (l1 : list A) (l2 : list B) a b,
length l1 = length l2 -> combine (l1 ++ [a]) (l2 ++ [b]) = combine l1 l2 ++ [(a, b)].
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] a b L; cbn in *; try discriminate; [reflexivity|].
rewrite IH by lia. reflexivity.
Qed.

Lemma after_last_nl_snoc : forall s c,
after_last_nl (s ++ [c]) = if c =? 10 then zlength s + 1 else after_last_nl s.
Proof.
intros s c. unfold after_last_nl. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, seq_S, map_app. cbn [map].
rewrite combine_app1 by (rewrite length_map, length_seq; reflexivity).
rewrite fold_left_app. cbn [fold_left fst snd]. unfold zlength. rewrite Nat.add_0_l. destruct (c =? 10); reflexivity.
Qed.

Lemma after_last_nl_nil : after_last_nl [] = 0.
Proof. reflexivity. Qed.

Lemma after_last_nl_app_nonl : forall s t, ~ In 10 t -> after_last_nl (s ++ t) = after_last_nl s.
Proof.
intros s t. induction t as [|c t IH] using rev_ind; intros NI.
- rewrite app_nil_r. reflexivity.
- rewrite app_assoc, after_last_nl_snoc. rewrite in_app_iff in NI. cbn in NI.
destruct (Z.eqb_spec c 10); [exfalso; apply NI; right; left; lia|]. apply IH. intros H; apply NI; left; exact H.
Qed.

Lemma after_last_nl_found : forall s t, ~ In 10 t -> after_last_nl (s ++ 10 :: t) = zlength s + 1.
Proof.
intros s t NI. change (s ++ 10 :: t) with (s ++ [10] ++ t). rewrite app_assoc, after_last_nl_app_nonl by exact NI.
rewrite after_last_nl_snoc. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma after_last_nl_range : forall s, 0 <= after_last_nl s <= zlength s.
Proof.
induction s as [|c s IH] using rev_ind. { rewrite after_last_nl_nil. unfold zlength. cbn. lia. }
rewrite after_last_nl_snoc. unfold zlength in *. rewrite length_app. cbn [length]. destruct (c =? 10); lia.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bs X1c2 X1bn X1cc X1c8 X1c0.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qx.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gj X1fl X1ei X1ea X1fr X1gg X1eo X1gh.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1en.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0pt.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c4.
Local Ltac plia_gen stock ::= plia_size stock.
Import X1bs.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_to_bytes : forall l, zb l = to_bytes l.
Proof. reflexivity. Qed.
Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. intros. unfold zb. rewrite firstn_map. reflexivity. Qed.
Lemma zb_skipn : forall n l, zb (skipn n l) = skipn n (zb l).
Proof. intros. unfold zb. rewrite skipn_map. reflexivity. Qed.

Lemma split_at_znth : forall (cs : list Z) i, 0 <= i < zlength cs ->
cs = firstn (Z.to_nat i) cs ++ znth cs i :: skipn (Z.to_nat (i + 1)) cs.
Proof.
intros cs i Hi. unfold zlength in Hi.
rewrite <- (firstn_skipn (Z.to_nat i) cs) at 1. f_equal.
replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by lia. rewrite <- skipn_skipn.
unfold znth. destruct (Z.ltb_spec i 0); [lia|].
rewrite <- (Nat.add_0_r (Z.to_nat i)) at 2. rewrite <- (nth_skipn _ cs 0 0%Z).
destruct (skipn (Z.to_nat i) cs) as [|c rest] eqn:E.
- exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
- reflexivity.
Qed.

Section Scan.
Context {RCEIL : RunCeiling}.
Variables (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Variables (wpos S l : Z) (bs : list Z).
Variable POST : machine_state -> Prop.
Hypothesis SRC : bytes_at rsegs m S (zb bs).
Hypothesis LEN : zlength bs = l.
Hypothesis BYT : Forall (fun c => 0 <= c < 256) bs.
Hypothesis L1 : 1 <= l.
Hypothesis LHI : l < 2^62.

Definition scan_st (k : Z) (a3 : word) : machine_state :=
MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
(Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34d9c) fc None m (seg_rom rsegs).

Hypothesis NF : forall a3,
after_last_nl bs = 0 ->
evt rsegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
(Z_to_bv 64 (-1 - l)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 l) (Z_to_bv 64 (S + l))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34db4) fc None m (seg_rom rsegs)).

Hypothesis FD : forall k a3,
0 <= k < l -> after_last_nl bs = l - k ->
evt rsegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
(Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34dd8) fc None m (seg_rom rsegs)).

#[using="SRC LEN BYT L1 LHI NF FD"] Lemma scan_loop : forall (n : nat) k a3,
Z.of_nat n = l - k -> 0 <= k < l ->
~ In 10 (skipn (Z.to_nat (l - k)) bs) ->
evt rsegs POST (scan_st k a3).
Proof.
induction n as [|n IH]; intros k a3 Hn Hk NI; [lia|].
unfold scan_st.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS. unfold zlength in LEN.
assert (RD : ov_read_bytes rsegs m (wa (S + (l - 1 - k))) 1 = Some [Z_to_bv 8 (znth bs (l - 1 - k))]).
{ rewrite (bytes_at_read rsegs m S (zb bs) (l - 1 - k) 1 SRC) by (rewrite ?zb_length; lia).
f_equal. unfold zb. rewrite skipn_map, firstn_map. unfold znth.
destruct (Z.ltb_spec (l - 1 - k) 0); [lia|].
destruct (skipn (Z.to_nat (l - 1 - k)) bs) as [|c rest] eqn:E.
- exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
- cbn [firstn map]. f_equal. f_equal. rewrite <- (Nat.add_0_r (Z.to_nat (l - 1 - k))), <- (nth_skipn _ bs 0 0%Z), E. reflexivity. }
pose proof (proj1 (List.Forall_forall _ _) BYT) as BYT'.
assert (CR : 0 <= znth bs (l - 1 - k) < 256).
{ unfold znth. destruct (Z.ltb_spec (l - 1 - k) 0); [lia|]. apply BYT'. apply nth_In. lia. }
pose proof (split_at_znth bs (l - 1 - k) ltac:(unfold zlength; lia)) as SPL.
replace (l - 1 - k + 1) with (l - k) in SPL by lia.
step.
replace (Z_to_bv 64 (S + l + (-1 - k)) : word) with (wa (S + (l - 1 - k))) by (unfold wa; f_equal; lia).
step.
unfold zxb. rewrite (X0pt.unsigned_lit8 _ CR).
step. if_cases Hnl; zify_cond Hnl.
-   apply FD; [lia|].
rewrite Hnl in SPL. rewrite SPL at 1. rewrite after_last_nl_found by exact NI.
unfold zlength. rewrite length_firstn. lia.
- step. step. step.
if_cases Hend; zify_cond Hend.
+
replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - (k + 1)) : word) by (f_equal; lia).
apply (IH (k + 1)).
{ clear - Hn. lia. }
{ clear - Hk Hend. lia. }
{ replace (Z.to_nat (l - (k + 1))) with (Z.to_nat (l - 1 - k)) by (clear - Hk; lia).
rewrite SPL at 1. rewrite skipn_app. rewrite skipn_firstn_comm, Nat.sub_diag, firstn_O, length_firstn.
replace (Z.to_nat (l - 1 - k) - Nat.min (Z.to_nat (l - 1 - k)) (length bs))%nat with 0%nat by (clear - Hk LEN; lia).
cbn [skipn app]. intros [H|H]; [clear - H Hnl; lia| exact (NI H)]. }
+
replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - l) : word) by (f_equal; clear - Hend; lia).
replace (Z_to_bv 64 (k + 1) : word) with (Z_to_bv 64 l : word) by (f_equal; exact Hend).
apply NF.
rewrite <- (app_nil_l bs). rewrite after_last_nl_app_nonl; [reflexivity|].
rewrite SPL at 1. replace (Z.to_nat (l - 1 - k)) with 0%nat by (clear - Hend Hk; lia). cbn [firstn app].
intros [H|H]; [clear - H Hnl; lia | exact (NI H)].
Qed.
End Scan.

Lemma zbv_sub_wrap : forall e k, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e) - k) = Z_to_bv 64 (e - k).
Proof.
intros e k. apply X1cf.Z_to_bv_eqm. rewrite unsigned_lit_wrap. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

Lemma CB_prefix_bytes_at : forall m A n (bb : list byte) (p : list byte),
rw_cells rsegs m A [CB n bb] -> firstn (length p) bb = p -> bytes_at rsegs m A p.
Proof.
intros m A n bb p H E.
pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
rewrite <- E. rewrite <- (firstn_skipn (length p) bb) in B.
exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)).
Qed.

Theorem fwritex_stdout_proof : fwritex_stdout_stmt.
Proof.
unfold fwritex_stdout_stmt, out_stmt. intros St get_so set_so GS SS. intros until canary.
intros SINK SRC BYT BSL -> -> ST LO GLO SPHI TOP SSP MI SEPF SEPB SEPS1 SEPS2 SEPS3.
first [ sf_destruct 10%nat SINK as ACT flags mode tail bufbytes FC FL104 BUF BUFP BUFL | sf_fb; destruct SINK as (ACT & flags & mode & tail & bufbytes & FC & FL104 & BUF & BUFP & BUFL) ].
unfold OUT_DEPTH, GLOBALS_TOP, STDOUT_BUFSIZ in *.
change X1ff.rsegs with rsegs in *.
pose proof SSP as SSP0.
destruct SSP as [GOT GUARD]. change X1fd.rsegs with rsegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS.
assert (LSB : length (zb bs) = length bs) by apply zb_length.
pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0.
remember (get_so st) as so eqn:ESO.
set (buf := so_buf so) in *.
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
assert (LS : 0 <= zlength bs) by (unfold zlength; lia).
pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
assert (LBB : length bufbytes = 1024%nat) by (destruct BUF as [[WF _] _]; cbn in WF; exact (proj1 WF)).
assert (LTB : length (to_bytes buf) = length buf) by (unfold to_bytes; apply length_map).
set (S := bv_unsigned a0) in *.
assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
assert (FL64 : Z.land (bv_unsigned flags) 64 = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec i 6) as [->|NE].
- pose proof (f_equal (fun z => Z.testbit z 6) FL104) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
change (Z.testbit 64 6) with true in T |- *. change (Z.testbit 104 6) with true in T. exact T.
- change 64 with (2^6). rewrite Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec 6 i); [lia|]. apply Bool.andb_false_r. }
assert (BUFB : bytes_at rsegs m RSTDOUT_BUF (to_bytes buf)).
{ eapply CB_prefix_bytes_at; [exact BUF|]. rewrite LTB. exact BUFP. }
unfold zlength in *. unfold file_cells in FC.
unfold stdout_fwritex, stdout_towrite.
apply (implM_updso rsegs get_so set_so). rewrite <- ESO, ACT.
apply (implM_rdso rsegs get_so). rewrite GS.
set (st1 := set_so so st).
assert (ESO1 : get_so st1 = so) by (unfold st1; apply GS).
change (so_buf so) with buf. unfold STDOUT_BUFSIZ. cbv beta. unfold zlength.
destruct (1024 - Z.of_nat (length buf) <? Z.of_nat (length bs)) eqn:CMP.
-
pose proof (proj1 (Z.ltb_lt _ _) CMP) as CMP'.
eapply implM_evt.
{ eapply fwx_nofit with (lo := lo); [exact FC | exact EA0 | reflexivity | reflexivity | lia | lia | lia | lia
| destruct (so_first so); lia | destruct (so_first so); reflexivity | exact ST | lia | lia | exact MI | lia]. }
cbv beta. intros ms1 PO.
first [ sf_destruct 17%nat PO as t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 -> MU1 WM1 MI1 ST1 | sf_fb; destruct PO as (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1) ].
transport_after_call rsegs m m1 MU1 WM1.
replace (Z_to_bv 64 (if so_first so then 217340 else 216932) : word) with (Z_to_bv 64 (wfn_of (get_so st1)) : word)
by (rewrite ESO1; reflexivity).
eapply implM_mono.
{ eapply (stdout_writefn_spec get_so set_so GS SS) with (lo := lo) (S := S) (flags := flags) (mode := mode) (tail := tail) (canary := canary);
[ rewrite ESO1; exact ACT
| unfold stdout_cells, wfn_of, lbf_of, file_cells; rewrite ESO1; exact FC
| exact FL64
| rewrite ESO1; exact BUFB
| rewrite ESO1; unfold zlength; exact BUFL
| rewrite <- zb_to_bytes; exact SRC
| reflexivity | reflexivity | reflexivity
| exact ST1 | unfold STDOUT_WRITE_DEPTH; lia | lia
| split; [exact GOT | exact GUARD] | exact MI1
| unfold zlength; lia | lia | unfold zlength; lia
| right; unfold zlength; split; lia
| intros ->; cbn [length Z.of_nat] in CMP'; lia ]. }
cbv beta. intros [] st' ms' PO.
first [ sf_destruct 23%nat PO as t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m2 -> MU2 WM2 MI2 ST2 FC2 SSP2 -> | sf_fb; destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->) ].
unfold STDOUT_WRITE_DEPTH in MU2.
rewrite ESO1 in FC2 |- *.
pose proof (rw_cells_transport rsegs _ m1 m2 _ _ BUF MU2 WM2 ltac:(cbn; lia)) as BUF2.
pose proof (bytes_at_transport rsegs _ m1 m2 _ _ SRC MU2 ltac:(cbn; rewrite LSB; lia)) as SRC2.
unfold out_post, SR. sf_eexists 16%nat. split; [reflexivity|].
split. { apply (munch_trans _ m m1 m2).
- eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
- eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [eapply wmono_trans; [exact WM1 | exact WM2] |]. split; [exact MI2|]. split; [exact ST2|].
split.
{
unfold SINK_stdout. rewrite GS. split; [reflexivity|].
first [ unshelve sf_eexists 4%nat; [ exact (flags) | exact (mode) | exact (tail) | exact (bufbytes) | ] | sf_fb; exists flags, mode, tail, bufbytes ].
split; [unfold stdout_cells, wfn_of, lbf_of in FC2; cbn [so_after so_buf so_first so_lbf_nl] in FC2; exact FC2|].
split; [exact FL104|]. split; [exact BUF2|]. split; [reflexivity|]. unfold zlength; cbn; lia. }
split; [exact SSP2 | exact SRC2].
- pose proof (proj1 (Z.ltb_ge _ _) CMP) as CMP'.

pose proof BUF as BUF0.
apply (rw_cells_split_CB rsegs _ _ [] 1024 bufbytes [] [length buf; 1024 - length buf]%nat) in BUF; [| cbn; lia].
cbn [mk_CB_cells app] in BUF. rewrite BUFP in BUF.
apply (proj1 (X1en.rw_cells_app rsegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite firstn_all2 in BUFb by (rewrite length_skipn; lia).
destruct (so_lbf_nl so) eqn:LBF.
2: {
apply implM_upd. cbv beta. rewrite ESO1. unfold st1. rewrite SS.
eapply evt_mono.
{ eapply (fwx_fit_plain ra sp gp tp t0 t1 t2 s0 s1 a0) with (lo := lo) (cap := (1024 - length buf)%nat) (src := zb bs) (S := S)
(Fp := RSTDOUT) (wend := RSTDOUT_BUF + 1024) (wpos := RSTDOUT_BUF + Z.of_nat (length buf)) (junk := skipn (length buf) bufbytes);
[ exact FC | exact BUFb | lia | exact SRC | rewrite LSB; reflexivity | exact EA0 | reflexivity | reflexivity | try lia .. ];
[exact ST | exact MI]. }
cbv beta. intros ms' PO.
first [ sf_destruct 23%nat PO as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MU2 WM2 MI2 ST2 FC2 DST2 SRC2 | sf_fb; destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2) ].
unfold out_post, SR. sf_eexists 16%nat.
split. { reflexivity. }
split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
assert (GOT2 : rw_cells rsegs m2 245968 [C8 (Z_to_bv 64 448184)]).
{ eapply (rw_cells_transport rsegs _ m m2); [exact GOT | exact MU2 | exact WM2 | cbn; lia]. }
assert (GUARD2 : rw_cells rsegs m2 448184 [C8 canary]).
{ eapply (rw_cells_transport rsegs _ m m2); [exact GUARD | exact MU2 | exact WM2 | cbn; lia]. }
assert (BUFa2 : rw_cells rsegs m2 RSTDOUT_BUF [CB (length buf) (to_bytes buf)]).
{ eapply (rw_cells_transport rsegs _ m m2); [exact BUFa | exact MU2 | exact WM2 | cbn; lia]. }
split.
{
unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [exact ACT|].
first [ unshelve sf_eexists 4%nat; [ exact (flags) | exact (mode) | exact (tail) | exact ((to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes))) | ] | sf_fb; exists flags, mode, tail, (to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes)) ].
split. { unfold zlength, file_cells. change (so_buf so) with buf. rewrite length_app, Nat2Z.inj_add, Z.add_assoc, LBF. exact FC2. }
split; [exact FL104|].
split.
{ assert (J : rw_cells rsegs m2 RSTDOUT_BUF ([] ++ [CB (length buf) (to_bytes buf); CB (length (zb bs)) (zb bs); CB (1024 - length buf - length (zb bs))%nat (skipn (length (zb bs)) (skipn (length buf) bufbytes))] ++ [])).
{ cbn [app]. apply (proj2 (X1en.rw_cells_app rsegs _ _ [_] _)); split; [exact BUFa2|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
rewrite LSB in J |- *.
replace (length buf + (length bs + (1024 - length buf - length bs + 0)))%nat with 1024%nat in J by lia. exact J. }
split.
{ change (so_buf so) with buf. rewrite length_app, app_assoc, firstn_app, length_app, LTB, LSB, Nat.sub_diag, firstn_O, app_nil_r.
rewrite firstn_all2 by (rewrite length_app, LTB, LSB; lia). unfold to_bytes, zb. rewrite map_app. reflexivity. }
change (so_buf so) with buf. unfold zlength. rewrite length_app. lia. }
split; [split; [exact GOT2 | exact GUARD2] | exact SRC2]. }

pose proof (after_last_nl_range bs) as IR. unfold zlength in IR.
pose proof BUFa as BUFam. change (rw_cells rsegs m RSTDOUT_BUF [CB (length buf) (to_bytes buf)]) with (boxed (rw_cells rsegs m RSTDOUT_BUF [CB (length buf) (to_bytes buf)])) in BUFam.
destruct (0 <? after_last_nl bs) eqn:CI.
2: {
pose proof (proj1 (Z.ltb_ge _ _) CI) as CI'.
apply implM_retb. apply implM_upd. cbv beta. rewrite ESO1. unfold st1. rewrite SS.
replace (after_last_nl bs) with 0 by (clear - CI' IR; lia). change (skipn (Z.to_nat 0) bs) with bs.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT + 40, RSTDOUT + 48); (RSTDOUT_BUF + Z.of_nat (length buf), RSTDOUT_BUF + Z.of_nat (length buf) + Z.of_nat (length bs))] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
rewrite EA0.
carve_frame 64%nat ST.
do 13 step.
if_cases Hw; zify_cond Hw. 1:{ exfalso. clear - Hw. lia. }
do 3 step.
if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. clear - Hr CMP'. lia. }
do 3 step.
if_cases Hl; zify_cond Hl.
1:{ exfalso. clear - Hl. replace (bv_unsigned (sx32 (Z_to_bv 64 10))) with 10 in Hl by reflexivity. lia. }
step. if_cases Hz; zify_cond Hz.
1:{
eapply evt_mono.
{ eapply fwx_tail with (lo := lo) (cap := (1024 - length buf)%nat) (src := zb bs) (i := 0) (m0 := m);
[ exact FR | exact FC | exact BUFb | clear - LSB CMP'; lia | exact SRC | rewrite LSB; reflexivity | exact ST
| clear - LO GLO; lia | exact SPHI | exact MU | exact WM | exact MI
| try (cbn in RA0; clear - RA0 Hz LSB CMP' BUFL LZ LS SEPF SEPB SEPS1 SEPS2 SEPS3 BS GLO LO SPHI; lia) .. ]. }
cbv beta. intros ms' PO.
first [ sf_destruct 23%nat PO as t0' t1' t2' a1' a2' a3'' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MU2 WM2 MI2 ST2 FC2 DST2 SRC2 | sf_fb; destruct PO as (t0' & t1' & t2' & a1' & a2' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2) ].
unfold out_post, SR. sf_eexists 16%nat.
split. { reflexivity. }
split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
destruct SSP0 as [GOTm GUARDm]. change X1fd.rsegs with rsegs in GOTm, GUARDm. unfold got_ssp, ssp_guard in GOTm, GUARDm.
assert (GOT2 : rw_cells rsegs m2 245968 [C8 (Z_to_bv 64 448184)]).
{ eapply (rw_cells_transport rsegs _ m m2); [exact GOTm | exact MU2 | exact WM2 | cbn; lia]. }
assert (GUARD2 : rw_cells rsegs m2 448184 [C8 canary]).
{ eapply (rw_cells_transport rsegs _ m m2); [exact GUARDm | exact MU2 | exact WM2 | cbn; lia]. }
assert (BUFa2 : rw_cells rsegs m2 RSTDOUT_BUF [CB (length buf) (to_bytes buf)]).
{ unfold boxed in BUFam. eapply (rw_cells_transport rsegs _ m m2); [exact BUFam | exact MU2 | exact WM2 | cbn; lia]. }
split.
{
unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [exact ACT|].
first [ unshelve sf_eexists 4%nat; [ exact (flags) | exact (mode) | exact (tail) | exact ((to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes))) | ] | sf_fb; exists flags, mode, tail, (to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes)) ].
split. { unfold zlength, file_cells. change (so_buf so) with buf. rewrite length_app, Nat2Z.inj_add, Z.add_assoc, LBF. exact FC2. }
split; [exact FL104|].
split.
{ assert (J : rw_cells rsegs m2 RSTDOUT_BUF ([] ++ [CB (length buf) (to_bytes buf); CB (length (zb bs)) (zb bs); CB (1024 - length buf - length (zb bs))%nat (skipn (length (zb bs)) (skipn (length buf) bufbytes))] ++ [])).
{ cbn [app]. apply (proj2 (X1en.rw_cells_app rsegs _ _ [_] _)); split; [exact BUFa2|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
rewrite LSB in J |- *.
replace (length buf + (length bs + (1024 - length buf - length bs + 0)))%nat with 1024%nat in J by lia. exact J. }
split.
{ change (so_buf so) with buf. rewrite length_app, app_assoc, firstn_app, length_app, LTB, LSB, Nat.sub_diag, firstn_O, app_nil_r.
rewrite firstn_all2 by (rewrite length_app, LTB, LSB; lia). unfold to_bytes, zb. rewrite map_app. reflexivity. }
change (so_buf so) with buf. unfold zlength. rewrite length_app. clear - CMP' LZ Hz. lia. }
split; [split; [exact GOT2 | exact GUARD2] | exact SRC2]. }

do 4 step.
replace (Z_to_bv 64 (-1) : word) with (Z_to_bv 64 (-1 - 0) : word) by reflexivity.
eapply (scan_loop _ sp) with (bs := bs) (n := length bs);
[ exact SRC | reflexivity | exact BYT | clear - Hz LS; lia | clear - BSL; lia | | | clear - Hz; lia | clear - Hz LS; lia | ].
3:{ rewrite Z.sub_0_r, Nat2Z.id, skipn_all. intros H; exact H. }
2:{ intros k a3x Hk Hanl. exfalso. clear - Hk Hanl CI'. lia. }
cbv beta. intros a3x _.
step. step.
eapply evt_mono.
{ eapply fwx_tail with (lo := lo) (cap := (1024 - length buf)%nat) (src := zb bs) (i := 0) (m0 := m);
[ exact FR | exact FC | exact BUFb | clear - LSB CMP'; lia | exact SRC | rewrite LSB; reflexivity | exact ST
| clear - LO GLO; lia | exact SPHI | exact MU | exact WM | exact MI
| try (cbn in RA0; clear - RA0 Hz LSB CMP' BUFL LZ LS SEPF SEPB SEPS1 SEPS2 SEPS3 BS GLO LO SPHI; lia) .. ]. }
cbv beta. intros ms' PO.
first [ sf_destruct 23%nat PO as t0' t1' t2' a1' a2' a3'' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MU2 WM2 MI2 ST2 FC2 DST2 SRC2 | sf_fb; destruct PO as (t0' & t1' & t2' & a1' & a2' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2) ].
unfold out_post, SR. sf_eexists 16%nat.
split. { reflexivity. }
split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
destruct SSP0 as [GOTm GUARDm]. change X1fd.rsegs with rsegs in GOTm, GUARDm. unfold got_ssp, ssp_guard in GOTm, GUARDm.
assert (GOT2 : rw_cells rsegs m2 245968 [C8 (Z_to_bv 64 448184)]).
{ eapply (rw_cells_transport rsegs _ m m2); [exact GOTm | exact MU2 | exact WM2 | cbn; lia]. }
assert (GUARD2 : rw_cells rsegs m2 448184 [C8 canary]).
{ eapply (rw_cells_transport rsegs _ m m2); [exact GUARDm | exact MU2 | exact WM2 | cbn; lia]. }
assert (BUFa2 : rw_cells rsegs m2 RSTDOUT_BUF [CB (length buf) (to_bytes buf)]).
{ unfold boxed in BUFam. eapply (rw_cells_transport rsegs _ m m2); [exact BUFam | exact MU2 | exact WM2 | cbn; lia]. }
split.
{
unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [exact ACT|].
first [ unshelve sf_eexists 4%nat; [ exact (flags) | exact (mode) | exact (tail) | exact ((to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes))) | ] | sf_fb; exists flags, mode, tail, (to_bytes buf ++ zb bs ++ skipn (length (zb bs)) (skipn (length buf) bufbytes)) ].
split. { unfold zlength, file_cells. change (so_buf so) with buf. rewrite length_app, Nat2Z.inj_add, Z.add_assoc, LBF. exact FC2. }
split; [exact FL104|].
split.
{ assert (J : rw_cells rsegs m2 RSTDOUT_BUF ([] ++ [CB (length buf) (to_bytes buf); CB (length (zb bs)) (zb bs); CB (1024 - length buf - length (zb bs))%nat (skipn (length (zb bs)) (skipn (length buf) bufbytes))] ++ [])).
{ cbn [app]. apply (proj2 (X1en.rw_cells_app rsegs _ _ [_] _)); split; [exact BUFa2|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
rewrite LSB in J |- *.
replace (length buf + (length bs + (1024 - length buf - length bs + 0)))%nat with 1024%nat in J by lia. exact J. }
split.
{ change (so_buf so) with buf. rewrite length_app, app_assoc, firstn_app, length_app, LTB, LSB, Nat.sub_diag, firstn_O, app_nil_r.
rewrite firstn_all2 by (rewrite length_app, LTB, LSB; lia). unfold to_bytes, zb. rewrite map_app. reflexivity. }
change (so_buf so) with buf. unfold zlength. rewrite length_app. clear - CMP' LZ. lia. }
split; [split; [exact GOT2 | exact GUARD2] | exact SRC2]. }

pose proof (proj1 (Z.ltb_lt _ _) CI) as CI'.
set (i := after_last_nl bs) in *.
eapply (implM_evt rsegs) with (P := fun ms1 => exists (k : Z) (a3x : word) (j8 : list byte) (m1 : mem),
0 <= k < Z.of_nat (length bs) /\ i = Z.of_nat (length bs) - k /\
ms1 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RSTDOUT) (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 (RSTDOUT_BUF + Z.of_nat (length buf)))
(Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3x a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + Z.of_nat (length bs)))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34dd8) fc None m1 (seg_rom rsegs) /\
rw_cells rsegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
stk rsegs m1 lo (bv_unsigned sp + -64)).
{ pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
rewrite EA0.
carve_frame 64%nat ST.
do 13 step.
if_cases Hw; zify_cond Hw. 1:{ exfalso. clear - Hw. lia. }
do 3 step.
if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. clear - Hr CMP'. lia. }
do 3 step.
if_cases Hl; zify_cond Hl.
1:{ exfalso. clear - Hl. replace (bv_unsigned (sx32 (Z_to_bv 64 10))) with 10 in Hl by reflexivity. lia. }
step. if_cases Hz; zify_cond Hz.
1:{ exfalso. clear - Hz CI' IR. lia. }
do 4 step.
replace (Z_to_bv 64 (-1) : word) with (Z_to_bv 64 (-1 - 0) : word) by reflexivity.
eapply (scan_loop _ sp) with (bs := bs) (n := length bs);
[ exact SRC | reflexivity | exact BYT | clear - Hz LS; lia | clear - BSL; lia | | | clear - Hz; lia | clear - Hz LS; lia | ].
3:{ rewrite Z.sub_0_r, Nat2Z.id, skipn_all. intros H; exact H. }
1:{ intros a3x Hanl. exfalso. clear - Hanl CI'. subst i. lia. }
cbv beta. intros k a3x Hk Hanl.
apply evt_done. exists k, a3x. eexists. exists m0.
split; [exact Hk|]. split; [subst i; exact Hanl|]. split; [reflexivity|].
split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact ST. }
intros ms1 sfH_; first [ sf_destruct 12%nat sfH_ as k a3x j8 m1 Hk Hik -> FR1 MU1 WM1 MI1 ST1 | sf_fb; destruct sfH_ as (k & a3x & j8 & m1 & Hk & Hik & -> & FR1 & MU1 & WM1 & MI1 & ST1) ].
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO; lia).
transport_after_call rsegs m m1 MU1 WM1.
eapply (implM_evt rsegs). 2:{ intros ms' H; exact H. } cbv beta.
do 5 step. step.
rewrite ?zbv_sub_wrap. rewrite ?(unsigned_lit k) by (clear - Hk BSL; lia).
try rewrite (Z.add_opp_r (Z.of_nat (length bs)) k).
assert (LFI : zlength (firstn (Z.to_nat i) bs) = Z.of_nat (length bs) - k).
{ unfold zlength. rewrite length_firstn. clear - Hk Hik IR. lia. }
rewrite <- LFI.
rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
replace (Z_to_bv 64 (if so_first so then 217340 else 216932) : word) with (Z_to_bv 64 (wfn_of (get_so st1)) : word)
by (rewrite ESO1; reflexivity).
assert (SRCa : bytes_at rsegs m1 S (to_bytes (firstn (Z.to_nat i) bs))).
{ rewrite <- (firstn_skipn (Z.to_nat i) bs), zb_app in SRC. exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) SRC)). }
apply evt_done.
eapply implM_bind.
{ eapply (stdout_writefn_spec get_so set_so GS SS) with (lo := lo) (S := S) (flags := flags) (mode := mode) (tail := tail) (canary := canary);
[ rewrite ESO1; exact ACT
| unfold stdout_cells, wfn_of, lbf_of, file_cells; rewrite ESO1, LBF; exact FC
| exact FL64
| rewrite ESO1; exact BUFB
| rewrite ESO1; unfold zlength; exact BUFL
| exact SRCa
| reflexivity | reflexivity | reflexivity
| rewrite ESP; exact ST1 | rewrite ESP; unfold STDOUT_WRITE_DEPTH; clear - LO; lia | exact GLO
| split; [exact GOT | exact GUARD] | exact MI1
| clear - LFI BSL Hk; lia | cbn in RA0; clear - RA0; lia | clear - LFI BS Hk; lia
| right; rewrite ESP; clear - LFI Hk SEPS1 SEPS2; split; lia
| intros E; exfalso; rewrite E in LFI; unfold zlength in LFI; cbn [length Z.of_nat] in LFI; lia ]. }
cbv beta. intros [] st2 ms2 PO2.
first [ sf_destruct 23%nat PO2 as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MU2 WM2 MI2 ST2 FC2 SSP2 -> | sf_fb; destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->) ].
unfold STDOUT_WRITE_DEPTH in MU2.
rewrite ESP in MU2, ST2. rewrite ESO1 in FC2 |- *.
apply implM_upd. cbv beta. rewrite GS. unfold st1. rewrite !SS. cbn [so_active so_buf so_lbf_nl so_first so_after].
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply (rw_cells_transport rsegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn; clear - LO GLO RSP; lia]. }
assert (BUF2 : rw_cells rsegs m2 RSTDOUT_BUF [CB 1024 bufbytes]).
{ eapply (rw_cells_transport rsegs _ m1 m2); [exact BUF0 | exact MU2 | exact WM2 | cbn; clear - GLO LO; lia]. }
assert (SRC2 : bytes_at rsegs m2 S (zb bs)).
{ eapply (bytes_at_transport rsegs _ m1 m2); [exact SRC | exact MU2 | cbn; rewrite LSB; clear - SEPS1 SEPS2 GLO LO; lia]. }
clear FR1 BUF0 SRC SRCa BUFa BUFb BUFB FC GOT GUARD.
unfold stdout_cells, file_cells, wfn_of, lbf_of in FC2. cbn [so_active so_buf so_lbf_nl so_first so_after zlength length Z.of_nat] in FC2.
rewrite Z.add_0_r, LBF in FC2.
rewrite (ret_pc_even 216560) by (cbn; lia).
step. if_cases Hn; zify_cond Hn. 1:{ exfalso. clear - Hn. lia. }
step. step. step.
rewrite ?zbv_sub_wrap. rewrite ?(unsigned_lit k) by (clear - Hk BSL; lia).
try rewrite (Z.add_opp_r (S + Z.of_nat (length bs)) k).
set (S2 := (S + Z.of_nat (length bs) - k) mod 2^64).
replace (Z_to_bv 64 (S + Z.of_nat (length bs) - k) : word) with (Z_to_bv 64 S2 : word) by (subst S2; apply X1cf.Z_to_bv_mod64).
assert (HS2 : 0 <= S2 < 2^64) by (subst S2; apply Z.mod_pos_bound; reflexivity).
assert (HS2c : S2 = S + Z.of_nat (length bs) - k \/ (S2 = 0 /\ k = 0 /\ S + Z.of_nat (length bs) = 2^64)).
{ subst S2. cbn in RA0. destruct (Z.eq_dec (S + Z.of_nat (length bs) - k) (2^64)) as [E|E].
- right. rewrite E. rewrite Z_mod_same_full. clear - E Hk BS RA0. lia.
- left. rewrite Z.mod_small; [clear; lia|]. clear - BS Hk E RA0. lia. }
assert (SRCk : bytes_at rsegs m2 S2 (zb (skipn (Z.to_nat i) bs))).
{ destruct (Z.eq_dec k 0) as [K0|K0].
- replace (skipn (Z.to_nat i) bs) with (@nil Z) by (symmetry; apply skipn_all2; clear - Hik K0 IR; lia).
apply bytes_at_nil. clear - HS2; lia.
- destruct HS2c as [E|[_ [E _]]]; [| exfalso; exact (K0 E)]. rewrite E.
pose proof SRC2 as X. rewrite <- (firstn_skipn (Z.to_nat i) bs), zb_app in X.
apply (proj1 (bytes_at_app _ _ _ _ _)) in X. destruct X as [_ X]. rewrite zb_length, length_firstn in X.
replace (S + Z.of_nat (length bs) - k) with (S + Z.of_nat (Nat.min (Z.to_nat i) (length bs))) by (clear - Hik Hk IR; lia). exact X. }
eapply evt_mono.
{ eapply fwx_tail with (lo := lo) (cap := 1024%nat) (src := zb (skipn (Z.to_nat i) bs)) (m0 := m2) (S := S2);
[ exact FR2 | exact FC2 | exact BUF2
| rewrite zb_length, length_skipn; clear - CMP' LZ; lia
| exact SRCk
| rewrite zb_length, length_skipn; clear - Hik Hk IR; lia
| exact ST2
| clear - LO GLO; lia | exact SPHI | apply munch_refl | apply wmono_refl | exact MI2
| try (cbn in RA0; clear - RA0 HS2 HS2c LFI Hik Hk IR LSB CMP' BUFL LZ LS SEPF SEPB SEPS1 SEPS2 SEPS3 BS GLO LO SPHI; lia) .. ]. }
cbv beta. intros ms' PO.
first [ sf_destruct 23%nat PO as t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 -> MU3 WM3 MI3 ST3 FC3 DST3 SRC3 | sf_fb; destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 & -> & MU3 & WM3 & MI3 & ST3 & FC3 & DST3 & SRC3) ].
unfold out_post, SR. sf_eexists 16%nat.
split. { reflexivity. }
split. { apply (munch_trans _ m m1 m3).
- eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
- apply (munch_trans _ m1 m2 m3).
+ eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia.
+ eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
split. { eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]. }
split; [exact MI3|]. split; [exact ST3|].
assert (SRC3f : bytes_at rsegs m3 S (zb bs)).
{ eapply (bytes_at_transport rsegs _ m2 m3); [exact SRC2 | exact MU3 | cbn; rewrite LSB; clear - SEPS1 SEPS2 SEPS3 GLO LO Hk CMP'; lia]. }
destruct SSP2 as [GOT2 GUARD2]. change X1fd.rsegs with rsegs in GOT2, GUARD2. unfold got_ssp, ssp_guard in GOT2, GUARD2.
assert (GOT3 : rw_cells rsegs m3 245968 [C8 (Z_to_bv 64 448184)]).
{ eapply (rw_cells_transport rsegs _ m2 m3); [exact GOT2 | exact MU3 | exact WM3 | cbn; clear - GLO LO Hk; lia]. }
assert (GUARD3 : rw_cells rsegs m3 448184 [C8 canary]).
{ eapply (rw_cells_transport rsegs _ m2 m3); [exact GUARD2 | exact MU3 | exact WM3 | cbn; clear - GLO LO Hk; lia]. }
split.
{ unfold SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first app]. split; [reflexivity|].
first [ unshelve sf_eexists 4%nat; [ exact (flags) | exact (mode) | exact (tail) | exact ((zb (skipn (Z.to_nat i) bs) ++ skipn (length (zb (skipn (Z.to_nat i) bs))) bufbytes)) | ] | sf_fb; exists flags, mode, tail, (zb (skipn (Z.to_nat i) bs) ++ skipn (length (zb (skipn (Z.to_nat i) bs))) bufbytes) ].
split. { unfold zlength, file_cells. rewrite length_skipn, LBF.
replace (449312 + Z.of_nat (length bs - Z.to_nat i)) with (449312 + k) by (clear - Hik Hk IR; lia). exact FC3. }
split; [exact FL104|].
split.
{ assert (J : rw_cells rsegs m3 RSTDOUT_BUF ([] ++ [CB (length (zb (skipn (Z.to_nat i) bs))) (zb (skipn (Z.to_nat i) bs)); CB (1024 - length (zb (skipn (Z.to_nat i) bs)))%nat (skipn (length (zb (skipn (Z.to_nat i) bs))) bufbytes)] ++ [])) by exact DST3.
apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
replace (length (zb (skipn (Z.to_nat i) bs)) + (1024 - length (zb (skipn (Z.to_nat i) bs)) + 0))%nat with 1024%nat in J
by (rewrite zb_length, length_skipn; clear - Hik Hk IR CMP' LZ; lia).
exact J. }
split. { rewrite <- (zb_length (skipn (Z.to_nat i) bs)), firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity. }
unfold zlength. rewrite length_skipn. clear - CMP' LZ Hik IR Hk; lia. }
split; [split; [exact GOT3 | exact GUARD3] | exact SRC3f].
Qed.
