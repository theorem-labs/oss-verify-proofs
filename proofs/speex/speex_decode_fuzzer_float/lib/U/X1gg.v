(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bs X1c2 X1bn X1cc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gj X1fl X1ei X1ea.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0pt X0qr.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation rsegs := X1gj.rsegs.
Notation mem := (word -> option byte).

Definition STDIO_WRITE : Z := 0x34f64.
Definition STDIO_WRITE_DEPTH : Z := 112.

Definition iovs_of (buf s : list Z) : list (list byte) :=
match buf with [] => [to_bytes s] | _ => [to_bytes buf; to_bytes s] end.

Definition boxed (P : Prop) : Prop := P.

Ltac src_now SRC SEPS MU LSB :=
unfold boxed in SRC;
lazymatch goal with
| |- bytes_at _ ?m' ?S (to_bytes ?s) =>
destruct SEPS as [-> | [SEP1 SEP2]];
[ apply bytes_at_nil; lia
| apply (bytes_at_transport _ _ _ m' _ _ SRC MU); cbn [disjoint_from]; rewrite LSB; unfold zlength in SEP1, SEP2; lia ]
end.

Section StdioWrite.
Context {RCEIL : RunCeiling}.
Context {St : Type}.

#[using="Type"] Lemma implM_sysk : forall {A B} (n : node) (dec : resp -> option A) (k : A -> @M St B) (s : St) Q ms,
evt rsegs (fun ms1 => at_node rsegs n ms1 /\
(forall rsp a, dec rsp = Some a -> implM rsegs (k a) s Q (nret ms1 rsp))) ms ->
implM rsegs (X1qx.mbind (msys n dec) k) s Q ms.
Proof.
intros A B n dec k s Q ms H. unfold implM, X1qx.mbind, msys, ebind, enode in *. cbn [X1bs.bind impl].
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. destruct (dec rsp) as [a|] eqn:E; cbn [X1bs.bind fst snd].
- exact (Hk rsp a E).
- apply impl_ret_unr.
Qed.

#[using="Type"] Lemma implM_from_evt : forall {A} (c : @M St A) (s : St) Q ms,
evt rsegs (fun ms' => implM rsegs c s Q ms') ms -> implM rsegs c s Q ms.
Proof. intros A c s Q ms H. eapply implM_evt; [exact H|]. intros ms' H'; exact H'. Qed.

Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (flags : word) (B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(l : Z) (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' Fp (file_cells flags (B + bufsize) B B wfn B bufsize fd mode lbf tail)
/\ ssp_cells m' canary
/\ st' = st.

Section Call.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(buf s : list Z) (S lo : Z) (canary : word).
Let POST := stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
(Z.of_nat (length s)) lo canary m st.

Definition sw_frame (j : list byte) (b0 l0 b1 l1 : word) : list cell :=
[CB 8 j; C8 b0; C8 l0; C8 b1; C8 l1; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma bytes_at_drop : forall (mx : mem) A (bs : list byte) n,
bytes_at rsegs mx A bs -> (n <= length bs)%nat -> bytes_at rsegs mx (A + Z.of_nat n) (skipn n bs).
Proof.
intros mx A bs n H Hn. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H. destruct H as [_ H].
rewrite firstn_length, Nat.min_l in H by lia. exact H.
Qed.

#[using="Type"] Lemma frame_iov2 : forall (mx : mem) j b0 l0 b1 l1,
rw_cells rsegs mx (bv_unsigned sp + -112) (sw_frame j b0 l0 b1 l1) ->
bytes_at rsegs mx (bv_unsigned sp + -104) (iovec_bytes [(b0, l0); (b1, l1)])
/\ bytes_at rsegs mx (bv_unsigned sp + -88) (iovec_bytes [(b1, l1)]).
Proof.
intros mx j b0 l0 b1 l1 FR. unfold sw_frame in FR. destruct FR as [[WF FB] _].
cbn [cells_wf cell_wf] in WF. destruct WF as [L8 _]. cbn [cells_bytes cbytes] in FB.
apply bytes_at_app in FB as [_ FB]. rewrite L8 in FB.
apply bytes_at_app in FB as [FB1 FB]. rewrite length_le8 in FB.
apply bytes_at_app in FB as [FB2 FB]. rewrite length_le8 in FB.
apply bytes_at_app in FB as [FB3 FB]. rewrite length_le8 in FB.
apply bytes_at_app in FB as [FB4 _].
cbn [iovec_bytes flat_map fst snd]. rewrite !app_nil_r. split.
- apply bytes_at_app. rewrite length_app, !length_le8. split.
+ apply bytes_at_app. rewrite length_le8. split.
* match type of FB1 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -104) with a by lia end. exact FB1.
* match type of FB2 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -104 + Z.of_nat 8) with a by lia end. exact FB2.
+ apply bytes_at_app. rewrite length_le8. split.
* match type of FB3 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -104 + Z.of_nat (8 + 8)) with a by lia end. exact FB3.
* match type of FB4 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -104 + Z.of_nat (8 + 8) + Z.of_nat 8) with a by lia end. exact FB4.
- apply bytes_at_app. rewrite length_le8. split.
+ match type of FB3 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -88) with a by lia end. exact FB3.
+ match type of FB4 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -88 + Z.of_nat 8) with a by lia end. exact FB4.
Qed.

Definition cur_iovs (ic d0 d1 : Z) : list (list Z) :=
if ic =? 2 then [skipn (Z.to_nat d0) buf; skipn (Z.to_nat d1) s] else [skipn (Z.to_nat d1) s].

Hypotheses (FD : fd = 1 \/ fd = 2) (LO : lo <= bv_unsigned sp - 112) (GLO : 0x6e000 <= lo)
(Fp0 : 0 <= Fp) (FPLO : Fp + 232 <= lo)
(FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) (FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp)
(B0 : 0 <= B) (BS0 : 0 <= bufsize) (BUFLE : Z.of_nat (length buf) <= bufsize) (BShi : B + bufsize < 2^64)
(LENS : Z.of_nat (length buf) + Z.of_nat (length s) <= 2^26) (S0 : 0 <= S < 2^64) (Shi : S + Z.of_nat (length s) <= 2^64)
(SEPS : s = [] \/ ((S + Z.of_nat (length s) <= lo \/ bv_unsigned sp <= S) /\ (S + Z.of_nat (length s) <= Fp + 32 \/ Fp + 64 <= S)))
(SEPB : B + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= B)
(SPHI : 0 <= bv_unsigned sp < 2^64)

(BTS : B + Z.of_nat (length buf) <= TASK_SIZE) (STS : s = [] -> S <= TASK_SIZE).

#[using="LO GLO Fp0 FPLO FSEP1 FSEP2"] Lemma sw_exit : forall (raX a0X a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 s2X s3X s4X s6X : word) (m1 : mem) j b0 l0 b1 l1,
rw_cells rsegs m1 (bv_unsigned sp + -112) (sw_frame j b0 l0 b1 l1) ->
rw_cells rsegs m1 Fp (file_cells flags wend (B + Z.of_nat (length buf)) B wfn B bufsize fd mode lbf tail) ->
rw_cells rsegs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m1 ssp_guard [C8 canary] ->
stk rsegs m1 lo (bv_unsigned sp + -112) -> mem_inv rsegs m1 -> munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m m1 -> wmono rsegs m m1 ->
evt rsegs (POST tt st)
(MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 Fp) a0X a1 a2 a3 a4 a5 a6 a7
s2X s3X s4X (Z_to_bv 64 ssp_guard) s6X s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34ff8) fc None m1 (seg_rom rsegs)).
Proof.
intros until l1. intros FR FC GOT GUARD ST MI MU WM.
unfold sw_frame, file_cells, got_ssp, ssp_guard in *.
do 6 step. step. step. step. step. if_false.
do 10 step.
release_frame FR ST (bv_unsigned sp).
subst POST. unfold stdio_write_post, file_cells, ssp_cells, got_ssp, ssp_guard, STDIO_WRITE_DEPTH. sys_finish.
reflexivity.
Qed.

Hypothesis SRC : boxed (bytes_at rsegs m S (to_bytes s)).

#[using="lo FD LO GLO FPLO LENS S0 Shi SEPS SEPB SPHI BTS STS SRC"] Lemma sw_at_node : forall (mx : mem) j b0 l0 b1 l1 (ic d0 d1 : Z) fcx (pcx : word)
(x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
((ic = 2 /\ d1 = 0 /\ 0 <= d0 <= Z.of_nat (length buf) /\ b0 = Z_to_bv 64 (B + d0) /\ l0 = Z_to_bv 64 (Z.of_nat (length buf) - d0))
\/ (ic = 1 /\ d0 = Z.of_nat (length buf) /\ 0 <= d1 <= Z.of_nat (length s))) ->
S + d1 < 2^64 -> b1 = Z_to_bv 64 (S + d1) -> l1 = Z_to_bv 64 (Z.of_nat (length s) - d1) ->
rw_cells rsegs mx (bv_unsigned sp + -112) (sw_frame j b0 l0 b1 l1) ->
bytes_at rsegs mx B (to_bytes buf) -> munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m mx ->
mem_inv rsegs mx ->
at_node rsegs (NWritev fd (map to_bytes (cur_iovs ic d0 d1)))
(MSsvc (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 fd)
(Z_to_bv 64 (if ic =? 2 then bv_unsigned sp + -104 else bv_unsigned sp + -88)) (Z_to_bv 64 ic)
x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F pcx (Z_to_bv 64 66) fcx None mx (seg_rom rsegs)).
Proof.
intros until x31. intros CASE SD1 -> -> FR BUFB MU MI.
destruct (frame_iov2 _ _ _ _ _ _ FR) as [IOV2 IOV1].
assert (LSB : length (to_bytes s) = length s) by (unfold to_bytes; apply length_map).
assert (LBB : length (to_bytes buf) = length buf) by (unfold to_bytes; apply length_map).
pose proof (bytes_at_bound _ _ _ _ BUFB) as BB. rewrite LBB in BB.
assert (SRC1 : s = [] \/ bytes_at rsegs mx S (to_bytes s)).
{ destruct SEPS as [Es | [SEP1 SEP2]]; [left; exact Es| right].
pose proof SRC as SRC0. unfold boxed in SRC0.
apply (bytes_at_transport _ _ _ mx _ _ SRC0 MU). cbn [disjoint_from]. rewrite LSB. lia. }
assert (TL : bytes_at rsegs mx (S + d1) (to_bytes (skipn (Z.to_nat d1) s))).
{ rewrite to_bytes_skipn. destruct SRC1 as [Es | SRC1].
- rewrite Es. cbn [to_bytes map]. rewrite skipn_nil. apply bytes_at_nil. rewrite Es in *. cbn [length] in *. lia.
- replace (S + d1) with (S + Z.of_nat (Z.to_nat d1)) by lia. apply bytes_at_drop; [exact SRC1| rewrite LSB; lia]. }

assert (MT : mem_top rsegs = TASK_SIZE) by reflexivity.
assert (SPTS : bv_unsigned sp <= TASK_SIZE).
{ destruct FR as [_ W]. pose proof (wr_at_below _ _ _ _ MI W) as X. unfold sw_frame in X. cbn [cells_size csize Nat.add] in X. lia. }
assert (STS' : S + Z.of_nat (length s) <= TASK_SIZE).
{ destruct (Nat.eq_dec (length s) 0) as [L0|L1].
- pose proof (STS ltac:(apply length_zero_iff_nil; exact L0)). lia.
- destruct SRC1 as [Es|SB]; [rewrite Es in L1; cbn in L1; lia|].
pose proof (bytes_at_below _ _ _ _ MI SB ltac:(intros E; apply (f_equal (@length _)) in E; rewrite LSB in E; cbn in E; lia)) as X.
rewrite LSB in X. lia. }
unfold cur_iovs. destruct CASE as [(-> & -> & D0 & -> & ->) | (-> & -> & D1)]; cbn [Z.eqb Pos.eqb map].
-
at_node_red; split_spine; try reflexivity; try lia.
+ cbn [length]. lia.
+ cbn [concat]. rewrite !length_app, !to_bytes_length, !length_skipn. cbn [length]. unfold Uaccess.rw_bytes_max, node_rw_max. lia.
+ rewrite unsigned_lit by lia. cbn [length]. lia.
+ exists [(Z_to_bv 64 (B + d0), Z_to_bv 64 (Z.of_nat (length buf) - d0)); (Z_to_bv 64 (S + 0), Z_to_bv 64 (Z.of_nat (length s) - 0))].
split; [rewrite unsigned_lit by lia; exact IOV2|].
constructor; [| constructor; [|constructor]]; cbn [fst snd].
* split; [f_equal; rewrite to_bytes_length, length_skipn; lia|].
rewrite unsigned_lit by lia. split; [rewrite to_bytes_length, length_skipn; lia|]. rewrite to_bytes_skipn.
replace (B + d0) with (B + Z.of_nat (Z.to_nat d0)) by lia. apply bytes_at_drop; [exact BUFB| rewrite LBB; lia].
* split; [f_equal; rewrite to_bytes_length, length_skipn; lia|].
rewrite unsigned_lit by lia. split; [rewrite to_bytes_length, length_skipn; lia|]. exact TL.
-
at_node_red; split_spine; try reflexivity; try lia.
+ cbn [length]. lia.
+ cbn [concat]. rewrite !length_app, !to_bytes_length, !length_skipn. cbn [length]. unfold Uaccess.rw_bytes_max, node_rw_max. lia.
+ rewrite unsigned_lit by lia. cbn [length]. lia.
+ exists [(Z_to_bv 64 (S + d1), Z_to_bv 64 (Z.of_nat (length s) - d1))].
split; [rewrite unsigned_lit by lia; exact IOV1|].
constructor; [|constructor]; cbn [fst snd].
split; [f_equal; rewrite to_bytes_length, length_skipn; lia|].
rewrite unsigned_lit by lia. split; [rewrite to_bytes_length, length_skipn; lia|]. exact TL.
Qed.

#[using="Type"] Lemma v_sltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof.
clear. intros a b Ha Hb. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia. destruct (a <? b); reflexivity.
Qed.

#[using="FD LO GLO Fp0 FPLO FSEP1 FSEP2 LENS S0 Shi SEPS SEPB SPHI BTS STS SRC"] Lemma sw_loop : forall (fuel : nat) (ic d0 d1 k rem iov : Z) (raX a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 s4X : word)
(m1 : mem) j (b0 l0 b1 l1 : word),
((ic = 2 /\ d1 = 0 /\ 0 <= d0 <= Z.of_nat (length buf) /\ b0 = Z_to_bv 64 (B + d0) /\ l0 = Z_to_bv 64 (Z.of_nat (length buf) - d0))
\/ (ic = 1 /\ d0 = Z.of_nat (length buf) /\ 0 <= d1 <= Z.of_nat (length s))) ->
rem = Z.of_nat (length buf) - d0 + (Z.of_nat (length s) - d1) ->
iov = (if ic =? 2 then bv_unsigned sp + -104 else bv_unsigned sp + -88) ->
b1 = Z_to_bv 64 (S + d1) -> l1 = Z_to_bv 64 (Z.of_nat (length s) - d1) ->
1 <= k < rem ->
rw_cells rsegs m1 (bv_unsigned sp + -112) (sw_frame j b0 l0 b1 l1) ->
rw_cells rsegs m1 Fp (file_cells flags wend (B + Z.of_nat (length buf)) B wfn B bufsize fd mode lbf tail) ->
bytes_at rsegs m1 B (to_bytes buf) ->
rw_cells rsegs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m1 ssp_guard [C8 canary] ->
stk rsegs m1 lo (bv_unsigned sp + -112) -> mem_inv rsegs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m m1 -> wmono rsegs m m1 ->
implM rsegs (stdio_wloop fuel fd (wv_advance k (cur_iovs ic d0 d1))) st POST
(MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 Fp)
(Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ic) (Z_to_bv 64 iov) s4X (Z_to_bv 64 ssp_guard)
(Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x35084) fc None m1 (seg_rom rsegs)).
Proof.
induction fuel as [|fuel IH]; intros until l1; intros CASE -> -> -> -> HK FR FC BUFB GOT GUARD ST MI MU WM.
{ cbn [stdio_wloop]. apply implM_unr. }
assert (LSB : length (to_bytes s) = length s) by (unfold to_bytes; apply length_map).
assert (LBB : length (to_bytes buf) = length buf) by (unfold to_bytes; apply length_map).
pose proof (bytes_at_bound _ _ _ _ BUFB) as BB. rewrite LBB in BB.
unfold sw_frame, file_cells, got_ssp, ssp_guard in *.
destruct CASE as [(-> & -> & D0 & -> & ->) | (-> & -> & D1)]; cbn [Z.eqb Pos.eqb] in *.
2:{
rewrite Z.sub_diag, Z.add_0_l in *.
replace (wv_advance k (cur_iovs 1 (Z.of_nat (length buf)) d1)) with (cur_iovs 1 (Z.of_nat (length buf)) (d1 + k)).
2:{ unfold cur_iovs. cbn [Z.eqb Pos.eqb wv_advance]. unfold zlength. rewrite length_skipn.
replace (Z.of_nat (length s - Z.to_nat d1) <? k) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite skipn_skipn. f_equal. f_equal. lia. }
cbn [stdio_wloop]. apply implM_sysk.
step. if_cases Hneg; zify_cond Hneg. { exfalso. lia. }
step. step. rewrite v_sltu_lit by lia. replace (Z.of_nat (length s) - d1 <? k) with false by (symmetry; apply Z.ltb_ge; lia).
step. step. step.
zstep. zstep. zstep. zstep. rewrite ?Z.land_0_l, ?Z.sub_0_r. replace (S + d1 + k) with (S + (d1 + k)) by lia.
step. step. if_cases Hge; zify_cond Hge. 2:{ exfalso. lia. }
step. step. step. step. zstep. step. zstep. zstep. rewrite ?Z.land_0_l, ?Z.sub_0_r.
replace (Z.of_nat (length s) - d1 - k) with (Z.of_nat (length s) - (d1 + k)) by lia.
step. step. step. step_ecall.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply X0pt.sx32_small; lia).
split.
{ eapply (sw_at_node _ j b0 l0 _ _ 1 (Z.of_nat (length buf)) (d1 + k)); [right; lia | lia | | | exact FR | exact BUFB | exact MU | assumption]; f_equal; lia. }
intros rsp k' Hdec. unfold dec_writev in Hdec. apply dec_count_Some in Hdec as (Hc & Hcnt & Hk1 & Hklt).
assert (TOT : wv_total (cur_iovs 1 (Z.of_nat (length buf)) (d1 + k)) = Z.of_nat (length s) - (d1 + k)).
{ unfold wv_total, cur_iovs, zlength. cbn [Z.eqb Pos.eqb concat]. rewrite app_nil_r, length_skipn. lia. }
rewrite TOT in *.
apply implM_from_evt. sys_nret.
step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. } step.
replace (ret_pc (Z_to_bv 64 0x3507c)) with (Z_to_bv 64 0x3507c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. step. if_cases Hfull; zify_cond Hfull; apply evt_done.
+
subst k'. rewrite Z.eqb_refl. apply implM_ret.
eapply sw_exit; [exact FR | exact FC | exact GOT | exact GUARD | exact ST | exact MI | exact MU | exact WM].
+
replace (k' =? Z.of_nat (length s) - (d1 + k)) with false by (symmetry; apply Z.eqb_neq; exact Hfull).
eapply (IH 1 (Z.of_nat (length buf)) (d1 + k) k');
only 7: exact FR;
[right; lia | lia | reflexivity | f_equal; lia | f_equal; lia | lia
| exact FC | exact BUFB | exact GOT | exact GUARD | exact ST | exact MI | exact MU | exact WM]. }

rewrite Z.sub_0_r, Z.add_0_r in *.
cbn [stdio_wloop]. apply implM_sysk.
step. if_cases Hneg; zify_cond Hneg. { exfalso. lia. }
step. step. rewrite v_sltu_lit by lia.
destruct (Z.of_nat (length buf) - d0 <? k) eqn:CMP.
+
apply Z.ltb_lt in CMP.
replace (wv_advance k (cur_iovs 2 d0 0)) with (cur_iovs 1 (Z.of_nat (length buf)) (k - (Z.of_nat (length buf) - d0))).
2:{ unfold cur_iovs. cbn [Z.eqb Pos.eqb wv_advance Z.to_nat skipn]. unfold zlength. rewrite length_skipn.
replace (Z.of_nat (length buf - Z.to_nat d0) <? k) with true by (symmetry; apply Z.ltb_lt; lia).
f_equal. f_equal. lia. }
step. step. step.
zstep. zstep. zstep. zstep.
rewrite (Z.land_comm 18446744073709551615), X0qr.land_W64_small by lia.
replace (S + (k - (Z.of_nat (length buf) - d0))) with (S + (k - (Z.of_nat (length buf) - d0))) by lia.
step. step. if_cases Hge; zify_cond Hge. { exfalso. lia. }
step. step. step. step. step. zstep. step. zstep. zstep.
step. step. step. step_ecall.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply X0pt.sx32_small; lia).
set (d1' := k - (Z.of_nat (length buf) - d0)) in *.
split.
{ eapply (sw_at_node _ j _ _ _ _ 1 (Z.of_nat (length buf)) d1'); [right; lia | lia | | | exact FR | exact BUFB | exact MU | assumption]; f_equal; lia. }
intros rsp k' Hdec. unfold dec_writev in Hdec. apply dec_count_Some in Hdec as (Hc & Hcnt & Hk1 & Hklt).
assert (TOT : wv_total (cur_iovs 1 (Z.of_nat (length buf)) d1') = Z.of_nat (length s) - d1').
{ unfold wv_total, cur_iovs, zlength. cbn [Z.eqb Pos.eqb concat]. rewrite app_nil_r, length_skipn. lia. }
rewrite TOT in *.
replace (Z.of_nat (length buf) - d0 + Z.of_nat (length s) - k) with (Z.of_nat (length s) - d1') by lia.
apply implM_from_evt. sys_nret.
step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. } step.
replace (ret_pc (Z_to_bv 64 0x3507c)) with (Z_to_bv 64 0x3507c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. step. if_cases Hfull; zify_cond Hfull; apply evt_done.
* subst k'. rewrite Z.eqb_refl. apply implM_ret.
eapply sw_exit; [exact FR | exact FC | exact GOT | exact GUARD | exact ST | exact MI | exact MU | exact WM].
* replace (k' =? Z.of_nat (length s) - d1') with false by (symmetry; apply Z.eqb_neq; exact Hfull).
eapply (IH 1 (Z.of_nat (length buf)) d1' k');
only 7: exact FR;
[right; lia | lia | reflexivity | f_equal; lia | f_equal; lia | lia
| exact FC | exact BUFB | exact GOT | exact GUARD | exact ST | exact MI | exact MU | exact WM].
+
apply Z.ltb_ge in CMP.
replace (wv_advance k (cur_iovs 2 d0 0)) with (cur_iovs 2 (d0 + k) 0).
2:{ unfold cur_iovs. cbn [Z.eqb Pos.eqb wv_advance]. unfold zlength. rewrite length_skipn.
replace (Z.of_nat (length buf - Z.to_nat d0) <? k) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite skipn_skipn. f_equal. f_equal. lia. }
step. step. step.
zstep. zstep. zstep. zstep. rewrite ?Z.land_0_l, ?Z.sub_0_r. replace (B + d0 + k) with (B + (d0 + k)) by lia.
step. step. if_cases Hge; zify_cond Hge. 2:{ exfalso. lia. }
step. step. step. step. zstep. step. zstep. zstep. rewrite ?Z.land_0_l, ?Z.sub_0_r.
replace (Z.of_nat (length buf) - d0 - k) with (Z.of_nat (length buf) - (d0 + k)) by lia.
step. step. step. step_ecall.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply X0pt.sx32_small; lia).
split.
{ eapply (sw_at_node _ j _ _ _ _ 2 (d0 + k) 0); [left; repeat split; lia | lia | | | exact FR | exact BUFB | exact MU | assumption]; f_equal; lia. }
intros rsp k' Hdec. unfold dec_writev in Hdec. apply dec_count_Some in Hdec as (Hc & Hcnt & Hk1 & Hklt).
assert (TOT : wv_total (cur_iovs 2 (d0 + k) 0) = Z.of_nat (length buf) - (d0 + k) + Z.of_nat (length s)).
{ unfold wv_total, cur_iovs, zlength. cbn [Z.eqb Pos.eqb concat]. change (Z.to_nat 0) with 0%nat. rewrite skipn_O, app_nil_r, length_app, length_skipn. lia. }
rewrite TOT in *.
replace (Z.of_nat (length buf) - d0 + Z.of_nat (length s) - k) with (Z.of_nat (length buf) - (d0 + k) + Z.of_nat (length s)) by lia.
apply implM_from_evt. sys_nret.
step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. } step.
replace (ret_pc (Z_to_bv 64 0x3507c)) with (Z_to_bv 64 0x3507c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. step. if_cases Hfull; zify_cond Hfull; apply evt_done.
* subst k'. rewrite Z.eqb_refl. apply implM_ret.
eapply sw_exit; [exact FR | exact FC | exact GOT | exact GUARD | exact ST | exact MI | exact MU | exact WM].
* replace (k' =? Z.of_nat (length buf) - (d0 + k) + Z.of_nat (length s)) with false by (symmetry; apply Z.eqb_neq; exact Hfull).
eapply (IH 2 (d0 + k) 0 k');
only 7: exact FR;
[left; repeat split; lia | lia | reflexivity | f_equal; lia | f_equal; lia | lia
| exact FC | exact BUFB | exact GOT | exact GUARD | exact ST | exact MI | exact MU | exact WM].
Time Qed.

#[using="Type"] Lemma wv_iovs_nil' : length buf = 0%nat -> wv_iovs buf s = [s].
Proof. clear. intros H. destruct buf; [reflexivity| cbn in H; lia]. Qed.
#[using="Type"] Lemma wv_iovs_cons' : length buf <> 0%nat -> wv_iovs buf s = [buf; s].
Proof. clear. intros H. destruct buf; [cbn in H; lia| reflexivity]. Qed.

#[using="FD LO GLO Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE BShi LENS S0 Shi SEPS SEPB SPHI BTS STS SRC"] Lemma sw_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rw_cells rsegs m Fp (file_cells flags wend (B + Z.of_nat (length buf)) B wfn B bufsize fd mode lbf tail) ->
bytes_at rsegs m B (to_bytes buf) ->
stk rsegs m lo (bv_unsigned sp) -> rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
rw_cells rsegs m ssp_guard [C8 canary] -> mem_inv rsegs m ->
implM rsegs (stdio_writev (St:=St) fd buf s) st POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length s))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34f64) fc None m (seg_rom rsegs)).
Proof.
intros until t6. intros FC BUFB ST GOT GUARD MI.
assert (LSB : length (to_bytes s) = length s) by (unfold to_bytes; apply length_map).
assert (LBB : length (to_bytes buf) = length buf) by (unfold to_bytes; apply length_map).
pose proof (bytes_at_bound _ _ _ _ BUFB) as BB. rewrite LBB in BB.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
unfold stdio_writev, zlength. destruct (Z.ltb_spec WRITEV_MAX (Z.of_nat (length buf) + Z.of_nat (length s))) as [OV|ENV].
{ apply implM_unr. }
clear ENV. cbn [stdio_wloop]. apply implM_sysk.
unfold file_cells, got_ssp, ssp_guard in FC, GOT, GUARD |- *.
carve_frame 112%nat ST.
do 12 step. do 13 step.
rewrite !unsigned_lit by lia. rewrite !unsigned_lit in FR by lia.
replace (B + Z.of_nat (length buf) - B) with (Z.of_nat (length buf) - 0) in FR |- * by lia.
replace (Z.lxor (B + Z.of_nat (length buf)) B) with (Z.lxor (B + Z.of_nat (length buf)) (B + 0)) by (rewrite Z.add_0_r; reflexivity).
destruct (Nat.eq_dec (length buf) 0) as [NIL|CONS].
-
rewrite (wv_iovs_nil' NIL). change [s] with (cur_iovs 1 0 0).
rewrite !NIL. cbn [Z.of_nat]. rewrite !Z.add_0_r, !Z.add_0_l, Z.lxor_nilpotent.
change (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) with (Z_to_bv 64 0).
step. if_true. do 6 step. step_ecall.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply X0pt.sx32_small; lia).
split.
{ eapply (sw_at_node _ _ _ _ _ _ 1 0 0); only 5: exact FR; [right; lia | lia | f_equal; lia | f_equal; lia | exact BUFB | exact MU | assumption]. }
intros rsp k Hdec. unfold dec_writev in Hdec. apply dec_count_Some in Hdec as (Hc & Hcnt & Hk1 & Hklt).
assert (TOT : wv_total (cur_iovs 1 0 0) = Z.of_nat (length s)).
{ unfold wv_total, cur_iovs, zlength. cbn [Z.eqb Pos.eqb concat]. change (Z.to_nat 0) with 0%nat. rewrite skipn_O, app_nil_r. reflexivity. }
rewrite TOT in Hcnt, Hk1 |- *.
apply implM_from_evt. sys_nret.
step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. } step.
replace (ret_pc (Z_to_bv 64 0x34ff4)) with (Z_to_bv 64 0x34ff4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_cases Hfull; zify_cond Hfull; apply evt_done.
+ replace (k =? Z.of_nat (length s)) with false by (symmetry; apply Z.eqb_neq; exact Hfull).
eapply (sw_loop _ 1 0 0 k);
only 7: exact FR;
[right; lia | lia | reflexivity | f_equal; lia | f_equal; lia | lia
| exact FC | exact BUFB | exact GOT | exact GUARD | exact ST | exact MI | exact MU | exact WM].
+ subst k. rewrite Z.eqb_refl. apply implM_ret.
eapply sw_exit; [exact FR | exact FC | exact GOT | exact GUARD | exact ST | exact MI | exact MU | exact WM].
-
assert (NB1 : 1 <= Z.of_nat (length buf)) by lia.
rewrite (wv_iovs_cons' CONS). change [buf; s] with (cur_iovs 2 0 0).
assert (XNZ : Z.lxor (B + Z.of_nat (length buf)) (B + 0) <> 0).
{ intros E. apply Z.lxor_eq in E. lia. }
replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (B + Z.of_nat (length buf)) (B + 0)))) with (Z_to_bv 64 1).
2:{ pose proof (Z_lxor_range (B + Z.of_nat (length buf)) (B + 0) ltac:(lia) ltac:(lia)) as XR.
unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
destruct (Z.ltb_spec0 0 (Z.lxor (B + Z.of_nat (length buf)) (B + 0))); [reflexivity| exfalso; lia]. }
step. if_cases Hb; zify_cond Hb. 1:{ exfalso. lia. } do 7 step. step_ecall.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply X0pt.sx32_small; lia).
split.
{ eapply (sw_at_node _ _ _ _ _ _ 2 0 0); only 5: exact FR; [left; repeat split; try lia; f_equal; lia | lia | f_equal; lia | f_equal; lia | exact BUFB | exact MU | assumption]. }
intros rsp k Hdec. unfold dec_writev in Hdec. apply dec_count_Some in Hdec as (Hc & Hcnt & Hk1 & Hklt).
assert (TOT : wv_total (cur_iovs 2 0 0) = Z.of_nat (length buf) + Z.of_nat (length s)).
{ unfold wv_total, cur_iovs, zlength. cbn [Z.eqb Pos.eqb concat]. change (Z.to_nat 0) with 0%nat. rewrite !skipn_O, app_nil_r, length_app. lia. }
rewrite TOT in Hcnt, Hk1 |- *.
replace (Z.of_nat (length buf) - 0 + Z.of_nat (length s)) with (Z.of_nat (length buf) + Z.of_nat (length s)) by lia.
apply implM_from_evt. sys_nret.
step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. } step.
replace (ret_pc (Z_to_bv 64 0x34ff4)) with (Z_to_bv 64 0x34ff4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_cases Hfull; zify_cond Hfull; apply evt_done.
+ replace (k =? Z.of_nat (length buf) + Z.of_nat (length s)) with false by (symmetry; apply Z.eqb_neq; exact Hfull).
eapply (sw_loop _ 2 0 0 k); only 7: exact FR;
[left; repeat split; try lia; f_equal; lia | lia | reflexivity | f_equal; lia | f_equal; lia | lia
| exact FC | exact BUFB | exact GOT | exact GUARD | exact ST | exact MI | exact MU | exact WM].
+ subst k. rewrite Z.eqb_refl. apply implM_ret.
eapply sw_exit; [exact FR | exact FC | exact GOT | exact GUARD | exact ST | exact MI | exact MU | exact WM].
Time Qed.
End Call.

#[using="Type"] Lemma stdio_write_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(buf s : list Z) (S lo : Z) (canary : word),
rw_cells rsegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
bytes_at rsegs m B (to_bytes buf) ->
bytes_at rsegs m S (to_bytes s) ->
a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
(fd = 1 \/ fd = 2) ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDIO_WRITE_DEPTH) -> (0x6e000 <= lo) ->
ssp_cells m canary -> mem_inv rsegs m ->
(0 <= Fp) -> (Fp + 232 <= lo) ->
(Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
(0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize < 2^64) ->
(zlength buf + zlength s < 2^62) -> (0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
(s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
(B + zlength buf <= lo \/ bv_unsigned sp <= B) ->
(B + zlength buf <= TASK_SIZE) -> (s = [] -> S <= TASK_SIZE) ->
implM rsegs (stdio_writev (St:=St) fd buf s) st
(stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
(zlength s) lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34f64) fc None m (seg_rom rsegs)).
Proof.
intros until canary. intros FC BUFB SRC -> -> -> FD ST LO GLO SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE BShi LENS S0 Shi SEPS SEPB BTS STS.
pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
destruct SSP as [GOT GUARD]. change X1fd.rsegs with rsegs in GOT, GUARD. unfold STDIO_WRITE_DEPTH in *.
unfold zlength in *.
destruct (Z.le_gt_cases (Z.of_nat (length buf) + Z.of_nat (length s)) WRITEV_MAX) as [ENV|OV].
- unfold WRITEV_MAX in ENV.
eapply sw_main; try eassumption; try lia.
- unfold stdio_writev, zlength. replace (WRITEV_MAX <? Z.of_nat (length buf) + Z.of_nat (length s)) with true by (symmetry; apply Z.ltb_lt; lia).
apply implM_unr.
Qed.
End StdioWrite.
