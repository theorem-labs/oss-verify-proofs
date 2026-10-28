(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1cc X1bk X1bj X1cf X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ii.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r0 X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition wpre (l : list Z) (ws : list word) : Prop := firstn (length l) ws = map wz l /\ (length l <= length ws)%nat.

Lemma nth_firstn_lt' : forall {X} (l : list X) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
induction l as [|x l IH]; intros [|n] [|k] d Hk; cbn; try reflexivity; try lia. apply IH. lia.
Qed.

Lemma wpre_nth : forall l ws i, wpre l ws -> 0 <= i -> (Z.to_nat i < length l)%nat ->
nth (Z.to_nat i) ws (Z_to_bv 64 0) = wz (znth l i).
Proof.
intros l ws i [P LE] Hi Hl. unfold znth. destruct (Z.ltb_spec i 0); [lia|].
rewrite <- (nth_firstn_lt' ws (length l) (Z.to_nat i) (Z_to_bv 64 0)) by lia. rewrite P.
change (Z_to_bv 64 0) with (wz 0). apply map_nth.
Qed.

Lemma zx32_wz : forall v, 0 <= v < 2^32 -> zx32 (wz v) = wz v.
Proof. intros v Hv. unfold zx32, wz. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite !Z.mod_small; lia. Qed.

Lemma u32_read : forall m L l ws (i : Z) a,
u32arr rsegs m L ws -> wpre l ws -> 0 <= i -> (Z.to_nat i < length l)%nat -> a = wa (L + 4 * i) ->
ov_read_bytes rsegs m a 4 = Some (le4 (wz (znth l i))).
Proof.
intros m L l ws i a ARR PREw Hi Hl ->. rewrite <- (wpre_nth l ws i PREw Hi Hl).
eapply (u32arr_read rsegs m L ws i); [exact ARR| | lia| reflexivity].
apply nth_error_nth'. destruct PREw. lia.
Qed.
Lemma u64_read : forall m Gv l ws (i : Z) a,
u64arr rsegs m Gv ws -> wpre l ws -> 0 <= i -> (Z.to_nat i < length l)%nat -> a = wa (Gv + 8 * i) ->
ov_read_bytes rsegs m a 8 = Some (le8 (wz (znth l i))).
Proof.
intros m Gv l ws i a ARR PREw Hi Hl ->. rewrite <- (wpre_nth l ws i PREw Hi Hl).
eapply (u64arr_read rsegs m Gv ws i); [exact ARR| | lia| reflexivity].
apply nth_error_nth'. destruct PREw. lia.
Qed.

Lemma gather255_stop : forall size rest eos bytes n, size <> 255 -> gather255 size rest eos bytes n = Some (n, eos, bytes).
Proof. intros. destruct rest; cbn [gather255]; destruct (Z.eqb_spec size 255); try lia; reflexivity. Qed.
Lemma gather255_go : forall val rest eos bytes n,
gather255 255 (val :: rest) eos bytes n =
gather255 (Z.land val 255) rest (if negb (Z.land val 512 =? 0) then 512 else eos) (bytes + Z.land val 255) (n + 1).
Proof. intros. reflexivity. Qed.
Lemma gather255_nil : forall eos bytes n, gather255 255 [] eos bytes n = None.
Proof. intros. reflexivity. Qed.

Lemma land_pow2_cases : forall v k, 0 <= k -> Z.land v (2^k) = 0 \/ Z.land v (2^k) = 2^k.
Proof.
intros v k Hk.
destruct (Z.testbit v k) eqn:T.
- right. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec k i); [subst; rewrite T; reflexivity| apply andb_false_r].
- left. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
destruct (Z.eqb_spec k i); [subst; rewrite T; reflexivity| apply andb_false_r].
Qed.

Lemma gather255_facts : forall rest size eos bytes n n' eos' bytes',
gather255 size rest eos bytes n = Some (n', eos', bytes') -> 0 <= bytes ->
0 <= bytes' <= bytes + 255 * (n' - n) /\ (eos' = eos \/ eos' = 512).
Proof.
induction rest as [|val rest IH]; intros size eos bytes n n' eos' bytes' G Hb.
- destruct (Z.eqb_spec size 255); [subst; rewrite gather255_nil in G; discriminate|].
rewrite gather255_stop in G by assumption. injection G as <- <- <-. lia.
- destruct (Z.eqb_spec size 255).
+ subst. rewrite gather255_go in G.
assert (R : 0 <= Z.land val 255 < 256).
{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
apply IH in G; [|lia]. destruct (Z.land val 512 =? 0); cbn [negb] in G; lia.
+ rewrite gather255_stop in G by assumption. injection G as <- <- <-. lia.
Qed.

Definition stream_fields_ok (os : stream_st bptr) : Prop :=
0 <= os_body_storage os < 2^63 /\ 0 <= os_body_fill os < 2^63 /\ 0 <= os_body_returned os /\
int31 (os_lacing_storage os) /\ int31 (os_lacing_fill os) /\ int31 (os_lacing_packet os) /\ int31 (os_lacing_returned os) /\
int31 (os_header_fill os) /\ int31 (os_e_o_s os) /\ int31 (os_b_o_s os) /\
-2^31 <= os_serialno os < 2^31 /\ -1 <= os_pageno os <= 2^32.

Definition lacing_vals_ok (l : list Z) : Prop := Forall (fun v => 0 <= v < 2048) l.

Definition granules_ok (l : list Z) : Prop := Forall (fun v => -2^63 <= v < 2^63) l.

Lemma Forall_znth : forall (P : Z -> Prop) l i, Forall P l -> P 0 -> P (znth l i).
Proof.
intros P l i H H0. unfold znth. destruct (i <? 0); [exact H0|].
destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)).
- eapply Forall_nth in H; [exact H| assumption].
- rewrite nth_overflow by lia. exact H0.
Qed.

Definition op_cells (Bd : Z) (opo : option packet) (gw : word) (kc : list cell) : list cell :=
match opo with
| Some op => [C8 (wz (Bd + pk_off op)); C8 (wz (pk_bytes op)); C8 (wz (pk_b_o_s op)); C8 (wz (pk_e_o_s op)); C8 gw; C8 (wz (pk_packetno op))]
| None => kc
end.

Definition packetout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A Bd L Gv K : Z) (hdr : list byte) (kc : list cell) (m : mem)
(r : Z) (opo : option packet) (os' : stream_st bptr) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (gw : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(A, A + 408); (K, K + 48)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' A (stream_cells Bd L Gv hdr os') /\ stream_fields_ok os'
/\ rw_cells rsegs m' K (op_cells Bd opo gw kc).

Section PK.
Context {RCEIL : RunCeiling}.
Variables (A Bd L Gv K : Z) (hdr : list byte) (os : stream_st bptr) (lws gws : list word) (k0 k1 k2 k3 k4 k5 : list byte).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
Local Notation kc := [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
Local Notation W := [(A, A + 408); (K, K + 48)].
Hypothesis HL : length hdr = 284%nat.
Hypothesis FOK : stream_fields_ok os.
Hypothesis INV : lacing_inv os.
Hypothesis LOK : lacing_vals_ok (os_lacing os).
Hypothesis LPRE : wpre (os_lacing os) lws.
Hypothesis LLEN : Z.of_nat (length lws) = os_lacing_storage os.
Hypothesis GLEN : Z.of_nat (length gws) = os_lacing_storage os.
Hypothesis GFIL : length (os_granules os) = length (os_lacing os).
Hypothesis HA : 0 < A. Hypothesis HK : 0 < K. Hypothesis HBd : 0 <= Bd < 2^63.
Hypothesis TOPL : L + 4 * Z.of_nat (length lws) < 2^63. Hypothesis TOPG : Gv + 8 * Z.of_nat (length gws) < 2^63.
Hypothesis SEP_AK : A + 408 <= K \/ K + 48 <= A.
Hypothesis SEP_AL : A + 408 <= L \/ L + 4 * Z.of_nat (length lws) <= A.
Hypothesis SEP_AG : A + 408 <= Gv \/ Gv + 8 * Z.of_nat (length gws) <= A.
Hypothesis SEP_KL : K + 48 <= L \/ L + 4 * Z.of_nat (length lws) <= K.
Hypothesis SEP_KG : K + 48 <= Gv \/ Gv + 8 * Z.of_nat (length gws) <= K.

Notation POST := (packetout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A Bd L Gv K hdr kc m0).

#[using="os lws gws HL GFIL HA SEP_AK"] Lemma pko_tail : forall m r (os1 : stream_st bptr) (newret : Z) opo (gw : word)
(x5 x6 x7 x11 x12 x15 x16 x17 x28 x29 x30 x31 : word),
munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
rw_cells rsegs m A (stream_cells Bd L Gv hdr os1) -> stream_fields_ok os1 -> 0 <= newret < 2^31 ->
rw_cells rsegs m K (op_cells Bd opo gw kc) ->
evt rsegs (POST r opo (mkStream (os_body_data os1) (os_body os1) (os_body_storage os1) (os_body_fill os1) (os_body_returned os1)
(os_lacing_vals os1) (os_lacing os1) (os_granule_vals os1) (os_granules os1)
(os_lacing_storage os1) (os_lacing_fill os1) (os_lacing_packet os1) newret
(os_header_fill os1) (os_e_o_s os1) (os_b_o_s os1) (os_serialno os1) (os_pageno os1)
(os_packetno os1 + 1) (os_granulepos os1)))
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 A) x11 x12 (Z_to_bv 64 r) (Z_to_bv 64 newret) x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x30d8c) fc None m (seg_rom rsegs)).
Proof.
intros until x31. intros MU WM MI OS FOK1 Hnr OP.
pose proof FOK1 as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
unfold stream_cells, wz in OS.
pose proof (rw_cells_bound _ _ _ _ OS) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (rw_cells_bound _ _ _ _ OP) as KB.
destruct opo as [op|]; cbn [op_cells] in OP, KB; unfold wz in OP, KB; cbn [cells_size csize Nat.add] in KB.
all: zstep; zstep; zstep; zstep; zstep; zstep.
all: finish.
all: try (cbn [op_cells]; unfold wz; eassumption).
all: unfold stream_fields_ok, int31 in *; cbn; lia.
Unshelve. all: try exact (Z_to_bv 64 0).
Qed.

Definition gather_post (x29 x30 x31 : word) (v0 p' eos' bytes' : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (x7 x28 : word),
ms' = MS (mkR ra sp gp tp (Z_to_bv 64 255) (Z_to_bv 64 (L + 4 * (p' + 1))) x7 s0 s1
(Z_to_bv 64 A) (Z_to_bv 64 K) (Z_to_bv 64 1) (Z_to_bv 64 1)
(Z_to_bv 64 p') (Z_to_bv 64 bytes') (Z_to_bv 64 v0) (Z_to_bv 64 eos')
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x30d1c) fc None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

#[using="Gv hdr gws HL LOK LPRE LLEN GLEN GFIL SEP_AK SEP_AL SEP_AG SEP_KL SEP_KG"] Lemma pko_gather : forall (rest : list Z) (p n eos bytes n' eos' bytes' t1v v0 : Z) m (x7 x28 x29 x30 x31 : word),
rest = skipn (Z.to_nat (p + 1)) (os_lacing os) -> 0 <= p ->
gather255 255 rest eos bytes n = Some (n', eos', bytes') ->
t1v = L + 4 * (p + 1) -> 0 <= eos < 2^31 -> 0 <= bytes <= 255 * (p + 1) -> 0 <= v0 < 2^31 ->
u32arr rsegs m L lws -> mem_inv rsegs m ->
evt rsegs (gather_post x29 x30 x31 v0 (p + (n' - n)) eos' bytes' m)
(MS (mkR ra sp gp tp (Z_to_bv 64 255) (Z_to_bv 64 t1v) x7 s0 s1
(Z_to_bv 64 A) (Z_to_bv 64 K) (Z_to_bv 64 1) (Z_to_bv 64 1)
(Z_to_bv 64 p) (Z_to_bv 64 bytes) (Z_to_bv 64 v0) (Z_to_bv 64 eos)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x30cf8) fc None m (seg_rom rsegs)).
Proof.
induction rest as [|val rest IH]; intros p n eos bytes n' eos' bytes' t1v v0 m x7 x28 x29 x30 x31 Hrest Hp G -> Heos Hbytes Hv0 LAC MI.
{ rewrite gather255_nil in G. discriminate. }
rewrite gather255_go in G.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof LPRE as [LP1 LP2]. pose proof (u32arr_bound _ _ _ _ LAC) as LB.

assert (Hlen : (Z.to_nat (p + 1) < length (os_lacing os))%nat).
{ destruct (Nat.lt_ge_cases (Z.to_nat (p + 1)) (length (os_lacing os))) as [?|Hge]; [assumption|].
rewrite skipn_all2 in Hrest by lia. discriminate. }
assert (Hval : znth (os_lacing os) (p + 1) = val).
{ unfold znth. destruct (Z.ltb_spec (p + 1) 0); [lia|]. rewrite <- (Nat.add_0_r (Z.to_nat (p + 1))), <- nth_skipn, <- Hrest. reflexivity. }
pose proof (Forall_znth _ (os_lacing os) (p + 1) LOK ltac:(cbv beta; lia)) as Rval. cbv beta in Rval. rewrite Hval in Rval.
pose proof (u32_read m L _ lws (p + 1) _ LAC LPRE ltac:(lia) Hlen eq_refl) as RD. rewrite Hval in RD.
assert (Hrest' : rest = skipn (Z.to_nat (p + 1 + 1)) (os_lacing os)).
{ replace (Z.to_nat (p + 1 + 1)) with (S (Z.to_nat (p + 1))) by lia.
rewrite (skipn_nth_cons (os_lacing os) (Z.to_nat (p + 1)) 0) in Hrest by lia. injection Hrest as _ <-. reflexivity. }
assert (R255 : 0 <= Z.land val 255 < 256) by (rewrite Z.land_comm; apply (X1bk.land_lt_pow2 255 val 8); lia).

zstep. rewrite sx32_wz by (unfold int31; lia). unfold wz. zstep.
zstep. if_cases CND; zify_cond CND; rewrite ?unsigned_lit in CND by lia.
-
rewrite CND, Z.eqb_refl in G. cbv beta iota delta [negb] in G.

zstep. zstep. zstep. zstep. zstep.
if_cases CN2; zify_cond CN2; rewrite ?unsigned_lit in CN2 by lia.
+
rewrite CN2 in G |- *.
replace (p + (n' - n)) with (p + 1 + (n' - (n + 1))) by lia.
eapply (IH (p + 1) (n + 1)); try eassumption; try lia.
+ rewrite gather255_stop in G by lia. injection G as <- <- <-.
replace (p + (n + 1 - n)) with (p + 1) by lia.
match goal with |- context [Z_to_bv 64 (?e + 4)] => replace (e + 4) with (L + 4 * (p + 1 + 1)) by lia end.
finish.
-
destruct (Z.eqb_spec (Z.land val 512) 0); [lia|]. cbv beta iota delta [negb] in G.
zstep. zstep. zstep. zstep. zstep. zstep.
if_cases CN2; zify_cond CN2; rewrite ?unsigned_lit in CN2 by lia.
+ rewrite CN2 in G |- *.
replace (p + (n' - n)) with (p + 1 + (n' - (n + 1))) by lia.
eapply (IH (p + 1) (n + 1)); try eassumption; try lia.
+ rewrite gather255_stop in G by lia. injection G as <- <- <-.
replace (p + (n + 1 - n)) with (p + 1) by lia.
match goal with |- context [Z_to_bv 64 (?e + 4)] => replace (e + 4) with (L + 4 * (p + 1 + 1)) by lia end.
finish.
Qed.

#[using="HL FOK INV LOK LPRE LLEN GLEN GFIL HA HK TOPL TOPG SEP_AK SEP_AL SEP_AG SEP_KL SEP_KG"] Lemma pko_fill : forall m (p' bytes' eos' v0 : Z) (x5 x6 x7 x13 x28 x29 x30 x31 : word),
let ptr := os_lacing_returned os in
ptr <= p' < os_lacing_packet os -> 0 <= bytes' <= 255 * (p' + 1) -> 0 <= eos' < 2^31 -> v0 = znth (os_lacing os) ptr ->
munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
rw_cells rsegs m A (stream_cells Bd L Gv hdr os) -> u32arr rsegs m L lws -> u64arr rsegs m Gv gws ->
rw_cells rsegs m K kc ->
evt rsegs (POST 1 (Some (mkPacket (os_body_returned os) bytes' (Z.land v0 256) eos' (znth (os_granules os) p') (os_packetno os)))
(mkStream (os_body_data os) (os_body os) (os_body_storage os) (os_body_fill os) (os_body_returned os + bytes')
(os_lacing_vals os) (os_lacing os) (os_granule_vals os) (os_granules os)
(os_lacing_storage os) (os_lacing_fill os) (os_lacing_packet os) (p' + 1)
(os_header_fill os) (os_e_o_s os) (os_b_o_s os) (os_serialno os) (os_pageno os)
(os_packetno os + 1) (os_granulepos os)))
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 K) (Z_to_bv 64 1) x13
(Z_to_bv 64 p') (Z_to_bv 64 bytes') (Z_to_bv 64 v0) (Z_to_bv 64 eos')
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x30d20) fc None m (seg_rom rsegs)).
Proof.
intros until x31. intros ptr Hp Hb He Hv0 MU WM MI OS LAC GRA OP.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
pose proof INV as (I1 & I2 & I3). unfold zlength in I2. pose proof LPRE as [LP1 LP2].
unfold stream_cells, wz in OS.
pose proof (rw_cells_bound _ _ _ _ OS) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (rw_cells_bound _ _ _ _ OP) as KB. cbn [cells_size csize Nat.add] in KB.
pose proof (u32arr_bound _ _ _ _ LAC) as LB.
pose proof (u64arr_bound _ _ _ _ GRA) as GB.
pose proof (Forall_znth _ (os_lacing os) ptr LOK ltac:(cbv beta; lia)) as Rv0. cbv beta in Rv0. rewrite <- Hv0 in Rv0.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.

zstep. rewrite swrap32_small by lia. zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia.
replace (Gv + p' * 2 ^ 3) with (Gv + 8 * p') by lia.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (u64arr_read rsegs mx Gv gws p' _ _ GRA (nth_error_nth' (n := Z.to_nat p') gws (Z_to_bv 64 0) ltac:(lia)) ltac:(lia) eq_refl) as RG end.
zstep. zstep. zstep. zstep. zstep.

zstep. if_cases CND; zify_cond CND; rewrite ?unsigned_lit in CND by lia; [exfalso; lia|].
zstep. zstep. rewrite swrap32_small by lia. zstep. zstep. zstep. zstep.
eapply (pko_tail _ 1 (mkStream (os_body_data os) (os_body os) (os_body_storage os) (os_body_fill os) (os_body_returned os + bytes')
(os_lacing_vals os) (os_lacing os) (os_granule_vals os) (os_granules os)
(os_lacing_storage os) (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os)
(os_header_fill os) (os_e_o_s os) (os_b_o_s os) (os_serialno os) (os_pageno os)
(os_packetno os) (os_granulepos os)) (p' + 1) (Some _)); try eassumption; try lia.
unfold stream_fields_ok, int31 in *; cbn. lia.
Qed.

#[using="HL FOK INV LOK LPRE LLEN GLEN GFIL HA HK HBd TOPL TOPG SEP_AK SEP_AL SEP_AG SEP_KL SEP_KG"] Lemma pko_body : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) r opo (os' : stream_st bptr),
mem_inv rsegs m0 ->
rw_cells rsegs m0 A (stream_cells Bd L Gv hdr os) -> u32arr rsegs m0 L lws -> u64arr rsegs m0 Gv gws ->
rw_cells rsegs m0 K kc ->
(os_body_data os = None <-> Bd = 0) ->
ogg_stream_packetout os = Some ((r, opo), os') ->
evt rsegs (POST r opo os')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 K) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_packetout) fc None m0 (seg_rom rsegs)).
Proof.
intros until os'. intros MI OS LAC GRA OP HBd' RES. unfold A_ogg_stream_packetout.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
pose proof INV as (I1 & I2 & I3). unfold zlength in I2. pose proof LPRE as [LP1 LP2].
unfold stream_cells, wz in OS.
pose proof (rw_cells_bound _ _ _ _ OS) as AB. cbn [cells_size csize Nat.add] in AB.
pose proof (rw_cells_bound _ _ _ _ OP) as KB. cbn [cells_size csize Nat.add] in KB.
pose proof (u32arr_bound _ _ _ _ LAC) as LB. pose proof (u64arr_bound _ _ _ _ GRA) as GB.
pose proof (munch_refl W m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
unfold ogg_stream_packetout, ogg_stream_check in RES.

zstep. if_cases CN0; zify_cond CN0; rewrite ?unsigned_lit in CN0 by lia; [exfalso; lia|].
zstep. zstep. if_cases CB0; zify_cond CB0; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CB0 by lia.
-
destruct (os_body_data os) as [bd|]; [exfalso; pose proof (proj2 HBd' CB0); discriminate|].
injection RES as <- <- <-.
zstep. zstep. finish.
- destruct (os_body_data os) as [bd|]; [| exfalso; pose proof (proj1 HBd' eq_refl); lia].
unfold packetout in RES.
set (lr := os_lacing_returned os) in *. set (lp := os_lacing_packet os) in *.

zstep. zstep. zstep. zstep. zstep. rewrite swrap32_small by lia.
zstep. if_cases CN1; zify_cond CN1; rewrite ?signed_lit_small in CN1 by lia.
+
destruct (Z.leb_spec lp lr); [|exfalso; lia]. injection RES as <- <- <-.
zstep. zstep. zstep. zstep. finish.
+ destruct (Z.leb_spec lp lr); [exfalso; lia|].
set (v := znth (os_lacing os) lr) in *.
pose proof (Forall_znth _ (os_lacing os) lr LOK ltac:(cbv beta; lia)) as Rv. cbv beta in Rv. fold v in Rv.
pose proof (u32_read m0 L _ lws lr _ LAC LPRE ltac:(lia) ltac:(lia) eq_refl) as RD. fold v in RD. unfold wz in RD.

zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. zstep. replace (L + lr * 2 ^ 2) with (L + 4 * lr) by lia.
zstep. rewrite zx32_wz by lia. unfold wz. zstep.
zstep. if_cases C2_; zify_cond C2_; rewrite ?unsigned_lit in C2_ by lia.
*
destruct (Z.eqb_spec (Z.land v 1024) 0); [lia|]. cbn [negb] in RES. injection RES as <- <- <-.
zstep. zstep.
eapply (pko_tail _ (-1) os (lr + 1) None); try eassumption; try lia.
* destruct (Z.eqb_spec (Z.land v 1024) 0); [|lia]. cbn [negb] in RES.
assert (R255 : 0 <= Z.land v 255 < 256) by (rewrite Z.land_comm; apply (X1bk.land_lt_pow2 255 v 8); lia).
assert (R512 : 0 <= Z.land v 512 <= 512).
{ change 512 with (2^9). destruct (land_pow2_cases v 9 ltac:(lia)) as [-> | ->]; lia. }

zstep. zstep. if_cases CN3; zify_cond CN3; rewrite ?unsigned_lit in CN3 by lia; [|exfalso; lia].
zstep. zstep. zstep.
zstep. if_cases CN4; zify_cond CN4; rewrite ?unsigned_lit in CN4 by lia.
--
rewrite gather255_stop in RES by lia.
destruct (packetout_inv os _ _ _ INV ltac:(unfold packetout; fold lr lp; destruct (Z.leb_spec lp lr); [lia|];
fold v; destruct (Z.eqb_spec (Z.land v 1024) 0); [|lia]; cbn [negb]; rewrite gather255_stop by lia; reflexivity)) as (Iv' & _).
injection RES as <- <- <-. rewrite !Z.add_0_r.
zstep. zstep. if_cases CN5; zify_cond CN5; rewrite ?unsigned_lit in CN5 by lia; [|exfalso; lia].
eapply (pko_fill _ lr); try eassumption; try lia. reflexivity.
--
rewrite CN4 in RES.
destruct (gather255 255 (zdrop (lr + 1) (os_lacing os)) (Z.land v 512) 255 0) as [[[n' eos'] bytes']|] eqn:G; [|discriminate].
destruct (packetout_inv os _ _ _ INV ltac:(unfold packetout; fold lr lp; destruct (Z.leb_spec lp lr); [lia|];
fold v; destruct (Z.eqb_spec (Z.land v 1024) 0); [|lia]; cbn [negb]; rewrite CN4, G; reflexivity)) as (Iv' & _).
destruct Iv' as (J1 & J2 & J3). cbn [os_lacing_returned os_lacing_packet os_lacing] in J1, J2.
pose proof (gather255_bound _ _ _ _ _ _ _ _ G) as NB.
injection RES as <- <- <-.
zstep. zstep. rewrite ?CN4.
call (pko_gather (zdrop (lr + 1) (os_lacing os)) lr 0 (Z.land v 512) 255 n' eos' bytes' (L + 4 * lr + 4) v).
all: try eassumption; try lia; try reflexivity.
pose proof (gather255_facts _ _ _ _ _ _ _ _ G ltac:(lia)) as [GB1 GB2].
replace (lr + (n' - 0)) with (lr + n') by lia.

zstep. if_cases CN6; zify_cond CN6; rewrite ?unsigned_lit in CN6 by lia; [exfalso; lia|].
eapply (pko_fill _ (lr + n')); try eassumption; try lia. reflexivity.
Unshelve. all: try exact (Z_to_bv 64 0).
Qed.
End PK.

Lemma ogg_stream_packetout_spec : forall (A Bd L Gv K : Z) (hdr : list byte) (os : stream_st bptr) (lws gws : list word) (k0 k1 k2 k3 k4 k5 : list byte)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) r opo (os' : stream_st bptr),
length hdr = 284%nat -> stream_fields_ok os -> lacing_inv os -> lacing_vals_ok (os_lacing os) ->
wpre (os_lacing os) lws ->
Z.of_nat (length lws) = os_lacing_storage os -> Z.of_nat (length gws) = os_lacing_storage os ->
length (os_granules os) = length (os_lacing os) ->
0 < A -> 0 < K -> 0 <= Bd < 2^63 -> L + 4 * Z.of_nat (length lws) < 2^63 -> Gv + 8 * Z.of_nat (length gws) < 2^63 ->
(A + 408 <= K \/ K + 48 <= A) -> (A + 408 <= L \/ L + 4 * Z.of_nat (length lws) <= A) -> (A + 408 <= Gv \/ Gv + 8 * Z.of_nat (length gws) <= A) ->
(K + 48 <= L \/ L + 4 * Z.of_nat (length lws) <= K) -> (K + 48 <= Gv \/ Gv + 8 * Z.of_nat (length gws) <= K) ->
mem_inv rsegs m ->
rw_cells rsegs m A (stream_cells Bd L Gv hdr os) -> u32arr rsegs m L lws -> u64arr rsegs m Gv gws ->
rw_cells rsegs m K [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5] ->
(os_body_data os = None <-> Bd = 0) ->
ogg_stream_packetout os = Some ((r, opo), os') ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 K ->
evt rsegs (packetout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A Bd L Gv K hdr [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5] m r opo os')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_packetout) fc None m (seg_rom rsegs)).
Proof.
intros until os'. intros HL FOK INV LOK LPRE LLEN GLEN GFIL HA HK HBd TOPL TOPG S1 S2 S3 S4 S5 MI OS LAC GRA OP HBD RES -> ->.
eapply (pko_body A Bd L Gv K hdr os lws gws k0 k1 k2 k3 k4 k5); eassumption.
Qed.
