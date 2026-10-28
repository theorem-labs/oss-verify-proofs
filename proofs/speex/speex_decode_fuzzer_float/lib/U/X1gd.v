(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc X1cb.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hu X1nq. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g7 X1hm.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require UbDec.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac ms_eq := cbv [mkR]; repeat first [ reflexivity | apply (f_equal (Z_to_bv 64)); lia | progress f_equal ].

Lemma swrap32_mod64_small : forall x c, -2^31 <= x + c < 2^31 ->
bv_swrap 32 (x mod 18446744073709551616 + c) = x + c.
Proof.
intros x c H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z.
replace (x mod 18446744073709551616) with (x - 18446744073709551616 * (x / 18446744073709551616))
by (pose proof (Z.div_mod x 18446744073709551616 ltac:(lia)); lia).
replace (x - 18446744073709551616 * (x / 18446744073709551616) + c + 2147483648)
with ((x + c + 2147483648) + (- 4294967296 * (x / 18446744073709551616)) * 4294967296) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Ltac br_split K :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:K; [ | ]
end;
zify_cond K; rewrite ?signed_lit_small in K by lia.
Ltac brT := let K := fresh "Kbr" in br_split K; [ try clear K | exfalso; lia ].
Ltac brF := let K := fresh "Kbr" in br_split K; [ exfalso; lia | try clear K ].

Ltac shw := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC=" pc; idtac "REGS=" R | |- ?g => idtac "GOAL=" g end.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

#[using="Type"] Lemma unpack_pair : forall b n, speex_bits_unpack_unsigned b n = (uv b n, ub b n).
Proof. intros. unfold uv, ub. destruct (speex_bits_unpack_unsigned b n); reflexivity. Qed.

Lemma land3_mod4 : forall v, Z.land v 3 = v mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Ltac fix32 := repeat match goal with |- context [bv_swrap 32 ?x] => rewrite (X1cc.swrap32_small x) by lia end.
Ltac ltb_fix := repeat match goal with |- context [?x <? ?y] =>
first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia)
| replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ] end.
Ltac ee_pos p := lazymatch p with xH => idtac | xO ?q => ee_pos q | xI ?q => ee_pos q end.
Ltac ee_zlit z := lazymatch z with Z0 => idtac | Zpos ?p => ee_pos p | Zneg ?p => ee_pos p end.
Ltac lit_fold := repeat match goal with |- context [Z_to_bv 64 ?e] =>
tryif ee_zlit e then fail else (tryif (match e with context [?x] => is_var x end) then fail else (let v := eval vm_compute in e in ee_zlit v; change e with v)) end.
Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?land3_mod4, ?UbDec.sh_land7 in K; rewrite ?signed_lit_small in K by lia; [exfalso; lia | clear K].
Ltac nt := first [ if_false_x | ntk ].
Ltac znorm := rewrite ?Z.shiftl_mul_pow2 by lia; try change (2^2) with 4; try change (2^3) with 8;
rewrite ?(Z.mod_small _ 18446744073709551616) by lia.
Ltac adv := lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => try fix32; znorm; rewrite ?UbDec.ub_ptr_guard_nonneg by lia; rewrite ?UbDec.lxor_sign_nn by lia; try ltb_fix; try lit_fold; nt
| |- _ => zstep; try fix32; znorm
end.
Ltac upto p := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail | _ => adv end).

#[using="Type"] Lemma scb_loop3 : forall (k : nat) (j ss row e inn CDB : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s0 a0 a2 s2 s3 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = ss - j -> 0 <= j < ss -> 0 <= e -> e + ss <= 40 ->
0 <= row -> row + ss <= Z.of_nat (length CD) -> u8ro rsegs m1 CDB CD -> 0x10000 <= CDB -> CDB + Z.of_nat (length CD) <= 0x1b000 ->
inn + 160 <= CDB \/ CDB + Z.of_nat (length CD) <= inn ->
0 < inn -> inn mod 4 = 0 -> inn + 160 < 2^63 -> row + ss < 2^31 ->
u32arr rsegs m1 inn cur -> length cur = 40%nat ->
munch [(inn, inn + 160)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (x0 x1 x2 x3 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp x0 x1 x2 s0 (Z_to_bv 64 inn) a0 (Z_to_bv 64 1) a2 (Z_to_bv 64 1) (Z_to_bv 64 ss) (Z_to_bv 64 0) (Z_to_bv 64 row) (Z_to_bv 64 e)
s2 s3 s4 (Z_to_bv 64 ss) (Z_to_bv 64 CDB) s7 s8 s9 s10 s11 x3 t4 t5 t6)
F2 (Z_to_bv 64 0x29e94) fc2 None m2 (seg_rom rsegs)
/\ munch [(inn, inn + 160)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 inn cur' /\ length cur' = 40%nat)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 inn) a0 (Z_to_bv 64 1) a2 (Z_to_bv 64 1) (Z_to_bv 64 j) (Z_to_bv 64 0) (Z_to_bv 64 row) (Z_to_bv 64 e)
s2 s3 s4 (Z_to_bv 64 ss) (Z_to_bv 64 CDB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x29df8) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros j ss row e inn CDB CD cur m0
ra sp gp tp t0 t1 t2 s0 a0 a2 s2 s3 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hj He0 He1 R0 R1 RO C0 C1 AP IN0 IN4 INB RB QA Lcur MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ QA) as BQ. rewrite Lcur in BQ.
assert (Hnth : nth_error CD (Z.to_nat (row + j)) = Some (nth (Z.to_nat (row + j)) CD (Z_to_bv 8 0))).
{ apply nth_error_nth'. lia. }
pose proof (u8ro_read rsegs m1 CDB CD (row + j) _ _ RO Hnth ltac:(lia) ltac:(f_equal; lia)) as RD.
pose proof (u32arr_read_nth rsegs m1 inn cur (e + j) _ QA ltac:(lia) ltac:(f_equal; lia)) as RD'.
upto 0x29e70.
zstep. zstep. clear RD RD' Hnth.
do 5 adv.
pose proof (u32arr_store_ok rsegs m1 inn cur (e + j) _ QA ltac:(lia) ltac:(f_equal; lia)) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 inn cur (e + j) v QA ltac:(lia)) as QA' end.
clear QA. store_done. try clear SOK.
zstep. if_cases K; zify_cond K.
- eapply (IH (j + 1) ss row e inn CDB CD _ m0); try eassumption; try lia. rewrite upd_length; exact Lcur.
- apply evt_done. subst ss.
do 4 eexists. do 4 eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length; exact Lcur.
Qed.
#[using="Type"] Lemma nth_upd_same : forall {X} (l : list X) i x d, (i < length l)%nat -> nth i (upd l i x) d = x.
Proof. intros X l. induction l as [|y l IH]; intros [|i] x d Hi; cbn in Hi |- *; try lia; [reflexivity|]. apply IH. lia. Qed.
#[using="Type"] Lemma nth_upd_other : forall {X} (l : list X) i j x d, i <> j -> nth j (upd l i x) d = nth j l d.
Proof. intros X l. induction l as [|y l IH]; intros [|i] [|j] x d Hij; cbn; try reflexivity; [lia|]. apply IH. lia. Qed.

Definition ind_ok (sb : Z) (n : nat) (l : list word) : Prop :=
forall j, (j < n)%nat -> exists v, nth j l (Z_to_bv 64 0) = Z_to_bv 64 v /\ 0 <= v < 2 ^ sb.
#[using="Type"] Lemma ind_ok_0 : forall sb l, ind_ok sb 0 l.
Proof. intros sb l j Hj. lia. Qed.
#[using="Type"] Lemma ind_ok_upd : forall sb n l v, ind_ok sb n l -> (n < length l)%nat -> 0 <= v < 2 ^ sb ->
ind_ok sb (S n) (upd l n (Z_to_bv 64 v)).
Proof.
intros sb n l v H Hn Hv j Hj. destruct (Nat.eq_dec j n) as [->|NE].
- exists v. split; [| exact Hv]. rewrite nth_upd_same by exact Hn. reflexivity.
- destruct (H j ltac:(lia)) as (v' & E & Hv'). exists v'. split; [| exact Hv'].
rewrite nth_upd_other by lia. exact E.
Qed.
#[using="Type"] Lemma ind_ok_other : forall sb n l i w, ind_ok sb n l -> (n <= i)%nat -> ind_ok sb n (upd l i w).
Proof.
intros sb n l i w H Hi j Hj. destruct (H j Hj) as (v & E & Hv). exists v. split; [| exact Hv].
rewrite nth_upd_other by lia. exact E.
Qed.

#[using="Type"] Lemma u8ro_read64 : forall m A ws (i : Z) w a,
u8ro rsegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof.
intros m A ws i w a Hb Hn Hi ->.
first [ pose proof (u64s_split _ _ _ Hn) as sfP_; sf_destruct 6%nat sfP_ as pre post E Hlen Eu Hlu | sf_fb; destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu) ].
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
unfold u8ro in Hb.
rewrite (bytes_at_ov_read rsegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Definition SIGN_W0 : word := Z_to_bv 64 13808036457517940736.
Definition SIGN_W1 : word := Z_to_bv 64 4584664420663164928.
#[using="Type"] Lemma sign_tbl_ro : forall m, mem_inv rsegs m -> u8ro rsegs m 0x10a70 (u64s [SIGN_W0; SIGN_W1]).
Proof.
intros m MI. unfold u8ro.
pose proof (ro_cells_bytes_at rsegs m 0x10a70 _ (ro_cells_image rsegs m 0x10a70 (u64s [SIGN_W0; SIGN_W1]) MI
ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))) as BY.
cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
Qed.
#[using="Type"] Lemma sign_tbl_read : forall m (c : bool) a, mem_inv rsegs m -> a = wa (0x10a70 + 8 * Z.b2z c) ->
ov_read_bytes rsegs m a 8 = Some (le8 (if c then SIGN_W1 else SIGN_W0)).
Proof.
intros m c a MI ->. eapply (u8ro_read64 m 0x10a70 [SIGN_W0; SIGN_W1] (Z.b2z c)); [apply sign_tbl_ro; exact MI| destruct c; reflexivity| destruct c; cbn; lia| reflexivity].
Qed.

Definition nl (P : Prop) : Prop := P.
#[using="Type"] Lemma nl_i : forall P : Prop, P -> nl P. Proof. intros P H; exact H. Qed.
#[using="Type"] Lemma nl_e : forall P : Prop, nl P -> P. Proof. intros P H; exact H. Qed.

#[using="Type"] Lemma scb_loop2 : forall (k : nat) (i ss nb sb inn CDB IND SGN nI nS : Z) (CD : list byte) (cur idl sgl : list word) (nw : nat) (m0 : mem)
(ra sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 s4 s7 s10 s11 t3 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = nb - i -> 0 <= i < nb -> 1 <= ss -> nl (ss * nb = 40) -> 1 <= sb <= 8 ->
2 ^ sb * ss <= Z.of_nat (length CD) -> u8ro rsegs m1 CDB CD -> 0x10000 <= CDB -> CDB + Z.of_nat (length CD) <= 0x1b000 ->
inn + 160 <= CDB \/ CDB + Z.of_nat (length CD) <= inn ->
u32arr rsegs m1 inn cur -> length cur = 40%nat ->
u32arr rsegs m1 IND idl -> length idl = nw -> ind_ok sb (Z.to_nat nb) idl -> nb <= Z.of_nat nw ->
u32arr rsegs m1 SGN sgl -> length sgl = nw ->
apart inn 160 IND (4 * Z.of_nat nw) -> apart inn 160 SGN (4 * Z.of_nat nw) ->
0 < inn -> inn mod 4 = 0 -> inn + 160 < 2^63 ->
nS = 2^64 - 1 - SGN -> nI = 2^64 - 1 - IND ->
rw_cells rsegs m1 (bv_unsigned s0 + -120) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 nI)] -> apart inn 160 (bv_unsigned s0 + -120) 16 ->
munch [(inn, inn + 160)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (x0 x1 x2 x3 x4 x5 x6 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp x0 x1 x2 s0 (Z_to_bv 64 inn) (Z_to_bv 64 nb) (Z_to_bv 64 1) (Z_to_bv 64 0x10a70) (Z_to_bv 64 1)
(Z_to_bv 64 nb) x4 x5 x6
s2 s3 s4 (Z_to_bv 64 ss) (Z_to_bv 64 CDB) s7 (Z_to_bv 64 SGN) (Z_to_bv 64 nS) s10 s11 x3 (Z_to_bv 64 IND) t5 t6)
F2 (Z_to_bv 64 0x29ea0) fc2 None m2 (seg_rom rsegs)
/\ munch [(inn, inn + 160)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 inn cur' /\ length cur' = 40%nat)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 inn) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 0x10a70) (Z_to_bv 64 1)
a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 ss) (Z_to_bv 64 CDB) s7 (Z_to_bv 64 SGN) (Z_to_bv 64 nS) s10 s11 t3 (Z_to_bv 64 IND) t5 t6)
F1 (Z_to_bv 64 0x29d9c) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i ss nb sb inn CDB IND SGN nI nS CD cur idl sgl nw m0
ra sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s2 s3 s4 s7 s10 s11 t3 t5 t6 F1 fc1 m1
Hk Hi Hss Hsn Hsb TBL RO C0 C1 AP QA Lcur IA Lidl IOK Hnw SA Lsgl AP1 AP2 IN0 IN4 INB ENS ENI FRS APF MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ QA) as BQ. rewrite Lcur in BQ.
pose proof (u32arr_bound _ _ _ _ IA) as BI. rewrite Lidl in BI.
pose proof (u32arr_bound _ _ _ _ SA) as BS. rewrite Lsgl in BS.
pose proof (rw_cells_bound _ _ _ _ FRS) as BF. cbn [cells_size csize Nat.add] in BF.
assert (P2 : 1 <= 2 ^ sb) by (pose proof (Z.pow_pos_nonneg 2 sb); lia).
assert (SB8 : 2 ^ sb <= 256) by (change 256 with (2 ^ 8); apply Z.pow_le_mono_r; lia).
assert (ROW : ss * i + ss <= 40).
{ pose proof (Z.mul_le_mono_nonneg_l (i + 1) nb ss ltac:(lia) ltac:(lia)) as X. rewrite (nl_e _ Hsn) in X. lia. }
assert (ROW0 : 0 <= ss * i) by (apply Z.mul_nonneg_nonneg; lia).
destruct (IOK (Z.to_nat i) ltac:(lia)) as (v & Ev & Hv).
unfold apart in AP1, AP2, APF.
pose proof (Z.mul_nonneg_nonneg v ss ltac:(lia) ltac:(lia)) as VS0.
pose proof (Z.mul_le_mono_nonneg_r (v + 1) (2 ^ sb) ss ltac:(lia) ltac:(lia)) as VS1.
rewrite Z.mul_add_distr_r, Z.mul_1_l in VS1.
pose proof (u32arr_read_nth rsegs m1 IND idl i _ IA ltac:(lia) ltac:(f_equal; lia)) as RD1.
pose proof (u32arr_read_nth rsegs m1 SGN sgl i _ SA ltac:(lia) ltac:(f_equal; lia)) as RD2.
upto 0x29db4.
zstep.
rewrite Ev, sx32_small by (unfold int31; lia).
upto 0x29de0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with |- context [Z_to_bv 64 (68208 + Z.b2z ?c * 8)] =>
pose proof (sign_tbl_read mc c _ MI ltac:(f_equal; lia)) as RD end end.
zstep. clear RD.
upto 0x29df8.
rewrite Z.lxor_nilpotent, Z.add_0_r. change (Z.b2z (0 <? 0)) with 0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(inn, inn + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (scb_loop3 (Z.to_nat ss) 0 ss (v * ss) (ss * i) inn CDB CD cur mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption.
clear MUL WML. try rename MI0 into MI.
match goal with H : u32arr rsegs _ inn ?c, L : length ?c = 40%nat |- _ => rename H into QA2; rename L into LQ2 end.
zstep. try fix32. zstep. zstep. if_cases K; zify_cond K.
- eapply (IH (i + 1) ss nb sb inn CDB IND SGN nI nS CD _ idl sgl nw m0); try eassumption; try lia.
- apply evt_done. do 7 eexists. do 4 eexists. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. assumption.
Qed.

Ltac rebits R A D bb rj Lrj OBJ bs DAT Hbs SIDE :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (R : bits_rep rsegs mc A D bb)
by (split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]);
clear OBJ DAT
end.
Ltac after_unpack b0 bb n rj Lrj OBJ bs DAT Hbs SIDE OKp OKn Hv Lbs :=
try rename MI0 into MI; rewrite (unpack_pair bb n) in *; cbn [fst snd] in *;
lazymatch goal with H : bits_rep _ _ _ _ (ub bb n) |- _ =>
destruct H as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE); unfold bits_cells in OBJ end;
lazymatch goal with H : ?v = Z_to_bv 64 (uv bb n) |- _ => subst v end;
pose proof (speex_bits_unpack_unsigned_ok bb n _ _ OKp ltac:(lia) (unpack_pair bb n)) as (OKn & Hv & _);
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b0)
by (let X := fresh in pose proof OKn as X; unfold bits_ok in X; rewrite Hbs, zlength_map_unsigned, ?ub_size in X; lia).

#[using="Type"] Lemma scb_bits_size : forall n hs sb b, sb_buf_size (scb_bits n hs sb b) = sb_buf_size b.
Proof.
induction n as [|n IH]; intros hs sb b; cbn [scb_bits]; [reflexivity|].
rewrite IH, ub_size. destruct (negb (hs =? 0)); [rewrite ub_size|]; reflexivity.
Qed.

#[using="Type"] Lemma scb_loop1 : forall (k : nat) (i nb sb hs A D IND SGN PAR nI nS p4 cnt : Z) (b0 bcur : bits_st ptr) (idl sgl : list word) (nw : nat)
(pc0 pc1 pc2 pc4 : word) (m0 : mem)
(sp gp tp s0 s1 s5 s6 t6 : word) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = nb - i -> 0 <= i < nb -> 1 <= sb <= 8 -> (hs = 0 \/ hs = 1) -> p4 = 4 * i -> cnt = nb - i ->
bits_rep rsegs m1 A D bcur -> bits_ok bcur -> sb_buf_size bcur = sb_buf_size b0 ->
ro_cells rsegs m1 PAR [C4 pc0; C4 pc1; C8 pc2; C4 (Z_to_bv 64 sb); C4 pc4] ->
PAR + 24 <= A -> PAR + 24 <= SGN ->
u32arr rsegs m1 IND idl -> length idl = nw -> ind_ok sb (Z.to_nat i) idl -> nb <= Z.of_nat nw <= 8 ->
u32arr rsegs m1 SGN sgl -> length sgl = nw -> SGN + 4 * Z.of_nat nw = IND ->
apart A BITS_SIZEOF SGN (8 * Z.of_nat nw) -> apart D (sb_buf_size b0) SGN (8 * Z.of_nat nw) ->
nS = 2^64 - 1 - SGN -> nI = 2^64 - 1 - IND ->
rw_cells rsegs m1 (bv_unsigned s0 + -120) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 nI)] ->
apart A BITS_SIZEOF (bv_unsigned s0 + -120) 16 -> apart SGN (8 * Z.of_nat nw) (bv_unsigned s0 + -120) 16 ->
munch [(A, A + BITS_SIZEOF); (SGN, SGN + 8 * Z.of_nat nw)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt5 : word)
(F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (idl' sgl' : list word),
ms' = MS (mkR xra sp gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 A) (Z_to_bv 64 PAR) (Z_to_bv 64 (4 * nb)) s5 s6 (Z_to_bv 64 0) (Z_to_bv 64 SGN) (Z_to_bv 64 nS)
(Z_to_bv 64 IND) (Z_to_bv 64 hs) xt3 (Z_to_bv 64 IND) xt5 t6)
F2 (Z_to_bv 64 0x29d88) fc2 None m2 (seg_rom rsegs)
/\ munch [(A, A + BITS_SIZEOF); (SGN, SGN + 8 * Z.of_nat nw)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2
/\ bits_rep rsegs m2 A D (scb_bits k hs sb bcur) /\ bits_ok (scb_bits k hs sb bcur)
/\ u32arr rsegs m2 IND idl' /\ length idl' = nw /\ ind_ok sb (Z.to_nat nb) idl'
/\ u32arr rsegs m2 SGN sgl' /\ length sgl' = nw)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 A) (Z_to_bv 64 PAR) (Z_to_bv 64 p4) s5 s6 (Z_to_bv 64 cnt) (Z_to_bv 64 SGN) (Z_to_bv 64 nS)
(Z_to_bv 64 IND) (Z_to_bv 64 hs) t3 t4 t5 t6)
F1 (Z_to_bv 64 0x29d30) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i nb sb hs A D IND SGN PAR nI nS p4 cnt b0 bcur idl sgl nw pc0 pc1 pc2 pc4 m0
sp gp tp s0 s1 s5 s6 t6 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 F1 fc1 m1
Hk Hi Hsb Hhs -> -> REP OK SZ PARC PA PS IA Lidl IOK Hnw SA Lsgl ADJ AP1 AP2 ENS ENI FRS APF1 APF2 MU WM MI FRM; [lia|].
assert (BS : BITS_SIZEOF = 48) by reflexivity.
pose proof (u32arr_bound _ _ _ _ IA) as BI. rewrite Lidl in BI.
pose proof (u32arr_bound _ _ _ _ SA) as BSG. rewrite Lsgl in BSG.
pose proof (ro_cells_bound _ _ _ _ PARC) as BP. cbn [cells_size csize Nat.add] in BP.
pose proof (rw_cells_bound _ _ _ _ FRS) as BF. cbn [cells_size csize Nat.add] in BF.
pose proof REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE).
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos BUFMAX _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & BUFMAX & _ & SEP) ]. unfold BITS_BUF_MAX in BUFMAX.
unfold bits_cells in OBJ. clear REP.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ DAT) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b0).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
assert (P2 : 1 <= 2 ^ sb) by (pose proof (Z.pow_pos_nonneg 2 sb); lia).
assert (SB8 : 2 ^ sb <= 256) by (change 256 with (2 ^ 8); apply Z.pow_le_mono_r; lia).
unfold apart in AP1, AP2, APF1, APF2.
cbn [scb_bits].

destruct Hhs as [Hh | Hh]; rewrite Hh; zstep.
-
if_true. cbn [Z.eqb Pos.eqb negb scb_bits].
pose proof OBJ as OBJS. pose proof DAT as DATS. pose proof Lrj as LrjS. pose proof Hbs as HbsS. pose proof SIDE as SIDES. clear OBJ DAT.
rename rj into rjS. rename bs into bsS.
upto 0x29d58.
pose proof (u32arr_store_ok rsegs _ SGN _ i _ SA ltac:(lia) ltac:(f_equal; lia)) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mq _ (le4 ?w)) _) =>
pose proof (u32arr_write rsegs mq SGN _ i w SA ltac:(lia)) as SA' end.
clear SA. store_done. try clear SOK. rename SA' into SA.
upto 0x1cc58. rewrite sx32_small by (unfold int31; lia).
rebits REP A D bcur rjS LrjS OBJS bsS DATS HbsS SIDES.
call (speex_bits_unpack_unsigned_spec A D bcur sb); [exact REP | exact OK | lia | exact MI |]. clear REP.
after_unpack b0 bcur sb rjT LrjT OBJT bsT DATT HbsT SIDET OK OKT HvT LbsT.
upto 0x29d7c.
pose proof (u32arr_store_ok rsegs _ IND _ i _ IA ltac:(lia) ltac:(f_equal; lia)) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mq _ (le4 ?w)) _) =>
pose proof (u32arr_write rsegs mq IND _ i w IA ltac:(lia)) as IA' end.
clear IA. store_done. try clear SOK. rename IA' into IA.
pose proof (ind_ok_upd sb (Z.to_nat i) _ (uv bcur sb) IOK ltac:(lia) HvT) as IOK'.
replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in IOK' by lia. clear IOK.
zstep. zstep. if_cases K; zify_cond K.
+ eapply (IH (i + 1) nb sb _ A D IND SGN PAR nI nS _ _ b0 (ub bcur sb) _ _ nw pc0 pc1 pc2 pc4 m0); try eassumption; try lia.
* split; [exists rjT; split; [exact LrjT| unfold bits_cells; exact OBJT]| split; [exists bsT; split; [exact DATT| exact HbsT]| exact SIDET]].
* rewrite ub_size. first [exact SZ | rewrite ub_size; exact SZ].
* rewrite upd_length. exact Lidl.
* rewrite upd_length. exact Lsgl.
+ apply evt_done. assert (k = 0%nat) as -> by lia. cbn [scb_bits].
replace (Z.to_nat nb) with (Z.to_nat (i + 1)) by lia.
sf_eexists 14%nat. sf_eexists 5%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [split; [exists rjT; split; [exact LrjT| unfold bits_cells; exact OBJT]| split; [exists bsT; split; [exact DATT| exact HbsT]| exact SIDET]]|].
split; [exact OKT|].
split; [exact IA|]. split; [rewrite upd_length; exact Lidl|]. split; [exact IOK'|].
split; [exact SA|]. rewrite upd_length; exact Lsgl.
-
if_false. cbn [Z.eqb Pos.eqb negb].
upto 0x1cc58.
rebits REP A D bcur rj Lrj OBJ bs DAT Hbs SIDE.
call (speex_bits_unpack_unsigned_spec A D bcur 1); [exact REP | exact OK | lia | exact MI |]. clear REP.
after_unpack b0 bcur 1 rjS LrjS OBJS bsS DATS HbsS SIDES OK OKS HvS LbsS.
upto 0x29d48.
pose proof (u32arr_store_ok rsegs _ SGN _ i _ SA ltac:(lia) ltac:(f_equal; lia)) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mq _ (le4 ?w)) _) =>
pose proof (u32arr_write rsegs mq SGN _ i w SA ltac:(lia)) as SA' end.
clear SA. store_done. try clear SOK. rename SA' into SA.
upto 0x1cc58. rewrite sx32_small by (unfold int31; lia).
rebits REP A D (ub bcur 1) rjS LrjS OBJS bsS DATS HbsS SIDES.
call (speex_bits_unpack_unsigned_spec A D (ub bcur 1) sb); [exact REP | exact OKS | lia | exact MI |]. clear REP.
after_unpack b0 (ub bcur 1) sb rjT LrjT OBJT bsT DATT HbsT SIDET OKS OKT HvT LbsT.
upto 0x29d7c.
pose proof (u32arr_store_ok rsegs _ IND _ i _ IA ltac:(lia) ltac:(f_equal; lia)) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mq _ (le4 ?w)) _) =>
pose proof (u32arr_write rsegs mq IND _ i w IA ltac:(lia)) as IA' end.
clear IA. store_done. try clear SOK. rename IA' into IA.
pose proof (ind_ok_upd sb (Z.to_nat i) _ (uv (ub bcur 1) sb) IOK ltac:(lia) HvT) as IOK'.
replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in IOK' by lia. clear IOK.
zstep. zstep. if_cases K; zify_cond K.
+ eapply (IH (i + 1) nb sb _ A D IND SGN PAR nI nS _ _ b0 (ub (ub bcur 1) sb) _ _ nw pc0 pc1 pc2 pc4 m0); try eassumption; try lia.
* split; [exists rjT; split; [exact LrjT| unfold bits_cells; exact OBJT]| split; [exists bsT; split; [exact DATT| exact HbsT]| exact SIDET]].
* rewrite ub_size. first [exact SZ | rewrite ub_size; exact SZ].
* rewrite upd_length. exact Lidl.
* rewrite upd_length. exact Lsgl.
+ apply evt_done. assert (k = 0%nat) as -> by lia. cbn [scb_bits].
replace (Z.to_nat nb) with (Z.to_nat (i + 1)) by lia.
sf_eexists 14%nat. sf_eexists 5%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [split; [exists rjT; split; [exact LrjT| unfold bits_cells; exact OBJT]| split; [exists bsT; split; [exact DATT| exact HbsT]| exact SIDET]]|].
split; [exact OKT|].
split; [exact IA|]. split; [rewrite upd_length; exact Lidl|]. split; [exact IOK'|].
split; [exact SA|]. rewrite upd_length; exact Lsgl.
Qed.

Definition cdbk_bytes (base : Z) (n : nat) : list byte :=
match image_bytes rsegs base n with Some bs => bs | None => [] end.
#[using="Type"] Lemma cdbk_ro : forall m base n, mem_inv rsegs m ->
ro_bytes_b rsegs base (cdbk_bytes base n) = true -> 0 <= base -> base + Z.of_nat (length (cdbk_bytes base n)) <= 2^64 ->
u8ro rsegs m base (cdbk_bytes base n).
Proof.
intros m base n MI RB H0 HL. unfold u8ro.
pose proof (ro_cells_bytes_at rsegs m base _ (ro_cells_image rsegs m base _ MI RB H0 HL)) as BY.
cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
Qed.
Ltac shape_ro_tac base n :=
let L := fresh "L" in
exists (cdbk_bytes base n); assert (L : length (cdbk_bytes base n) = n) by (vm_compute; reflexivity);
split; [| rewrite L; reflexivity]; apply cdbk_ro; [assumption| vm_compute; reflexivity| lia| rewrite L; cbn; lia].
#[using="Type"] Lemma shape_cb_ro : forall t m, mem_inv rsegs m ->
exists CD, u8ro rsegs m (shape_cb_addr t) CD /\ Z.of_nat (length CD) = shape_cb_size t.
Proof.
intros [| | | | | | |] m MI; cbn [shape_cb_addr shape_cb_size].
- shape_ro_tac 0x128c8 1280%nat.
- shape_ro_tac 0x12788 320%nat.
- shape_ro_tac 0x12188 1024%nat.
- shape_ro_tac 0x12048 320%nat.
- shape_ro_tac 0x11fa8 160%nat.
- shape_ro_tac 0x12dc8 640%nat.
- shape_ro_tac 0x134ec 1024%nat.
- shape_ro_tac 0x133ac 320%nat.
Qed.
#[using="Type"] Lemma shape_cb_addr_range : forall t, 0x10000 <= shape_cb_addr t /\ shape_cb_addr t + shape_cb_size t <= 0x1b000 /\ 0 < shape_cb_size t.
Proof. intros [| | | | | | |]; cbn; lia. Qed.

#[using="Type"] Lemma rodata_ro : forall x, 0x10000 <= x < 0x1b000 -> ro_addr rsegs (wa x) = true.
Proof.
intros x Hx. unfold ro_addr. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
cbn [find_segment Ubsan.M.loaded_segments Ubsan_loaded_segments Ubsan_segment_000 seg_base seg_size].
replace (Z.of_N 0x10000 <=? x) with true by (symmetry; apply Z.leb_le; lia).
replace (x + 1 <=? Z.of_N 0x10000 + Z.of_N 0xb000) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb]. reflexivity.
Qed.
#[using="Type"] Lemma wr_at_apart_ro : forall m q k c n, mem_inv rsegs m -> wr_at rsegs m q k -> 0 < k -> 0 < n ->
0x10000 <= c -> c + n <= 0x1b000 -> q + k <= c \/ c + n <= q.
Proof.
intros m q k c n MI [Hq0 [Hqk W]] Hk Hn Hc0 Hc1.
destruct (Z_lt_dec q (c + n)); [|lia]. destruct (Z_lt_dec c (q + k)); [|lia]. exfalso.
set (x := Z.max q c).
assert (Hx1 : q <= x < q + k) by lia. assert (Hx2 : c <= x < c + n) by lia.
specialize (W (x - q) ltac:(lia)). replace (q + (x - q)) with x in W by lia.
pose proof (rodata_ro x ltac:(lia)) as RO.
destruct (m (wa x)) eqn:E.
- pose proof (mem_inv_ro _ _ MI _ _ E). congruence.
- pose proof (wview_not_ro rsegs m (wa x) W E). congruence.
Qed.

Ltac thaw_rw H MUF WMF :=
eapply (rw_cells_transport rsegs _ _ _ _ _) in H;
[| exact MUF | exact WMF | cbn [disjoint_from]; rewrite ?cells_size_f32; cbn [cells_size csize Nat.add length]; repeat split; alia ].
Ltac thaw_u8 H MUF WMF :=
eapply (u8arr_transport rsegs _ _ _ _ _) in H; [| exact MUF | exact WMF | cbn [disjoint_from]; repeat split; alia ].
Ltac thaw_u32 H MUF WMF :=
eapply (u32arr_transport rsegs _ _ _ _ _) in H; [| exact MUF | exact WMF | cbn [disjoint_from]; repeat split; alia ].
Ltac thaw_ro H MUF :=
eapply (ro_cells_transport rsegs _ _ _ _ _) in H; [| exact MUF | cbn [disjoint_from cells_size csize Nat.add length]; repeat split; alia ].

#[using="Type"] Lemma lxor_ones64 : forall w, 0 <= w < 2^64 -> Z.lxor w 18446744073709551615 = 2^64 - 1 - w.
Proof. intros w Hw. rewrite lnot_mod64 by lia. unfold Z.lnot, Z.pred. symmetry. apply Z.mod_unique with (q := -1); [left; lia| lia]. Qed.
Ltac join_cells H1 H2 H :=
lazymatch type of H1 with rw_cells ?sg ?mm ?a ?c1 =>
lazymatch type of H2 with rw_cells _ _ ?b ?c2 =>
assert (H : rw_cells sg mm a (c1 ++ c2))
by (apply rw_cells_join; [exact H1 | replace (a + Z.of_nat (cells_size c1)) with b by (cbn [cells_size csize Nat.add]; lia); exact H2])
end end; cbn [app] in H.

#[using="Type"] Lemma scb_body : forall p (A D : Z) b (inn seedp PAR lo : Z) (is0 : list word) (seed0 : word) (nw : nat) (idl sgl : list word)
(fr0 : word) (j8 j16 : list byte) (CDBw : Z)
(ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s9 t3 t4 t5 t6 : word)
(sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 svra : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m m1 : mem),
scb_params_ok p ->
let ss := scb_subvect_size p in let nb := scb_nb_subvect p in let sb := scb_shape_bits p in let hs := scb_have_sign p in
let usp := bv_unsigned sp in
CDBw = shape_cb_addr (scb_shape_cb p) ->
bits_rep rsegs m1 A D b -> bits_ok b ->
u32arr rsegs m1 inn is0 -> length is0 = 40%nat ->
rw_cells rsegs m1 seedp [C4 seed0] ->
ro_cells rsegs m1 PAR (scb_par_cells p) -> PAR + 24 <= NB_GLOBALS_TOP -> NB_GLOBALS_TOP <= A ->
NB_GLOBALS_TOP <= lo -> lo + 4352 <= usp -> usp < 2^63 ->
nb <= Z.of_nat nw <= 8 ->
rw_cells rsegs m1 (usp + -128) [C8 fr0; CB 8 j8; CB 8 j16; C8 sv11; C8 sv10; C8 sv9; C8 sv8; C8 sv7; C8 sv6; C8 sv5; C8 sv4; C8 sv3; C8 sv2; C8 sv1; C8 sv0; C8 svra] ->
u32arr rsegs m1 (usp + -128 - 4 * Z.of_nat nw) idl -> length idl = nw ->
u32arr rsegs m1 (usp + -128 - 8 * Z.of_nat nw) sgl -> length sgl = nw ->
stk rsegs m1 lo (usp + -128 - 8 * Z.of_nat nw) ->
apart inn 160 lo (usp - lo) -> apart seedp 4 lo (usp - lo) ->
apart A BITS_SIZEOF lo (usp - lo) -> apart D (sb_buf_size b) lo (usp - lo) ->
apart inn 160 seedp 4 -> apart inn 160 A BITS_SIZEOF -> apart inn 160 D (sb_buf_size b) ->
apart seedp 4 A BITS_SIZEOF -> apart seedp 4 D (sb_buf_size b) ->
inn mod 4 = 0 -> 0 < inn ->
munch [(lo, usp); (inn, inn + 160); (seedp, seedp + 4); (A, A + BITS_SIZEOF)] m m1 -> wmono rsegs m m1 ->
mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (innov_unquant_post (InnovSplitCbShapeSignUnquant p) A D b inn seedp lo svra sp gp tp sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 m)
(MS (mkR ra (Z_to_bv 64 (usp + -128 - 8 * Z.of_nat nw)) gp tp t0 t1 t2 sp (Z_to_bv 64 inn)
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 A) (Z_to_bv 64 PAR) s4 (Z_to_bv 64 ss) (Z_to_bv 64 CDBw) (Z_to_bv 64 nb)
(Z_to_bv 64 (usp + -128 - 8 * Z.of_nat nw)) s9 (Z_to_bv 64 (usp + -128 - 4 * Z.of_nat nw)) (Z_to_bv 64 hs) t3 t4 t5 t6)
F1 (Z_to_bv 64 0x29d1c) fc1 None m1 (seg_rom rsegs)).
Proof.
intros until m1. intros POK ss nb sb hs usp -> REP OK INA LIS SEEDC PARC PARB GLA GLO LO SP63 NW FR IA Lidl SA Lsgl STK
AQ1 AQ2 AQ3 AQ4 AQ5 AQ6 AQ7 AQ8 AQ9 IN4 IN0 MU WM MI FRM.
first [ sf_destruct 6%nat POK as SS1 NB1 SN40 SB TBL HS | sf_fb; destruct POK as (SS1 & NB1 & SN40 & SB & TBL & HS) ].
subst ss nb sb hs. set (ss := scb_subvect_size p) in *. set (nb := scb_nb_subvect p) in *.
set (sb := scb_shape_bits p) in *. set (hs := scb_have_sign p) in *.
pose proof (nl_i _ SN40) as SN. clear SN40.
unfold NB_GLOBALS_TOP in *. assert (BS : BITS_SIZEOF = 48) by reflexivity.
pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rsp.
subst usp.
pose proof REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE).
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos BUFMAX _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & BUFMAX & _ & SEP) ]. unfold BITS_BUF_MAX in BUFMAX.
unfold bits_cells in OBJ. clear REP.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GBd. cbn [cells_size csize Nat.add length] in GBd.
pose proof (u8arr_bound _ _ _ _ DAT) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (u32arr_bound _ _ _ _ INA) as GI. rewrite LIS in GI.
pose proof (rw_cells_bound _ _ _ _ SEEDC) as GS. cbn [cells_size csize Nat.add] in GS.
pose proof (shape_cb_addr_range (scb_shape_cb p)) as CR.
assert (P2 : 1 <= 2 ^ sb) by (pose proof (Z.pow_pos_nonneg 2 sb); lia).
assert (SB8 : 2 ^ sb <= 256) by (change 256 with (2 ^ 8); apply Z.pow_le_mono_r; lia).
unfold scb_par_cells in PARC. fold ss nb sb hs in PARC.
pose proof INA as INA'. destruct INA' as [_ WQ]. rewrite LIS in WQ.
assert (INB : inn + 160 < 2^63).
{ pose proof (wr_at_below _ _ _ _ MI WQ ltac:(cbn; lia)) as X. assert (MT : mem_top rsegs = TASK_SIZE) by reflexivity.
rewrite MT in X. assert (TS : TASK_SIZE < 2^63) by (unfold Z.lt; vm_compute; reflexivity). cbn in X. lia. }
clear WQ.

zstep. zstep. zstep. rewrite !lxor_ones64 by lia.
zstep. zstep.
apply rw_cells_uncons in FR as [FR0 FRr]. cbn [csize] in FRr.
replace (bv_unsigned sp + -128 + Z.of_nat 8) with (bv_unsigned sp + -120) in FRr by lia.
lazymatch type of FRr with rw_cells _ _ _ (?c1 :: ?c2 :: ?rest) => change (c1 :: c2 :: rest) with ([c1; c2] ++ rest) in FRr end.
apply rw_cells_app in FRr as [FRS FRT]. cbn [cells_size csize Nat.add] in FRT.
replace (bv_unsigned sp + -120 + Z.of_nat 16) with (bv_unsigned sp + -104) in FRT by lia.
pose proof FRS as FRSh.
pose proof (conj FR0 (conj FRSh (conj FRT (conj INA (conj SEEDC I))))) as HIDE1. clear FR0 FRSh FRT INA SEEDC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(A, A + BITS_SIZEOF); (bv_unsigned sp + -128 - 8 * Z.of_nat nw, bv_unsigned sp + -128 - 8 * Z.of_nat nw + 8 * Z.of_nat nw)] mc) as MUL;
pose proof (wmono_refl rsegs mc) as WML;
call (scb_loop1 (Z.to_nat nb) 0 nb sb hs A D (bv_unsigned sp + -128 - 4 * Z.of_nat nw) (bv_unsigned sp + -128 - 8 * Z.of_nat nw) PAR _ _ _ _ b b idl sgl nw
_ _ _ _ mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try reflexivity.
all: try (apply ind_ok_0). all: try (unfold apart; alia).
{ split; [exists rj; split; [exact Lrj| unfold bits_cells; exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]. }
rename MUL into MUL1. rename WML into WML1. try rename MI0 into MI.
first [ sf_destruct 6%nat HIDE1 as FR0 FRSh FRT INA SEEDC _ | sf_fb; destruct HIDE1 as (FR0 & FRSh & FRT & INA & SEEDC & _) ].
try clear FRS. rename FRSh into FRS.
thaw_rw FR0 MUL1 WML1. thaw_rw FRS MUL1 WML1. thaw_rw FRT MUL1 WML1.
thaw_u32 INA MUL1 WML1. thaw_rw SEEDC MUL1 WML1. clear MUL1 WML1.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -128 - 4 * Z.of_nat nw) ?l, L : length ?l = nw, K : ind_ok sb _ ?l |- _ =>
rename H into IA2; rename L into Lidl2; rename K into IOK2 end.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -128 - 8 * Z.of_nat nw) ?l, L : length ?l = nw |- _ => rename H into SA2; rename L into Lsgl2 end.
match goal with H : bits_rep rsegs _ A D ?bb, K : bits_ok ?bb |- _ => rename H into REP2; rename K into OK2 end.

upto 0x29d9c.
ltb_fix. cbn [Z.b2z].
destruct (shape_cb_ro (scb_shape_cb p) _ MI) as (CD & CRO & LCD).
pose proof INA as INA'. destruct INA' as [_ WQ]. rewrite LIS in WQ.
destruct CR as (CR1 & CR2 & CR3).
pose proof (wr_at_apart_ro _ inn _ (shape_cb_addr (scb_shape_cb p)) (shape_cb_size (scb_shape_cb p)) MI WQ ltac:(lia) CR3 CR1 CR2) as RA. clear WQ.
pose proof FRS as FRSh.
pose proof (conj FR0 (conj FRSh (conj FRT (conj SEEDC (conj REP2 I))))) as HIDE2. clear FR0 FRSh FRT SEEDC REP2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(inn, inn + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (scb_loop2 (Z.to_nat nb) 0 ss nb sb inn (shape_cb_addr (scb_shape_cb p)) (bv_unsigned sp + -128 - 4 * Z.of_nat nw) (bv_unsigned sp + -128 - 8 * Z.of_nat nw)
_ _ CD _ _ _ nw mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try exact SN. all: try eassumption.
all: try (rewrite LCD; exact TBL). all: try (unfold apart; alia).
rename MUL into MUL2. rename WML into WML2. try rename MI0 into MI.
first [ sf_destruct 6%nat HIDE2 as FR0 FRSh FRT SEEDC REP2 _ | sf_fb; destruct HIDE2 as (FR0 & FRSh & FRT & SEEDC & REP2 & _) ].
try clear FRS. rename FRSh into FRS.
thaw_rw FR0 MUL2 WML2. thaw_rw FRS MUL2 WML2. thaw_rw FRT MUL2 WML2. thaw_rw SEEDC MUL2 WML2.
destruct REP2 as ((rj2 & Lrj2 & OBJ2) & (bs2 & DAT2 & Hbs2) & SIDE2).
unfold bits_cells in OBJ2. thaw_rw OBJ2 MUL2 WML2.
assert (Lbs2 : Z.of_nat (length bs2) = sb_buf_size b).
{ pose proof OK2 as X. unfold bits_ok in X. rewrite Hbs2, zlength_map_unsigned, scb_bits_size in X. lia. }
thaw_u8 DAT2 MUL2 WML2. clear MUL2 WML2.
match goal with H : u32arr rsegs _ inn ?c, L : length ?c = 40%nat |- _ => rename H into INA3; rename L into LIS3 end.
join_cells FRS FRT FRr. join_cells FR0 FRr FR. clear FR0 FRS FRT FRr.
zstep. do 13 zstep. zstep.

pose proof (f32_of_u32arr rsegs _ _ _ SA2) as SGC. pose proof (f32_of_u32arr rsegs _ _ _ IA2) as IDC.
eapply stk_release in SGC; [| exact STK | lia]. clear STK.
rewrite cells_size_f32, Lsgl2 in SGC.
eapply stk_release in IDC; [| replace (bv_unsigned sp + -128 - 4 * Z.of_nat nw) with (bv_unsigned sp + -128 - 8 * Z.of_nat nw + Z.of_nat (4 * nw)) by lia; exact SGC | lia].
clear SGC. rewrite cells_size_f32, Lidl2 in IDC.
eapply stk_release in FR; [| replace (bv_unsigned sp + -128) with (bv_unsigned sp + -128 - 4 * Z.of_nat nw + Z.of_nat (4 * nw)) by lia; exact IDC | lia].
clear IDC. cbn [cells_size csize Nat.add] in FR. replace (bv_unsigned sp + -128 + Z.of_nat 128) with (bv_unsigned sp) in FR by lia.
zstep.
apply evt_done. unfold innov_unquant_post. cbn [innov_bits].
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _, _.
split; [unfold callR; cbn [c_t0 c_t1 c_t2 c_a1 c_a2 c_a3 c_a4 c_a5 c_a6 c_a7 c_t3 c_t4 c_t5 c_t6]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|]. split; [exact FR|].
split; [apply f32_of_u32arr; exact INA3|]. split; [exact LIS3|].
split; [exact SEEDC|].
split; [| exact OK2].
split; [exists rj2; split; [exact Lrj2| unfold bits_cells; exact OBJ2]| split; [exists bs2; split; [exact DAT2| exact Hbs2]| exact SIDE2]].
Qed.

#[using="Type"] Lemma zext32_x4_shl_mod : forall x, 0 <= x < 2^30 -> Z.shiftr ((Z.shiftl x 32) mod 18446744073709551616) 30 = x * 4.
Proof.
intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. change (2^30) with 1073741824 in Hx.
rewrite Z.mod_small by (change (2^32) with 4294967296; lia).
rewrite Z.shiftr_div_pow2 by lia. change (2^32) with (4 * 1073741824). change (2^30) with 1073741824.
replace (x * (4 * 1073741824)) with (x * 4 * 1073741824) by lia. apply Z.div_mul. lia.
Qed.
#[using="Type"] Lemma zext32_id_shl_mod : forall x, 0 <= x < 2^32 -> Z.shiftr ((Z.shiftl x 32) mod 18446744073709551616) 32 = x.
Proof. intros x Hx. change 18446744073709551616 with (2^64). rewrite zb_shl_shr by lia. change (64 - 32) with 32. apply Z.mod_small. lia. Qed.

#[using="Type"] Lemma vla_al : forall n, 1 <= n <= 8 ->
Z.land (n * 4 + 15) 18446744073709551600 = (if n <=? 4 then 16 else 32).
Proof.
intros n Hn.
assert (C : n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8) by lia.
destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity.
Qed.

Ltac norm_splits :=
repeat match goal with
| |- context [Z.sub (Z.add (bv_unsigned ?r) ?c) ?d] =>
is_Zlit c; is_Zlit d; let v := eval vm_compute in (c - d)%Z in
replace (Z.sub (Z.add (bv_unsigned r) c) d) with (Z.add (bv_unsigned r) v) by lia
end.

Ltac eqaddr_exact H :=
lazymatch goal with |- stk _ _ _ ?want =>
lazymatch type of H with stk _ _ _ ?have => replace want with have by lia; exact H end end.

#[using="Type"] Lemma split_cb_shape_sign_unquant_proof : forall p, scb_params_ok p -> @innov_unquant_stmt ptr (InnovSplitCbShapeSignUnquant p).
Proof.
intros p POK. pose proof POK as sfP_; first [ sf_destruct 6%nat sfP_ as SS1 NB1 SN40 SB TBL HS | sf_fb; destruct sfP_ as (SS1 & NB1 & SN40 & SB & TBL & HS) ].
unfold innov_unquant_stmt, INNOV_DEPTH. intros until m.
intros REP OK INC LIS SEEDC PARC PARB GLA STK LO GLO SP63 AQ1 AQ2 AQ3 AQ4 AQ5 AQ6 AQ7 AQ8 AQ9 IN4 IN0 PAR8 -> -> -> -> -> -> MI FRM.
cbn iota in PAR8. destruct PAR8 as [PAR8 PAR0].
unfold innov_entry, A_split_cb_shape_sign_unquant. unfold NB_GLOBALS_TOP in *. assert (BS : BITS_SIZEOF = 48) by reflexivity.
set (ss := scb_subvect_size p) in *. set (nb := scb_nb_subvect p) in *. set (sb := scb_shape_bits p) in *. set (hs := scb_have_sign p) in *.
pose proof (nl_i _ SN40) as SN. clear SN40.
pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rsp.
pose proof REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE).
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos BUFMAX _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & BUFMAX & _ & SEP) ]. unfold BITS_BUF_MAX in BUFMAX.
unfold bits_cells in OBJ.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GBd. cbn [cells_size csize Nat.add length] in GBd.
pose proof (u8arr_bound _ _ _ _ DAT) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (rw_cells_bound _ _ _ _ INC) as GI. rewrite cells_size_f32, LIS in GI.
pose proof (rw_cells_bound _ _ _ _ SEEDC) as GS. cbn [cells_size csize Nat.add] in GS.
pose proof (ro_cells_bound _ _ _ _ PARC) as GP. cbn [scb_par_cells cells_size csize Nat.add] in GP.
unfold scb_par_cells in PARC. fold ss nb sb hs in PARC.
pose proof (munch_refl [(lo, bv_unsigned sp); (inn, inn + 160); (seedp, seedp + 4); (A, A + BITS_SIZEOF)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.

pose proof (u32arr_of_f32 rsegs _ _ _ INC) as INA. clear INC.
pose proof (conj INA (conj SEEDC (conj OBJ (conj DAT I)))) as HIDE. clear INA SEEDC OBJ DAT REP.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUF. pose proof (wmono_refl rsegs m) as WMF.
carve_frame 128%nat STK.
apply (rw_cells_split_CB rsegs _ _ [] 128%nat junk [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
cbn [app mk_CB_cells] in FR.

zstep. lstep. do 13 zstep. zstep.
upto 0x29ccc.
rewrite sx32_small by (unfold int31; lia).
upto 0x29ce0.
rewrite ?sx32_small by (unfold int31; lia).
zstep. znorm. zstep. zstep. rewrite (vla_al nb) by lia.

destruct (Z.leb_spec nb 4) as [NB4|NB4].
-
carve_frame 16%nat STK. rename FR0 into INDc.
carve_frame 16%nat STK. rename FR0 into SGNc.
carve_frame 4056%nat STK. rename FR0 into JK1.
carve_frame 8%nat STK. rename FR0 into P1.
carve_frame 8%nat STK. rename FR0 into JK2.
carve_frame 8%nat STK. rename FR0 into P2.

zstep. norm_splits. zstep. zstep. norm_splits. lstep. zstep. brF.
zstep. zstep. norm_splits. zstep. zstep. norm_splits. lstep. zstep. brF. zstep.

eapply stk_release in P2; [| exact STK | lia]. clear STK. cbn [cells_size csize Nat.add] in P2.
eapply stk_release in JK2; [| eqaddr_exact P2 | lia]. clear P2. cbn [cells_size csize Nat.add] in JK2.
eapply stk_release in P1; [| eqaddr_exact JK2 | lia]. clear JK2. cbn [cells_size csize Nat.add] in P1.
eapply stk_release in JK1; [| eqaddr_exact P1 | lia]. clear P1. cbn [cells_size csize Nat.add] in JK1. rename JK1 into STK.
lazymatch type of STK with stk _ _ _ ?hi => replace hi with (bv_unsigned sp + -128 - 8 * Z.of_nat 4) in STK by lia end.

destruct (rw_cells_CB_f32 rsegs _ _ 4%nat _ INDc) as (idl & Lidl & INDf). clear INDc.
destruct (rw_cells_CB_f32 rsegs _ _ 4%nat _ SGNc) as (sgl & Lsgl & SGNf). clear SGNc.
pose proof (u32arr_of_f32 rsegs _ _ _ INDf) as IA. pose proof (u32arr_of_f32 rsegs _ _ _ SGNf) as SA. clear INDf SGNf.
lazymatch type of IA with u32arr _ _ ?a _ => replace a with (bv_unsigned sp + -128 - 4 * Z.of_nat 4) in IA by lia end.
lazymatch type of SA with u32arr _ _ ?a _ => replace a with (bv_unsigned sp + -128 - 8 * Z.of_nat 4) in SA by lia end.

first [ sf_destruct 5%nat HIDE as INA SEEDC OBJ DAT _ | sf_fb; destruct HIDE as (INA & SEEDC & OBJ & DAT & _) ].
thaw_u32 INA MUF WMF. thaw_rw SEEDC MUF WMF. thaw_rw OBJ MUF WMF. thaw_u8 DAT MUF WMF. clear MUF WMF.
replace (Z_to_bv 64 (bv_unsigned sp + -160)) with (Z_to_bv 64 (bv_unsigned sp + -128 - 8 * Z.of_nat 4)) by (f_equal; lia).
replace (Z_to_bv 64 (bv_unsigned sp + -144)) with (Z_to_bv 64 (bv_unsigned sp + -128 - 4 * Z.of_nat 4)) by (f_equal; lia).
eapply (scb_body p A D b inn seedp PAR lo is0 seed0 4%nat idl sgl); try eassumption; try lia; try reflexivity.
all: try (split; [exists rj; split; [exact Lrj| unfold bits_cells; exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]).
-
carve_frame 32%nat STK. rename FR0 into INDc.
carve_frame 32%nat STK. rename FR0 into SGNc.
carve_frame 4024%nat STK. rename FR0 into JK1.
carve_frame 8%nat STK. rename FR0 into P1.
carve_frame 24%nat STK. rename FR0 into JK2.
carve_frame 8%nat STK. rename FR0 into P2.

zstep. norm_splits. zstep. zstep. norm_splits. lstep. zstep. brF.
zstep. zstep. norm_splits. zstep. zstep. norm_splits. lstep. zstep. brF. zstep.

eapply stk_release in P2; [| exact STK | lia]. clear STK. cbn [cells_size csize Nat.add] in P2.
eapply stk_release in JK2; [| eqaddr_exact P2 | lia]. clear P2. cbn [cells_size csize Nat.add] in JK2.
eapply stk_release in P1; [| eqaddr_exact JK2 | lia]. clear JK2. cbn [cells_size csize Nat.add] in P1.
eapply stk_release in JK1; [| eqaddr_exact P1 | lia]. clear P1. cbn [cells_size csize Nat.add] in JK1. rename JK1 into STK.
lazymatch type of STK with stk _ _ _ ?hi => replace hi with (bv_unsigned sp + -128 - 8 * Z.of_nat 8) in STK by lia end.

destruct (rw_cells_CB_f32 rsegs _ _ 8%nat _ INDc) as (idl & Lidl & INDf). clear INDc.
destruct (rw_cells_CB_f32 rsegs _ _ 8%nat _ SGNc) as (sgl & Lsgl & SGNf). clear SGNc.
pose proof (u32arr_of_f32 rsegs _ _ _ INDf) as IA. pose proof (u32arr_of_f32 rsegs _ _ _ SGNf) as SA. clear INDf SGNf.
lazymatch type of IA with u32arr _ _ ?a _ => replace a with (bv_unsigned sp + -128 - 4 * Z.of_nat 8) in IA by lia end.
lazymatch type of SA with u32arr _ _ ?a _ => replace a with (bv_unsigned sp + -128 - 8 * Z.of_nat 8) in SA by lia end.

first [ sf_destruct 5%nat HIDE as INA SEEDC OBJ DAT _ | sf_fb; destruct HIDE as (INA & SEEDC & OBJ & DAT & _) ].
thaw_u32 INA MUF WMF. thaw_rw SEEDC MUF WMF. thaw_rw OBJ MUF WMF. thaw_u8 DAT MUF WMF. clear MUF WMF.
replace (Z_to_bv 64 (bv_unsigned sp + -192)) with (Z_to_bv 64 (bv_unsigned sp + -128 - 8 * Z.of_nat 8)) by (f_equal; lia).
replace (Z_to_bv 64 (bv_unsigned sp + -160)) with (Z_to_bv 64 (bv_unsigned sp + -128 - 4 * Z.of_nat 8)) by (f_equal; lia).
eapply (scb_body p A D b inn seedp PAR lo is0 seed0 8%nat idl sgl); try eassumption; try lia; try reflexivity.
all: try (split; [exists rj; split; [exact Lrj| unfold bits_cells; exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]).
Qed.
End F.
