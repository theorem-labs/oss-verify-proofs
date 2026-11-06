(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import MM_syscalls WStr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase AKit AKit2 ARep ARepKit ARepFrame ARefill_iface RT_stubs
F_apoison F_acache F_aalloc3 F_ammap F_aensure.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
cbn in HP. Local Ltac2 Set LiaHints.tbl := fun () => "0020>56459188277.9 56461269045.1400000400=S2HES2H12H21H".
destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
Local Ltac transport_after_call segs m m' MU WM ::=
let W := lazymatch type of MU with munch ?W _ _ => W end in
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u32arr segs m ?A2 ?xs |- _ =>
first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u64arr segs m ?A2 ?xs |- _ =>
first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : stk segs m ?loq ?hiq |- _ =>
first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
| clear H ]
| H : munch ?Wq ?mq m |- _ =>
first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
| fail 100 "callee footprint not inside caller footprint" ]
| H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
end.
Local Ltac band_lin :=
repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac aload ST8 i AEXPR :=
lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
let RD := fresh "RD" in
pose proof (u64arr_read bsegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
step; clear RD
end.
Local Ltac astore ST8 i :=
lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
let SOK := fresh "SOK" in
pose proof (u64arr_store_ok bsegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
step;
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
let S2 := fresh "STATS" in
pose proof (u64arr_write bsegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
replace (A + 8 * i)%Z with E in S2 by lia;
clear ST8; store_done; try clear SOK; rename S2 into ST8
end
end.
Local Ltac by_GC GC := rewrite ?GC; cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count cls_set_mapped_user].
Section CANSEC1. Context {rc : runConstT}.
Definition populate_entry := 0x37374.
End CANSEC1.
Notation POPULATE_STACK := 512 (only parsing).
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma size_of_class_pos : forall c, 1 <= c < K_NUM_CLASSES -> 32 <= size_of_class c <= 65536 /\ size_of_class c mod 32 = 0.
Proof.
intros c Hc. unfold K_NUM_CLASSES in Hc.
Local Ltac2 Set LiaHints.tbl := fun () => "0010=57608172620.3000004S2Hc".
assert (E : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
\/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
repeat (destruct E as [->|E]; [vm_compute; split; [split; discriminate| reflexivity] |]). subst. vm_compute. split; [split; discriminate| reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma size_formula : forall c, 17 <= c <= 30 ->
Z_to_bv 64 (Z.land ((Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 63))) 63) mod 18446744073709551616)
(Z.shiftr ((Z.shiftl 512 ((Z.shiftr (c + -16) 1) mod 64)) mod 18446744073709551616) 1)
+ Z.shiftl 512 ((Z.shiftr (c + -16) 1) mod 64)) = Z_to_bv 64 (size_of_class c).
Proof.
intros c Hc.
Local Ltac2 Set LiaHints.tbl := fun () => "0010=17784234060.3000004S2Hc".
assert (E : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
repeat (destruct E as [->|E]; [apply f_equal; vm_compute; reflexivity|]). subst. apply f_equal. vm_compute. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma m_divu_lit : forall x y, 0 <= x < 2^64 -> 0 < y < 2^64 ->
mul_div M_DIVU (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
intros x y Hx Hy. unfold mul_div. Local Ltac2 Set LiaHints.tbl := fun () => "0030=16680828220.531332194325.55744833145.5 00000400800<S2HyS2HyS2Hx".
rewrite (unsigned_lit y) by lia.
replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
apply bv_eq. rewrite bv_divu_unsigned, !unsigned_lit; [reflexivity| |lia|lia].
Z.div_mod_to_equations. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma aclass_eta1 : forall r x y,
cls_set_allocated_user x (cls_set_num_freed y r) = mkAClass (c_mapped_user r) x y (c_mapped_free_array r) (c_count r).
Proof. intros [] ? ?; reflexivity. Qed.
#[using="Type"] Lemma aclass_eta2 : forall r x y z,
cls_set_allocated_user x (cls_set_num_freed y (cls_set_mapped_free_array z r)) = mkAClass (c_mapped_user r) x y z (c_count r).
Proof. intros [] ? ? ?; reflexivity. Qed.
#[using="Type"] Lemma u32arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u32arr bsegs m A [].
Proof.
intros m A H0 H1. split.
- split; [exact H0|]. Local Ltac2 Set LiaHints.tbl := fun () => "0030=11200452157.540669651966.559308586248.700000400800<S2H1S2H1S2Hi".
split; [cbn; lia|]. intros i Hi. cbn in Hi. exfalso. lia.
- split; [exact H0|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. exfalso. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition fvals (au S : Z) (n : nat) : list word :=
rev (map (fun j => Z_to_bv 64 (Z.shiftr (au + Z.of_nat j * S) 4)) (seq 0 n)).
#[using="Type"] Lemma fvals_S : forall au S n, fvals au S (Datatypes.S n) = Z_to_bv 64 (Z.shiftr (au + Z.of_nat n * S) 4) :: fvals au S n.
Proof. intros. unfold fvals. rewrite seq_S, map_app, rev_app_distr. reflexivity. Qed.
#[using="Type"] Lemma fvals_length : forall au S n, length (fvals au S n) = n.
Proof. intros. unfold fvals. rewrite length_rev, length_map, length_seq. reflexivity. Qed.
#[using="Type"] Lemma snoc_inv : forall {X} (l : list X) n, length l = Datatypes.S n -> exists l' x, l = l' ++ [x] /\ length l' = n.
Proof.
intros X l n HL. Local Ltac2 Set LiaHints.tbl := fun () => "0020=40178449815.645046957094.4000004008S2HLS2HL".
destruct l as [|y l0]; [cbn in HL; lia|].
exists (removelast (y :: l0)), (last (y :: l0) y). split; [apply app_removelast_last; discriminate|].
rewrite length_removelast by discriminate. rewrite HL. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fill_loop_spec : forall RNG (d : nat) (i ncnt A au S : Z) (jk : list word)
ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
d = Z.to_nat (ncnt - i) ->
0 <= i < ncnt -> length jk = Z.to_nat (ncnt - i) ->
u32arr bsegs m A (jk ++ fvals au S (Z.to_nat i)) ->
mem_inv bsegs m ->
0 <= au -> 0 < S -> au + ncnt * S < 2^47 -> 0 <= A -> A + 4 * ncnt < 2^47 ->
(forall k, 0 <= k < ncnt -> rng RNG (A + 4 * k) 4) ->
evtF bsegs RNG (fun ms' => exists a4' a5' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ncnt) (Z_to_bv 64 (A + 4 * ncnt)) (Z_to_bv 64 (au + ncnt * S)) a3 a4' a5' a6 a7
s2 (Z_to_bv 64 ncnt) s4 (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x37550) fc None m' (seg_rom bsegs)
/\ munch [(A, A + 4 * ncnt)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ u32arr bsegs m' A (fvals au S (Z.to_nat ncnt)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 (A + 4 * ncnt)) (Z_to_bv 64 (au + i * S)) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 ncnt) s4 (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x37530) fc None m (seg_rom bsegs)).
Proof.
intros RNG d. Local Ltac2 Set LiaHints.tbl := fun () => "00O0>10296156802.5711449825958.2026465232335.5628915217077.6134372785862.5634401868868.5039637404430.5639639647631.5540707959754.5741415745009.5442759408493.5646376088233.5746589418947.5747479230895.5448779389527.574958384495.57 49770897812.5751230606742.6651442028992.5751632219936.5752263722799.5753304293264.5653811000002.5759308664168.5963267165125.4866253248513.5466262435255.6366262435257.6168343621556.56769540254.58  8218818298.57 00000D00X01001=01R01\02102F02[02h03@03T03d04604N04f05805H05Z05j06?06O06c07707A07V07k08@08R08k09?S2HD1I3LJK4LJK'2LL1KS1I2A02AB1H2H02H42H5S2HD1I3LJK2SP2A04LJK'2LLS2HD3LJK4LJK'S2HD1I3LJK2SP4LJK'2LLS2HD1I3LJKS2HD1I3LJK2SP4LJK'2LLS2HD1I3LJK2SP4LJK'2LLS2HD1I3LJK2SP4LJK'2LLS2HD3LJK4LJK'S2HD1I3LJK2SP2AB4LJK'2LLS2HD1I3LJK4LJK'2LL1KS2HD3LJK4LJK'2LLS2HD1I3LJK2SP4LJK'S2HD1I3LJK2A02AB4LJK'2LLS2HD1I3LJK2A02AB4LJK'2LLS2HD1I3LJK4LJK'2LLS2HD3LJK4LJK'2LLS2HD1I3LJK4LJK'2LLS2HD3LJK4LJK'2LLS2HD1I3LJK2SP4LJK'2LLS2HD3LJK4LJK'2LLS2HD1I3LJK4LJK'2LL1KS2HD1I3LJK4LJK'2LL1KS2HD1I3LJKS2HD1I3LJK2A02AB4LJK'S2HD1I3LJK2A02AB4LJK'S2HD1I3LJK2A02AB4LJK'S2HD1I3LJK4LJK'2LLS2HD1I3LJK2AU2SP3AUB4LJK'S2HD1I3LJK4LJK'2LL1K".
induction d as [|d IH]; intros until m; intros HD I LJK AR MI AU SP AUB A0 AB RA; [lia|].
destruct (snoc_inv jk (Z.to_nat (ncnt - i - 1)) ltac:(rewrite LJK; lia)) as (jk' & x & -> & LJK').
pose proof (munch_refl [(A, A + 4 * ncnt)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
zstep. zstep. zstep. zstep. zstep.
setreg 15 (Z_to_bv 64 (A + 4 * (ncnt - 1 - i)))
ltac:(apply Z_to_bv_eqm; rewrite zb_lxor_ones by lia; rewrite Z.shiftl_mul_pow2 by lia; clear -I A0 AB; Z.div_mod_to_equations; lia).
assert (LL : length ((jk' ++ [x]) ++ fvals au S (Z.to_nat i)) = Z.to_nat ncnt) by (rewrite !length_app, fvals_length, LJK'; cbn; lia).
pose proof (u32arr_store_ok bsegs m A _ (ncnt - 1 - i) (wa (A + 4 * (ncnt - 1 - i))) AR ltac:(rewrite LL; lia) eq_refl) as SOK.
pose proof (RA (ncnt - 1 - i) ltac:(lia)) as RA1.
step. clear RA1.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le4 ?v)) _) =>
let E := lazymatch a with wa ?E => E | Z_to_bv _ ?E => E end in
pose proof (u32arr_write bsegs m A _ (ncnt - 1 - i) v AR ltac:(rewrite LL; lia)) as AR2;
replace (A + 4 * (ncnt - 1 - i))%Z with E in AR2 by lia
end.
replace (upd ((jk' ++ [x]) ++ fvals au S (Z.to_nat i)) (Z.to_nat (ncnt - 1 - i)) (Z_to_bv 64 (Z.shiftr (au + i * S) 4)))
with (jk' ++ fvals au S (Z.to_nat (i + 1))) in AR2.
2:{ rewrite <- app_assoc. rewrite upd_firstn_skipn by (rewrite app_assoc, LL; lia).
replace (Z.to_nat (ncnt - 1 - i)) with (length jk') by lia.
rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
replace (Datatypes.S (length jk')) with (length (jk' ++ [x])) by (rewrite length_app; cbn; lia).
rewrite app_assoc, skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app].
replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) by lia. rewrite fvals_S.
f_equal. f_equal. f_equal. f_equal. f_equal. lia. }
clear AR. store_done. try clear SOK.
zstep. setreg 12 (Z_to_bv 64 (au + (i + 1) * S)) ltac:(f_equal; lia).
step. if_cases K; zify_cond K.
-
try rewrite Z.mod_small in K by lia.
eapply evtF_mono.
{ eapply (IH (i + 1) ncnt A au S jk'); try eassumption; try lia. }
cbv beta. intros ms' (a4' & a5' & m' & -> & MU2 & WM2 & MI2 & AR3).
exists a4', a5', m'. split; [reflexivity|].
split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
split; [exact MI2| exact AR3].
-
try rewrite Z.mod_small in K by lia. assert (EI : i + 1 = ncnt) by lia.
apply evtF_done. rewrite EI in AR2 |- *. eexists _, _, _. split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|].
destruct jk' as [|y jk'']; [| exfalso; cbn in LJK'; lia]. cbn [app] in AR2. exact AR2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition pop_after {R} (c : Z) (k : astate -> bool -> AM R) (st1 : astate) : AM R :=
let size := size_of_class c in
let r1 := get_cls st1 c in
let new_cnt := (c_mapped_user r1 - c_allocated_user r1) / size in
let total_freed := c_num_freed r1 + new_cnt in
ensure_free_array st1 c total_freed (fun st2 ok =>
if negb ok then k st2 false else
let r2 := get_cls st2 c in
k (put_cls c (cls_set_allocated_user (c_allocated_user r2 + new_cnt * size) (cls_set_num_freed total_freed r2)) st2) true).
#[using="Type"] Lemma populate_unfold : forall {R} st c req (k : astate -> bool -> AM R),
populate_free_array st c req k =
(let size := size_of_class c in let r := get_cls st c in
let total_user := c_allocated_user r + req * size in
if total_user <=? c_mapped_user r then pop_after c k st else
let ums := rup (total_user - c_mapped_user r) K_USER_MAP in
if K_FREEARR_OFF <? c_mapped_user r + ums then aundef_ (UCheck 705) (k st false)
else let beg := region_beg st c + c_mapped_user r in
ev (AMmap beg ums PROT_RW F_FIXED) (fun a =>
if negb (fixed_answer_ok beg a) then aundef_ UBadAnswer (k st false)
else if is_err a then k st false
else pop_after c k (put_cls c (cls_set_mapped_user (c_mapped_user r + ums) r) st))).
Proof. intros. reflexivity. Qed.
Definition tail_ret (L : alayout) (RNG : footprint) (sp : word) (st st1 : astate) (c lo : Z) (m1 : amem)
(st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
let r1 := get_cls st1 c in let S := size_of_class c in
let FA := afreearr L c in let RI := aregion_info L c in
let mu1 := c_mapped_user r1 in let au := c_allocated_user r1 in let nf := c_num_freed r1 in let mfa := c_mapped_free_array r1 in
let ncnt := (mu1 - au) / S in
fp_le RNG RNG' /\
exists mfa' sj',
( (4 * (nf + ncnt) <= mfa /\ mfa' = mfa /\ RNG' = RNG)
\/ (mfa < 4 * (nf + ncnt) /\ mfa' = rup (4 * (nf + ncnt)) K_FREEARR_MAP
/\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
/\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
/\ 4 * (nf + ncnt) <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
/\ u32arr bsegs m' (FA + 4 * nf) (fvals au S (Z.to_nat ncnt))
/\ junk_at m' (FA + 4 * (nf + ncnt)) (mfa' - 4 * (nf + ncnt))
/\ st2 = put_cls c (mkAClass mu1 (au + ncnt * S) (nf + ncnt) mfa' (c_count r1)) st
/\ munch [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp);
(FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
(al_t L + 2800, al_t L + 3168); (RI + 16, RI + 56); (RI + 68, RI + 69)]%Z m1 m'
/\ wmono bsegs m1 m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' (RI + 16)
[C8 (Z_to_bv 64 (nf + ncnt)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 (au + ncnt * S)); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 mu1); C8 (Z_to_bv 64 0)]
/\ rw_cells bsegs m' (RI + 68) [C1 (Z_to_bv 8 0)]
/\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
/\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
/\ m3_cells L m'.
#[using="Type"] Lemma pop_tail_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
(rav sp gp tp t0 t1 t2 s0v s1v a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(rax s1x s3x s6x a1x a2x a4x a5x : word)
(F : bvmap 5 word) fc (m1 : amem) (L : alayout) (st st1 : astate) (c lo : Z) (sj : list word) (fj : list byte),
let r1 := get_cls st1 c in let S := size_of_class c in
let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
let mu1 := c_mapped_user r1 in let au := c_allocated_user r1 in let nf := c_num_freed r1 in let mfa := c_mapped_free_array r1 in
stk bsegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
mem_inv bsegs m1 -> tp = Z_to_bv 64 ATP ->
rw_cells bsegs m1 (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
m3_cells L m1 ->
rw_cells bsegs m1 (RI + 16)
[C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu1); C8 (Z_to_bv 64 0)] ->
rw_cells bsegs m1 (RI + 68) [C1 (Z_to_bv 8 0)] ->
u64arr bsegs m1 (al_t L + 2800) sj -> length sj = 46%nat ->
rw_cells bsegs m1 (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
azero m1 (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
(forall r', put_cls c r' st1 = put_cls c r' st) -> a_space_beg st1 = al_space_beg L ->
1 <= c < K_NUM_CLASSES ->
0 <= au <= mu1 -> mu1 <= K_FREEARR_OFF -> au mod S = 0 ->
0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
(al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
(al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
(al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
rng RNG (FA + 4 * nf) (mfa - 4 * nf) ->
AIMG_HI <= al_ctx L ->
iclr (al_t L) 4096 ->
(forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
tail_ret L RNG sp st st1 c lo m1 st2 RNG' m' ->
implS bsegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
(MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc rav) fc None m' (seg_rom bsegs))) ->
evtF bsegs RNG (fun ms' => implS bsegs RNG (aembed ATOP (pop_after c k st1)) (epostF Q) ms')
(MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RI) s1x (Z_to_bv 64 AINSTANCE) a1x a2x (Z_to_bv 64 au) a4x a5x a6 a7
(Z_to_bv 64 RB) s3x (Z_to_bv 64 mu1) (Z_to_bv 64 S) s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x374e8) fc None m1 (seg_rom bsegs)).
Proof.
intros until fj. cbv zeta.
intros ST CEIL LO MI TP FR MC REG EXH STATS LSJ FJ AZF PUTEQ SBE HC MU MUX AUM NF NFA MFA MFAM
SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP RIMG RSTK RCTX RT RRI RFJ CXI TIC KONT. band_lin.
box TCX. box SCX. box TSP.
pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
change (2^37) with 137438953472 in *.
word_range sp SPR.
pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
set (S := size_of_class c) in *.
set (mu1 := c_mapped_user (get_cls st1 c)) in *. set (au := c_allocated_user (get_cls st1 c)) in *.
set (nf := c_num_freed (get_cls st1 c)) in *. set (mfa := c_mapped_free_array (get_cls st1 c)) in *.
assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
rewrite RIE in REG, EXH, RRI |- *. rewrite RBE. rewrite FAE in FJ, AZF, RFJ.
set (ncnt := (mu1 - au) / S).
assert (NC : 0 <= ncnt /\ ncnt * S <= mu1 - au /\ S * nf <= au /\ 4 * (nf + ncnt) <= 469762048).
{ subst ncnt. clear -MU MUX SZ NF NFA AUM. Z.div_mod_to_equations. nia. }
destruct NC as (NC0 & NC1 & NC2 & NC3).
pose proof (munch_refl [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp)]%Z m1) as MUN.
pose proof (wmono_refl bsegs m1) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "0220?10011396056.15410011800560.8  1047820382.122 11449825958.24 11807744665.25 11807744665.28 12367362435.17412588978415.12215868313659.33 16840761955.12217776320431.17418996607512.9  19617313304.12219699687380.12220077088535.7  20661731462.19 21148432843.9  21321497359.16421918414723.17522223432586.15322264047035.26 22706556809.13 2457667210.8   25065190167.15 25065190167.25 25071629079.17625071629079.17925157604214.12225204913932.17 25671044393.17925878270254.17526494647592.17626494647592.17926496924968.18 26496924968.19 26626369225.12 26630220530.7  26774792334.12 27019211341.17527080574928.17627392054441.16427392054441.17827720211314.8  28573892092.17 29954546818.17830943742742.12930952909723.16730985182006.12336115622446.17536423735576.16736476002851.1223650812240.176 36993589379.17637966830910.12938512504620.17938524084430.4  38559484822.7  38672940819.17538672940828.12638672940829.17139372028142.17639417581631.1223945979267.175 39758838.15    41018445754.17941422282358.15641809558659.17441853125.15    42831019478.17643060403331.17643146092179.17743987951406.17544085337631.6  44478759382.25 45652632450.16545652632450.17947068567158.17647301160366.17648187556003.17648320450459.1794847493603.176 49058487571.17349343544633.1664955647451.172 50372678712.4  5060919171.18  51425718543.17551481786499.17651678667183.17452203974527.17552569147371.28 52569147371.29 52605708918.7  52642596093.15 53708791826.5  53767577775.1745378322263.179 54106309066.12254270591515.16454270591515.17854547327141.7  55816980214.12755816980214.17255816980214.17656170256219.122563227834.179  58827996926.8  59308628566.12 59403314721.17760223348125.17661086706081.17361622553569.8  61913402812.3  61917199020.17362729283214.4  63235321900.17363743784865.17563743784878.12663743784879.17164130211677.12264295209551.17264302934340.15464303324524.8  6504785026.180 65593145730.174760586265.167  7795890457.179 7937143714.7   8806423751.17  9689982781.3   00000<00D00L00X00m01H01M01U02@02E02M02S02T02Z02_03003403D03I03N03d03h03i03o04A04F04K04P04_04d04l05105605E05Z05e06006>06?06D06I06N06X06e06j07=07T07c07k08308708<08A08I08N08O08T08U08V08W08_08g08l09409<09A09F09O09W09\09]09e09f0:80:=0:B0:G0:O0:T0:U0:Z0:[0:`0;;0;<0;J0;O0;T0;\0;a0<@0<o0=60=?0=C0=K0=P0=U0=V0=W0=\0=]0=b0=g0=h0>00>10>90>>0>R0>W0>X0>\0>d0>e0>m0?20?30?80?=0?E0?M0?Q0?V0?[0@90@M0@T0@`0@dS2MU3MUX3LWSS2MU3MUXS3CX12T1S1H2H02H42H5S4CEIL2LO2HC3SP24NEWBS2HC2NF3MFA3NC04NEWB4NEWM1YS3LWSS2NF3MFAS2HC2NF3MFA3SP13SP24NEWB1H2H02H42H52H94NEWMS3SP2S2LO3LWSS4NEWBFS4MFAMS3NCPS4NEWB3Hkk2Hq3HI4S2WFS2NF3NC33LWS3NCPS3LWSS3LWSS2HC2NF3SP13NC04NEWB1YS2HxSS2HC1YS2HC3MFA4NEWB4NEWMS3LWSS3LWSS3SP1S2HC3SP24NEWB1HS3LWSS2LO3LWSS3LWSS3LWSS2HC2NF3SP13SHTS2HC2NF3SP14SHF24NEWBS2HC2NF3SP1S2HC2NF3SP1S2HC3MFA3SP21HFS3LWSS3LWSS3LWSS3MFA4NEWMS3NC04NEWB2HxS3LWSS2MU3MUX2SZ3NC03NC1S2MU3MUX2SZ3NC03NC13LWSS4CEIL2LO3SPR1HS2LO3LWSS2LO3LWSS2HCS3LWSS3LWSS2MU3MUXS3LWSSS3MFAFFFS3LWS2HBS2NF3NC0S3LWSS3Hkk2LES3LWS2HBS3LWSS3LWSS3Hkk3LO4S3LWS2HBS3LWSFS2LO3LWSSS4CEIL2HC3SP24NEWBS3LWSS3LWSS3LWSS3LWS2HBS3LWSFS3LWSFS3LWSS3MUX2NF2SZ3NC03NC13NC23LWSSS4MFAM1H2H02H4S3LWSS3LWSS2LO3LWSS3LWSS4CEIL2LO2HC3SP22T14NEWB4SHF21HS4CEIL2LO2HC3SP13SP22T14NEWB4SHF21Y2NF3MFA4NEWMS2MU2K2S3MUX3NC1S2MUS2LO3LWSS3LWSS3NC3FFS3NC0SS3LWSS3LWSSS3LWS2HBSS3NC12K3S3LWSS4CEIL2LO2HC3SP23LWSS3LWSSS2LOS2LO3LWSSS2LO3LWSS3LWSSS3LWSS3SP3S2SZ3LWSS2SZ3LWSS2SZS3LWSS3LWSS2MU3MUX2NF2SZ3NC03NC13NC23LWSS4CEIL2LO2HC3SP23LWSS2SZ2K2S3MFA3NC02HxS2SZ".
step.
zstep.
step.
setreg 19 (Z_to_bv 64 ncnt) ltac:(subst ncnt; symmetry; apply m_divu_lit; clear -MU MUX SZ; lia).
zstep. step. step. step.
step.
apply evtF_done. unfold pop_after. cbv zeta. fold S. fold mu1 au nf. fold ncnt.
name_sp sp (-64).
eapply ensure_spec with (lo := lo) (L := L).
all: try lazymatch goal with
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
| |- stk _ _ _ _ => rewrite Hsp; eassumption
| |- ATOP <= _ => atop_facts; exact CEIL
| |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
| |- mem_inv _ _ => assumption
| |- m3_cells _ _ => exact MC
| |- rw_cells _ _ (aregion_info _ _ + 16) _ => rewrite RIE; exact REG
| |- u64arr _ _ _ _ => exact STATS
| |- length _ = _ => exact LSJ
| |- azero _ _ _ => rewrite FAE; exact AZF
| |- rng_aimg _ => exact RIMG
| |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
| |- rng _ (aregion_info _ _) _ => rewrite RIE; exact RRI
| |- rng _ _ _ => first [assumption | solve_rng]
| |- @eq word _ _ => first [reflexivity | exact TP | rewrite ?RIE, ?RBE; reflexivity]
| |- a_space_beg _ = _ => exact SBE
| |- boxed _ => assumption
| |- _ \/ _ => first [ub TCX; exact Y | ub SCX; exact Y | ub TSP; exact Y]
end.
all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
clear KONT; fold mfa; lia).
intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ER.
unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP in ER. cbv zeta in ER. fold mfa nf au mu1 in ER. rewrite FAE, RIE in ER.
destruct ER as (FPLE & new & sj' & DISJ & NEWB & NEWM & NEWMOD & MU2 & WM2 & MI2 & ST2 & REG2 & STATS2 & LSJ2 & AZ2 & MC2).
box DISJ. unname_sp.
apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFJ.
assert (SHF : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
/\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (new - mfa) <= 0x10007fff8000).
{ rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
destruct SHF as [SHF1 SHF2].
xport FR MU2 WM2 ltac:(clear -SPR CEIL LO SHF1 SHF2 SP1 SP2 HC MFA NF NEWB NEWM T0 T1; lia).
xport EXH MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SHF1 SHF2 SP1 SP2 HC MFA NF NEWB NEWM T0 T1 Y; lia).
xport FJ MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SHF1 SHF2 SP1 SP2 HC MFA NF NEWB NEWM T0 T1 Y; lia).
clear ST MI STATS LSJ REG AZF.
pose proof MC2 as MC0. destruct MC0 as (PC2 & RC2 & TI2 & TK2 & T882 & TSD2 & CT2 & ISB2 & IREL2 & ISE2 & IPRE2). unfold ATP88, ATSD in T882, TSD2.
clear TI TK T88 TSD CT ISB IREL ISE IPRE PC RC.
assert (FALL : junk_at m2 (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) (4 * ncnt + (new - 4 * nf - 4 * ncnt))).
{ replace (4 * ncnt + (new - 4 * nf - 4 * ncnt)) with (new - 4 * nf) by (clear; lia).
with_box DISJ ltac:(destruct DX as [(LE & Enew & _ & _)|(LT & Enew & _ & ZNEW & _)];
[ exists fj; rewrite Enew; exact FJ
| eexists;
replace (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
with (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + Z.of_nat (Z.to_nat (mfa - 4 * nf))) in ZNEW by (clear -MFA NF; lia);
pose proof (cb_app m2 _ _ _ _ _ FJ ZNEW) as CA;
replace (Z.to_nat (mfa - 4 * nf) + Z.to_nat (new - mfa))%nat with (Z.to_nat (new - 4 * nf)) in CA by (clear -MFA NF NEWM; lia);
exact CA ]). }
destruct (junk_split m2 _ _ _ FALL ltac:(clear -NC0; lia) ltac:(clear -NEWB; lia)) as [[bsw FW] JR]. clear FALL.
pose proof (u8arr_of_rw_cells bsegs m2 _ _ _ FW) as U8.
assert (LBS : length bsw = (4 * Z.to_nat ncnt)%nat).
{ destruct FW as [[WF _] _]. cbn in WF. clear -WF NC0. lia. }
destruct (u32arr_of_u8arr bsegs m2 _ bsw (Z.to_nat ncnt) U8 LBS) as (ws & LWS & _ & AR). clear U8 FW LBS bsw.
cbn [negb].
replace (ret_pc (Z_to_bv 64 226568)) with (Z_to_bv 64 226568 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
iprefix.
step. if_lit.
step.
lazymatch goal with |- evtF _ _ ?P _ =>
assert (FIN : forall m3 (s1y a0y a1y a2y a4y a5y : word),
munch [(al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf, al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * ncnt)]%Z m2 m3 ->
wmono bsegs m2 m3 -> mem_inv bsegs m3 ->
u32arr bsegs m3 (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) (fvals au S (Z.to_nat ncnt)) ->
evtF bsegs RNG' P
(MS (mkR (Z_to_bv 64 0x37508) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2'
(Z_to_bv 64 (al_space_beg L + 137438953472 + c * 128)) s1y a0y a1y a2y (Z_to_bv 64 au) a4y a5y a6' a7'
(Z_to_bv 64 (al_space_beg L + c * 4294967296)) (Z_to_bv 64 ncnt) (Z_to_bv 64 (mu1 - au)) (Z_to_bv 64 S)
s6x s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x37550) fc None m3 (seg_rom bsegs)))
end.
{ intros m3 s1y a0y a1y a2y a4y a5y MU3x WM3 MI3 AR3.
xport FR MU3x WM3 ltac:(clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM NC0; lia).
xport EXH MU3x WM3 ltac:(clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM NC0; lia).
xport REG2 MU3x WM3 ltac:(clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM NC0; lia).
xport STATS2 MU3x WM3 ltac:(rewrite LSJ2; ub TSP; clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM NC0 T0 T1 Y; lia).
pose proof (stk_transport_disjoint bsegs _ m2 m3 _ _ ST2 MU3x WM3 ltac:(cbn [disjoint_from]; clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM NC0; lia)) as ST3.
clear ST2.
assert (MU3 : munch [(al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf, al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * ncnt);
(al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56);
(al_space_beg L + 137438953472 + c * 128 + 68, al_space_beg L + 137438953472 + c * 128 + 69)]%Z m2 m3).
{ eapply munch_weaken; [| exact MU3x]. unfold sub_fp; cbn [outside]; clear -NEWB NC0; intros x Hx; lia. }
clear MU3x.
step.
zstep.
step.
zstep. zstep.
snapshot [(al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56);
(al_space_beg L + 137438953472 + c * 128 + 68, al_space_beg L + 137438953472 + c * 128 + 69)]%Z MUf WMf.
box STATS2. box AR3.
step. step.
step. if_cases K3; zify_cond K3. { exfalso. clear -K3 NC1 NC0 MU MUX SZ. rewrite ?unsigned_lit in K3 by lia. lia. }
step. step. step. if_lit.
step.
step. step.
do 10 step.
carry STATS2 MUf WMf ltac:(rewrite LSJ2; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia).
carry AR3 MUf WMf ltac:(rewrite fvals_length; clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM NC0; lia).
lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -64) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
rename MU3 into MU24. clear MUf. rename WM3 into WM24. clear WMf.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m4 _) =>
assert (MU14 : munch [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp);
(al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf, al_space_beg L + c * 4294967296 + 3758096384 + new);
(shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa), shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (new - mfa));
(al_t L + 2800, al_t L + 3168);
(al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56);
(al_space_beg L + 137438953472 + c * 128 + 68, al_space_beg L + 137438953472 + c * 128 + 69)]%Z m1 m4);
[ eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU24]]; unfold sub_fp; cbn [outside]; clear -NEWB NC0 MFA NF; intros x Hx; lia |]
end.
pose proof (wmono_trans _ _ _ _ WM2 WM24) as WM14.
assert (W24OK : Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
[(al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf, al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * ncnt);
(al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56);
(al_space_beg L + 137438953472 + c * 128 + 68, al_space_beg L + 137438953472 + c * 128 + 69)]%Z).
{ ub SCX. unfold AIMG_HI, AIMG_LO. do 3 (apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX0 CX1 SP1 SP2 HC MFA NF NEWB NC0 Y; lia |]). apply Forall_nil. }
assert (ST2EQ : put_cls c (cls_set_allocated_user (c_allocated_user (get_cls st2 c) + ncnt * S) (cls_set_num_freed (nf + ncnt) (get_cls st2 c))) st2
= put_cls c (mkAClass mu1 (au + ncnt * S) (nf + ncnt) new (c_count (get_cls st1 c))) st).
{ with_box DISJ ltac:(destruct DX as [(LE & Enew & Est2 & _)|(LT & Enew & Est2 & _)]; rewrite Est2;
[ rewrite PUTEQ, aclass_eta1, Enew; reflexivity
| rewrite get_cls_put_cls_eq, put_cls_put_cls, PUTEQ, aclass_eta2; reflexivity ]). }
apply evtF_done. rewrite ST2EQ. eapply KONT.
unfold tail_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold S mu1 au nf mfa. fold ncnt. rewrite FAE, RIE.
split; [exact FPLE|]. exists new, sj'.
split. { with_box DISJ ltac:(destruct DX as [(LE & Enew & _ & Erng)|(LT & Enew & _ & _ & FILL & GR1 & GR2 & BW)];
[ left; split; [exact LE| split; [exact Enew| exact Erng]]
| right; split; [exact LT|]; split; [exact Enew|]; split; [| split; [exact GR1| split; [exact GR2| exact BW]]];
eapply fill_frame; [exact FILL | exact MU24 | exact WM24 |];
intros _; cbn [disjoint_from]; clear -SHF1 SHF2 SP1 SP2 HC NF MFA; lia ]). }
split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|].
split; [exact AR3|].
split. { replace (al_space_beg L + c * 4294967296 + 3758096384 + 4 * (nf + ncnt)) with (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * ncnt) by (clear; lia).
replace (new - 4 * (nf + ncnt)) with (new - 4 * nf - 4 * ncnt) by (clear; lia).
eapply junk_frame; [exact JR | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from]; clear -SP1 SP2 HC NF MFA NEWB NC0; lia. }
split; [reflexivity|].
split; [exact MU14|]. split; [exact WM14|]. split; [assumption|]. split; [assumption|].
split; [assumption|]. split; [assumption|]. split; [exact STATS2|]. split; [exact LSJ2|].
split. { eapply azero_frame; [exact AZ2 | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
assert (SHT : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + new)
/\ shad (al_space_beg L + c * 4294967296 + 3758096384 + new) + shlen (536870912 - new) <= 0x10007fff8000).
{ rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
clear -SHT SP1 SP2 HC NF MFA. lia. }
eapply m3_cells_frame; [exact MC2 | exact MU24 | exact WM24 | exact W24OK]. }
step. if_cases K2; zify_cond K2.
{ assert (NC00 : ncnt = 0) by (subst ncnt; rewrite ?unsigned_lit in K2 by (clear -MU MUX SZ; lia); apply Z.div_small; clear -K2 MU; lia).
rewrite NC00 in FIN |- *.
eapply FIN; [ | apply wmono_refl | exact MI2 |].
- replace (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * 0) with (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) by (clear; lia). apply munch_refl.
- apply u32arr_nil; clear -SP1 SP2 HC NF MFA; lia. }
assert (NCP : 0 < ncnt) by (subst ncnt; rewrite ?unsigned_lit in K2 by (clear -MU MUX SZ; lia); apply Z.div_str_pos; clear -K2 SZ; lia).
step. step. zstep. zstep. zstep. zstep. step.
setreg 11 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * ncnt)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; clear -NC0 NF; Z.div_mod_to_equations; lia).
setreg 12 (Z_to_bv 64 (au + 0 * S)) ltac:(f_equal; clear; lia).
eapply evtF_cut.
{ eapply (fill_loop_spec RNG' _ 0 ncnt _ au S ws); try reflexivity.
- clear -NCP; lia.
- rewrite LWS; clear; lia.
- cbn [Z.to_nat fvals seq map rev]. rewrite app_nil_r. exact AR.
- exact MI2.
- clear -MU; lia.
- clear -SZ; lia.
- clear -NC1 MU MUX SP1 SP2 HC; lia.
- clear -SP1 NF HC; lia.
- clear -SP1 SP2 HC NF NEWB NC0; lia.
- intros kk Hkk. assert (M4 : exists q, mfa = 4 * q) by (exists (mfa / 4); clear -MFAM; Z.div_mod_to_equations; lia). destruct M4 as [q Hq].
with_box DISJ ltac:(destruct DX as [(LE & Enew & _ & _)|(LT & Enew & _ & _ & _ & GR1 & _)];
[ eapply rng_sub'; [exact RFJ|]; clear -Hkk LE MFA NF NC0; lia
| destruct (Z_lt_le_dec (4 * nf + 4 * kk + 3) mfa) as [LO4|HI4];
[ eapply rng_sub'; [exact RFJ|]; clear -Hkk LO4 MFA NF NC0; lia
| eapply rng_sub'; [exact GR1|]; clear -Hkk HI4 MFA NF NC0 NEWB Hq; lia ] ]). }
cbv beta. intros ms' (a4y & a5y & m3 & -> & MU3 & WM3 & MI3 & AR3).
replace (Z_to_bv 64 (au + 0 * S)) with (Z_to_bv 64 au : word) by (f_equal; clear; lia).
eapply FIN; [exact MU3 | exact WM3 | exact MI3 | exact AR3].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition populate_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c req lo : Z) (sj : list word) (m : amem)
(st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
let r := get_cls st c in let S := size_of_class c in
let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
fp_le RNG RNG' /\
exists mu' mfa' ncnt sj' (stm' : word),
( (au + req * S <= mu /\ mu' = mu)
\/ (mu < au + req * S /\ mu' = mu + rup (au + req * S - mu) K_USER_MAP
/\ rw_cells bsegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
/\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
/\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
/\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
/\ ncnt = (mu' - au) / S /\ 0 <= ncnt
/\ ( (4 * (nf + ncnt) <= mfa /\ mfa' = mfa)
\/ (mfa < 4 * (nf + ncnt) /\ mfa' = rup (4 * (nf + ncnt)) K_FREEARR_MAP
/\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
/\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
/\ 4 * (nf + ncnt) <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
/\ u32arr bsegs m' (FA + 4 * nf) (fvals au S (Z.to_nat ncnt))
/\ junk_at m' (FA + 4 * (nf + ncnt)) (mfa' - 4 * (nf + ncnt))
/\ st2 = put_cls c (mkAClass mu' (au + ncnt * S) (nf + ncnt) mfa' (c_count r)) st
/\ munch [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp);
(RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
(FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
(al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
(RI + 16, RI + 56); (RI + 68, RI + 69)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' (RI + 16)
[C8 (Z_to_bv 64 (nf + ncnt)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 (au + ncnt * S)); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
/\ rw_cells bsegs m' (RI + 68) [C1 (Z_to_bv 8 0)]
/\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
/\ rw_cells bsegs m' (al_t L + 2792) [C8 stm']
/\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
/\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
/\ m3_cells L m'.
#[using="Type"] Lemma pop_map_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
(rav sp gp tp t0 t1 t2 s0v s1v a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(rax a1x a2x a3x a4x a5x s6x : word)
(F : bvmap 5 word) fc (m1 : amem) (L : alayout) (st : astate) (c req lo : Z) (sj : list word) (stm : word) (fj : list byte),
let r := get_cls st c in let S := size_of_class c in
let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
stk bsegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
mem_inv bsegs m1 -> tp = Z_to_bv 64 ATP ->
rw_cells bsegs m1 (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
m3_cells L m1 ->
rw_cells bsegs m1 (RI + 16)
[C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
rw_cells bsegs m1 (RI + 68) [C1 (Z_to_bv 8 0)] ->
u64arr bsegs m1 (al_t L + 2800) sj -> length sj = 46%nat ->
rw_cells bsegs m1 (al_t L + 2792) [C8 stm] ->
rw_cells bsegs m1 (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
azero m1 (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
azero m1 (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
0 <= req < 2^31 -> mu < au + req * S ->
0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
(al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
(al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
(al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
rng RNG (FA + 4 * nf) (mfa - 4 * nf) ->
AIMG_HI <= al_ctx L ->
iclr (al_t L) 4096 ->
(forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
populate_ret L RNG sp st c req lo sj m1 st2 RNG' m' ->
implS bsegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
(MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc rav) fc None m' (seg_rom bsegs))) ->
evtF bsegs RNG (fun ms' => implS bsegs RNG (aembed ATOP (populate_free_array st c req k)) (epostF Q) ms')
(MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RI) (Z_to_bv 64 (al_t L + 2768)) (Z_to_bv 64 AINSTANCE)
a1x a2x a3x a4x a5x a6 a7
(Z_to_bv 64 RB) (Z_to_bv 64 (au + req * S)) (Z_to_bv 64 mu) (Z_to_bv 64 S) s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x37414) fc None m1 (seg_rom bsegs)).
Proof.
intros until fj. cbv zeta.
intros ST CEIL LO MI TP FR MC REG EXH STATS LSJ STM FJ AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM REQ LT
SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFJ CXI TIC KONT. band_lin.
pose proof T0 as TB. unfold sclr, KLS in TB.
box TCX. box SCX. box TSP.
pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
change (2^37) with 137438953472 in *.
word_range sp SPR.
pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
set (S := size_of_class c) in *.
set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
rewrite RIE in REG, EXH, RRI |- *. rewrite RBE in AZU |- *. rewrite FAE in FJ, AZF, RFJ.
set (total := au + req * S) in *.
assert (TOT : mu < total < 2^48) by (subst total; clear -LT MU MUX REQ SZ; nia).
Local Ltac2 Set LiaHints.tbl := fun () => "03D0?1047820382.14  10649802198.19410951828771.19511116365401.19711169171764.13 11797343393.19111797343393.19211799489569.19711805467289.19311805467289.20311807678621.1  11807744665.11 11807744665.12 11807744665.17 11807744665.18 11807744665.20 11807744665.23 12428150072.19512560036718.2031279872003.13  12890934992.8  13035828566.19213036208498.23 13313577562.3  13596006226.19314488382853.10 14566500566.19115045184517.19115045184517.19215617080686.20316006764370.19316152533917.18916831639642.3  17048393888.19517534156933.19217534156933.19317694175958.19117803025398.18917986879152.14 17986879152.24 19617313304.26 19617313304.38 19617313304.60 20431170854.1932189499897.36  22226902198.19222233892466.20322264047035.36 2265538580.51  22790591833.19724033202211.19524436996044.3  24487705898.1292452149659.200 25065190167.19 25065190167.21 25065190167.24 25065190167.26 25071471268.40 25076071819.19525076071819.19625571772251.53 25787186364.3  2582348142.203 26043010902.19226690313645.18927189741570.19127392054441.20327574660131.19727756642518.19128754851922.19329954546818.13930065953837.16930065953964.17030985182006.13930985182006.17730985182006.19230997602604.20331235492528.3  31240592726.19231423336146.19331759389002.9  32616367638.19732740259714.19233062543571.24 33399844006.19133405859426.2043429883184.135 3435498654.6   3437496860.128 34924617402.7  3530317142.192 36284156488.12836515951321.19736816827353.19737311011542.1913788358132.196 387780808.13   39482238446.20340318426646.19241225433302.1914179232035.195 42805740039.19542831019478.19343146092176.13843224177418.23 43407902550.19243863873618.19344305789522.19344448589954.24 44487020398.19745124086358.19145297343979.19245624631730.19245652632450.20446024503394.19946026600554.20346224309403.8  46784882134.19247745717529.19747920061294.20348330303854.20348817770594.35 49058487570.20049058487570.20249171173510.18 49476425442.19949476425442.20250480208598.19151318623851.19151635592409.19751644794710.19251721615267.19551866641414.18951877860133.14 52058491293.16 52564965719.90 52564965975.52 52564965976.58 52564966103.72 52564966103.73 52564966103.76 52567164907.19352567164907.20352575291859.19152575291859.19253050663610.20353103882817.4  53345018455.20353684145930.1695374621898.60  54270591515.2035480300246.191 54969794426.14 55310130352.3  55588686165.0  55662215590.23 56170256219.13856170256219.17656170256219.19156678337134.19356862825848.19257440577106.19357628700040.13 57745675194.20358061001392.8  58790418937.12 58962623805.24 59115889619.3  59169407342.20359308628433.6  59314873579.17 59403314722.13859828660087.23 59895521983.12 60339709476.11 60925674652.31 61086706080.20061086706080.20261475112864.8  62275100527.13662381799044.53 62385982264.74 63255209115.2006366460303.24  63926788569.19764099247705.19764691122136.19264955147683.19565141294375.25 65141294375.26 65593145730.20165593145730.20366139459811.19566149329551.31 66151427842.16 66161973590.19267221797942.24 68124044985.19268196356771.19568205640558.20368218227538.19368510959950.8  7231441189.24  7335252430.24  7339453554.45  8806423751.20  9302277252.70  9317568675.195 9364391923.8   9692327568.11  999829106.24   00000800900K00X00Y00Z00[01H01I01J01K01Q02102E02_03503Q03R03g04104204a04o05005_05h06W06\06a07607e07j07k08S08X08]09L09M09S09Y09Z09[09\09]0:<0:=0:>0:n0:o0;<0;N0;S0;T0;Y0;m0<A0<\0=A0=c0?N0?O0@20@60@K0A:0A?0AC0AD0AE0B40Bc0Bd0C80CO0C^0Cm0D<0D=0DB0E10E`0Ea0F=0FA0FB0FC0FD0FL0FT0F\0Ff0GU0Ga0Gn0H;0Hj0IA0IB0IW0IX0JG0JY0JZ0J^0J_0J`0KO0L>0Lm0M20M30Mb0Mk0Ml0Mm0N20N30N40Nc0O00OE0OZ0Of0Og0Oh0P80P=0P>0PG0PP0P]0QL0Q^0Q_0Qc0R50Sk0Tj0V50WF0XZ0Y]0Y^0Y_0Y`0Ya0Ye0Yf0Yg0Yh0Zi0Zj0[Y0[^0[c0[d0[e0[f0[k0\00\40\50\d0\h0\l0]10]50]60]:0]O0]S0][0]\0]a0]e0]m0^G0^H0^I0^J0^K0^L0^M0^R0^W0^d0_10_20_D0_X0`00`10`20`D0`X0`e0aT0aa0ab0b40bI0c80c90c=0c>0c?0cC0dM0d_0dd0dh0e6S3CX12T1SS4CEIL2LO4SHB13HspS4CEIL2LO3HspFSSS4CEIL2LO4SHB24SHB33Hsp3CX12HC3MFA3SP22T13LSJSSSS1Y2HCS2HC3SP12TB1Y4CEIL2LO2T13SP23MFAS2HC2NF3MFA3SP12TB1YS2HC3BG33BG53SP14SHB24SHB3S2TB4SHB14SHB24SHB32T2S2HC2MU3SP12TB3BG23BG33BG51YFS3SP13TOT3RU13KX'3BG2S3BG52P21HFS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S2HC3SP23BG31HFS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S3KX'3BG5S3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S3LSJS3LSJS3SP13TOT3RU13KX'3BG2S3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S3LSJFS4CEIL2LO2HC2MU3SP13SP23KX'3BG54SHB23HspS3LSJS3LSJS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5SS4CEILS4CEILFFFSS2HC2MU3SP12TB3BG23BG31Y2Y03CX2SSS4CEIL2LO3CX11H3SP12TB4SHB14SHB22Y03CX23TIC2HC1YFS4CEIL2LO3HspS4CEIL2LO4SHB13HspS3HspSS3LSJS4CEIL2LO3BG24SHB61HS4CEIL2LO2HC3SP23BG3S4CEIL2LO2HC2NF3MFA3SP23BG3S4CEIL2LO2HC2MU3SP22T12TB3BG23BG31Y1HS4CEIL2LO2HC3SP23BG21H2H02H42H52H9S4CEIL2LO3LSJ2MU3AUM2LT3SP13CX13TIC2TB2SZ4SZ323RU33BG23BG43BG54SHB14SHB22K13CX22T23Hsp2HC2NF3MFA3SP22T13MUXFS3MUM3BG41H2H02H42H52H93H103H143H24S2LOS3SP13TOT3RU13KX'3BG2S3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S3LSJS2T1SFS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5SS2HC3SP23BG23BG33BG5S2K22HC3SP23BG23BG33BG5S4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HSS3HspS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5SS4CEIL2LO2HC3SP23KX'3BG53HspS2T1SSSS2MU3MUXS2MU3MUXS2MU3MUXS2T13TIC1HS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S2MU3TOT3RU1S4CEIL2LO3HspS4CEIL2LO3HspS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S4CEIL2LO4SHB24SHB33HspSS3SP13TOT3RU13KX'3BG2SS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S4CEIL2LO4SHB13HspFS2HBFSS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S3BG8FS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S3LSJ3TICSSS3LSJSSS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S4CEIL2LO3HspS3SP13TOT3RU13KX'3BG2S3SP13TOT3RU13KX'3BG2S2MU3TOT3RU1FFS2HC3SP23BG23BG3S3LSJSS3LSJ3TICS3LSJ3TICS4CEIL2LO3HspS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S4CEIL2LO4SHB13HspSS2LOS2HC3SP23BG33BG51HS4CEIL2LO2HC2MU2NF3MFA3SP13SP22TB3BG23BG33BG54SHB34SHB44SHB51H2H02H42H52H93H103H193H203H213H223H233H243H253H293H303H34S4CEIL2LO2HC2NF3MFA3SP13SP22T12TB4NEWB1Y1H2H02H42H53H103H113H14S4CEIL2LO2HC2MU2NF3MFA3SP13SP22TB3BG23BG33BG51H2H02H42H52H93H103H143H153H19S4CEIL2LO2HC2MU2NF3SP13SP22T12TB3BG23BG33BG54NEWB1Y1H2H02H42H52H93H103H113H123H13S4CEIL2LO2HC2MU2NF3MFA3SP13SP22TB3BG23BG33BG54SHB21H2H02H42H52H93H103H203H213H233H24S4CEIL2LO2HC2MU3SP13SP22TB3BG23BG54SHB44SHB51H2H02H42H53H203H213H24SSSSS2HBSSSS2HC2MU3MUM3SP13SP33TOT3RU13RU23KX'1H2H02H42H52H93H103H143H193H24FS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S3CXIS3HspSSSS3HspS3HspS2HBSS3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S2HxS2HBS3TOTS2KXSS2LOS3SP13TOT3RU13KX'3BG2S2K2S3BG22K1SS3BG2S2KXS2MU3BG5S2MU3TOT1H2H02H42H52H93H10SSSFFFS3LSJS3BG5S4CEIL2LO3HspS4CEIL2LO3HspSS4CEIL2LO4SHB13HspS3KX'3BG51H2H02H42H5S3TOT3RU13KX'1H2H02H42H5SSS4CEIL2LO4SHB13HspS3MUM3RU21H2H02H42H9S3TAL1H2H02H4S3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5S3BG23BG43BG5SS4CEIL2LO4SHB13HspS3SP13TOT3RU13KX'3BG2S3LSJ2MU3MUM3AUM2NF3MFA4MFAM3SP13TAL2SZ3BG23BG5FS2LOFFS2HxS2HC3SP23BG13BG23BG33BG43BG51H2H02H42H52H93H103H143H153H193H203H243H293H34S4CEIL2LO4SHB13HspS3TOTS2SZS2HC3SP23BG31H".
pose proof (rup18_facts (total - mu) ltac:(clear -TOT; lia)) as (RU1 & RU2 & RU3).
set (ums := rup (total - mu) 262144) in *.
pose proof (munch_refl [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp)]%Z m1) as MUN.
pose proof (wmono_refl bsegs m1) as WM.
lazymatch goal with |- evtF _ _ ?P _ =>
assert (JOIN : forall a1z : word,
evtF bsegs RNG P
(MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (al_space_beg L + 137438953472 + c * 128))
(Z_to_bv 64 (al_t L + 2768)) (Z_to_bv 64 650968) a1z a2x a3x a4x a5x a6 a7
(Z_to_bv 64 (al_space_beg L + c * 4294967296)) (Z_to_bv 64 total) (Z_to_bv 64 mu) (Z_to_bv 64 S) s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x37418) fc None m1 (seg_rom bsegs)))
end.
2:{ step. if_cases KZ; zify_cond KZ.
- step. step. if_lit.
step. step.
rewrite ?unsigned_lit in KZ by (clear -MU MUX; lia). rewrite <- KZ. apply JOIN.
- apply JOIN. }
intros a1z.
zstep. zstep. zstep. zstep. zstep.
step.
zstep.
setreg 19 (Z_to_bv 64 ums)
ltac:(f_equal; rewrite zb_lxor_ones by (clear -MU MUX; lia);
pose proof (Z.mod_pos_bound (total + (18446744073709551615 - mu)) 18446744073709551616 ltac:(clear; lia)) as B;
rewrite land_align2p18 by exact B; subst ums; unfold rup; clear -TOT MU B; Z.div_mod_to_equations; lia).
step. zstep. zstep. zstep. zstep.
step. if_cases KX; zify_cond KX.
{
apply evtF_done. rewrite populate_unfold. cbv zeta. unfold K_FREEARR_OFF, K_USER_MAP. fold S mu au. fold total. fold ums.
replace (total <=? mu) with false by (symmetry; apply Z.leb_gt; clear -TOT; lia).
replace (3758096384 <? mu + ums) with true by (symmetry; apply Z.ltb_lt; rewrite ?unsigned_lit in KX by (clear -MU MUX RU1 TOT; lia); clear -KX MU RU1 TOT; lia).
cbv beta iota. rewrite aembed_aundef_. apply implF_ret_unr. }
assert (KX' : mu + ums <= 3758096384) by (rewrite ?unsigned_lit in KX by (clear -MU MUX RU1 TOT; lia); clear -KX MU RU1 TOT; lia). clear KX.
lstep.
zstep.
setreg 20 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + mu)) ltac:(f_equal; clear; lia).
step. if_lit.
step. zstep. step. step. step.
step.
apply evtF_done. rewrite populate_unfold. cbv zeta. unfold K_FREEARR_OFF, K_USER_MAP. fold S mu au. fold total. fold ums.
replace (total <=? mu) with false by (symmetry; apply Z.leb_gt; clear -TOT; lia).
replace (3758096384 <? mu + ums) with false by (symmetry; apply Z.ltb_ge; exact KX').
cbv beta iota. unfold ev. rewrite aembed_vis. cbn [aev_tree]. unfold PROT_RW, F_FIXED.
unfold region_beg, K_REGION. change (2^32) with 4294967296. rewrite SBE.
set (BEG := al_space_beg L + c * 4294967296 + mu) in *.
assert (BEGF : BEG mod 4096 = 0 /\ 0x10007fff8000 <= BEG /\ BEG + ums <= al_space_beg L + c * 4294967296 + 3758096384 /\ ums mod 4096 = 0 /\ 0 < ums /\ BEG mod 8 = 0).
{ subst BEG. clear -SP1 SP3 HC MU MUM KX' RU1 RU2 TOT. Z.div_mod_to_equations. lia. }
destruct BEGF as (BG1 & BG2 & BG3 & BG4 & BG5 & BG8).
name_sp sp (-64).
eapply rmap_spec with (addr := BEG) (size := ums) (lo := lo).
all: try lazymatch goal with
| |- stk _ _ _ _ => rewrite Hsp; eassumption
| |- ATOP <= _ => atop_facts; exact CEIL
| |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
| |- mem_inv _ _ => assumption
| |- rmap_cells _ => exact RC
| |- rng_aimg _ => exact RIMG
| |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
| |- rng _ _ _ => solve_rng
| |- @eq word _ _ => reflexivity
| |- _ mod 4096 = 0 => assumption
| |- 0 < _ => exact BG5
end.
all: try (unfold AIMG_HI; clear -BG1 BG2 BG3 BG4 BG5 SP2 CEIL LO HC; rewrite ?unsigned_lit by lia; lia).
{
intros a RNG' ms' NE P1 P2. unfold fixed_answer_ok, is_err, TWO64.
replace (2 ^ 64 - 4096 <? a) with false by (symmetry; apply Z.ltb_ge; clear -P2 BG5; atop_facts; lia).
replace (a =? BEG) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [negb orb]. rewrite aembed_aundef_. apply implF_ret_unr. }
intros RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RP.
destruct RP as (FPLE & _ & MU2 & WM2 & MI2 & ST2 & ZNEW & GR1 & GR2 & BW1 & RC2). unname_sp.
apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFJ.
assert (SHB : 0x2008fff7000 <= shad BEG /\ shad BEG + shlen ums <= 0x10007fff8000 /\ 0 < shlen ums
/\ shad BEG + shlen ums = shad (BEG + ums) /\ shad (BEG + ums) + shlen (3758096384 - (mu + ums)) <= 0x10007fff8000
/\ shad BEG + shlen (3758096384 - mu) <= 0x10007fff8000).
{ rewrite !shad_div, !shlen_div. unfold ASHOFF. subst BEG. clear -BG1 BG2 BG3 BG4 BG5 SP1 SP2 HC MU KX'. Z.div_mod_to_equations. lia. }
destruct SHB as (SHB1 & SHB2 & SHB3 & SHB4 & SHB5 & SHB6).
xport FR MU2 WM2 ltac:(clear -SPR CEIL LO BG2 BG3 SP2 HC; lia).
xport REG MU2 WM2 ltac:(clear -SPR CEIL LO BG2 BG3 SP2 HC; lia).
xport EXH MU2 WM2 ltac:(clear -SPR CEIL LO BG2 BG3 SP2 HC; lia).
xport STATS MU2 WM2 ltac:(rewrite LSJ; ub TSP; clear -SPR CEIL LO BG2 BG3 SP2 HC T0 T1 MU Y TIC TB; subst BEG; lia).
xport STM MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO BG2 BG3 SP2 HC T0 T1 MU Y TIC TB; subst BEG; lia).
xport FJ MU2 WM2 ltac:(clear -SPR CEIL LO BG2 BG3 SP2 HC MFA NF; subst BEG; lia).
assert (AZU2 : azero m2 (shad BEG) (shlen (3758096384 - mu))).
{ eapply azero_frame; [exact AZU | exact MU2 | exact WM2 |]. intros _; cbn [disjoint_from].
clear -SPR CEIL LO SHB6 BG2. lia. }
assert (AZF2 : azero m2 (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) (shlen (536870912 - mfa))).
{ eapply azero_frame; [exact AZF | exact MU2 | exact WM2 |]. intros _; cbn [disjoint_from].
rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -SPR CEIL LO BG2 BG3 BG5 SP1 SP2 HC MFA NF. subst BEG. Z.div_mod_to_equations. lia. }
clear ST MI.
assert (MUW : munch [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp); (BEG, BEG + ums); (shad BEG, shad BEG + shlen ums);
(al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
(al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56)]%Z m1 m2).
{ eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
clear MU2 MUN.
assert (WOK : Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
[(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp); (BEG, BEG + ums); (shad BEG, shad BEG + shlen ums);
(al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
(al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56)]%Z).
{ ub SCX. ub TCX. unfold AIMG_HI, AIMG_LO.
do 6 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 T0 T1 TIC SP1 SP2 HC MU BG2 BG3 SHB1 SHB2 SHB3 Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil. }
assert (MC2 : m3_cells L m2) by (eapply m3_cells_frame; [exact MC | exact MUW | exact WM2 | exact WOK]).
clear TI TK T88 TSD CT ISB IREL ISE IPRE PC RC.
pose proof MC2 as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE). unfold ATP88, ATSD in T88, TSD.
unfold fixed_answer_ok, is_err, TWO64. rewrite Z.eqb_refl.
replace (2 ^ 64 - 4096 <? BEG) with false by (symmetry; apply Z.ltb_ge; clear -BG3 BG5 SP2 HC; lia). cbn [negb orb].
replace (ret_pc (Z_to_bv 64 226452)) with (Z_to_bv 64 226452 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
iprefix.
step. if_cases K1; zify_cond K1. { exfalso. clear -K1 BG2 BG3 SP2 HC. rewrite ?unsigned_lit in K1 by lia. lia. }
step. step. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }
step. step. step.
pose proof (azero_cb m2 _ _ (shlen ums) AZU2 ltac:(rewrite !shlen_div; clear -MU KX' RU1 TOT; Z.div_mod_to_equations; lia)) as SHCB.
step. with_band CX0 ltac:(with_band T0 ltac:(call_sp (poison_shadow_spec RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BEG ums 250 lo))).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- poison_cells _ => exact PC
| |- @eq word _ _ => reflexivity
| |- rw_cells _ _ (shad _) _ => exact SHCB
| |- rng _ (shad _) _ => exact GR2
| |- rng _ _ _ => solve_rng
end.
all: try (atop_facts; clear -BG1 BG2 BG3 BG4 BG5 BG8 SP2 CEIL LO HC; rewrite ?shlen_div; first [lia | Z.div_mod_to_equations; lia]).
all: try (unfold ablk; right; unfold K_SPACE_SIZE in *; clear -BG2 BG3 SP1 SP2 SP3 HC; lia).
all: match goal with |- evtF _ _ _ _ => idtac | |- ?G => idtac "REM-POISON" G end.
step. with_band T0 ltac:(call_sp (thread_stats_spec RNG' (al_ctx L) (al_t L) lo)).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- @eq word _ _ => first [reflexivity | exact TP]
| |- rw_cells _ _ _ _ => assumption
| |- rng _ _ _ => solve_rng
end.
all: try (unfold AIMG_HI; clear -CEIL LO CX0 CX1 T0 T1 CXI TIC TB; lia).
aload STATS 9 (al_t L + 2800 + 72). aload STATS 10 (al_t L + 2800 + 80).
zstep. zstep.
snapshot [(al_t L + 2800, al_t L + 3168)]%Z MUs WMs.
box CT. box REG. box ZNEW. box POST. box FR. box EXH. box STM. box FJ.
astore STATS 9. astore STATS 10.
carry CT MUs WMs ltac:(ub TCX; clear -CX0 CX1 T0 T1 Y TIC CXI TB; lia).
carry REG MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y TIC TB; lia).
carry ZNEW MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 MU BG2 BG3 BG5 Y TIC TB; subst BEG; lia).
carry POST MUs WMs ltac:(clear -SHB1 SHB2 SHB3 T0 T1 TIC TB; with_band T0 lia).
carry FR MUs WMs ltac:(clear -SPR CEIL LO T0 T1 TIC TB; lia).
carry EXH MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y TIC TB; lia).
carry STM MUs WMs ltac:(clear; lia).
carry FJ MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 MFA NF Y TIC TB; lia).
clear MUs WMs.
step. zstep.
setreg 9 (Z_to_bv 64 (al_t L + 2792)) ltac:(f_equal; clear; lia).
assert (AMO : amo_aligned AD (Z_to_bv 64 (al_t L + 2792)) = true) by (apply amo_alignedD_intro; [clear -T0 T1 TIC TB; lia| clear -TAL; Z.div_mod_to_equations; lia]).
snapshot [(al_t L + 2792, al_t L + 2800)]%Z MUa WMa.
box CT. box REG. box ZNEW. box POST. box FR. box EXH. box FJ. box STATS.
amo_stepA AMO.
carry CT MUa WMa ltac:(ub TCX; clear -CX0 CX1 T0 T1 Y TIC CXI TB; lia).
carry REG MUa WMa ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y TIC TB; lia).
carry ZNEW MUa WMa ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 MU BG2 BG3 BG5 Y TIC TB; subst BEG; lia).
carry POST MUa WMa ltac:(clear -SHB1 SHB2 SHB3 T0 T1 TIC TB; with_band T0 lia).
carry FR MUa WMa ltac:(clear -SPR CEIL LO T0 T1 TIC TB; lia).
carry EXH MUa WMa ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y TIC TB; lia).
carry FJ MUa WMa ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 MFA NF Y TIC TB; lia).
carry STATS MUa WMa ltac:(rewrite ?upd_length, LSJ; clear; lia).
clear MUa WMa.
step. step. zstep.
snapshot [(al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56)]%Z MUr WMr.
box CT. box ZNEW. box POST. box FR. box STM. box FJ. box STATS.
step.
carry CT MUr WMr ltac:(ub SCX; clear -HC CX0 CX1 SP1 SP2 Y CXI; lia).
carry ZNEW MUr WMr ltac:(clear -HC SP1 SP2 MU BG2 BG3 BG5; subst BEG; lia).
carry POST MUr WMr ltac:(clear -SHB1 SHB2 SHB3 SP1 SP2 HC; lia).
carry FR MUr WMr ltac:(clear -SPR CEIL LO SP1 SP2 HC; lia).
carry STM MUr WMr ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y TIC TB; lia).
carry FJ MUr WMr ltac:(clear -HC SP1 SP2 MFA NF; lia).
carry STATS MUr WMr ltac:(rewrite ?upd_length, LSJ; ub TSP; clear -HC T0 T1 SP1 SP2 Y TIC TB; lia).
clear MUr WMr.
set (st1 := put_cls c (cls_set_mapped_user (mu + ums) (get_cls st c)) st) in *.
assert (GC : get_cls st1 c = cls_set_mapped_user (mu + ums) (get_cls st c)) by (apply get_cls_put_cls_eq).
replace (Z_to_bv 64 (mu + ums)) with (Z_to_bv 64 (c_mapped_user (get_cls st1 c)) : word) by (rewrite GC; reflexivity).
replace (Z_to_bv 64 au) with (Z_to_bv 64 (c_allocated_user (get_cls st1 c)) : word) by (rewrite GC; reflexivity).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (m3_cells_frame L m1 mm _ MC MUW WM2 WOK) as MC3 end.
eapply pop_tail_spec with (lo := lo).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- implS _ _ _ _ _ => idtac
| |- stk _ _ _ _ => eassumption
| |- ATOP <= _ => atop_facts; exact CEIL
| |- _ <= bv_unsigned _ - _ => clear -LO; lia
| |- mem_inv _ _ => assumption
| |- m3_cells _ _ => exact MC3
| |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
| |- rw_cells _ _ (aregion_info _ _ + 16) _ => rewrite RIE; by_GC GC; exact REG
| |- rw_cells _ _ (aregion_info _ _ + 68) _ => rewrite RIE; exact EXH
| |- rw_cells _ _ (afreearr _ _ + _) _ => rewrite FAE; by_GC GC; exact FJ
| |- u64arr _ _ _ _ => exact STATS
| |- length _ = _ => rewrite ?upd_length; exact LSJ
| |- azero _ _ _ => rewrite FAE; by_GC GC; unfold K_FREEARR_MAX; eapply azero_frame; [exact AZF | exact MUW | exact WM2 |];
intros _; cbn [disjoint_from]; rewrite !shad_div, !shlen_div in *; unfold ASHOFF in *;
clear -SPR CEIL LO BG2 BG3 BG5 SP1 SP2 HC MFA NF T0 TB MU TIC; subst BEG; Z.div_mod_to_equations; lia
| |- (forall r', put_cls _ r' _ = put_cls _ r' _) => intros r'; apply put_cls_put_cls
| |- a_space_beg _ = _ => exact SBE
| |- rng_aimg _ => exact RIMG
| |- rng _ _ (bv_unsigned _ - _) => exact RSTK
| |- rng _ (aregion_info _ _) _ => rewrite RIE; exact RRI
| |- rng _ (afreearr _ _ + _) _ => rewrite FAE; by_GC GC; exact RFJ
| |- rng _ _ _ => solve_rng
| |- @eq word _ _ => first [reflexivity | exact TP]
| |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
end.
all: try (by_GC GC; unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
clear KONT; fold S mu au nf mfa; first [assumption | clear -MU MUX KX' RU1 TOT AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC CXI TB; lia]).
intros st2 RNG'' m'' t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' TR.
eapply KONT.
unfold tail_ret in TR. rewrite GC in TR. cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count cls_set_mapped_user] in TR.
fold mu au nf mfa in TR. fold S in TR. rewrite FAE, RIE in TR. unfold K_FREEARR_MAX, K_FREEARR_MAP in TR.
destruct TR as (FPLE2 & mfa' & sj'' & FDISJ & NEWB & NEWM & NEWMOD & AR & JR & ST2EQ & MUT & WMT & MIT & STT & REGT & EXHT & STATST & LSJT & AZT & MCT).
box FDISJ.
unfold populate_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold S mu au nf mfa. rewrite FAE, RIE, RBE. fold total. fold ums. fold BEG.
split; [eapply fp_le_trans; [exact FPLE | exact FPLE2]|].
lazymatch type of STM with rw_cells _ _ _ [C8 ?w] => exists (mu + ums), mfa', ((mu + ums - au) / S), sj'', w end.
replace (mu + ums - mu) with ums by (clear; lia).
replace (al_space_beg L + c * 4294967296 + (mu + ums)) with (BEG + ums) by (subst BEG; clear; lia).
assert (DJU : forall lo' hi', (hi' <= BEG \/ BEG + ums <= lo') -> (hi' <= shad BEG \/ shad BEG + shlen ums <= lo') ->
(hi' <= al_t L + 2792 \/ al_t L + 2800 <= lo') -> True) by (intros; exact I).
assert (BW2 : fp_bw RNG'').
{ with_box FDISJ ltac:(destruct DX as [(_ & _ & Erng)|(_ & _ & _ & _ & _ & BWx)]; [rewrite Erng; exact BW1| exact BWx]). }
split. { right. split; [exact LT|]. split; [reflexivity|].
split; [| split; [| split; [eapply rng_fp_le; [exact FPLE2| exact GR1] | split; [eapply rng_fp_le; [exact FPLE2| exact GR2]| exact BW2]]]].
- eapply cells_frame; [exact ZNEW | exact MUT | exact WMT |].
cbn [disjoint_from cells_size csize Nat.add]. rewrite ?Z2Nat.id by (clear -BG5; lia).
ub TSP. clear -SPR CEIL LO BG2 BG3 BG5 SP1 SP2 HC MU MFA NF NEWB NEWM T0 T1 SHB1 SHB2 Y TIC TB. rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. subst BEG.
Z.div_mod_to_equations. lia.
- eapply fill_frame; [exact POST | exact MUT | exact WMT |]. intros _. cbn [disjoint_from].
ub TSP. clear -SPR CEIL LO BG2 BG3 BG5 SP1 SP2 HC MU MFA NF NEWB NEWM T0 T1 SHB1 SHB2 SHB3 Y TIC TB. rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. subst BEG.
Z.div_mod_to_equations. lia. }
split; [clear -KX' BG5; lia|]. split; [clear -MUM RU2; Z.div_mod_to_equations; lia|].
split; [reflexivity|]. split; [apply Z.div_pos; clear -MU BG5 SZ; lia|].
split; [with_box FDISJ ltac:(destruct DX as [(LE & Emfa & _)|RR]; [left; split; [exact LE| exact Emfa] | right; exact RR])|]. split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|].
split; [exact AR|]. split; [exact JR|]. split; [exact ST2EQ|].
split. { eapply munch_trans; [eapply munch_weaken; [| exact MUW] | eapply munch_weaken; [| exact MUT]]; unfold sub_fp; cbn [outside]; subst BEG;
clear -NEWB NEWM MFA NF BG5; intros x Hx; lia. }
split; [eapply wmono_trans; [exact WM2 | exact WMT]|]. split; [exact MIT|]. split; [exact STT|].
split; [exact REGT|]. split; [exact EXHT|]. split; [exact STATST|]. split; [exact LSJT|].
split. { eapply cells_frame; [exact STM | exact MUT | exact WMT |]. cbn [disjoint_from cells_size csize Nat.add].
ub TSP. clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM T0 T1 Y TIC TB. rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
split. {
pose proof (azero_split m1 _ _ (shlen ums) AZU ltac:(rewrite !shlen_div; clear -KX' BG5 MU; Z.div_mod_to_equations; lia)) as AZT'.
rewrite SHB4 in AZT'.
replace (shlen (3758096384 - mu) - shlen ums) with (shlen (3758096384 - (mu + ums))) in AZT'
by (rewrite !shlen_div; clear -MUM RU2 BG4; Z.div_mod_to_equations; lia).
eapply azero_frame; [eapply azero_frame; [exact AZT' | exact MUW | exact WM2 |] | exact MUT | exact WMT |];
intros _; cbn [disjoint_from]; ub TSP; clear -SPR CEIL LO BG2 BG3 BG5 SP1 SP2 HC MU MFA NF NEWB NEWM T0 T1 SHB1 SHB2 SHB3 SHB4 SHB5 KX' Y TIC TB;
rewrite !shad_div, !shlen_div in *; unfold ASHOFF in *; subst BEG; Z.div_mod_to_equations; lia. }
split; [exact AZT | exact MCT].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma populate_ret_pre : forall L RNG sp st c req lo sj m m1 st2 RNG' m',
munch [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp)]%Z m m1 -> wmono bsegs m m1 ->
populate_ret L RNG sp st c req lo sj m1 st2 RNG' m' -> populate_ret L RNG sp st c req lo sj m st2 RNG' m'.
Proof.
intros until m'. intros MU0 WM0 PR. unfold populate_ret in *. cbv zeta in PR. cbv zeta.
destruct PR as (FP & mu' & mfa' & ncnt & sj' & stm' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & MU & WM & REST).
split; [exact FP|]. exists mu', mfa', ncnt, sj', stm'.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|].
split. { eapply munch_trans; [eapply munch_weaken; [| exact MU0] | exact MU]. Local Ltac2 Set LiaHints.tbl := fun () => "0010=22706556809.8000004S2Hx".
unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
split; [eapply wmono_trans; [exact WM0 | exact WM]|]. exact REST.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma tail_to_populate : forall L RNG (sp : word) st c req lo sj m1 (stm : word) st2 RNG' m',
let r := get_cls st c in let S := size_of_class c in
let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
au + req * S <= mu -> 0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> 0 < S ->
0 <= nf -> 4 * nf <= mfa -> 1 <= c < K_NUM_CLASSES ->
ATOP <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
(al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
rw_cells bsegs m1 (al_t L + 2792) [C8 stm] ->
azero m1 (shad (aregion L c + mu)) (shlen (K_FREEARR_OFF - mu)) ->
iclr (al_t L) 4096 ->
tail_ret L RNG sp st st c lo m1 st2 RNG' m' -> populate_ret L RNG sp st c req lo sj m1 st2 RNG' m'.
Proof.
intros until m'. cbv zeta. intros LE MU MUX MUM SZ NF MFA HC CEIL LO SP1 SP2 SP3 T0 T1 TSP STM AZU TIC TR. band_lin.
pose proof T0 as TB. unfold sclr, KLS in TB.
unfold K_NUM_CLASSES, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. change (2^37) with 137438953472 in *.
assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
unfold tail_ret, K_FREEARR_MAX, K_FREEARR_MAP in TR. cbv zeta in TR. rewrite FAE, RIE in TR.
destruct TR as (FP & mfa' & sj' & FDISJ & NEWB & NEWM & NEWMOD & AR & JR & ST2EQ & MUT & WMT & MIT & STT & REGT & EXHT & STATST & LSJT & AZT & MCT).
unfold populate_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. rewrite FAE, RBE, RIE. rewrite RBE in AZU.
set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *. set (S := size_of_class c) in *.
assert (SHF : shad (al_space_beg L + c * 4294967296 + mu) + shlen (3758096384 - mu) <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
/\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (mfa' - mfa) <= 0x10007fff8000
/\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) <= 0x10007fff8000
/\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)).
{ rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -MU MUX MUM NF MFA NEWB NEWM HC SP1 SP2 SP3. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0080>16032236000.7121627639569.7 25593949770.6 52567063507.3052567063507.3354758581875.158806423751.10 9689982781.7  00001;01?01D02702e03503903=S2NF3MFA2HC3SP13SP23SP34NEWB4NEWM1H2H02H42H52H93H103H143H153H203H213H243H34S2MUS3MUXS2NF2HC4CEIL2LO3SP13SP22T13TSP4NEWB2TB4SHF24SHF42H0S2MU2NF2HC4CEIL2LO3SP13TSP2TB4SHF14SHF33SLO2H0S2MU2HC3SP11H2H0S2HxS2SZ".
lia. }
destruct SHF as (SHF1 & SHF2 & SHF3 & SHF4).
split; [exact FP|]. exists mu, mfa', ((mu - au) / S), sj', stm.
split; [left; split; [exact LE| reflexivity]|].
split; [clear -MU MUX; lia|]. split; [exact MUM|]. split; [reflexivity|]. split; [apply Z.div_pos; clear -MU SZ; lia|].
split; [destruct FDISJ as [(LE2 & Emfa & _)|RR]; [left; split; [exact LE2| exact Emfa] | right; exact RR]|].
split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|].
split; [exact AR|]. split; [exact JR|]. split; [exact ST2EQ|].
split. { eapply munch_weaken; [| exact MUT]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
split; [exact WMT|]. split; [exact MIT|]. split; [exact STT|]. split; [exact REGT|]. split; [exact EXHT|]. split; [exact STATST|]. split; [exact LSJT|].
split. { eapply cells_frame; [exact STM | exact MUT | exact WMT |]. cbn [disjoint_from cells_size csize Nat.add].
clear -CEIL LO SP1 SP2 HC NF MFA NEWB NEWM T0 T1 TSP SHF2 SHF4 TIC TB. pose proof (bv_unsigned_in_range 64 sp). lia. }
split. { eapply azero_frame; [exact AZU | exact MUT | exact WMT |]. intros _. cbn [disjoint_from].
assert (SLO : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu)) by (rewrite shad_div; unfold ASHOFF; clear -SP1 HC MU; Z.div_mod_to_equations; lia).
clear -CEIL LO SP1 SP2 HC NF MFA NEWB NEWM T0 T1 TSP SHF1 SHF2 SHF3 SLO MU TIC TB. pose proof (bv_unsigned_in_range 64 sp). lia. }
split; [exact AZT | exact MCT].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma populate_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c req lo : Z) (sj : list word) (stm : word) (fj : list byte),
let r := get_cls st c in let S := size_of_class c in
let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 2768) -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 RI -> a4 = Z_to_bv 64 req ->
m3_cells L m ->
rw_cells bsegs m (RI + 16)
[C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
0 <= req < 2^31 ->
0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
(al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
(al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
(al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
rng RNG (FA + 4 * nf) (mfa - 4 * nf) ->
AIMG_HI <= al_ctx L ->
iclr (al_t L) 4096 ->
(forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
populate_ret L RNG sp st c req lo sj m st2 RNG' m' ->
implS bsegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
implS bsegs RNG (aembed ATOP (populate_free_array st c req k)) (epostF Q)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 populate_entry) fc None m (seg_rom bsegs)).
Proof.
intros until fj. cbv zeta.
intros ST CEIL LO MI TP -> -> -> -> -> MC REG EXH STATS LSJ STM FJ AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM REQ
SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFJ CXI TIC KONT. band_lin.
pose proof T0 as TB. unfold sclr, KLS in TB.
box TCX. box SCX. box TSP.
pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, populate_entry in *.
change (2^37) with 137438953472 in *.
word_range sp SPR.
pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
set (S := size_of_class c) in *.
set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
pose proof (munch_refl [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp)]%Z m) as MUN.
pose proof (wmono_refl bsegs m) as WM.
set (total := au + req * S).
assert (TOTB : 0 <= total < 2^48) by (subst total; clear -MU MUX REQ SZ; nia).
iprefix.
Local Ltac2 Set LiaHints.tbl := fun () => "03?0?10122937661.4  11449825958.16 11777263255.12611805467289.12311805467289.12511805467289.12611805645610.31 11912744615.12512367362435.12512560036718.12512979092160.12912979092161.12813021749692.12513464694894.12513596006226.12513682426862.12614939502107.1301527479463.123 15501093667.12515582139502.12315617080686.12515768979799.1251586831214.126 16006764370.12516397621975.12617506121710.12617527738094.12317646078182.11617776320431.12418383852439.12518649666969.12318909637614.12619049469500.12619320801509.30 19596407918.12520857051927.12520921468142.12321064248558.12321105598062.12521305858542.12621585288942.12621918414723.12522159532183.12323253790359.12524630998586.12325314760359.1262582348142.125 25878270254.1252610662845.9   26551019630.12527389957282.13127389957282.13227392054442.13427923971379.12528132537239.12628344324846.12628487105262.12628754851922.12529238159895.12529545175216.12529950340078.12630759277294.12630954221806.12631081687356.12631423336146.12531523060718.12631928062011.30 32651489978.12533039531175.12633227529838.12533298494999.12633640253591.12533680001082.12634122383132.13534122383133.13334122383133.1343437494409.121 3437494409.122 35022110958.12336115622446.12536993589379.12637107179452.12537150386135.1263734855790.125 37364793838.1263822472729.125 38692635477.0  3875130862.126 38982519319.12639284637285.0  3945979267.125 39482238446.12539558636183.12339987860078.12540672532759.12541454716183.12641809558659.12342220796142.12642238456215.12642332025047.12642654422266.12742831019478.12542860312857.12543055091515.11443060403331.12643065324654.12543682861079.12343863873618.12543941322990.12643987951406.12544080882466.1  44305789522.12545099762158.12645221239098.1264534591639.125 45652632450.13245652632450.13345652632450.13546058767598.12546270630510.12547524266455.12347920061294.12548076354211.12548187556003.12548318732953.12648330303854.1254847493603.125 48724676119.12549058487570.12949058487570.13049060584731.1334934770723.125 50978328983.12651359989486.12351421085373.12551425718543.12551481786499.12651678667183.12451905078894.12552622824343.12652861484439.1255316791447.126 53345018455.12553460783854.12553767577775.1245378322263.125 54269560302.12654270591512.13454272688656.13154272688656.13254725287469.12154725287469.12255336861645.13255338958790.13155338958790.13355347944512.12155347945285.12056228262055.125563227834.125  56478134243.2  57440577106.12557697976473.12657708859886.12657745675194.12558995781614.12659106945047.12559169407342.12559311160430.12559586081467.13060025031335.1266062692974.125 61086706080.12961086706080.13061088803241.13361406539758.12661847185431.12661902786670.12561917199023.12462891835758.12663162687513.12563235321900.12263694018620.12663713694743.12563776448791.12664297306692.13564297306693.13364297306693.13465593145730.13065593145730.13165593145730.1346611761774.125 66410366446.1266746801847.130 6746801848.129 67800801447.12568055296919.12568205640558.12568218227538.12568423505646.1236979066647.123 7010956092.123 8163491438.126 8583720762.126 8799536366.123 9270407065.126 9372136215.126 985337532.125  00000<00H00\00]00^00_01=01>01?01H01P01X01\01e01n02702802902E02N02W02k03403=03Q03Z03c03d03h04404L04U04Y04a04j05>05G05P05Y05b05k05l06@06M06R06S06\06`06o07807907:07;07<07L07U07^07g08708;08D08M08V08Z08c08l09509:09;09D09Q09^09c09h09m0:20::0:B0:K0:O0:P0:T0:h0;10;:0;R0;S0;\0;h0;i0;j0<30<C0<L0<\0<h0<i0=20=F0=Z0=[0=`0>80><0>=0>F0>S0>\0>e0>i0>j0?30?<0?A0?M0?N0?O0?P0?Y0?b0@60@?0@O0@c0A;0AD0AX0Al0Am0An0Ao0B<0BL0BU0Bm0Bn0Bo0C30C<0CP0C\0Cl0D@0DI0DM0Da0Dj0Dk0Dl0Dm0E30E90E=0EA0EE0EI0EM0EN0ES0EX0Ea0F90FB0FG0FP0Fd0Fm0G60G70G80GA0GB0GC0GD0GM0GY0Gb0Gf0Go0HG0HK0HO0H_0Hl0I00I40I80I90I:0I;0ID0IM0IN0IO0IP0I]0If0Io0J80JD0JH0JQ0JV0J_0K70KD0KHS2HC3K313K16S1H2H02H42H5S4CEIL2LO2HC3SP23RIESSSS4CEIL2LO2HC3SP21H2H02H42H52H9SSS4CEIL2LOS2HC3K16S2HC3K16S2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOFSS4CEIL2LO2T1S4CEIL2LOS4CEIL2LOS4CEIL2LO2HC3SP23RIES4CEIL2LOS4CEIL2LOS4CEIL2LO2HC3SP23RIES4CEIL2LOS4CEIL2LOSS2LOS4CEIL2LO2T1S4CEIL2LO2HC3MFA3SP23FAES4CEIL2LOS2HBS3SP12SZS4CEIL2LOS4CEIL2LO2HC3SP23RIES4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LO2HC3SP23RIES4CEIL2LO3CX1S3SPRSS4CEIL2LOS2LOS4CEIL2LO3CX11HS4CEIL2LOSSSSS4CEIL2LO3LSJ2T1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO3LSJ2T1S2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS3MFA3SP1S3SPRSS4CEIL2LOS4CEIL2LO3CX1S4CEIL2LO3CX1S3SPRS3REQS3REQS3REQS2MU3MUXS2MU3MUXS4CEIL2LOS2LOSS2HBS4CEIL2LO2HC3SP23RIES4CEIL2LOS4CEIL2LOS4CEIL2LO2HC3MFA3SP23FAESS4CEIL2LOS4CEIL2LO2T1SSS4CEIL2LOS4CEIL2LO3LSJ2T1S4CEIL2LOS4CEIL2LO3LSJ2T1S4CEIL2LO2T1SS4CEIL2LOS4CEIL2LO2HC3SP23RIES4CEIL2LO2HC3SP23RIEFS3SPRS4CEIL2LO2HC3MFA3SP23FAES2LOSS4CEIL2LOS4CEIL2LO3CX1S4CEIL2LOS4CEIL2LOS2LOSS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LO2T1SSSS4CEIL2LOS4CEIL2LOS4CEIL2LO2HC3SP23RIES4CEIL2LOS4CEIL2LO3LSJ2T1S4CEIL2LO2HC3SP23RIES4CEIL2LO2HC3MFA3SP23FAES4CEIL2LOS4CEIL2LO2HC3SP23RIES4CEIL2LO2HC3SP23RIEFFFS4CEIL2LO3CX1S4CEIL2LO3LSJ2T1S4CEIL2LOS4CEIL2LO2HC3MFA3SP23FAESSS2LOS4CEIL2LOS4CEIL2LO2HC3SP23RIES4CEIL2LO2T1S4CEIL2LO3LSJ2T1S4CEIL2LO2HC3SP23RIES4CEIL2LOS2LOS4CEIL2LO2HC3SP23RIES4CEIL2LOFFFS4TOTBS4TOTBS2HCS2HCS2HCS2HCS2HCSS3SPRS3K16S4CEIL2LOS4CEIL2LO2HC3MFA3SP23FAES4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LO2HC3SP23RIES4CEIL2LOS4CEIL2LOSSS4CEIL2LOSSSS4CEIL2LOS4CEIL2LO2T1S4CEIL2LOS2LOS4CEIL2LOS4CEIL2LO2HC3MFA3SP23FAES2LOS2HBS4CEIL2LO3LSJ2T1S4CEIL2LO3CX1S2SZS2SZS2SZSSSS4CEIL2LOS4CEIL2LOSSSS4CEIL2LO3CX1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S2HBS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LO2HC3MFA3SP23FAES4CEIL2LO3CX1S2HB".
carve_frame 64%nat ST.
do 9 step.
step. step.
rewrite RIE in REG, EXH, RRI |- *. rewrite RBE in AZU. rewrite FAE in FJ, AZF, RFJ.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (AZU1 : azero m1 (shad (al_space_beg L + c * 4294967296 + mu)) (shlen (3758096384 - mu)));
[ eapply azero_frame; [exact AZU | exact MUN | exact WM |]; intros _; cbn [disjoint_from];
rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MU MUX; Z.div_mod_to_equations; lia |];
assert (AZF1 : azero m1 (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) (shlen (536870912 - mfa)));
[ eapply azero_frame; [exact AZF | exact MUN | exact WM |]; intros _; cbn [disjoint_from];
rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MFA NF; Z.div_mod_to_equations; lia |]
end.
clear AZU AZF.
lazymatch goal with |- evtF _ _ ?P (MS _ _ _ _ _ ?m1 _) =>
assert (MAPK : forall a1x a2x a3x a4x a5x a6x : word, mu < total ->
evtF bsegs RNG P
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (al_space_beg L + 137438953472 + c * 128))
(Z_to_bv 64 (al_t L + 2768)) (Z_to_bv 64 650968) a1x a2x a3x a4x a5x a6x a7
(Z_to_bv 64 (al_space_beg L + c * 4294967296)) (Z_to_bv 64 total) (Z_to_bv 64 mu) (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x37414) fc None m1 (seg_rom bsegs)));
[ intros a1x a2x a3x a4x a5x a6x KM;
eapply pop_map_spec with (lo := lo) (L := L) (st := st);
try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- implS _ _ _ _ _ => idtac
| |- stk _ _ _ _ => eassumption
| |- ATOP <= _ => atop_facts; exact CEIL
| |- mem_inv _ _ => assumption
| |- m3_cells _ _ => eapply m3_cells_frame; [exact MC | exact MUN | exact WM | apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX1 CXI; unfold AIMG_HI; lia | apply Forall_nil]]
| |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
| |- rw_cells _ _ (aregion_info _ _ + 16) _ => rewrite RIE; exact REG
| |- rw_cells _ _ (aregion_info _ _ + 68) _ => rewrite RIE; exact EXH
| |- rw_cells _ _ (afreearr _ _ + _) _ => rewrite FAE; exact FJ
| |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
| |- u64arr _ _ _ _ => exact STATS
| |- length _ = _ => exact LSJ
| |- azero _ (shad (aregion _ _ + _)) _ => rewrite RBE; exact AZU1
| |- azero _ (shad (afreearr _ _ + _)) _ => rewrite FAE; exact AZF1
| |- a_space_beg _ = _ => exact SBE
| |- rng_aimg _ => exact RIMG
| |- rng _ _ (bv_unsigned _ - _) => exact RSTK
| |- rng _ (aregion_info _ _) _ => rewrite RIE; exact RRI
| |- rng _ (afreearr _ _ + _) _ => rewrite FAE; exact RFJ
| |- rng _ _ _ => solve_rng
| |- @eq word _ _ => first [reflexivity | exact TP]
| |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
| |- forall st2, _ => intros * PR; eapply KONT; eapply populate_ret_pre; [exact MUN | exact WM | exact PR]
end;
unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
clear KONT; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM REQ KM LO HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC CXI TB; lia]
| ]
end.
lazymatch goal with |- evtF _ _ ?P (MS _ _ _ _ _ ?m1 _) =>
assert (TAILK : forall s1x s3x a1x a2x a4x a5x a6x : word, total <= mu ->
evtF bsegs RNG P
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (al_space_beg L + 137438953472 + c * 128))
s1x (Z_to_bv 64 650968) a1x a2x (Z_to_bv 64 au) a4x a5x a6x a7
(Z_to_bv 64 (al_space_beg L + c * 4294967296)) s3x (Z_to_bv 64 mu) (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x374e8) fc None m1 (seg_rom bsegs)));
[ intros s1x s3x a1x a2x a4x a5x a6x KM;
eapply evtF_mono;
[ eapply pop_tail_spec with (lo := lo) (L := L) (st := st) (st1 := st);
try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- implS _ _ _ _ _ => idtac
| |- stk _ _ _ _ => eassumption
| |- ATOP <= _ => atop_facts; exact CEIL
| |- mem_inv _ _ => assumption
| |- m3_cells _ _ => eapply m3_cells_frame; [exact MC | exact MUN | exact WM | apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX1 CXI; unfold AIMG_HI; lia | apply Forall_nil]]
| |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
| |- rw_cells _ _ (aregion_info _ _ + 16) _ => rewrite RIE; exact REG
| |- rw_cells _ _ (aregion_info _ _ + 68) _ => rewrite RIE; exact EXH
| |- rw_cells _ _ (afreearr _ _ + _) _ => rewrite FAE; exact FJ
| |- u64arr _ _ _ _ => exact STATS
| |- length _ = _ => exact LSJ
| |- azero _ (shad (afreearr _ _ + _)) _ => rewrite FAE; exact AZF1
| |- (forall r', put_cls _ r' _ = put_cls _ r' _) => intros r'; reflexivity
| |- a_space_beg _ = _ => exact SBE
| |- rng_aimg _ => exact RIMG
| |- rng _ _ (bv_unsigned _ - _) => exact RSTK
| |- rng _ (aregion_info _ _) _ => rewrite RIE; exact RRI
| |- rng _ (afreearr _ _ + _) _ => rewrite FAE; exact RFJ
| |- rng _ _ _ => solve_rng
| |- @eq word _ _ => first [reflexivity | exact TP]
| |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
| |- forall st2, _ => intros * TR; eapply KONT; eapply populate_ret_pre; [exact MUN | exact WM |];
eapply tail_to_populate; try eassumption; try (first [unboxed TSP | rewrite RBE; exact AZU1 | atop_facts; exact CEIL]);
unfold K_NUM_CLASSES, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
clear -MU MUX MUM NF MFA HC KM LO SZ SP1 SP2 SP3 T0 T1 TIC TB; lia
end;
unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
clear KONT; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM REQ KM LO HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC CXI TB; lia]
| cbv beta; intros ms' H; rewrite populate_unfold; cbv zeta; fold S mu au; fold total;
replace (total <=? mu) with true by (symmetry; apply Z.leb_le; exact KM); exact H ]
| ]
end.
step.
step. zstep.
step. if_cases K31; zify_cond K31.
1: step.
1: setreg 21 (Z_to_bv 64 S) ltac:(subst S; rewrite K31; reflexivity).
2: step; step; if_cases K16; zify_cond K16.
2: do 9 zstep.
2: setreg 21 (Z_to_bv 64 S) ltac:(subst S; symmetry; apply size_formula; clear -K16 K31 HC; lia).
3: zstep.
3: setreg 21 (Z_to_bv 64 S) ltac:(subst S; unfold size_of_class; replace (c <=? 16) with true by (symmetry; apply Z.leb_le; clear -K16; lia);
rewrite Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia).
all: step; step.
all: zstep; zstep; zstep.
all: setreg 19 (Z_to_bv 64 total) ltac:(subst total; apply Z_to_bv_eqm; clear -REQ SZ MU MUX; Z.div_mod_to_equations; nia).
all: setreg 18 (Z_to_bv 64 (al_space_beg L + c * 4294967296)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
all: step; if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by (clear -MU MUX TOTB; lia).
- apply MAPK. exact KM.
- step. apply TAILK. exact KM.
- apply TAILK. exact KM.
- apply MAPK. exact KM.
- apply MAPK. exact KM.
- step. apply TAILK. exact KM.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
